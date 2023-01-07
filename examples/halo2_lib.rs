use std::vec;

use ark_std::{end_timer, start_timer};
use halo2_base::{
    gates::{
        flex_gate::{FlexGateConfig, GateStrategy},
        GateInstructions,
    },
    utils::ScalarField,
    AssignedValue, Context, ContextParams,
    QuantumCell::{Constant, Existing, Witness},
};
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    halo2curves::bn256::{Bn256, Fr, G1Affine},
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Assigned, Circuit, ConstraintSystem,
        Error,
    },
    poly::{
        commitment::ParamsProver,
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverSHPLONK, VerifierSHPLONK},
            strategy::SingleStrategy,
        },
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use rand::rngs::OsRng;

#[derive(Clone, Debug)]
struct PoseidonConfig<F: ScalarField> {
    pub gate: FlexGateConfig<F>,
}

#[derive(Clone, Debug)]
struct PoseidonChip<'v, F: ScalarField> {
    pub config: PoseidonConfig<F>,
    pub buffer: Vec<AssignedValue<'v, F>>,
}

impl<'v, F: ScalarField> PoseidonChip<'v, F> {
    pub fn new(config: PoseidonConfig<F>) -> Self {
        Self { config, buffer: vec![] }
    }
    pub fn update(&mut self, stream: &[AssignedValue<'v, F>]) {
        for x in stream.iter() {
            self.buffer.push(x.clone());
        }
    }
    pub fn squeeze(&mut self, ctx: &mut Context<'v, F>) -> AssignedValue<'v, F> {
        let mut res = self.config.gate.load_constant(ctx, F::zero());
        for x in self.buffer.iter() {
            let res2 = self.config.gate.mul(ctx, Existing(&res), Existing(&res));
            let res4 = self.config.gate.mul(ctx, Existing(&res2), Existing(&res2));
            let res5 = self.config.gate.mul(ctx, Existing(&res4), Existing(&res));
            res = self.config.gate.add(ctx, Existing(&res5), Existing(&x));
        }
        self.buffer.clear();
        res
    }
}

#[derive(Clone, Default)]
struct MyCircuit {
    x: Value<Fr>,
}

impl Circuit<Fr> for MyCircuit {
    type Config = PoseidonConfig<Fr>;
    type FloorPlanner = SimpleFloorPlanner; // we will always use SimpleFloorPlanner

    fn without_witnesses(&self) -> Self {
        // set `x` to `Value::unknown()` for verifying key and proving key generation, which are steps that do not depend on the witnesses
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        // you can always set strategy to Vertical and context_id = 0 for now
        // we need to know `degree` where the final circuit will have `2^degree` rows
        // `advice` is the number of advice columns
        // `fixed` is the number of fixed columns
        let degree: usize = std::env::var("DEGREE")
            .unwrap_or_else(|_| panic!("set DEGREE env variable to usize"))
            .parse()
            .unwrap_or_else(|_| panic!("set DEGREE env variable to usize"));
        let gate = FlexGateConfig::configure(meta, GateStrategy::Vertical, &[2], 1, 0, degree);
        println!("{}", meta.blinding_factors());
        PoseidonConfig { gate }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        // this is where witness generation happens

        // halo2 allows you to specify computations and constraints in "regions": you specify what columns to use, and row positions are relative to the region
        // it will then try to re-arrange the regions vertically to pack in as much as possible - this is called the layouter

        // we find the layouter to slow down performance, so we prefer to do everything in a single region and you as the circuit designer can either manually or automatically optimize the grid layout
        let mut first_pass = true;
        layouter.assign_region(
            || "put a name if you want",
            |region| {
                // because of the layouter's intent to re-arrange regions, it always calls this closure TWICE: the first time to figure out the "shape" of the region, the second time to actually do the computations
                // doing things twice is slow, so we skip this step. ONLY do this if you are using a single region!
                if first_pass {
                    first_pass = false;
                    return Ok(());
                }

                // to do our own "auto-"assignment of cells and to keep track of how many cells are used, etc, we put everything into a `Context` struct: this is basically the `region` + helper stats
                let mut ctx = Context::new(
                    region,
                    ContextParams {
                        max_rows: config.gate.max_rows,
                        num_context_ids: 1,
                        fixed_columns: config.gate.constants.clone(),
                    },
                );

                // now to the actual computation

                // first we load a private input `x` (let's not worry about public inputs for now)
                let x = config.gate.assign_witnesses(&mut ctx, vec![self.x]).pop().unwrap();

                let mut poseidon_chip = PoseidonChip::new(config.clone());
                poseidon_chip.update(&vec![x.clone(); 5]);
                let y = poseidon_chip.squeeze(&mut ctx);
                println!("{:?}", y.value());
                // the `vec![(0, None)]` tells us to turn on a vertical `a + b * c = d` gate at row position 0. Ignore the `None` for now - it's just always there

                ctx.print_stats(&["Gate"]);
                Ok(())
            },
        )?;

        // post processing if you want
        Ok(())
    }
}

fn main() {
    let k = 6; // this is the log_2(rows) you specify
    std::env::set_var("DEGREE", k.to_string());
    // just to emphasize that for vk, pk we don't need to know the value of `x`
    let circuit = MyCircuit { x: Value::known(Fr::random(OsRng)) };

    MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();

    let circuit = MyCircuit { x: Value::unknown() };
    // we generate a universal trusted setup of our own for testing
    let params = ParamsKZG::<Bn256>::setup(k, OsRng);

    let vk = keygen_vk(&params, &circuit).expect("vk should not fail");
    let pk = keygen_pk(&params, vk, &circuit).expect("pk should not fail");

    // now we generate an actual proof for a random input x
    let circuit = MyCircuit { x: Value::known(Fr::random(OsRng)) };

    let pf_time = start_timer!(|| "Creating proof");
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<_>>,
        _,
    >(&params, &pk, &[circuit], &[&[]], OsRng, &mut transcript)
    .expect("prover should not fail");
    let proof = transcript.finalize();
    end_timer!(pf_time);

    // verify the proof to make sure everything is ok
    let verifier_params = params.verifier_params();
    let strategy = SingleStrategy::new(&params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(verifier_params, pk.get_vk(), strategy, &[&[]], &mut transcript)
    .is_ok());
}
