//! `pinc-sim`: the scenario suite's runs are a function of the world, the driver and the layers, and nothing else.
//!
//! Where the expected behaviour comes from:
//! - `pinc_sim::suite::world` (world/mod.rs): "generation is a pure function of its arguments (no clock, no global
//!   state)", so generating twice gives the same world.
//! - The simulator is the project's deterministic network simulator: the same world, driver and layers give the same
//!   run, so the same encoded result and the same trace hash. `suite::run::run` says "Every run happens on one
//!   long-lived thread ... which also keeps the connection tables of finished runs for the next one": a run in
//!   between, of another world, must not change the next run of the first one (the metamorphic check here).
//! - `suite::run::codec::decode`: "Decodes the text made by `encode`", so encoding the decoded result gives the text
//!   back.
//!
//! The scenario durations are shortened (`duration_s`) so a case takes seconds; the scenario's own parameters are
//! otherwise those of `public_params`.

use ephyra::{check_generator, gens};
use pinc_sim::Driver;
use pinc_sim::suite::run::{LayerSet, codec, run};
use pinc_sim::suite::world::{Param, Params, SCENARIOS, generate};

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Pick {
    #[ephyra(gen = gens::int(0usize..=11))]
    scenario: usize,
    #[ephyra(gen = gens::frequency(vec![(3, gens::int(0u64..=8).boxed()), (1, gens::int(0u64..=u64::MAX).boxed())]))]
    seed: u64,
    #[ephyra(gen = gens::int(5i64..=30))]
    duration_s: i64,
    reference: bool,
    node_layers: bool,
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Case {
    first: Pick,
    between: Pick,
}

fn result(p: &Pick) -> Option<String> {
    let id = SCENARIOS[p.scenario];
    let mut params = Params::new();
    params.insert("duration_s".to_owned(), Param::Int(p.duration_s));
    let world = generate(id, &params, p.seed).ok()?;
    let again = generate(id, &params, p.seed).ok()?;
    assert!(format!("{world:?}") == format!("{again:?}"), "{id} seed {}: two generations differ", p.seed);
    let driver = if p.reference { Driver::Reference } else { Driver::Pinc };
    let layers = if p.node_layers { LayerSet::NODE } else { LayerSet::NONE };
    let r = run(&world, driver, layers);
    assert!(r.is_ok(), "{id} seed {}: the run failed: {:?}", p.seed, r.as_ref().err());
    let r = r.ok()?;
    let text = codec::encode(&r);
    let back = codec::decode(&text);
    assert!(back.is_ok(), "{id}: decode refused what encode wrote: {:?}", back.as_ref().err());
    let again = back.map(|b| codec::encode(&b)).unwrap_or_default();
    assert!(again == text, "{id}: encode(decode(text)) differs from text");
    Some(format!("{}\n{text}", r.trace_hash))
}

fn prop(c: &Case) -> ephyra::TestResult {
    let a = result(&c.first);
    // a world the scenario's generator refuses for these overrides is not a case
    ephyra::assume!(a.is_some());
    let a = a.unwrap_or_default();
    let _ = result(&c.between);
    let b = result(&c.first).unwrap_or_default();
    if a != b {
        let line = a.lines().zip(b.lines()).position(|(x, y)| x != y);
        let at = line.and_then(|l| a.lines().nth(l)).unwrap_or("").to_owned();
        let bt = line.and_then(|l| b.lines().nth(l)).unwrap_or("").to_owned();
        panic!("the same run gave another result after a run in between: line {line:?}: {at:?} then {bt:?}");
    }
    ephyra::TestResult::Pass
}

#[test]
fn a_run_depends_only_on_its_world_driver_and_layers() {
    let h = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let config = ephyra::Config::default()
                .tests(6)
                .name("a_run_depends_only_on_its_world_driver_and_layers");
            ephyra::check(&config, ephyra::any::<Case>(), |c: Case| prop(&c)).assert_passed();
        })
        .unwrap();
    if let Err(e) = h.join() {
        std::panic::resume_unwind(e);
    }
}

#[test]
fn the_sim_case_generator_stays_in_support() {
    let ok = |p: &Pick| p.scenario < SCENARIOS.len() && (5..=30).contains(&p.duration_s);
    check_generator(&ephyra::Config::default().tests(200), ephyra::any::<Case>(), move |c: &Case| ok(&c.first) && ok(&c.between))
        .assert_passed();
}
