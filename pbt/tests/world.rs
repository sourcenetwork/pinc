//! The `world` property: generated `pinc-sim` networks of the three shapes under a generated application script. The
//! worlds, the application and the oracles are in `world_harness` (shared with `repro_world.rs`), whose module doc
//! says where every expectation comes from.
#![allow(clippy::unwrap_used, clippy::panic)]

mod world_harness;

use ephyra::check_generator;
use world_harness::{Spec, prop};

fn big_stack(f: impl FnOnce() + Send + 'static) {
    let r = std::thread::Builder::new().stack_size(256 << 20).spawn(f).unwrap().join();
    if let Err(e) = r {
        std::panic::resume_unwind(e);
    }
}

#[test]
fn every_shape_of_network_reaches_every_pair_and_keeps_every_byte() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(6)
            .name("every_shape_of_network_reaches_every_pair_and_keeps_every_byte");
        ephyra::check(&config, ephyra::any::<Spec>(), |s: Spec| prop(&s)).assert_passed();
    });
}

#[test]
fn the_world_spec_generator_stays_in_support() {
    let ok = |s: &Spec| (2..=6).contains(&s.apps.len()) && (1..=2).contains(&s.dedicated) && s.loss_pm <= 30;
    check_generator(&ephyra::Config::default().tests(300), ephyra::any::<Spec>(), move |s: &Spec| ok(s)).assert_passed();
}
