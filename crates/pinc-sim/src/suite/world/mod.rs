//! World generation: the reference harness's scenarios, reproduced bit-exactly from a seed.
//!
//! [`generate`] builds the world of one scenario from its parameter overrides and a seed, [`add_adversary`] adds the
//! hidden adversary, [`variants`] lists the 96 hidden-matrix entries and [`build`] turns one into a finished world the
//! way the reference runner does. Every random draw happens in the order, and with the float arithmetic, of the
//! reference generators, so a world is identical to the one the reference harness builds for the same inputs; the
//! `canon` module writes the canonical text that proves it against vectors made by the reference itself.
//!
//! Invariants: generation is a pure function of its arguments (no clock, no global state); it never panics, and a
//! request the reference generator would reject (an empty population to draw from, a missing parameter) is a
//! [`WorldError`].

// The generators keep the reference's one-letter names (a, z, t, i) so a reader can lay the two side by side.
// Each generator is a port of one reference function and is kept whole so that it reads against its source.
#![allow(clippy::many_single_char_names, clippy::too_many_lines)]

mod adversary;
mod build;
pub mod canon;
mod error;
mod large;
mod matrix;
mod mixed;
pub mod model;
mod p1;
mod p1_capacity;
mod params;
mod s14;
mod slice;

pub use adversary::{AdversaryCfg, add_adversary, adversary_for};
pub use error::WorldError;
pub use matrix::{SeedSet, Variant, build, variants};
pub use model::{Param, Params, World};
pub use params::public_params;

/// The scenario ids this module generates, in numeric order.
pub const SCENARIOS: [&str; 12] = [
    "S1", "S2", "S3", "S4", "S5", "S6", "S10", "S11", "S12", "S13", "S14", "S15",
];

/// Generates the world of scenario `id` for `seed`. `params` are overrides applied over [`public_params`], exactly as
/// the reference does with `p = dict(PUBLIC[sid]); p.update(params)`. The adversary is not added; see
/// [`add_adversary`].
///
/// # Errors
/// [`WorldError::UnknownScenario`] for an id that is not in [`SCENARIOS`], and the errors of the generator when the
/// parameters leave it with nothing to draw from.
pub fn generate(id: &str, params: &Params, seed: u64) -> Result<World, WorldError> {
    if !SCENARIOS.contains(&id) {
        return Err(WorldError::UnknownScenario(id.to_string()));
    }
    let mut p = public_params(id);
    p.extend(params.iter().map(|(k, v)| (k.clone(), v.clone())));
    match id {
        "S14" => s14::generate(p, seed),
        "S1" | "S4" | "S6" | "S10" | "S12" | "S13" | "S15" => p1::generate(id, p, seed),
        _ => slice::generate(id, p, seed),
    }
}

#[cfg(test)]
#[allow(clippy::expect_used)]
mod tests {
    use super::params::{int, table};
    use super::*;

    #[test]
    fn generation_is_deterministic_and_seed_dependent() {
        for id in SCENARIOS {
            let small = table(vec![("n_items", int(200))]);
            let a = generate(id, &small, 5).expect("generates");
            assert_eq!(a, generate(id, &small, 5).expect("generates"), "{id}");
            assert_ne!(a, generate(id, &small, 6).expect("generates"), "{id}");
        }
    }

    #[test]
    fn overrides_win_over_the_public_shape() {
        let w = generate("S5", &table(vec![("n_home", int(2)), ("n_mobile", int(1))]), 1).expect("generates");
        assert_eq!((w.homes.len(), w.mobiles.len()), (2, 1));
        assert_eq!(w.params.get("n_home"), Some(&Param::Int(2)));
        assert!(w.params.contains_key("fetch_sizes"), "unrelated public parameters stay");
    }

    #[test]
    fn env_and_intents_are_sorted() {
        let w = generate("S3", &Params::new(), 3).expect("generates");
        assert!(w.env.windows(2).all(|p| (p[0].t, p[0].kind) <= (p[1].t, p[1].kind)));
        assert!(w.intents.windows(2).all(|p| (p[0].t, p[0].node) <= (p[1].t, p[1].node)));
    }

    #[test]
    fn a_workload_with_nobody_to_churn_is_an_error() {
        let p = table(vec![("n_home", int(0)), ("n_mobile", int(0)), ("n_late_join", int(1))]);
        assert!(matches!(generate("S2", &p, 1), Err(WorldError::Empty(_))));
    }

    #[test]
    fn a_parameter_of_the_wrong_type_is_named() {
        let p = table(vec![("n_home", super::params::float(2.0))]);
        assert_eq!(
            generate("S2", &p, 1),
            Err(WorldError::BadParam {
                key: "n_home".into(),
                want: "an integer"
            })
        );
    }
}
