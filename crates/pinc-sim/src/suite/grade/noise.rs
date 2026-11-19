//! The noise floor of the reference and the `is_better` margin.
//!
//! Each variant has four reference seeds. A draw picks, per variant, two different seeds (one for the scored set and
//! one for the noise set), pools both sets per scenario, scores the noise set against the scored set, takes the
//! geometric mean over scenarios `t`, and records the spread `exp(|ln t|) - 1`. The floor is the 95th percentile of
//! 20,000 spreads, rounded to four places. The generator is the reference one seeded with 7, and the draw order is
//! the order of the input (scenarios, then variants, then the two picks of a variant).
//!
//! Invariant: a variant with a missing seed is an error, never silently dropped from the pool.

use super::Terms;
use super::score::{headline, pool, round4, total};
use crate::reference::RefRng;

/// The number of draws.
pub const NOISE_DRAWS: usize = 20_000;

/// Why a noise floor cannot be computed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NoiseError {
    /// A reference run has no terms: `(scenario position, variant, seed slot)`.
    MissingTerms(usize, usize, usize),
    /// A draw had no comparable term in any scenario, so it has no spread.
    NoComparableTerms,
}

impl std::fmt::Display for NoiseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingTerms(s, v, k) => {
                write!(
                    f,
                    "noise floor: reference run without terms (scenario {s}, variant {v}, seed {k})"
                )
            }
            Self::NoComparableTerms => f.write_str("noise floor: a draw had no comparable terms"),
        }
    }
}

impl std::error::Error for NoiseError {}

/// The noise floor of the reference. `scenarios[s][v]` holds the four seeds' terms of variant `v` of the `s`-th
/// scenario, scenarios in the order of the reference matrix (first appearance), variants in matrix order, seeds in
/// the order matrix seed, its extra, noise seed, its extra.
///
/// # Errors
/// A seed without terms is [`NoiseError::MissingTerms`]; a draw with nothing to compare is
/// [`NoiseError::NoComparableTerms`].
pub fn noise_floor(scenarios: &[Vec<[Option<Terms>; 4]>]) -> Result<f64, NoiseError> {
    let mut variants: Vec<Vec<[Terms; 4]>> = Vec::with_capacity(scenarios.len());
    for (si, vs) in scenarios.iter().enumerate() {
        let mut row = Vec::with_capacity(vs.len());
        for (vi, v) in vs.iter().enumerate() {
            let mut seeds = [Terms::new(); 4];
            for (k, slot) in v.iter().enumerate() {
                match (slot, seeds.get_mut(k)) {
                    (Some(t), Some(dst)) => *dst = *t,
                    _ => return Err(NoiseError::MissingTerms(si, vi, k)),
                }
            }
            row.push(seeds);
        }
        variants.push(row);
    }
    let mut rng = RefRng::python(7);
    let mut spreads = Vec::with_capacity(NOISE_DRAWS);
    for _ in 0..NOISE_DRAWS {
        let mut scores = Vec::with_capacity(variants.len());
        for vs in &variants {
            let (mut a, mut b) = (Vec::with_capacity(vs.len()), Vec::with_capacity(vs.len()));
            for v in vs {
                let pick = rng.py().sample_indices(4, 2).unwrap_or_default();
                if let [i, j] = pick[..] {
                    a.push(v[i]);
                    b.push(v[j]);
                }
            }
            scores.push(headline(&pool(&b), &pool(&a)));
        }
        let t = total(&scores).ok_or(NoiseError::NoComparableTerms)?;
        spreads.push(t.ln().abs().exp() - 1.0);
    }
    spreads.sort_by(f64::total_cmp);
    let at = (0.95 * (NOISE_DRAWS - 1) as f64) as usize;
    Ok(round4(spreads[at]))
}

/// Whether `new` beats `old` by more than the margin `max(0.02, noise_floor)`. A non-finite `new` (an invalid
/// grading) never wins; a non-finite `old` always loses.
pub fn is_better(new: f64, old: f64, noise_floor: f64) -> bool {
    if !new.is_finite() {
        return false;
    }
    if !old.is_finite() {
        return true;
    }
    new < old * (1.0 - noise_floor.max(0.02))
}
