//! The score: term ratios against a reference term set, pooled per scenario, combined by geometric means.
//!
//! `ratio(term) = (candidate + floor) / (reference + floor)` with additive floors, so a near-zero reference value
//! cannot explode a ratio. A scenario's score is the weighted geometric mean of its ratios (weights renormalised
//! over the terms present on both sides); the total is the geometric mean over scenarios. Lower is better and the
//! reference scores 1.0. The runs of one scenario are pooled by averaging each term over the runs where it exists.
//!
//! Invariant: the sums and the order of the weights follow the reference code term by term, so a score reproduces
//! the reference value to the last digit the arithmetic allows; the total and the group totals exist only when every
//! scenario was scored from all of its runs.

use super::{TERMS, Terms};

const MS: f64 = 1_000_000.0;

/// The weight of each term, in [`TERMS`] order.
pub const WEIGHTS: [(&str, f64); 21] = [
    ("L1", 0.05),
    ("L2", 0.07),
    ("L3", 0.05),
    ("L4", 0.04),
    ("L5", 0.04),
    ("T1", 0.08),
    ("T2", 0.04),
    ("T3", 0.03),
    ("T4", 0.05),
    ("C1", 0.05),
    ("C2", 0.05),
    ("C3", 0.05),
    ("C4", 0.04),
    ("B1", 0.09),
    ("B2", 0.05),
    ("B3", 0.04),
    ("B4", 0.03),
    ("B5", 0.03),
    ("R1", 0.05),
    ("R2", 0.05),
    ("R3", 0.02),
];

/// The score groups and their terms.
pub const GROUPS: [(&str, &[&str]); 5] = [
    ("LATENCY", &["L1", "L2", "L3", "L4", "L5"]),
    ("THROUGHPUT", &["T1", "T2", "T3", "T4"]),
    ("CONTINUATION", &["C1", "C2", "C3", "C4"]),
    ("COST", &["B1", "B2", "B3", "B4", "B5"]),
    ("RESOURCES", &["R1", "R2", "R3"]),
];

/// The additive floor of a term: latency 1 ms; T1/T2 1 ms per MiB (ns per byte); T4 0.001; C1 64 B; C3 and C4 0.01;
/// B1 64 B per MiB; B2 16 B per item; B3 64 B/h; B4 1/h; B5 0.001; R1 1 ns/B; R2 1 KiB; R3 256 B.
pub fn floor(term: &str) -> f64 {
    match term {
        "T1" | "T2" => MS / f64::from(1u32 << 20),
        "T4" | "B5" => 0.001,
        "C1" | "B3" => 64.0,
        "C3" | "C4" => 0.01,
        "B1" => 64.0 / f64::from(1u32 << 20),
        "B2" => 16.0,
        "B4" | "R1" => 1.0,
        "R2" => 1024.0,
        "R3" => 256.0,
        _ => MS,
    }
}

/// The weight of `term` (0 for an unknown name).
pub fn weight(term: &str) -> f64 {
    WEIGHTS.iter().find(|(t, _)| *t == term).map_or(0.0, |&(_, w)| w)
}

/// Averages every term over the runs of one scenario (absent if absent everywhere).
pub fn pool(runs: &[Terms]) -> Terms {
    let mut out = Terms::new();
    for (i, slot) in out.v.iter_mut().enumerate() {
        let (mut sum, mut n) = (0.0, 0usize);
        for v in runs.iter().filter_map(|r| r.v[i]) {
            sum += v;
            n += 1;
        }
        *slot = (n != 0).then(|| sum / n as f64);
    }
    out
}

/// The ratios of the terms present on both sides, in [`TERMS`] order.
pub fn ratios(cand: &Terms, reference: &Terms) -> Vec<(&'static str, f64)> {
    TERMS
        .iter()
        .filter_map(|&t| match (cand.get(t), reference.get(t)) {
            (Some(c), Some(r)) => Some((t, (c + floor(t)) / (r + floor(t)))),
            _ => None,
        })
        .collect()
}

/// The weighted geometric mean of the ratios of `terms` (all ratios when `None`), or `None` when there are none.
pub fn wgeo(r: &[(&str, f64)], terms: Option<&[&str]>) -> Option<f64> {
    let keys: Vec<(&str, f64)> = match terms {
        None => r.to_vec(),
        Some(ts) => ts
            .iter()
            .filter_map(|t| r.iter().find(|(k, _)| k == t).copied())
            .collect(),
    };
    if keys.is_empty() {
        return None;
    }
    let wsum: f64 = keys.iter().map(|(t, _)| weight(t)).sum();
    let lsum: f64 = keys.iter().map(|(t, v)| weight(t) * v.max(1e-12).ln()).sum();
    Some((lsum / wsum).exp())
}

/// The headline of [`scenario_score`] without building the ratio list: the same sums in the same order.
pub fn headline(cand: &Terms, reference: &Terms) -> Option<f64> {
    let (mut wsum, mut lsum) = (0.0, 0.0);
    let mut any = false;
    for (&(t, w), ((_, c), (_, r))) in WEIGHTS.iter().zip(cand.iter().zip(reference.iter())) {
        if let (Some(c), Some(r)) = (c, r) {
            any = true;
            wsum += w;
            lsum += w * ((c + floor(t)) / (r + floor(t))).max(1e-12).ln();
        }
    }
    any.then(|| (lsum / wsum).exp())
}

/// A scenario's score and its ratios: the candidate's pooled terms against the reference's.
pub fn scenario_score(cand: &Terms, reference: &Terms) -> (Option<f64>, Vec<(&'static str, f64)>) {
    let r = ratios(cand, reference);
    (wgeo(&r, None), r)
}

/// `round(x, 4)` as Python does (correctly rounded, ties to even on the exact binary value).
pub fn round4(x: f64) -> f64 {
    format!("{x:.4}").parse().unwrap_or(x)
}

/// The group scores of a ratio set, each rounded to four places.
pub fn group_ratios(r: &[(&str, f64)]) -> Vec<(&'static str, Option<f64>)> {
    GROUPS
        .iter()
        .map(|&(g, ts)| (g, wgeo(r, Some(ts)).map(round4)))
        .collect()
}

/// The geometric mean of the present scores, or `None` when there are none.
pub fn total(scores: &[Option<f64>]) -> Option<f64> {
    let vals: Vec<f64> = scores.iter().flatten().copied().collect();
    if vals.is_empty() {
        return None;
    }
    Some((vals.iter().map(|s| s.max(1e-12).ln()).sum::<f64>() / vals.len() as f64).exp())
}

/// The runs of one scenario: the candidate's, the reference's, and how many candidate runs make the scenario whole.
#[derive(Clone, Debug)]
pub struct ScenarioRuns {
    /// The scenario id.
    pub id: String,
    /// The candidate's terms, one entry per finished run.
    pub cand: Vec<Terms>,
    /// The reference's terms on the same seeds.
    pub reference: Vec<Terms>,
    /// How many runs the scenario has in the matrix; fewer finished runs leave the scenario unscored.
    pub runs_expected: usize,
}

/// One scenario's result.
#[derive(Clone, Debug)]
pub struct ScenarioScore {
    /// The scenario id.
    pub id: String,
    /// The candidate's pooled terms.
    pub terms: Terms,
    /// The score (unrounded), `None` when no term is present on both sides.
    pub score: Option<f64>,
    /// The ratios behind it.
    pub ratios: Vec<(&'static str, f64)>,
    /// The group scores, rounded to four places.
    pub groups: Vec<(&'static str, Option<f64>)>,
    /// The scenario has no score or not all of its runs finished.
    pub unscored: bool,
}

/// The score over all scenarios.
#[derive(Clone, Debug)]
pub struct ScoreReport {
    /// Per scenario, in input order.
    pub scenarios: Vec<ScenarioScore>,
    /// The ids of the unscored scenarios.
    pub unscored: Vec<String>,
    /// The geometric mean of the scenario scores; `None` while any scenario is unscored.
    pub total: Option<f64>,
    /// The group totals (geometric mean of the scenarios' rounded group scores); `None` while any is unscored.
    pub groups: Vec<(&'static str, Option<f64>)>,
}

impl ScoreReport {
    /// The total rounded to four places, as the reference reports it.
    pub fn total_rounded(&self) -> Option<f64> {
        self.total.map(round4)
    }
}

/// Scores a candidate against a reference over the given scenarios.
pub fn score(scenarios: &[ScenarioRuns]) -> ScoreReport {
    let mut out = Vec::new();
    for s in scenarios {
        let cand = pool(&s.cand);
        let (sc, r) = scenario_score(&cand, &pool(&s.reference));
        let unscored = sc.is_none() || s.cand.len() < s.runs_expected;
        out.push(ScenarioScore {
            id: s.id.clone(),
            terms: cand,
            score: sc,
            groups: group_ratios(&r),
            ratios: r,
            unscored,
        });
    }
    let unscored: Vec<String> = out.iter().filter(|s| s.unscored).map(|s| s.id.clone()).collect();
    let scores: Vec<Option<f64>> = out.iter().map(|s| s.score).collect();
    let total_all = unscored.is_empty().then(|| total(&scores)).flatten();
    let groups = GROUPS
        .iter()
        .enumerate()
        .map(|(gi, &(g, _))| {
            let vals: Vec<Option<f64>> = out
                .iter()
                .map(|s| s.groups.get(gi).and_then(|x| x.1))
                .filter(|v| v.is_some_and(|x| x != 0.0))
                .collect();
            (
                g,
                if unscored.is_empty() {
                    total(&vals).map(round4)
                } else {
                    None
                },
            )
        })
        .collect();
    ScoreReport {
        scenarios: out,
        unscored,
        total: total_all,
        groups,
    }
}
