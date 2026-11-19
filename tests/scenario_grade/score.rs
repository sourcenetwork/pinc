//! The score, the noise floor and `is_better`.

use pinc_sim::suite::grade::{
    NoiseError, ScenarioRuns, Terms, is_better, noise_floor, pool, scenario_score, score, total, with_fair,
};

use crate::common::*;

// ----------------------------------------------------------------------------------------------- score

const REFERENCE_TERMS: &str = include_str!("../data/reference_terms.txt");

fn parse(kind_wanted: &str, fair: bool) -> Vec<(String, usize, usize, Terms)> {
    let mut out: Vec<(String, usize, usize, Terms)> = Vec::new();
    for ln in REFERENCE_TERMS.lines() {
        let mut it = ln.split_whitespace();
        let (kind, sid) = (it.next().unwrap(), it.next().unwrap());
        let (v, slot): (usize, usize) = (it.next().unwrap().parse().unwrap(), it.next().unwrap().parse().unwrap());
        if kind != kind_wanted {
            continue;
        }
        let mut t = Terms::new();
        for kv in it {
            let (k, x) = kv.split_once('=').unwrap();
            t.set(k, Some(x.parse().unwrap()));
        }
        out.push((sid.to_owned(), v, slot, t));
    }
    let _ = fair;
    out
}

/// The reference's runs: current terms, or with the fair rule replacing L1, L2, L4 and T4.
fn reference(fair: bool) -> Vec<(String, usize, usize, Terms)> {
    let cur = parse("cur", false);
    if !fair {
        return cur;
    }
    let f = parse("fair", true);
    cur.into_iter()
        .zip(f)
        .map(|((s, v, k, c), (s2, v2, k2, fr))| {
            assert_eq!((&s, v, k), (&s2, v2, k2));
            (s, v, k, with_fair(&c, &fr))
        })
        .collect()
}

fn scenario_ids(data: &[(String, usize, usize, Terms)]) -> Vec<String> {
    let mut ids: Vec<String> = Vec::new();
    for (s, ..) in data {
        if !ids.contains(s) {
            ids.push(s.clone());
        }
    }
    ids
}

fn noise_input(data: &[(String, usize, usize, Terms)]) -> Vec<Vec<[Option<Terms>; 4]>> {
    scenario_ids(data)
        .iter()
        .map(|sid| {
            let nv = data.iter().filter(|d| &d.0 == sid).map(|d| d.1).max().unwrap() + 1;
            (0..nv)
                .map(|v| {
                    let mut seeds = [None; 4];
                    for (_, _, k, t) in data.iter().filter(|d| &d.0 == sid && d.1 == v) {
                        seeds[*k] = Some(*t);
                    }
                    seeds
                })
                .collect()
        })
        .collect()
}

#[test]
fn the_noise_floor_reproduces_the_reference_value() {
    // 0.1264: the value the reference harness stored with this data
    let cur = noise_floor(&noise_input(&reference(false))).unwrap();
    assert!((cur - 0.1264).abs() < 1e-4, "{cur}");
}

#[test]
fn the_fair_noise_floor_reproduces_the_reference_value() {
    // 0.1096, likewise
    let fair = noise_floor(&noise_input(&reference(true))).unwrap();
    assert!((fair - 0.1096).abs() < 1e-4, "{fair}");
}

#[test]
fn the_noise_floor_on_a_small_fabricated_cache_matches_the_reference_draws() {
    let fab = |s: usize, v: usize, k: usize| {
        Terms::from_pairs(&[
            ("L1", (1 + s + v + k) as f64 * 1e8),
            ("B1", 5.0 + 0.5 * k as f64 + v as f64),
            ("R2", 1e5 * (1 + k) as f64 + 1000.0 * s as f64),
        ])
    };
    let input: Vec<Vec<[Option<Terms>; 4]>> = [(0, 2), (1, 1), (2, 3)]
        .into_iter()
        .map(|(s, nv)| (0..nv).map(|v| std::array::from_fn(|k| Some(fab(s, v, k)))).collect())
        .collect();
    // recorded from the reference procedure (random.Random(7), 20000 draws, sample(range(4), 2) per variant)
    let got = noise_floor(&input).unwrap();
    assert!((got - 0.4495).abs() < 1e-12, "{got}");
}

#[test]
fn the_noise_floor_refuses_a_missing_seed() {
    let t = Terms::from_pairs(&[("L1", 1.0)]);
    let input = vec![vec![[Some(t), Some(t), None, Some(t)]]];
    assert_eq!(noise_floor(&input), Err(NoiseError::MissingTerms(0, 0, 2)));
}

#[test]
fn is_better_needs_the_margin() {
    assert!(is_better(0.80, 1.0, 0.1264));
    assert!(!is_better(0.88, 1.0, 0.1264), "within the noise floor");
    assert!(is_better(0.97, 1.0, 0.0), "the margin is at least 2 percent");
    assert!(!is_better(0.99, 1.0, 0.0));
    assert!(!is_better(f64::INFINITY, 1.0, 0.0), "an invalid grading never wins");
    assert!(
        is_better(1.0, f64::INFINITY, 0.1264),
        "anything valid beats an invalid incumbent"
    );
    assert!(!is_better(f64::NAN, 1.0, 0.0));
}

fn runs_of(data: &[(String, usize, usize, Terms)], sid: &str, slot: usize) -> Vec<Terms> {
    data.iter().filter(|d| d.0 == sid && d.2 == slot).map(|d| d.3).collect()
}

#[test]
fn scores_match_the_reference_harness() {
    // candidate = the second seed of every variant, reference = the first; expected values from the reference code
    let expect_cur = [
        ("S2", 0.7701432120184228),
        ("S3", 0.8639545521814097),
        ("S5", 0.9820721001420891),
        ("S11", 1.0746462330411681),
        ("S1", 0.8420837224267979),
        ("S4", 0.6376791854007365),
        ("S6", 0.9303922751320121),
        ("S10", 1.426730240661177),
        ("S12", 0.6896599243455214),
        ("S13", 0.9745170187790724),
        ("S14", 0.9566972677471298),
        ("S15", 1.2909353854053012),
    ];
    let expect_fair = [
        ("S2", 0.8604823963662706),
        ("S12", 0.9790612732499561),
        ("S15", 1.2623106861170648),
    ];
    for (fair, total_want, groups_want) in [
        (false, 0.9294192958464547, [0.8069, 1.0902, 1.0279, 0.9548, 0.9575]),
        (true, 0.964223179360874, [0.9109, 1.0902, 1.0279, 0.9548, 0.9575]),
    ] {
        let data = reference(fair);
        let runs: Vec<ScenarioRuns> = scenario_ids(&data)
            .into_iter()
            .map(|id| {
                let n = runs_of(&data, &id, 1).len();
                ScenarioRuns {
                    cand: runs_of(&data, &id, 1),
                    reference: runs_of(&data, &id, 0),
                    runs_expected: n,
                    id,
                }
            })
            .collect();
        let rep = score(&runs);
        assert!(rep.unscored.is_empty());
        for s in &rep.scenarios {
            let list: &[(&str, f64)] = if fair { &expect_fair } else { &expect_cur };
            if let Some((_, want)) = list.iter().find(|(id, _)| *id == s.id) {
                assert!(close(s.score.unwrap(), *want), "{} {fair}: {:?}", s.id, s.score);
            }
        }
        assert!(close(rep.total.unwrap(), total_want), "{fair}: {:?}", rep.total);
        for ((g, v), want) in rep.groups.iter().zip(groups_want) {
            assert_eq!(*v, Some(want), "{g} {fair}");
        }
        // S14 has no throughput term on either side: that group is absent, not zero
        let s14 = rep.scenarios.iter().find(|s| s.id == "S14").unwrap();
        assert_eq!(s14.groups.iter().find(|g| g.0 == "THROUGHPUT").unwrap().1, None);
    }
}

#[test]
fn the_reference_scores_one_against_itself_and_floors_bite() {
    let data = reference(false);
    let runs: Vec<ScenarioRuns> = scenario_ids(&data)
        .into_iter()
        .map(|id| {
            let r = runs_of(&data, &id, 0);
            ScenarioRuns {
                id,
                cand: r.clone(),
                reference: r.clone(),
                runs_expected: r.len(),
            }
        })
        .collect();
    let rep = score(&runs);
    assert_eq!(rep.total, Some(1.0));
    assert!(rep.scenarios.iter().all(|s| s.score == Some(1.0)));
    assert!(
        rep.groups
            .iter()
            .all(|g| g.1 == Some(1.0) || g.1.is_none() || g.1 == Some(1.0))
    );
    // a floor: against a zero reference, a candidate of 1 ms on L1 scores (1 ms + 1 ms) / (0 + 1 ms) = 2
    let (sc, ratios) = scenario_score(&Terms::from_pairs(&[("L1", 1e6)]), &Terms::from_pairs(&[("L1", 0.0)]));
    assert!(close(sc.unwrap(), 2.0));
    assert_eq!(ratios, vec![("L1", 2.0)]);
    // R2: floor 1 KiB
    let (sc, _) = scenario_score(
        &Terms::from_pairs(&[("R2", 1024.0)]),
        &Terms::from_pairs(&[("R2", 0.0)]),
    );
    assert!(close(sc.unwrap(), 2.0));
}

#[test]
fn weighted_geometric_mean_renormalises_over_present_terms() {
    // L1 (weight 0.05) at ratio 4 and B1 (0.09) at ratio 1 -> exp(0.05 ln 4 / 0.14)
    let c = Terms::from_pairs(&[("L1", 4e6 - 1e6), ("B1", 1.0)]);
    let r = Terms::from_pairs(&[("L1", 0.0), ("B1", 1.0), ("R2", 5.0)]);
    let (sc, ratios) = scenario_score(&c, &r);
    assert_eq!(ratios.len(), 2, "R2 is absent on one side and dropped");
    assert!(close(sc.unwrap(), (0.05 * 4.0f64.ln() / 0.14).exp()));
    assert_eq!(scenario_score(&Terms::new(), &r).0, None);
}

#[test]
fn pooling_averages_each_term_over_the_runs_that_have_it() {
    let a = Terms::from_pairs(&[("L1", 1.0), ("B1", 2.0)]);
    let b = Terms::from_pairs(&[("L1", 3.0)]);
    let p = pool(&[a, b]);
    assert_eq!(p.get("L1"), Some(2.0));
    assert_eq!(p.get("B1"), Some(2.0));
    assert_eq!(p.get("R2"), None);
    assert_eq!(pool(&[]).get("L1"), None);
}

#[test]
fn an_unfinished_scenario_blocks_the_total() {
    let t = Terms::from_pairs(&[("L1", 1e6)]);
    let mk = |id: &str, finished: usize| ScenarioRuns {
        id: id.to_owned(),
        cand: vec![t; finished],
        reference: vec![t; 2],
        runs_expected: 2,
    };
    let rep = score(&[mk("S2", 2), mk("S3", 1)]);
    assert_eq!(rep.unscored, vec!["S3".to_owned()]);
    assert_eq!(rep.total, None);
    assert!(rep.groups.iter().all(|g| g.1.is_none()));
    let rep = score(&[mk("S2", 2), mk("S3", 2)]);
    assert_eq!(rep.total, Some(1.0));
    assert_eq!(rep.total_rounded(), Some(1.0));
    assert_eq!(total(&[]), None);
    assert_eq!(total(&[None, Some(4.0), Some(1.0)]), Some(2.0));
}
