//! The hidden scenario matrix: 24 variants of the twelve scenarios, their 24 noise-floor twins and the two groups of
//! extra seeds, 96 worlds in all, and the construction of a finished world from one of them the way the reference
//! runner does (generate, then add the hidden adversary with the same seed).
//!
//! Invariant: the parameter overrides are the reference matrix's, value for value; the vector test compares the
//! merged parameters of every variant, so a transcription slip fails there.

use super::adversary::{add_adversary, adversary_for};
use super::model::Params;
use super::params::{flag, float, int, ints, rf, ri, strs, table};
use super::{World, WorldError, generate};

const MIB: i64 = 1024 * 1024;
const GIB: i64 = 1024 * MIB;
const TIB: i64 = 1024 * GIB;

/// Which group of seeds a variant belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SeedSet {
    /// The scored seed of the variant.
    Matrix,
    /// The noise-floor seed (disjoint from the matrix seeds).
    Noise,
    /// The matrix seed plus one (reference-only).
    Extra1,
    /// The noise seed plus fifty (reference-only).
    Extra2,
}

/// One hidden-matrix entry.
#[derive(Clone, Debug, PartialEq)]
pub struct Variant {
    /// The scenario id.
    pub id: &'static str,
    /// Which of the scenario's two variants this is (1 or 2).
    pub variant: u8,
    /// The group of seeds.
    pub set: SeedSet,
    /// The generator seed.
    pub seed: u64,
    /// Parameter overrides over the public shape.
    pub params: Params,
}

/// The matrix entries `(scenario, overrides, seed)`, in the reference order.
fn matrix() -> Vec<(&'static str, Params, u64)> {
    vec![
        (
            "S2",
            table(vec![
                ("n_cloud", int(4)),
                ("n_home", int(14)),
                ("n_mobile", int(12)),
                ("duration_s", int(540)),
                ("active_s", ri(12, 360)),
                ("idle_s", ri(440, 540)),
                ("publish_every_s", int(22)),
                ("home_loss", float(0.004)),
                ("mobile_loss", float(0.015)),
                ("burst_ms", ri(8, 80)),
                ("v6_share", float(0.40)),
                ("n_echo", int(36)),
                ("n_docsync", int(26)),
            ]),
            90211,
        ),
        (
            "S2",
            table(vec![
                ("n_cloud", int(3)),
                ("n_home", int(12)),
                ("n_mobile", int(16)),
                ("duration_s", int(540)),
                ("active_s", ri(12, 360)),
                ("idle_s", ri(440, 540)),
                ("push_every_s", int(12)),
                ("mobile_delay_ms", ri(25, 70)),
                ("v6_open_share", float(0.3)),
                ("crash_frac", float(0.12)),
                ("n_fetch", int(5)),
            ]),
            77345,
        ),
        (
            "S3",
            table(vec![
                ("n_home", int(3)),
                ("n_mobile", int(14)),
                ("duration_s", int(540)),
                ("active_s", ri(10, 380)),
                ("idle_s", ri(440, 540)),
                ("mobile_loss", rf(0.02, 0.08)),
                ("mobile_delay_ms", ri(30, 250)),
                ("handover_every_s", ri(50, 110)),
                ("suspend_s", ri(8, 35)),
            ]),
            31337,
        ),
        (
            "S3",
            table(vec![
                ("n_home", int(4)),
                ("n_mobile", int(12)),
                ("duration_s", int(540)),
                ("active_s", ri(10, 380)),
                ("idle_s", ri(440, 540)),
                ("mobile_loss", rf(0.01, 0.06)),
                ("burst_ms", ri(30, 150)),
                ("rebind_every_s", ri(60, 120)),
                ("fetch_sizes", ri(2 * MIB, 5 * MIB)),
            ]),
            55021,
        ),
        (
            "S5",
            table(vec![
                ("n_home", int(10)),
                ("n_mobile", int(10)),
                ("duration_s", int(420)),
                ("active_s", ri(10, 290)),
                ("idle_s", ri(340, 420)),
                ("n_echo", int(50)),
                ("fetch_sizes", ri(256 * 1024, 3 * MIB)),
            ]),
            12011,
        ),
        (
            "S5",
            table(vec![
                ("n_cloud", int(3)),
                ("n_home", int(8)),
                ("n_mobile", int(12)),
                ("duration_s", int(420)),
                ("active_s", ri(10, 290)),
                ("idle_s", ri(340, 420)),
                ("mobile_loss", float(0.02)),
                ("v6_open_share", float(0.0)),
            ]),
            44417,
        ),
        (
            "S11",
            table(vec![
                ("full_sizes", ints(&[2 * MIB, 6 * MIB, 20 * MIB])),
                ("multi_size", int(24 * MIB)),
                ("range_sizes", ints(&[3 * GIB, TIB])),
                ("stream_rate_bps", int(6_000_000)),
            ]),
            66001,
        ),
        (
            "S11",
            table(vec![
                ("n_home", int(5)),
                ("n_mobile", int(3)),
                ("full_sizes", ints(&[MIB, 12 * MIB, 28 * MIB])),
                ("multi_size", int(16 * MIB)),
                ("n_multi_prov", int(2)),
                ("range_sizes", ints(&[64 * GIB, TIB])),
                ("home_loss", float(0.005)),
            ]),
            23456,
        ),
        (
            "S1",
            table(vec![
                ("n_server", int(17)),
                ("bulk_sizes", ints(&[256 * MIB])),
                ("server_delay_us", ri(5, 20)),
                ("publish_every_s", int(6)),
                ("n_echo", int(36)),
            ]),
            81401,
        ),
        (
            "S1",
            table(vec![
                ("n_server", int(21)),
                ("bulk_sizes", ints(&[512 * MIB])),
                ("server_bps", ri(25_000_000_000, 100_000_000_000)),
                ("n_push_pairs", int(8)),
                ("n_docsync", int(40)),
            ]),
            81877,
        ),
        (
            "S4",
            table(vec![
                ("n_home", int(12)),
                ("n_mobile", int(6)),
                ("tcp_idle_s", ri(30, 60)),
                ("portal_share", float(0.5)),
                ("fw_reject", flag(true)),
            ]),
            84121,
        ),
        (
            "S4",
            table(vec![
                ("n_home", int(8)),
                ("n_mobile", int(10)),
                ("tls_only", flag(true)),
                ("hostile_share", float(0.8)),
                ("tcp_idle_s", ri(30, 90)),
                ("portal_s", ri(30, 120)),
            ]),
            84733,
        ),
        (
            "S6",
            table(vec![
                ("n_rural", int(8)),
                ("n_geo", int(3)),
                ("n_2g", int(5)),
                ("loss", rf(0.02, 0.05)),
                ("n_echo", int(20)),
            ]),
            86017,
        ),
        (
            "S6",
            table(vec![
                ("n_rural", int(4)),
                ("n_geo", int(8)),
                ("n_2g", int(2)),
                ("geo_delay_ms", ri(300, 350)),
                ("fetch_sizes", ri(32 * 1024, 128 * 1024)),
                ("publish_every_s", int(45)),
            ]),
            86551,
        ),
        (
            "S10",
            table(vec![
                ("n_browser", int(18)),
                ("n_home", int(0)),
                ("browser_mobile_share", float(0.5)),
                ("n_echo", int(36)),
            ]),
            81003,
        ),
        (
            "S10",
            table(vec![
                ("n_cloud", int(4)),
                ("n_browser", int(12)),
                ("n_home", int(4)),
                ("crash_frac", float(0.15)),
                ("n_docsync", int(30)),
            ]),
            81077,
        ),
        (
            "S12",
            table(vec![
                ("n_denied", int(6)),
                ("n_liar_fetch", int(5)),
                ("sybil_publish_every_s", int(10)),
            ]),
            81211,
        ),
        (
            "S12",
            table(vec![
                ("n_home", int(12)),
                ("n_mobile", int(4)),
                ("n_denied", int(3)),
                ("n_late_join", int(2)),
                ("liar_sizes", ri(MIB, 4 * MIB)),
            ]),
            81299,
        ),
        (
            "S13",
            table(vec![
                ("crash_frac", float(0.2)),
                ("partitions", strs(&["complete", "oneway"])),
                ("stateless_share", float(0.7)),
                ("n_slow", int(3)),
            ]),
            81313,
        ),
        (
            "S13",
            table(vec![
                ("n_home", int(10)),
                ("n_mobile", int(8)),
                ("partitions", strs(&["partial", "complete", "oneway"])),
                ("cut_s", ri(30, 90)),
                ("skew_s", ri(-30, 30)),
                ("n_jump", int(5)),
                ("n_late_join", int(4)),
                ("n_upgrade", int(3)),
            ]),
            81371,
        ),
        (
            "S14",
            table(vec![("n_items", int(12000)), ("n_sessions", int(30))]),
            81409,
        ),
        (
            "S14",
            table(vec![
                ("n_items", int(2000)),
                ("n_home", int(10)),
                ("profiles", strs(&["small", "large", "large", "branch", "cold", "cold"])),
                ("branch_items", ri(1000, 3000)),
            ]),
            81457,
        ),
        ("S15", table(vec![]), 81503),
        (
            "S15",
            table(vec![
                ("n_home", int(9)),
                ("n_mobile", int(2)),
                ("publish_every_s", int(20)),
                ("push_every_s", int(15)),
            ]),
            81589,
        ),
    ]
}

/// The 96 hidden-matrix entries: the matrix, the noise-floor twins, and the two groups of extra seeds, in that order.
pub fn variants() -> Vec<Variant> {
    let m = matrix();
    let noise_seeds: [u64; 8] = [1201, 1202, 1301, 1302, 1501, 1502, 1101, 1102];
    let mut seen: Vec<&str> = Vec::new();
    let mut ordinal = Vec::with_capacity(m.len());
    for (id, _, _) in &m {
        ordinal.push(1 + u8::try_from(seen.iter().filter(|s| *s == id).count()).unwrap_or(1));
        seen.push(id);
    }
    let noise: Vec<u64> = m
        .iter()
        .enumerate()
        .map(|(i, (_, _, seed))| noise_seeds.get(i).copied().unwrap_or(seed + 7))
        .collect();
    let mut out = Vec::with_capacity(4 * m.len());
    for (set, seeds) in [
        (SeedSet::Matrix, m.iter().map(|e| e.2).collect::<Vec<_>>()),
        (SeedSet::Noise, noise.clone()),
        (SeedSet::Extra1, m.iter().map(|e| e.2 + 1).collect()),
        (SeedSet::Extra2, noise.iter().map(|s| s + 50).collect()),
    ] {
        for (i, (id, params, _)) in m.iter().enumerate() {
            out.push(Variant {
                id,
                variant: ordinal[i],
                set,
                seed: seeds[i],
                params: params.clone(),
            });
        }
    }
    out
}

/// Builds the world of a variant exactly as the reference runner does: generate it, then add the hidden adversary of
/// its scenario with the same seed.
///
/// # Errors
/// The errors of [`generate`] and [`add_adversary`].
pub fn build(variant: &Variant) -> Result<World, WorldError> {
    let mut w = generate(variant.id, &variant.params, variant.seed)?;
    add_adversary(&mut w, &adversary_for(variant.id), variant.seed)?;
    Ok(w)
}
