//! Scenario parameters: the public shapes of every scenario and typed access to a [`Params`] table.
//!
//! The accessors fail with a [`WorldError`] where the reference would raise a `KeyError` or `TypeError`; they never
//! substitute a default the reference does not have. The `*_or` forms are the places where the reference reads
//! `p.get(key, default)`.

use super::WorldError;
use super::model::{Param, Params};

const KIB: i64 = 1024;
const MIB: i64 = 1024 * KIB;

/// An integer parameter.
pub(super) const fn int(v: i64) -> Param {
    Param::Int(v)
}

/// A float parameter.
pub(super) const fn float(v: f64) -> Param {
    Param::Float(v)
}

/// A flag parameter.
pub(super) const fn flag(v: bool) -> Param {
    Param::Bool(v)
}

/// A pair of integers.
pub(super) const fn ri(lo: i64, hi: i64) -> Param {
    Param::Range {
        lo: lo as f64,
        hi: hi as f64,
        ints: true,
    }
}

/// A pair of floats.
pub(super) const fn rf(lo: f64, hi: f64) -> Param {
    Param::Range { lo, hi, ints: false }
}

/// A tuple of integers.
pub(super) fn ints(v: &[i64]) -> Param {
    Param::Ints(v.to_vec())
}

/// A tuple of names.
pub(super) fn strs(v: &[&str]) -> Param {
    Param::Strs(v.iter().map(|s| (*s).to_string()).collect())
}

/// A table from `(name, value)` pairs.
pub(super) fn table(entries: Vec<(&str, Param)>) -> Params {
    entries.into_iter().map(|(k, v)| (k.to_string(), v)).collect()
}

fn missing(key: &str) -> WorldError {
    WorldError::MissingParam(key.to_string())
}

fn bad(key: &str, want: &'static str) -> WorldError {
    WorldError::BadParam {
        key: key.to_string(),
        want,
    }
}

/// Typed reads of a parameter table.
pub(super) trait ParamsExt {
    /// The integer `p[key]`.
    fn int(&self, key: &str) -> Result<i64, WorldError>;
    /// `p.get(key, default)` for an integer.
    fn int_or(&self, key: &str, default: i64) -> Result<i64, WorldError>;
    /// The count `p[key]` as a loop bound (negative is zero, as `range` does).
    fn count(&self, key: &str) -> Result<usize, WorldError>;
    /// A number `p[key]`, integer or float, as a float.
    fn num(&self, key: &str) -> Result<f64, WorldError>;
    /// The flag `p[key]`.
    fn flag(&self, key: &str) -> Result<bool, WorldError>;
    /// `p.get(key, default)` for a flag.
    fn flag_or(&self, key: &str, default: bool) -> Result<bool, WorldError>;
    /// The pair `p[key]` as floats `(lo, hi)`.
    fn pair(&self, key: &str) -> Result<(f64, f64), WorldError>;
    /// The pair `p[key]` as integers; the reference passes it to `randint` or multiplies it as integers.
    fn int_pair(&self, key: &str) -> Result<(i64, i64), WorldError>;
    /// The tuple of integers `p[key]`.
    fn int_list(&self, key: &str) -> Result<&[i64], WorldError>;
    /// The tuple of names `p[key]`.
    fn str_list(&self, key: &str) -> Result<&[String], WorldError>;
    /// `bool(p.get(key))`: present and not zero, false or empty.
    fn truthy(&self, key: &str) -> bool;
}

impl ParamsExt for Params {
    fn int(&self, key: &str) -> Result<i64, WorldError> {
        match self.get(key) {
            Some(Param::Int(v)) => Ok(*v),
            Some(_) => Err(bad(key, "an integer")),
            None => Err(missing(key)),
        }
    }

    fn int_or(&self, key: &str, default: i64) -> Result<i64, WorldError> {
        if self.contains_key(key) {
            self.int(key)
        } else {
            Ok(default)
        }
    }

    fn count(&self, key: &str) -> Result<usize, WorldError> {
        Ok(usize::try_from(self.int(key)?).unwrap_or(0))
    }

    fn num(&self, key: &str) -> Result<f64, WorldError> {
        match self.get(key) {
            Some(Param::Int(v)) => Ok(*v as f64),
            Some(Param::Float(v)) => Ok(*v),
            Some(_) => Err(bad(key, "a number")),
            None => Err(missing(key)),
        }
    }

    fn flag(&self, key: &str) -> Result<bool, WorldError> {
        match self.get(key) {
            Some(Param::Bool(v)) => Ok(*v),
            Some(_) => Err(bad(key, "a flag")),
            None => Err(missing(key)),
        }
    }

    fn flag_or(&self, key: &str, default: bool) -> Result<bool, WorldError> {
        if self.contains_key(key) {
            self.flag(key)
        } else {
            Ok(default)
        }
    }

    fn pair(&self, key: &str) -> Result<(f64, f64), WorldError> {
        match self.get(key) {
            Some(Param::Range { lo, hi, .. }) => Ok((*lo, *hi)),
            Some(_) => Err(bad(key, "a pair of numbers")),
            None => Err(missing(key)),
        }
    }

    fn int_pair(&self, key: &str) -> Result<(i64, i64), WorldError> {
        match self.get(key) {
            Some(Param::Range { lo, hi, ints: true }) => Ok((*lo as i64, *hi as i64)),
            Some(_) => Err(bad(key, "a pair of integers")),
            None => Err(missing(key)),
        }
    }

    fn int_list(&self, key: &str) -> Result<&[i64], WorldError> {
        match self.get(key) {
            Some(Param::Ints(v)) => Ok(v),
            Some(_) => Err(bad(key, "a tuple of integers")),
            None => Err(missing(key)),
        }
    }

    fn str_list(&self, key: &str) -> Result<&[String], WorldError> {
        match self.get(key) {
            Some(Param::Strs(v)) => Ok(v),
            Some(_) => Err(bad(key, "a tuple of names")),
            None => Err(missing(key)),
        }
    }

    fn truthy(&self, key: &str) -> bool {
        match self.get(key) {
            None => false,
            Some(Param::Int(v)) => *v != 0,
            Some(Param::Float(v)) => *v != 0.0,
            Some(Param::Bool(v)) => *v,
            Some(Param::Ints(v)) => !v.is_empty(),
            Some(Param::Strs(v)) => !v.is_empty(),
            Some(Param::Range { .. }) => true,
        }
    }
}

/// The public parameters of scenario `id` (the empty table for an id that is not generated).
pub fn public_params(id: &str) -> Params {
    match id {
        "S1" => s1(),
        "S2" => s2(),
        "S3" => s3(),
        "S4" => s4(),
        "S5" => s5(),
        "S6" => s6(),
        "S10" => s10(),
        "S11" => s11(),
        "S12" => s12(),
        "S13" => s13(),
        "S14" => s14(),
        "S15" => s15(),
        _ => Params::new(),
    }
}

fn s1() -> Params {
    table(vec![
        ("n_cloud", int(3)),
        ("n_server", int(13)),
        ("duration_s", int(240)),
        ("active_s", ri(8, 150)),
        ("idle_s", ri(200, 240)),
        ("server_bps", ri(10_000_000_000, 100_000_000_000)),
        ("server_delay_us", ri(5, 30)),
        ("mtu", int(9000)),
        ("publish_every_s", int(8)),
        ("n_push_pairs", int(6)),
        ("push_every_s", int(5)),
        ("n_docsync", int(30)),
        ("n_manage", int(6)),
        ("n_echo", int(30)),
        ("n_fetch", int(0)),
        ("fetch_sizes", ri(64 * MIB, 64 * MIB)),
        ("bulk_sizes", ints(&[256 * MIB, 64 * MIB])),
        ("crash_frac", float(0.0)),
        ("n_leave", int(0)),
        ("n_late_join", int(0)),
        ("n_upgrade", int(0)),
        ("n_revoke", int(0)),
        ("n_denied", int(0)),
        ("no_punch", flag(false)),
        ("v6_share", float(0.0)),
        ("v6_open_share", float(0.0)),
    ])
}

fn s2() -> Params {
    table(vec![
        ("n_cloud", int(4)),
        ("n_home", int(18)),
        ("n_mobile", int(14)),
        ("duration_s", int(600)),
        ("active_s", ri(12, 400)),
        ("publish_every_s", int(25)),
        ("n_push_pairs", int(8)),
        ("push_every_s", int(15)),
        ("n_docsync", int(30)),
        ("n_manage", int(8)),
        ("n_echo", int(40)),
        ("n_fetch", int(6)),
        ("fetch_sizes", ri(256 * KIB, 4 * MIB)),
        ("crash_frac", float(0.1)),
        ("n_leave", int(2)),
        ("n_late_join", int(2)),
        ("n_upgrade", int(1)),
        ("n_revoke", int(1)),
        ("n_denied", int(1)),
        ("home_loss", float(0.002)),
        ("mobile_loss", float(0.01)),
        ("burst_ms", ri(10, 60)),
        ("mobile_delay_ms", ri(20, 45)),
        ("idle_s", ri(480, 600)),
        ("no_punch", flag(false)),
        ("v6_share", float(0.45)),
        ("v6_open_share", float(0.2)),
        ("mtu", int(1500)),
    ])
}

fn s3() -> Params {
    table(vec![
        ("n_cloud", int(3)),
        ("n_home", int(4)),
        ("n_mobile", int(16)),
        ("duration_s", int(600)),
        ("active_s", ri(10, 420)),
        ("publish_every_s", int(30)),
        ("n_push_pairs", int(8)),
        ("push_every_s", int(12)),
        ("n_docsync", int(16)),
        ("n_manage", int(4)),
        ("n_echo", int(20)),
        ("n_fetch", int(6)),
        ("fetch_sizes", ri(MIB, 6 * MIB)),
        ("handover_every_s", ri(60, 120)),
        ("handover_outage_ms", ri(200, 2000)),
        ("suspend_every_s", ri(150, 260)),
        ("suspend_s", ri(10, 40)),
        ("rebind_every_s", ri(80, 160)),
        ("mobile_loss", rf(0.01, 0.10)),
        ("burst_ms", ri(20, 120)),
        ("mobile_delay_ms", ri(20, 290)),
        ("home_loss", float(0.002)),
        ("idle_s", ri(480, 600)),
        ("no_punch", flag(false)),
        ("v6_share", float(0.45)),
        ("v6_open_share", float(0.2)),
        ("mtu", int(1500)),
    ])
}

fn s4() -> Params {
    table(vec![
        ("n_cloud", int(3)),
        ("n_home", int(10)),
        ("n_mobile", int(8)),
        ("duration_s", int(480)),
        ("active_s", ri(10, 330)),
        ("idle_s", ri(390, 480)),
        ("publish_every_s", int(30)),
        ("n_push_pairs", int(6)),
        ("push_every_s", int(15)),
        ("n_docsync", int(20)),
        ("n_manage", int(4)),
        ("n_echo", int(30)),
        ("n_fetch", int(4)),
        ("fetch_sizes", ri(256 * KIB, 2 * MIB)),
        ("crash_frac", float(0.05)),
        ("n_leave", int(1)),
        ("n_late_join", int(1)),
        ("n_upgrade", int(0)),
        ("n_revoke", int(0)),
        ("n_denied", int(0)),
        ("home_loss", float(0.002)),
        ("mobile_loss", float(0.01)),
        ("burst_ms", ri(10, 60)),
        ("mobile_delay_ms", ri(20, 45)),
        ("no_punch", flag(false)),
        ("v6_share", float(0.45)),
        ("v6_open_share", float(0.2)),
        ("mtu", int(1500)),
        ("hostile_share", float(1.0)),
        ("tcp_ports", ints(&[443, 8443])),
        ("tls_only", flag(false)),
        ("fw_reject", flag(false)),
        ("tcp_idle_s", ri(30, 120)),
        ("portal_s", ri(20, 90)),
        ("portal_share", float(0.4)),
    ])
}

fn s5() -> Params {
    table(vec![
        ("n_cloud", int(3)),
        ("n_home", int(12)),
        ("n_mobile", int(12)),
        ("duration_s", int(480)),
        ("active_s", ri(10, 330)),
        ("publish_every_s", int(30)),
        ("n_push_pairs", int(8)),
        ("push_every_s", int(15)),
        ("n_docsync", int(30)),
        ("n_manage", int(6)),
        ("n_echo", int(60)),
        ("n_fetch", int(6)),
        ("fetch_sizes", ri(512 * KIB, 4 * MIB)),
        ("home_loss", float(0.002)),
        ("mobile_loss", float(0.01)),
        ("burst_ms", ri(10, 60)),
        ("mobile_delay_ms", ri(20, 45)),
        ("idle_s", ri(390, 480)),
        ("no_punch", flag(true)),
        ("v6_share", float(0.45)),
        ("v6_open_share", float(0.1)),
        ("mtu", int(1500)),
    ])
}

fn s6() -> Params {
    table(vec![
        ("n_cloud", int(3)),
        ("n_rural", int(6)),
        ("n_geo", int(5)),
        ("n_2g", int(4)),
        ("duration_s", int(600)),
        ("active_s", ri(15, 420)),
        ("idle_s", ri(480, 600)),
        ("publish_every_s", int(60)),
        ("n_push_pairs", int(5)),
        ("push_every_s", int(40)),
        ("n_docsync", int(12)),
        ("n_manage", int(3)),
        ("n_echo", int(16)),
        ("n_fetch", int(4)),
        ("fetch_sizes", ri(16 * KIB, 96 * KIB)),
        ("crash_frac", float(0.0)),
        ("n_leave", int(1)),
        ("n_late_join", int(1)),
        ("n_upgrade", int(0)),
        ("n_revoke", int(0)),
        ("n_denied", int(0)),
        ("rural_bps", ri(40_000, 100_000)),
        ("geo_bps", ri(30_000, 100_000)),
        ("g2_bps", ri(10_000, 40_000)),
        ("rural_delay_ms", ri(300, 600)),
        ("geo_delay_ms", ri(300, 400)),
        ("g2_delay_ms", ri(400, 1000)),
        ("loss", rf(0.01, 0.05)),
        ("burst_ms", ri(20, 200)),
        ("no_punch", flag(false)),
        ("v6_share", float(0.2)),
        ("v6_open_share", float(0.1)),
        ("mtu", int(1500)),
        ("home_loss", float(0.0)),
    ])
}

fn s10() -> Params {
    table(vec![
        ("n_cloud", int(3)),
        ("n_browser", int(14)),
        ("n_home", int(2)),
        ("duration_s", int(480)),
        ("active_s", ri(10, 330)),
        ("idle_s", ri(390, 480)),
        ("publish_every_s", int(25)),
        ("n_push_pairs", int(6)),
        ("push_every_s", int(15)),
        ("n_docsync", int(24)),
        ("n_manage", int(6)),
        ("n_echo", int(30)),
        ("n_fetch", int(4)),
        ("fetch_sizes", ri(256 * KIB, 2 * MIB)),
        ("crash_frac", float(0.1)),
        ("n_leave", int(2)),
        ("n_late_join", int(2)),
        ("n_upgrade", int(0)),
        ("n_revoke", int(0)),
        ("n_denied", int(0)),
        ("home_loss", float(0.002)),
        ("mobile_loss", float(0.01)),
        ("burst_ms", ri(10, 60)),
        ("browser_mobile_share", float(0.3)),
        ("mobile_delay_ms", ri(20, 45)),
        ("no_punch", flag(false)),
        ("v6_share", float(0.45)),
        ("v6_open_share", float(0.2)),
        ("mtu", int(1500)),
    ])
}

fn s11() -> Params {
    table(vec![
        ("n_cloud", int(3)),
        ("n_home", int(6)),
        ("n_mobile", int(2)),
        ("duration_s", int(420)),
        ("full_sizes", ints(&[MIB, 4 * MIB, 16 * MIB, 32 * MIB])),
        ("multi_size", int(32 * MIB)),
        ("n_multi_prov", int(3)),
        ("range_sizes", ints(&[1 << 30, 1 << 40])),
        ("stream_size", int(8 * MIB)),
        ("stream_rate_bps", int(8_000_000)),
        ("n_restart", int(1)),
        ("n_disconnect", int(2)),
        ("home_loss", float(0.002)),
        ("mobile_loss", float(0.01)),
        ("burst_ms", ri(10, 60)),
        ("mobile_delay_ms", ri(20, 45)),
        ("home_down_bps", int(100_000_000)),
        ("home_up_bps", int(40_000_000)),
        ("idle_s", ri(360, 420)),
        ("no_punch", flag(false)),
        ("v6_share", float(0.45)),
        ("v6_open_share", float(0.2)),
        ("mtu", int(1500)),
    ])
}

fn s12() -> Params {
    table(vec![
        ("n_cloud", int(3)),
        ("n_home", int(10)),
        ("n_mobile", int(6)),
        ("duration_s", int(480)),
        ("active_s", ri(10, 330)),
        ("idle_s", ri(390, 480)),
        ("publish_every_s", int(25)),
        ("n_push_pairs", int(6)),
        ("push_every_s", int(15)),
        ("n_docsync", int(20)),
        ("n_manage", int(4)),
        ("n_echo", int(30)),
        ("n_fetch", int(0)),
        ("fetch_sizes", ri(256 * KIB, 2 * MIB)),
        ("crash_frac", float(0.0)),
        ("n_leave", int(0)),
        ("n_late_join", int(1)),
        ("n_upgrade", int(0)),
        ("n_revoke", int(1)),
        ("n_denied", int(4)),
        ("home_loss", float(0.002)),
        ("mobile_loss", float(0.01)),
        ("burst_ms", ri(10, 60)),
        ("mobile_delay_ms", ri(20, 45)),
        ("no_punch", flag(false)),
        ("v6_share", float(0.45)),
        ("v6_open_share", float(0.2)),
        ("mtu", int(1500)),
        ("sybil_publish_every_s", int(20)),
        ("n_liar_fetch", int(4)),
        ("liar_sizes", ri(256 * KIB, 2 * MIB)),
    ])
}

fn s13() -> Params {
    table(vec![
        ("n_cloud", int(3)),
        ("n_home", int(12)),
        ("n_mobile", int(6)),
        ("duration_s", int(600)),
        ("active_s", ri(10, 420)),
        ("idle_s", ri(520, 600)),
        ("publish_every_s", int(25)),
        ("n_push_pairs", int(6)),
        ("push_every_s", int(15)),
        ("n_docsync", int(20)),
        ("n_manage", int(4)),
        ("n_echo", int(24)),
        ("n_fetch", int(2)),
        ("fetch_sizes", ri(256 * KIB, MIB)),
        ("crash_frac", float(0.15)),
        ("n_leave", int(2)),
        ("n_late_join", int(3)),
        ("n_upgrade", int(2)),
        ("n_revoke", int(1)),
        ("n_denied", int(0)),
        ("home_loss", float(0.002)),
        ("mobile_loss", float(0.01)),
        ("burst_ms", ri(10, 60)),
        ("mobile_delay_ms", ri(20, 45)),
        ("no_punch", flag(false)),
        ("v6_share", float(0.45)),
        ("v6_open_share", float(0.2)),
        ("mtu", int(1500)),
        ("stateless_share", float(0.5)),
        ("partitions", strs(&["complete", "partial", "oneway"])),
        ("cut_s", ri(20, 60)),
        ("cut_window_s", ri(60, 340)),
        ("skew_s", ri(-8, 8)),
        ("drift_ppm", ri(-80, 80)),
        ("n_jump", int(3)),
        ("jump_s", ri(1, 30)),
        ("n_slow", int(2)),
        ("slow_factor", ri(4, 12)),
    ])
}

fn s14() -> Params {
    table(vec![
        ("n_cloud", int(3)),
        ("n_home", int(8)),
        ("n_mobile", int(3)),
        ("duration_s", int(480)),
        ("active_s", ri(10, 380)),
        ("idle_s", ri(420, 480)),
        ("n_items", int(4000)),
        ("small_diff", ri(1, 10)),
        ("large_frac", rf(0.10, 0.30)),
        ("branch_items", ri(500, 1500)),
        ("cold_frac", rf(0.0, 0.05)),
        ("n_sessions", int(24)),
        ("deadline_s", int(60)),
        ("n_echo", int(8)),
        ("profiles", strs(&["small", "small", "large", "branch", "cold"])),
        ("home_loss", float(0.002)),
        ("mobile_loss", float(0.01)),
        ("burst_ms", ri(10, 60)),
        ("mobile_delay_ms", ri(20, 45)),
        ("no_punch", flag(false)),
        ("v6_share", float(0.45)),
        ("v6_open_share", float(0.2)),
        ("mtu", int(1500)),
    ])
}

fn s15() -> Params {
    table(vec![
        ("n_cloud", int(3)),
        ("n_home", int(7)),
        ("n_mobile", int(4)),
        ("duration_s", int(3600)),
        ("active_s", ri(10, 3300)),
        ("idle_s", ri(3360, 3600)),
        ("publish_every_s", int(30)),
        ("n_push_pairs", int(5)),
        ("push_every_s", int(20)),
        ("n_docsync", int(60)),
        ("n_manage", int(10)),
        ("n_echo", int(60)),
        ("n_fetch", int(6)),
        ("fetch_sizes", ri(256 * KIB, 2 * MIB)),
        ("crash_frac", float(0.1)),
        ("n_leave", int(1)),
        ("n_late_join", int(1)),
        ("n_upgrade", int(1)),
        ("n_revoke", int(0)),
        ("n_denied", int(0)),
        ("home_loss", float(0.002)),
        ("mobile_loss", float(0.01)),
        ("burst_ms", ri(10, 60)),
        ("mobile_delay_ms", ri(20, 45)),
        ("no_punch", flag(false)),
        ("v6_share", float(0.45)),
        ("v6_open_share", float(0.2)),
        ("mtu", int(1500)),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typed_reads_and_errors() {
        let p = table(vec![
            ("n", int(3)),
            ("x", float(0.5)),
            ("r", ri(1, 2)),
            ("f", flag(true)),
            ("z", int(0)),
        ]);
        assert_eq!(p.int("n"), Ok(3));
        assert_eq!(p.num("n"), Ok(3.0));
        assert_eq!(p.num("x"), Ok(0.5));
        assert_eq!(p.int_pair("r"), Ok((1, 2)));
        assert_eq!(p.pair("r"), Ok((1.0, 2.0)));
        assert_eq!(p.int_or("absent", 7), Ok(7));
        assert!(p.truthy("n") && p.truthy("r") && p.truthy("f"));
        assert!(!p.truthy("z") && !p.truthy("absent"));
        assert_eq!(p.int("absent"), Err(WorldError::MissingParam("absent".into())));
        assert!(matches!(p.int("x"), Err(WorldError::BadParam { .. })));
        assert!(matches!(p.int_pair("x"), Err(WorldError::BadParam { .. })));
        assert!(matches!(p.flag("n"), Err(WorldError::BadParam { .. })));
    }

    #[test]
    fn every_public_shape_has_the_run_window() {
        for id in crate::suite::world::SCENARIOS {
            let p = public_params(id);
            for key in ["n_cloud", "duration_s", "idle_s"] {
                assert!(p.contains_key(key), "{id} lacks {key}");
            }
            assert!(p.int_pair("idle_s").is_ok());
        }
        assert!(public_params("S7").is_empty());
    }
}
