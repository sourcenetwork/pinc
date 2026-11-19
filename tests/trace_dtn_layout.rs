//! Trace generation for the bundle layout (`SliceLayout`): the real code on boundary parameters, recorded as ndjson
//! (`dtn_layout.ndjson`) for the TLA+ trace check (`TraceDtnLayout.tla`) and the Lean replay (`Pinc/TraceDtnLayout.lean`).
//!
//! A run sweeps `(k, m)` over the validity boundary (`k = 0`, `k + m = 255` and `256`), the slice logs 0, 3, 4 and 5
//! and payload lengths around the data counts: 0, 1, `D * plain` and its neighbours for small `D`, for `D = 2^j` and
//! the counts near the largest payload whose sealed length fits a `u64` (found by bisection on the real `new`), and
//! `u64::MAX`. For a layout that `new` accepts, the event records the counts, the padded and sealed lengths, and at
//! the boundary indices `block_k`, `block_n`, `block_start`, `locate`, `data_symbol` and `byte_range`. A `u64` is
//! four 16-bit limbs, as in the other layout traces. Every result is checked here against `u128` arithmetic written
//! apart from the code, so the test is meaningful without the proof tools. The trace is written to the directory in
//! `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::comparison_chain,
    clippy::nonminimal_bool,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    unreachable_pub
)]

mod dtn_common;

use std::fmt::Write as _;

use dtn_common::{keypair, make, plan, recipient};
use pinc_crypto::IdentityAlg;
use pinc_dtn::hlc::Hlc;
use pinc_dtn::layout::SliceLayout;

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn opt_ok(v: bool) -> &'static str {
    if v { "true" } else { "false" }
}

/// Whether the sealed length of `payload` fits a `u64`, by `u128` arithmetic apart from the code.
fn fits(k: u8, m: u8, log: u8, payload: u64) -> bool {
    if k == 0 || u32::from(k) + u32::from(m) > 255 || log > 4 || payload == 0 {
        return false;
    }
    let s = 1024u128 << log;
    let plain = s - 16;
    let data = u128::from(payload).div_ceil(plain);
    let blocks = data.div_ceil(u128::from(k));
    (data + blocks * u128::from(m)) * s < 1u128 << 64
}

/// The largest payload that fits, by bisection on the predicate (monotone in the payload).
fn max_payload(k: u8, m: u8, log: u8) -> Option<u64> {
    if !fits(k, m, log, 1) {
        return None;
    }
    let (mut lo, mut hi) = (1u64, u64::MAX);
    if fits(k, m, log, hi) {
        return Some(hi);
    }
    while lo + 1 < hi {
        let mid = lo + (hi - lo) / 2;
        if fits(k, m, log, mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    Some(lo)
}

fn event(k: u8, m: u8, log: u8, payload: u64, out: &mut Vec<String>) {
    let res = SliceLayout::new(k, m, log, payload);
    let want = fits(k, m, log, payload);
    assert_eq!(res.is_ok(), want, "new({k}, {m}, {log}, {payload})");
    let mut line = format!(
        r#"{{"t":"dl","k":{k},"m":{m},"log":{log},"p":{},"ok":{}"#,
        limbs(payload),
        opt_ok(want)
    );
    let Ok(l) = res else {
        line.push('}');
        out.push(line);
        return;
    };
    let (kk, mm, sl) = (u128::from(k), u128::from(m), 1024u128 << log);
    let plain = sl - 16;
    let data = u128::from(payload).div_ceil(plain);
    let blocks = data.div_ceil(kk);
    let total = data + blocks * mm;
    assert_eq!(u128::from(l.slice_len()), sl);
    assert_eq!(u128::from(l.plain_len()), plain);
    assert_eq!(u128::from(l.data_symbols()), data);
    assert_eq!(u128::from(l.blocks()), blocks);
    assert_eq!(u128::from(l.total_symbols()), total);
    assert_eq!(u128::from(l.total_len()), total * sl);
    assert_eq!(u128::from(l.padded_len()), data * plain);
    let pad = data * plain - u128::from(payload);
    assert!(pad < plain);
    write!(
        line,
        r#","d":{},"bl":{},"ts":{},"tl":{},"pad":{}"#,
        limbs(l.data_symbols()),
        limbs(l.blocks()),
        limbs(l.total_symbols()),
        limbs(l.total_len()),
        limbs(l.padded_len())
    )
    .unwrap();
    // block_k, block_n, block_start at the boundary blocks
    let bl = l.blocks();
    let mut bidx = vec![0, 1, bl.saturating_sub(1), bl, bl.saturating_add(1), u64::MAX];
    if bl >= 2 {
        bidx.push(bl - 2);
    }
    bidx.sort_unstable();
    bidx.dedup();
    let rows: Vec<String> = bidx
        .iter()
        .map(|&b| {
            let (bk, bn, st) = (l.block_k(b) as u64, l.block_n(b) as u64, l.block_start(b));
            let b128 = u128::from(b);
            let want_bk = if b128 + 1 < blocks {
                kk
            } else if b128 + 1 == blocks {
                data - (blocks - 1) * kk
            } else {
                0
            };
            assert_eq!(u128::from(bk), want_bk);
            assert_eq!(u128::from(bn), if want_bk == 0 { 0 } else { want_bk + mm });
            if b128 <= blocks {
                assert_eq!(u128::from(st), b128 * (kk + mm));
            } else {
                assert!(u128::from(st) <= u128::from(u64::MAX));
            }
            format!("[{},{},{},{}]", limbs(b), limbs(bk), limbs(bn), limbs(st))
        })
        .collect();
    write!(line, r#","bk":[{}]"#, rows.join(",")).unwrap();
    // locate
    let t = l.total_symbols();
    let ls = l.block_start(bl - 1);
    let mut sidx = vec![
        0,
        1,
        u64::MAX,
        t,
        t.saturating_add(1),
        t - 1,
        ls,
        ls + 1,
        u64::from(k) + u64::from(m) - 1,
        u64::from(k) + u64::from(m),
        u64::from(k) + u64::from(m) + 1,
    ];
    if ls >= 1 {
        sidx.push(ls - 1);
    }
    if t >= 2 {
        sidx.push(t - 2);
    }
    sidx.sort_unstable();
    sidx.dedup();
    let rows: Vec<String> = sidx
        .iter()
        .map(|&s| {
            let r = l.locate(s);
            assert_eq!(r.is_some(), u128::from(s) < total, "locate {s}");
            match r {
                Some(p) => {
                    let pb = kk + mm;
                    assert_eq!(u128::from(p.block), u128::from(s) / pb);
                    assert_eq!(p.index as u128, u128::from(s) % pb);
                    assert_eq!(p.is_parity(), p.index >= p.block_k);
                    format!("[{},true,{},{},{}]", limbs(s), limbs(p.block), p.index, p.block_k)
                }
                None => format!("[{},false,[0,0,0,0],0,0]", limbs(s)),
            }
        })
        .collect();
    write!(line, r#","lc":[{}]"#, rows.join(",")).unwrap();
    // data_symbol
    let d = l.data_symbols();
    let mut didx = vec![
        0,
        1,
        u64::MAX,
        d,
        d.saturating_add(1),
        d - 1,
        u64::from(k).saturating_sub(1),
        u64::from(k),
        u64::from(k) + 1,
    ];
    didx.sort_unstable();
    didx.dedup();
    let rows: Vec<String> = didx
        .iter()
        .map(|&x| {
            let r = l.data_symbol(x);
            assert_eq!(r.is_some(), u128::from(x) < data);
            match r {
                Some(sym) => {
                    let p = l.locate(sym).unwrap();
                    assert_eq!(u128::from(p.block), u128::from(x) / kk);
                    assert_eq!(p.index as u128, u128::from(x) % kk);
                    assert!(!p.is_parity());
                    format!("[{},true,{}]", limbs(x), limbs(sym))
                }
                None => format!("[{},false,[0,0,0,0]]", limbs(x)),
            }
        })
        .collect();
    write!(line, r#","ds":[{}]"#, rows.join(",")).unwrap();
    // byte_range
    let ridx = {
        let mut v = vec![0, 1, t, t.saturating_add(1), t - 1, u64::MAX];
        v.sort_unstable();
        v.dedup();
        v
    };
    let mut rows = vec![];
    for &a in &ridx {
        for &b in &ridx {
            let r = l.byte_range(&(a..b));
            let bad = a > b || b > t;
            assert_eq!(r.is_err(), bad);
            match r {
                Ok(rg) => {
                    assert_eq!(u128::from(rg.start), u128::from(a) * sl);
                    assert_eq!(u128::from(rg.end), u128::from(b) * sl);
                    rows.push(format!(
                        "[{},{},true,{},{}]",
                        limbs(a),
                        limbs(b),
                        limbs(rg.start),
                        limbs(rg.end)
                    ));
                }
                Err(_) => rows.push(format!("[{},{},false,[0,0,0,0],[0,0,0,0]]", limbs(a), limbs(b))),
            }
        }
    }
    write!(line, r#","br":[{}]}}"#, rows.join(",")).unwrap();
    out.push(line);
}

/// The clock and lifetime events (`hc`): `Hlc::tick`, `Hlc::observe`, `Hlc::expires_at` and `Head::is_expired` on the
/// boundary values, each result also checked against `u128` arithmetic written apart from the code.
fn clock_events(out: &mut Vec<String>) {
    let walls = [0u64, 5, u64::MAX];
    let ctrs = [0u32, u32::MAX - 1, u32::MAX];
    let times = [0u64, 5, u64::MAX];
    for &w in &walls {
        for &c in &ctrs {
            for &now in &times {
                let t = Hlc::new(w, c).tick(now);
                let ew = u128::from(w.max(now));
                assert_eq!(u128::from(t.wall), ew);
                assert_eq!(t.counter, if now > w { 0 } else { c.saturating_add(1) });
                out.push(format!(
                    r#"{{"t":"hc","op":"tick","w":{},"c":{},"now":{},"ow":{},"oc":{}}}"#,
                    limbs(w),
                    limbs(u64::from(c)),
                    limbs(now),
                    limbs(t.wall),
                    limbs(u64::from(t.counter))
                ));
                for &rw in &walls {
                    for &rc in &ctrs {
                        let o = Hlc::new(w, c).observe(Hlc::new(rw, rc), now);
                        assert_eq!(o.wall, w.max(rw).max(now));
                        if c < u32::MAX {
                            assert!(o > Hlc::new(w, c), "observe is above the receiver");
                        }
                        if rc < u32::MAX {
                            assert!(o > Hlc::new(rw, rc), "observe is above the remote stamp");
                        }
                        out.push(format!(
                            r#"{{"t":"hc","op":"obs","w":{},"c":{},"rw":{},"rc":{},"now":{},"ow":{},"oc":{}}}"#,
                            limbs(w),
                            limbs(u64::from(c)),
                            limbs(rw),
                            limbs(u64::from(rc)),
                            limbs(now),
                            limbs(o.wall),
                            limbs(u64::from(o.counter))
                        ));
                    }
                }
            }
        }
    }
    let signer = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let sealed = make(&signer, &to, plan(1, 0, 0), &[1, 2, 3], 9);
    for &w in &[0u64, 1, u64::MAX - 1, u64::MAX] {
        for &life in &[0u64, 1, u64::MAX - 1, u64::MAX] {
            let mut head = *sealed.signed.head();
            head.created = Hlc::new(w, 0);
            head.lifetime_ms = life;
            let e = head.expires_at();
            assert_eq!(
                u128::from(e),
                (u128::from(w) + u128::from(life)).min(u128::from(u64::MAX))
            );
            assert_eq!(Hlc::new(w, 0).expires_at(life), e);
            let mut probes = vec![0, 1, e, u64::MAX];
            if e >= 1 {
                probes.push(e - 1);
            }
            if e < u64::MAX {
                probes.push(e + 1);
            }
            probes.sort_unstable();
            probes.dedup();
            let mut prev = false;
            let rows: Vec<String> = probes
                .iter()
                .map(|&n| {
                    let x = head.is_expired(n);
                    assert_eq!(x, e <= n, "expired exactly from the expiry on");
                    assert!(!prev || x, "expiry is monotone in time");
                    prev = x;
                    format!("[{},{x}]", limbs(n))
                })
                .collect();
            out.push(format!(
                r#"{{"t":"hc","op":"exp","w":{},"life":{},"e":{},"pr":[{}]}}"#,
                limbs(w),
                limbs(life),
                limbs(e),
                rows.join(",")
            ));
        }
    }
}

#[test]
fn layout_trace() {
    let kms: [(u8, u8); 10] = [
        (0, 5),
        (1, 0),
        (1, 254),
        (1, 255),
        (3, 252),
        (128, 127),
        (254, 1),
        (255, 0),
        (255, 1),
        (7, 3),
    ];
    let mut out = vec![];
    let mut valid = 0;
    for &(k, m) in &kms {
        for log in [0u8, 3, 4, 5] {
            let plain = (1024u64 << log.min(40)) - 16;
            let mut payloads = vec![0, 1, u64::MAX, u64::MAX - 1, plain - 1, plain, plain + 1];
            let mut counts: Vec<u64> = (1..=3).collect();
            counts.extend([u64::from(k), u64::from(k) + 1]);
            for j in [8, 32, 53] {
                counts.extend([(1u64 << j) - 1, 1 << j, (1 << j) + 1]);
            }
            if let Some(mx) = max_payload(k, m, log) {
                payloads.extend([mx, mx - 1, mx + 1, mx.saturating_add(2)]);
                let dmx = mx.div_ceil(plain);
                counts.extend([dmx.saturating_sub(2), dmx.saturating_sub(1), dmx, dmx + 1, dmx + 2]);
            }
            for d in counts {
                if let Some(top) = d.checked_mul(plain) {
                    payloads.extend([top, top + 1, top.saturating_sub(1), top.saturating_sub(plain - 1)]);
                }
            }
            payloads.sort_unstable();
            payloads.dedup();
            for p in payloads {
                if fits(k, m, log, p) {
                    valid += 1;
                }
                event(k, m, log, p, &mut out);
            }
        }
    }
    assert!(valid > 100);
    clock_events(&mut out);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            std::path::Path::new(&dir).join("dtn_layout.ndjson"),
            out.join("\n") + "\n",
        )
        .unwrap();
    }
}
