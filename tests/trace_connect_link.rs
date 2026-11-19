//! Trace generation for the client carrier state machine: seeded random runs of the real `Link` through its public API,
//! recorded as ndjson (`connect_link.ndjson`) for the TLA+ trace check (`TraceConnectLink.tla`) and the Lean replay
//! (`Pinc/TraceConnectLink.lean`).
//!
//! A run starts a link with some node-wide shared state (phone or not, `KEEP_LEARN` on or off, a lease learned or not, a
//! restart pending or not) and calls it with every method of the module in a random order, at instants that step by
//! amounts around every rule constant (and sometimes go back), with every context of the node. After every call the
//! link and the shared state are read back (through their `Debug` form, the fields are private) and recorded with the
//! answer, so the model must agree on the state as well as on what the host is told to do. Instants are whole
//! milliseconds and are recorded in microseconds, which TLC's 32-bit integers hold.
//! The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    unreachable_pub
)]

use std::collections::BTreeMap;

use pinc_connect::client::link::{Act, Ctx, Link, Pulse, Shared};
use pinc_tests::SplitMix64;

const MS: u64 = 1_000_000;
const S: u64 = 1_000_000_000;

/// The fields of a derived `Debug` struct: `Name { a: 1, b: Some(2) }`.
fn fields(d: &str) -> BTreeMap<String, String> {
    let inner = d.split_once('{').unwrap().1.trim_end_matches('}').trim();
    let mut out = BTreeMap::new();
    let mut depth = 0;
    let mut cur = String::new();
    for ch in inner.chars() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {}
        }
        if ch == ',' && depth == 0 {
            let (k, v) = cur.split_once(':').unwrap();
            out.insert(k.trim().to_string(), v.trim().to_string());
            cur.clear();
        } else {
            cur.push(ch);
        }
    }
    if !cur.trim().is_empty() {
        let (k, v) = cur.split_once(':').unwrap();
        out.insert(k.trim().to_string(), v.trim().to_string());
    }
    out
}

/// A nanosecond count as whole microseconds.
fn us(v: &str) -> u64 {
    let n: u64 = v.parse().unwrap();
    assert_eq!(n % 1000, 0, "{n} is not whole microseconds");
    n / 1000
}

fn opt_us(v: &str) -> i64 {
    if v == "None" {
        -1
    } else {
        us(v.strip_prefix("Some(").unwrap().trim_end_matches(')')) as i64
    }
}

fn link_json(l: &Link) -> String {
    let f = fields(&format!("{l:?}"));
    let st = match f["state"].as_str() {
        "Down" => "down",
        "Dialing" => "dialing",
        "Open" => "open",
        s => panic!("{s}"),
    };
    format!(
        r#"{{"st":"{st}","retry":{},"at":{},"ds":{},"chk":{},"ride":{},"gap":{},"lrx":{},"hlt":{},"defer":{},"was":{}}}"#,
        us(&f["retry"]),
        us(&f["at"]),
        us(&f["dial_start"]),
        us(&f["chk"]),
        f["ride"],
        us(&f["gap"]),
        us(&f["lrx"]),
        us(&f["hlt"]),
        f["defer"],
        f["was_open"]
    )
}

fn shared_json(s: &Shared) -> String {
    let f = fields(&format!("{s:?}"));
    format!(
        r#"{{"phone":{},"kfail":{},"lhi":{},"klearn":{},"kiv":{},"restarted":{},"du":{}}}"#,
        f["phone"],
        opt_us(&f["keep_fail"]),
        us(&f["lease_hi"]),
        f["keep_learn"],
        us(&f["keep_iv"]),
        f["restarted"],
        opt_us(&f["defer_until"])
    )
}

fn ctx_json(c: &Ctx) -> String {
    format!(
        r#"{{"home":{},"rtt":{},"udp":{},"rides":{},"queued":{}}}"#,
        c.home,
        c.rtt / 1000,
        c.udp_any,
        c.rides,
        c.queued
    )
}

fn act(a: Option<Act>) -> &'static str {
    match a {
        None => "none",
        Some(Act::Dial) => "dial",
        Some(Act::Close) => "close",
        Some(Act::Ping) => "ping",
        Some(Act::Check) => "check",
    }
}

fn pick<T: Copy>(rng: &mut SplitMix64, v: &[T]) -> T {
    v[(rng.next_u64() % v.len() as u64) as usize]
}

fn run(seed: u64, steps: usize, out: &mut Vec<String>) {
    let mut rng = SplitMix64::traced(seed);
    let mut sh = Shared {
        phone: rng.next_u64().is_multiple_of(3),
        keep_learn: rng.next_u64().is_multiple_of(2),
        lease_hi: pick(&mut rng, &[0, 0, 15 * S, 20 * S, 30 * S, 40 * S]),
        restarted: rng.next_u64().is_multiple_of(4),
        ..Shared::default()
    };
    let mut l = Link::new();
    let mut now = pick(&mut rng, &[0, 5 * S, 100 * S]);
    out.push(format!(r#"{{"t":"lknew","S":{}}}"#, shared_json(&sh)));
    let deltas: [u64; 24] = [
        0,
        MS,
        100 * MS,
        500 * MS,
        599 * MS,
        600 * MS,
        601 * MS,
        S,
        2 * S,
        2999 * MS,
        3 * S,
        7999 * MS,
        8 * S,
        8001 * MS,
        14_999 * MS,
        15 * S,
        17_500 * MS,
        29_999 * MS,
        30 * S,
        30_001 * MS,
        64_999 * MS,
        65 * S,
        65_001 * MS,
        600 * S,
    ];
    let rtts: [u64; 8] = [0, MS, 100 * MS, 500 * MS, S, 2 * S, 3 * S, 5 * S];
    for _ in 0..steps {
        let r = rng.next_u64() % 100;
        // TLC's integers are 32 bits wide: a run ends before its clock passes 1500 s (microseconds in the trace)
        if now > 1500 * S {
            break;
        }
        now = match r % 7 {
            0 if now > 100 * S => now.saturating_sub(pick(&mut rng, &deltas)),
            1 => now + (rng.next_u64() % 100_000) * MS / 10,
            _ => now + pick(&mut rng, &deltas),
        };
        let c = Ctx {
            home: !rng.next_u64().is_multiple_of(4),
            rtt: pick(&mut rng, &rtts),
            udp_any: rng.next_u64().is_multiple_of(3),
            rides: rng.next_u64().is_multiple_of(3),
            queued: rng.next_u64().is_multiple_of(4),
        };
        let line = |call: &str, res: &str, l: &Link, sh: &Shared| {
            format!(
                r#"{{"t":"lk","c":"{call}","now":{},"ctx":{},"res":{res},"L":{},"S":{}}}"#,
                now / 1000,
                ctx_json(&c),
                link_json(l),
                shared_json(sh)
            )
        };
        let before = sh;
        match r {
            0..=17 => {
                let a = l.want_dial(now, &mut sh, &c);
                out.push(line("want_dial", &format!("\"{}\"", act(a)), &l, &sh));
            }
            18..=29 => {
                let was = l.opened(now);
                out.push(line("opened", &format!("{was}"), &l, &sh));
            }
            30..=39 => {
                l.closed(now);
                out.push(line("closed", "\"none\"", &l, &sh));
            }
            40..=47 => {
                l.heard(now);
                out.push(line("heard", "\"none\"", &l, &sh));
            }
            48..=53 => {
                l.wrote(now);
                out.push(line("wrote", "\"none\"", &l, &sh));
            }
            54..=57 => {
                let p = l.pulse(now, &c);
                let s = match p {
                    Pulse::Closed => "closed",
                    Pulse::Waiting => "waiting",
                    Pulse::Ping => "ping",
                };
                out.push(line("pulse", &format!("\"{s}\""), &l, &sh));
            }
            58..=60 => {
                let a = l.reset(now);
                out.push(line("reset", &format!("\"{}\"", act(Some(a))), &l, &sh));
            }
            61..=68 => {
                let a = l.before_send(now, &sh, &c);
                out.push(line("before_send", &format!("\"{}\"", act(a)), &l, &sh));
            }
            69..=76 => {
                let ridden = rng.next_u64().is_multiple_of(2);
                let a = l.check(now, &c, ridden);
                out.push(line("check", &format!("\"{}\"", act(a)), &l, &sh).replacen(
                    "\"ctx\"",
                    &format!("\"ridden\":{ridden},\"ctx\""),
                    1,
                ));
            }
            77..=91 => {
                let a = l.tick(now, &mut sh, &c);
                out.push(line("tick", &format!("\"{}\"", act(a)), &l, &sh));
            }
            92..=97 => {
                let d = l.next_deadline(now, &sh, &c);
                // the only deadline that is not whole microseconds is the dial watchdog's, one nanosecond past
                // a whole number of them; it is recorded rounded up
                let v = d.map_or(-1, |d| d.div_ceil(1000) as i64);
                out.push(line("deadline", &format!("{v}"), &l, &sh));
                if let Some(d) = d {
                    // the deadline is honoured: a tick strictly before it does nothing
                    if d > now {
                        let mut l2 = l;
                        let mut sh2 = sh;
                        assert_eq!(
                            l2.tick(d - 1, &mut sh2, &c),
                            None,
                            "a tick before the deadline acts: {l:?} {sh:?} {c:?} now={now} d={d}"
                        );
                    }
                }
            }
            _ => {
                // the node changes the shared state between calls
                match rng.next_u64() % 6 {
                    0 => sh.phone = !sh.phone,
                    1 => sh.keep_learn = !sh.keep_learn,
                    2 => {
                        sh.restarted = !sh.restarted;
                        sh.defer_until = None;
                    }
                    3 => sh.lease_hi = pick(&mut rng, &[0, 15 * S, 20 * S, 30 * S, 40 * S]),
                    4 => sh.keep_iv = pick(&mut rng, &[0, 15 * S, 20 * S, 40 * S]),
                    _ => sh.keep_fail = pick(&mut rng, &[None, Some(now), Some(now.saturating_sub(700 * S))]),
                }
                out.push(format!(r#"{{"t":"lkset","S":{}}}"#, shared_json(&sh)));
                continue;
            }
        }
        // the retry wait is 1 s or 2 s, and the lease never rises
        let f = fields(&format!("{l:?}"));
        let retry = f["retry"].parse::<u64>().unwrap();
        assert!(retry == S || retry == 2 * S);
        if before.lease_hi != 0 {
            assert!(sh.lease_hi != 0 && sh.lease_hi <= before.lease_hi, "the lease rose");
        }
    }
}

#[test]
fn connect_link_trace() {
    let mut out = Vec::new();
    for seed in 0..220u64 {
        run(0x11C0 + seed, 450, &mut out);
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::write(format!("{dir}/connect_link.ndjson"), out.join("\n") + "\n").unwrap();
    }
    assert!(out.len() > 10_000);
}
