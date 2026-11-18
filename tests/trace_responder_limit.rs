//! Trace generation for the limit on a responder's handshake: a real responder, its dialer's datagrams passed by hand
//! at ticks of 10 s, recorded as ndjson (`responder_limit.ndjson`) for the TLA+ trace check (`TraceResponderLimit.tla`).
//!
//! A run is given the round trip of the dial (`rtt`, in ticks), the tick at which the dialer's first flight reaches the
//! responder (`ans`), the tick at which a flight for a prekey the responder does not hold reaches it (`rej`) and the
//! tick at which the held Finish is delivered (`fin`), each -1 for never. At every tick the responder's timers run and
//! the run records whether the responder has answered and where its handshake stands: open, done or gone. Nothing the
//! responder sends reaches a dialer after its answer.
//!
//! The test asserts, without the model: a Finish delivered by tick 6 completes the handshake (a Finish that came after
//! the base limit of 30 s was held and still taken), a responder nobody finishes is open at tick 3 or 6 and gone by
//! tick 4 or 7, and `answered` is 0 before the first flight and, with none, always. The trace is written to the
//! directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::redundant_closure_for_method_calls
)]

use std::fmt::Write as _;

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::PathId;

const TICK: u64 = 10 * SEC;
const TICKS: i64 = 12;

/// Every datagram `n` has to send at `now`.
fn drain(n: &mut Node<'_>, now: u64) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut buf = vec![0u8; 65536];
    while let Some(t) = n.with_lent(now, |c, env, l| c.poll_transmit(env, l, &mut buf)) {
        out.extend(buf[..t.len].chunks(t.segment_size).map(<[u8]>::to_vec));
    }
    out
}

/// Hand `dgrams` to the responder. A refusal (the responder is gone, or the datagram is not for it) is the run's
/// business, not the test's: the observation shows what became of the handshake.
fn to_server(s: &mut Node<'_>, stores: &mut Stores, now: u64, dgrams: Vec<Vec<u8>>) {
    for mut d in dgrams {
        let _ = s.with_lent(now, |c, env, l| c.handle_datagram_with(env, l, stores, PathId(2), &mut d));
    }
    s.service(now);
}

fn run_case(out: &mut String, rtt: i64, ans: i64, rej: i64, fin: i64) {
    writeln!(out, r#"{{"t":"init","rtt":{rtt},"ans":{ans},"rej":{rej},"fin":{fin}}}"#).unwrap();
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.thin = false;
    w.cfg.flight_split = false;
    w.cfg.probe_mtu = false;
    let mut w2 = World::new(IdentityAlg::Ed25519);
    (w2.cfg.thin, w2.cfg.flight_split, w2.cfg.probe_mtu) = (false, false, false);
    w2.short = true;
    let (mut sc, mut ss, mut sr) = (Store::new(true), Store::new(false), Store::new(true));
    let mut client = w.client(&mut sc, None, pinc_security::ClientTickets::new());
    let mut server = w.server(&mut ss);
    let mut rejecter = w2.client(&mut sr, None, pinc_security::ClientTickets::new());
    let mut held: Vec<Vec<u8>> = Vec::new();
    let mut done = false;
    let mut seen: Vec<(i64, &str, bool)> = Vec::new();
    for k in 0..=TICKS {
        let now = T0 + k as u64 * TICK;
        if k == ans {
            let first = drain(&mut client, now);
            to_server(&mut server, &mut w.stores, now, first);
            let answer = drain(&mut server, now);
            for mut d in answer {
                let _ = client.with_lent(now, |c, env, l| c.handle_datagram(env, l, PathId(1), &mut d));
            }
            client.service(now);
            held.extend(drain(&mut client, now));
        }
        if k == rej {
            let first = drain(&mut rejecter, now);
            to_server(&mut server, &mut w.stores, now, first);
            drain(&mut server, now);
        }
        if k == fin && !held.is_empty() {
            let finish = std::mem::take(&mut held);
            to_server(&mut server, &mut w.stores, now, finish);
        }
        while let Some(d) = server.conn.poll_timeout() {
            if d > now {
                break;
            }
            server.with_lent(d.max(T0), |c, env, l| c.handle_timeout(env, l));
            server.service(now);
            drain(&mut server, now);
        }
        let phase = server.conn.trace_timers().phase;
        done |= phase == 1;
        let r = if done {
            "done"
        } else if phase >= 2 {
            "gone"
        } else {
            "open"
        };
        let answered = server.conn.answered();
        writeln!(
            out,
            r#"{{"t":"obs","tk":{k},"r":"{r}","answered":{}}}"#,
            u8::from(answered)
        )
        .unwrap();
        seen.push((k, r, answered));
    }
    let at = |k: i64| seen[k as usize];
    for &(k, _, answered) in &seen {
        assert_eq!(
            answered,
            ans != -1 && k >= ans,
            "answered at tick {k} of {rtt} {ans} {rej} {fin}"
        );
    }
    if ans != -1 && fin != -1 && fin <= 6 {
        assert_eq!(
            at(TICKS).1,
            "done",
            "a Finish at tick {fin} did not complete: {rtt} {ans} {rej}"
        );
    }
    if ans == -1 {
        assert_eq!(at(3).1, "open", "a responder nobody dialed was gone by tick 3: {rej}");
        assert_eq!(at(4).1, "gone", "a responder nobody dialed was open at tick 4: {rej}");
    } else if fin == -1 {
        assert_eq!(at(6).1, "open", "an unfinished responder was gone by tick 6: {ans}");
        assert_eq!(at(7).1, "gone", "an unfinished responder was open at tick 7: {ans}");
    }
}

#[test]
fn responder_limit_traces() {
    let out = big_stack(|| {
        let mut out = String::new();
        let mut runs = 0;
        for (ans, rej) in [(0, -1), (1, -1), (-1, -1), (-1, 0), (-1, 1)] {
            for rtt in 1..=3i64 {
                let fins = if ans == -1 {
                    vec![-1]
                } else {
                    vec![rtt, 2 * rtt, 3 + 2 * rtt, -1]
                };
                for fin in fins {
                    run_case(&mut out, rtt, ans, rej, fin);
                    runs += 1;
                }
            }
        }
        assert_eq!(runs, 33);
        out
    });
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("responder_limit.ndjson"), out).unwrap();
    }
}
