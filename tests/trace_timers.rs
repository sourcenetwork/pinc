//! Trace generation for the timers and the closing state of the VINCER connection: scripted pairs of real connections
//! (`vinc-transport`, built with the `trace` feature) driven call by call, recorded as ndjson (`timers.ndjson`) for
//! the TLA+ trace check (`TraceTimers.tla`) and the Lean replay (`Vinc/TraceTimers.lean`).
//!
//! Two connections are connected over the in-memory link, then the test takes over: every datagram either side writes
//! goes to a pool, and the script decides which reaches the other side, when, again (a duplicate) or altered (it
//! does not authenticate), or never. Each call of the connection's API is one event with the time, what the call
//! returned, the lifecycle events it reported and the state of the timers right after it ([`TimerView`]: the
//! lifecycle fields and every deadline `poll_timeout` reads). The calls are `poll_timeout`, `handle_timeout` (at the
//! time `poll_timeout` named, just before it, and at other times), `poll_transmit`, `handle_datagram`, `close`, frames
//! injected that do not decode or break a rule, `sleep`, `wake`, `set_link_down`, `set_keepalive`, `pulse` and the
//! application's opens and writes. The scenarios: random runs with traffic, loss, duplicates, sleep and wake, link
//! outages, keepalives and closes; the idle timeout on both sides; a local close and its one CLOSE; a close whose
//! connection reaches a timer first; violations; a sleeping peer held 120 s; an unanswered WAKE; a link outage past
//! 30 s; a dial nobody answers, until its handshake gives up; a close while handshaking; a dialing side whose Finish
//! never reached the responder (the test takes over once the dialing side is connected), which ends the session
//! unconfirmed at its connect limit counted from when it established (30 s, 60 s on a thin node, the limit following
//! the node's kind when it changes) while the responder's handshake runs out; sessions whose probes time out with
//! nothing coming back while the relay's carrier answers (`set_carrier_heard`), on a relay path with a fresh carrier,
//! which a 4th probe timeout closes with a CLOSE (with and without a round-trip sample: a lost first flight leaves the
//! handshake with none), and the near misses (3 probe timeouts, a carrier heard 6 s ago, a carrier never open, a
//! direct path, the peer heard just before). Each call carries what the recovery timer read for that rule
//! (`CarrierView`), and the test checks that the rule's own decision, taken from those reads in nanoseconds and in the
//! rounded microseconds the checkers take, is the same, that the close happened exactly then, and that every case above
//! was reached.
//!
//! Times are written in whole microseconds, rounded up (every time the test drives is a whole microsecond, so each
//! comparison with a deadline keeps its result, and the minimum `poll_timeout` takes commutes with the rounding); a
//! component deadline at or past the largest 32-bit checker integer is written as it (it is never the minimum: the
//! idle deadline is always below it).
//!
//! The test checks by itself what it can see from outside: at most one CLOSE leaves a connection, a closed connection
//! has no timer, writes nothing and refuses datagrams and opens, and the idle timeout, the unanswered WAKE and the end
//! of a session its peer never confirmed are reported at the time the constants say.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::fn_params_excessive_bools,
    clippy::panic,
    clippy::large_stack_arrays,
    clippy::needless_range_loop,
    unreachable_pub
)]

#[path = "trace_timers/duo.rs"]
mod duo;
#[path = "trace_timers/lifecycle.rs"]
mod lifecycle;
#[path = "trace_timers/random.rs"]
mod random;
#[path = "trace_timers/rec.rs"]
mod rec;
#[path = "trace_timers/relay.rs"]
mod relay;
#[path = "trace_timers/unconfirmed.rs"]
mod unconfirmed;

use vinc_tests::*;

use lifecycle::{close_run, dead_run, idle_run, link_run, sleep_hold_run, violation_run, wake_run};
use random::random_run;
use rec::Log;
use relay::{Carrier, relay_run};
use unconfirmed::{dial_run, unconfirmed_run};

#[test]
fn timers_match_the_models() {
    big_stack(|| {
        let mut log = Log {
            out: String::new(),
            run: 0,
            closes: [0; 2],
            seen: std::collections::BTreeMap::new(),
        };
        let next = |log: &mut Log| {
            log.run += 1;
            log.closes = [0; 2];
        };
        for seed in 1..=4 {
            next(&mut log);
            idle_run(&mut log, 100 + seed);
        }
        for (i, (timer_first, talk)) in [(false, false), (true, false), (false, true), (true, true)]
            .into_iter()
            .enumerate()
        {
            next(&mut log);
            close_run(&mut log, 200 + i as u64, timer_first, talk);
        }
        for (i, bad) in [true, false].into_iter().enumerate() {
            next(&mut log);
            violation_run(&mut log, 300 + i as u64, bad);
        }
        next(&mut log);
        sleep_hold_run(&mut log, 400);
        for (i, answered) in [false, true].into_iter().enumerate() {
            next(&mut log);
            wake_run(&mut log, 500 + i as u64, answered);
        }
        next(&mut log);
        link_run(&mut log, 600);
        for seed in 0..2 {
            next(&mut log);
            dead_run(&mut log, 650 + seed);
        }
        for (i, c) in [None, Some(2 * SEC)].into_iter().enumerate() {
            next(&mut log);
            dial_run(&mut log, 700 + i as u64, c);
        }
        for (i, (thin, turn)) in [
            (false, None),
            (true, None),
            (false, Some((10 * SEC, true))),
            (true, Some((40 * SEC, false))),
        ]
        .into_iter()
        .enumerate()
        {
            next(&mut log);
            unconfirmed_run(&mut log, 750 + i as u64, thin, turn);
        }
        for (i, (relay, carrier, node)) in [
            (true, Carrier::Fresh, None),
            (true, Carrier::Edge, None),
            (true, Carrier::Stale, None),
            (true, Carrier::Never, None),
            (true, Carrier::Heard, None),
            (false, Carrier::Fresh, None),
            (true, Carrier::Fresh, Some(300 * MS)),
        ]
        .into_iter()
        .enumerate()
        {
            next(&mut log);
            relay_run(&mut log, 800 + i as u64, relay, carrier, node, i % 2, false);
        }
        // the same with no round-trip sample: the first flight of the dial was lost, the handshake measured none
        for (i, (carrier, node, side)) in [
            (Carrier::Fresh, None, 0),
            (Carrier::Fresh, Some(300 * MS), 0),
            (Carrier::Fresh, Some(900 * MS), 0),
            (Carrier::Heard, None, 0),
            (Carrier::Fresh, None, 1),
            (Carrier::SilentHit, None, 0),
            (Carrier::SilentMiss, None, 0),
            (Carrier::SilentHit, Some(900 * MS), 0),
            (Carrier::SilentMiss, Some(900 * MS), 0),
        ]
        .into_iter()
        .enumerate()
        {
            next(&mut log);
            relay_run(&mut log, 850 + i as u64, true, carrier, node, side, true);
        }
        for seed in 1..=24u64 {
            next(&mut log);
            random_run(&mut log, 1000 + seed, 400);
        }
        for k in [
            "idle",
            "local",
            "peer",
            "viol",
            "dead",
            "hs",
            "unconf",
            "asleep",
            "awake",
            "unanswered",
            "inject",
            "link",
            "keepalive",
            "pulse",
            "sleep",
            "wake",
            "carrier_close",
            "carrier_close_sampled",
            "carrier_close_unsampled",
            "near_pto3",
            "near_stale",
            "near_nocarrier",
            "near_direct",
            "near_heard_sampled",
            "near_heard_unsampled",
        ] {
            assert!(
                log.seen.get(k).copied().unwrap_or(0) > 0,
                "the scenarios never reached {k}: {:?}",
                log.seen
            );
        }
        eprintln!("timers: {} events {:?}", log.out.lines().count(), log.seen);
        if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("timers.ndjson"), &log.out).unwrap();
        }
    });
}
