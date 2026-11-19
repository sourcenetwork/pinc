//! The scripted lifecycle runs of the timers trace: idle timeout, local close, violation, sleep hold, WAKE, silent end
//! and link outage.

use pinc_tests::*;
use pinc_transport::conn::{IDLE_TIMEOUT, PathId};

use crate::duo::{How, app, close, inject, simple, with_pair};
use crate::rec::Log;

/// Nothing is heard: both sides close for idleness at the first timer call at or after 75 s of silence, and not a
/// microsecond earlier.
pub fn idle_run(log: &mut Log, seed: u64) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        d.lose_all();
        for n in 0..2 {
            let idle = d.nodes[n].conn.trace_timers().idle;
            assert_eq!(idle, d.nodes[n].conn.trace_timers().last_activity + IDLE_TIMEOUT);
        }
        let mut closed = [false; 2];
        for _ in 0..400 {
            // the recovery timers fire meanwhile; their probes are lost
            if !d.advance_to_next(log) {
                break;
            }
            for n in 0..2 {
                d.tx(log, n);
            }
            d.lose_all();
            for n in 0..2 {
                let v = d.nodes[n].conn.trace_timers();
                if v.phase == 1 && d.now.div_ceil(1000) * 1000 + 1000 <= v.idle && v.idle < d.now + SEC {
                    // just before the deadline: nothing
                    let at = v.idle.div_ceil(1000) * 1000 - 1000;
                    if at >= d.now {
                        d.now = at;
                        let ev = d.timeout(log, n);
                        assert!(!ev.contains(&"idle"), "closed for idleness before the deadline");
                    }
                }
            }
            for n in 0..2 {
                if !closed[n] && d.nodes[n].conn.is_closed() {
                    closed[n] = true;
                }
            }
            if closed.iter().all(|c| *c) {
                break;
            }
        }
        assert!(closed.iter().all(|c| *c), "an idle connection stayed open");
        // closed: no timer, nothing written, nothing taken
        for n in 0..2 {
            assert!(d.poll(log, n).is_none());
            assert_eq!(d.tx(log, n), 0);
            app(log, n, &mut d.nodes[n], d.now, 10);
        }
    });
}

/// A local close: one CLOSE, then nothing; the peer ends silently on it.
pub fn close_run(log: &mut Log, seed: u64, timer_first: bool, keep_talking: bool) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        if keep_talking {
            app(log, 1, &mut d.nodes[1], d.now, 5000);
            d.tx(log, 1);
        }
        d.now += 3 * MS;
        let err = seed % 0x40;
        close(log, 0, &mut d.nodes[0], d.now, err);
        assert!(d.nodes[0].conn.is_closed());
        assert_eq!(d.poll(log, 0), Some(0));
        if timer_first {
            // the timer comes before the CLOSE is written: the connection is over and nothing leaves
            d.timeout(log, 0);
            assert_eq!(d.tx(log, 0), 0);
            assert_eq!(log.closes[0], 0);
        } else {
            assert_eq!(d.tx(log, 0), 1, "one CLOSE");
            assert_eq!(log.closes[0], 1);
        }
        d.deliver_all(log);
        if !timer_first {
            assert!(d.nodes[1].conn.is_closed(), "the peer took the CLOSE");
            assert_eq!(d.tx(log, 1), 0, "the peer's end is silent");
        }
        for _ in 0..3 {
            d.now += SEC;
            d.fire(log);
            for n in 0..2 {
                d.tx(log, n);
                app(log, n, &mut d.nodes[n], d.now, 10);
            }
            d.deliver_all(log);
            // a datagram for a closed connection: refused
            if !d.pool.is_empty() {
                d.deliver(log, 0, How::Again);
            }
        }
        assert!(log.closes[0] <= 1 && log.closes[1] == 0);
    });
}

/// A violation: injected frames that do not decode, or that acknowledge a packet never sent; one CLOSE follows.
pub fn violation_run(log: &mut Log, seed: u64, bad: bool) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        d.now += 5 * MS;
        inject(log, 1, &mut d.nodes[1], d.now, PathId(2), bad);
        assert!(d.nodes[1].conn.is_closed());
        assert_eq!(d.tx(log, 1), 1);
        d.deliver_all(log);
        d.now += SEC;
        d.fire(log);
        d.tx(log, 0);
        d.tx(log, 1);
    });
}

/// A peer that announced its sleep is held 120 s: no idle close at 75 s, a close at the first timer call 120 s after
/// its last SLEEP.
pub fn sleep_hold_run(log: &mut Log, seed: u64) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        d.now += 10 * MS;
        simple(log, 0, &mut d.nodes[0], d.now, "sleep", 0);
        d.tx(log, 0);
        d.deliver_all(log);
        d.tx(log, 0);
        d.tx(log, 1);
        assert!(d.nodes[1].conn.peer_asleep());
        // nothing more is heard from the sleeper, and what the held side sends is lost
        d.lose_all();
        let pa = d.nodes[1].conn.trace_timers().peer_asleep.unwrap();
        for _ in 0..400 {
            if !d.advance_to_next(log) || d.nodes[1].conn.is_closed() {
                break;
            }
            d.tx(log, 1);
            d.lose_all();
            if d.now < pa + 120 * SEC {
                assert!(
                    !d.nodes[1].conn.is_closed(),
                    "the sleeping peer was let go before 120 s"
                );
            }
        }
        assert!(d.nodes[1].conn.is_closed());
        assert!(d.now >= pa + 120 * SEC);
    });
}

/// A WAKE nobody answers is reported 800 ms later; an answer in time clears the wait.
pub fn wake_run(log: &mut Log, seed: u64, answered: bool) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        d.now += 10 * MS;
        simple(log, 0, &mut d.nodes[0], d.now, "sleep", 0);
        d.tx(log, 0);
        d.lose_all();
        d.now += 2 * SEC;
        d.fire(log);
        let at = d.now;
        simple(log, 0, &mut d.nodes[0], d.now, "wake", 0);
        d.tx(log, 0);
        if answered {
            d.deliver_all(log);
            d.tx(log, 1);
            d.now += 50 * MS;
            d.deliver_all(log);
        } else {
            d.lose_all();
        }
        let mut cleared = d.nodes[0].conn.trace_timers().wake_deadline.is_none().then_some(d.now);
        if answered {
            assert!(cleared.is_some(), "the answer did not end the wait");
        }
        for _ in 0..100 {
            if d.now >= at + 2 * SEC {
                break;
            }
            if d.next_deadline().is_none_or(|t| t > at + 2 * SEC) {
                d.now = at + 2 * SEC;
                d.fire(log);
            } else {
                d.advance_to_next(log);
            }
            if cleared.is_none() && d.nodes[0].conn.trace_timers().wake_deadline.is_none() {
                cleared = Some(d.now);
            }
            d.tx(log, 0);
            d.tx(log, 1);
            if answered {
                d.deliver_all(log);
            } else {
                d.lose_all();
            }
        }
        if !answered {
            assert_eq!(
                cleared,
                Some(at + 800 * MS),
                "the unanswered WAKE is reported at 800 ms"
            );
        }
    });
}

/// Data in flight and nothing comes back: recovery gives up (or the idle timeout comes first), silently.
pub fn dead_run(log: &mut Log, seed: u64) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        app(log, 0, &mut d.nodes[0], d.now, 20_000);
        for _ in 0..2000 {
            d.tx(log, 0);
            d.tx(log, 1);
            d.lose_all();
            if d.nodes[0].conn.is_closed() || !d.advance_to_next(log) {
                break;
            }
        }
        assert!(d.nodes[0].conn.is_closed());
        assert_eq!(log.closes, [0, 0], "a silent end sent a CLOSE");
        assert_eq!(d.tx(log, 0), 0);
    });
}

/// A link outage longer than 30 s: the freeze ends by itself at 30 s.
pub fn link_run(log: &mut Log, seed: u64) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        app(log, 0, &mut d.nodes[0], d.now, 20_000);
        d.tx(log, 0);
        d.lose_all();
        d.now += 5 * MS;
        simple(log, 0, &mut d.nodes[0], d.now, "link", 1);
        let down = d.now;
        for _ in 0..200 {
            if !d.advance_to_next(log) || d.now > down + 40 * SEC {
                break;
            }
            d.tx(log, 0);
            d.tx(log, 1);
            d.lose_all();
        }
        assert!(
            d.nodes[0].conn.trace_timers().link_down.is_none(),
            "the outage outlived its bound"
        );
        simple(log, 0, &mut d.nodes[0], d.now, "link", 0);
        d.exchange(log);
    });
}
