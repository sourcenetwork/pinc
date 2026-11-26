//! Reproductions of bugs the `transport*` properties found in `pinc-transport`. Each test fails on the code it was
//! found on and names the bug.
#![allow(clippy::unwrap_used)]

use pinc_transport::recovery::{FrameRef, FrameRefs, Recovery, SECOND, Sent};

/// The probe timer near the end of the clock: after it fires at its deadline, it must move to a later deadline.
///
/// Expected: `recovery::deadline_after` documents the rule every timer of the module follows: "A deadline saturated
/// at u64::MAX could never be later than a call made at u64::MAX, so it would fire on every call." A timer that fired
/// at `t` is next due after `t`, so a driver that waits for `next_timeout()` makes progress.
///
/// Actual: `Recovery::pto_deadline` (crates/pinc-transport/src/recovery/pto.rs:57) adds the backed-off probe timeout
/// to the send time with `saturating_add`. When that sum passes `u64::MAX` the deadline is `u64::MAX`; firing at
/// `u64::MAX` leaves `next_timeout() == Some(u64::MAX)`, so every further call fires again at the same instant and
/// each firing declares another packet lost and bumps the probe count. The shrunk counterexample of
/// `recovery_matches_the_model_near_the_end_of_the_clock` is the same: replay `EPHYRA_REPLAY=18109605289167201268:1`.
///
/// Who can trigger it: the local application, through the clock it passes to the connection (a clock within a probe
/// timeout of `u64::MAX` nanoseconds, for example a monotonic clock with a large base). A remote peer cannot.
#[test]
fn probe_timer_stays_due_after_firing_at_the_end_of_the_clock() {
    let mut rec = Recovery::<48>::new(1200);
    let start = u64::MAX - SECOND / 2;
    for _ in 0..5 {
        let pn = rec.next_pn();
        let mut frames = FrameRefs::new();
        frames
            .push(FrameRef::Stream {
                id: 0,
                offset: pn * 100,
                len: 100,
                fin: false,
            })
            .unwrap();
        rec.on_packet_sent(Sent {
            pn,
            time: start,
            size: 100,
            path: 0,
            is_repair: false,
            is_mtu_probe: false,
            frames,
        })
        .unwrap();
    }
    let mut fired = Vec::new();
    for _ in 0..4 {
        let Some(t) = rec.next_timeout() else { break };
        rec.on_timeout(t, |_| {});
        fired.push(t);
        let next = rec.next_timeout();
        assert!(
            next.is_none_or(|n| n > t),
            "the timer fired at {t} and is still due at {next:?} (fired at {fired:?})"
        );
    }
}
