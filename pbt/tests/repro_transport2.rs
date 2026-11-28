//! Reproducing tests of bugs the `timers_due` properties found in `pinc-transport` timers. Each fails on the
//! unmodified code. The drivers are `timers_due_conn` (a bare pair of connections) and `timers_due_harness` (a pair of
//! `pinc-core` endpoints).

mod core_harness;
mod timers_due_conn;
mod timers_due_harness;

use core_harness::big_stack;
use timers_due_conn::{CCase, COp};
use timers_due_harness::{Case, Op};

/// Bug: the keepalive timer stays due while its PING cannot leave: with the in-flight ring full, the connection
/// asks to be woken at an instant already past after every `handle_timeout`, until an acknowledgement or a loss frees
/// a slot of the ring.
///
/// Expected: `Connection::poll_timeout` is "The next time [`handle_timeout`] must run"
/// (crates/pinc-transport/src/conn/timer.rs:29); timer.rs:3: "a timer is reported only while it can still act (a
/// stale deadline would make a driver spin)". The acknowledgement timer is already gated this way (timer.rs:58, only
/// with room to send).
///
/// Actual: the dialer sleeps (it acknowledges nothing), the server's keepalive of 1 ms fills its ring with PINGs, and
/// from 543 ms after the dial `poll_timeout()` returns the same past instant after `handle_timeout` and `poll_transmit`
/// (`recovery().ring_has_room()` and `can_send()` false; the loss timer is 1 s later). A real event loop spins on the
/// CPU until then.
///
/// Fault: crates/pinc-transport/src/conn/timer.rs:66 adds `last_sent + keepalive` with no gate on whether a packet
/// can be built; the PING is a forced packet of `build_app` (conn/send.rs:407-409) and needs ring room. The known
/// key-roll case (`repro_transport_link.rs`, timer.rs:56) is the same missing gate on another timer: fixing that one
/// does not fix this one.
///
/// Who: any application that sets a keepalive while its peer acknowledges nothing for a while (it sleeps, its link is
/// down, the path drops everything) and the ring fills; `pinc-core` sets one on every session (keepalive.rs: 5 s, 40 s,
/// 60 s or 70 s), see the next test. Found by `no_connection_timer_stays_due_after_it_ran`,
/// `EPHYRA_REPLAY=5223478271764586093:7056`, and near the end of the clock by the same property (`:3438`, `:8181`).
#[test]
fn the_keepalive_timer_does_not_stay_due_while_its_ping_cannot_be_sent() {
    big_stack(|| {
        timers_due_conn::run(&CCase {
            end: 0,
            delay_ms: 1,
            flight_split: false,
            ops: vec![COp::Sleep(0), COp::Keepalive { from: 1, ms: 1 }, COp::Wait(1)],
        });
    });
}

/// The same bug on `pinc-core` endpoints with their own keepalive schedule: the server writes 127 kB and then 262 kB
/// while the dialer suspends (`Command::Suspend`); 40 s after the dialer said it sleeps (the keepalive of a plain
/// session, `pinc-core` keepalive.rs) the server's `Endpoint::poll_timeout()` stays at a past instant after
/// `handle_timeout` and `poll_transmit`. Without the writes (nothing fills the ring) the same run passes. Found by
/// `no_timer_stays_due_after_it_ran`, `EPHYRA_REPLAY=17047169529368638292:1066` (and `:1514`, `:7969`, `:12484`,
/// `:23230`, all with a sleeping peer and a large write).
#[test]
fn an_endpoint_keepalive_does_not_stay_due_while_the_peer_sleeps() {
    big_stack(|| {
        timers_due_harness::run(&Case {
            seed: 0,
            split: false,
            room: false,
            delay_ms: 1,
            jitter_ms: 0,
            ops: vec![
                Op::Write {
                    from: 1,
                    len: 127_301,
                    fin: true,
                },
                Op::Sleep(0),
                Op::Write {
                    from: 1,
                    len: 262_145,
                    fin: false,
                },
            ],
        });
    });
}

/// The control: a keepalive of 5 s toward a sleeping peer, with nothing written, keeps the rule.
#[test]
fn a_keepalive_toward_a_sleeping_peer_with_room_in_the_ring_keeps_the_rule() {
    big_stack(|| {
        timers_due_conn::run(&CCase {
            end: 0,
            delay_ms: 1,
            flight_split: false,
            ops: vec![COp::Sleep(0), COp::Keepalive { from: 1, ms: 5_000 }, COp::Wait(60_000)],
        });
    });
}
