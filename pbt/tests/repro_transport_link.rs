//! Reproductions of bugs `transport_link.rs` found: two real connections over a scripted link (the harness is
//! `transport_harness.rs`). Each test fails on the code it was found on and names the bug.
#![allow(clippy::unwrap_used)]

#[path = "transport_harness.rs"]
mod harness;

use harness::*;

fn knobs(key_update_after: u64, ack_every: Option<u32>, keepalive: Option<u64>) -> Knobs {
    Knobs {
        key_update_after,
        max_gso: 1,
        flight_split: false,
        ack_every,
        keepalive,
        probe_mtu: false,
    }
}

/// A connection that rolls its keys while its in-flight ring is full, on a 10 ms link that truncates and holds
/// some datagrams for the first 796 ms.
fn rekey_case(key_update_after: u64) -> Case {
    use Fate::Deliver as D;
    Case {
        delay: 10,
        chaos: 796,
        early: true,
        fates: vec![Fate::Truncate(36), D, D, Fate::Hold(235), D, D, Fate::Truncate(342), D],
        client_streams: vec![(true, 399_093), (true, 351_467)],
        server_streams: vec![58_016],
        datagrams: vec![],
        chunks: 256,
        knobs: knobs(key_update_after, Some(3), Some(10_529_764_314)),
    }
}

/// Bug: the key-roll timer stays due while its REKEY cannot leave, so the connection asks to be woken at an
/// instant already past, again and again, until an acknowledgement frees the ring.
///
/// Expected: `Connection::poll_timeout` is "The next time [`handle_timeout`] must run"
/// (crates/pinc-transport/src/conn/timer.rs:29). Once `handle_timeout` ran at that time with nothing it can do, the
/// next time is later, as the pacing timer already ensures ("with nothing to send, a poll inside the pacing gap
/// would arm a timer that wakes the endpoint for no reason", conn/send.rs:401) and the acknowledgement timer
/// (timer.rs:58, only with room to send).
///
/// Actual: with `key_update_after` 194 the client begins a roll, the request's resend deadline
/// (`request_at + pto`, conn/keys.rs:280) comes due at 831.609527 ms while `recovery().ring_has_room()` and
/// `can_send()` are both false. Control frames, REKEY among them, are written only with ring room
/// (conn/send.rs:714), so `poll_rekey` is never reached, `request_at` never moves, and `poll_timeout` keeps
/// returning 1000831609527 after every `handle_timeout` (20000 calls at that instant in the harness). The loss
/// timer is 131 us later; a real event loop spins on the CPU until then or until an acknowledgement arrives, up to a
/// round trip. The same case with `key_update_after` 2^21 completes (`rekey_deadline_case_completes_without_a_roll`).
///
/// Fault: conn/timer.rs:56 adds `rekey_deadline()` with no gate on whether the REKEY can be written
/// (conn/send.rs:714 `ring_room`).
///
/// Who: any connection that rolls its keys (by default every 2^21 packets, `Config::key_update_after`) while its
/// in-flight ring is full, which a bulk sender reaches and a peer can prolong by acknowledging slowly.
///
/// Found by `two_connections_deliver_every_byte_over_a_scripted_link`, `EPHYRA_SEED=7002`, replay
/// `EPHYRA_REPLAY=7002:5299`.
#[test]
fn the_key_roll_timer_does_not_stay_due_while_the_request_cannot_be_sent() {
    big_stack(|| run(&rekey_case(194)));
}

/// The control for the test above: the same link and data with no key roll completes.
#[test]
fn rekey_deadline_case_completes_without_a_roll() {
    big_stack(|| run(&rekey_case(2_097_152)));
}

/// A handshake over a 30 ms link with one corrupted datagram, the fifth one sent.
fn handshake_case(fates: Vec<Fate>) -> Case {
    Case {
        delay: 30,
        chaos: 34,
        early: true,
        fates,
        client_streams: vec![(false, 1000)],
        server_streams: vec![],
        datagrams: vec![],
        chunks: 64,
        knobs: Knobs::default_config(),
    }
}

/// Bug: a dialing side takes the server's connection id from the unauthenticated long header of the packet that
/// completes the Reply, not from the `scid_R` the authenticated Reply carries, so one changed header byte makes it
/// address every later packet to an id the server does not have, and the connection dies.
///
/// Expected: "A dialing side believes nothing of the packet itself: its path (held or not) and source id count only
/// once the message it completes has authenticated (`follow_reply`)" (crates/pinc-transport/src/conn/recv.rs:266).
/// The Reply carries `scid_R` (crates/pinc-security/src/message.rs:14) and the initiator absorbs it into the
/// transcript (crates/pinc-security/src/initiator.rs:562), so the authenticated id is at hand; a header that disagrees
/// should be dropped like any other corrupt packet, and the handshake should finish once the link is clean.
///
/// Actual: the server's Reply leaves in a 1200-byte and an 86-byte Handshake datagram. Flipping bit 0 of byte 11 of
/// the second (the last byte of the 4-byte source id: flags, version, dcid length, dcid, scid length, scid) is
/// accepted: `on_handshake` returns Ok, `reply_from` records `header.scid` (recv.rs:288), and `follow_reply` sets it
/// as the remote id (conn/drive.rs:229). Every 1-RTT packet of the client then reaches the server as
/// `Drop::Unroutable`; the server closes with `PathDead` (the client with `HandshakeTimeout` in other cases). The
/// same flip on the sixth datagram (the client's) is tolerated: the connection completes.
///
/// Fault: conn/recv.rs:288 records the header's `scid` and conn/drive.rs:229 believes it; `Established`
/// (crates/pinc-security/src/session.rs:109) does not hand back the authenticated `scid_R` to check it against.
///
/// Who: anyone on the path who can change one byte of one datagram of the handshake (a bit error that the UDP
/// checksum misses, or an on-path party) turns a recoverable corruption into a dead connection; the server's
/// packet-level drop of a corrupt packet, which every other byte gets, does not cover these four bytes.
///
/// Found by `two_connections_deliver_every_byte_over_a_scripted_link`, `EPHYRA_SEED=7002`, replays
/// `EPHYRA_REPLAY=7002:3433` (server `PathDead`), `EPHYRA_REPLAY=7002:10928` (write refused after the close) and
/// `EPHYRA_REPLAY=7002:7572` (byte 8, the first of the id: no byte arrives once the link is clean).
#[test]
fn a_corrupted_source_id_in_the_last_reply_packet_is_not_believed() {
    use Fate::Deliver as D;
    big_stack(|| run(&handshake_case(vec![D, D, D, D, Fate::Corrupt { at: 11, xor: 1 }])));
}
