//! Reproducing tests of bugs the `core_parts` property found in `pinc-core`: an honest handshake that one datagram
//! from a third party (or one bit error on the path) blocks until the dialer gives up. Each fails on the unmodified
//! code. The driver is `core_parts_harness`: an honest client (host 1) and server (host 2) on `core_harness`, and a
//! third party that taps their datagrams before the link's loss and sends what its rules derive from them.

mod core_harness;
mod core_parts_harness;

use core_harness::{Edit, big_stack};
use core_parts_harness::{Act, Case, Forge, Src, quiet, run};

/// The client's first flight is lost after the tap saw it (or the copy simply wins the race), and the third party
/// sends the server one exact copy of its first datagram from an address of its own.
fn replayed_first_flight(split: bool, offset: i16, drop_first: bool) -> Case {
    Case {
        delay_ms: 1,
        drop_first,
        acts: vec![Act {
            dir: 0,
            trigger: 0,
            every: false,
            forge: Forge::Copy(Vec::new()),
            src: Src::Other(0),
            offset,
        }],
        ..quiet(split)
    }
}

/// Bug: a copy of the dialer's first flight sent from another address before the dialer's own makes the server
/// answer only that address for the whole handshake, so the dialer, whose repeats reach the same session, never hears
/// the Reply and times out.
///
/// Expected: "A responder in its handshake learns the address of every handshake datagram that names its ids: the
/// dialer's flight may arrive on several paths and its last flight on one the first did not use"
/// (crates/pinc-transport/src/conn/recv.rs:186), and rx.rs: "a forged flight never displaces the first". The dialer's
/// own repeat comes from its own address and is recognised as the same Initial ("The same Initial again (a
/// retransmission, or its other form): send the same Reply again", pinc-security responder.rs:303), so the Reply
/// should reach the address the repeat came from, and the handshake complete within the 30 s connect limit.
///
/// Actual: the copy (1275 bytes from 192.0.2.1) arrives first and makes the session; its first path is that address
/// and stays the active one. Every repeat of the client is taken by that session as "the same Initial again" and
/// `out.resend()` queues the Reply, which goes out on the active path only (crates/pinc-transport/src/conn/send.rs:215
/// puts `self.paths.active` in the candidates for the flight; the client's own address is learned as an unvalidated
/// standby path and never gets the flight). The server sends 3765 bytes to 192.0.2.1 (three times what it received,
/// then the ledger holds it) and nothing to the client, which ends with `ConnectFailed { reason: Timeout }` at 30 s.
/// The same copy arriving 5 ms after the genuine flight is harmless (`a_late_copy_from_another_address_is_harmless`).
///
/// Fault: the responder's flight follows the path of the first datagram of its session
/// (crates/pinc-transport/src/conn/recv.rs:188 `learn_path` makes the first path the active one,
/// crates/pinc-transport/src/conn/path.rs:617) and a repeat of the same first message on another path does not move
/// the answer there (responder.rs:303 `self.out.resend()` with no path).
///
/// Who: an unauthenticated third party that sees the dialer's first datagram (a tap anywhere on the path, or any
/// on-path box) and sends one datagram from any address of its own (no spoofing), arriving before the dialer's copy:
/// it only has to win the race, or sit upstream of a loss of the first datagram. It needs no key and changes no byte.
/// Found by `a_third_party_never_blocks_an_honest_handshake`, `EPHYRA_REPLAY=16310380395566303574:23` (shrunk from a
/// case of three rules to this one datagram).
#[test]
fn a_first_flight_replayed_from_another_address_does_not_block_the_dialer() {
    big_stack(|| run(&replayed_first_flight(true, 0, true)));
}

/// The same with every flight cut to the minimum datagram size (the transport's default `flight_split: false`): the
/// copy is of the first part only, 1200 bytes.
#[test]
fn a_first_part_replayed_from_another_address_does_not_block_the_dialer() {
    big_stack(|| run(&replayed_first_flight(false, 0, true)));
}

/// The control: the same copy arriving after the genuine first flight is harmless.
#[test]
fn a_late_copy_from_another_address_is_harmless() {
    big_stack(|| run(&replayed_first_flight(true, 5, false)));
}

/// The first flight in two parts (the transport's default, every flight cut to 1200-byte datagrams) is lost, and in
/// its place the server gets its second datagram with one bit flipped (bit 0 of byte 19, a byte of the client's
/// encapsulation key), as a bit error on the path that the UDP checksum misses would leave it, and the first datagram
/// unchanged when `with_first` (else it was lost).
fn damaged_second_part(jitter_ms: u64, seed: u64, with_first: bool) -> Case {
    let mut acts = vec![
            Act {
                dir: 0,
                trigger: 0,
                every: false,
                forge: Forge::Copy(Vec::new()),
                src: Src::Victim,
                offset: 0,
            },
            Act {
                dir: 0,
                trigger: 1,
                every: false,
                forge: Forge::Copy(vec![Edit(12971, 0, 0)]),
                src: Src::Victim,
                offset: 0,
            },
        ];
    if !with_first {
        acts.remove(0);
    }
    Case {
        seed,
        delay_ms: 1,
        jitter_ms,
        drop_first: true,
        acts,
        ..quiet(false)
    }
}

/// Bug: a first message damaged on the way is never replaced by the dialer's repeat when the repeat comes in parts: the
/// repeat's later part waits in the endpoint's table of held fragments for 1 s, and the part that would start the new
/// session comes only with the next resend, 1 s, 2 s, 4 s ... later, so the dialer times out.
///
/// Expected: pinc-security responder.rs:324: "The held Initial was not the dialer's (a bit flipped on the way, or a
/// forgery): the dialer's own repeat differs from it, and the host starts the session again from the repeat." rx.rs
/// (`offer`): "A later part that completed a message other than every holder's: it waits for the start of that
/// message, which then gets a session of its own (see `starts_held_message`)."
///
/// Here the first datagram of the first flight was lost too (`with_first` false, the shrunk case); the next test has
/// only the bit error, on a link with a few ms of jitter.
///
/// Actual (the trace of `PBT_TRACE=1`): the damaged part is held, the first part of the first resend makes session
/// S1 with it at 501 ms, and S1 answers the damaged message. At every
/// later resend of the client (1500, 3500, 7500, 15500 ms) the first part reaches S1, which takes it as a part of a new
/// message (`take_handshake_part`, and with one holder `offer` lets it own the datagram); the second part completes
/// the genuine Initial at S1, which refuses it as `DifferentFirst`, so `offer` holds it (`fragments_held` goes 2, 3,
/// 4, 5). The start of that message is the first part of the next resend, which is 2 s or more away; by then the
/// held part is past `ORPHAN_LIFE` (`fragments_expired` 1, 2, 3, 4) and `starts_held_message` is false, so the cycle
/// repeats until `ConnectFailed { reason: Timeout }` at 30 s.
///
/// Fault: within a flight the part that starts the message leaves first, so the start of the repeat always reaches
/// the holder before the later part that `offer` holds (crates/pinc-core/src/rx.rs:192-243); only the next resend can
/// meet it, and the resend gap (500 ms doubling, crates/pinc-transport/src/conn/handshake.rs:72) is at least the
/// held part's life (`ORPHAN_LIFE`, 1 s, crates/pinc-core/src/orphan.rs:24) from the second resend on.
///
/// Who: no attacker is needed: one bit error in the first flight that leaves it parseable (most bytes of the 1184-byte
/// encapsulation key do) on any path, or a third party on the path that can send one datagram from the dialer's
/// address. The dial fails after 30 s.
#[test]
fn a_damaged_second_part_of_the_first_flight_is_recovered_from_the_repeat() {
    big_stack(|| run(&damaged_second_part(0, 0, false)));
}

/// Only the bit error (the first part arrives intact), on a link of 1 ms with up to 5 ms of jitter: the repeat's
/// second part, held at the first resend, and the first part of the second resend are 1000 ms apart on a link whose
/// delay never varies, exactly `ORPHAN_LIFE`, and further apart when the jitter delays the later one.
#[test]
fn a_damaged_second_part_is_recovered_from_the_repeat_on_a_jittery_link() {
    for seed in 0..8 {
        big_stack(move || run(&damaged_second_part(5, seed, true)));
    }
}

/// The same bit error on the endpoint's default configuration (the first flight leaves whole, only the resends are
/// cut): the repeat's first part and its held second part are 1000 ms apart at the second resend, exactly
/// `ORPHAN_LIFE`, so the session is only started again on a link whose delay never varies; with a few ms of jitter
/// it is past the life and the dial times out (`ConnectFailed { reason: Timeout }`).
#[test]
fn a_damaged_whole_first_flight_is_recovered_from_the_repeat_on_a_jittery_link() {
    for seed in 0..8 {
        big_stack(move || {
            run(&Case {
                seed,
                delay_ms: 10,
                jitter_ms: 5,
                drop_first: true,
                acts: vec![Act {
                    dir: 0,
                    trigger: 0,
                    every: false,
                    forge: Forge::Mutate {
                        at: 30,
                        xor: 1,
                        cut: 0,
                        parts: 3,
                    },
                    src: Src::Victim,
                    offset: 0,
                }],
                ..quiet(true)
            });
        });
    }
}

/// Bug: a copy of the server's Reply sent to the dialer from another address, arriving before the genuine one, moves
/// the dialer's session onto that address: the dialer reports `Connected`, sends its Finish and everything after it to
/// the third party, and the server never hears the Finish; the dialer's session dies 29 s later (`PathDead`).
///
/// Expected: the property's rule (an honest handshake completes whatever a third party sends), and
/// crates/pinc-transport/src/conn/path.rs:305 (`add_path`): "A new direct path is probed with PATH_CHALLENGE once the
/// handshake is done"; drive.rs:219: "the path that did not answer is validated only when a challenge on it is
/// answered". A path is validated by an answered challenge, never by a datagram whose source nobody checked.
///
/// Actual: the copy (1269 bytes from 192.0.2.1, the server's whole first datagram, unchanged) completes the Reply, which
/// authenticates (its bytes are the server's); `follow_reply` learns the copy's path, sets it `validated`, marks the
/// server's own path not validated and makes the copy's path the active one. The client then sends 3807 bytes to
/// 192.0.2.1 (three times what came from there, the ledger's bound) and its Finish never reaches the server, whose
/// session stays half-open (`Incoming` is never raised).
///
/// Fault: crates/pinc-transport/src/conn/drive.rs:227-248 (`follow_reply`): the authentication of the Reply's message
/// is taken as proof of the datagram's source address; a replay of an authentic message from anywhere passes it. The
/// known case of `repro_transport_link.rs` (a corrupted source id in the last Reply packet) is the same function
/// believing another field of the same datagram; this one changes no byte.
///
/// Who: a third party that sees the server's first datagram (a tap anywhere on the path) and sends one copy of it from
/// any address of its own (no spoofing), arriving first: a shorter path, an on-path box, or a loss of the genuine
/// datagram after the tap. It also points the dialer's traffic at any address it can send from. Found by
/// `a_third_party_never_blocks_an_honest_handshake_apart_from_the_known_causes`, `EPHYRA_SEED=2`,
/// `EPHYRA_REPLAY=2:28`: one injected datagram.
#[test]
fn a_reply_replayed_from_another_address_does_not_move_the_dialer() {
    big_stack(|| {
        run(&Case {
            delay_ms: 1,
            drop_first: true,
            acts: vec![Act {
                dir: 1,
                trigger: 0,
                every: false,
                forge: Forge::Copy(Vec::new()),
                src: Src::Other(0),
                offset: -1,
            }],
            ..quiet(true)
        });
    });
}

/// The control: the same copy arriving after the genuine Reply is harmless.
#[test]
fn a_late_copy_of_the_reply_from_another_address_is_harmless() {
    big_stack(|| {
        run(&Case {
            delay_ms: 1,
            acts: vec![Act {
                dir: 1,
                trigger: 0,
                every: false,
                forge: Forge::Copy(Vec::new()),
                src: Src::Other(0),
                offset: 5,
            }],
            ..quiet(true)
        });
    });
}

/// Bug: the reassembly of a first message takes a fragment from anyone who names the dialer's ids from the dialer's
/// address: one spoofed fragment of another length that lands between the two parts of each flight wipes the parts
/// before it (reassembly starts the count over), so the genuine message never completes and the dial times out.
///
/// Expected: rx.rs: "a forged flight never displaces the first"; `CONNECT_TIMEOUT` (30 s) and the property's rule.
/// crates/pinc-transport/src/conn/reasm.rs:5 documents the mechanism: "A fragment of a message of another length starts
/// the count over".
///
/// Actual (`PBT_TRACE=1`): the forged 1-byte fragment (offset 0, total 1253, the dialer's dcid and scid, padded to
/// 1200 bytes) makes a session at 6 ms. At every resend the order on a link with 9 ms of jitter is: the genuine first
/// part (total 1254), which starts the count over at 1254; the forged fragment 5 ms behind it, which starts it over at
/// 1253; the genuine second part, which starts it over at 1254 again. Nothing completes, no table counts anything
/// (`dropped_in`, `fragments_held` stay 0), the server sends nothing, and the client ends with `ConnectFailed {
/// reason: Timeout }`.
///
/// Fault: crates/pinc-transport/src/conn/reasm.rs:51-52 (`total != self.total` resets the runs): an unauthenticated
/// fragment can erase the authentic ones; and nothing ties the fragments of one message together (a digest of the
/// whole message in each fragment would keep the parts of different messages apart).
///
/// Who: a third party that sees the dialer's first flight (the ids are in clear), with one 21-byte datagram per resend
/// between the two parts (on the path, or helped by jitter as here; the case sends it 5 ms after the first part). The
/// session reassembles fragments whatever address they come from, so no spoofing is needed once the session exists
/// (`an_edited_copy_of_a_part_from_another_address_does_not_erase_the_first_message`); here the fragment also comes
/// from the dialer's address so that its first copy makes the session. Found by the same property, `EPHYRA_SEED=2`, `EPHYRA_REPLAY=2:285`:
/// one rule, two datagrams per flight (one per part).
#[test]
fn a_spoofed_fragment_of_another_length_does_not_erase_the_first_message() {
    big_stack(|| {
        run(&Case {
            seed: 2430118572310390513,
            delay_ms: 1,
            jitter_ms: 9,
            drop_first: true,
            acts: vec![Act {
                dir: 0,
                trigger: 0,
                every: true,
                forge: Forge::Total {
                    delta: -1,
                    off: 0,
                    len: 1,
                },
                src: Src::Victim,
                offset: 5,
            }],
            ..quiet(false)
        });
    });
}

/// Bug: the same cause with fragments of the same length: a copy of the first message with one byte changed, sent in
/// two parts from the dialer's address behind each genuine datagram, mixes into the reassembly of every holder. Every
/// session the server makes holds the forged message or a mixture of the two, the dialer refuses every Reply, and the
/// dial times out with four half-open sessions (the cap) and the server having sent 60 kB.
///
/// Expected: as above; rx.rs: "a first flight that every holder says differs from its own gets a half-open session of
/// its own under the same id, up to four holders, so a forged flight never displaces the first".
///
/// Actual (`PBT_TRACE=1`): the forgery (the later part first, then a 1-byte start) makes S1 at 1 ms with the forged
/// message. At each resend the genuine first part, the forged later part and the forged start overwrite each other's
/// bytes in S1 (`copy_from_slice` over a run already held) and the genuine second part completes a message that is
/// not the dialer's; the held parts start S2, S3, S4 the same way. The client takes every datagram (`dropped_in` 3)
/// and accepts no Reply; `ConnectFailed { reason: Timeout }`.
///
/// Fault: crates/pinc-transport/src/conn/reasm.rs:47-88 (`add` keeps the last bytes written to an offset, from any
/// sender), as above.
///
/// Who: as above, with one forged message per datagram of each flight, sent right behind it (not racing it). Found by
/// the same property, `EPHYRA_SEED=1` and `EPHYRA_SEED=3`, `EPHYRA_REPLAY=1:334` and `3:213`.
#[test]
fn spoofed_fragments_of_the_same_length_do_not_corrupt_the_first_message() {
    big_stack(|| {
        run(&Case {
            delay_ms: 1,
            drop_first: true,
            acts: vec![Act {
                dir: 0,
                trigger: 0,
                every: true,
                forge: Forge::Mutate {
                    at: 3,
                    xor: 1,
                    cut: 1,
                    parts: 0,
                },
                src: Src::Victim,
                offset: 0,
            }],
            ..quiet(false)
        });
    });
}

/// The same cause from the third party's own address (no spoofing), off the path: after a lossy start (72 per mille
/// for 1.5 s), a copy of the dialer's second datagram with one byte of its header doubled (so it parses as a fragment
/// at another offset or of another length) arrives from 192.0.2.1 13 ms after each genuine one, and the dial times out.
/// Found by the property, `EPHYRA_SEED=4`, `EPHYRA_REPLAY=4:3632`: one rule, one datagram per flight.
#[test]
fn an_edited_copy_of_a_part_from_another_address_does_not_erase_the_first_message() {
    big_stack(|| {
        run(&Case {
            seed: 177079125032515673,
            delay_ms: 1,
            jitter_ms: 7,
            drop_first: true,
            loss: 72,
            lossy_ms: 1502,
            acts: vec![Act {
                dir: 0,
                trigger: 1,
                every: true,
                forge: Forge::Copy(vec![Edit(13654, 73, 0)]),
                src: Src::Other(0),
                offset: 13,
            }],
            ..quiet(false)
        });
    });
}
