//! `pinc-core`: can a third party block an honest handshake with datagrams of its own? An honest client dials an
//! honest server (real endpoints, `core_harness`) over a link that is lossy for a while and then clean, while a third
//! party that sees the datagrams of the two on their way (a tap, before any loss) sends the endpoints datagrams it
//! derives from them: copies with edits, the first message with a byte changed (whole or cut in parts), fragments
//! with another message length, fragments that overwrite a range of the message. It uses only what crosses the wire in
//! clear (the connection ids and the handshake messages), sends from its own addresses or from the address of the
//! honest sender (a spoofed source), and its datagram may arrive before the genuine one (it races it: it sits on the
//! path or has a shorter one) or after it (off the path).
//!
//! Where the expected behaviour comes from:
//! - `pinc_core` rx.rs: "a first flight that every holder says differs from its own gets a half-open session of its
//!   own under the same id, up to four holders, so a forged flight never displaces the first", and "A later part of a
//!   first message that arrives before the part that starts it is held for a moment ... and handed to the session
//!   once the first part has created it".
//! - `pinc_security` responder.rs (`on_initial`): "The held Initial was not the dialer's (a bit flipped on the way, or
//!   a forgery): the dialer's own repeat differs from it, and the host starts the session again from the repeat."
//! - The half-open cap row of `docs/proofs/properties.md`: "An unauthenticated session lives the node's connect
//!   limit, 30 s ... and at least 60 s once it answered as a responder ... so never above 60 s; it is there at
//!   `created + life` and gone one tick past it".
//! - `pinc_transport` handshake.rs: `CONNECT_TIMEOUT` is "How long an unestablished handshake lasts on a node that is
//!   not thin" (30 s), and a dialing side resends its first flight on a doubling schedule from 500 ms.
//!
//! So: once the link is clean (from at most 6 s after the dial, so at least one resend of the first flight crosses
//! it before the connect limit), the honest handshake completes within the 30 s connect limit whatever the third
//! party sent, and every table stays within its bound after every step (`core_harness::Host::check_stats`); 61 s
//! after the last datagram that could have made a half-open session, none is left.

mod core_harness;
mod core_parts_harness;

use core_harness::big_stack;
use core_parts_harness::{Case, in_support, quiet, run, run_with};
use ephyra::check_generator;

#[test]
fn a_third_party_never_blocks_an_honest_handshake() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(40)
            .name("a_third_party_never_blocks_an_honest_handshake");
        ephyra::check(&config, ephyra::any::<Case>(), |c: Case| run(&c)).assert_passed();
    });
}

/// The same property with the known causes (`repro_core2.rs`, `core_parts_harness::known_cause`) let through, so the
/// search finds the others.
#[test]
fn a_third_party_never_blocks_an_honest_handshake_apart_from_the_known_causes() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(40)
            .name("a_third_party_never_blocks_an_honest_handshake_apart_from_the_known_causes");
        ephyra::check(&config, ephyra::any::<Case>(), |c: Case| run_with(&c, true)).assert_passed();
    });
}

#[test]
fn the_third_party_case_generator_stays_in_support() {
    let cfg = ephyra::Config::default().tests(300);
    check_generator(&cfg, ephyra::any::<Case>(), in_support).assert_passed();
}

#[test]
fn an_honest_handshake_completes_with_no_third_party() {
    big_stack(|| {
        run(&quiet(true));
        run(&quiet(false));
    });
}

/// The first flight is lost after the tap, and a copy of it with one byte of the client's ephemeral key changed
/// (which still parses) arrives in its place, as a bit error on the path would leave it: the client's own repeat
/// must start the session again ("the dialer's own repeat differs from it, and the host starts the session again from
/// the repeat", pinc-security responder.rs).
#[test]
fn a_first_flight_damaged_on_the_way_is_recovered_from_its_repeat() {
    use core_parts_harness::{Act, Forge, Src};
    for split in [true, false] {
        big_stack(move || {
            run(&Case {
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
                ..quiet(split)
            });
        });
    }
}
