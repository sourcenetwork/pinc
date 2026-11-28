//! `pinc-transport` end to end: two real connections (a client and a server, the public API an application uses)
//! joined by a link whose every datagram is delivered, dropped, repeated, delayed past later ones, cut short or
//! corrupted by a generated schedule, on virtual time. After a stretch of chaos the link turns clean.
//!
//! Where the expected behaviour comes from:
//! - `conn` module docs: "running out drops data (a received packet is not acknowledged, so the peer sends it again)
//!   and never overflows. Nothing allocates per packet and no input panics"; "A datagram never exceeds the datagram
//!   size of its path".
//! - `stream` module docs and `Connection::write` / `read_chunk` / `consume`: a stream delivers the bytes written,
//!   in order, once; the end is seen after the last byte (`RecvStatus::Finished`).
//! - `stream::datagram`: an unreliable datagram arrives at most once and unchanged (a duplicate packet is dropped by
//!   the received-packet set: "a forgotten packet is dropped as a duplicate rather than processed twice").
//! - Universal: neither side closes the connection on a link that loses at most part of its datagrams for a few
//!   seconds (the idle timeout is 75 s); after the link turns clean the transfer completes within a bounded span of
//!   virtual time; the driver loop makes progress (a timer that fired moves on).
#![allow(clippy::unwrap_used)]

#[path = "transport_harness.rs"]
mod harness;

use harness::*;

#[test]
fn two_connections_deliver_every_byte_over_a_scripted_link() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(150)
            .name("two_connections_deliver_every_byte_over_a_scripted_link");
        ephyra::check(&config, case(), |c: Case| run(&c)).assert_passed();
    });
}
#[test]
fn the_link_case_generator_and_shrinker_stay_in_support() {
    let cfg = ephyra::Config::default().tests(300);
    ephyra::check_generator(&cfg, case(), in_support).assert_passed();
    ephyra::check_shrinker(&cfg, case(), in_support, case_size).assert_passed();
}
