//! Trace generation for the packet header codecs: seeded calls of the real `LongHeader::write` and `parse`,
//! `ShortHeader::write`, `short_dcid`, `unprotect_header`, `packets`, `seal` and `open` (`pinc-transport`), recorded
//! as ndjson (`hdr.ndjson`) for the TLA+ trace check (`TraceHdr.tla`) and the Lean replay (`Pinc/TraceHdr.lean`).
//!
//! A long header is written with every packet-number length, into buffers around its size, with body lengths at the
//! varint boundaries; what was written is parsed back whole, cut at every length, with its body one byte short and
//! with a byte changed (the version, an id length, the first byte, any byte) or a length that is no varint. A short header is written and read
//! back the same way. Datagrams are long packets back to back, then a short packet, padding, a byte that is no
//! packet or nothing, cut or damaged at random; the event holds every item the iterator yields with the offset of
//! the bytes it lends, taken from the slice's address. Packets are sealed and opened through a provider that
//! records the associated data the AEAD is given, so the event holds the bytes the real code authenticated.
//!
//! The body of a Handshake packet is traced from both sides: real clients (two identity algorithms, windows of 64 to
//! 2000 bytes, the first flight and its resends) build datagrams (`hw`) that real servers hand to
//! `Handshake::on_fragment` (`hf`, through the `trace`-feature accessor `Connection::trace_fragment`, with the
//! reassembly before and after); seeded bodies cut from messages of every length in every order, with refused ones
//! between, go the same way. `pad_to` (`pad`) and `sample_at` (`smp`, and `smpp` around `unprotect_header`) are
//! called on writers and packets around their boundaries.
//!
//! A second file (`hdr_wide.ndjson`, read by the Lean replay only: the TLA+ checker has 32-bit integers) takes body
//! lengths up to `usize::MAX`, where a length of `2^63` or more must be refused with nothing written.
//!
//! The runs are in three files under `trace_hdr/`: `headers.rs` (the codecs, datagrams and sealed packets, with the
//! generators they share), `body.rs` (the Handshake body) and `helpers.rs` (`pad_to` and `sample_at`); this file draws
//! them in one order from one generator and writes the two ndjson files.
//!
//! The test asserts the round trips, that a refused write wrote nothing and that the ranges of a datagram are back
//! to back, so it is meaningful without the proof tools.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::too_many_arguments,
    clippy::redundant_closure_for_method_calls,
    unreachable_pub
)]

#[path = "trace_hdr/body.rs"]
mod body;
#[path = "trace_hdr/headers.rs"]
mod headers;
#[path = "trace_hdr/helpers.rs"]
mod helpers;

use body::hs_run;
use headers::{datagram_run, long_run, sealed_run, short_run};
use helpers::{pad_run, sample_run};
use pinc_tests::{SplitMix64, big_stack};

#[test]
fn header_calls_match_the_models() {
    let mut rng = SplitMix64::new(0x4844_0001);
    let mut out = String::new();
    long_run(&mut rng, &mut out, false, 500);
    short_run(&mut rng, &mut out, 250);
    datagram_run(&mut rng, &mut out, 1600);
    sealed_run(&mut rng, &mut out, 250);
    pad_run(&mut rng, &mut out, 1500);
    sample_run(&mut rng, &mut out, false, 1500);
    out.push_str(&big_stack(|| hs_run(0x4844_0002, 40)));
    let mut wide = String::new();
    long_run(&mut rng, &mut wide, true, 400);
    sample_run(&mut rng, &mut wide, true, 200);
    for needle in [
        r#""op":"lw""#,
        r#""op":"lp""#,
        r#""op":"sw""#,
        r#""op":"sd""#,
        r#""op":"dg""#,
        r#""op":"un""#,
        r#""op":"seal""#,
        r#""op":"open""#,
        r#""op":"hw""#,
        r#""op":"hf""#,
        r#""op":"pad""#,
        r#""op":"smp""#,
        r#""op":"smpp""#,
        r#""k":"short""#,
        r#""err":"Truncated""#,
        r#""err":"BufferTooSmall""#,
        r#""err":"VarintTooLong""#,
        r#""err":"VarintNonMinimal""#,
        r#""err":"Form""#,
        r#""err":"LongType""#,
        r#""err":"Version""#,
        r#""err":"ConnIdLength""#,
        r#""err":"Reserved""#,
        r#""err":"PnLength""#,
        r#""err":"TooShort""#,
        r#""err":"Length""#,
        r#""err":"Record""#,
    ] {
        assert!(out.contains(needle), "the calls never reach {needle}");
    }
    let hf = |f: fn(&str) -> bool| out.lines().filter(|l| l.contains(r#""op":"hf""#)).any(f);
    assert!(hf(|l| !l.contains(r#""ret":-1"#)), "no message was ever completed");
    assert!(hf(|l| l.contains(r#""body":[]"#)), "no empty body");
    assert!(
        out.lines()
            .any(|l| l.contains(r#""op":"pad""#) && l.contains(r#""err":"BufferTooSmall""#)),
        "no padding was refused"
    );
    assert!(
        wide.contains(r#""err":"VarintOverflow""#),
        "the wide calls never reach VarintOverflow"
    );
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("hdr.ndjson"), &out).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("hdr_wide.ndjson"), &wide).unwrap();
    }
}
