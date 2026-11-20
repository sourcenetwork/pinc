//! Trace generation for the handshake message codec (`message.rs` of `pinc-security`): the real parsers and writers of
//! every message, driven through the public API and recorded as ndjson (`message.ndjson`) for the TLA+ trace check
//! (`TraceMessageCodec`).
//!
//! * `type`: `MessageType::of` of the empty buffer, of every single byte and of the garbage strings.
//! * `write`: the `write` of a message into a buffer of a given capacity, with the bytes it wrote, or `BufferTooSmall`
//!   (`small`) or `VarintOverflow` (`overflow`).
//! * `parse`: the parser of one kind on a byte string, with the message it gives back or the error (`truncated`,
//!   `unexpected` with its reason).
//!
//! The messages are those of `MessageCodec.tla` (190 of the two Initial forms, both rejects, the Reply, the Finish, the
//! resume Hello and Reply and the identity plaintext, at the real sizes) and 70 seeded random ones. For each: the writes
//! at its size, one byte short and at 0; its own parser on its bytes, on every cut at the start, the end and around
//! every field boundary, with a trailing byte, with a byte changed, and (for the small ones) every other parser on it.
//! Then 300 garbage strings through every parser and the fields out of range. Every result is also asserted here
//! against the documented rule: the round trip, the size, every proper prefix `Truncated`, every trailing byte refused,
//! a changed byte that still parses re-encoding to itself, and every cross parse the wrong type.
//!
//! The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written, the
//! assertions still run.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::cast_possible_wrap,
    clippy::manual_is_multiple_of,
    clippy::panic,
    unreachable_pub
)]

#[path = "trace_message/common.rs"]
mod common;

use common::{
    Expect, Kind, deterministic, exercise, out_of_range, parse_ev, random_bytes, random_messages, type_ev, write_ev,
};
use pinc_tests::SplitMix64;
use pinc_wire::WireError;

#[test]
fn message_traces() {
    let mut out = String::new();

    let mut messages = deterministic();
    messages.extend(random_messages(&mut SplitMix64::traced(4)));
    for m in &messages {
        exercise(&mut out, m);
    }

    // the type of every first byte
    assert_eq!(type_ev(&mut out, &[]).unwrap_err(), WireError::Truncated { needed: 1 });
    for v in 0..=255u8 {
        let r = type_ev(&mut out, &[v]);
        assert_eq!(r.is_ok(), (1..=8).contains(&v));
        if let Ok(t) = r {
            assert_eq!(t as u8, v);
        }
    }

    // garbage through every parser
    let mut rng = SplitMix64::traced(5);
    for _ in 0..300 {
        let n = (rng.next_u64() % 65) as usize;
        let mut g = random_bytes(&mut rng, n);
        if let Some(first) = g.first_mut() {
            *first = (rng.next_u64() % 10) as u8;
        }
        let _ = type_ev(&mut out, &g);
        for k in [
            Kind::Initial,
            Kind::Reject(3),
            Kind::Reject(8),
            Kind::Reply,
            Kind::Finish,
            Kind::Hello,
            Kind::RReply,
            Kind::IdSig(false),
            Kind::IdSig(true),
        ] {
            let _ = parse_ev(&mut out, k, &g);
        }
    }

    // fields out of range: Initial::write and ResumeHello::write do not refuse an ALPN of 0 or 33 to 255 bytes (today's
    // behaviour, recorded as it is); the parser refuses what they write
    for (m, expect) in out_of_range() {
        let r = write_ev(&mut out, &m, 70000);
        match expect {
            Expect::Overflow => assert_eq!(r.unwrap_err(), WireError::VarintOverflow),
            Expect::Refused(what) => {
                let written = r.unwrap();
                assert_eq!(
                    parse_ev(&mut out, m.kind(), &written).err(),
                    Some(WireError::Unexpected(what))
                );
            }
        }
    }

    for reason in [
        "unknown message type",
        "wrong message type",
        "connection id too long",
        "alpn length",
        "aead offer",
        "unknown aead",
        "sealed length",
        "ticket count",
        "unknown identity algorithm",
        "public key length",
        "signature length",
        "trailing bytes",
    ] {
        assert!(
            pinc_tests::soaking() || out.contains(&format!(r#""what":"{reason}""#)),
            "the runs never produce {reason}"
        );
    }
    for form in ["ok", "truncated", "unexpected", "small", "overflow"] {
        assert!(
            out.contains(&format!(r#""res":"{form}""#)),
            "the runs never produce a {form} result"
        );
    }
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("message.ndjson"), out).unwrap();
}
