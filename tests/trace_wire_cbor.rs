//! Trace generation for the TLA+ specification of the DAG-CBOR codec (`WireCbor.tla`): the `Decoder`, the `MapReader`,
//! the `Encoder` and `MapKeys` of `pinc-wire`, recorded as ndjson (`tla/wire_cbor.ndjson`) for the trace check
//! (`TraceWireCbor.tla`, `MaxDepth = 64`).
//!
//! The decoder runs on every first byte followed by 37 tails, on every token sequence of the skip family (grown while
//! `skip_value` answers `Truncated`), on nesting around the real bound (a tag takes a frame, so it counts toward
//! `MAX_DEPTH` as the code stands), on non-maps given to the `MapReader`, and on 400 seeded random trees with three
//! mutations each. The encoder runs each boundary call at five buffer sizes, 1364 ordered-map runs and 300 seeded
//! random runs. A `u64` is written as four 16-bit limbs, least significant first, which `U64.tla` reads. Every result
//! is also checked here (decode then encode is the identity, encode then decode returns the item, a refusal writes
//! nothing), so the test is meaningful without the proof tools. The file goes to `tla/` under `PINC_TRACE_DIR` when
//! it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::needless_range_loop,
    clippy::too_many_lines,
    clippy::panic,
    clippy::explicit_auto_deref,
    clippy::ignored_unit_patterns,
    unreachable_pub
)]

#[path = "trace_wire_cbor/common.rs"]
mod common;

use common::{
    Seen, decoder_boundary, decoder_depth, decoder_non_maps, decoder_trees, encoder_boundary, encoder_random,
    omap_runs, visit,
};

#[test]
fn wire_cbor_traces_are_consistent_with_the_code() {
    let (mut out, mut seen) = (String::new(), Seen::default());
    assert_eq!(decoder_boundary(&mut out, &mut seen), 9472);
    visit(&mut Vec::new(), &[], 0, &mut out, &mut seen);
    decoder_depth(&mut out, &mut seen);
    decoder_non_maps(&mut out, &mut seen);
    assert_eq!(decoder_trees(&mut out, &mut seen), 3200);
    encoder_boundary(&mut out, &mut seen);
    assert_eq!(omap_runs(&mut out, &mut seen), 1364);
    encoder_random(&mut out, &mut seen);
    if !pinc_tests::soaking() {
        for why in [
            "reserved additional information",
            "indefinite lengths are not allowed",
            "argument is not minimally encoded",
            "text is not valid UTF-8",
            "only tag 42 is allowed",
            "tag 42 content must be a byte string starting with 0x00",
            "floats must be 64-bit",
            "NaN and infinity are not allowed",
            "reserved or indefinite form",
            "undefined and other simple values are not allowed",
            "map keys must be text strings",
            "map keys out of order",
            "duplicate map key",
            "depth",
            "expected a map",
            "truncated",
        ] {
            assert!(seen.dec.contains(why), "the decoder never answered {why:?}");
        }
        for why in [
            "small",
            "more keys than the declared map length",
            "duplicate map key",
            "map keys out of order",
        ] {
            assert!(seen.enc.contains(why), "the encoder never answered {why:?}");
        }
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = std::path::Path::new(&dir).join("tla");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("wire_cbor.ndjson"), &out).unwrap();
    }
}
