//! The value wire: strict, canonical, zero-copy; the proof frames ride as transport extension frames.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::assert_is_empty,
    clippy::doc_markdown,
    clippy::similar_names,
    clippy::single_range_in_vec_init,
    clippy::unreadable_literal,
    reason = "tests assert freely and name protocol rules in capitals"
)]

use proptest::prelude::*;
use pinc_transport::frame::{Frame, ext};
use pinc_values::knobs::{MAX_REQ_RANGES, WT_PMAX};
use pinc_values::span::Span;
use pinc_values::wire::{GROUP_HDR, GroupHeader, PROOF_BODY_MAX, ProofFrame, ProofReq, REQ_FIXED, REQ_MAX, Req};
use pinc_wire::{Reader, WireError, Writer};

fn truncated<T>(r: &Result<T, WireError>) -> bool {
    matches!(r, Err(WireError::Truncated { .. }))
}

fn spans() -> impl Strategy<Value = Vec<Span>> {
    proptest::collection::vec(
        (any::<u64>(), any::<u64>()).prop_map(|(off, len)| Span { off, len }),
        0..=MAX_REQ_RANGES,
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn a_request_round_trips_and_every_prefix_is_truncated(root in any::<[u8; 32]>(), ranges in spans()) {
        let mut buf = [0u8; REQ_MAX];
        let n = Req::encode(&root, &ranges, &mut buf).unwrap();
        prop_assert_eq!(n, REQ_FIXED + 16 * ranges.len());
        let (req, used) = Req::parse(&buf[..n]).unwrap();
        prop_assert_eq!(used, n);
        prop_assert_eq!(req.root(), &root);
        prop_assert_eq!(req.count(), ranges.len());
        prop_assert_eq!(req.ranges().collect::<Vec<_>>(), ranges);
        prop_assert_eq!(Req::total_len(&buf[..REQ_FIXED]).unwrap(), n);
        // Trailing bytes are left for the caller; a short buffer is truncated, never a partial success.
        let mut longer = buf[..n].to_vec();
        longer.push(7);
        prop_assert_eq!(Req::parse(&longer).unwrap().1, n);
        for cut in 0..n {
            prop_assert!(truncated(&Req::parse(&buf[..cut])), "prefix {} parsed", cut);
        }
    }

    #[test]
    fn arbitrary_request_bytes_never_panic_and_a_success_is_canonical(bytes in proptest::collection::vec(any::<u8>(), 0..700)) {
        if let Ok((req, used)) = Req::parse(&bytes) {
            let ranges: Vec<_> = req.ranges().collect();
            let mut out = [0u8; REQ_MAX];
            let n = Req::encode(req.root(), &ranges, &mut out).unwrap();
            prop_assert_eq!(&out[..n], &bytes[..used]);
        }
        let _ = Req::total_len(&bytes);
    }

    #[test]
    fn a_group_header_round_trips_and_is_canonical(off in any::<u64>(), len in 1u32.., pairs in 0u16..1000, follows in any::<bool>()) {
        let h = GroupHeader { off, len, plen: pairs * 64, follows };
        let bytes = h.encode();
        prop_assert_eq!(GroupHeader::parse(&bytes).unwrap(), h);
        for cut in 0..GROUP_HDR {
            let short = GroupHeader::parse(&bytes[..cut]);
            prop_assert!(truncated(&short));
        }
    }

    #[test]
    fn arbitrary_group_header_bytes_never_panic_and_a_success_is_canonical(bytes in any::<[u8; 16]>()) {
        if let Ok(h) = GroupHeader::parse(&bytes) {
            prop_assert_eq!(h.encode(), bytes);
        }
    }

    #[test]
    fn a_proof_frame_round_trips_and_rides_as_an_extension(sid in 0u64..(1 << 62), glog in any::<u8>(), start in any::<u64>(), wn in any::<u32>(), ln in any::<u64>(), pairs in 0usize..=(WT_PMAX / 64), seed in any::<u8>()) {
        let proof: Vec<u8> = (0..pairs * 64).map(|i| (i as u8).wrapping_add(seed)).collect();
        let mut body = [0u8; PROOF_BODY_MAX];
        let head = ProofFrame::write_head(sid, glog, start, wn, ln, &mut body).unwrap();
        body[head..head + proof.len()].copy_from_slice(&proof);
        let body = &body[..head + proof.len()];
        let pf = ProofFrame::parse(body).unwrap();
        prop_assert_eq!((pf.sid, pf.glog, pf.start, pf.wn, pf.ln, pf.proof), (sid, glog, start, wn, ln, proof.as_slice()));
        // As a transport frame: an extension type, passed through unparsed with its length.
        let mut payload = [0u8; 1500];
        let mut w = Writer::new(&mut payload);
        Frame::Extension { ty: ext::PROOF, body }.write(&mut w).unwrap();
        let n = w.written().len();
        let mut r = Reader::new(&payload[..n]);
        match Frame::decode(&mut r).unwrap() {
            Frame::Extension { ty, body: got } => { prop_assert_eq!(ty, ext::PROOF); prop_assert_eq!(got, body); }
            other => prop_assert!(false, "decoded as {:?}", other),
        }
        prop_assert!(r.is_empty());
    }

    #[test]
    fn arbitrary_proof_frame_bytes_never_panic(bytes in proptest::collection::vec(any::<u8>(), 0..1300)) {
        if let Ok(pf) = ProofFrame::parse(&bytes) {
            prop_assert_eq!(pf.proof.len() % 64, 0);
            prop_assert!(pf.proof.len() <= WT_PMAX);
        }
    }

    #[test]
    fn a_proof_request_round_trips_and_is_exact(sid in 0u64..(1 << 62), from in any::<u64>(), upto in any::<u64>()) {
        let rq = ProofReq { sid, from, upto };
        let mut buf = [0u8; 32];
        let n = rq.encode(&mut buf).unwrap();
        prop_assert_eq!(ProofReq::parse(&buf[..n]).unwrap(), rq);
        for cut in 0..n {
            prop_assert!(ProofReq::parse(&buf[..cut]).is_err());
        }
        buf[n] = 0;
        prop_assert!(ProofReq::parse(&buf[..=n]).is_err(), "trailing byte accepted");
        let mut payload = [0u8; 64];
        let mut w = Writer::new(&mut payload);
        Frame::Extension { ty: ext::PROOF_REQ, body: &buf[..n] }.write(&mut w).unwrap();
        prop_assert!(w.written().len() > n);
    }

    #[test]
    fn arbitrary_proof_request_bytes_never_panic(bytes in proptest::collection::vec(any::<u8>(), 0..40)) {
        let _ = ProofReq::parse(&bytes);
    }
}

#[test]
fn strictness_cases() {
    // A request: wrong type, the largest count, too many ranges to encode.
    let mut buf = [0u8; REQ_MAX + 16];
    Req::encode(&[1; 32], &[], &mut buf).unwrap();
    buf[0] = 2;
    assert!(Req::parse(&buf).is_err());
    buf[0] = 1;
    buf[33] = MAX_REQ_RANGES as u8;
    assert_eq!(Req::parse(&buf).map(|(_, n)| n), Ok(REQ_MAX));
    assert_eq!(Req::total_len(&buf[..REQ_FIXED]), Ok(REQ_MAX));
    assert!(Req::encode(&[1; 32], &vec![Span::default(); MAX_REQ_RANGES + 1], &mut buf).is_err());
    let mut small = [0u8; 40];
    assert!(Req::encode(&[1; 32], &[Span::default(); 4], &mut small).is_err());
    assert_eq!(small, [0u8; 40], "a failed encode writes nothing");
    // A group header: follows 2, proof not whole pairs, empty group, wrong type.
    let good = GroupHeader {
        off: 5,
        len: 9,
        plen: 128,
        follows: true,
    }
    .encode();
    for (i, v) in [(0usize, 3u8), (15, 2), (14, 1), (12, 1)] {
        let mut b = good;
        b[i] = v;
        if i == 12 {
            b[9..13].copy_from_slice(&0u32.to_be_bytes());
        }
        assert!(GroupHeader::parse(&b).is_err(), "byte {i} = {v}");
    }
    // A proof frame: a proof that is not whole pairs, and one over the largest size.
    let mut body = vec![0u8; 40];
    assert!(ProofFrame::parse(&body[..1]).is_err());
    body.extend(std::iter::repeat_n(0, 63));
    body[0] = 5;
    assert!(ProofFrame::parse(&body).is_err());
    let big = vec![0u8; 22 + WT_PMAX + 64];
    assert!(ProofFrame::parse(&big).is_err());
    // A non-minimal stream id varint is refused.
    let mut v = vec![0x80, 0x00];
    v.extend_from_slice(&[0u8; 16]);
    assert!(ProofReq::parse(&v).is_err());
}

#[test]
fn a_failed_frame_head_encode_writes_nothing() {
    // The sid varint fits a 3-byte buffer but the rest does not: the old encoders left the varint behind.
    let rq = ProofReq {
        sid: 300,
        from: 1,
        upto: 2,
    };
    let need = rq.encode(&mut [0u8; 32]).unwrap();
    for cap in 0..need {
        let mut buf = vec![0xaa; cap];
        assert_eq!(
            rq.encode(&mut buf),
            Err(WireError::BufferTooSmall { needed: need - cap })
        );
        assert!(buf.iter().all(|&b| b == 0xaa), "PROOF_REQ cap {cap}");
    }
    let need = ProofFrame::write_head(300, 4, 1, 2, 3, &mut [0u8; 32]).unwrap();
    for cap in 0..need {
        let mut buf = vec![0xaa; cap];
        assert_eq!(
            ProofFrame::write_head(300, 4, 1, 2, 3, &mut buf),
            Err(WireError::BufferTooSmall { needed: need - cap })
        );
        assert!(buf.iter().all(|&b| b == 0xaa), "PROOF cap {cap}");
    }
    // An id that does not fit a varint is refused before the room is looked at.
    assert_eq!(
        ProofReq {
            sid: 1 << 63,
            from: 0,
            upto: 0
        }
        .encode(&mut [0u8; 2]),
        Err(WireError::VarintOverflow)
    );
}
