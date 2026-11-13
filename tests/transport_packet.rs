//! Fixed-width packet numbers, long and short headers, header protection, in-place seal and open and coalesced
//! datagrams.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::unreadable_literal,
    clippy::identity_op,
    clippy::assert_is_empty,
    clippy::int_plus_one,
    clippy::many_single_char_names
)]

use proptest::prelude::*;
use vinc_crypto::{Aead, Provider, Secret, Software};
use vinc_security::{HeaderKey, PacketKey, RecordError};
use vinc_tests::SplitMix64;
use vinc_transport::frame::{Frame, FrameIter};
use vinc_transport::packet::{
    ConnId, Header, LongHeader, LongType, MAX_PN, Opened, PN_LEN_BASE, PN_LEN_WIDE, PacketError, PnLayout, ShortHeader,
    VERSION, WIDE_WINDOW, decode_pn, encode_pn, open, packets, pad_to, pn_len_for, protect_header, sample_at, seal,
    short_dcid, short_header_len, unprotect_header,
};
use vinc_wire::{WireError, Writer};

mod hexutil;
use hexutil::{arr, hex};

vinc_tests::install_counting_allocator!();

const AEADS: [Aead; 2] = [Aead::ChaCha20Poly1305, Aead::Aes128Gcm];

fn secret(tag: u8) -> Secret<32> {
    Secret::new([tag; 32])
}

fn cid(bytes: &[u8]) -> ConnId {
    ConnId::new(bytes).unwrap()
}

struct Side {
    tx: PacketKey<Software>,
    rx: PacketKey<Software>,
    hk: HeaderKey<Software>,
}

/// One endpoint's keys: both ends of the same secret.
fn side(aead: Aead, tag: u8) -> Side {
    let p = Software;
    Side {
        tx: PacketKey::from_secret(&p, aead, &secret(tag)).unwrap(),
        rx: PacketKey::from_secret(&p, aead, &secret(tag)).unwrap(),
        hk: HeaderKey::from_secret(&p, aead, &secret(tag)).unwrap(),
    }
}

/// Build, seal and protect a short packet; returns its length.
fn build_short(
    buf: &mut [u8],
    s: &mut Side,
    dcid: ConnId,
    key_phase: bool,
    pn: u64,
    largest_acked: Option<u64>,
    frames: &[Frame<'_>],
) -> usize {
    let _ = largest_acked;
    let pn_len = PN_LEN_BASE;
    let pnb = encode_pn(pn, pn_len).unwrap();
    let mut w = Writer::new(buf);
    ShortHeader { key_phase, dcid }.write(&mut w, &pnb[..pn_len]).unwrap();
    let header_len = w.written().len();
    for f in frames {
        f.write(&mut w).unwrap();
    }
    let payload_len = w.written().len() - header_len;
    let layout = PnLayout {
        pn_off: 1 + dcid.as_bytes().len(),
        pn_len,
        long: false,
    };
    seal(&mut s.tx, &s.hk, &Software, buf, layout, payload_len, pn).unwrap()
}

// ---- packet numbers ----

#[test]
fn packet_numbers_have_a_fixed_width() {
    // 0x5c02 is the low two bytes of 0xac5c02, 0xe8fe the low two of 0xace8fe; three bytes keep one more.
    let b = encode_pn(0xac5c02, PN_LEN_BASE).unwrap();
    assert_eq!(&b[..2], &[0x5c, 0x02]);
    let b = encode_pn(0xace8fe, PN_LEN_WIDE).unwrap();
    assert_eq!(&b[..3], &[0xac, 0xe8, 0xfe]);
    // Expanding picks the value closest to the next expected one.
    assert_eq!(decode_pn(0x9b32, 2, Some(0xa82f_30ea)), 0xa82f_9b32);
    assert_eq!(encode_pn(0, PN_LEN_BASE).unwrap(), [0; 3]);
    assert_eq!(decode_pn(0, 2, None), 0);
    // Only the two widths exist, and the number must be in the 62-bit space.
    for len in [0usize, 1, 4, 9] {
        assert_eq!(encode_pn(5, len), Err(PacketError::PnLength), "width {len}");
    }
    assert_eq!(encode_pn(MAX_PN + 1, PN_LEN_BASE), Err(PacketError::PacketNumber));
    assert!(encode_pn(MAX_PN, PN_LEN_WIDE).is_ok());
}

#[test]
fn the_width_follows_the_granted_window() {
    assert_eq!(pn_len_for(0), PN_LEN_BASE);
    assert_eq!(pn_len_for(1_310_720), PN_LEN_BASE);
    assert_eq!(pn_len_for(WIDE_WINDOW), PN_LEN_BASE);
    assert_eq!(pn_len_for(WIDE_WINDOW + 1), PN_LEN_WIDE);
    assert_eq!(pn_len_for(u64::MAX), PN_LEN_WIDE);
}

#[test]
fn decoding_wraps_around_the_window_in_both_directions() {
    assert_eq!(decode_pn(0xff, 1, Some(0x100)), 0xff);
    assert_eq!(decode_pn(0x00, 1, Some(0xff)), 0x100);
    assert_eq!(decode_pn(0x01, 0, Some(0)), 1);
    assert_eq!(decode_pn(0x01, 9, Some(0)), 1);
    // Two bytes cover 16,384 packets either side of the next expected number.
    assert_eq!(decode_pn(0x0000, 2, Some(0xffff)), 0x1_0000);
    assert_eq!(decode_pn(0xffff, 2, Some(0x1_0000)), 0xffff);
}

proptest! {
    #[test]
    fn decode_of_encode_within_the_window(
        base in 0u64..(1 << 61),
        delta in 1u64..16_000,
        lag in 0u64..16_000,
    ) {
        let full = base + delta;
        for len in [PN_LEN_BASE, PN_LEN_WIDE] {
            let bytes = encode_pn(full, len).unwrap();
            let truncated = bytes[..len].iter().fold(0u32, |a, b| (a << 8) | u32::from(*b));
            // The receiver's largest is anywhere from `lag` below the packet to the packet before this one.
            let largest = full.saturating_sub(1 + lag.min(delta + 15_000));
            prop_assert_eq!(decode_pn(truncated, len, Some(largest)), full);
        }
    }
}

// ---- long headers ----

#[test]
fn long_header_layout_and_round_trip() {
    let dcid = cid(&[1, 2, 3, 4]);
    let scid = cid(&[9; 20]);
    for (ty, pn_len, first) in [(LongType::Handshake, 0usize, 0xc0u8), (LongType::ZeroRtt, 2, 0xd1)] {
        let h = LongHeader {
            ty,
            dcid,
            scid,
            body_len: 300,
        };
        let mut buf = [0u8; 64];
        let mut w = Writer::new(&mut buf);
        h.write(&mut w, pn_len).unwrap();
        let written = w.written().len();
        assert_eq!(written, h.header_len());
        let mut expect = vec![first, VERSION, 4, 1, 2, 3, 4, 20];
        expect.extend_from_slice(&[9; 20]);
        expect.extend_from_slice(&[0xac, 0x02]); // 300 as a varint
        assert_eq!(&buf[..written], &expect[..], "{ty:?}");
        // The body must be present for the parse to accept it.
        let mut packet = buf[..written].to_vec();
        packet.extend_from_slice(&[0u8; 300]);
        packet.extend_from_slice(&[0xee; 7]); // a following coalesced packet is not part of this one
        assert_eq!(LongHeader::parse(&packet).unwrap(), (h, written));
    }
}

// A body length that no varint holds is refused before a byte of the header is written.
#[cfg(target_pointer_width = "64")]
#[test]
fn long_header_writes_nothing_for_a_body_length_no_varint_holds() {
    let mut buf = [0xeeu8; 64];
    let mut w = Writer::new(&mut buf);
    let h = LongHeader {
        ty: LongType::Handshake,
        dcid: cid(&[7, 7]),
        scid: cid(&[9]),
        body_len: 1usize << 63,
    };
    assert_eq!(h.write(&mut w, 0), Err(PacketError::Wire(WireError::VarintOverflow)));
    assert!(w.written().is_empty());
}

#[test]
fn long_header_rejects_malformed_input() {
    let ok = {
        let mut buf = [0u8; 64];
        let mut w = Writer::new(&mut buf);
        LongHeader {
            ty: LongType::Handshake,
            dcid: cid(&[1, 2]),
            scid: cid(&[3]),
            body_len: 2,
        }
        .write(&mut w, 0)
        .unwrap();
        let mut v = w.written().to_vec();
        v.extend_from_slice(&[0xaa, 0xbb]);
        v
    };
    assert!(LongHeader::parse(&ok).is_ok());
    let mut bad = ok.clone();
    bad[0] = 0x80 | 0x00; // no fixed bit
    assert_eq!(LongHeader::parse(&bad), Err(PacketError::Form));
    let mut bad = ok.clone();
    bad[0] = 0x40; // short form
    assert_eq!(LongHeader::parse(&bad), Err(PacketError::Form));
    let mut bad = ok.clone();
    bad[0] = 0xf0; // type 3
    assert_eq!(LongHeader::parse(&bad), Err(PacketError::LongType));
    let mut bad = ok.clone();
    bad[0] |= 0x01; // a handshake low nibble must be zero
    assert_eq!(LongHeader::parse(&bad), Err(PacketError::Reserved));
    let mut bad = ok.clone();
    bad[1] = 2;
    assert_eq!(LongHeader::parse(&bad), Err(PacketError::Version(2)));
    let mut bad = ok.clone();
    bad[2] = 21; // dcid length above 20
    assert_eq!(LongHeader::parse(&bad), Err(PacketError::ConnIdLength));
    let mut bad = ok.clone();
    let last = bad.len() - 3;
    bad[last] = 3; // body length 3 with only 2 bytes left
    assert_eq!(LongHeader::parse(&bad), Err(PacketError::Length));
    for cut in 0..ok.len() - 2 {
        assert!(LongHeader::parse(&ok[..cut]).is_err(), "cut {cut}");
    }
    // Writing: pn_len must match the type, and the buffer must fit; nothing is written on failure.
    let h = LongHeader {
        ty: LongType::ZeroRtt,
        dcid: cid(&[]),
        scid: cid(&[]),
        body_len: 0,
    };
    let mut buf = [0u8; 64];
    for bad_len in [0usize, 1, 3, 5] {
        assert_eq!(h.write(&mut Writer::new(&mut buf), bad_len), Err(PacketError::PnLength));
    }
    let hs = LongHeader {
        ty: LongType::Handshake,
        ..h
    };
    assert_eq!(hs.write(&mut Writer::new(&mut buf), 1), Err(PacketError::PnLength));
    let mut tiny = [0u8; 3];
    let mut w = Writer::new(&mut tiny);
    assert!(matches!(
        hs.write(&mut w, 0),
        Err(PacketError::Wire(WireError::BufferTooSmall { .. }))
    ));
    assert!(w.written().is_empty());
}

// ---- short headers ----

#[test]
fn short_header_layout() {
    let dcid = cid(&[0xa1, 0xa2, 0xa3, 0xa4]);
    for (phase, pn, first) in [(true, &[0x11u8, 0x22][..], 0x51u8), (false, &[1, 2, 3][..], 0x42)] {
        let mut buf = [0u8; 16];
        let mut w = Writer::new(&mut buf);
        ShortHeader { key_phase: phase, dcid }.write(&mut w, pn).unwrap();
        let n = w.written().len();
        assert_eq!(n, short_header_len(4, pn.len()));
        assert_eq!(buf[0], first);
        assert_eq!(&buf[1..5], dcid.as_bytes());
        assert_eq!(&buf[5..n], pn);
        assert_eq!(short_dcid(&buf[..n], 4).unwrap(), dcid);
    }
    let mut buf = [0u8; 16];
    for bad in [&[][..], &[0u8][..], &[0u8; 4][..], &[0u8; 5][..]] {
        assert_eq!(
            ShortHeader { key_phase: false, dcid }.write(&mut Writer::new(&mut buf), bad),
            Err(PacketError::PnLength)
        );
    }
}

#[test]
fn short_dcid_checks_form_and_length() {
    let pkt = [0x40, 1, 2, 3, 4, 5, 6, 7, 8];
    assert_eq!(short_dcid(&pkt, 4).unwrap().as_bytes(), &[1, 2, 3, 4]);
    assert_eq!(short_dcid(&pkt, 0).unwrap().as_bytes(), &[] as &[u8]);
    assert_eq!(short_dcid(&pkt, 8).unwrap().as_bytes(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(short_dcid(&pkt, 9), Err(PacketError::TooShort));
    assert_eq!(short_dcid(&pkt, 21), Err(PacketError::ConnIdLength));
    assert_eq!(short_dcid(&[], 4), Err(PacketError::TooShort));
    assert_eq!(short_dcid(&[0x00, 1, 2, 3, 4], 4), Err(PacketError::Form)); // no fixed bit
    assert_eq!(short_dcid(&[0xc0, 1, 2, 3, 4], 4), Err(PacketError::Form)); // long
    assert_eq!(short_dcid(&[0x60, 1, 2, 3, 4], 4), Err(PacketError::Form)); // bit 5 set
}

// ---- header protection ----

#[test]
fn header_protection_matches_a_manual_mask() {
    let p = Software;
    for aead in AEADS {
        let s = secret(3);
        let hk = HeaderKey::from_secret(&p, aead, &s).unwrap();
        let mut hp = [0u8; 32];
        vinc_crypto::expand(
            s.expose(),
            vinc_security::labels::HEADER_KEY,
            &[],
            &mut hp[..aead.key_len()],
        );
        let raw = p.hp_key(aead, &hp[..aead.key_len()]).unwrap();
        for long in [false, true] {
            for pn_len in 1..=4usize {
                let pn_off = 7;
                let mut packet = vec![0u8; pn_off + pn_len + 40];
                SplitMix64::new(pn_len as u64).fill(&mut packet);
                packet[0] = (if long { 0xd0 } else { 0x40 }) | (pn_len as u8 - 1);
                let plain = packet.clone();
                let sample: [u8; 16] = plain[pn_off + 4..pn_off + 20].try_into().unwrap();
                assert_eq!(sample_at(&plain, pn_off).unwrap(), sample);
                let mask = p.hp_mask(&raw, &sample);
                protect_header(&hk, &p, &mut packet, PnLayout { pn_off, pn_len, long }).unwrap();
                let bits = if long { 0x0f } else { 0x1f };
                let mut expect = plain.clone();
                expect[0] ^= mask[0] & bits;
                for i in 0..pn_len {
                    expect[pn_off + i] ^= mask[1 + i];
                }
                assert_eq!(packet, expect, "{aead:?} long {long} pn_len {pn_len}");
                // Remove it: the first byte and the number come back, with the length.
                let mut pn_bytes = [0u8; 4];
                pn_bytes[..pn_len].copy_from_slice(&plain[pn_off..pn_off + pn_len]);
                // The random first byte above has reserved bits cleared by construction of `packet[0]`.
                let got = unprotect_header(&hk, &p, &mut packet, pn_off, long).unwrap();
                assert_eq!(packet, plain);
                assert_eq!(got.pn_len, pn_len);
                assert_eq!(got.first, plain[0]);
                let want = pn_bytes[..pn_len].iter().fold(0u32, |a, b| (a << 8) | u32::from(*b));
                assert_eq!(got.truncated, want);
            }
        }
    }
}

#[test]
fn packets_too_short_to_sample_are_rejected() {
    let p = Software;
    let hk = HeaderKey::from_secret(&p, Aead::ChaCha20Poly1305, &secret(1)).unwrap();
    let layout = PnLayout {
        pn_off: 5,
        pn_len: 2,
        long: false,
    };
    // The sample needs pn_off + 4 + 16 = 25 bytes.
    for len in 0..25 {
        let mut pkt = vec![0x41u8; len];
        assert_eq!(sample_at(&pkt, 5), Err(PacketError::TooShort), "len {len}");
        assert_eq!(protect_header(&hk, &p, &mut pkt, layout), Err(PacketError::TooShort));
        assert_eq!(
            unprotect_header(&hk, &p, &mut pkt, 5, false),
            Err(PacketError::TooShort)
        );
    }
    let mut pkt = vec![0x41u8; 25];
    assert!(protect_header(&hk, &p, &mut pkt, layout).is_ok());
    assert_eq!(sample_at(&pkt, usize::MAX), Err(PacketError::TooShort));
    // A short packet whose payload is under 4 bytes minus the number is refused before sealing.
    let mut s = side(Aead::Aes128Gcm, 1);
    let mut buf = [0u8; 64];
    buf[0] = 0x40; // pn_len 1
    let l1 = PnLayout {
        pn_off: 1,
        pn_len: 1,
        long: false,
    };
    assert_eq!(
        seal(&mut s.tx, &s.hk, &p, &mut buf, l1, 2, 0),
        Err(PacketError::TooShort)
    );
    assert_eq!(s.tx.sealed(), 0);
    assert!(seal(&mut s.tx, &s.hk, &p, &mut buf, l1, 3, 0).is_ok());
    // No room for the tag.
    let mut small = [0u8; 20];
    assert!(matches!(
        seal(&mut s.tx, &s.hk, &p, &mut small, l1, 10, 1),
        Err(PacketError::Wire(WireError::BufferTooSmall { .. }))
    ));
}

#[test]
fn chacha20_header_protection_known_answer() {
    // A published ChaCha20-Poly1305 short-header vector: the header key and the AEAD key are given directly, so
    // it checks the mask and the seal against an independent implementation. Its packet number is 3 bytes wide.
    let p = Software;
    let hp: [u8; 32] = arr("25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4");
    let key: [u8; 32] = arr("c6d98ff3441c3fe1b2182094f69caa2ed4b716b65488960a7a984979fb23e1c8");
    let iv: [u8; 12] = arr("e0459b3474bdd0e44a41c144");
    let protected = hex("4cfe4189655e5cd55c41f69080575d7999c25a5bfb");
    let pn_full = 654_360_564u64;
    let hp_key = p.hp_key(Aead::ChaCha20Poly1305, &hp).unwrap();
    let sample = sample_at(&protected, 1).unwrap();
    assert_eq!(sample, arr::<16>("5e5cd55c41f69080575d7999c25a5bfb"));
    let mask = p.hp_mask(&hp_key, &sample);
    assert_eq!(mask, arr::<5>("aefefe7d03"));
    // Unmask by hand, as the packet layer does.
    let mut header = protected[..4].to_vec();
    header[0] ^= mask[0] & 0x1f;
    for i in 0..3 {
        header[1 + i] ^= mask[1 + i];
    }
    assert_eq!(header, hex("4200bff4"));
    assert_eq!(header[0] & 0x03, 2); // pn_len 3
    let truncated = u32::from_be_bytes([0, header[1], header[2], header[3]]);
    assert_eq!(decode_pn(truncated, 3, Some(pn_full - 1)), pn_full);
    assert_eq!(encode_pn(pn_full, PN_LEN_WIDE).unwrap(), [0x00, 0xbf, 0xf4]);
    // The AEAD: nonce = iv xor pn, the unmasked header is the associated data.
    let aead = p.aead_key(Aead::ChaCha20Poly1305, &key).unwrap();
    let mut nonce = iv;
    for (n, b) in nonce[4..].iter_mut().zip(pn_full.to_be_bytes()) {
        *n ^= b;
    }
    let mut body = protected[4..protected.len() - 16].to_vec();
    let tag: [u8; 16] = protected[protected.len() - 16..].try_into().unwrap();
    p.open(&aead, &nonce, &header, &mut body, &tag).unwrap();
    assert_eq!(body, [0x01]);
}

// ---- seal and open ----

#[test]
fn short_packet_seals_and_opens_in_place() {
    let p = Software;
    let dcid = cid(&[0xd0, 0xd1, 0xd2, 0xd3]);
    for aead in AEADS {
        let mut s = side(aead, 7);
        let frames = [
            Frame::Ping,
            Frame::Stream {
                id: 4,
                offset: 99,
                fin: true,
                data: b"hello world, hello",
                implicit_len: true,
            },
        ];
        for (key_phase, pn, acked, largest) in [
            (false, 0u64, None, None),
            (true, 1, Some(0), Some(0)),
            (false, 0x1234_5678, Some(0x1234_5000), Some(0x1234_5670)),
            (true, MAX_PN, Some(MAX_PN - 1000), Some(MAX_PN - 5)),
        ] {
            let mut buf = vec![0u8; 1452];
            let len = build_short(&mut buf, &mut s, dcid, key_phase, pn, acked, &frames);
            let datagram = &mut buf[..len];
            let mut it = packets(datagram, 4);
            let pkt = it.next().unwrap().unwrap();
            assert!(it.next().is_none());
            assert_eq!(pkt.header, Header::Short { dcid });
            let pn_off = pkt.pn_off();
            let bytes = pkt.bytes;
            let un = unprotect_header(&s.hk, &p, bytes, pn_off, false).unwrap();
            assert_eq!(un.key_phase(), key_phase);
            let Opened {
                pn: got,
                payload_start,
                payload_end,
            } = open(&mut s.rx, &p, bytes, pn_off, &un, largest).unwrap();
            assert_eq!(got, pn);
            let got_frames: Vec<_> = FrameIter::new(&bytes[payload_start..payload_end])
                .map(Result::unwrap)
                .collect();
            assert_eq!(got_frames, frames);
        }
    }
}

#[test]
fn every_single_bit_flip_is_rejected() {
    let p = Software;
    let dcid = cid(&[1, 2, 3, 4]);
    for aead in AEADS {
        let mut s = side(aead, 9);
        let mut buf = vec![0u8; 200];
        let frames = [Frame::Ping, Frame::MaxStreamData { id: 4, max: 77 }];
        let len = build_short(&mut buf, &mut s, dcid, true, 5, Some(2), &frames);
        let good = buf[..len].to_vec();
        for bit in 0..len * 8 {
            let mut pkt = good.clone();
            pkt[bit / 8] ^= 1 << (bit % 8);
            let res = unprotect_header(&s.hk, &p, &mut pkt, 5, false)
                .and_then(|un| open(&mut s.rx, &p, &mut pkt, 5, &un, Some(2)));
            assert!(res.is_err(), "{aead:?} bit {bit} was accepted");
        }
        // The untouched packet still opens.
        let mut pkt = good.clone();
        let un = unprotect_header(&s.hk, &p, &mut pkt, 5, false).unwrap();
        assert!(open(&mut s.rx, &p, &mut pkt, 5, &un, Some(2)).is_ok());
        // A packet too short to hold a tag.
        let mut tiny = good[..5 + un.pn_len + 8].to_vec();
        let res = unprotect_header(&s.hk, &p, &mut tiny, 5, false);
        assert_eq!(res, Err(PacketError::TooShort));
    }
}

#[test]
fn open_reports_authentication_and_pn_range() {
    let p = Software;
    let mut s = side(Aead::ChaCha20Poly1305, 2);
    let dcid = cid(&[5, 6, 7, 8]);
    let mut buf = vec![0u8; 100];
    let len = build_short(&mut buf, &mut s, dcid, false, 9, Some(8), &[Frame::Padding { len: 8 }]);
    let mut wrong = side(Aead::ChaCha20Poly1305, 3);
    let mut pkt = buf[..len].to_vec();
    // Another key: the mask differs, so the header decodes to garbage; whichever step refuses it, it is refused.
    let res = unprotect_header(&wrong.hk, &p, &mut pkt, 5, false)
        .and_then(|un| open(&mut wrong.rx, &p, &mut pkt, 5, &un, None));
    assert!(res.is_err());
    // The right header key but another packet key: authentication fails and counts toward the limit.
    let mut pkt = buf[..len].to_vec();
    let un = unprotect_header(&s.hk, &p, &mut pkt, 5, false).unwrap();
    assert_eq!(
        open(&mut wrong.rx, &p, &mut pkt, 5, &un, Some(8)),
        Err(PacketError::Record(RecordError::Authentication))
    );
    // The first attempt with the wrong header key may or may not have reached the authentication step.
    assert!((1..=2).contains(&wrong.rx.failed_opens()));
    // A truncated number that expands past 2^62 is refused.
    let un = vinc_transport::packet::Unprotected {
        first: 0x43,
        pn_len: 4,
        truncated: 0,
    };
    let mut pkt = vec![0u8; 40];
    assert_eq!(
        open(&mut s.rx, &p, &mut pkt, 5, &un, Some(MAX_PN)),
        Err(PacketError::PacketNumber)
    );
}

#[test]
fn zero_rtt_long_packet_seals_and_opens() {
    let p = Software;
    for aead in AEADS {
        let mut s = side(aead, 4);
        let (dcid, scid) = (cid(&[1, 2, 3, 4, 5, 6, 7, 8]), cid(&[8, 7, 6]));
        let pn = 70_000u64;
        let pn_len = PN_LEN_BASE;
        let pnb = encode_pn(pn, pn_len).unwrap();
        let frames = [Frame::Datagram {
            data: b"early data",
            implicit_len: false,
        }];
        let payload_len: usize = frames.iter().map(Frame::encoded_len).sum();
        let header = LongHeader {
            ty: LongType::ZeroRtt,
            dcid,
            scid,
            body_len: pn_len + payload_len + 16,
        };
        let mut buf = vec![0u8; 300];
        let mut w = Writer::new(&mut buf);
        header.write(&mut w, pn_len).unwrap();
        w.put_slice(&pnb[..pn_len]).unwrap();
        frames[0].write(&mut w).unwrap();
        let pn_off = header.header_len();
        let layout = PnLayout {
            pn_off,
            pn_len,
            long: true,
        };
        let total = seal(&mut s.tx, &s.hk, &p, &mut buf, layout, payload_len, pn).unwrap();
        assert_eq!(total, pn_off + header.body_len);
        // A coalesced short packet could follow; the iterator hands out exactly this packet.
        buf.truncate(total);
        buf.extend_from_slice(&[0, 0, 0]);
        let mut it = packets(&mut buf, 4);
        let pkt = it.next().unwrap().unwrap();
        assert!(it.next().is_none(), "trailing zero bytes are padding");
        let Header::Long {
            header: got,
            header_len,
        } = pkt.header
        else {
            panic!("expected a long packet");
        };
        assert_eq!(
            (got.ty, got.dcid, got.scid, header_len),
            (LongType::ZeroRtt, dcid, scid, pn_off)
        );
        let un = unprotect_header(&s.hk, &p, pkt.bytes, pn_off, true).unwrap();
        let opened = open(&mut s.rx, &p, pkt.bytes, pn_off, &un, Some(69_500)).unwrap();
        assert_eq!(opened.pn, pn);
        assert_eq!(
            FrameIter::new(&pkt.bytes[opened.payload_start..opened.payload_end]).next(),
            Some(Ok(frames[0].clone()))
        );
    }
}

// ---- coalesced datagrams ----

#[test]
fn coalesced_datagram_yields_long_packets_then_one_short() {
    let (dcid, scid) = (cid(&[1, 2, 3, 4]), cid(&[9, 9]));
    let mut buf = vec![0u8; 400];
    let mut w = Writer::new(&mut buf);
    let bodies: [&[u8]; 3] = [b"first handshake message", b"retry token", b""];
    let types = [LongType::Handshake, LongType::ZeroRtt, LongType::Handshake];
    for (ty, body) in types.iter().zip(bodies) {
        LongHeader {
            ty: *ty,
            dcid,
            scid,
            body_len: body.len(),
        }
        .write(&mut w, if *ty == LongType::ZeroRtt { PN_LEN_BASE } else { 0 })
        .unwrap();
        w.put_slice(body).unwrap();
    }
    ShortHeader { key_phase: false, dcid }.write(&mut w, &[7, 8]).unwrap();
    w.put_slice(&[0xaa; 40]).unwrap();
    let total = w.written().len();
    let mut dg = buf[..total].to_vec();
    let mut got = Vec::new();
    for item in packets(&mut dg, 4) {
        let pkt = item.unwrap();
        got.push((pkt.header, pkt.bytes.len()));
    }
    assert_eq!(got.len(), 4);
    for (i, (h, len)) in got[..3].iter().enumerate() {
        let Header::Long { header, header_len } = h else {
            panic!("packet {i} should be long");
        };
        assert_eq!((header.ty, header.body_len), (types[i], bodies[i].len()));
        assert_eq!(*len, header_len + bodies[i].len());
    }
    assert_eq!(got[3], (Header::Short { dcid }, 1 + 4 + 2 + 40));
    // Packets are disjoint, in order, and cover the datagram.
    assert_eq!(got.iter().map(|(_, l)| l).sum::<usize>(), total);
}

#[test]
fn padding_after_long_packets_is_skipped_and_garbage_is_not() {
    let (dcid, scid) = (cid(&[1]), cid(&[2]));
    let mut buf = vec![0u8; 1200];
    let mut w = Writer::new(&mut buf);
    LongHeader {
        ty: LongType::Handshake,
        dcid,
        scid,
        body_len: 3,
    }
    .write(&mut w, 0)
    .unwrap();
    w.put_slice(b"abc").unwrap();
    let used = w.written().len();
    pad_to(&mut w, 1200).unwrap();
    assert_eq!(w.written().len(), 1200);
    assert_eq!(pad_to(&mut w, 100), Ok(())); // already long enough
    assert!(matches!(
        pad_to(&mut w, 1201),
        Err(PacketError::Wire(WireError::BufferTooSmall { needed: 1 }))
    ));
    assert_eq!(w.written().len(), 1200, "a failed pad writes nothing");
    let mut dg = buf.clone();
    let items: Vec<_> = packets(&mut dg, 4).collect();
    assert_eq!(items.len(), 1);
    assert!(items[0].is_ok());
    assert!(buf[used..].iter().all(|b| *b == 0));
    // A non-zero byte after the padding is an error, and then the iterator stops.
    let mut dg = buf.clone();
    dg[1199] = 1;
    let mut it = packets(&mut dg, 4);
    assert!(it.next().unwrap().is_ok());
    assert_eq!(it.next(), Some(Err(PacketError::Form)));
    assert!(it.next().is_none());
}

#[test]
fn iterator_stops_at_the_first_error() {
    let mut buf = vec![0u8; 64];
    let mut w = Writer::new(&mut buf);
    LongHeader {
        ty: LongType::Handshake,
        dcid: cid(&[1]),
        scid: cid(&[2]),
        body_len: 1,
    }
    .write(&mut w, 0)
    .unwrap();
    w.put_u8(0xee).unwrap();
    let n = w.written().len();
    // A second long packet whose length runs past the datagram.
    w.put_slice(&[0xc0, VERSION, 0, 0, 50, 1, 2]).unwrap();
    let total = w.written().len();
    let mut dg = buf[..total].to_vec();
    let mut it = packets(&mut dg, 4);
    assert_eq!(it.next().unwrap().unwrap().bytes.len(), n);
    assert_eq!(it.next(), Some(Err(PacketError::Length)));
    assert!(it.next().is_none());
    // A short packet whose dcid does not fit.
    let mut dg = vec![0x40, 1, 2];
    assert_eq!(packets(&mut dg, 4).next(), Some(Err(PacketError::TooShort)));
    assert!(packets(&mut [], 4).next().is_none());
}

// ---- robustness ----

proptest! {
    #[test]
    fn arbitrary_bytes_never_panic_and_always_progress(
        bytes in proptest::collection::vec(any::<u8>(), 0..400),
        dcid_len in 0usize..24,
        long_prefix in any::<bool>(),
        seed in any::<u64>(),
    ) {
        let mut dg = bytes;
        if long_prefix && dg.len() >= 8 {
            dg[0] = 0xc0 | (dg[0] & 0x30 & 0x20);
            dg[1] = VERSION;
            dg[2] %= 21;
            dg[3] %= 21;
        }
        let total = dg.len();
        let _ = LongHeader::parse(&dg);
        let _ = short_dcid(&dg, dcid_len);
        let mut count = 0usize;
        let mut consumed = 0usize;
        let mut ended_on_error = false;
        for item in packets(&mut dg.clone(), dcid_len) {
            prop_assert!(!ended_on_error, "an item followed an error");
            count += 1;
            match item {
                Ok(pkt) => {
                    prop_assert!(!pkt.bytes.is_empty());
                    consumed += pkt.bytes.len();
                }
                Err(_) => ended_on_error = true,
            }
            prop_assert!(count <= total + 1);
        }
        prop_assert!(consumed <= total);
        // Header protection and open on garbage report errors rather than panic.
        let p = Software;
        let mut s = side(Aead::Aes128Gcm, (seed & 0xff) as u8);
        let pn_off = (seed >> 8) as usize % 30;
        let mut copy = dg.clone();
        if let Ok(un) = unprotect_header(&s.hk, &p, &mut copy, pn_off, seed & 1 == 0) {
            let _ = open(&mut s.rx, &p, &mut copy, pn_off, &un, Some(seed >> 20));
        }
    }
}

// ---- allocation ----

#[test]
fn packet_paths_allocate_nothing() {
    let p = Software;
    let dcid = cid(&[1, 2, 3, 4]);
    let mut s = side(Aead::ChaCha20Poly1305, 6);
    let mut buf = vec![0u8; 1452];
    let mut dg = vec![0u8; 1452];
    let mut out = [0u8; 80];
    let frames = [
        Frame::Ping,
        Frame::Stream {
            id: 0,
            offset: 5,
            fin: false,
            data: &[7u8; 1000],
            implicit_len: false,
        },
    ];
    let stats = vinc_tests::measure(|| {
        let len = build_short(&mut buf, &mut s, dcid, false, 3, Some(1), &frames);
        dg[..len].copy_from_slice(&buf[..len]);
        for item in packets(&mut dg[..len], 4) {
            let pkt = item.unwrap();
            let pn_off = pkt.pn_off();
            let un = unprotect_header(&s.hk, &p, pkt.bytes, pn_off, false).unwrap();
            let o = open(&mut s.rx, &p, pkt.bytes, pn_off, &un, Some(2)).unwrap();
            assert_eq!(FrameIter::new(&pkt.bytes[o.payload_start..o.payload_end]).count(), 2);
        }
        let mut w = Writer::new(&mut out);
        LongHeader {
            ty: LongType::Handshake,
            dcid,
            scid: dcid,
            body_len: 0,
        }
        .write(&mut w, 0)
        .unwrap();
        let n = w.written().len();
        LongHeader::parse(&out[..n]).unwrap();
        let mut w = Writer::new(&mut out);
        pad_to(&mut w, 50).unwrap();
        let b = encode_pn(1000, PN_LEN_BASE).unwrap();
        let t = b[..PN_LEN_BASE].iter().fold(0u32, |a, x| (a << 8) | u32::from(*x));
        assert_eq!(decode_pn(t, PN_LEN_BASE, Some(999)), 1000);
    });
    assert_eq!(stats.count(), 0, "{stats:?}");
}
