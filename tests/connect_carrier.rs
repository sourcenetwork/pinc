//! The protected carrier (handshake to the relay's identity, record protection, reassembly, tampering) and the
//! WebSocket framing that can carry it.
#![allow(
    clippy::many_single_char_names,
    clippy::assert_is_empty,
    clippy::decimal_bitwise_operands,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::cast_lossless,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements
)]

mod connect_common;

use connect_common::{Out, Rig, big_stack, enc, id, nid};
use proptest::prelude::*;
use pinc_connect::carrier::session::{CarrierError, IN_LEN, MAX_UNIT_LEN, PEER_ALPN};
use pinc_connect::carrier::ws::{self, Decoder, MAX_PAYLOAD, Opcode, Role, WsError, WsFrame};
use pinc_connect::carrier::{BatchBuilder, Frame, MAX_FRAME_LEN, Offer};

fn pkt(n: usize, fill: u8) -> Vec<u8> {
    vec![fill; n]
}

#[test]
fn the_handshake_authenticates_both_ends_and_frames_flow_both_ways() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        assert!(!rig.client.is_open() && !rig.relay.is_open());
        let (relay_seen, client_seen) = rig.handshake();
        assert_eq!(relay_seen, id(&rig.relay_kp));
        assert_eq!(client_seen, id(&rig.client_kp));
        assert_eq!(rig.client.peer(), Some(relay_seen));
        assert_eq!(rig.relay.peer(), Some(client_seen));
        assert!(rig.client.is_open() && rig.relay.is_open());

        let p = pkt(500, 0x42);
        let f = Frame::Send {
            dst: nid(3),
            flag: 1,
            packet: &p,
        };
        let unit = rig.seal_client(&f);
        rig.feed_relay(&unit);
        assert_eq!(rig.poll_relay().unwrap(), Out::Frame(enc(&f)));
        assert_eq!(rig.poll_relay().unwrap(), Out::Idle);

        let r = Frame::Recv {
            src: nid(4),
            flag: 2,
            packet: &p,
        };
        let unit = rig.seal_relay(&r);
        assert_eq!(unit.len(), 2 + enc(&r).len() + 16, "length prefix, frame, tag");
        rig.feed_client(&unit);
        assert_eq!(rig.poll_client().unwrap(), Out::Frame(enc(&r)));
    });
}

#[test]
fn the_responder_tells_a_peer_relay_from_a_client_by_the_protocol_name() {
    big_stack(|| {
        let mut client = Rig::new(None);
        client.handshake();
        assert!(!client.relay.is_peer_relay(), "a client dials the carrier protocol");
        let mut peer = Rig::with_alpn(None, PEER_ALPN);
        peer.handshake();
        assert!(peer.relay.is_peer_relay(), "a relay dials the peer protocol");
        assert!(peer.client.peer().is_some());
    });
}

#[test]
fn the_wire_form_of_a_unit_is_a_length_a_ciphertext_and_a_tag() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        rig.handshake();
        let unit = rig.seal_client(&Frame::Ping);
        assert_eq!(usize::from(u16::from_be_bytes([unit[0], unit[1]])), unit.len() - 2);
        assert_eq!(unit.len(), 2 + 1 + 16);
        // the same frame sealed twice differs: the packet number is in the nonce
        let again = rig.seal_client(&Frame::Ping);
        assert_ne!(unit, again);
    });
}

#[test]
fn bytes_may_arrive_one_at_a_time() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        // handshake with one byte per step in each direction
        let (mut c_open, mut r_open) = (false, false);
        for _ in 0..200_000 {
            let mut b = [0u8; 1];
            if rig.client.transmit(&mut b) == 1 {
                rig.feed_relay(&b);
            }
            while let Out::Open(_) | Out::Handshake = rig.poll_relay().unwrap() {
                r_open |= rig.relay.is_open();
            }
            if rig.relay.transmit(&mut b) == 1 {
                rig.feed_client(&b);
            }
            while let Out::Open(_) | Out::Handshake = rig.poll_client().unwrap() {
                c_open |= rig.client.is_open();
            }
            if c_open && r_open {
                break;
            }
        }
        assert!(c_open && r_open);
        let p = pkt(1000, 7);
        let f = Frame::Send {
            dst: nid(1),
            flag: 0,
            packet: &p,
        };
        let unit = rig.seal_client(&f);
        for (i, b) in unit.iter().enumerate() {
            assert_eq!(
                rig.poll_relay().unwrap(),
                Out::Idle,
                "no frame before the last byte (at {i})"
            );
            rig.feed_relay(&[*b]);
        }
        assert_eq!(rig.poll_relay().unwrap(), Out::Frame(enc(&f)));
    });
}

#[test]
fn several_units_in_one_read_are_delivered_in_order() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        rig.handshake();
        let mut wire = Vec::new();
        let mut want = Vec::new();
        for i in 0..20u8 {
            let p = pkt(10 + usize::from(i), i);
            let f = Frame::SelfSend { packet: &p };
            want.push(enc(&f));
            wire.extend(rig.seal_client(&f));
        }
        rig.feed_relay(&wire);
        for w in want {
            assert_eq!(rig.poll_relay().unwrap(), Out::Frame(w));
        }
        assert_eq!(rig.poll_relay().unwrap(), Out::Idle);
    });
}

#[test]
fn the_input_buffer_is_bounded_and_pushes_back() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        rig.handshake();
        let junk = vec![0u8; 3 * IN_LEN];
        let taken = rig.relay.receive(&junk);
        assert_eq!(taken, IN_LEN, "no more than the buffer holds");
        assert_eq!(rig.relay.free(), 0);
        assert_eq!(rig.relay.receive(&junk), 0);
    });
}

#[test]
fn a_dialer_refuses_a_relay_that_is_not_the_one_it_named() {
    big_stack(|| {
        let mut rig = Rig::new(Some(nid(0x99)));
        let mut failed = None;
        for _ in 0..16 {
            rig.flush_client();
            let _ = rig.poll_relay();
            rig.flush_relay();
            match rig.poll_client() {
                Err(e) => {
                    failed = Some(e);
                    break;
                }
                Ok(Out::Open(_)) => panic!("opened to the wrong node"),
                Ok(_) => {}
            }
        }
        let e = failed.expect("the dialer must fail");
        assert!(matches!(e, CarrierError::Handshake(_)) && e.is_fatal(), "{e:?}");
        assert!(rig.client.is_ended());
        assert!(!rig.client.is_open());
        // an ended carrier stays ended and seals nothing
        assert_eq!(rig.poll_client().unwrap_err(), CarrierError::Closed);
        let mut out = vec![0u8; 100];
        assert_eq!(
            rig.client
                .seal(&pinc_crypto::Software, &Frame::Ping, &mut out)
                .unwrap_err(),
            CarrierError::Closed
        );
    });
}

#[test]
fn nothing_is_sealed_before_the_handshake() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        let mut out = vec![0u8; 100];
        assert_eq!(
            rig.client
                .seal(&pinc_crypto::Software, &Frame::Ping, &mut out)
                .unwrap_err(),
            CarrierError::NotOpen
        );
        assert!(!CarrierError::NotOpen.is_fatal());
    });
}

#[test]
fn a_tampered_handshake_never_opens() {
    big_stack(|| {
        // flip each byte of the dialer's first flight in turn: the listener must not open
        let first = {
            let mut rig = Rig::new(None);
            let mut b = vec![0u8; 32 * 1024];
            let n = rig.client.transmit(&mut b);
            b.truncate(n);
            b
        };
        for i in (0..first.len()).step_by(37) {
            let mut rig = Rig::new(None);
            let mut b = first.clone();
            b[i] ^= 0x01;
            rig.feed_relay(&b);
            let mut opened = false;
            for _ in 0..4 {
                match rig.poll_relay() {
                    Ok(Out::Open(_)) => opened = true,
                    Ok(Out::Idle) | Err(_) => break,
                    Ok(_) => {}
                }
            }
            // a flip in the length prefix can leave the unit incomplete, which is also not open
            assert!(!opened, "flip at {i} opened the carrier");
        }
        // and the listener's reply
        let mut rig = Rig::new(None);
        rig.flush_client();
        while !matches!(rig.poll_relay().unwrap(), Out::Idle) {}
        let mut b = vec![0u8; 32 * 1024];
        let n = rig.relay.transmit(&mut b);
        b.truncate(n);
        for i in (0..n).step_by(53) {
            let mut rig = Rig::new(None);
            rig.flush_client();
            while !matches!(rig.poll_relay().unwrap(), Out::Idle) {}
            let mut bad = b.clone();
            bad[i] ^= 0x80;
            rig.feed_client(&bad);
            let mut opened = false;
            for _ in 0..4 {
                match rig.poll_client() {
                    Ok(Out::Open(_)) => opened = true,
                    Ok(Out::Idle) | Err(_) => break,
                    Ok(_) => {}
                }
            }
            assert!(!opened, "flip at {i} in the reply opened the carrier");
        }
    });
}

#[test]
fn a_tampered_record_ends_the_carrier() {
    big_stack(|| {
        let p = pkt(200, 3);
        let f = Frame::Send {
            dst: nid(1),
            flag: 0,
            packet: &p,
        };
        let len = {
            let mut rig = Rig::new(None);
            rig.handshake();
            rig.seal_client(&f).len()
        };
        // flip a bit at every position of the unit (the length prefix may only stall or be refused)
        for i in (0..len).filter(|i| *i < 6 || i % 11 == 0 || *i + 20 > len) {
            let mut rig = Rig::new(None);
            rig.handshake();
            let mut unit = rig.seal_client(&f);
            unit[i] ^= 0x10;
            rig.feed_relay(&unit);
            match rig.poll_relay() {
                Ok(Out::Frame(got)) => panic!("tampered byte {i} produced a frame: {got:?}"),
                Ok(Out::Idle) => assert!(i < 2, "only a changed length can stall (byte {i})"),
                Ok(other) => panic!("{other:?}"),
                Err(e) => {
                    assert!(e.is_fatal(), "{e:?}");
                    assert!(rig.relay.is_ended());
                    assert_eq!(rig.poll_relay().unwrap_err(), CarrierError::Closed);
                }
            }
        }
        // the error for a body flip is authentication
        let mut rig = Rig::new(None);
        rig.handshake();
        let mut unit = rig.seal_client(&f);
        unit[10] ^= 1;
        rig.feed_relay(&unit);
        assert_eq!(rig.poll_relay().unwrap_err(), CarrierError::Authentication);
    });
}

#[test]
fn a_replayed_or_reordered_record_is_refused() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        rig.handshake();
        let a = rig.seal_client(&Frame::Ping);
        let b = rig.seal_client(&Frame::Pong);
        // replay: the same unit twice
        rig.feed_relay(&a);
        assert!(matches!(rig.poll_relay().unwrap(), Out::Frame(_)));
        rig.feed_relay(&a);
        assert_eq!(rig.poll_relay().unwrap_err(), CarrierError::Authentication);
        // reorder: the second unit first
        let mut rig = Rig::new(None);
        rig.handshake();
        let _a = rig.seal_client(&Frame::Ping);
        let b2 = rig.seal_client(&Frame::Pong);
        rig.feed_relay(&b2);
        assert_eq!(rig.poll_relay().unwrap_err(), CarrierError::Authentication);
        let _ = b;
    });
}

#[test]
fn units_of_the_wrong_size_end_the_carrier() {
    big_stack(|| {
        // a record unit of zero length
        let mut rig = Rig::new(None);
        rig.handshake();
        rig.feed_relay(&[0, 0]);
        assert_eq!(rig.poll_relay().unwrap_err(), CarrierError::UnitSize);
        // shorter than a tag
        let mut rig = Rig::new(None);
        rig.handshake();
        rig.feed_relay(&[0, 5, 1, 2, 3, 4, 5]);
        assert_eq!(rig.poll_relay().unwrap_err(), CarrierError::UnitSize);
        // longer than any record: refused on the length alone, before the bytes arrive
        let mut rig = Rig::new(None);
        rig.handshake();
        let too_long = u16::try_from(MAX_UNIT_LEN + 1).unwrap().to_be_bytes();
        rig.feed_relay(&too_long);
        assert_eq!(rig.poll_relay().unwrap_err(), CarrierError::UnitSize);
        // a handshake message length beyond any message, at the start
        let mut rig = Rig::new(None);
        rig.feed_relay(&[0xff, 0xff]);
        assert_eq!(rig.poll_relay().unwrap_err(), CarrierError::UnitSize);
    });
}

#[test]
fn a_bad_frame_in_a_good_record_is_dropped_and_the_carrier_lives_on() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        rig.handshake();
        let bad = rig.seal_client_bytes(&[0xee, 1, 2, 3]).unwrap();
        let good = rig.seal_client(&Frame::Ping);
        rig.feed_relay(&bad);
        rig.feed_relay(&good);
        let e = rig.poll_relay().unwrap_err();
        assert!(matches!(e, CarrierError::Frame(_)) && !e.is_fatal());
        assert!(rig.relay.is_open());
        assert_eq!(rig.poll_relay().unwrap(), Out::Frame(enc(&Frame::Ping)));
        // sealing nothing, or too much, is refused and the carrier lives on
        for bytes in [vec![], vec![0u8; MAX_FRAME_LEN + 1]] {
            let e = rig.seal_client_bytes(&bytes).unwrap_err();
            assert!(matches!(e, CarrierError::Frame(_)) && !e.is_fatal(), "{e:?}");
            assert!(rig.client.is_open());
        }
        assert_eq!(rig.seal_client(&Frame::Ping).len(), enc(&Frame::Ping).len() + 2 + 16);
    });
}

#[test]
fn a_handshake_output_that_fills_up_ends_the_carrier_and_the_error_says_so() {
    big_stack(|| {
        // the listener's host never transmits: each copy of the dialer's first message queues another reply
        let mut rig = Rig::new(None);
        let mut first = vec![0u8; 32 * 1024];
        let n = rig.client.transmit(&mut first);
        first.truncate(n);
        let mut failed = None;
        'copies: for _ in 0..64 {
            rig.feed_relay(&first);
            loop {
                match rig.poll_relay() {
                    Ok(Out::Idle) => break,
                    Ok(_) => {}
                    Err(e) => {
                        failed = Some(e);
                        break 'copies;
                    }
                }
            }
        }
        let e = failed.expect("the output never filled");
        assert_eq!(e, CarrierError::OutputFull);
        assert!(rig.relay.is_ended());
        assert!(e.is_fatal(), "the carrier ended and the error does not say so");
    });
}

#[test]
fn an_ended_carrier_answers_closed_before_any_other_check() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        rig.handshake();
        rig.feed_relay(&[0, 0]);
        assert_eq!(rig.poll_relay().unwrap_err(), CarrierError::UnitSize);
        assert!(rig.relay.is_ended());
        let p = pinc_crypto::Software;
        // no room, nothing to seal, too much to seal: the end is reported first
        assert_eq!(
            rig.relay.seal(&p, &Frame::Ping, &mut [0u8; 1]).unwrap_err(),
            CarrierError::Closed
        );
        let mut out = vec![0u8; 20 * 1024];
        assert_eq!(
            rig.relay.seal_bytes(&p, &[], &mut out).unwrap_err(),
            CarrierError::Closed
        );
        assert_eq!(
            rig.relay
                .seal_bytes(&p, &vec![0u8; MAX_FRAME_LEN + 1], &mut out)
                .unwrap_err(),
            CarrierError::Closed
        );
        assert_eq!(
            rig.relay.seal_bytes(&p, &[1], &mut [0u8; 1]).unwrap_err(),
            CarrierError::Closed
        );
        // a dialer that ended in its handshake answers a key answer the same way
        let mut rig = Rig::new(Some(nid(0x99)));
        let mut ended = false;
        for _ in 0..16 {
            rig.flush_client();
            let _ = rig.poll_relay();
            rig.flush_relay();
            if rig.poll_client().is_err() {
                ended = true;
                break;
            }
        }
        assert!(ended && rig.client.is_ended());
        assert_eq!(rig.answer_client().unwrap_err(), CarrierError::Closed);
    });
}

#[test]
fn a_key_answer_nobody_asked_for_changes_nothing() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        rig.handshake();
        let e = rig.answer_client().unwrap_err();
        assert_eq!(e, CarrierError::NoKeyRequest);
        assert!(!e.is_fatal());
        assert!(rig.client.is_open(), "a stray key answer ended an open carrier");
        // the carrier still carries frames both ways
        let ping = rig.seal_client(&Frame::Ping);
        rig.feed_relay(&ping);
        assert_eq!(rig.poll_relay().unwrap(), Out::Frame(enc(&Frame::Ping)));
        // before the handshake asks for a key it is the same: nothing ends
        let mut rig = Rig::new(None);
        assert_eq!(rig.answer_client().unwrap_err(), CarrierError::NoKeyRequest);
        assert!(!rig.client.is_ended());
        rig.handshake();
    });
}

#[test]
fn the_room_reported_counts_the_unit_a_poll_already_took() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        rig.handshake();
        assert_eq!(rig.relay.free(), IN_LEN);
        let ping = rig.seal_client(&Frame::Ping);
        rig.feed_relay(&ping);
        assert_eq!(rig.relay.free(), IN_LEN - ping.len());
        assert_eq!(rig.poll_relay().unwrap(), Out::Frame(enc(&Frame::Ping)));
        // the unit was taken: the next receive has the whole buffer, and `free` says so before it
        assert_eq!(rig.relay.free(), IN_LEN);
        let junk = vec![0u8; 2 * IN_LEN];
        assert_eq!(rig.relay.receive(&junk), IN_LEN);
    });
}

#[test]
fn a_finished_batch_travels_as_one_record() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        rig.handshake();
        let mut buf = vec![0u8; MAX_FRAME_LEN + 64];
        let mut b = BatchBuilder::new(&mut buf);
        let p = pkt(300, 9);
        for i in 0..5u8 {
            let f = Frame::SendAlias {
                alias: i,
                flag: 0,
                packet: &p,
            };
            assert_eq!(b.offer(&f).unwrap(), Offer::Added);
        }
        let plain = b.finish().unwrap().unwrap().to_vec();
        let unit = rig.seal_client_bytes(&plain).unwrap();
        rig.feed_relay(&unit);
        let Out::Frame(bytes) = rig.poll_relay().unwrap() else {
            panic!()
        };
        assert_eq!(bytes, plain);
        let Frame::Batch(batch) = Frame::decode(&bytes).unwrap() else {
            panic!()
        };
        assert_eq!(batch.len(), 5);
    });
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn garbage_on_an_open_carrier_never_panics_and_never_yields_a_frame(bytes in proptest::collection::vec(any::<u8>(), 0..300)) {
        big_stack(move || {
            let mut rig = Rig::new(None);
            rig.handshake();
            rig.feed_relay(&bytes);
            for _ in 0..4 {
                match rig.poll_relay() {
                    Ok(Out::Frame(_)) => panic!("unauthenticated bytes produced a frame"),
                    Ok(Out::Idle) | Err(_) => break,
                    Ok(_) => {}
                }
            }
        });
    }

    #[test]
    fn garbage_before_the_handshake_never_panics_or_opens(bytes in proptest::collection::vec(any::<u8>(), 0..400)) {
        big_stack(move || {
            let mut rig = Rig::new(None);
            rig.feed_relay(&bytes);
            for _ in 0..4 {
                match rig.poll_relay() {
                    Ok(Out::Open(_)) => panic!("garbage opened a carrier"),
                    Ok(Out::Idle) | Err(_) => break,
                    Ok(_) => {}
                }
            }
        });
    }
}

// ---- WebSocket framing ----

fn encode_ws(op: Opcode, payload: &[u8], mask: Option<[u8; 4]>) -> Vec<u8> {
    let mut out = vec![0u8; payload.len() + ws::MAX_HEADER];
    let n = ws::encode(op, payload, mask, &mut out).unwrap();
    out.truncate(n);
    out
}

#[test]
fn websocket_client_frames_are_masked_and_server_frames_are_not() {
    let payload = pkt(300, 0x5a);
    let mask = [1, 2, 3, 4];
    let c = encode_ws(Opcode::Binary, &payload, Some(mask));
    assert_eq!(c[0], 0x82, "FIN and binary");
    assert_eq!(c[1], 0x80 | 126, "masked, 16-bit length");
    assert_eq!(&c[2..4], &300u16.to_be_bytes());
    assert_eq!(&c[4..8], &mask);
    assert_ne!(&c[8..], &payload[..], "the payload is masked on the wire");
    let mut dec = Decoder::new(Role::Client);
    let mut buf = c.clone();
    let (frame, used) = dec.decode(&mut buf).unwrap().unwrap();
    assert_eq!(frame, WsFrame::Data(&payload));
    assert_eq!(used, c.len());

    let s = encode_ws(Opcode::Binary, &payload, None);
    assert_eq!(s[1], 126);
    assert_eq!(&s[4..], &payload[..], "a server frame is plain");
    let mut dec = Decoder::new(Role::Server);
    let mut buf = s.clone();
    let (frame, _) = dec.decode(&mut buf).unwrap().unwrap();
    assert_eq!(frame, WsFrame::Data(&payload));
    // the small length form
    let small = encode_ws(Opcode::Binary, &[1, 2, 3], None);
    assert_eq!(small, [0x82, 3, 1, 2, 3]);
}

#[test]
fn websocket_refuses_wrong_masking_and_everything_unsupported() {
    let masked = encode_ws(Opcode::Binary, b"abc", Some([9, 9, 9, 9]));
    let plain = encode_ws(Opcode::Binary, b"abc", None);
    // a server must not mask, a client must
    assert_eq!(
        Decoder::new(Role::Server).decode(&mut masked.clone()).unwrap_err(),
        WsError::Mask
    );
    assert_eq!(
        Decoder::new(Role::Client).decode(&mut plain.clone()).unwrap_err(),
        WsError::Mask
    );
    // reserved bits, text, unknown opcodes
    for first in [0xc2u8, 0xa2, 0x92] {
        assert_eq!(
            Decoder::new(Role::Server).decode(&mut [first, 0]).unwrap_err(),
            WsError::Reserved
        );
    }
    assert_eq!(
        Decoder::new(Role::Server).decode(&mut [0x81, 0]).unwrap_err(),
        WsError::Opcode(1)
    );
    for op in [3u8, 4, 7, 0xb, 0xf] {
        assert_eq!(
            Decoder::new(Role::Server).decode(&mut [0x80 | op, 0]).unwrap_err(),
            WsError::Opcode(op)
        );
    }
    // control frames: fragmented, too long
    assert_eq!(
        Decoder::new(Role::Server).decode(&mut [0x09, 0]).unwrap_err(),
        WsError::Control
    );
    let mut long_ping = vec![0x89, 126, 0, 126];
    long_ping.extend(vec![0u8; 126]);
    assert_eq!(
        Decoder::new(Role::Server).decode(&mut long_ping).unwrap_err(),
        WsError::Control
    );
    let mut out = vec![0u8; 400];
    assert_eq!(
        ws::encode(Opcode::Ping, &[0; 126], None, &mut out).unwrap_err(),
        WsError::Control
    );
    // a continuation with nothing to continue
    assert_eq!(
        Decoder::new(Role::Server).decode(&mut [0x80, 0]).unwrap_err(),
        WsError::Sequence
    );
    // a length not in its shortest form, and one over the bound
    assert_eq!(
        Decoder::new(Role::Server)
            .decode(&mut [0x82, 126, 0, 5, 0, 0, 0, 0, 0])
            .unwrap_err(),
        WsError::LengthForm
    );
    let mut big = vec![0x82, 127];
    big.extend((MAX_PAYLOAD as u64 + 100_000).to_be_bytes());
    assert_eq!(
        Decoder::new(Role::Server).decode(&mut big).unwrap_err(),
        WsError::TooLong
    );
    let mut small64 = vec![0x82, 127];
    small64.extend(5u64.to_be_bytes());
    assert_eq!(
        Decoder::new(Role::Server).decode(&mut small64).unwrap_err(),
        WsError::LengthForm
    );
    assert_eq!(
        ws::encode(Opcode::Binary, &vec![0; MAX_PAYLOAD + 1], None, &mut vec![0u8; 100_000]).unwrap_err(),
        WsError::TooLong
    );
    assert_eq!(
        ws::encode(Opcode::Binary, &[1, 2, 3], None, &mut [0u8; 3]).unwrap_err(),
        WsError::NoRoom
    );
}

#[test]
fn websocket_fragments_control_frames_and_partial_input() {
    let mut dec = Decoder::new(Role::Server);
    // a message in three fragments with a ping in between
    let mut wire = vec![0x02, 2, 1, 2]; // binary, not final
    wire.extend([0x89, 1, 0xee]); // ping
    wire.extend([0x00, 2, 3, 4]); // continuation, not final
    wire.extend([0x80, 1, 5]); // continuation, final
    wire.extend([0x8a, 0]); // pong
    wire.extend([0x88, 2, 0x03, 0xe8]); // close 1000
    let mut got = Vec::new();
    let mut at = 0;
    while at < wire.len() {
        let (frame, used) = dec.decode(&mut wire[at..]).unwrap().unwrap();
        match frame {
            WsFrame::Data(d) => got.extend_from_slice(d),
            WsFrame::Ping(p) => assert_eq!(p, [0xee]),
            WsFrame::Pong(p) => assert!(p.is_empty()),
            WsFrame::Close(c) => assert_eq!(c, Some(1000)),
        }
        at += used;
    }
    assert_eq!(got, [1, 2, 3, 4, 5]);
    // a data frame inside an unfinished message is out of sequence
    let mut dec = Decoder::new(Role::Server);
    dec.decode(&mut [0x02, 1, 1]).unwrap().unwrap();
    assert_eq!(dec.decode(&mut [0x82, 1, 1]).unwrap_err(), WsError::Sequence);
    // partial input asks for more at every cut and consumes nothing
    let full = encode_ws(Opcode::Binary, &pkt(500, 1), None);
    let mut dec = Decoder::new(Role::Server);
    for cut in 0..full.len() {
        assert!(dec.decode(&mut full[..cut].to_vec()).unwrap().is_none(), "cut {cut}");
    }
    assert!(dec.decode(&mut full.clone()).unwrap().is_some());
}

proptest! {
    #[test]
    fn websocket_round_trips_and_garbage_never_panics(
        payload in proptest::collection::vec(any::<u8>(), 0..2000),
        mask in any::<[u8; 4]>(),
        junk in proptest::collection::vec(any::<u8>(), 0..64),
        client in any::<bool>(),
    ) {
        let m = client.then_some(mask);
        let mut wire = encode_ws(Opcode::Binary, &payload, m);
        let peer = if client { Role::Client } else { Role::Server };
        let mut copy = wire.clone();
        let (frame, used) = Decoder::new(peer).decode(&mut copy).unwrap().unwrap();
        prop_assert_eq!(frame, WsFrame::Data(&payload));
        prop_assert_eq!(used, wire.len());
        let mut j = junk;
        let _ = Decoder::new(Role::Server).decode(&mut j);
        let _ = Decoder::new(Role::Client).decode(&mut wire);
    }
}

#[test]
fn the_carrier_runs_inside_websocket_frames() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        // every stream chunk travels as one WebSocket binary frame: the dialer masks, the listener does not
        let mut to_relay = Decoder::new(Role::Client);
        let mut to_client = Decoder::new(Role::Server);
        let wrap = |chunk: &[u8], mask: Option<[u8; 4]>| encode_ws(Opcode::Binary, chunk, mask);
        let mut ready = (false, false);
        for round in 0..64u8 {
            let mut buf = vec![0u8; 32 * 1024];
            let n = rig.client.transmit(&mut buf);
            if n > 0 {
                let mut frame = wrap(&buf[..n], Some([round, 2, 3, 4]));
                let mut at = 0;
                while at < frame.len() {
                    let (f, used) = to_relay.decode(&mut frame[at..]).unwrap().unwrap();
                    let WsFrame::Data(d) = f else { panic!() };
                    rig.feed_relay(d);
                    at += used;
                }
            }
            while let Out::Handshake | Out::Open(_) = rig.poll_relay().unwrap() {}
            let n = rig.relay.transmit(&mut buf);
            if n > 0 {
                let mut frame = wrap(&buf[..n], None);
                let mut at = 0;
                while at < frame.len() {
                    let (f, used) = to_client.decode(&mut frame[at..]).unwrap().unwrap();
                    let WsFrame::Data(d) = f else { panic!() };
                    rig.feed_client(d);
                    at += used;
                }
            }
            while let Out::Handshake | Out::Open(_) = rig.poll_client().unwrap() {}
            ready = (rig.client.is_open(), rig.relay.is_open());
            if ready == (true, true) {
                break;
            }
        }
        assert_eq!(ready, (true, true));
        let f = Frame::Ping;
        let unit = rig.seal_client(&f);
        let mut frame = wrap(&unit, Some([9, 8, 7, 6]));
        let (w, _) = to_relay.decode(&mut frame).unwrap().unwrap();
        let WsFrame::Data(d) = w else { panic!() };
        rig.feed_relay(d);
        assert_eq!(rig.poll_relay().unwrap(), Out::Frame(enc(&f)));
    });
}
