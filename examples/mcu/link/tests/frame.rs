//! The framing gives back every datagram it was given, whatever its bytes.
#![allow(missing_docs, clippy::unwrap_used, clippy::cast_possible_truncation)]

use pinc_mcu_link::frame::{Deframer, encode, encoded_max};

fn round_trip(data: &[u8]) {
    let mut enc = vec![0u8; encoded_max(data.len())];
    let n = encode(data, &mut enc).unwrap();
    assert!(n <= enc.len());
    assert_eq!(enc[n - 1], 0);
    assert!(
        enc[..n - 1].iter().all(|b| *b != 0),
        "a zero inside the frame of {data:02x?}"
    );
    let mut d = Deframer::<4096>::new();
    let mut got = None;
    for &b in &enc[..n] {
        if let Some(f) = d.push(b) {
            got = Some(f.to_vec());
        }
    }
    assert_eq!(got.as_deref(), Some(data), "frame {:02x?}", &enc[..n]);
}

#[test]
fn every_shape_of_datagram_survives() {
    round_trip(&[2, 0x43, 0, 0, 0, 0, 0, 0x10, 0, 0]);
    round_trip(&[0]);
    round_trip(&[0, 0, 0]);
    round_trip(&[1]);
    for len in [1usize, 2, 253, 254, 255, 256, 507, 508, 509, 510, 1200, 1500] {
        round_trip(&vec![0xAA; len]);
        round_trip(&vec![0; len]);
        let mut x = 0x1234_5678u32;
        let v: Vec<u8> = (0..len)
            .map(|_| {
                x = x.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
                if x >> 28 < 3 { 0 } else { (x >> 16) as u8 }
            })
            .collect();
        round_trip(&v);
        let mut edge = vec![0x55; len];
        *edge.last_mut().unwrap() = 0;
        round_trip(&edge);
    }
}

#[test]
fn a_receiver_that_joins_in_mid_frame_is_in_step_at_the_next_zero() {
    let mut d = Deframer::<64>::new();
    for b in [9u8, 9, 9, 0] {
        let _ = d.push(b);
    }
    let mut enc = [0u8; 16];
    let n = encode(b"ok", &mut enc).unwrap();
    let mut got = None;
    for &b in &enc[..n] {
        if let Some(f) = d.push(b) {
            got = Some(f.to_vec());
        }
    }
    assert_eq!(got.as_deref(), Some(&b"ok"[..]));
}
