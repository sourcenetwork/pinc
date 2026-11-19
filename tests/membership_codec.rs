//! The hub stream codec: every frame round-trips, the parser is strict, passthrough frames are untouched, and the
//! codec never allocates.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::struct_excessive_bools,
    clippy::cast_possible_truncation,
    clippy::doc_markdown,
    clippy::bool_to_int_with_if,
    clippy::manual_range_contains,
    clippy::manual_assert_eq,
    clippy::redundant_closure_for_method_calls,
    clippy::assert_is_empty,
    clippy::len_zero,
    clippy::unused_self,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::too_many_arguments
)]

use proptest::prelude::*;
use pinc_membership::NodeId;
use pinc_membership::codec::{
    Alive, Down, ENTRY_LEN, Frame, FrameError, Hello, MAX_BODY, Other, Path, Probe, Proof, Record, SNAP_CHUNK, Snap,
    entry_bytes, ty,
};

pinc_tests::install_counting_allocator!();

fn rec(n: u8) -> Record {
    Record {
        inc: 0x0102_0304_0506_0000 + u64::from(n),
        ver: 0x0a0b,
        thash: [n; 8],
    }
}

fn roundtrip(f: &Frame<'_>) -> Vec<u8> {
    let mut buf = vec![0u8; 70_000];
    let bytes = f.encode(&mut buf).unwrap().to_vec();
    let (back, used) = Frame::read(&bytes).unwrap().unwrap();
    assert_eq!(used, bytes.len());
    assert_eq!(&back, f);
    let again = back.encode(&mut buf).unwrap();
    assert_eq!(again, &bytes[..], "a parsed frame encodes to the same bytes");
    bytes
}

#[test]
fn hello_layout_and_flags() {
    let h = Frame::Hello(Hello {
        rec: rec(1),
        snap: true,
        homed: true,
    });
    let b = roundtrip(&h);
    // len32 | type | topic_len | inc8 ver2 thash8 flags
    assert_eq!(&b[..6], &[0, 0, 0, 21, 1, 0]);
    assert_eq!(b.len(), 4 + 21);
    assert_eq!(b[24], 3, "bit0 snapshot, bit1 homed");
    for (snap, homed, flags) in [(false, false, 0), (true, false, 1), (false, true, 2)] {
        let b = roundtrip(&Frame::Hello(Hello {
            rec: rec(2),
            snap,
            homed,
        }));
        assert_eq!(b[24], flags);
    }
}

#[test]
fn ack_probe_delta_snap_down_roundtrip() {
    roundtrip(&Frame::Ack);
    roundtrip(&Frame::Probe);
    let m: NodeId = [9; 32];
    for alive in [Alive::Down, Alive::Alive, Alive::Left] {
        let b = roundtrip(&Frame::Delta(pinc_membership::codec::Entry {
            member: &m,
            rec: rec(3),
            alive,
        }));
        assert_eq!(b.len(), 4 + 2 + ENTRY_LEN, "one 51 byte entry");
    }
    let mut entries = Vec::new();
    for i in 0..5u8 {
        entries.extend_from_slice(&entry_bytes(&[i; 32], &rec(i), Alive::Alive));
    }
    for (partial, more) in [(false, false), (true, false), (false, true), (true, true)] {
        let s = Snap::new(partial, more, &entries).unwrap();
        assert_eq!(s.len(), 5);
        let b = roundtrip(&Frame::Snap(s));
        assert_eq!(b[6], u8::from(partial) | (u8::from(more) << 1));
        let names: Vec<u8> = s.entries().map(|e| e.member[0]).collect();
        assert_eq!(names, [0, 1, 2, 3, 4]);
    }
    let proof = Proof::new(
        1500,
        &[
            Probe {
                age_ms: 1200,
                path: Path::Session,
            },
            Probe {
                age_ms: 1100,
                path: Path::Relay,
            },
        ],
    )
    .unwrap();
    assert!(proof.independent());
    roundtrip(&Frame::Down(Down {
        member: &m,
        inc: 0x1234_5678_0001,
        proof,
    }));
    let same = Proof::new(
        10,
        &[Probe {
            age_ms: 1,
            path: Path::Session,
        }; 2],
    )
    .unwrap();
    assert!(!same.independent(), "two probes on one path are not independent");
}

#[test]
fn other_frames_pass_through_untouched() {
    for t in [5u8, 6, 7, 8, 9, 10, 11, ty::FLOOR, 15, 16, 77, 255] {
        let f = Frame::Other(Other {
            ty: t,
            topic: b"news",
            rest: &[1, 2, 3, 4],
        });
        let b = roundtrip(&f);
        assert_eq!(&b[4..6], &[t, 4]);
    }
    let long = [7u8; 255];
    roundtrip(&Frame::Other(Other {
        ty: 9,
        topic: &long,
        rest: &[],
    }));
}

#[test]
fn strictness() {
    let mut buf = [0u8; 256];
    let m: NodeId = [1; 32];
    let hello = Frame::Hello(Hello {
        rec: rec(1),
        snap: false,
        homed: false,
    })
    .encode(&mut buf)
    .unwrap()
    .to_vec();
    fn body(b: &[u8]) -> Result<Frame<'_>, FrameError> {
        Frame::parse(&b[4..])
    }

    // trailing byte, short body
    let mut long = hello.clone();
    long.push(0);
    assert!(matches!(body(&long), Err(FrameError::Malformed(_))));
    assert!(body(&hello[..hello.len() - 1]).is_err());
    // reserved flag bit
    let mut bad = hello.clone();
    *bad.last_mut().unwrap() = 4;
    assert!(matches!(body(&bad), Err(FrameError::Malformed("reserved HELLO flag"))));
    // a membership frame with a topic
    assert!(matches!(
        Frame::parse(&[ty::ACK, 1, b'x']),
        Err(FrameError::Malformed("membership frame with a topic"))
    ));
    assert!(Frame::parse(&[ty::ACK, 0, 0]).is_err(), "ACK is empty");
    assert!(Frame::parse(&[ty::PROBE, 0, 0]).is_err(), "PROBE is empty");
    // topic longer than the frame
    assert!(Frame::parse(&[200, 9, 1]).is_err());
    assert!(Frame::parse(&[]).is_err());
    assert!(Frame::parse(&[1]).is_err());
    // alive byte out of range
    let mut e = vec![ty::DELTA, 0];
    e.extend_from_slice(&entry_bytes(&m, &rec(1), Alive::Alive));
    *e.last_mut().unwrap() = 3;
    assert!(matches!(Frame::parse(&e), Err(FrameError::Malformed("alive byte"))));
    // a snapshot of anything but alive entries
    let mut s = vec![ty::SNAP, 0, 0];
    s.extend_from_slice(&entry_bytes(&m, &rec(1), Alive::Down));
    assert!(Frame::parse(&s).is_err());
    // a snapshot that is not a whole number of entries, or has a reserved flag
    let mut s = vec![ty::SNAP, 0, 0];
    s.extend_from_slice(&entry_bytes(&m, &rec(1), Alive::Alive));
    s.push(0);
    assert!(Frame::parse(&s).is_err());
    s.pop();
    s[2] = 4;
    assert!(Frame::parse(&s).is_err());
    // an empty snapshot is valid (a hub with no members)
    assert!(matches!(Frame::parse(&[ty::SNAP, 0, 0]), Ok(Frame::Snap(s)) if s.is_empty()));
    // DOWN: no probes, too many probes, bad path, trailing bytes
    let mut d = vec![ty::DOWN, 0];
    d.extend_from_slice(&m);
    d.extend_from_slice(&[0; 8]);
    d.extend_from_slice(&[0, 0, 0, 5]);
    d.push(0);
    assert!(Frame::parse(&d).is_err(), "a DOWN without proof is refused");
    d.pop();
    d.extend_from_slice(&[1, 0, 0, 0, 1, 9]);
    assert!(Frame::parse(&d).is_err(), "path 9");
    let n = d.len();
    d[n - 1] = 1;
    assert!(Frame::parse(&d).is_ok());
    d.push(0);
    assert!(Frame::parse(&d).is_err());
}

#[test]
fn stream_reading() {
    let mut buf = [0u8; 64];
    let a = Frame::Ack.encode(&mut buf).unwrap().to_vec();
    let mut two = a.clone();
    two.extend_from_slice(&a);
    let (f, n) = Frame::read(&two).unwrap().unwrap();
    assert_eq!((f, n), (Frame::Ack, a.len()));
    let (f, _) = Frame::read(&two[n..]).unwrap().unwrap();
    assert_eq!(f, Frame::Ack);
    for cut in 0..a.len() {
        assert_eq!(Frame::read(&a[..cut]), Ok(None), "a partial frame waits for more bytes");
    }
    // a length over the limit fails at the prefix, before any body arrives
    let big = u32::try_from(MAX_BODY + 1).unwrap().to_be_bytes();
    assert_eq!(Frame::read(&big), Err(FrameError::TooLarge));
    assert_eq!(
        Frame::read(&0u32.to_be_bytes()),
        Err(FrameError::Wire(pinc_wire::WireError::Truncated { needed: 1 }))
    );
    // output too small
    assert!(matches!(Frame::Ack.encode(&mut [0u8; 3]), Err(FrameError::Wire(_))));
}

#[test]
fn zero_copy_views_borrow_the_input() {
    let mut entries = Vec::new();
    entries.extend_from_slice(&entry_bytes(&[5; 32], &rec(5), Alive::Alive));
    let snap = Snap::new(false, false, &entries).unwrap();
    let mut buf = vec![0u8; 256];
    let bytes = Frame::Snap(snap).encode(&mut buf).unwrap().to_vec();
    let (Frame::Snap(s), _) = Frame::read(&bytes).unwrap().unwrap() else {
        panic!("snap")
    };
    let e = s.entries().next().unwrap();
    let base = bytes.as_ptr() as usize;
    let at = e.member.as_ptr() as usize;
    assert!(
        at >= base && at + 32 <= base + bytes.len(),
        "the member id points into the frame"
    );
    let Ok(Frame::Other(o)) = Frame::parse(&[9, 1, b't', 1, 2]) else {
        panic!("other")
    };
    assert_eq!((o.topic, o.rest), (&b"t"[..], &[1u8, 2][..]));
}

#[test]
fn the_codec_never_allocates() {
    let m: NodeId = [4; 32];
    let mut buf = [0u8; 4096];
    let mut entries = [0u8; ENTRY_LEN * SNAP_CHUNK];
    for i in 0..SNAP_CHUNK {
        entries[i * ENTRY_LEN..(i + 1) * ENTRY_LEN].copy_from_slice(&entry_bytes(
            &[i as u8; 32],
            &rec(1),
            Alive::Alive,
        ));
    }
    let stats = pinc_tests::measure(|| {
        for _ in 0..100 {
            let snap = Snap::new(false, true, &entries).unwrap();
            let n = Frame::Snap(snap).encode(&mut buf).unwrap().len();
            let (Frame::Snap(s), used) = Frame::read(&buf[..n]).unwrap().unwrap() else {
                panic!()
            };
            assert_eq!((used, s.entries().count()), (n, SNAP_CHUNK));
            let d = Frame::Delta(pinc_membership::codec::Entry {
                member: &m,
                rec: rec(2),
                alive: Alive::Down,
            });
            let n = d.encode(&mut buf).unwrap().len();
            assert_eq!(Frame::read(&buf[..n]).unwrap().unwrap().0, d);
        }
    });
    assert_eq!(stats.count(), 0, "{stats:?}");
}

fn arb_record() -> impl Strategy<Value = Record> {
    (any::<u64>(), any::<u16>(), any::<[u8; 8]>()).prop_map(|(inc, ver, thash)| Record { inc, ver, thash })
}

fn arb_alive() -> impl Strategy<Value = Alive> {
    prop_oneof![Just(Alive::Down), Just(Alive::Alive), Just(Alive::Left)]
}

fn arb_path() -> impl Strategy<Value = Path> {
    prop_oneof![Just(Path::Session), Just(Path::Direct), Just(Path::Relay)]
}

proptest! {
    #[test]
    fn hello_roundtrips(r in arb_record(), snap in any::<bool>(), homed in any::<bool>()) {
        roundtrip(&Frame::Hello(Hello { rec: r, snap, homed }));
    }

    #[test]
    fn delta_roundtrips(m in any::<[u8; 32]>(), r in arb_record(), a in arb_alive()) {
        roundtrip(&Frame::Delta(pinc_membership::codec::Entry { member: &m, rec: r, alive: a }));
    }

    #[test]
    fn snap_roundtrips(
        ents in proptest::collection::vec((any::<[u8; 32]>(), arb_record()), 0..40),
        partial in any::<bool>(),
        more in any::<bool>(),
    ) {
        let mut raw = Vec::new();
        for (m, r) in &ents {
            raw.extend_from_slice(&entry_bytes(m, r, Alive::Alive));
        }
        let s = Snap::new(partial, more, &raw).unwrap();
        roundtrip(&Frame::Snap(s));
        let got: Vec<(NodeId, Record)> = s.entries().map(|e| (*e.member, e.rec)).collect();
        prop_assert_eq!(got, ents);
    }

    #[test]
    fn down_roundtrips(
        m in any::<[u8; 32]>(),
        inc in any::<u64>(),
        silence in any::<u32>(),
        probes in proptest::collection::vec((any::<u32>(), arb_path()), 1..=4),
    ) {
        let ps: Vec<Probe> = probes.iter().map(|&(age_ms, path)| Probe { age_ms, path }).collect();
        let proof = Proof::new(silence, &ps).unwrap();
        roundtrip(&Frame::Down(Down { member: &m, inc, proof }));
    }

    #[test]
    fn other_roundtrips(
        t in prop::sample::select((5u8..=255).filter(|t| !matches!(t, 12 | 13)).collect::<Vec<_>>()),
        topic in proptest::collection::vec(any::<u8>(), 0..255),
        rest in proptest::collection::vec(any::<u8>(), 0..300),
    ) {
        roundtrip(&Frame::Other(Other { ty: t, topic: &topic, rest: &rest }));
    }

    #[test]
    fn parse_never_panics_and_is_canonical(bytes in proptest::collection::vec(any::<u8>(), 0..200)) {
        if let Ok(f) = Frame::parse(&bytes) {
            let mut buf = vec![0u8; 1024];
            let enc = f.encode(&mut buf).unwrap();
            prop_assert_eq!(&enc[4..], &bytes[..], "only the canonical encoding parses");
        }
        let _ = Frame::read(&bytes);
    }

    #[test]
    fn a_cut_frame_never_parses_as_another(r in arb_record(), cut in 0usize..25) {
        let mut buf = [0u8; 64];
        let b = Frame::Hello(Hello { rec: r, snap: true, homed: false }).encode(&mut buf).unwrap().to_vec();
        if cut < b.len() {
            prop_assert_eq!(Frame::read(&b[..cut]), Ok(None));
        }
    }
}
