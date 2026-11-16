#![allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]

use super::*;

const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];
const ORIGIN: NodeId = [0x42; 32];
const KEY: [u8; MAX_PUBLIC_KEY_LEN] = [0xab; MAX_PUBLIC_KEY_LEN];
const SIG: [u8; MAX_SIGNATURE_LEN] = [0xcd; MAX_SIGNATURE_LEN];

/// A fixed buffer a head can be appended to.
struct Buf {
    b: [u8; MAX_HEAD2 + 16],
    n: usize,
}

impl Buf {
    fn new() -> Self {
        Self {
            b: [0; MAX_HEAD2 + 16],
            n: 0,
        }
    }

    fn bytes(&self) -> &[u8] {
        &self.b[..self.n]
    }
}

impl Extend<u8> for Buf {
    fn extend<I: IntoIterator<Item = u8>>(&mut self, iter: I) {
        for x in iter {
            self.b[self.n] = x;
            self.n += 1;
        }
    }
}

/// Eight parents in ascending order; a test takes a prefix.
fn parents() -> [ContentId; 8] {
    core::array::from_fn(|i| [u8::try_from(i).unwrap() + 3; 32])
}

fn head(alg: IdentityAlg, ps: &[ContentId]) -> Head2<'_> {
    Head2 {
        alg,
        isb: true,
        origin: &ORIGIN,
        incarnation: 9,
        seq: 77,
        ts: Hlc::new(1_700_000_000_000, 4),
        parents: ps,
        pk: if alg == IdentityAlg::Ed25519 {
            &[]
        } else {
            &KEY[..alg.public_key_len()]
        },
        sig: &SIG[..alg.signature_len()],
    }
}

fn written(h: &Head2<'_>, body: &[u8]) -> Buf {
    let mut b = Buf::new();
    h.write(u32::try_from(body.len()).unwrap(), &mut b).unwrap();
    b.extend(body.iter().copied());
    b
}

#[test]
fn write_then_parse_is_the_identity() {
    for alg in ALGS {
        for np in [0u8, 1, 8] {
            let ps = parents();
            let h = head(alg, &ps[..usize::from(np)]);
            let b = written(&h, b"body");
            let (got, len) = Head2::parse(b.bytes()).unwrap();
            assert_eq!(got, h, "{alg:?} with {np} parents");
            assert_eq!(len, h.len());
            assert_eq!(&b.bytes()[len..], b"body");
            assert_eq!(b.n, h.len() + 4);
        }
    }
}

#[test]
fn the_layout_is_fixed() {
    let ps = parents();
    let h = head(IdentityAlg::Ed25519, &ps[..1]);
    let b = written(&h, b"");
    let x = b.bytes();
    assert_eq!(x[..4], [2, 1, 1, 1]);
    assert_eq!(x[4..36], ORIGIN);
    assert_eq!(x[36..44], 9u64.to_be_bytes());
    assert_eq!(x[44..52], 77u64.to_be_bytes());
    assert_eq!(x[52..60], 1_700_000_000_000u64.to_be_bytes());
    assert_eq!(x[60..64], 4u32.to_be_bytes());
    assert_eq!(x[64..68], 0u32.to_be_bytes());
    assert_eq!(x[68..100], ps[0]);
    assert_eq!(x[100..], SIG[..64]);
}

fn flipped(alg: IdentityAlg, np: u8, f: impl FnOnce(&mut [u8])) -> Result<(), Malformed> {
    let ps = parents();
    let h = head(alg, &ps[..usize::from(np)]);
    let mut b = written(&h, b"");
    f(&mut b.b[..b.n]);
    Head2::parse(b.bytes()).map(|_| ())
}

#[test]
fn malformed_heads_are_refused() {
    let alg = IdentityAlg::Ed25519;
    assert_eq!(flipped(alg, 2, |b| b[0] = 1), Err(Malformed("version")));
    assert_eq!(flipped(alg, 2, |b| b[0] = 3), Err(Malformed("version")));
    assert_eq!(flipped(alg, 2, |b| b[1] = 9), Err(Malformed("algorithm")));
    for flags in [2u8, 3, 0x80] {
        assert_eq!(flipped(alg, 2, |b| b[2] = flags), Err(Malformed("flags")));
    }
    assert_eq!(flipped(alg, 2, |b| b[3] = 9), Err(Malformed("parents")));
    assert_eq!(flipped(alg, 2, |b| b[3] = 255), Err(Malformed("parents")));
    let (a, z) = (68, 100);
    assert_eq!(
        flipped(alg, 2, |b| {
            let first: [u8; 32] = b[a..z].try_into().unwrap();
            b.copy_within(z..z + 32, a);
            b[z..z + 32].copy_from_slice(&first);
        }),
        Err(Malformed("parents"))
    );
    assert_eq!(flipped(alg, 2, |b| b.copy_within(a..z, z)), Err(Malformed("parents")));
    assert_eq!(flipped(alg, 2, |_| {}), Ok(()));
}

#[test]
fn a_body_that_differs_from_blen_is_refused() {
    let h = head(IdentityAlg::Ed25519, &[]);
    let mut b = Buf::new();
    h.write(3, &mut b).unwrap();
    for body in [&b""[..], b"ab", b"abcd"] {
        let mut c = Buf::new();
        c.extend(b.bytes().iter().copied().chain(body.iter().copied()));
        assert_eq!(
            Head2::parse(c.bytes()).map(|_| ()),
            Err(Malformed("body length")),
            "{}",
            body.len()
        );
    }
    let mut c = Buf::new();
    c.extend(b.bytes().iter().copied().chain(*b"abc"));
    assert!(Head2::parse(c.bytes()).is_ok());
}

#[test]
fn every_cut_head_is_refused() {
    for alg in ALGS {
        for np in [0u8, 1, 8] {
            let ps = parents();
            let h = head(alg, &ps[..usize::from(np)]);
            let b = written(&h, b"");
            for k in 0..h.len() {
                assert!(Head2::parse(&b.bytes()[..k]).is_err(), "{alg:?} np {np} cut at {k}");
            }
            assert!(Head2::parse(b.bytes()).is_ok());
        }
    }
}

#[test]
fn the_longest_head_is_the_maximum() {
    assert_eq!(MAX_HEAD2, 5681);
    let ps = parents();
    let h = head(IdentityAlg::Hybrid, &ps);
    assert_eq!(h.len(), MAX_HEAD2);
    assert_eq!(written(&h, b"").n, MAX_HEAD2);
    let ps = parents();
    for alg in ALGS {
        assert!(head(alg, &ps).len() <= MAX_HEAD2);
    }
}

#[test]
fn nine_parents_are_not_written() {
    let nine: [ContentId; 9] = core::array::from_fn(|i| [u8::try_from(i).unwrap(); 32]);
    let h = head(IdentityAlg::Ed25519, &nine);
    let mut b = Buf::new();
    assert_eq!(h.write(0, &mut b), Err(TooLong));
    assert_eq!(b.n, 0);
}

#[test]
fn the_id_is_the_version_1_function() {
    let h = head(IdentityAlg::Ed25519, &[]);
    assert_eq!(h.mid(b"t/1"), message_id(&ORIGIN, 9, 77, b"t/1"));
    assert_ne!(h.mid(b"t/1"), h.mid(b"t/2"));
}

#[test]
fn the_statement_fields_are_the_heads() {
    let ps = parents();
    let h = head(IdentityAlg::Ed25519, &ps[..2]);
    let hash = [5u8; 32];
    let f = h.statement_fields(b"t/1", &hash);
    assert_eq!((f.origin_alg, f.origin), (IdentityAlg::Ed25519, &ORIGIN));
    assert_eq!((f.incarnation, f.seq, f.flags), (9, 77, 1));
    assert_eq!(
        (f.topic, f.time, f.parents, f.body),
        (&b"t/1"[..], h.ts, &ps[..2], &hash)
    );
}
