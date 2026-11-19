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
    clippy::panic
)]

use std::collections::BTreeSet;
use std::fmt::Write as _;

use pinc_crypto::IdentityAlg;
use pinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use pinc_security::credit::CreditRecord;
use pinc_security::ids::{aead_from_tag, aead_tag};
use pinc_security::message::{
    Finish, IdSig, Initial, MAX_ID_SIG_LEN, MAX_MESSAGE_LEN, MessageType, PrekeyField, Reject, Reply, ResumeHello,
    ResumeReply,
};
use pinc_security::{AeadSet, ConnId, TicketBatch, TicketEntry};
use pinc_tests::SplitMix64;
use pinc_wire::{WireError, Writer};

fn bytes(b: &[u8]) -> String {
    format!("[{}]", b.iter().map(u8::to_string).collect::<Vec<_>>().join(","))
}

/// `[(i * s + 7) % 256 for i in 1..=n]`.
fn pat(n: usize, s: usize) -> Vec<u8> {
    (1..=n).map(|i| ((i * s + 7) % 256) as u8).collect()
}

fn arr<const N: usize>(v: &[u8]) -> [u8; N] {
    v.try_into().unwrap()
}

/// A message, owned: the fields of `MessageCodec.tla`, shared by the deterministic, random and parsed messages.
#[derive(Clone)]
enum Msg {
    Initial {
        full: bool,
        ver: u8,
        dcid: Vec<u8>,
        scid: Vec<u8>,
        alpn: Vec<u8>,
        offer: u8,
        e: [u8; 32],
        pre: Vec<u8>,
        cr: [u8; 6],
    },
    Reject {
        ty: u8,
        echo: [u8; 16],
    },
    Reply {
        scid: Vec<u8>,
        aead: u8,
        e: [u8; 32],
        ct: Vec<u8>,
        sealed: Vec<u8>,
    },
    Finish {
        sealed: Vec<u8>,
    },
    Hello {
        ver: u8,
        dcid: Vec<u8>,
        scid: Vec<u8>,
        alpn: Vec<u8>,
        aead: u8,
        tid: [u8; 16],
        e: [u8; 32],
        binder: [u8; 32],
        cr: [u8; 6],
    },
    RReply {
        scid: Vec<u8>,
        e: [u8; 32],
        tickets: Vec<([u8; 16], [u8; 4])>,
        cr: [u8; 6],
        confirm: [u8; 32],
    },
    IdSig {
        alg: u8,
        pk: Vec<u8>,
        sig: Vec<u8>,
        cr: Option<[u8; 6]>,
    },
}

/// A parser of the codec: which one, with the type of a reject and whether an identity plaintext has a credit record.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Initial,
    Reject(u8),
    Reply,
    Finish,
    Hello,
    RReply,
    IdSig(bool),
}

impl Kind {
    const fn name(self) -> &'static str {
        match self {
            Self::Initial => "initial",
            Self::Reject(_) => "reject",
            Self::Reply => "reply",
            Self::Finish => "finish",
            Self::Hello => "hello",
            Self::RReply => "rreply",
            Self::IdSig(_) => "idsig",
        }
    }

    const fn ty(self) -> u8 {
        match self {
            Self::Reject(t) => t,
            _ => 0,
        }
    }

    const fn wc(self) -> bool {
        matches!(self, Self::IdSig(true))
    }
}

impl Msg {
    const fn kind(&self) -> Kind {
        match self {
            Self::Initial { .. } => Kind::Initial,
            Self::Reject { ty, .. } => Kind::Reject(*ty),
            Self::Reply { .. } => Kind::Reply,
            Self::Finish { .. } => Kind::Finish,
            Self::Hello { .. } => Kind::Hello,
            Self::RReply { .. } => Kind::RReply,
            Self::IdSig { cr, .. } => Kind::IdSig(cr.is_some()),
        }
    }
}

const fn message_type(ty: u8) -> MessageType {
    if ty == 3 {
        MessageType::PrekeyReject
    } else {
        MessageType::ResumeReject
    }
}

fn json(m: &Msg) -> String {
    match m {
        Msg::Initial {
            full,
            ver,
            dcid,
            scid,
            alpn,
            offer,
            e,
            pre,
            cr,
        } => format!(
            r#"{{"k":"initial","full":{full},"ver":{ver},"dcid":{},"scid":{},"alpn":{},"offer":{offer},"e":{},"pre":{},"cr":{}}}"#,
            bytes(dcid),
            bytes(scid),
            bytes(alpn),
            bytes(e),
            bytes(pre),
            bytes(cr)
        ),
        Msg::Reject { ty, echo } => format!(r#"{{"k":"reject","ty":{ty},"echo":{}}}"#, bytes(echo)),
        Msg::Reply {
            scid,
            aead,
            e,
            ct,
            sealed,
        } => format!(
            r#"{{"k":"reply","scid":{},"aead":{aead},"e":{},"ct":{},"sealed":{}}}"#,
            bytes(scid),
            bytes(e),
            bytes(ct),
            bytes(sealed)
        ),
        Msg::Finish { sealed } => format!(r#"{{"k":"finish","sealed":{}}}"#, bytes(sealed)),
        Msg::Hello {
            ver,
            dcid,
            scid,
            alpn,
            aead,
            tid,
            e,
            binder,
            cr,
        } => format!(
            r#"{{"k":"hello","ver":{ver},"dcid":{},"scid":{},"alpn":{},"aead":{aead},"tid":{},"e":{},"binder":{},"cr":{}}}"#,
            bytes(dcid),
            bytes(scid),
            bytes(alpn),
            bytes(tid),
            bytes(e),
            bytes(binder),
            bytes(cr)
        ),
        Msg::RReply {
            scid,
            e,
            tickets,
            cr,
            confirm,
        } => {
            let t = tickets
                .iter()
                .map(|(tid, life)| format!(r#"{{"tid":{},"life":{}}}"#, bytes(tid), bytes(life)))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                r#"{{"k":"rreply","scid":{},"e":{},"tickets":[{t}],"cr":{},"confirm":{}}}"#,
                bytes(scid),
                bytes(e),
                bytes(cr),
                bytes(confirm)
            )
        }
        Msg::IdSig { alg, pk, sig, cr } => format!(
            r#"{{"k":"idsig","alg":{alg},"pk":{},"sig":{},"cr":{}}}"#,
            bytes(pk),
            bytes(sig),
            cr.as_ref().map_or_else(|| "[]".to_owned(), |c| bytes(c))
        ),
    }
}

/// Builds the borrowed message of `m` and calls its `write`.
fn write(m: &Msg, w: &mut Writer<'_>) -> Result<(), WireError> {
    match m {
        Msg::Initial {
            full,
            ver,
            dcid,
            scid,
            alpn,
            offer,
            e,
            pre,
            cr,
        } => {
            let prekey = if *full {
                PrekeyField::Full(<&[u8; KEM_ENCAPS_KEY_LEN]>::try_from(pre.as_slice()).unwrap())
            } else {
                PrekeyField::Hash(<&[u8; 32]>::try_from(pre.as_slice()).unwrap())
            };
            Initial {
                version: *ver,
                dcid: ConnId::new(dcid).unwrap(),
                scid: ConnId::new(scid).unwrap(),
                alpn: alpn.as_slice(),
                aead_offer: AeadSet::from_bits(*offer).unwrap(),
                e: *e,
                prekey,
                credit: CreditRecord::decode(cr),
            }
            .write(w)
        }
        Msg::Reject { ty, echo } => Reject { echo: *echo }.write(w, message_type(*ty)),
        Msg::Reply {
            scid,
            aead,
            e,
            ct,
            sealed,
        } => Reply {
            scid: ConnId::new(scid).unwrap(),
            aead: aead_from_tag(*aead).unwrap(),
            e: *e,
            ct: <&[u8; KEM_CIPHERTEXT_LEN]>::try_from(ct.as_slice()).unwrap(),
            sealed: sealed.as_slice(),
        }
        .write(w),
        Msg::Finish { sealed } => Finish {
            sealed: sealed.as_slice(),
        }
        .write(w),
        Msg::Hello {
            ver,
            dcid,
            scid,
            alpn,
            aead,
            tid,
            e,
            binder,
            cr,
        } => ResumeHello {
            version: *ver,
            dcid: ConnId::new(dcid).unwrap(),
            scid: ConnId::new(scid).unwrap(),
            alpn: alpn.as_slice(),
            aead: aead_from_tag(*aead).unwrap(),
            tid: *tid,
            e: *e,
            binder: *binder,
            credit: CreditRecord::decode(cr),
        }
        .write(w),
        Msg::RReply {
            scid,
            e,
            tickets,
            cr,
            confirm,
        } => {
            let mut batch = TicketBatch::new();
            for (tid, life) in tickets {
                assert!(batch.push(TicketEntry {
                    tid: *tid,
                    lifetime_s: u32::from_be_bytes(*life),
                }));
            }
            ResumeReply {
                scid: ConnId::new(scid).unwrap(),
                e: *e,
                tickets: batch,
                credit: CreditRecord::decode(cr),
                confirm: *confirm,
            }
            .write(w)
        }
        Msg::IdSig { alg, pk, sig, cr } => IdSig {
            alg: IdentityAlg::from_tag(*alg).unwrap(),
            public_key: pk.as_slice(),
            signature: sig.as_slice(),
            credit: cr.as_ref().map(CreditRecord::decode),
        }
        .write(w),
    }
}

/// The message the parser `kind` reads from `b`, as an owned message.
fn parse(kind: Kind, b: &[u8]) -> Result<Msg, WireError> {
    Ok(match kind {
        Kind::Initial => {
            let i = Initial::parse(b)?;
            let (full, pre) = match i.prekey {
                PrekeyField::Full(k) => (true, k.to_vec()),
                PrekeyField::Hash(h) => (false, h.to_vec()),
            };
            Msg::Initial {
                full,
                ver: i.version,
                dcid: i.dcid.as_bytes().to_vec(),
                scid: i.scid.as_bytes().to_vec(),
                alpn: i.alpn.to_vec(),
                offer: i.aead_offer.bits(),
                e: i.e,
                pre,
                cr: i.credit.encode(),
            }
        }
        Kind::Reject(ty) => Msg::Reject {
            ty,
            echo: Reject::parse(b, message_type(ty))?.echo,
        },
        Kind::Reply => {
            let r = Reply::parse(b)?;
            Msg::Reply {
                scid: r.scid.as_bytes().to_vec(),
                aead: aead_tag(r.aead),
                e: r.e,
                ct: r.ct.to_vec(),
                sealed: r.sealed.to_vec(),
            }
        }
        Kind::Finish => Msg::Finish {
            sealed: Finish::parse(b)?.sealed.to_vec(),
        },
        Kind::Hello => {
            let h = ResumeHello::parse(b)?;
            Msg::Hello {
                ver: h.version,
                dcid: h.dcid.as_bytes().to_vec(),
                scid: h.scid.as_bytes().to_vec(),
                alpn: h.alpn.to_vec(),
                aead: aead_tag(h.aead),
                tid: h.tid,
                e: h.e,
                binder: h.binder,
                cr: h.credit.encode(),
            }
        }
        Kind::RReply => {
            let r = ResumeReply::parse(b)?;
            Msg::RReply {
                scid: r.scid.as_bytes().to_vec(),
                e: r.e,
                tickets: r
                    .tickets
                    .entries()
                    .iter()
                    .map(|t| (t.tid, t.lifetime_s.to_be_bytes()))
                    .collect(),
                cr: r.credit.encode(),
                confirm: r.confirm,
            }
        }
        Kind::IdSig(wc) => {
            let i = IdSig::parse(b, wc)?;
            Msg::IdSig {
                alg: i.alg.tag(),
                pk: i.public_key.to_vec(),
                sig: i.signature.to_vec(),
                cr: i.credit.map(|c| c.encode()),
            }
        }
    })
}

/// The error of a parse as the model reads it; any other error fails the test.
fn parse_err(e: &WireError) -> String {
    match e {
        WireError::Truncated { needed } => format!(r#"{{"res":"truncated","needed":{needed}}}"#),
        WireError::Unexpected(what) => format!(r#"{{"res":"unexpected","what":"{what}"}}"#),
        other => panic!("a parse returned {other:?}"),
    }
}

/// The encoding of `m` into a buffer that is large enough, not recorded.
fn encode(m: &Msg) -> Vec<u8> {
    let mut buf = vec![0u8; MAX_MESSAGE_LEN + 100];
    let mut w = Writer::new(&mut buf);
    write(m, &mut w).unwrap();
    w.written().to_vec()
}

/// `MessageType::of(b)`, recorded.
fn type_ev(out: &mut String, b: &[u8]) -> Result<MessageType, WireError> {
    let r = MessageType::of(b);
    let res = match &r {
        Ok(t) => format!(r#"{{"res":"ok","ty":{}}}"#, *t as u8),
        Err(e) => parse_err(e),
    };
    let _ = writeln!(out, r#"{{"op":"type","b":{},"r":{res}}}"#, bytes(b));
    r
}

/// The parser `kind` on `b`, recorded.
fn parse_ev(out: &mut String, kind: Kind, b: &[u8]) -> Result<Msg, WireError> {
    let r = parse(kind, b);
    let res = match &r {
        Ok(m) => format!(r#"{{"res":"ok","m":{}}}"#, json(m)),
        Err(e) => parse_err(e),
    };
    let _ = writeln!(
        out,
        r#"{{"op":"parse","kind":"{}","ty":{},"wc":{},"b":{},"r":{res}}}"#,
        kind.name(),
        kind.ty(),
        kind.wc(),
        bytes(b)
    );
    r
}

/// The write of `m` into a buffer of `cap` bytes, recorded; the bytes it wrote.
fn write_ev(out: &mut String, m: &Msg, cap: usize) -> Result<Vec<u8>, WireError> {
    let mut buf = vec![0u8; cap];
    let mut w = Writer::new(&mut buf);
    let r = write(m, &mut w).map(|()| w.written().to_vec());
    let res = match &r {
        Ok(b) => format!(r#"{{"res":"ok","bytes":{}}}"#, bytes(b)),
        Err(WireError::BufferTooSmall { needed }) => format!(r#"{{"res":"small","needed":{needed}}}"#),
        Err(WireError::VarintOverflow) => r#"{"res":"overflow"}"#.to_owned(),
        Err(other) => panic!("a write returned {other:?}"),
    };
    let _ = writeln!(out, r#"{{"op":"write","m":{},"cap":{cap},"r":{res}}}"#, json(m));
    r
}

/// The lengths of the pieces of the encoding of `m`, in the order the code writes them.
fn pieces(m: &Msg) -> Vec<usize> {
    match m {
        Msg::Initial {
            dcid, scid, alpn, pre, ..
        } => vec![1, 1, 1, dcid.len(), 1, scid.len(), 1, alpn.len(), 1, 32, pre.len(), 6],
        Msg::Reject { .. } => vec![1, 16],
        Msg::Reply { scid, sealed, .. } => vec![1, 1, scid.len(), 1, 32, 1088, 2, sealed.len()],
        Msg::Finish { sealed } => vec![1, 2, sealed.len()],
        Msg::Hello { dcid, scid, alpn, .. } => {
            vec![1, 1, 1, dcid.len(), 1, scid.len(), 1, alpn.len(), 1, 16, 32, 32, 6]
        }
        Msg::RReply { scid, tickets, .. } => {
            let mut v = vec![1, 1, scid.len(), 32, 1];
            for _ in tickets {
                v.extend([16, 4]);
            }
            v.extend([6, 32]);
            v
        }
        Msg::IdSig { pk, sig, cr, .. } => {
            let mut v = vec![1, 2, pk.len(), 2, sig.len()];
            if cr.is_some() {
                v.push(6);
            }
            v
        }
    }
}

/// The values of `cands` inside `lo..hi`, no repeats.
fn within(cands: impl IntoIterator<Item = isize>, lo: usize, hi: usize) -> BTreeSet<usize> {
    cands
        .into_iter()
        .filter_map(|j| usize::try_from(j).ok())
        .filter(|j| (lo..hi).contains(j))
        .collect()
}

const TRAILING: WireError = WireError::Unexpected("trailing bytes");
const WRONG: WireError = WireError::Unexpected("wrong message type");

/// Every call the specification lists for one message.
fn exercise(out: &mut String, m: &Msg) {
    let b = encode(m);
    let n = b.len();
    assert!(n <= MAX_MESSAGE_LEN, "a message over MAX_MESSAGE_LEN");
    if matches!(m, Msg::IdSig { .. }) {
        assert!(n <= MAX_ID_SIG_LEN, "a plaintext over MAX_ID_SIG_LEN");
    }
    let small = n <= 1024;
    let own = m.kind();
    let ends: Vec<isize> = pieces(m)
        .iter()
        .scan(0isize, |acc, p| {
            *acc += *p as isize;
            Some(*acc)
        })
        .collect();
    let ni = n as isize;

    // 1. writes: exactly its size, one byte short, and none
    assert_eq!(write_ev(out, m, n).unwrap(), b);
    for cap in [n - 1, 0] {
        assert_eq!(
            write_ev(out, m, cap).unwrap_err(),
            WireError::BufferTooSmall { needed: 1 }
        );
    }

    // 2. its own parser gives the message back
    let back = parse_ev(out, own, &b).unwrap();
    assert_eq!(json(&back), json(m), "the round trip");

    // 3. cuts
    let cuts = if small {
        within(
            (0..=4)
                .chain([ni - 3, ni - 2, ni - 1])
                .chain(ends.iter().flat_map(|e| [e - 1, *e, e + 1])),
            0,
            n,
        )
    } else {
        within((0..=4).chain([ni - 1]).chain(ends.iter().copied()), 0, n)
    };
    for j in cuts {
        match parse_ev(out, own, &b[..j]) {
            Err(WireError::Truncated { needed }) => assert!(needed >= 1),
            other => panic!("a cut at {j} of {n} is not truncated: {:?}", other.err()),
        }
    }

    // 4. trailing bytes
    for v in if small { &[0u8, 1, 255][..] } else { &[0u8][..] } {
        let mut t = b.clone();
        t.push(*v);
        assert_eq!(parse_ev(out, own, &t).err(), Some(TRAILING));
    }

    // 5. changed bytes
    let positions = if small {
        within(
            (1..=4)
                .chain([ni - 2, ni - 1, ni])
                .chain(ends.iter().flat_map(|e| [e - 1, *e, e + 1])),
            1,
            n + 1,
        )
    } else {
        within([1, ni].into_iter().chain(ends.iter().map(|e| e + 1)), 1, n + 1)
    };
    for j in positions {
        for v in if small { &[0u8, 21, 255][..] } else { &[0u8, 255][..] } {
            if b[j - 1] == *v {
                continue;
            }
            let mut c = b.clone();
            c[j - 1] = *v;
            if let Ok(m2) = parse_ev(out, own, &c) {
                assert_eq!(
                    encode(&m2),
                    c,
                    "a changed byte at {j} parses and does not re-encode to itself"
                );
            }
        }
    }

    // 6. every other parser refuses it as the wrong type
    if small && !matches!(m, Msg::IdSig { .. }) {
        for k in [
            Kind::Initial,
            Kind::Reply,
            Kind::Finish,
            Kind::Hello,
            Kind::RReply,
            Kind::Reject(3),
            Kind::Reject(8),
        ] {
            if k != own {
                assert_eq!(parse_ev(out, k, &b).err(), Some(WRONG));
            }
        }
    }
}

const CR_A: [u8; 6] = [0, 4, 0, 100, 5, 220];

/// The messages of `MessageCodec.tla`, two sets narrowed.
fn deterministic() -> Vec<Msg> {
    let (c0, c1, c4, c20) = (vec![], vec![9u8], pat(4, 3), pat(20, 5));
    let (a1, a32) = (vec![104u8], pat(32, 11));
    let (e32, h32) = (arr::<32>(&pat(32, 17)), pat(32, 23));
    let (ek, ct, p16) = (pat(1184, 19), pat(1088, 41), arr::<16>(&pat(16, 29)));
    let sealed = |n: usize| pat(n, if n == 5384 { 37 } else { 31 });
    let mut v = Vec::new();
    for ver in [0u8, 255] {
        for dcid in [&c0, &c1, &c4, &c20] {
            for scid in [&c0, &c20] {
                for alpn in [&a1, &a32] {
                    for offer in [1u8, 3] {
                        v.push(Msg::Initial {
                            full: false,
                            ver,
                            dcid: dcid.clone(),
                            scid: scid.clone(),
                            alpn: alpn.clone(),
                            offer,
                            e: e32,
                            pre: h32.clone(),
                            cr: CR_A,
                        });
                    }
                }
            }
        }
    }
    for (dcid, scid) in [(&c0, &c20), (&c20, &c0), (&c4, &c4)] {
        for alpn in [&a1, &a32] {
            for offer in [1u8, 3] {
                v.push(Msg::Initial {
                    full: true,
                    ver: 1,
                    dcid: dcid.clone(),
                    scid: scid.clone(),
                    alpn: alpn.clone(),
                    offer,
                    e: e32,
                    pre: ek.clone(),
                    cr: [0; 6],
                });
            }
        }
    }
    for ty in [3u8, 8] {
        for echo in [[0u8; 16], p16] {
            v.push(Msg::Reject { ty, echo });
        }
    }
    for scid in [&c0, &c20] {
        for aead in [1u8, 2] {
            for n in [16, 123, 5384] {
                v.push(Msg::Reply {
                    scid: scid.clone(),
                    aead,
                    e: e32,
                    ct: ct.clone(),
                    sealed: sealed(n),
                });
            }
        }
    }
    for n in [16, 17, 123, 5384] {
        v.push(Msg::Finish { sealed: sealed(n) });
    }
    for dcid in [&c0, &c1, &c4, &c20] {
        for scid in [&c0, &c20] {
            for alpn in [&a1, &a32] {
                for aead in [1u8, 2] {
                    v.push(Msg::Hello {
                        ver: 1,
                        dcid: dcid.clone(),
                        scid: scid.clone(),
                        alpn: alpn.clone(),
                        aead,
                        tid: p16,
                        e: e32,
                        binder: arr::<32>(&h32),
                        cr: CR_A,
                    });
                }
            }
        }
    }
    let t1 = (p16, [0u8; 4]);
    let t2 = ([0u8; 16], [255u8; 4]);
    for scid in [&c0, &c20] {
        for tickets in [vec![], vec![t1], vec![t1, t2], vec![t2, t1, t2], vec![t1, t2, t1, t2]] {
            v.push(Msg::RReply {
                scid: scid.clone(),
                e: e32,
                tickets,
                cr: CR_A,
                confirm: arr::<32>(&h32),
            });
        }
    }
    for tag in 1..=4u8 {
        let alg = IdentityAlg::from_tag(tag).unwrap();
        for cr in [None, Some(CR_A)] {
            v.push(Msg::IdSig {
                alg: tag,
                pk: pat(alg.public_key_len(), 43),
                sig: pat(alg.signature_len(), 47),
                cr,
            });
        }
    }
    v
}

fn random_bytes(rng: &mut SplitMix64, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    rng.fill(&mut v);
    v
}

fn random_array<const N: usize>(rng: &mut SplitMix64) -> [u8; N] {
    let mut v = [0u8; N];
    rng.fill(&mut v);
    v
}

fn random_credit(rng: &mut SplitMix64) -> [u8; 6] {
    CreditRecord::decode(&random_array(rng)).encode()
}

fn random_len(rng: &mut SplitMix64, base: u64, modulus: u64) -> usize {
    (base + rng.next_u64() % modulus) as usize
}

/// 10 random messages of each kind.
fn random_messages(rng: &mut SplitMix64) -> Vec<Msg> {
    let mut v = Vec::new();
    for _ in 0..10 {
        let full = rng.next_u64() % 2 == 0;
        let ver = (rng.next_u64() % 256) as u8;
        let n = random_len(rng, 0, 21);
        let dcid = random_bytes(rng, n);
        let n = random_len(rng, 0, 21);
        let scid = random_bytes(rng, n);
        let n = random_len(rng, 1, 32);
        let alpn = random_bytes(rng, n);
        let offer = (1 + rng.next_u64() % 3) as u8;
        let e = random_array(rng);
        let pre = random_bytes(rng, if full { KEM_ENCAPS_KEY_LEN } else { 32 });
        let cr = random_credit(rng);
        v.push(Msg::Initial {
            full,
            ver,
            dcid,
            scid,
            alpn,
            offer,
            e,
            pre,
            cr,
        });
    }
    for _ in 0..10 {
        let ty = if rng.next_u64() % 2 == 0 { 3 } else { 8 };
        v.push(Msg::Reject {
            ty,
            echo: random_array(rng),
        });
    }
    for _ in 0..10 {
        let n = random_len(rng, 0, 21);
        let scid = random_bytes(rng, n);
        let aead = (1 + rng.next_u64() % 2) as u8;
        let e = random_array(rng);
        let ct = random_bytes(rng, KEM_CIPHERTEXT_LEN);
        let n = random_len(rng, 16, 300);
        let sealed = random_bytes(rng, n);
        v.push(Msg::Reply {
            scid,
            aead,
            e,
            ct,
            sealed,
        });
    }
    for _ in 0..10 {
        let n = random_len(rng, 16, 300);
        v.push(Msg::Finish {
            sealed: random_bytes(rng, n),
        });
    }
    for _ in 0..10 {
        let ver = (rng.next_u64() % 256) as u8;
        let n = random_len(rng, 0, 21);
        let dcid = random_bytes(rng, n);
        let n = random_len(rng, 0, 21);
        let scid = random_bytes(rng, n);
        let n = random_len(rng, 1, 32);
        let alpn = random_bytes(rng, n);
        let aead = (1 + rng.next_u64() % 2) as u8;
        let tid = random_array(rng);
        let e = random_array(rng);
        let binder = random_array(rng);
        let cr = random_credit(rng);
        v.push(Msg::Hello {
            ver,
            dcid,
            scid,
            alpn,
            aead,
            tid,
            e,
            binder,
            cr,
        });
    }
    for _ in 0..10 {
        let n = random_len(rng, 0, 21);
        let scid = random_bytes(rng, n);
        let count = rng.next_u64() % 5;
        let tickets: Vec<([u8; 16], [u8; 4])> = (0..count)
            .map(|_| {
                let tid = random_array(rng);
                let life = (rng.next_u64() as u32).to_be_bytes();
                (tid, life)
            })
            .collect();
        let e = random_array(rng);
        let cr = random_credit(rng);
        let confirm = random_array(rng);
        v.push(Msg::RReply {
            scid,
            e,
            tickets,
            cr,
            confirm,
        });
    }
    for _ in 0..10 {
        let tag = (1 + rng.next_u64() % 4) as u8;
        let alg = IdentityAlg::from_tag(tag).unwrap();
        let pk = random_bytes(rng, alg.public_key_len());
        let sig = random_bytes(rng, alg.signature_len());
        let cr = (rng.next_u64() % 2 == 0).then(|| random_credit(rng));
        v.push(Msg::IdSig { alg: tag, pk, sig, cr });
    }
    v
}

/// What an out-of-range field must do.
enum Expect {
    /// Written, and refused by its own parser with this reason.
    Refused(&'static str),
    /// Not written: a length that does not fit its prefix.
    Overflow,
}

/// The fields out of the documented ranges, with what each must do.
fn out_of_range() -> Vec<(Msg, Expect)> {
    let (c4, e32, h32, p16, ct) = (
        pat(4, 3),
        arr::<32>(&pat(32, 17)),
        arr::<32>(&pat(32, 23)),
        arr::<16>(&pat(16, 29)),
        pat(1088, 41),
    );
    let mut v = Vec::new();
    for n in [0, 33, 255, 256] {
        let expect = || {
            if n == 256 {
                Expect::Overflow
            } else {
                Expect::Refused("alpn length")
            }
        };
        v.push((
            Msg::Initial {
                full: false,
                ver: 1,
                dcid: c4.clone(),
                scid: c4.clone(),
                alpn: pat(n, 13),
                offer: 1,
                e: e32,
                pre: h32.to_vec(),
                cr: CR_A,
            },
            expect(),
        ));
        v.push((
            Msg::Hello {
                ver: 1,
                dcid: c4.clone(),
                scid: c4.clone(),
                alpn: pat(n, 13),
                aead: 1,
                tid: p16,
                e: e32,
                binder: h32,
                cr: CR_A,
            },
            expect(),
        ));
    }
    for n in [15, 5385, 65536] {
        v.push((
            Msg::Finish { sealed: pat(n, 3) },
            if n == 65536 {
                Expect::Overflow
            } else {
                Expect::Refused("sealed length")
            },
        ));
    }
    for n in [15, 5385] {
        v.push((
            Msg::Reply {
                scid: c4.clone(),
                aead: 1,
                e: e32,
                ct: ct.clone(),
                sealed: pat(n, 3),
            },
            Expect::Refused("sealed length"),
        ));
    }
    v.push((
        Msg::IdSig {
            alg: 1,
            pk: pat(31, 43),
            sig: pat(64, 47),
            cr: None,
        },
        Expect::Refused("public key length"),
    ));
    v.push((
        Msg::IdSig {
            alg: 1,
            pk: pat(32, 43),
            sig: pat(63, 47),
            cr: None,
        },
        Expect::Refused("signature length"),
    ));
    v
}

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
