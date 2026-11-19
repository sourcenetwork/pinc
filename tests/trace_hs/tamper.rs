//! The tampers of `trace_handshake.rs`: which field of which message a flipped bit changes, in the model's names, and
//! the inputs built from them.
use pinc_security::Established;
use pinc_security::ids::aead_tag;
use pinc_security::message::{Finish, Initial, MessageType, PrekeyField, Reject, Reply, ResumeHello, ResumeReply};

use crate::sim::Inp;

/// What a tamper did to a message, as the model can state it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Class {
    /// Does not parse.
    Malformed,
    /// One modelled field changed: the model's field name.
    Field(&'static str),
    /// Anything else (a length byte, several fields): not run.
    Unmodelled,
}

/// A tamper: the delivery index it applies to, the mutated bytes and what the mutation changed.
pub type Tamper = (usize, Vec<u8>, Class);

/// The fields of a message a tamper can change, by the model's names, or `None` if it does not parse.
fn fields(bytes: &[u8]) -> Option<Vec<(&'static str, Vec<u8>)>> {
    let ty = MessageType::of(bytes).ok()?;
    Some(match ty {
        MessageType::Initial | MessageType::ShortInitial => {
            let m = Initial::parse(bytes).ok()?;
            let pk = match m.prekey {
                PrekeyField::Full(k) => k.to_vec(),
                PrekeyField::Hash(h) => h.to_vec(),
            };
            vec![
                ("ver", vec![m.version]),
                ("dc", m.dcid.as_bytes().to_vec()),
                ("sc", m.scid.as_bytes().to_vec()),
                ("al", m.alpn.to_vec()),
                ("of", vec![m.aead_offer.bits()]),
                ("e", m.e.to_vec()),
                ("pk", pk),
                ("cr", m.credit.encode().to_vec()),
            ]
        }
        MessageType::PrekeyReject | MessageType::ResumeReject => {
            vec![("echo", Reject::parse(bytes, ty).ok()?.echo.to_vec())]
        }
        MessageType::Reply => {
            let m = Reply::parse(bytes).ok()?;
            vec![
                ("sc", m.scid.as_bytes().to_vec()),
                ("ad", vec![aead_tag(m.aead)]),
                ("e", m.e.to_vec()),
                ("ct", m.ct.to_vec()),
                ("sealed", m.sealed.to_vec()),
            ]
        }
        MessageType::Finish => vec![("sealed", Finish::parse(bytes).ok()?.sealed.to_vec())],
        MessageType::ResumeHello => {
            let m = ResumeHello::parse(bytes).ok()?;
            vec![
                ("ver", vec![m.version]),
                ("dc", m.dcid.as_bytes().to_vec()),
                ("sc", m.scid.as_bytes().to_vec()),
                ("al", m.alpn.to_vec()),
                ("ad", vec![aead_tag(m.aead)]),
                ("tid", m.tid.to_vec()),
                ("e", m.e.to_vec()),
                ("binder", m.binder.to_vec()),
                ("cr", m.credit.encode().to_vec()),
            ]
        }
        MessageType::ResumeReply => {
            let m = ResumeReply::parse(bytes).ok()?;
            let mut t = [0u8; 81];
            let n = m.tickets.encode(&mut t).ok()?;
            vec![
                ("sc", m.scid.as_bytes().to_vec()),
                ("e", m.e.to_vec()),
                ("tids", t[..n].to_vec()),
                ("cr", m.credit.encode().to_vec()),
                ("conf", m.confirm.to_vec()),
            ]
        }
    })
}

pub fn classify(orig: &[u8], mutated: &[u8]) -> Class {
    let (Some(a), Some(b)) = (fields(orig), fields(mutated)) else {
        return Class::Malformed;
    };
    let changed: Vec<&'static str> = a.iter().zip(&b).filter(|(x, y)| x.1 != y.1).map(|(x, _)| x.0).collect();
    match changed.as_slice() {
        ["ad"] | [] => Class::Unmodelled,
        [f] => Class::Field(f),
        _ => Class::Unmodelled,
    }
}

/// The tampers of one message: the first and the last byte of each modelled field (a bit flipped), the message cut by
/// a byte and extended by one. A byte whose flip changes a length or several fields is left out.
pub fn tamper_cases(msg: &[u8]) -> Vec<(Vec<u8>, Class)> {
    // the bit to flip: bit 0, or bit 1 where that makes the byte invalid (the AEAD offer)
    let mut seen: Vec<(Class, (usize, u8), (usize, u8))> = Vec::new();
    for idx in 1..msg.len() {
        for mask in [1u8, 2] {
            let mut m = msg.to_vec();
            m[idx] ^= mask;
            let c = classify(msg, &m);
            if matches!(c, Class::Field(_)) {
                match seen.iter_mut().find(|s| s.0 == c) {
                    Some(s) => s.2 = (idx, mask),
                    None => seen.push((c.clone(), (idx, mask), (idx, mask))),
                }
            }
            if c != Class::Malformed {
                break;
            }
        }
    }
    let mut out = Vec::new();
    for (c, first, last) in seen {
        // a changed byte of a full prekey may break the key's own range check, which the model does not say: only
        // its last byte (the seed of the matrix) is flipped
        let picks = if c == Class::Field("pk") && msg[0] == 1 {
            vec![last]
        } else if first == last {
            vec![first]
        } else {
            vec![first, last]
        };
        for (idx, mask) in picks {
            let mut m = msg.to_vec();
            m[idx] ^= mask;
            out.push((m, c.clone()));
        }
    }
    out.push((msg[..msg.len() - 1].to_vec(), Class::Malformed));
    let mut ext = msg.to_vec();
    ext.push(0);
    out.push((ext, Class::Malformed));
    out
}

/// The message with its field `name` changed, as an input.
pub fn flip_field(msg: &[u8], name: &'static str) -> Inp {
    for (m, c) in tamper_cases(msg) {
        if c == Class::Field(name) {
            return Inp::Forged {
                base: msg.to_vec(),
                bytes: m,
                fld: name,
            };
        }
    }
    panic!("no tamper of field {name}");
}

/// Bytes that do not parse, as an input.
pub fn malformed(bytes: &[u8]) -> Inp {
    Inp::Malformed(bytes.to_vec())
}

/// The message types of a log.
pub fn kinds(log: &[Vec<u8>]) -> Vec<u8> {
    log.iter().map(|m| m[0]).collect()
}

/// Both sides derived the same keys.
pub fn agree(i: &Established, r: &Established) {
    assert_eq!(i.traffic.send, r.traffic.recv);
    assert_eq!(i.traffic.recv, r.traffic.send);
    assert_eq!(i.resume, r.resume);
    assert_eq!(i.cid_secret, r.cid_secret);
    assert_eq!(i.resumed, r.resumed);
    assert_eq!(i.alpn, r.alpn);
}
