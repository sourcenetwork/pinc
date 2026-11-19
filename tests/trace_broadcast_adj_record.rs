//! Trace generation for the adjacency record of the topic broadcast: the real parser and signature check of a hub
//! (`Topics::adj_probe`, behind the `trace` feature of `pinc-broadcast`) on records made by hand with eight real keys
//! (two of each identity algorithm) and then cut, extended and altered at every field, on the records real nodes of
//! each algorithm write through `Topics::set_adjacent` (captured from the frame they send to their hub), and on seeded
//! random records. Every key, every signature made, every parse and every captured record is one line of
//! `bcast/adj_record.ndjson` for the TLA+ trace check (`TraceBroadcastAdjRecord.tla`), which keeps an oracle of the
//! signatures made (crypto ideal) and checks what the hub's parser accepts and verifies.
//!
//! The test asserts the facts it relies on itself: an unchanged hand-made record parses and verifies, every cut and
//! every layout refusal is refused, every altered one parses and does not verify, and a record a node wrote verifies,
//! names its origin, and lists the distinct peers it was given, in order, without itself and at most `ADJ_MAX`. The
//! trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::too_many_arguments,
    unreachable_pub,
    clippy::many_single_char_names,
    clippy::struct_field_names
)]

#[path = "broadcast_common.rs"]
mod common;

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::rc::Rc;

use common::{Net, SEC, keypair, ty};
use pinc_broadcast::consts::ADJ_MAX;
use pinc_broadcast::{AdjProbe, Topics};
use pinc_crypto::{IdentityAlg, Keypair};
use pinc_membership::NodeId;
use pinc_tests::SplitMix64;

/// The algorithm tag of free key `k`.
const TAGS: [u8; 8] = [1, 2, 3, 4, 1, 2, 3, 4];

fn arr(b: &[u8]) -> String {
    let v: Vec<String> = b.iter().map(u8::to_string).collect();
    format!("[{}]", v.join(","))
}

fn arrs(v: &[[u8; 32]]) -> String {
    let s: Vec<String> = v.iter().map(|p| arr(p)).collect();
    format!("[{}]", s.join(","))
}

/// A key of the trace.
struct Key {
    key: Keypair,
    tag: u8,
    id: NodeId,
    /// The public key bytes (also for Ed25519).
    pk: Vec<u8>,
}

impl Key {
    fn new(key: Keypair) -> Self {
        let mut buf = vec![0u8; 4096];
        let n = key.public_key(&mut buf).unwrap();
        buf.truncate(n);
        Self {
            tag: key.alg().tag(),
            id: key.node_id().bytes,
            pk: buf,
            key,
        }
    }

    /// The key as a record carries it: nothing for Ed25519.
    fn header_pk(&self) -> &[u8] {
        if self.tag == 1 { &[] } else { &self.pk }
    }

    /// Where the fields of a record start after the origin, the tag and the key.
    fn fixed(&self) -> usize {
        33 + self.header_pk().len()
    }
}

/// A record's bytes up to its signature.
fn signed_of(k: &Key, origin: &NodeId, inc: u64, seq: u64, count: u16, peers: &[NodeId]) -> Vec<u8> {
    let mut b = origin.to_vec();
    b.push(k.tag);
    b.extend_from_slice(k.header_pk());
    b.extend_from_slice(&inc.to_be_bytes());
    b.extend_from_slice(&seq.to_be_bytes());
    b.extend_from_slice(&count.to_be_bytes());
    b.extend_from_slice(peers.as_flattened());
    b
}

struct World {
    out: String,
}

impl World {
    fn key_event(&mut self, idx: usize, k: &Key) {
        let _ = writeln!(
            self.out,
            r#"{{"t":"adj","op":"key","k":{idx},"alg":{},"id":{},"pk":{}}}"#,
            k.tag,
            arr(&k.id),
            arr(&k.pk)
        );
    }

    /// Sign `signed` with `k` (index `idx`), recorded; the signature.
    fn sign(&mut self, idx: usize, k: &Key, signed: &[u8]) -> Vec<u8> {
        let mut buf = vec![0u8; k.key.alg().signature_len()];
        let n = k.key.sign(&Topics::adj_digest(signed), &mut buf).unwrap();
        buf.truncate(n);
        let _ = writeln!(
            self.out,
            r#"{{"t":"adj","op":"sign","k":{idx},"signed":{},"sig":{}}}"#,
            arr(signed),
            arr(&buf)
        );
        buf
    }

    fn parse(&mut self, b: &[u8]) -> Option<AdjProbe> {
        let r = Topics::adj_probe(b);
        let mut line = format!(r#"{{"t":"adj","op":"parse","b":{}"#, arr(b));
        match &r {
            None => line.push_str(r#","none":true"#),
            Some(p) => {
                let _ = write!(
                    line,
                    r#","origin":{},"alg":{},"pk":{},"inc":{},"seq":{},"peers":{},"slen":{},"sig":{},"ver":{}"#,
                    arr(&p.origin),
                    p.alg,
                    arr(&p.pk),
                    arr(&p.inc.to_be_bytes()),
                    arr(&p.seq.to_be_bytes()),
                    arrs(&p.peers),
                    p.signed_len,
                    arr(&p.sig),
                    p.verified
                );
            }
        }
        line.push_str("}\n");
        self.out.push_str(&line);
        r
    }
}

/// The cut lengths of a record of `len` bytes.
fn cuts(len: usize) -> BTreeSet<usize> {
    if len < 200 {
        (0..len).collect()
    } else {
        (0..=60)
            .chain((0..len).filter(|c| c % 64 == 0))
            .chain(len - 8..len)
            .collect()
    }
}

/// Input 1 for free key `idx`.
fn hand_made(w: &mut World, keys: &[Key], idx: usize) {
    let k = &keys[idx];
    let other = &keys[(idx + 4) % 8];
    let (p1, p2) = ([0x10u8; 32], [0x20u8; 32]);
    for peers in [vec![], vec![p1], vec![p1, p2]] {
        let count = u16::try_from(peers.len()).unwrap();
        let signed = signed_of(k, &k.id, 1, 2, count, &peers);
        let sig = w.sign(idx, k, &signed);
        let rec = [signed.as_slice(), &sig].concat();
        let p = w.parse(&rec).unwrap();
        assert!(p.verified, "an unchanged record does not verify");
        assert_eq!(p.signed_len, signed.len());
        assert_eq!(
            (p.origin, p.alg, p.inc, p.seq, p.peers.clone()),
            (k.id, k.tag, 1, 2, peers.clone())
        );
        for cut in cuts(rec.len()) {
            assert!(w.parse(&rec[..cut]).is_none(), "a cut record parsed");
        }
        let mut longer = rec.clone();
        longer.push(0);
        assert!(w.parse(&longer).is_none());
        for t in [0u8, 5] {
            let mut m = rec.clone();
            m[32] = t;
            assert!(w.parse(&m).is_none());
        }
        let mut m = rec.clone();
        m[32] = k.tag % 4 + 1;
        w.parse(&m);
        let at = k.fixed() + 16;
        for delta in [1i32, -1] {
            let mut m = rec.clone();
            let count = u16::from_be_bytes([m[at], m[at + 1]]).wrapping_add_signed(delta as i16);
            m[at..at + 2].copy_from_slice(&count.to_be_bytes());
            assert!(w.parse(&m).is_none(), "a wrong count parsed");
        }
        // altered, still parsing, not verifying
        let mut m = rec.clone();
        *m.last_mut().unwrap() ^= 1;
        assert!(!w.parse(&m).unwrap().verified);
        let mut m = rec.clone();
        m[k.fixed() + 15] ^= 1;
        assert!(!w.parse(&m).unwrap().verified);
        if !peers.is_empty() {
            let mut m = rec.clone();
            m[k.fixed() + 18] ^= 1;
            assert!(!w.parse(&m).unwrap().verified);
        }
        let mut m = rec.clone();
        m[..32].copy_from_slice(&other.id);
        assert!(!w.parse(&m).unwrap().verified);
        if k.tag != 1 {
            let mut m = rec.clone();
            m[33..33 + k.pk.len()].copy_from_slice(&other.pk);
            assert!(!w.parse(&m).unwrap().verified);
        }
    }
    // layout refusals, signed anew
    for peers in [vec![p2, p1], vec![p1, p1], vec![k.id]] {
        let signed = signed_of(k, &k.id, 1, 2, u16::try_from(peers.len()).unwrap(), &peers);
        let sig = w.sign(idx, k, &signed);
        assert!(
            w.parse(&[signed.as_slice(), &sig].concat()).is_none(),
            "a layout refusal parsed"
        );
    }
    let signed = signed_of(k, &k.id, 1, 2, 1025, &[]);
    assert!(w.parse(&signed).is_none());
}

/// The record `member` (net index) sends its hub after `set_adjacent(given)`, as the frame's bytes after its header.
fn write(w: &mut World, net: &mut Net, member: usize, given: &[NodeId]) -> Vec<u8> {
    let frame = Rc::new(RefCell::new(Vec::new()));
    let f = frame.clone();
    net.filter = Some(Box::new(move |from, _, b: &mut Vec<u8>| {
        if from == member && b.get(4) == Some(&ty::ADJ) {
            f.borrow_mut().clone_from(b);
            return false;
        }
        true
    }));
    let now = net.now;
    let n = &mut net.nodes[member];
    n.h.tick(now);
    n.t.set_adjacent(&mut n.h, now, given).unwrap();
    net.pump();
    net.filter = None;
    let b = frame.borrow();
    assert!(!b.is_empty(), "no record was sent");
    let rest = b[6..].to_vec();
    let _ = writeln!(
        w.out,
        r#"{{"t":"adj","op":"write","k":{},"given":{},"b":{}}}"#,
        10 + member,
        arrs(given),
        arr(&rest)
    );
    rest
}

fn node_records(w: &mut World, net: &mut Net, rng: &mut SplitMix64) {
    let members = 1..=4usize;
    for i in members.clone() {
        let me = net.id(i);
        let mut others: Vec<NodeId> = members.clone().filter(|j| *j != i).map(|j| net.id(j)).collect();
        others.sort_unstable();
        let mut sets: Vec<(Vec<NodeId>, Vec<NodeId>)> = vec![(vec![], vec![])];
        sets.extend(others.iter().map(|o| (vec![*o], vec![*o])));
        sets.push((others.clone(), others.clone()));
        sets.push((vec![me, others[0], others[0]], vec![others[0]]));
        let mut desc = others.clone();
        desc.sort_unstable_by(|a, b| b.cmp(a));
        sets.push((desc, others.clone()));
        if i == 1 {
            let mut ids = BTreeSet::new();
            while ids.len() < 1100 {
                let mut id = [0u8; 32];
                rng.fill(&mut id);
                ids.insert(id);
            }
            let given: Vec<NodeId> = ids.iter().copied().collect();
            let want: Vec<NodeId> = given.iter().copied().take(ADJ_MAX).collect();
            sets.push((given, want));
        }
        for (given, want) in sets {
            let rest = write(w, net, i, &given);
            let p = w.parse(&rest).unwrap();
            assert!(p.verified, "a record a node wrote does not verify");
            assert_eq!(p.origin, me);
            assert!(p.peers.windows(2).all(|x| x[0] < x[1]), "peers are not ascending");
            assert!(!p.peers.contains(&me));
            assert_eq!(p.peers, want);
        }
    }
}

fn seeded(w: &mut World, keys: &[Key], rng: &mut SplitMix64) {
    for _ in 0..400 {
        let idx = usize::try_from(rng.next_u64() % 8).unwrap();
        let k = &keys[idx];
        let n = usize::try_from(rng.next_u64() % 4).unwrap();
        let mut peers: Vec<NodeId> = (0..n)
            .map(|_| {
                let mut p = [0u8; 32];
                rng.fill(&mut p);
                p
            })
            .collect();
        peers.sort_unstable();
        let signed = signed_of(
            k,
            &k.id,
            rng.next_u64() % 4,
            rng.next_u64() % 4,
            u16::try_from(n).unwrap(),
            &peers,
        );
        let sig = w.sign(idx, k, &signed);
        let mut rec = [signed.as_slice(), &sig].concat();
        for _ in 0..rng.next_u64() % 3 {
            match rng.next_u64() % 4 {
                0 => {
                    let at = usize::try_from(rng.next_u64()).unwrap() % rec.len();
                    rec[at] = rng.next_u64() as u8;
                }
                1 => {
                    let at = usize::try_from(rng.next_u64()).unwrap() % rec.len();
                    rec.truncate(at.max(1));
                }
                2 => rec.push(rng.next_u64() as u8),
                _ => {
                    let first = k.fixed() + 18;
                    if peers.len() >= 2 && rec.len() >= first + 64 {
                        let (a, b) = rec.split_at_mut(first + 32);
                        a[first..].swap_with_slice(&mut b[..32]);
                    }
                }
            }
        }
        w.parse(&rec);
    }
}

#[test]
fn adj_record_trace() {
    let mut w = World { out: String::new() };
    let mut net = Net::with_algs(
        &[
            IdentityAlg::Ed25519,
            IdentityAlg::Ed25519,
            IdentityAlg::EcdsaP256,
            IdentityAlg::MlDsa65,
            IdentityAlg::Hybrid,
        ],
        1,
        SEC,
    );
    for i in 1..=4 {
        net.attach(i);
    }
    let keys: Vec<Key> = TAGS
        .iter()
        .enumerate()
        .map(|(k, t)| {
            let alg = IdentityAlg::from_tag(*t).unwrap();
            Key::new(Keypair::from_seed(alg, &vec![u8::try_from(k).unwrap() + 1; alg.seed_len()]).unwrap())
        })
        .collect();
    for (i, k) in keys.iter().enumerate() {
        w.key_event(i, k);
    }
    for i in 1..=4usize {
        let k = Key::new(keypair(net.algs[i], u8::try_from(i).unwrap() + 1));
        assert_eq!(k.id, net.id(i), "a node's key is not the one of the network");
        w.key_event(10 + i, &k);
    }
    for idx in 0..8 {
        hand_made(&mut w, &keys, idx);
    }
    let mut rng = SplitMix64::traced(0x5747_0004);
    node_records(&mut w, &mut net, &mut rng);
    seeded(&mut w, &keys, &mut rng);
    assert!(w.out.lines().count() > 2000);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = std::path::Path::new(&dir).join("bcast");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("adj_record.ndjson"), &w.out).unwrap();
    }
}
