//! Trace generation for the signing and verification of a version 2 message of the topic broadcast: the real
//! `auth2::{sign2, verify2}` of `pinc-broadcast` with eight real keys (two of each identity algorithm), signing field
//! sets at their edges and refusals, and verifying every signature made unchanged and with one field, the key or the
//! signature altered, then seeded random rounds. Every call is one line of `bcast/auth2.ndjson` for the TLA+ trace
//! check (`TraceBroadcastAuth2.tla`), which keeps an oracle of the signatures made (crypto ideal) and checks that a
//! verification returns an id only for a signature made over exactly that statement by the origin's key. Origins,
//! public keys and body hashes appear as small ids (`oid`, `pki`, `bid`), one per distinct byte string.
//!
//! The test asserts the facts it relies on itself: each signing is accepted or refused as the inputs say, an
//! unchanged head verifies to the id it was signed with exactly when its origin is the signer's own node id, every
//! altered head is refused, and equal fields give equal ids. The trace is written to the directory in
//! `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::type_complexity,
    unreachable_pub,
    clippy::assigning_clones,
    clippy::cast_sign_loss,
    clippy::manual_is_multiple_of,
    clippy::many_single_char_names,
    clippy::single_match_else
)]

use std::collections::HashMap;
use std::fmt::Write as _;

use pinc_broadcast::auth2::{sign2, verify2};
use pinc_broadcast::statement::{ContentId, Fields};
use pinc_broadcast::wire2::Head2;
use pinc_crypto::{IdentityAlg, Keypair};
use pinc_tests::SplitMix64;
use pinc_wire::hlc::Hlc;

/// The algorithm tag of key `k`; the trace spec's `KeyAlg`.
const TAGS: [u8; 8] = [1, 2, 3, 4, 1, 2, 3, 4];

fn arr(b: &[u8]) -> String {
    let v: Vec<String> = b.iter().map(u8::to_string).collect();
    format!("[{}]", v.join(","))
}

/// A set of signed fields, owned.
#[derive(Clone, PartialEq, Eq, Hash)]
struct F {
    alg: u8,
    origin: [u8; 32],
    inc: u64,
    seq: u64,
    topic: Vec<u8>,
    wall: u64,
    ctr: u32,
    flags: u8,
    parents: Vec<ContentId>,
    body: [u8; 32],
}

impl F {
    fn with(&self, f: impl FnOnce(&mut Self)) -> Self {
        let mut c = self.clone();
        f(&mut c);
        c
    }
}

/// A head and what it is verified against, owned.
#[derive(Clone)]
struct H {
    alg: u8,
    flags: u8,
    origin: [u8; 32],
    inc: u64,
    seq: u64,
    wall: u64,
    ctr: u32,
    parents: Vec<ContentId>,
    pk: Vec<u8>,
    sig: Vec<u8>,
    topic: Vec<u8>,
    body: Vec<u8>,
}

impl H {
    fn with(&self, f: impl FnOnce(&mut Self)) -> Self {
        let mut c = self.clone();
        f(&mut c);
        c
    }
}

struct World {
    keys: Vec<Keypair>,
    ids: Vec<[u8; 32]>,
    pks: Vec<Vec<u8>>,
    oid: HashMap<[u8; 32], u32>,
    pki: HashMap<Vec<u8>, i32>,
    bid: HashMap<[u8; 32], u32>,
    ids_made: HashMap<(usize, F), ContentId>,
    out: String,
}

impl World {
    fn new() -> Self {
        let keys: Vec<Keypair> = TAGS
            .iter()
            .enumerate()
            .map(|(k, t)| {
                let alg = IdentityAlg::from_tag(*t).unwrap();
                Keypair::from_seed(alg, &vec![u8::try_from(k).unwrap() + 1; alg.seed_len()]).unwrap()
            })
            .collect();
        let ids: Vec<[u8; 32]> = keys.iter().map(|k| k.node_id().bytes).collect();
        let pks: Vec<Vec<u8>> = keys
            .iter()
            .map(|k| {
                let mut buf = vec![0u8; 4096];
                let n = k.public_key(&mut buf).unwrap();
                buf.truncate(n);
                buf
            })
            .collect();
        let oid = ids
            .iter()
            .enumerate()
            .map(|(k, i)| (*i, u32::try_from(k).unwrap()))
            .collect();
        let pki = pks
            .iter()
            .enumerate()
            .map(|(k, p)| (p.clone(), i32::try_from(k).unwrap()))
            .collect();
        Self {
            keys,
            ids,
            pks,
            oid,
            pki,
            bid: HashMap::new(),
            ids_made: HashMap::new(),
            out: String::new(),
        }
    }

    fn oid(&mut self, origin: &[u8; 32]) -> u32 {
        let next = 8 + u32::try_from(self.oid.len() - 8).unwrap();
        *self.oid.entry(*origin).or_insert(next)
    }

    fn pki(&mut self, pk: &[u8]) -> i32 {
        if pk.is_empty() {
            return -1;
        }
        let next = 100 + i32::try_from(self.pki.len() - 8).unwrap();
        *self.pki.entry(pk.to_vec()).or_insert(next)
    }

    fn bid(&mut self, hash: &[u8; 32]) -> u32 {
        let next = u32::try_from(self.bid.len()).unwrap();
        *self.bid.entry(*hash).or_insert(next)
    }

    #[allow(clippy::too_many_arguments)]
    fn common(
        &mut self,
        alg: u8,
        origin: &[u8; 32],
        inc: u64,
        seq: u64,
        topic: &[u8],
        wall: u64,
        ctr: u32,
        flags: u8,
        parents: &[ContentId],
        body: &[u8; 32],
    ) -> String {
        let (oid, bid) = (self.oid(origin), self.bid(body));
        let parents: Vec<String> = parents.iter().map(|p| arr(p)).collect();
        format!(
            r#""alg":{alg},"oid":{oid},"inc":{},"seq":{},"topic":{},"wall":{},"ctr":{},"flags":{flags},"parents":[{}],"bid":{bid}"#,
            arr(&inc.to_be_bytes()),
            arr(&seq.to_be_bytes()),
            arr(topic),
            arr(&wall.to_be_bytes()),
            arr(&ctr.to_be_bytes()),
            parents.join(","),
        )
    }

    /// `sign2` with key `k` and a signature buffer of `cap` bytes, recorded.
    fn sign(&mut self, k: usize, f: &F, cap: usize) -> Option<(Vec<u8>, ContentId)> {
        let alg = IdentityAlg::from_tag(f.alg).unwrap();
        let fields = Fields {
            origin_alg: alg,
            origin: &f.origin,
            incarnation: f.inc,
            seq: f.seq,
            topic: &f.topic,
            time: Hlc::new(f.wall, f.ctr),
            flags: f.flags,
            parents: &f.parents,
            body: &f.body,
        };
        let mut out = vec![0u8; cap];
        let r = sign2(&self.keys[k], &fields, &mut out);
        let common = self.common(
            f.alg, &f.origin, f.inc, f.seq, &f.topic, f.wall, f.ctr, f.flags, &f.parents, &f.body,
        );
        let mut line = format!(r#"{{"t":"a2","op":"sign","k":{k},{common},"cap":{cap}"#);
        let res = match r {
            Some((n, id)) => {
                let _ = write!(line, r#","sig":{},"cid":{}"#, arr(&out[..n]), arr(&id));
                if let Some(prev) = self.ids_made.insert((k, f.clone()), id) {
                    assert_eq!(prev, id, "equal fields gave two ids");
                }
                Some((out[..n].to_vec(), id))
            }
            None => {
                line.push_str(r#","none":true"#);
                None
            }
        };
        line.push_str("}\n");
        self.out.push_str(&line);
        res
    }

    /// `verify2` of `h`, recorded.
    fn verify(&mut self, h: &H) -> Option<ContentId> {
        let alg = IdentityAlg::from_tag(h.alg).unwrap();
        let head = Head2 {
            alg,
            flags: h.flags,
            origin: &h.origin,
            incarnation: h.inc,
            seq: h.seq,
            ts: Hlc::new(h.wall, h.ctr),
            parents: &h.parents,
            pk: &h.pk,
            sig: &h.sig,
        };
        let r = verify2(&head, &h.topic, &h.body);
        let hash = *blake3::hash(&h.body).as_bytes();
        let common = self.common(
            h.alg, &h.origin, h.inc, h.seq, &h.topic, h.wall, h.ctr, h.flags, &h.parents, &hash,
        );
        let pki = self.pki(&h.pk);
        let mut line = format!(r#"{{"t":"a2","op":"verify",{common},"pki":{pki},"sig":{}"#, arr(&h.sig));
        match r {
            Some(id) => {
                let _ = write!(line, r#","id":{}"#, arr(&id));
            }
            None => line.push_str(r#","none":true"#),
        }
        line.push_str("}\n");
        self.out.push_str(&line);
        r
    }

    /// The base fields of key `k`.
    fn base(&self, k: usize) -> F {
        F {
            alg: TAGS[k],
            origin: self.ids[k],
            inc: 1,
            seq: 2,
            topic: b"t".to_vec(),
            wall: 3,
            ctr: 4,
            flags: 0,
            parents: Vec::new(),
            body: *blake3::hash(b"body").as_bytes(),
        }
    }

    /// The head of `f` signed by key `k` with `sig`, to be checked against `body`.
    fn head(&self, k: usize, f: &F, sig: &[u8], body: &[u8]) -> H {
        H {
            alg: f.alg,
            flags: f.flags,
            origin: f.origin,
            inc: f.inc,
            seq: f.seq,
            wall: f.wall,
            ctr: f.ctr,
            parents: f.parents.clone(),
            pk: if f.alg == 1 { Vec::new() } else { self.pks[k].clone() },
            sig: sig.to_vec(),
            topic: f.topic.clone(),
            body: body.to_vec(),
        }
    }

    /// The altered heads of input 2 for the head `h` of key `k`: one change each.
    fn altered(&self, k: usize, h: &H, other_sig: Option<&[u8]>) -> Vec<H> {
        let other = (k + 4) % 8;
        let mut v = vec![
            h.with(|c| c.alg = c.alg % 4 + 1),
            h.with(|c| c.origin = self.ids[other]),
            h.with(|c| c.origin = [0xee; 32]),
            h.with(|c| c.inc += 1),
            h.with(|c| c.seq += 1),
            h.with(|c| c.topic = b"u".to_vec()),
            h.with(|c| c.wall += 1),
            h.with(|c| c.ctr += 1),
            h.with(|c| c.flags ^= 1),
            h.with(|c| {
                if c.parents.is_empty() {
                    c.parents.push([0x11; 32]);
                } else {
                    c.parents.pop();
                }
            }),
            h.with(|c| c.body = b"bodz".to_vec()),
        ];
        if h.alg != 1 {
            v.push(h.with(|c| c.pk = self.pks[other].clone()));
            v.push(h.with(|c| c.pk = vec![0x5a; c.pk.len()]));
        }
        if let Some(s) = other_sig {
            v.push(h.with(|c| c.sig = s.to_vec()));
        }
        v.push(h.with(|c| {
            if let Some(b) = c.sig.last_mut() {
                *b ^= 1;
            }
        }));
        v
    }
}

fn signing(w: &mut World) -> Vec<(usize, F, Vec<u8>, ContentId)> {
    let mut made = Vec::new();
    for k in 0..8 {
        let siglen = w.keys[k].alg().signature_len();
        let b = w.base(k);
        let other = (k + 4) % 8;
        let next_alg = TAGS[(k + 1) % 8];
        let cases: Vec<(F, usize, bool)> = vec![
            (b.clone(), siglen, true),
            (b.with(|c| c.flags = 1), siglen, true),
            (
                b.with(|c| c.parents = (1..=8u8).map(|x| [x; 32]).collect()),
                siglen,
                true,
            ),
            (b.with(|c| c.topic = (0..255).map(|i| i as u8).collect()), siglen, true),
            (b.with(|c| c.origin = w.ids[other]), siglen, true),
            (b.with(|c| c.origin = [0xee; 32]), siglen, true),
            (b.with(|c| c.alg = next_alg), siglen, false),
            (b.with(|c| c.topic = vec![0; 256]), siglen, false),
            (
                b.with(|c| c.parents = (1..=9u8).map(|x| [x; 32]).collect()),
                siglen,
                false,
            ),
            (b.with(|c| c.parents = vec![[2; 32], [1; 32]]), siglen, false),
            (b.with(|c| c.flags = 2), siglen, false),
            (b.clone(), siglen - 1, false),
            (b.clone(), siglen + 7, true),
        ];
        for (f, cap, succeeds) in cases {
            let r = w.sign(k, &f, cap);
            assert_eq!(r.is_some(), succeeds, "key {k}: signing is not as the inputs say");
            if let Some((sig, id)) = r {
                made.push((k, f, sig, id));
            }
        }
    }
    made
}

fn verifying(w: &mut World, made: &[(usize, F, Vec<u8>, ContentId)]) {
    for (i, (k, f, sig, id)) in made.iter().enumerate() {
        let h = w.head(*k, f, sig, b"body");
        let own = f.origin == w.ids[*k];
        let r = w.verify(&h);
        assert_eq!(
            r,
            own.then_some(*id),
            "an unchanged head: its origin is the signer's own id: {own}"
        );
        let other_sig = made
            .iter()
            .cycle()
            .skip(i + 1)
            .take(made.len())
            .find(|(_, _, s, _)| s.len() == sig.len() && s != sig)
            .map(|(_, _, s, _)| s.clone());
        for alt in w.altered(*k, &h, other_sig.as_deref()) {
            assert_eq!(w.verify(&alt), None, "an altered head verified");
        }
    }
}

fn seeded(w: &mut World) {
    let mut rng = SplitMix64::traced(0x5747_0003);
    let bodies: [&[u8]; 3] = [b"body", b"bodz", b""];
    for _ in 0..300 {
        let k = usize::try_from(rng.next_u64() % 8).unwrap();
        let mut f = w.base(k);
        let len = usize::try_from(rng.next_u64() % 8).unwrap();
        f.topic = (0..len).map(|_| rng.next_u64() as u8 % 4).collect();
        f.flags = u8::try_from(rng.next_u64() % 3).unwrap();
        let n = usize::try_from(rng.next_u64() % 3).unwrap();
        f.parents = (0..n)
            .map(|_| {
                let mut p = [0u8; 32];
                p[0] = u8::try_from(rng.next_u64() % 4).unwrap();
                p
            })
            .collect();
        if rng.next_u64() % 4 < 3 {
            f.parents.sort_unstable();
        }
        f.inc = rng.next_u64() % 4;
        f.seq = rng.next_u64() % 4;
        f.wall = rng.next_u64() % 4;
        f.ctr = u32::try_from(rng.next_u64() % 4).unwrap();
        let body = bodies[usize::try_from(rng.next_u64() % 3).unwrap()];
        f.body = *blake3::hash(body).as_bytes();
        let siglen = w.keys[k].alg().signature_len();
        let cap = if rng.next_u64() % 10 < 9 { siglen } else { siglen - 1 };
        let Some((sig, _)) = w.sign(k, &f, cap) else { continue };
        let h = w.head(k, &f, &sig, body);
        if rng.next_u64() % 4 == 0 {
            w.verify(&h);
        } else {
            let alts = w.altered(k, &h, None);
            let pick = usize::try_from(rng.next_u64()).unwrap() % alts.len();
            w.verify(&alts[pick]);
        }
    }
}

#[test]
fn auth2_trace() {
    let mut w = World::new();
    let made = signing(&mut w);
    verifying(&mut w, &made);
    seeded(&mut w);
    assert!(w.out.lines().count() > 800);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = std::path::Path::new(&dir).join("bcast");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("auth2.ndjson"), &w.out).unwrap();
    }
}
