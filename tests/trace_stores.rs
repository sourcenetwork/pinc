//! Trace generation for the ticket stores and the prekey cache: real runs of `ClientTickets`, `ServerTickets` and
//! `PrekeyCache` through the public API, recorded as ndjson for the TLA+ trace check (`TraceStores.tla`) and the Lean
//! replay (`Vinc.TraceStores`).
//!
//! Every run drives one store with seeded random operations over a small world: seven peers (four identity
//! algorithms, two of them with the same node bytes), two ALPNs, six ticket ids, lifetimes of 0 and 1 seconds and
//! times around 0 and 10^9 ns, so that tickets expire at the boundary. `ClientTickets` is driven through
//! `accept_batch`, `accept_bytes` (also with malformed bytes), `take`, `export` (also with a buffer that is too
//! small) and `restore` (a fresh export, an old export, and every kind of malformed state). A ticket's fields are
//! not readable through the API, so after every operation the whole store is read back with `export` (the
//! `snap` field: every ticket, oldest first) and the ticket `take` returned is identified as the one that left the
//! store. The pre-shared key of an accepted ticket is read from an export of a one-slot store that accepted the
//! same ticket. `PrekeyCache` is driven through `get` and `insert`. `ServerTickets` is driven through `issue_batch`
//! with a random generator whose draws are known (the same seed gives the same draws, so a later call collides with
//! the ids already stored): the recorded draws are the first 32 of the seed, the most `issue_batch` can consume.
//!
//! An id stands for one distinct byte string (`idef` lines define them for the Lean replay). Every scenario is
//! asserted here, so the test is meaningful without the proof tools. The trace is written to `stores.ndjson` in the
//! directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
//!
//! What is not observable through the public API: the slot an issued ticket lands in (its eviction order), and
//! whether a particular ticket is still in a `ServerTickets` store; the server store is checked here for the batch
//! it issues, its length, the failure on collisions and the draws consumed, and its eviction order is proved in Lean
//! and model checked in TLA+ (`Tickets.tla`).
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::needless_pass_by_value,
    clippy::type_complexity,
    unreachable_pub
)]

use std::collections::HashMap;
use std::fmt::Write as _;

use vinc_crypto::provider::KEM_ENCAPS_KEY_LEN;
use vinc_crypto::{Aead, Drbg, IdentityAlg, NodeId, Secret, Software};
use vinc_security::tickets::{ID_ATTEMPTS, MAX_EXPORT_ENTRY_LEN};
use vinc_security::{
    Alpn, ClientTickets, CreditRecord, Env, Established, Failure, PrekeyCache, ServerTickets, TicketBatch, TicketEntry,
    Traffic,
};
use vinc_tests::SplitMix64;

const NS: u64 = 1_000_000_000;
/// The times of the world: a ticket of lifetime 1 s accepted at 0 expires after 10^9.
const NOWS: [u64; 6] = [0, 1, 2, NS, NS + 1, NS + 2];
const ALPNS: [&[u8]; 2] = [b"vinc/1", b"vinc/2"];
const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

fn hex(b: &[u8]) -> String {
    let mut s = String::with_capacity(b.len() * 2);
    for x in b {
        write!(s, "{x:02x}").unwrap();
    }
    s
}

/// Dense ids for byte strings, one id per (kind, algorithm, bytes), with the `idef` line that defines each.
#[derive(Default)]
struct Ids {
    map: HashMap<(char, u8, Vec<u8>), u32>,
    lines: Vec<String>,
}

impl Ids {
    fn id(&mut self, kind: char, alg: u8, bytes: &[u8]) -> u32 {
        let next = u32::try_from(self.map.len()).unwrap() + 1;
        let key = (kind, alg, bytes.to_vec());
        if let Some(id) = self.map.get(&key) {
            return *id;
        }
        self.map.insert(key, next);
        self.lines.push(format!(
            r#"{{"t":"idef","k":"{kind}","id":{next},"alg":{alg},"b":"{}"}}"#,
            hex(bytes)
        ));
        next
    }
}

/// One exported ticket, read back from the bytes `export` wrote.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Ent {
    alg: u8,
    node: [u8; 32],
    alpn: Vec<u8>,
    tid: [u8; 16],
    psk: [u8; 32],
    aead: u8,
    exp: u64,
    credit: [u8; 6],
}

impl Ent {
    fn json(&self, ids: &mut Ids, lf: u32) -> String {
        let p = ids.id('p', self.alg, &self.node);
        let a = ids.id('a', 0, &self.alpn);
        let t = ids.id('t', 0, &self.tid);
        let s = ids.id('s', 0, &self.psk);
        let c = ids.id('c', 0, &self.credit);
        format!(
            r#"{{"p":{p},"a":{a},"t":{t},"s":{s},"ae":{},"x":{},"cr":{},"lf":{lf}}}"#,
            self.aead, self.exp, c
        )
    }
}

/// The empty ticket, for the field of an event that has none.
const NO_ENT: &str = r#"{"p":0,"a":0,"t":0,"s":0,"ae":0,"x":0,"cr":0,"lf":0}"#;

fn ents_json(es: &[Ent], ids: &mut Ids) -> String {
    let parts: Vec<String> = es.iter().map(|e| e.json(ids, 0)).collect();
    format!("[{}]", parts.join(","))
}

/// What a state of exported bytes holds, parsed independently of the code under test: the version, the entries before
/// the first one the reader rejects, whether such an entry (or a short count) was met, and whether bytes trail.
struct Cls {
    ver: u8,
    ents: Vec<Ent>,
    bad: bool,
    trail: bool,
}

impl Cls {
    fn well_formed(&self) -> bool {
        self.ver == 1 && !self.bad && !self.trail
    }
}

fn classify(b: &[u8]) -> Cls {
    let mut c = Cls {
        ver: b.first().copied().unwrap_or(0),
        ents: vec![],
        bad: false,
        trail: false,
    };
    let (Some(_), Some(count)) = (b.first(), b.get(1)) else {
        c.bad = true;
        return c;
    };
    let mut at = 2usize;
    for _ in 0..*count {
        let Some(e) = entry_at(b, &mut at) else {
            c.bad = true;
            return c;
        };
        c.ents.push(e);
    }
    c.trail = at < b.len();
    c
}

fn entry_at(b: &[u8], at: &mut usize) -> Option<Ent> {
    let mut take = |n: usize| -> Option<&[u8]> {
        let s = b.get(*at..*at + n)?;
        *at += n;
        Some(s)
    };
    let alg = take(1)?[0];
    if !(1..=4).contains(&alg) {
        return None;
    }
    let node: [u8; 32] = take(32)?.try_into().ok()?;
    let alen = usize::from(take(1)?[0]);
    let alpn = take(alen)?.to_vec();
    if !(1..=32).contains(&alen) {
        return None;
    }
    let tid: [u8; 16] = take(16)?.try_into().ok()?;
    let psk: [u8; 32] = take(32)?.try_into().ok()?;
    let aead = take(1)?[0];
    if aead != 1 && aead != 2 {
        return None;
    }
    let exp = u64::from_be_bytes(take(8)?.try_into().ok()?);
    let credit: [u8; 6] = take(6)?.try_into().ok()?;
    Some(Ent {
        alg,
        node,
        alpn,
        tid,
        psk,
        aead,
        exp,
        credit,
    })
}

/// Every ticket in the store, oldest first, with its secrets: the state the model must reproduce.
fn snapshot<const N: usize>(s: &ClientTickets<N>) -> Vec<Ent> {
    let mut buf = vec![0u8; 2 + N * MAX_EXPORT_ENTRY_LEN];
    let n = s.export(0, N, &mut buf).unwrap();
    let c = classify(&buf[..n]);
    assert!(c.well_formed());
    c.ents
}

fn peer(k: usize) -> NodeId {
    NodeId {
        alg: ALGS[k % 4],
        bytes: [u8::try_from(k / 2 + 1).unwrap(); 32],
    }
}

fn session(peer: NodeId, alpn: &[u8], aead: Aead, resume: u8, peer_credit: CreditRecord) -> Established {
    Established {
        peer,
        alpn: Alpn::new(alpn).unwrap(),
        traffic: Traffic {
            aead,
            send: Secret::new([1; 32]),
            recv: Secret::new([2; 32]),
        },
        resume: Secret::new([resume; 32]),
        tickets: TicketBatch::new(),
        resumed: false,
        peer_credit,
        local_credit: CreditRecord::NONE,
        remembered_credit: CreditRecord::NONE,
        cid_secret: Secret::new([3; 32]),
    }
}

fn expiry(now: u64, life: u32) -> u64 {
    now.saturating_add(u64::from(life).saturating_mul(NS))
}

/// Counts of what the runs exercised, asserted at the end.
#[derive(Default)]
struct Seen {
    takes_hit: u32,
    takes_miss: u32,
    takes_expired_dropped: u32,
    takes_wrong_alpn: u32,
    replaced_same_peer: u32,
    evicted_full: u32,
    exports: u32,
    exports_small: u32,
    restores_ok: u32,
    restores_bad: [u32; 6],
    restores_with_expired: u32,
    bad_batches: u32,
    cache_hits: u32,
    cache_misses: u32,
    cache_evictions: u32,
    cache_refresh: u32,
    issue_collisions: u32,
    issue_failures: u32,
    issue_partial_collisions: u32,
    issue_evicting: u32,
}

#[allow(clippy::too_many_arguments)]
fn client_run<const N: usize>(run: u32, ops: usize, seed: u64, ids: &mut Ids, out: &mut Vec<String>, seen: &mut Seen) {
    let mut rng = SplitMix64::traced(seed);
    let mut store = ClientTickets::<N>::new();
    out.push(format!(r#"{{"t":"cnew","run":{run},"n":{N}}}"#));
    let mut serial: u16 = 0;
    let mut old_blobs: Vec<Vec<u8>> = vec![];
    let npeers = if N >= 5 { 7 } else { 5 };
    let pick = |rng: &mut SplitMix64, n: usize| usize::try_from(rng.next_u64() % n as u64).unwrap();
    for _ in 0..ops {
        let now = NOWS[pick(&mut rng, NOWS.len())];
        let before = snapshot(&store);
        match pick(&mut rng, 10) {
            0..=3 => {
                // accept_batch or accept_bytes of a batch of one session
                let k = pick(&mut rng, npeers);
                let alpn = ALPNS[pick(&mut rng, 2)];
                serial += 1;
                let credit = CreditRecord {
                    window_units: serial,
                    max_streams: u16::try_from(pick(&mut rng, 2)).unwrap(),
                    max_datagram: 0,
                };
                let aead = if pick(&mut rng, 2) == 0 {
                    Aead::ChaCha20Poly1305
                } else {
                    Aead::Aes128Gcm
                };
                let sess = session(
                    peer(k),
                    alpn,
                    aead,
                    u8::try_from(1 + pick(&mut rng, 3)).unwrap(),
                    credit,
                );
                let mut batch = TicketBatch::new();
                let mut lives = vec![];
                for _ in 0..pick(&mut rng, 5) {
                    let life = u32::try_from(pick(&mut rng, 2)).unwrap();
                    let tid = [u8::try_from(1 + pick(&mut rng, 6)).unwrap(); 16];
                    assert!(batch.push(TicketEntry { tid, lifetime_s: life }));
                    lives.push(life);
                }
                let via_bytes = pick(&mut rng, 3) == 0;
                if via_bytes {
                    let mut bytes = [0u8; 81];
                    let n = batch.encode(&mut bytes).unwrap();
                    store.accept_bytes(&sess, &bytes[..n], now).unwrap();
                } else {
                    store.accept_batch(&sess, &batch, now);
                }
                // the secrets of the batch, read from a one-slot store that accepted each ticket
                let mut es = vec![];
                for (e, life) in batch.entries().iter().zip(&lives) {
                    let mut one = TicketBatch::new();
                    one.push(*e);
                    let mut s1 = ClientTickets::<1>::new();
                    s1.accept_batch(&sess, &one, now);
                    let ent = snapshot(&s1).remove(0);
                    assert_eq!(ent.exp, expiry(now, *life));
                    es.push(ent.json(ids, *life));
                }
                let snap = snapshot(&store);
                if N > 0 && !batch.entries().is_empty() {
                    let last = &snap
                        .iter()
                        .find(|s| s.node == sess.peer.bytes && s.alg == sess.peer.alg.tag())
                        .expect("a store with a slot keeps the last ticket of the batch");
                    let want = batch.entries().last().unwrap();
                    assert_eq!(last.tid, want.tid);
                    assert_eq!(last.exp, expiry(now, want.lifetime_s));
                    assert_eq!(
                        snap.iter()
                            .filter(|s| s.node == sess.peer.bytes && s.alg == sess.peer.alg.tag())
                            .count(),
                        1
                    );
                    if before
                        .iter()
                        .any(|s| s.node == sess.peer.bytes && s.alg == sess.peer.alg.tag())
                    {
                        seen.replaced_same_peer += 1;
                    } else if before.len() == N {
                        seen.evicted_full += 1;
                    }
                }
                assert_eq!(store.len(), snap.len());
                assert!(store.len() <= N);
                out.push(format!(
                    r#"{{"t":"cacc","run":{run},"now":{now},"b":[{}],"snap":{},"len":{},"via":"{}"}}"#,
                    es.join(","),
                    ents_json(&snap, ids),
                    store.len(),
                    if via_bytes { "bytes" } else { "batch" }
                ));
            }
            4 => {
                // accept_bytes of bytes that are not exactly one batch: nothing is stored
                let sess = session(peer(0), ALPNS[0], Aead::ChaCha20Poly1305, 1, CreditRecord::NONE);
                let mut batch = TicketBatch::new();
                batch.push(TicketEntry {
                    tid: [9; 16],
                    lifetime_s: 1,
                });
                let mut bytes = [0u8; 82];
                let n = batch.encode(&mut bytes).unwrap();
                let mut bad = bytes[..n].to_vec();
                match pick(&mut rng, 3) {
                    0 => bad.push(0),
                    1 => {
                        bad.pop();
                    }
                    _ => bad[0] = 5,
                }
                assert!(store.accept_bytes(&sess, &bad, now).is_err());
                let snap = snapshot(&store);
                assert_eq!(snap, before);
                seen.bad_batches += 1;
                out.push(format!(
                    r#"{{"t":"cbad","run":{run},"snap":{},"len":{}}}"#,
                    ents_json(&snap, ids),
                    store.len()
                ));
            }
            5..=6 => {
                // take
                let k = pick(&mut rng, npeers);
                let want = peer(k);
                let alpn = ALPNS[pick(&mut rng, 2)];
                let got = store.take(&want, alpn, now);
                let after = snapshot(&store);
                let removed: Vec<&Ent> = before.iter().filter(|e| !after.contains(e)).collect();
                assert!(after.iter().all(|e| before.contains(e)));
                assert!(
                    after.iter().all(|e| e.exp >= now),
                    "an expired ticket is left in the store"
                );
                seen.takes_expired_dropped += u32::try_from(removed.iter().filter(|e| e.exp < now).count()).unwrap();
                let me = |e: &Ent| e.node == want.bytes && e.alg == want.alg.tag();
                let ent_json = if let Some(t) = got {
                    let hit: Vec<&&Ent> = removed.iter().filter(|e| me(e) && e.exp >= now).collect();
                    assert_eq!(hit.len(), 1);
                    let e = hit[0];
                    assert_eq!(e.alpn, alpn);
                    assert_eq!(t.peer(), &want);
                    assert_eq!(t.expiry(), e.exp);
                    assert_eq!(t.peer_credit().encode(), e.credit);
                    seen.takes_hit += 1;
                    // a ticket taken is not found again
                    assert!(store.take(&want, alpn, now).is_none());
                    let again = snapshot(&store);
                    assert_eq!(again, after);
                    e.json(ids, 0)
                } else {
                    assert!(
                        removed.iter().all(|e| e.exp < now),
                        "a ticket left the store without being returned"
                    );
                    let live_for_peer = before.iter().find(|e| me(e) && e.exp >= now);
                    if let Some(e) = live_for_peer {
                        assert_ne!(e.alpn, alpn);
                        assert!(after.contains(e));
                        seen.takes_wrong_alpn += 1;
                    }
                    seen.takes_miss += 1;
                    NO_ENT.to_string()
                };
                let pid = ids.id('p', want.alg.tag(), &want.bytes);
                let aid = ids.id('a', 0, alpn);
                out.push(format!(
                    r#"{{"t":"ctake","run":{run},"now":{now},"p":{pid},"a":{aid},"got":{},"e":{ent_json},"snap":{},"len":{}}}"#,
                    got_is(&ent_json),
                    ents_json(&after, ids),
                    store.len()
                ));
            }
            7 => {
                // export
                let max = pick(&mut rng, N + 2);
                let cap = match pick(&mut rng, 4) {
                    0 => pick(&mut rng, 2 + max * 100),
                    _ => 2 + max * MAX_EXPORT_ENTRY_LEN,
                };
                let mut buf = vec![0u8; cap];
                let res = store.export(now, max, &mut buf);
                seen.exports += 1;
                let snap = snapshot(&store);
                assert_eq!(snap, before, "export changes the store");
                if let Ok(n) = res {
                    let c = classify(&buf[..n]);
                    assert!(c.well_formed());
                    assert!(c.ents.len() <= max);
                    assert!(c.ents.iter().all(|e| e.exp >= now));
                    let live: Vec<&Ent> = before.iter().filter(|e| e.exp >= now).collect();
                    assert_eq!(c.ents.len(), live.len().min(max));
                    let skip = live.len() - c.ents.len();
                    // the newest at most max, oldest first: the snapshot is oldest first
                    for (a, b) in c.ents.iter().zip(live.iter().skip(skip)) {
                        assert_eq!(a, *b);
                    }
                    old_blobs.push(buf[..n].to_vec());
                    out.push(format!(
                        r#"{{"t":"cexp","run":{run},"now":{now},"max":{max},"cap":{cap},"ok":true,"blob":"{}","b":{},"snap":{},"len":{}}}"#,
                        hex(&buf[..n]),
                        ents_json(&c.ents, ids),
                        ents_json(&snap, ids),
                        store.len()
                    ));
                } else {
                    seen.exports_small += 1;
                    out.push(format!(
                        r#"{{"t":"cexp","run":{run},"now":{now},"max":{max},"cap":{cap},"ok":false,"blob":"","b":[],"snap":{},"len":{}}}"#,
                        ents_json(&snap, ids),
                        store.len()
                    ));
                }
            }
            _ => {
                // restore
                let mut buf = vec![0u8; 2 + N * MAX_EXPORT_ENTRY_LEN];
                let n = store.export(now, N, &mut buf).unwrap();
                let mut blob = if !old_blobs.is_empty() && pick(&mut rng, 2) == 0 {
                    old_blobs[pick(&mut rng, old_blobs.len())].clone()
                } else {
                    buf[..n].to_vec()
                };
                let mut mutated = 0usize;
                if pick(&mut rng, 2) == 0 {
                    let which = pick(&mut rng, 6);
                    let count = usize::from(blob[1]);
                    mutated = match which {
                        0 => {
                            blob[0] = 2;
                            1
                        }
                        1 => {
                            blob.push(0);
                            2
                        }
                        2 if blob.len() > 2 => {
                            blob.truncate(2 + pick(&mut rng, blob.len() - 2));
                            3
                        }
                        3 if count > 0 => {
                            blob[2] = if pick(&mut rng, 2) == 0 { 0 } else { 9 };
                            4
                        }
                        4 if count > 0 => {
                            // the ALPN length of the first entry
                            blob[2 + 33] = 0;
                            5
                        }
                        5 => {
                            blob[1] = u8::try_from(count + 1 + pick(&mut rng, 2)).unwrap();
                            6
                        }
                        _ => 0,
                    };
                }
                let cls = classify(&blob);
                let res = store.restore(&blob, now);
                let after = snapshot(&store);
                let live_in_blob = cls.ents.iter().filter(|e| e.exp >= now).count();
                if cls.well_formed() {
                    assert_eq!(res.as_ref().ok().copied(), Some(live_in_blob));
                    seen.restores_ok += 1;
                    if live_in_blob < cls.ents.len() {
                        seen.restores_with_expired += 1;
                    }
                } else {
                    assert!(res.is_err(), "a malformed state was accepted");
                    assert_eq!(after, before, "a malformed state stored something");
                    seen.restores_bad[mutated.saturating_sub(1).min(5)] += 1;
                }
                let stored = res.map_or(-1, |n| i64::try_from(n).unwrap());
                out.push(format!(
                    r#"{{"t":"cres","run":{run},"now":{now},"blob":"{}","ver":{},"b":{},"bad":{},"trail":{},"ok":{},"n":{stored},"snap":{},"len":{}}}"#,
                    hex(&blob),
                    cls.ver,
                    ents_json(&cls.ents, ids),
                    cls.bad,
                    cls.trail,
                    cls.well_formed(),
                    ents_json(&after, ids),
                    store.len()
                ));
            }
        }
    }
}

fn got_is(ent_json: &str) -> bool {
    ent_json != NO_ENT
}

fn cache_run<const N: usize>(run: u32, ops: usize, seed: u64, out: &mut Vec<String>, seen: &mut Seen) {
    let mut rng = SplitMix64::traced(seed);
    let mut cache = PrekeyCache::<N>::new();
    out.push(format!(r#"{{"t":"pnew","run":{run},"n":{N}}}"#));
    let universe = N + 3;
    let mut present: Vec<u8> = vec![];
    for _ in 0..ops {
        let h = u8::try_from(1 + rng.next_u64() % universe as u64).unwrap();
        if rng.next_u64().is_multiple_of(2) {
            let got = cache.get(&[h; 32]);
            let (hit, v) = match got {
                Some(k) => {
                    assert!(k.iter().all(|b| *b == k[0]));
                    (true, k[0])
                }
                None => (false, 0),
            };
            assert_eq!(hit, present.contains(&h) && N > 0 || (hit && present.contains(&h)));
            if hit {
                seen.cache_hits += 1;
                // a hit refreshes: the hash is now the most recently used
                present.retain(|x| *x != h);
                present.insert(0, h);
            } else {
                seen.cache_misses += 1;
            }
            out.push(format!(
                r#"{{"t":"pget","run":{run},"h":{h},"hit":{hit},"v":{v},"len":{}}}"#,
                cache.len()
            ));
        } else {
            let v = u8::try_from(1 + rng.next_u64() % 3).unwrap();
            let had = present.contains(&h);
            cache.insert([h; 32], &[v; KEM_ENCAPS_KEY_LEN]);
            if N > 0 {
                if had {
                    present.retain(|x| *x != h);
                    seen.cache_refresh += 1;
                } else if present.len() == N {
                    present.pop();
                    seen.cache_evictions += 1;
                }
                present.insert(0, h);
            }
            assert_eq!(cache.len(), present.len());
            out.push(format!(
                r#"{{"t":"pins","run":{run},"h":{h},"v":{v},"len":{}}}"#,
                cache.len()
            ));
        }
        assert!(cache.len() <= N);
    }
}

fn server_run<const N: usize>(run: u32, ops: usize, seed: u64, ids: &mut Ids, out: &mut Vec<String>, seen: &mut Seen) {
    let mut rng = SplitMix64::traced(seed);
    let mut store = ServerTickets::<N>::new();
    out.push(format!(r#"{{"t":"snew","run":{run},"n":{N}}}"#));
    let provider = Software;
    let sess = session(peer(1), ALPNS[0], Aead::Aes128Gcm, 7, CreditRecord::NONE);
    for _ in 0..ops {
        let now = NOWS[usize::try_from(rng.next_u64() % NOWS.len() as u64).unwrap()];
        let life = u32::try_from(rng.next_u64() % 2).unwrap();
        let count = usize::try_from(rng.next_u64() % 6).unwrap();
        let sd = u8::try_from(1 + rng.next_u64() % 3).unwrap();
        // the 32 draws this seed gives: the most issue_batch can consume (MAX_BATCH tickets of ID_ATTEMPTS draws)
        let mut shadow = Drbg::new(&[sd; 32]);
        let mut senv = Env {
            provider: &provider,
            now,
            drbg: &mut shadow,
        };
        let draws: Vec<u32> = (0..4 * ID_ATTEMPTS)
            .map(|_| ids.id('t', 0, &senv.random::<16>().unwrap()))
            .collect();
        let before = store.len();
        let mut drbg = Drbg::new(&[sd; 32]);
        let mut env = Env {
            provider: &provider,
            now,
            drbg: &mut drbg,
        };
        let res = store.issue_batch(&mut env, &sess, count, life);
        let (ok, batch): (bool, Vec<u32>) = match &res {
            Ok(b) => (true, b.entries().iter().map(|e| ids.id('t', 0, &e.tid)).collect()),
            Err(e) => {
                assert_eq!(*e, Failure::TicketId);
                seen.issue_failures += 1;
                (false, vec![])
            }
        };
        if let Ok(b) = &res {
            assert!(b.entries().iter().all(|e| e.lifetime_s == life));
            assert!(b.entries().len() <= count.min(4));
            if N == 0 {
                assert_eq!(b.entries(), []);
            }
            if before == N && N > 0 && !b.entries().is_empty() {
                seen.issue_evicting += 1;
            }
            // draws are consumed in order, so a collision shows as a draw that was skipped
            if !b.entries().is_empty() {
                let first = ids.id('t', 0, &b.entries()[0].tid);
                if draws[0] != first {
                    seen.issue_partial_collisions += 1;
                }
            }
        }
        assert!(store.len() <= N);
        if count == 0 {
            assert_eq!(store.len(), before);
        }
        if !ok {
            seen.issue_collisions += 1;
        }
        let ds: Vec<String> = draws.iter().map(u32::to_string).collect();
        let bs: Vec<String> = batch.iter().map(u32::to_string).collect();
        out.push(format!(
            r#"{{"t":"siss","run":{run},"now":{now},"lf":{life},"cnt":{count},"draws":[{}],"ok":{ok},"batch":[{}],"len":{}}}"#,
            ds.join(","),
            bs.join(","),
            store.len()
        ));
    }
}

/// A server store that fills up from one seed, so that a fresh generator with the same seed collides on every draw.
fn server_collision<const N: usize>(run: u32, ids: &mut Ids, out: &mut Vec<String>, seen: &mut Seen) {
    let mut store = ServerTickets::<N>::new();
    out.push(format!(r#"{{"t":"snew","run":{run},"n":{N}}}"#));
    let provider = Software;
    let sess = session(peer(0), ALPNS[1], Aead::ChaCha20Poly1305, 9, CreditRecord::NONE);
    let sd = 5u8;
    let mut shadow = Drbg::new(&[sd; 32]);
    let mut senv = Env {
        provider: &provider,
        now: 0,
        drbg: &mut shadow,
    };
    let draws: Vec<u32> = (0..4 * ID_ATTEMPTS)
        .map(|_| ids.id('t', 0, &senv.random::<16>().unwrap()))
        .collect();
    // two calls of the same generator fill ID_ATTEMPTS slots with the first 8 draws, then a third call with a fresh
    // generator of the same seed draws only ids that are stored
    for step in 0..3 {
        let mut drbg = Drbg::new(&[sd; 32]);
        // the second call uses a generator positioned after the first call's draws: skip them
        let skipped = usize::from(step == 1) * 4;
        for _ in 0..skipped {
            let mut sink = [0u8; 16];
            drbg.fill(&mut sink).unwrap();
        }
        let mut env = Env {
            provider: &provider,
            now: 0,
            drbg: &mut drbg,
        };
        let cnt = if step < 2 { 4 } else { 1 };
        let res = store.issue_batch(&mut env, &sess, cnt, 1);
        let (ok, batch): (bool, Vec<u32>) = match &res {
            Ok(b) => (true, b.entries().iter().map(|e| ids.id('t', 0, &e.tid)).collect()),
            Err(e) => {
                assert_eq!(*e, Failure::TicketId);
                seen.issue_failures += 1;
                (false, vec![])
            }
        };
        if !ok {
            seen.issue_collisions += 1;
        }
        let ds: Vec<String> = draws
            .iter()
            .skip(skipped)
            .chain(draws.iter().take(skipped))
            .map(u32::to_string)
            .collect();
        let bs: Vec<String> = batch.iter().map(u32::to_string).collect();
        out.push(format!(
            r#"{{"t":"siss","run":{run},"now":0,"lf":1,"cnt":{cnt},"draws":[{}],"ok":{ok},"batch":[{}],"len":{}}}"#,
            ds.join(","),
            bs.join(","),
            store.len()
        ));
    }
}

#[test]
fn trace_stores() {
    let mut ids = Ids::default();
    let mut out: Vec<String> = vec![];
    let mut seen = Seen::default();
    let mut run = 0u32;
    macro_rules! client {
        ($($n:literal),*) => {$(
            for s in 0..4u64 {
                run += 1;
                client_run::<$n>(run, 160, 0xC11E_0000 + s * 17 + $n, &mut ids, &mut out, &mut seen);
            }
        )*};
    }
    client!(0, 1, 2, 3, 5);
    macro_rules! cache {
        ($($n:literal),*) => {$(
            for s in 0..3u64 {
                run += 1;
                cache_run::<$n>(run, 200, 0xCAC4_E000 + s * 31 + $n, &mut out, &mut seen);
            }
        )*};
    }
    cache!(0, 1, 2, 3, 8);
    macro_rules! server {
        ($($n:literal),*) => {$(
            for s in 0..3u64 {
                run += 1;
                server_run::<$n>(run, 60, 0x5E57_0000 + s * 13 + $n, &mut ids, &mut out, &mut seen);
            }
        )*};
    }
    server!(0, 1, 2, 3, 5);
    run += 1;
    server_collision::<8>(run, &mut ids, &mut out, &mut seen);
    run += 1;
    server_collision::<3>(run, &mut ids, &mut out, &mut seen);

    assert!(
        seen.takes_hit > 0 && seen.takes_miss > 0,
        "takes never both hit and miss"
    );
    assert!(seen.takes_expired_dropped > 0, "no take ever dropped an expired ticket");
    assert!(seen.takes_wrong_alpn > 0, "no take ever met a ticket for another ALPN");
    assert!(
        seen.replaced_same_peer > 0,
        "no ticket ever replaced the ticket of its peer"
    );
    assert!(seen.evicted_full > 0, "no ticket ever made room in a full store");
    assert!(
        seen.exports > 0 && seen.exports_small > 0,
        "exports never both fit and overflow the buffer"
    );
    assert!(
        seen.restores_ok > 0 && seen.restores_with_expired > 0,
        "restores never met expired entries"
    );
    assert!(
        seen.restores_bad.iter().all(|c| *c > 0),
        "a kind of malformed state was never restored: {:?}",
        seen.restores_bad
    );
    assert!(seen.bad_batches > 0);
    assert!(seen.cache_hits > 0 && seen.cache_misses > 0 && seen.cache_evictions > 0 && seen.cache_refresh > 0);
    assert!(
        seen.issue_collisions > 0 && seen.issue_failures > 0,
        "no issue ever failed on colliding draws"
    );
    assert!(
        seen.issue_partial_collisions > 0,
        "no issue ever skipped a colliding draw and succeeded"
    );
    assert!(
        seen.issue_evicting > 0,
        "no issue ever overwrote a ticket of a full store"
    );

    let Some(dir) = std::env::var_os("VINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    let mut text = String::new();
    for l in ids.lines.iter().chain(out.iter()) {
        text.push_str(l);
        text.push('\n');
    }
    std::fs::write(dir.join("stores.ndjson"), text).unwrap();
}
