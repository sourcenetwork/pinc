//! Trace generation for custody: seeded random runs of the real `CustodyBook` on a shared `Ledger` through the public
//! API (`accept`, `offer`, `on_ack`, `delivered`, `expire`, `holds`, `owed_to`, `len`) and of the host's direct calls
//! on the ledger, recorded as ndjson for the TLA+ trace check (`TraceDtnCustody.tla`) and the Lean replay
//! (`Vinc/TraceDtnStore.lean`).
//!
//! The world is small so that every branch is met: books of one to three records, ledgers of two to four slots, a
//! budget of ten bytes, four bundles, three custodian nodes (real Ed25519 keys), sizes of 1 to 6 bytes, lifetimes and
//! clocks of 0 to 6. A run mixes, in a seeded order: acceptances (also of a bundle already held, of one already kept as
//! transit, with a full book, with a full ledger), offers (also of an unknown bundle), acknowledgements (valid from the
//! node custody was offered to, from another node, for an unknown bundle, with a signature that does not verify),
//! deliveries, the book's expiry, and the host's own calls on the ledger: admissions of transit bundles and mailbox
//! items, expiry and release. The host never admits or releases a key the book holds a record of.
//!
//! What is recorded is what an observer sees: the call, what it returned (the error, the evicted entries), and after
//! every call the kept entries in slot order, the bytes charged, the held bundles with the node each ack is owed to,
//! and the book's length. The node an offer was made to is not observable; the model has to reproduce it for the later
//! acknowledgements to match. A forged acknowledgement is an ack whose custodian field names a node that did not sign.
//!
//! The test asserts everything itself against a tracker written here that does not share code with the book
//! (`dtn_ledger_oracle` for the ledger), and that every outcome was met, so it is meaningful without the proof tools.
//! The trace is written to `dtn_custody.ndjson` in the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing
//! is written.
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

mod dtn_ledger_oracle;

use std::collections::BTreeMap;

use dtn_ledger_oracle::{Ent, Oracle, Refusal, ents_json};
use vinc_crypto::{IdentityAlg, Keypair, NodeId};
use vinc_dtn::custody::{CustodyAck, CustodyBook, CustodyError, Incoming};
use vinc_dtn::head::BundleId;
use vinc_dtn::hlc::Hlc;
use vinc_dtn::store::{Class, Entry, Key, Ledger, Space, StoreError};
use vinc_tests::SplitMix64;

const BUNDLES: u8 = 4;
const NODES: u8 = 3;

fn node_key(n: u8) -> Keypair {
    let mut seed = vec![0; IdentityAlg::Ed25519.seed_len()];
    SplitMix64::new(0xC0DE + u64::from(n)).fill(&mut seed);
    Keypair::from_seed(IdentityAlg::Ed25519, &seed).unwrap()
}

fn bundle(b: u8) -> BundleId {
    BundleId([b; 32])
}

fn key(space: u8, id: u8) -> Key {
    Key {
        space: Space(space),
        id: [id; 32],
    }
}

fn ent_of(e: &Entry) -> (u8, u8, u64, bool, u64) {
    (
        e.key.space.0,
        e.key.id[0],
        e.bytes,
        e.class == Class::Custody,
        e.expires,
    )
}

fn view(e: &Ent) -> (u8, u8, u64, bool, u64) {
    (e.space, e.id, e.bytes, e.custody, e.exp)
}

/// The book as a plain table: bundle, node owed to, node custody was offered to.
type Table = Vec<Option<(u8, u8, Option<u8>)>>;

struct Tracker {
    led: Oracle,
    rec: Table,
}

impl Tracker {
    fn sync(&mut self) {
        for s in &mut self.rec {
            if s.is_some_and(|(b, _, _)| !self.led.contains(1, b)) {
                *s = None;
            }
        }
    }

    fn holds(&self, b: u8) -> bool {
        self.rec.iter().flatten().any(|r| r.0 == b)
    }

    /// `accept`: the error name and the evicted entries.
    fn accept(&mut self, b: u8, prev: u8, bytes: u64, exp: u64, now: u64) -> (&'static str, Vec<Ent>) {
        let mut ev = self.led.expire(now);
        self.sync();
        if self.holds(b) {
            return ("ok", ev);
        }
        let Some(slot) = self.rec.iter().position(Option::is_none) else {
            return ("cap", ev);
        };
        if self.led.contains(1, b) {
            self.led.reclass(1, b, true);
        } else {
            let (r, more) = self.led.admit(1, b, bytes, true, exp, now);
            ev.extend(more);
            match r {
                Ok(()) => {}
                Err(Refusal::Custody) => return ("cust", ev),
                Err(Refusal::Full) => return ("full", ev),
                Err(Refusal::Dup) => unreachable!("the bundle is not kept"),
            }
        }
        self.sync();
        self.rec[slot] = Some((b, prev, None));
        ("ok", ev)
    }

    fn on_ack(&mut self, b: u8, c: u8, valid: bool) -> &'static str {
        if !valid {
            return "ack";
        }
        let Some(slot) = self.rec.iter().position(|s| s.is_some_and(|r| r.0 == b)) else {
            return "unknown";
        };
        if self.rec[slot].and_then(|r| r.2) != Some(c) {
            return "notoffered";
        }
        self.rec[slot] = None;
        if self.led.reclass(1, b, false) {
            "ok"
        } else {
            "storeunknown"
        }
    }
}

#[derive(Default)]
struct Seen(BTreeMap<String, u32>);

impl Seen {
    fn hit(&mut self, what: &str) {
        *self.0.entry(what.to_string()).or_insert(0) += 1;
    }
}

fn cname(e: &CustodyError) -> &'static str {
    match e {
        CustodyError::Store(StoreError::CustodyRefused) => "cust",
        CustodyError::Store(StoreError::Full) => "full",
        CustodyError::Store(StoreError::Duplicate) => "dup",
        CustodyError::Store(StoreError::Unknown) => "storeunknown",
        CustodyError::Ack(_) => "ack",
        CustodyError::Capacity => "cap",
        CustodyError::Unknown => "unknown",
        CustodyError::NotOffered => "notoffered",
    }
}

/// Every acknowledgement the runs use, signed once: for each bundle and claimed custodian, one signed by that node and
/// one whose custodian field names it although another node signed.
type Acks = BTreeMap<(u8, u8, bool), CustodyAck>;

fn acks_table(nodes: &[(Keypair, NodeId)]) -> Acks {
    let mut t = Acks::new();
    for b in 1..=BUNDLES {
        for c in 1..=NODES {
            let good = CustodyAck::sign(bundle(b), nodes[1].1, Hlc::new(1, 0), &nodes[usize::from(c)].0).unwrap();
            assert!(good.verify().is_ok());
            let signer = usize::from(c % NODES + 1);
            let mut forged = CustodyAck::sign(bundle(b), nodes[1].1, Hlc::new(1, 0), &nodes[signer].0).unwrap();
            forged.custodian = nodes[usize::from(c)].1;
            assert!(forged.verify().is_err());
            t.insert((b, c, true), good);
            t.insert((b, c, false), forged);
        }
    }
    t
}

fn nodes() -> Vec<(Keypair, NodeId)> {
    (0..=NODES)
        .map(|n| {
            let k = node_key(n);
            let id = k.node_id();
            (k, id)
        })
        .collect()
}

fn run<const NB: usize, const NL: usize>(
    seed: u64,
    ops: usize,
    nodes: &[(Keypair, NodeId)],
    acks: &Acks,
    out: &mut Vec<String>,
    seen: &mut Seen,
) {
    let node_no = |id: &NodeId| nodes.iter().position(|(_, n)| n == id).unwrap() as u8;
    let mut rng = SplitMix64::new(seed);
    let mut pick = |v: &[u64]| v[(rng.next_u64() % v.len() as u64) as usize];
    let budget = 10;
    let mut ledger = Ledger::<NL>::new(budget);
    let mut book = CustodyBook::<NB>::new();
    let mut model = Tracker {
        led: Oracle::new(NL, budget),
        rec: vec![None; NB],
    };
    let mut offered: BTreeMap<u8, u8> = BTreeMap::new();
    out.push(format!(r#"{{"t":"cu_new","n":{NB},"ln":{NL},"budget":{budget}}}"#));
    let sizes = [1, 2, 3, 4, 6];
    let times = [0, 1, 2, 3, 4, 5, 6];
    let state = |ledger: &Ledger<NL>, book: &CustodyBook<NB>, model: &Tracker| {
        let snap: Vec<_> = ledger.iter().map(ent_of).collect();
        assert_eq!(
            snap,
            model.led.ents().iter().map(view).collect::<Vec<_>>(),
            "kept entries"
        );
        assert_eq!(u128::from(ledger.used()), model.led.used());
        let mut held = vec![];
        for b in 1..=BUNDLES {
            assert_eq!(book.holds(&bundle(b)), model.holds(b), "holds {b}");
            if let Some(p) = book.owed_to(&bundle(b)) {
                let want = model.rec.iter().flatten().find(|r| r.0 == b).unwrap().1;
                assert_eq!(node_no(&p), want, "owed_to {b}");
                held.push(format!("[{b},{}]", node_no(&p)));
            }
        }
        assert_eq!(book.len(), model.rec.iter().flatten().count());
        format!(
            r#""snap":{},"used":{},"held":[{}],"blen":{}"#,
            ents_json(&model.led.ents()),
            ledger.used(),
            held.join(","),
            book.len()
        )
    };
    for _ in 0..ops {
        let kind = pick(&[0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 5, 5, 5, 6, 7, 8]);
        let b = pick(&[1, 2, 3, 4]) as u8;
        let now = pick(&times);
        match kind {
            0 => {
                let (p, bytes, exp) = (pick(&[1, 2, 3]) as u8, pick(&sizes), pick(&times));
                let mut gone = vec![];
                let r = book.accept(
                    &mut ledger,
                    Incoming {
                        bundle: bundle(b),
                        bytes,
                        expires: exp,
                        previous: nodes[usize::from(p)].1,
                    },
                    now,
                    |e| gone.push(*e),
                );
                let was_transit = model
                    .led
                    .ents()
                    .iter()
                    .any(|e| e.space == 1 && e.id == b && !e.custody && e.exp > now);
                let (merr, mev) = model.accept(b, p, bytes, exp, now);
                let err = r.as_ref().err().map_or("ok", cname);
                assert_eq!(err, merr, "accept");
                assert_eq!(
                    gone.iter().map(ent_of).collect::<Vec<_>>(),
                    mev.iter().map(view).collect::<Vec<_>>()
                );
                if let Ok(due) = &r {
                    assert_eq!(due.bundle, bundle(b));
                    assert_eq!(due.previous, nodes[usize::from(p)].1);
                }
                seen.hit(&format!("accept {err}"));
                if err == "ok" && was_transit {
                    seen.hit("accept promotes transit");
                }
                if mev.iter().any(|e| e.exp > now) {
                    seen.hit("accept evicts transit");
                }
                if model.rec.iter().flatten().any(|r| r.0 == b) {
                    offered.remove(&b);
                }
                out.push(format!(
                    r#"{{"t":"cu_acc","b":{b},"p":{p},"by":{bytes},"x":{exp},"now":{now},"err":"{err}","ev":{},{}}}"#,
                    ents_json(&mev),
                    state(&ledger, &book, &model)
                ));
            }
            1 => {
                let to = pick(&[1, 2, 3]) as u8;
                let r = book.offer(&bundle(b), nodes[usize::from(to)].1);
                let held = model.holds(b);
                assert_eq!(r.is_ok(), held);
                if held {
                    // The offer lands on the (only) record of the bundle.
                    for s in model.rec.iter_mut().flatten().filter(|r| r.0 == b) {
                        s.2 = Some(to);
                    }
                    offered.insert(b, to);
                } else {
                    assert_eq!(r.err(), Some(CustodyError::Unknown));
                }
                seen.hit(if held { "offer ok" } else { "offer unknown" });
                out.push(format!(
                    r#"{{"t":"cu_off","b":{b},"to":{to},"err":"{}",{}}}"#,
                    if held { "ok" } else { "unknown" },
                    state(&ledger, &book, &model)
                ));
            }
            2 => {
                // An acknowledgement: usually from the node custody was offered to, sometimes from another, and a
                // quarter of them with a custodian field that did not sign.
                let c = match (offered.get(&b), pick(&[0, 1, 2])) {
                    (Some(&o), 0 | 1) => o,
                    _ => pick(&[1, 2, 3]) as u8,
                };
                let valid = pick(&[0, 0, 0, 1]) != 1;
                let ack = acks[&(b, c, valid)].clone();
                let r = book.on_ack(&mut ledger, &ack);
                let merr = model.on_ack(b, c, valid);
                let err = r.as_ref().err().map_or("ok", cname);
                assert_eq!(err, merr, "on_ack");
                seen.hit(&format!("ack {err}"));
                if err == "ok" {
                    offered.remove(&b);
                }
                out.push(format!(
                    r#"{{"t":"cu_ack","b":{b},"c":{c},"v":{valid},"err":"{err}",{}}}"#,
                    state(&ledger, &book, &model)
                ));
            }
            3 => {
                let r = book.delivered(&mut ledger, &bundle(b));
                let held = model.holds(b);
                assert_eq!(r.is_ok(), held);
                if held {
                    for s in &mut model.rec {
                        if s.is_some_and(|r| r.0 == b) {
                            *s = None;
                        }
                    }
                    model.led.release(1, b);
                    offered.remove(&b);
                } else {
                    assert_eq!(r.err(), Some(CustodyError::Unknown));
                }
                seen.hit(if held { "delivered ok" } else { "delivered unknown" });
                out.push(format!(
                    r#"{{"t":"cu_del","b":{b},"err":"{}",{}}}"#,
                    if held { "ok" } else { "unknown" },
                    state(&ledger, &book, &model)
                ));
            }
            4 => {
                let mut gone = vec![];
                book.expire(&mut ledger, now, |e| gone.push(*e));
                let mev = model.led.expire(now);
                model.sync();
                assert_eq!(
                    gone.iter().map(ent_of).collect::<Vec<_>>(),
                    mev.iter().map(view).collect::<Vec<_>>()
                );
                if !mev.is_empty() {
                    seen.hit("book expiry removes");
                }
                out.push(format!(
                    r#"{{"t":"cu_exp","now":{now},"ev":{},{}}}"#,
                    ents_json(&mev),
                    state(&ledger, &book, &model)
                ));
            }
            5 => {
                // The host admits a bundle it is not in custody of (transit) or a mailbox item.
                let space = pick(&[1, 2]) as u8;
                let id = pick(&[1, 2, 3, 4, 5]) as u8;
                if space == 1 && model.holds(id) {
                    continue;
                }
                let (bytes, custody, exp) = (pick(&sizes), pick(&[0, 1]) == 0, pick(&times));
                let mut gone = vec![];
                let r = ledger.admit(
                    key(space, id),
                    bytes,
                    if custody { Class::Custody } else { Class::Transit },
                    exp,
                    now,
                    |e| gone.push(*e),
                );
                let (mr, mev) = model.led.admit(space, id, bytes, custody, exp, now);
                let err = match (&r, mr) {
                    (Ok(()), Ok(())) => "ok",
                    (Err(StoreError::Duplicate), Err(Refusal::Dup)) => "dup",
                    (Err(StoreError::CustodyRefused), Err(Refusal::Custody)) => "cust",
                    (Err(StoreError::Full), Err(Refusal::Full)) => "full",
                    other => panic!("host admit differs from the reference: {other:?}"),
                };
                assert_eq!(
                    gone.iter().map(ent_of).collect::<Vec<_>>(),
                    mev.iter().map(view).collect::<Vec<_>>()
                );
                seen.hit(&format!("host admit {err}"));
                out.push(format!(
                    r#"{{"t":"cu_hadm","s":{space},"i":{id},"b":{bytes},"c":{},"x":{exp},"now":{now},"err":"{err}","ev":{},{}}}"#,
                    u8::from(!custody),
                    ents_json(&mev),
                    state(&ledger, &book, &model)
                ));
            }
            6 => {
                // The host expires the ledger directly: the book keeps a stale record until its next call.
                let mut gone = vec![];
                ledger.expire(now, |e| gone.push(*e));
                let mev = model.led.expire(now);
                assert_eq!(
                    gone.iter().map(ent_of).collect::<Vec<_>>(),
                    mev.iter().map(view).collect::<Vec<_>>()
                );
                if model.rec.iter().flatten().any(|r| !model.led.contains(1, r.0)) {
                    seen.hit("stale record after a host expiry");
                }
                out.push(format!(
                    r#"{{"t":"cu_hexp","now":{now},"ev":{},{}}}"#,
                    ents_json(&mev),
                    state(&ledger, &book, &model)
                ));
            }
            _ => {
                let space = pick(&[1, 2]) as u8;
                let id = pick(&[1, 2, 3, 4, 5]) as u8;
                if space == 1 && model.holds(id) {
                    continue;
                }
                let got = ledger.release(&key(space, id));
                let mgot = model.led.release(space, id);
                assert_eq!(got.as_ref().map(ent_of), mgot.as_ref().map(view));
                let e = mgot.as_ref().map_or_else(
                    || r#"{"s":0,"i":0,"b":0,"c":0,"x":0}"#.to_string(),
                    dtn_ledger_oracle::ent_json,
                );
                out.push(format!(
                    r#"{{"t":"cu_hrel","s":{space},"i":{id},"got":{},"e":{e},{}}}"#,
                    got.is_some(),
                    state(&ledger, &book, &model)
                ));
            }
        }
    }
}

#[test]
fn custody_runs_match_the_tracker_and_are_recorded() {
    let mut out = vec![];
    let mut seen = Seen::default();
    let nodes = nodes();
    let acks = acks_table(&nodes);
    for seed in 0..40 {
        run::<1, 2>(seed, 70, &nodes, &acks, &mut out, &mut seen);
        run::<2, 3>(seed + 1_000, 70, &nodes, &acks, &mut out, &mut seen);
        run::<3, 4>(seed + 2_000, 70, &nodes, &acks, &mut out, &mut seen);
        run::<2, 2>(seed + 3_000, 70, &nodes, &acks, &mut out, &mut seen);
        run::<3, 2>(seed + 4_000, 70, &nodes, &acks, &mut out, &mut seen);
    }
    for what in [
        "accept ok",
        "accept cap",
        "accept cust",
        "accept promotes transit",
        "accept evicts transit",
        "offer ok",
        "offer unknown",
        "ack ok",
        "ack ack",
        "ack unknown",
        "ack notoffered",
        "ack storeunknown",
        "delivered ok",
        "delivered unknown",
        "book expiry removes",
        "host admit ok",
        "host admit dup",
        "host admit cust",
        "host admit full",
        "stale record after a host expiry",
    ] {
        assert!(
            seen.0.get(what).copied().unwrap_or(0) > 0,
            "the world never met: {what}: {:?}",
            seen.0
        );
    }
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        let mut text = out.join("\n");
        text.push('\n');
        std::fs::write(std::path::Path::new(&dir).join("dtn_custody.ndjson"), text).unwrap();
    }
}
