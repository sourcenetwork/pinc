//! Trace generation for the key roll: seeded random runs of the real `Roll`, `Rekey`, `PacketKey`, `roll_secret` and
//! `keyroll::due` through the public API, recorded as ndjson (`keyroll.ndjson`) for the TLA+ trace check
//! (`TraceKeyRoll.tla`) and the Lean replay (`Vinc/TraceKeyRoll.lean`).
//!
//! A run is two connections' worth of state: a dialing and an accepting `Roll`, each with its own generator, and four
//! packet keys (the sending and the receiving key of each node, the pair of one direction sharing a secret). A run
//! mixes, in a seeded order, the events a lossy, reordering, duplicating network produces: a node starts a roll (one
//! at a time, so a collision happens when both do), a message of the pool is delivered to a node any number of times
//! and in any order (a request or an answer to the method of its kind, and in one case in five to the method of the
//! other kind), a message whose share was changed by an attacker or is the all-zero value, a stale answer, a
//! duplicate request. Every completed roll rolls both packet keys of the node with the Diffie-Hellman value it
//! computed, as `vinc_transport::conn::keys` does; traffic is sealed on a node's sending key (packet numbers offered
//! in order, repeated, lower, and above 2^62) and opened at the peer's receiving key, with packets that are tampered
//! or opened under another number or another key. Keys run with small limits so the AEAD limits fire.
//!
//! What is recorded is what an observer sees. A share, a Diffie-Hellman value and a sealed packet are ids (one id per
//! distinct byte string in a run: equal bytes, equal id), so the checkers never see X25519 or the AEAD: they replay
//! the calls on symbolic terms and require the ids to relate exactly as the terms do (a share is a public atom, the
//! Diffie-Hellman value of two atoms is the unordered pair, a sealed packet is the pair of the key's secret and its
//! number). Both sides' values are equal iff the terms are equal, so the agreement of the two sides of a roll and
//! the disagreement after a stale or forged message are checked, not assumed. A run also ends with `due` verdicts at
//! the limits and the codec of the REKEY body (`enc`, `dec`).
//!
//! The test asserts everything itself (the real code against a plain tracker written here: the two sides of a roll
//! hold the same Diffie-Hellman value, an open succeeds iff the key chains and the number agree, ...), so it is
//! meaningful without the proof tools. `GenerationExhausted` is not reachable (it needs 2^32 - 1 rolls of one key):
//! that refusal is covered by the Lean and TLA+ models only. The flip/hold layer lives in `vinc-transport`
//! (`pub(crate)`), whose REKEY bodies the public `Connection` API moves but whose key state it does not expose, so
//! that layer is validated by model checking only, not by this trace.
//! The trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
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

use vinc_crypto::{Aead, Drbg, Secret, Software};
use vinc_security::keyroll::{ECHO_LEN, MAX_KEY_AGE_NS, MAX_REKEY_LEN, due, request_id};
use vinc_security::{Env, Failure, Limits, PacketKey, RecordError, Rekey, Roll, roll_secret};
use vinc_tests::SplitMix64;
use vinc_wire::WireError;

type Key = PacketKey<Software>;

fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

fn bytes32(rng: &mut SplitMix64) -> [u8; 32] {
    let mut b = [0u8; 32];
    rng.fill(&mut b);
    b
}

/// Dense ids, from 1, for distinct byte strings of one kind, in one run.
#[derive(Default)]
struct Ids(HashMap<(u8, Vec<u8>), u32>);

const K_SHARE: u8 = 1;
const K_DH: u8 = 2;
const K_CT: u8 = 3;
const K_ECHO: u8 = 4;

impl Ids {
    fn id(&mut self, kind: u8, bytes: &[u8]) -> i64 {
        let next = u32::try_from(self.0.len()).unwrap() + 1;
        i64::from(*self.0.entry((kind, bytes.to_vec())).or_insert(next))
    }
}

/// The trace, one ndjson line per event.
#[derive(Default)]
struct Trace(String);

impl Trace {
    fn line(&mut self, s: &str) {
        self.0.push_str(s);
        self.0.push('\n');
    }
}

fn b(x: bool) -> &'static str {
    if x { "true" } else { "false" }
}

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        (v >> 48) & 0xffff
    )
}

fn list(bytes: &[u8]) -> String {
    let mut s = String::from("[");
    for (i, x) in bytes.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, "{x}").unwrap();
    }
    s.push(']');
    s
}

/// A packet number as the trace records it: the small part and a code (0 as is, 1 for 2^62 plus the small part, 2 for
/// `u64::MAX`), since the TLA+ checker has 32-bit integers.
fn split_pn(pn: u64) -> (u64, u8) {
    if pn == u64::MAX {
        (0, 2)
    } else if pn >= 1 << 62 {
        (pn - (1 << 62), 1)
    } else {
        (pn, 0)
    }
}

fn env<'a>(p: &'a Software, drbg: &'a mut Drbg) -> Env<'a, Software> {
    Env {
        provider: p,
        now: 0,
        drbg,
    }
}

fn res_name(f: &Failure) -> &'static str {
    match f {
        Failure::UnexpectedMessage => "unexpected",
        Failure::InvalidPeerKey => "invalid",
        other => panic!("unexpected failure {other:?}"),
    }
}

/// The state of one run.
struct Run {
    id: u32,
    ids: Ids,
    roll: [Roll; 2],
    drbg: [Drbg; 2],
    /// Slots: 0 sending key of node 0, 1 receiving key of node 0, 2 sending key of node 1, 3 receiving key of node 1.
    keys: [Key; 4],
    /// The dh ids each slot was rolled with: a plain tracker of the key chains, to assert against.
    chain: [Vec<i64>; 4],
    /// The next packet number each slot may seal.
    next_pn: [u64; 4],
    pool: Vec<Rekey>,
    /// Sealed packets of the run by id: (ciphertext, tag, slot sealed under, chain at the time, number).
    packets: Vec<(i64, Vec<u8>, [u8; 16], usize, Vec<i64>, u64)>,
    /// For an answer share: the request share it answered and the value its sender computed.
    answered: HashMap<[u8; 32], ([u8; 32], [u8; 32])>,
}

const PLAIN: &[u8; 8] = b"VINCroll";
const AAD: &[u8] = b"hdr";

fn new_run(rng: &mut SplitMix64, tr: &mut Trace, id: u32) -> Run {
    let p = Software;
    let aead = if below(rng, 2) == 0 {
        Aead::Aes128Gcm
    } else {
        Aead::ChaCha20Poly1305
    };
    let limits = Limits {
        aes_gcm_packets: 2 + below(rng, 3),
        chacha_failures: 2 + below(rng, 2),
    };
    let (s01, s10) = (Secret::new(bytes32(rng)), Secret::new(bytes32(rng)));
    let mk = |s: &Secret<32>| PacketKey::from_secret(&p, aead, s).unwrap().with_limits(limits);
    let seed = |rng: &mut SplitMix64| Drbg::new(&bytes32(rng));
    let drbg = [seed(rng), seed(rng)];
    tr.line(&format!(
        r#"{{"t":"kr","op":"begin","run":{id},"aead":{},"al":{},"cl":{}}}"#,
        u8::from(aead == Aead::Aes128Gcm),
        limits.aes_gcm_packets,
        limits.chacha_failures
    ));
    Run {
        id,
        ids: Ids::default(),
        roll: [Roll::new(true), Roll::new(false)],
        drbg,
        keys: [mk(&s01), mk(&s10), mk(&s10), mk(&s01)],
        chain: [vec![], vec![], vec![], vec![]],
        next_pn: [0; 4],
        pool: Vec::new(),
        packets: Vec::new(),
        answered: HashMap::new(),
    }
}

impl Run {
    fn pend_id(&mut self, n: usize) -> i64 {
        match self.roll[n].pending() {
            Some(m) => self.ids.id(K_SHARE, &m.share),
            None => -1,
        }
    }

    fn tail(&mut self, n: usize) -> String {
        let pend = self.pend_id(n);
        format!(
            r#""pend":{pend},"idle":{},"rolls":{}"#,
            b(self.roll[n].is_idle()),
            self.roll[n].rolls()
        )
    }

    fn start(&mut self, tr: &mut Trace, n: usize) {
        let p = Software;
        let was_idle = self.roll[n].is_idle();
        let r = self.roll[n].start(&mut env(&p, &mut self.drbg[n]));
        let (res, share) = match r {
            Ok(req) => {
                assert!(was_idle && !req.answer && req.switch_pn == 0);
                self.pool.push(req);
                ("ok", self.ids.id(K_SHARE, &req.share))
            }
            Err(f) => {
                assert!(!was_idle && f == Failure::UnexpectedMessage);
                ("unexpected", -1)
            }
        };
        let tail = self.tail(n);
        tr.line(&format!(
            r#"{{"t":"kr","op":"start","run":{},"n":{n},"res":"{res}","share":{share},{tail}}}"#,
            self.id
        ));
    }

    /// Roll both packet keys of node `n` with `dh`.
    fn roll_keys(&mut self, tr: &mut Trace, n: usize, dh: &Secret<32>) {
        let p = Software;
        let dhid = self.ids.id(K_DH, dh.expose());
        for slot in [2 * n, 2 * n + 1] {
            let next = self.keys[slot].rolled(&p, dh).unwrap();
            self.keys[slot] = next;
            self.chain[slot].push(dhid);
            self.next_pn[slot] = 0;
            tr.line(&format!(
                r#"{{"t":"kr","op":"pkroll","run":{},"slot":{slot},"dh":{dhid},"res":"ok","gen":{}}}"#,
                self.id,
                self.keys[slot].generation()
            ));
        }
    }

    /// Deliver `msg` to node `n` through the method of its own kind, or (`wrong`) of the other kind.
    fn deliver(&mut self, tr: &mut Trace, n: usize, msg: Rekey, wrong: bool, spn: u64) {
        let p = Software;
        let zero = msg.share == [0u8; 32];
        let sid = self.ids.id(K_SHARE, &msg.share);
        let eid = self.ids.id(K_ECHO, &msg.echo);
        let as_answer = msg.answer != wrong;
        let head = format!(
            r#""run":{},"n":{n},"ans":{},"zero":{},"share":{sid},"echo":{eid},"spn":{}"#,
            self.id,
            b(msg.answer),
            b(zero),
            if as_answer { msg.switch_pn } else { spn }
        );
        if as_answer {
            let own = self.roll[n].pending().map(|r| r.share);
            let r = self.roll[n].on_answer(&env(&p, &mut self.drbg[n]), &msg);
            match r {
                Ok(done) => {
                    assert!(msg.answer && own.is_some());
                    let dhid = self.ids.id(K_DH, done.dh.expose());
                    // Agreement: the answer taken names the request that is out, and when it is one the answerer
                    // computed (its share unchanged), both sides hold the same value.
                    assert_eq!(
                        msg.echo,
                        request_id(&own.unwrap()),
                        "an answer is taken only for the request out"
                    );
                    if let Some((req, theirs)) = self.answered.get(&msg.share) {
                        assert_eq!(Some(*req), own);
                        assert_eq!(&theirs[..], &done.dh.expose()[..], "both sides computed the same value");
                    }
                    assert_eq!(done.peer_switch_pn, msg.switch_pn);
                    let tail = self.tail(n);
                    tr.line(&format!(
                        r#"{{"t":"kr","op":"onans",{head},"res":"ok","dh":{dhid},"pspn":{},{tail}}}"#,
                        done.peer_switch_pn
                    ));
                    self.roll_keys(tr, n, &done.dh);
                }
                Err(f) => {
                    let tail = self.tail(n);
                    tr.line(&format!(
                        r#"{{"t":"kr","op":"onans",{head},"res":"{}","dh":-1,"pspn":0,{tail}}}"#,
                        res_name(&f)
                    ));
                }
            }
        } else {
            let r = self.roll[n].on_request(&mut env(&p, &mut self.drbg[n]), &msg, spn);
            match r {
                Ok(answered) => {
                    assert!(!msg.answer && answered.answer.answer);
                    let oans = self.ids.id(K_SHARE, &answered.answer.share);
                    let oecho = self.ids.id(K_ECHO, &answered.answer.echo);
                    assert_eq!(answered.answer.echo, request_id(&msg.share));
                    let dh = answered.dh.as_ref().map_or(-1, |d| self.ids.id(K_DH, d.expose()));
                    if let Some(d) = &answered.dh {
                        self.answered.insert(answered.answer.share, (msg.share, *d.expose()));
                    }
                    self.pool.push(answered.answer);
                    let tail = self.tail(n);
                    tr.line(&format!(
                        r#"{{"t":"kr","op":"onreq",{head},"res":"ok","oans":{oans},"oecho":{oecho},"ospn":{},"dh":{dh},{tail}}}"#,
                        answered.answer.switch_pn
                    ));
                    if let Some(d) = answered.dh {
                        self.roll_keys(tr, n, &d);
                    }
                }
                Err(f) => {
                    let tail = self.tail(n);
                    tr.line(&format!(
                        r#"{{"t":"kr","op":"onreq",{head},"res":"{}","oans":-1,"oecho":-1,"ospn":0,"dh":-1,{tail}}}"#,
                        res_name(&f)
                    ));
                }
            }
        }
    }

    /// Seal on the sending slot of node `n` and open at some receiving slot.
    fn traffic(&mut self, rng: &mut SplitMix64, tr: &mut Trace, n: usize) {
        let p = Software;
        let slot = 2 * n;
        // The packet number offered: the next in order, a repeat of the last, a lower one, or above 2^62.
        let pn = match below(rng, 20) {
            0 => (1u64 << 62) + below(rng, 3),
            1 => u64::MAX,
            2 | 3 => self.next_pn[slot].saturating_sub(1),
            4 => 0,
            _ => self.next_pn[slot],
        };
        let mut buf = *PLAIN;
        let sealed_before = self.keys[slot].sealed();
        let r = self.keys[slot].seal(&p, pn, AAD, &mut buf);
        let (pn_event, big) = split_pn(pn);
        let (res, ct) = match r {
            Ok(tag) => {
                assert_eq!(self.keys[slot].sealed(), sealed_before + 1);
                self.next_pn[slot] = pn + 1;
                let mut all = buf.to_vec();
                all.extend_from_slice(&tag);
                let id = self.ids.id(K_CT, &all);
                self.packets
                    .push((id, buf.to_vec(), tag, slot, self.chain[slot].clone(), pn));
                ("ok", id)
            }
            Err(RecordError::PacketNumber) => {
                assert_eq!(buf, *PLAIN);
                ("pn", -1)
            }
            Err(RecordError::NotIncreasing) => {
                assert_eq!(buf, *PLAIN);
                ("inc", -1)
            }
            Err(RecordError::KeyRollRequired) => {
                assert_eq!(buf, *PLAIN);
                ("roll", -1)
            }
            Err(e) => panic!("unexpected {e:?}"),
        };
        if res != "ok" {
            assert_eq!(self.keys[slot].sealed(), sealed_before, "a refusal changes nothing");
        }
        tr.line(&format!(
            r#"{{"t":"kr","op":"seal","run":{},"slot":{slot},"pn":{pn_event},"big":{big},"res":"{res}","ct":{ct},"sealed":{},"gen":{}}}"#,
            self.id,
            self.keys[slot].sealed(),
            self.keys[slot].generation()
        ));
        // Open: some packet of the run at some receiving slot, with its number, another number, or tampered.
        if self.packets.is_empty() {
            return;
        }
        let k = if below(rng, 3) == 0 {
            below(rng, self.packets.len() as u64) as usize
        } else {
            self.packets.len() - 1
        };
        let (cid, ct_bytes, tag, from, chain_at, sealed_pn) = self.packets[k].clone();
        let rslot = if below(rng, 4) == 0 {
            [1usize, 3][below(rng, 2) as usize]
        } else {
            // The peer's receiving key of the slot it was sealed under.
            match from {
                0 => 3,
                2 => 1,
                other => other,
            }
        };
        let mut open_pn = sealed_pn;
        let (mut id, mut tampered) = (cid, false);
        let (mut obuf, mut otag) = (ct_bytes.clone(), tag);
        match below(rng, 10) {
            0 => open_pn = sealed_pn + 1 + below(rng, 3),
            3 => open_pn = 1 << 62,
            1 => {
                let i = below(rng, 8) as usize;
                obuf[i] ^= 1 << below(rng, 8);
                let mut all = obuf.clone();
                all.extend_from_slice(&otag);
                id = self.ids.id(K_CT, &all);
                tampered = true;
            }
            2 => {
                let i = below(rng, 16) as usize;
                otag[i] ^= 1 << below(rng, 8);
                let mut all = obuf.clone();
                all.extend_from_slice(&otag);
                id = self.ids.id(K_CT, &all);
                tampered = true;
            }
            _ => {}
        }
        let obig = open_pn > (1u64 << 62) - 1;
        let failed_before = self.keys[rslot].failed_opens();
        let copy = obuf.clone();
        let r = self.keys[rslot].open(&p, open_pn, AAD, &mut obuf, &otag);
        // The plain tracker: a packet opens iff it was not tampered, the number is the one it was sealed under, and
        // the chain of Diffie-Hellman values of the two keys is the same and they are of the same direction.
        let same_dir = matches!((from, rslot), (0, 3) | (2, 1));
        let expect_valid = !tampered && open_pn == sealed_pn && same_dir && chain_at == self.chain[rslot];
        let res = match r {
            Ok(()) => {
                assert!(expect_valid, "opened a packet the tracker says is not valid");
                assert_eq!(&obuf[..], &PLAIN[..]);
                assert_eq!(self.keys[rslot].failed_opens(), failed_before);
                "ok"
            }
            Err(RecordError::Authentication) => {
                assert!(!expect_valid, "refused a packet the tracker says is valid");
                assert_eq!(obuf, copy, "a failed open leaves the ciphertext");
                assert_eq!(self.keys[rslot].failed_opens(), failed_before + 1);
                "auth"
            }
            Err(RecordError::KeyRollRequired) => {
                assert_eq!(obuf, copy);
                "roll"
            }
            Err(RecordError::PacketNumber) => {
                assert!(obig);
                "pn"
            }
            Err(e) => panic!("unexpected {e:?}"),
        };
        let (open_pn_event, obigc) = split_pn(open_pn);
        tr.line(&format!(
            r#"{{"t":"kr","op":"open","run":{},"slot":{rslot},"ct":{id},"pn":{open_pn_event},"big":{obigc},"res":"{res}","failed":{},"gen":{}}}"#,
            self.id,
            self.keys[rslot].failed_opens(),
            self.keys[rslot].generation()
        ));
    }

    /// A message the attacker made: a legitimate one with a changed share, or the all-zero value.
    fn forge(&mut self, rng: &mut SplitMix64) {
        if self.pool.is_empty() {
            return;
        }
        let mut m = self.pool[below(rng, self.pool.len() as u64) as usize];
        match below(rng, 4) {
            0 => m.share = [0u8; 32],
            1 => m.echo[below(rng, 8) as usize] ^= 1 << below(rng, 8),
            _ => m.share[below(rng, 32) as usize] ^= 1 << below(rng, 8),
        }
        self.pool.push(m);
    }
}

fn run(rng: &mut SplitMix64, tr: &mut Trace, id: u32) {
    let mut r = new_run(rng, tr, id);
    let steps = 30 + below(rng, 30);
    for _ in 0..steps {
        match below(rng, 12) {
            0 | 1 => {
                let n = below(rng, 2) as usize;
                r.start(tr, n);
            }
            2..=6 => {
                if r.pool.is_empty() {
                    let n = below(rng, 2) as usize;
                    r.start(tr, n);
                    continue;
                }
                let msg = r.pool[below(rng, r.pool.len() as u64) as usize];
                // Mostly the peer of the sender, sometimes the sender itself; mostly the method of the kind.
                let n = below(rng, 2) as usize;
                let wrong = below(rng, 5) == 0;
                let spn = 1 + below(rng, 1000);
                r.deliver(tr, n, msg, wrong, spn);
            }
            7..=9 => {
                let n = below(rng, 2) as usize;
                r.traffic(rng, tr, n);
            }
            _ => r.forge(rng),
        }
    }
    // Every run ends with traffic from both nodes.
    r.traffic(rng, tr, 0);
    r.traffic(rng, tr, 1);
}

/// One `due` verdict, over keys driven to a state: sealed and failed-open counts, with small limits.
fn due_event(rng: &mut SplitMix64, tr: &mut Trace) {
    let p = Software;
    let limits = Limits {
        aes_gcm_packets: 1 + below(rng, 4),
        chacha_failures: 1 + below(rng, 3),
    };
    let mk = |rng: &mut SplitMix64| -> Key {
        let aead = if below(rng, 2) == 0 {
            Aead::Aes128Gcm
        } else {
            Aead::ChaCha20Poly1305
        };
        PacketKey::from_secret(&p, aead, &Secret::new([7; 32]))
            .unwrap()
            .with_limits(limits)
    };
    let (mut send, mut recv) = (mk(rng), mk(rng));
    for pn in 0..below(rng, 6) {
        let mut buf = *PLAIN;
        let _ = send.seal(&p, pn, AAD, &mut buf);
    }
    for _ in 0..below(rng, 5) {
        let mut buf = *PLAIN;
        let _ = recv.open(&p, 0, AAD, &mut buf, &[0u8; 16]);
    }
    let age = match below(rng, 5) {
        0 => MAX_KEY_AGE_NS - 1,
        1 => MAX_KEY_AGE_NS,
        2 => MAX_KEY_AGE_NS + 1,
        3 => below(rng, 1_000_000_000),
        _ => 1_500_000_000_000 + below(rng, 1_000_000_000),
    };
    let after = [1u64, 2, 3, 1 << 21][below(rng, 4) as usize];
    let got = due(&send, &recv, age, after);
    assert_eq!(
        got,
        send.limit_reached() || recv.limit_reached() || send.sealed() >= after || age >= MAX_KEY_AGE_NS
    );
    let aead_of = |k: &Key| u8::from(k.aead() == Aead::Aes128Gcm);
    tr.line(&format!(
        r#"{{"t":"kr","op":"due","sa":{},"ss":{},"sf":{},"ra":{},"rs":{},"rf":{},"al":{},"cl":{},"agem":{},"ager":{},"after":{after},"res":{},"lrs":{},"lrr":{}}}"#,
        aead_of(&send),
        send.sealed(),
        send.failed_opens(),
        aead_of(&recv),
        recv.sealed(),
        recv.failed_opens(),
        limits.aes_gcm_packets,
        limits.chacha_failures,
        age / 1_000_000,
        age % 1_000_000,
        b(got),
        b(send.limit_reached()),
        b(recv.limit_reached())
    ));
}

/// The switch numbers worth trying: every varint width boundary, 2^63 - 1, 2^63 (refused) and `u64::MAX`.
fn edge_numbers() -> Vec<u64> {
    let mut v = vec![0u64, 1, 2];
    for j in 1..=63u32 {
        v.extend([(1u64 << j) - 1, 1u64 << j, (1u64 << j) + 1]);
    }
    v.push(u64::MAX);
    v.sort_unstable();
    v.dedup();
    v
}

fn decode_event(tr: &mut Trace, bytes: &[u8]) {
    let (res, ans, share, echo, spn) = match Rekey::decode(bytes) {
        Ok(m) => {
            // An accepted body re-encodes to itself.
            let mut buf = [0u8; MAX_REKEY_LEN];
            let n = m.encode(&mut buf).unwrap();
            assert_eq!(&buf[..n], bytes);
            ("ok", m.answer, m.share.to_vec(), m.echo.to_vec(), m.switch_pn)
        }
        Err(WireError::Unexpected("rekey kind")) => ("kind", false, vec![], vec![], 0),
        Err(WireError::Unexpected("trailing bytes")) => ("trailing", false, vec![], vec![], 0),
        Err(_) => ("other", false, vec![], vec![], 0),
    };
    tr.line(&format!(
        r#"{{"t":"kr","op":"dec","bytes":{},"res":"{res}","ans":{},"share":{},"echo":{},"sl":{}}}"#,
        list(bytes),
        b(ans),
        list(&share),
        list(&echo),
        limbs(spn)
    ));
}

fn codec_events(rng: &mut SplitMix64, tr: &mut Trace) {
    let mut share = [0u8; 32];
    rng.fill(&mut share);
    let mut echo = [0u8; ECHO_LEN];
    rng.fill(&mut echo);
    for answer in [false, true] {
        for (i, &spn) in edge_numbers().iter().enumerate() {
            let m = Rekey {
                answer,
                share,
                echo: if answer { echo } else { [0; ECHO_LEN] },
                switch_pn: if answer { spn } else { 0 },
            };
            let mut buf = [0u8; MAX_REKEY_LEN];
            let e = m.encode(&mut buf);
            let (res, out) = match e {
                Ok(n) => {
                    assert_eq!(
                        n,
                        if answer {
                            33 + ECHO_LEN + vinc_wire::varint::encoded_len(spn)
                        } else {
                            33
                        }
                    );
                    assert_eq!(Rekey::decode(&buf[..n]).unwrap(), m, "decode (encode m) = m");
                    ("ok", buf[..n].to_vec())
                }
                Err(WireError::VarintOverflow) => {
                    assert!(answer && spn >= 1 << 63);
                    ("overflow", vec![])
                }
                Err(other) => panic!("unexpected {other:?}"),
            };
            tr.line(&format!(
                r#"{{"t":"kr","op":"enc","ans":{},"share":{},"echo":{},"sl":{},"res":"{res}","bytes":{}}}"#,
                b(answer),
                list(&share),
                list(&m.echo),
                limbs(spn),
                list(&out)
            ));
            // The refusals are tried on every seventh number and on the largest ones.
            if res != "ok" || (i % 7 != 0 && spn < 1 << 62) {
                continue;
            }
            // The refusals: every cut, a trailing byte, a changed kind, and a non-minimal switch number.
            decode_event(tr, &out);
            for cut in 0..out.len() {
                decode_event(tr, &out[..cut]);
            }
            for extra in [0u8, 1, 128, 255] {
                let mut longer = out.clone();
                longer.push(extra);
                decode_event(tr, &longer);
            }
            for kind in [2u8, 3, 255] {
                let mut other = out.clone();
                other[0] = kind;
                decode_event(tr, &other);
            }
            let mut flipped = out.clone();
            flipped[0] ^= 1;
            decode_event(tr, &flipped);
            if answer {
                let mut padded = out.clone();
                let last = padded.len() - 1;
                padded[last] |= 0x80;
                padded.push(0);
                decode_event(tr, &padded);
            }
        }
    }
    // Random bodies of random length.
    for _ in 0..40 {
        let len = below(rng, 56) as usize;
        let mut body = vec![0u8; len];
        rng.fill(&mut body);
        if !body.is_empty() {
            body[0] = below(rng, 3) as u8;
        }
        decode_event(tr, &body);
    }
}

#[test]
fn key_roll_runs_match_the_models() {
    let mut rng = SplitMix64::new(0x4b45_5952_4f4c_4c31);
    let mut tr = Trace::default();
    for id in 1..=60u32 {
        run(&mut rng, &mut tr, id);
    }
    for _ in 0..200 {
        due_event(&mut rng, &mut tr);
    }
    codec_events(&mut rng, &mut tr);
    // The roll function is the one the keys use: one old secret, two Diffie-Hellman values, two different results.
    let (s, d1, d2) = (Secret::new([5; 32]), Secret::new([6; 32]), Secret::new([7; 32]));
    assert_ne!(roll_secret(&s, &d1).expose(), roll_secret(&s, &d2).expose());
    assert_ne!(tr.0, "");
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("keyroll.ndjson"), &tr.0).unwrap();
    }
}
