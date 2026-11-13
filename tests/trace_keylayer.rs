//! Trace generation for the flip and hold layer of the key roll: seeded random runs of two real connections
//! (`vinc-transport` with the `trace` feature), recorded as ndjson (`keylayer.ndjson`) for the TLA+ trace check
//! (`TraceKeyLayer.tla`) and the Lean replay (`Vinc/TraceKeyLayer.lean`).
//!
//! A run connects a client and a server, then drives them datagram by datagram through a [`Pair`]: application data
//! is written (every sealed packet counts toward the roll), packets are built, and any datagram of the pool is
//! delivered any number of times, in any order, or never, some with the phase bit flipped by an attacker (the tag
//! then verifies under no key); time moves by explicit steps that also run the timers (loss detection and the
//! resend of a request). What is recorded is what the connection shows through the `trace` feature after every step
//! of its key layer: the phase bits, the sending, staged, current, previous and next keys (fingerprints, so equal
//! ids mean equal secrets), the floors and the hold deadline, the packet numbers, the roll machine and the REKEY
//! message waiting, with the time and probe timeout in force. The checkers replay each step with the operators of the
//! model (`KeyRoll.tla` `BeginOp`, `SendOp`, `DeliverOp`, `RequeueAns`, `RequestLostOp`; `Vinc.KeyRollSys`) and
//! require the state they compute to be the state recorded, with the keys related as symbolic terms (a bijection
//! between ids and terms, as in `trace_keyroll`).
//!
//! The test asserts what it can itself (a packet that opens is the one that was sealed; a message processed is the
//! one the packet carried) so it is meaningful without the proof tools. Times are nanoseconds from the start of the
//! run and stay below 2^31 (the TLA+ checker has 32-bit integers). The trace is written to `VINC_TRACE_DIR` when it
//! is set.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::items_after_statements,
    unreachable_pub
)]

use std::collections::HashMap;

use vinc_crypto::IdentityAlg;
use vinc_security::Rekey;
use vinc_tests::*;
use vinc_transport::conn::{KeyEvent, KeysView, Slot};

const TIME_LIMIT: u64 = (1 << 31) - 1;

/// Dense ids, from 1, for distinct values of one kind in one run.
#[derive(Default)]
struct Ids(HashMap<(u8, Vec<u8>), i64>);

const K_KEY: u8 = 1;
const K_SHARE: u8 = 2;
const K_ECHO: u8 = 3;

impl Ids {
    fn id(&mut self, kind: u8, bytes: &[u8]) -> i64 {
        let next = i64::try_from(self.0.len()).unwrap() + 1;
        *self.0.entry((kind, bytes.to_vec())).or_insert(next)
    }
    fn key(&mut self, fp: u64) -> i64 {
        self.id(K_KEY, &fp.to_le_bytes())
    }
}

fn b(x: bool) -> &'static str {
    if x { "true" } else { "false" }
}

/// What a sealed packet was: its number, phase bit, sealing key and message.
#[derive(Clone)]
struct SentInfo {
    pn: u64,
    phase: bool,
    key: u64,
    rekey: Option<Rekey>,
}

struct Emit<'t> {
    out: &'t mut String,
    ids: Ids,
    base: u64,
    run: u32,
}

impl Emit<'_> {
    /// A time as the trace records it: nanoseconds since the start of the run.
    fn t(&self, abs: u64) -> u64 {
        let rel = abs.checked_sub(self.base).expect("a time before the run");
        assert!(rel <= TIME_LIMIT, "the run is too long for the checkers");
        rel
    }

    fn msg(&mut self, prefix: &str, m: Option<&Rekey>) -> String {
        match m {
            None => format!(r#""{prefix}k":0,"{prefix}sh":-1,"{prefix}to":-1,"{prefix}spn":0"#),
            Some(r) => {
                let sh = self.ids.id(K_SHARE, &r.share);
                let to = if r.answer { self.ids.id(K_ECHO, &r.echo) } else { -1 };
                format!(
                    r#""{prefix}k":{},"{prefix}sh":{sh},"{prefix}to":{to},"{prefix}spn":{}"#,
                    if r.answer { 2 } else { 1 },
                    r.switch_pn
                )
            }
        }
    }

    fn opt_key(&mut self, fp: Option<u64>) -> i64 {
        fp.map_or(-1, |f| self.ids.key(f))
    }

    fn view(&mut self, v: &KeysView) -> String {
        let sk = self.ids.key(v.send_key);
        let stg = self.opt_key(v.staged_send);
        let cur = self.ids.key(v.recv_key);
        let (prev, prev_dl) = v.prev.map_or((-1, 0), |(k, dl)| (self.ids.key(k), self.t(dl)));
        let (next, floor) = v.next.map_or((-1, 0), |(k, fl)| (self.ids.key(k), fl));
        let pend = v.pending.as_ref().map_or(-1, |r| self.ids.id(K_SHARE, &r.share));
        let (last, last_sh) = v.last.as_ref().map_or((-1, -1), |(sh, a)| {
            (self.ids.id(K_SHARE, sh), self.ids.id(K_SHARE, &a.share))
        });
        let out = self.msg("o", v.out.as_ref());
        let lans = self.msg("l", v.last_answer.as_ref());
        let req_at = v.request_at.map_or(-1, |t| i64::try_from(self.t(t)).unwrap());
        format!(
            r#""sph":{},"sk":{sk},"stg":{stg},"rph":{},"cur":{cur},"first":{},"prev":{prev},"prevdl":{prev_dl},"next":{next},"floor":{floor},"npn":{},"idle":{},"pend":{pend},"last":{last},"lastsh":{last_sh},"rolls":{},"reqat":{req_at},{out},{lans}"#,
            b(v.send_phase),
            b(v.recv_phase),
            v.first_pn,
            v.next_pn,
            b(v.idle),
            v.rolls
        )
    }

    fn line(&mut self, s: &str) {
        self.out.push_str(s);
        self.out.push('\n');
    }
}

fn node(a: bool) -> u8 {
    u8::from(!a)
}

/// Run one seeded connection and append its events to `out`.
fn run(rng: &mut SplitMix64, out: &mut String, run: u32) -> bool {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.key_update_after = 6 + rng.next_u64() % 4;
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(run.into(), Params::new(MS)));
    assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
    let mut pair = Pair::from_net(net);
    let (ia, ib) = (pair.a.conn.open_bi().unwrap(), pair.b.conn.open_bi().unwrap());
    pair.settle();
    pair.events.clear();
    pair.pool.clear();
    let mut em = Emit {
        out,
        ids: Ids::default(),
        base: pair.now,
        run,
    };
    // The model starts at generation 0 with nothing staged and no roll under way; a run whose connection rolled
    // while it connected (a small `key_update_after`) is not recorded.
    let (va, vb) = (pair.a.conn.trace_keys().unwrap(), pair.b.conn.trace_keys().unwrap());
    let clean =
        |v: &KeysView| v.staged_send.is_none() && v.prev.is_none() && v.next.is_none() && v.idle && v.rolls == 0;
    if !(clean(&va) && clean(&vb)) {
        return false;
    }
    assert_eq!(va.send_key, vb.recv_key, "one secret per direction");
    assert_eq!(vb.send_key, va.recv_key);
    assert!(!va.send_phase && !va.recv_phase && !vb.send_phase && !vb.recv_phase);
    let (v0, v1) = (em.view(&va), em.view(&vb));
    let run_id = em.run;
    em.line(&format!(
        r#"{{"t":"kl","op":"init","run":{run_id},"a":{{{v0}}},"b":{{{v1}}}}}"#
    ));

    let mut sent: HashMap<usize, SentInfo> = HashMap::new();
    let mut logged = 0;
    let data = pattern(1000, 11);
    let steps = 150 + rng.next_u64() % 100;
    for _ in 0..steps {
        if pair.now - em.base > 1_500_000_000 {
            break;
        }
        let mut delivered: Option<(usize, bool)> = None;
        match rng.next_u64() % 12 {
            0..=2 => {
                let a = rng.next_u64().is_multiple_of(2);
                let id = if a { ia } else { ib };
                let _ = pair.node(a).conn.write(id, &data);
                pair.pump(a);
            }
            3 | 4 => {
                let a = rng.next_u64().is_multiple_of(2);
                pair.pump(a);
            }
            5..=9 => {
                if pair.pool.is_empty() {
                    continue;
                }
                let idx = (rng.next_u64() % pair.pool.len() as u64) as usize;
                let forged = rng.next_u64().is_multiple_of(10);
                if forged {
                    // The key phase bit is the 0x10 bit of the first byte, which header protection masks: flipping
                    // it flips the bit the receiver reads and breaks the tag.
                    pair.deliver_with(idx, |bytes| bytes[0] ^= 0x10);
                } else {
                    pair.deliver(idx);
                }
                delivered = Some((idx, forged));
            }
            _ => {
                pair.advance(1 + rng.next_u64() % 40_000_000);
                pair.pump(true);
                pair.pump(false);
            }
        }
        // Record what the step did.
        while logged < pair.events.len() {
            let l = pair.events[logged].clone();
            logged += 1;
            if let (
                KeyEvent::Sent {
                    pn, phase, key, rekey, ..
                },
                Some(d),
            ) = (&l.ev, l.dgram)
            {
                sent.insert(
                    d,
                    SentInfo {
                        pn: *pn,
                        phase: *phase,
                        key: *key,
                        rekey: *rekey,
                    },
                );
            }
            emit(&mut em, &l, delivered, &sent);
        }
    }
    // Keep the runs apart in the id space: the next run starts with new ids.
    em.line(&format!(r#"{{"t":"kl","op":"end","run":{run_id}}}"#));
    true
}

fn emit(em: &mut Emit<'_>, l: &Logged, delivered: Option<(usize, bool)>, sent: &HashMap<usize, SentInfo>) {
    let n = node(l.a);
    let run = em.run;
    match &l.ev {
        KeyEvent::Begun { now } => {
            let t = em.t(*now);
            let v = post_json(em, l);
            em.line(&format!(
                r#"{{"t":"kl","op":"begin","run":{run},"n":{n},"now":{t},{v}}}"#
            ));
        }
        KeyEvent::Sent {
            now,
            pto,
            pn,
            phase,
            key,
            rekey,
        } => {
            let t = em.t(*now);
            let k = em.ids.key(*key);
            let m = em.msg("m", rekey.as_ref());
            let v = post_json(em, l);
            em.line(&format!(
                r#"{{"t":"kl","op":"send","run":{run},"n":{n},"now":{t},"pto":{pto},"pn":{pn},"ph":{},"key":{k},{m},{v}}}"#,
                b(*phase)
            ));
        }
        KeyEvent::Received {
            now,
            pto,
            pn,
            phase,
            slot,
            opened,
            dup,
            promoted,
            rekey,
        } => {
            let (idx, forged) = delivered.expect("a packet arrived outside a delivery");
            let info = sent
                .get(&idx)
                .unwrap_or_else(|| panic!("datagram {idx} has no sealed packet"));
            let t = em.t(*now);
            let k = em.ids.key(info.key);
            // The packet the connection read is the one that was sealed (the flipped bit is the attacker's).
            assert_eq!(
                *pn, info.pn,
                "the number read is the number sealed: {l:?} forged {forged}"
            );
            assert_eq!(
                *phase,
                info.phase != forged,
                "the phase bit read is the one on the wire"
            );
            assert!(!(forged && *opened), "a packet with a flipped phase bit opened");
            if *opened && !*dup {
                assert_eq!(rekey, &info.rekey, "the message acted on is the one the packet carried");
            }
            if *dup || !*opened {
                assert!(rekey.is_none());
            }
            let slot = match slot {
                Some(Slot::Current) => 0,
                Some(Slot::Previous) => 1,
                Some(Slot::Next) => 2,
                None => 3,
            };
            let m = em.msg("m", info.rekey.as_ref());
            let v = post_json(em, l);
            em.line(&format!(
                r#"{{"t":"kl","op":"recv","run":{run},"n":{n},"now":{t},"pto":{pto},"pn":{pn},"ph":{},"key":{k},"forged":{},"slot":{slot},"opened":{},"dup":{},"promoted":{},{m},{v}}}"#,
                b(info.phase),
                b(forged),
                b(*opened),
                b(*dup),
                b(*promoted)
            ));
        }
        KeyEvent::AnswerRequeued => {
            em.line(&format!(r#"{{"t":"kl","op":"requeue","run":{run},"n":{n}}}"#));
        }
        KeyEvent::RequestLost => {
            em.line(&format!(r#"{{"t":"kl","op":"rlost","run":{run},"n":{n}}}"#));
        }
    }
}

/// The key state right after a step, as the `v` field (`null` for a loss event, which has none).
fn post_json(em: &mut Emit<'_>, l: &Logged) -> String {
    l.view
        .as_ref()
        .map_or_else(|| r#""v":null"#.to_string(), |v| format!(r#""v":{{{}}}"#, em.view(v)))
}

#[test]
fn key_layer_runs_match_the_models() {
    big_stack(|| {
        let mut rng = SplitMix64::traced(0x4b45_594c_4159_4552);
        let mut out = String::new();
        let mut recorded = 0;
        for run_id in 1..=40u32 {
            recorded += usize::from(run(&mut rng, &mut out, run_id));
        }
        assert!(recorded >= 10, "only {recorded} runs started clean");
        assert!(out.contains(r#""op":"recv""#) && out.contains(r#""op":"send""#));
        // The runs reach the interesting steps: a roll begun, an answer taken and the staged key promoted, a late
        // packet under the previous key, a forged phase bit.
        assert!(out.contains(r#""op":"begin""#), "no roll began");
        assert!(out.contains(r#""promoted":true"#), "no key was promoted");
        assert!(out.contains(r#""slot":1"#), "no packet opened under the previous key");
        assert!(out.contains(r#""forged":true"#), "no forged packet");
        if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("keylayer.ndjson"), &out).unwrap();
        }
    });
}
