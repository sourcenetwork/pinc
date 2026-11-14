//! Trace generation for the node's table of failed dials: seeded runs of a real table (`vinc-node`, built with the
//! `trace` feature), recorded as ndjson (`nobo.ndjson`) for the TLA+ trace check (`TraceNodeBackoff.tla`) and the
//! Lean replay (`Vinc/TraceNodeBackoff.lean`).
//!
//! The table is the node's own (`Io`, over an endpoint that does nothing): the calls are `backoff` (a dial failed),
//! `deny_back` (the peer's access check refused the dial) and `gate`, which hands a frame to the node's own stream
//! hand-off for a peer with no session and nothing queued and so reports exactly the answer of the backoff window
//! check. Times step forward, stand still, step back, land one nanosecond before, on and after the time of an
//! entry, and sit at the top of the `u64` range, where the entry's time saturates. Small runs keep a few peers, hubs
//! and others, so that waits double to their caps and refusals double to theirs; one run fills the table (4096
//! entries) and goes on, so that a full table refuses a new peer and still updates the entries it holds.
//!
//! The test compares every call with a naive table (a map written from the rules in the module docs of `duties.rs`
//! and `io.rs`) and checks the properties itself: the table never passes 4096 entries, a wait is at least the first
//! and at most the cap of its peer (900 s after a refusal), a full table changes nothing for a peer it holds no
//! entry for, and `gate` is false exactly inside the window. After every call the record carries the entry of the
//! peer and the size of the table; a dump of the whole table follows now and then and at the end of a run.
//!
//! One run drives a real node instead (a member over the scripted endpoint of `node_script.rs`) whose session table
//! is full: each dial of a hub comes up and the table sheds the session (`hub_connected`), which is a failed dial.
//! The node's table is a private field, so the run records the shed without an entry, then the node's duty passes
//! and whether each dialed the hub: never before the wait is over (a pass in the middle of it, and one on its last
//! nanosecond), always at its end (on the first nanosecond after it, or half a second after its last), through the
//! waits 2, 4, 8, 16, 16 and 16 s.
//!
//! Not driven here: the guard of `dial_peer` beyond the window (a session, a dial in progress, a revoked peer),
//! the reset of a session that lived 5 s and the table of dials in progress, which are `Node` methods over private
//! fields; those rules are in the models only. The prune runs at every duty pass of the node run but has nothing to
//! let go of there.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::cognitive_complexity,
    unreachable_pub
)]

mod node_script;

use std::collections::BTreeMap;
use std::fmt::Write as _;

use node_script::{DIALED, ScriptNode, hub_alpn, id_of, node_with};
use vinc_core::{Event, SessionId};
use vinc_crypto::NodeId;
use vinc_node::{BackoffProbe, HUB_ALPN, NoApps};
use vinc_tests::SplitMix64;

const MAX: usize = BackoffProbe::TABLE_MAX;
const FIRST: u64 = BackoffProbe::FIRST;
const HUB_CAP: u64 = BackoffProbe::HUB_CAP;
const CAP: u64 = BackoffProbe::CAP;
const DENY_FIRST: u64 = BackoffProbe::DENY_FIRST;
const DENY_CAP: u64 = BackoffProbe::DENY_CAP;
/// The duty cadence of a member node (`DUTY_MEMBER`, `config.rs`): the duty passes of the node run are at least this
/// far apart, so each call of `handle_timeout` there is a duty pass.
const DUTY: u64 = 500_000_000;

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

/// The id of peer number `n`.
fn peer(n: u32) -> [u8; 32] {
    let mut id = [0x11u8; 32];
    id[..4].copy_from_slice(&n.to_le_bytes());
    id
}
fn number(id: &[u8; 32]) -> u32 {
    u32::from_le_bytes(id[..4].try_into().unwrap())
}

/// The naive table: peer number to (time of the next dial, wait).
struct Naive {
    t: BTreeMap<u32, (u64, u64)>,
    hubs: Vec<u32>,
}

impl Naive {
    fn store(&mut self, now: u64, p: u32, back: u64) {
        if self.t.len() < MAX || self.t.contains_key(&p) {
            self.t.insert(p, (now.saturating_add(back), back));
        }
    }
    fn backoff(&mut self, now: u64, p: u32) -> u64 {
        let cap = if self.hubs.contains(&p) { HUB_CAP } else { CAP };
        let back = match self.t.get(&p) {
            None => FIRST,
            Some(&(_, b)) => (b.saturating_mul(2)).min(cap),
        };
        self.store(now, p, back);
        back
    }
    fn deny(&mut self, now: u64, p: u32) -> u64 {
        let back = match self.t.get(&p) {
            Some(&(_, b)) if b >= DENY_FIRST => b.saturating_mul(2).min(DENY_CAP),
            _ => DENY_FIRST,
        };
        self.store(now, p, back);
        back
    }
    fn window(&self, now: u64, p: u32) -> bool {
        self.t.get(&p).is_some_and(|&(u, _)| now < u)
    }
}

#[derive(Default)]
struct Seen {
    hub_cap: u32,
    cap: u32,
    deny_cap: u32,
    deny_from_backoff: u32,
    backoff_after_deny: u32,
    saturated: u32,
    blocked: u32,
    open: u32,
    at_edge: u32,
    refused: u32,
    full_updated: u32,
    stepped_back: u32,
}

fn entry_json(e: Option<(u64, u64)>) -> String {
    e.map_or_else(|| "[]".to_owned(), |(u, b)| format!("[{},{}]", limbs(u), limbs(b)))
}

fn dump(p: &BackoffProbe) -> String {
    let rows: Vec<String> = p
        .entries()
        .iter()
        .map(|(id, u, b)| format!("[{},{},{}]", number(id), limbs(*u), limbs(*b)))
        .collect();
    format!("[{}]", rows.join(","))
}

struct Cfg {
    peers: u32,
    hubs: Vec<u32>,
    steps: u32,
    fill: u32,
    dump_every: u32,
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, cfg: &Cfg, seen: &mut Seen) {
    let hub_ids: Vec<[u8; 32]> = cfg.hubs.iter().map(|n| peer(*n)).collect();
    let mut probe = BackoffProbe::new(&hub_ids);
    let mut naive = Naive {
        t: BTreeMap::new(),
        hubs: cfg.hubs.clone(),
    };
    let hubs_json: Vec<String> = cfg.hubs.iter().map(u32::to_string).collect();
    let _ = writeln!(
        out,
        r#"{{"t":"nobo","run":{id},"op":"init","max":{MAX},"peers":{},"hubs":[{}],"first":{},"hubcap":{},"cap":{},"dfirst":{},"dcap":{}}}"#,
        cfg.peers,
        hubs_json.join(","),
        limbs(FIRST),
        limbs(HUB_CAP),
        limbs(CAP),
        limbs(DENY_FIRST),
        limbs(DENY_CAP)
    );
    let mut last = 0u64;
    let mut denied: BTreeMap<u32, bool> = BTreeMap::new();
    for step in 0..cfg.steps {
        // the peer: while filling, a new peer each time; then any
        let (p, op) = if step < cfg.fill {
            (step + 1, i32::from(rng.next_u64().is_multiple_of(8)))
        } else {
            let p = 1 + (rng.next_u64() % u64::from(cfg.peers)) as u32;
            let op = match rng.next_u64() % 20 {
                0..=8 => 0,
                9..=10 => 1,
                _ => 2,
            };
            (p, op)
        };
        let e0 = naive.t.get(&p).copied();
        // the clock: forward, still, back, the edge of the entry's window, the top of the range
        let pick = rng.next_u64() % 14;
        let now = match pick {
            0 | 1 => last,
            2 => last.saturating_sub(rng.next_u64() % 5_000_000_000),
            3..=5 => last.saturating_add(rng.next_u64() % 40_000_000_000),
            6..=8 => match e0 {
                Some((u, _)) => [u.saturating_sub(1), u, u.saturating_add(1)][(rng.next_u64() % 3) as usize],
                None => last,
            },
            9 => u64::MAX,
            10 => u64::MAX - rng.next_u64() % (2 * DENY_CAP),
            11 => u64::MAX - rng.next_u64() % 4,
            _ => rng.next_u64() % 1_000_000_000_000,
        };
        if now < last {
            seen.stepped_back += 1;
        }
        // the top of the range is a visit: the clock goes on from where it was
        if !(9..=11).contains(&pick) {
            last = now;
        }
        let hub = naive.hubs.contains(&p);
        let was_full = naive.t.len() >= MAX;
        let id32 = peer(p);
        let (name, ok) = match op {
            0 => {
                let back = naive.backoff(now, p);
                probe.backoff(now, &id32);
                let cap = if hub { HUB_CAP } else { CAP };
                assert!(back >= FIRST && back <= cap, "a wait outside its bounds");
                match e0 {
                    None => assert_eq!(back, FIRST),
                    Some((_, b)) => assert_eq!(back, b.saturating_mul(2).min(cap)),
                }
                if e0.is_some_and(|(_, b)| b > cap) {
                    seen.backoff_after_deny += 1;
                }
                seen.hub_cap += u32::from(hub && back == HUB_CAP);
                seen.cap += u32::from(!hub && back == CAP);
                ("backoff", None)
            }
            1 => {
                let back = naive.deny(now, p);
                probe.deny_back(now, &id32);
                assert!(
                    (DENY_FIRST..=DENY_CAP).contains(&back),
                    "a refusal's wait outside its bounds"
                );
                seen.deny_cap += u32::from(back == DENY_CAP);
                seen.deny_from_backoff += u32::from(e0.is_some_and(|(_, b)| b < DENY_FIRST));
                denied.insert(p, true);
                ("deny", None)
            }
            _ => {
                let ok = probe.gate(now, &id32);
                assert_eq!(ok, !naive.window(now, p), "the guard differs from the naive window");
                assert_eq!(ok, e0.is_none_or(|(u, _)| now >= u), "the guard is not `now >= until`");
                seen.blocked += u32::from(!ok);
                seen.open += u32::from(ok && e0.is_some());
                seen.at_edge += u32::from(e0.is_some_and(|(u, _)| now == u || now.saturating_add(1) == u));
                ("gate", Some(ok))
            }
        };
        let e1 = probe.entry(&id32);
        assert_eq!(e1, naive.t.get(&p).copied(), "the entry differs from the naive table");
        assert_eq!(probe.entries().len(), naive.t.len());
        assert!(naive.t.len() <= MAX, "the table passed its bound");
        if op == 2 {
            assert_eq!(e1, e0, "a guard changed the table");
        } else {
            if was_full && e0.is_none() {
                assert!(e1.is_none(), "a full table took a new peer");
                seen.refused += 1;
            }
            if was_full && e0.is_some() {
                assert!(e1.is_some_and(|(_, b)| b >= FIRST));
                seen.full_updated += 1;
            }
            if let Some((u, b)) = e1 {
                assert!(u >= b, "an entry's time is below its wait");
                assert_eq!(
                    u,
                    now.saturating_add(b),
                    "an entry's time is not the failure's plus the wait"
                );
                seen.saturated += u32::from(u == u64::MAX);
            }
        }
        let ok_json = ok.map_or(String::new(), |b| format!(r#","ok":{b}"#));
        let _ = writeln!(
            out,
            r#"{{"t":"nobo","run":{id},"op":"{name}","now":{},"peer":{p}{ok_json},"e":{},"len":{}}}"#,
            limbs(now),
            entry_json(e1),
            naive.t.len()
        );
        if step % cfg.dump_every == cfg.dump_every - 1
            || step + 1 == cfg.steps
            || (cfg.fill > 0 && step + 1 == cfg.fill)
        {
            let _ = writeln!(
                out,
                r#"{{"t":"nobo","run":{id},"op":"dump","entries":{}}}"#,
                dump(&probe)
            );
        }
    }
    // every entry of the probe is the naive one
    let mut mine: Vec<(u32, u64, u64)> = probe.entries().iter().map(|(i, u, b)| (number(i), *u, *b)).collect();
    mine.sort_unstable();
    let theirs: Vec<(u32, u64, u64)> = naive.t.iter().map(|(p, (u, b))| (*p, *u, *b)).collect();
    assert_eq!(mine, theirs);
}

/// A thread with the stack a node needs.
fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// The dials `node` made of `hub` so far.
fn dials_of(node: &mut ScriptNode<NoApps>, hub: &NodeId) -> usize {
    node.endpoint_mut().dials.iter().filter(|d| *d == hub).count()
}

/// A duty pass of `node` at `now`, recorded as a `duty` event of peer 1 (`hub`): whether it dialed the hub.
fn duty(node: &mut ScriptNode<NoApps>, hub: &NodeId, now: u64, out: &mut String, id: u32) -> bool {
    let before = dials_of(node, hub);
    node.handle_timeout(now);
    let dialed = dials_of(node, hub) > before;
    let _ = writeln!(
        out,
        r#"{{"t":"nobo","run":{id},"op":"duty","now":{},"peer":1,"dialed":{dialed}}}"#,
        limbs(now)
    );
    dialed
}

/// The run of a real node: a member with hubs 1 and 2, whose session table 4000 sessions of a member (peer 3) and 96
/// of hub 2 fill. Each dial of hub 1 comes up and the full table sheds the session, a failed dial; the duty passes
/// that follow must not dial the hub before the wait is over and must dial it from then on.
fn shed_run(id: u32) -> String {
    let mut out = String::new();
    let (h1, h2) = (id_of(0x61), id_of(0x62));
    let mut node = node_with(false, &[h1, h2], HUB_ALPN, NoApps::default()).unwrap();
    let _ = writeln!(
        out,
        r#"{{"t":"nobo","run":{id},"op":"init","max":{MAX},"peers":3,"hubs":[1,2],"first":{},"hubcap":{},"cap":{},"dfirst":{},"dcap":{}}}"#,
        limbs(FIRST),
        limbs(HUB_CAP),
        limbs(CAP),
        limbs(DENY_FIRST),
        limbs(DENY_CAP)
    );
    let mut now = 1_000_000_000u64;
    for i in 0..MAX as u64 {
        let peer = if i < MAX as u64 - 96 { id_of(0x41) } else { h2 };
        node.endpoint_mut().events.push_back(Event::Incoming {
            session: SessionId(i),
            node: peer,
            alpn: hub_alpn(),
        });
        if i % 512 == 511 {
            node.poll(now);
            while node.poll_event().is_some() {}
            now += 1_000_000;
        }
    }
    assert!(node.endpoint_mut().closed.is_empty(), "the table took every session");
    assert_eq!(
        dials_of(&mut node, &h1),
        0,
        "the hub was dialed before the first duty pass"
    );
    assert!(
        duty(&mut node, &h1, now, &mut out, id),
        "the first duty pass did not dial the hub"
    );
    let mut back = 0u64;
    for k in 0..6u64 {
        let pos = node.endpoint_mut().dials.iter().rposition(|d| *d == h1).unwrap();
        let session = SessionId(DIALED + pos as u64);
        // the session comes up a little after the dial, later in each round
        let at = now + k * 3_000_000;
        node.endpoint_mut().events.push_back(Event::Connected {
            session,
            node: h1,
            alpn: hub_alpn(),
            resumed: false,
        });
        let closed = node.endpoint_mut().closed.len();
        node.poll(at);
        while node.poll_event().is_some() {}
        assert!(
            node.endpoint_mut().closed[closed..].contains(&session),
            "the full table took the hub session"
        );
        let _ = writeln!(
            out,
            r#"{{"t":"nobo","run":{id},"op":"shed","now":{},"peer":1}}"#,
            limbs(at)
        );
        back = if back == 0 { FIRST } else { (back * 2).min(HUB_CAP) };
        let until = at + back;
        assert!(
            !duty(&mut node, &h1, at + back / 2, &mut out, id),
            "the hub was redialed inside its backoff"
        );
        let open = if k % 2 == 0 {
            assert!(
                !duty(&mut node, &h1, until - 1, &mut out, id),
                "the hub was redialed on the last nanosecond of its backoff"
            );
            until - 1 + DUTY
        } else {
            until
        };
        assert!(
            duty(&mut node, &h1, open, &mut out, id),
            "the hub was not redialed once its backoff was over"
        );
        now = open;
    }
    assert_eq!(back, HUB_CAP, "the waits did not reach the hub cap");
    out
}

#[test]
fn the_failed_dials_match_the_models() {
    let mut rng = SplitMix64::new(0x6e62_0001);
    let mut out = String::new();
    let mut seen = Seen::default();
    for id in 1..=60u32 {
        let cfg = Cfg {
            peers: 5,
            hubs: vec![1, 2, 3],
            steps: 220,
            fill: 0,
            dump_every: 40,
        };
        run(&mut rng, &mut out, id, &cfg, &mut seen);
    }
    for id in 100..110u32 {
        let cfg = Cfg {
            peers: 14,
            hubs: vec![1, 2],
            steps: 150,
            fill: 0,
            dump_every: 40,
        };
        run(&mut rng, &mut out, id, &cfg, &mut seen);
    }
    // the table fills (4096 peers fail once), then goes on over a few more peers than it has room for
    let cfg = Cfg {
        peers: MAX as u32 + 60,
        hubs: vec![1, 2, 3],
        steps: MAX as u32 + 1500,
        fill: MAX as u32,
        dump_every: 700,
    };
    run(&mut rng, &mut out, 900, &cfg, &mut seen);
    // a real node whose full session table sheds every session of its dial of a hub
    out.push_str(&big(|| shed_run(950)));
    assert!(seen.hub_cap > 0, "no hub reached its cap");
    assert!(seen.cap > 0, "no other node reached its cap");
    assert!(seen.deny_cap > 0, "no refusal reached its cap");
    assert!(seen.deny_from_backoff > 0, "no refusal came after a plain failure");
    assert!(seen.backoff_after_deny > 0, "no plain failure came after a refusal");
    assert!(seen.saturated > 0, "no entry's time saturated");
    assert!(
        seen.blocked > 0 && seen.open > 0,
        "the window was never both shut and open"
    );
    assert!(seen.at_edge > 0, "no guard landed on the edge of a window");
    assert!(seen.refused > 0, "a full table never met a new peer");
    assert!(seen.full_updated > 0, "a full table never updated an entry");
    assert!(seen.stepped_back > 0, "the clock never stepped back");
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("nobo.ndjson"), &out).unwrap();
    }
}
