//! `pinc-membership`: the hub stream codec on hostile bytes, the incarnation under store failures, and the whole
//! membership machine (member and hub) driven by sequences of session events, remote frames, carrier changes,
//! revocations and timers, with its documented invariants checked after every step.
//!
//! Where the expected behaviour comes from:
//! - `pinc_membership` crate docs: "Invariants: all tables are bounded; no input panics; the same inputs produce the
//!   same outputs." and "Incarnations only go up, across restarts and clock jumps."
//! - `codec`: "[`Frame::parse`] and [`Frame::read`] never panic and never read outside the input; a frame that parses
//!   encodes back to the same bytes; the body of a frame is at most [`MAX_BODY`] bytes."
//! - `incarnation`: "[`Incarnation::word`] never decreases over the life of the value; a new epoch is sealed before
//!   the word that carries it is returned"; `next_record` and `observe`: "the value is unchanged" on an error.
//! - `view`: "the view epoch only increases ...; the view never lists the node itself; a revoked node is never
//!   listed". `node`: "every table is bounded by [`MAX_TABLE`] or [`MAX_HUBS`]". `event`: the queues are bounded and a
//!   gap is delivered as `Lost`. `Event::ViewChanged`: "the epoch only increases".
//! - `session`: the machine never sends to itself, and `revoke`: "close every session with it. Effective within this
//!   call", so nothing is sent to a revoked peer afterwards.

use std::collections::{BTreeMap, BTreeSet};

use ephyra::prelude::*;
use pinc_membership::codec::{Alive, Entry, Hello, MAX_BODY, Other, Path, Probe, Proof, Snap, entry_bytes, ty};
use pinc_membership::consts::{MAX_TABLE, QUEUE_CAP};
use pinc_membership::incarnation::{Incarnation, IncarnationError};
use pinc_membership::session::{LEAVE_CODE, StoreError};
use pinc_membership::{
    Broadcast, Carrier, CloseReason, Config, Event, Evidence, Frame, Local, Membership, NodeId, Record, Route, Session,
};

const MS: u64 = 1_000_000;
const SEC: u64 = 1_000_000_000;

fn id(i: u8) -> NodeId {
    [i + 1; 32]
}

// ---------------------------------------------------------------------------------------------------------------
// The host.

#[derive(Debug, Default)]
struct Host {
    sessions: BTreeSet<NodeId>,
    ev: BTreeMap<NodeId, Evidence>,
    carriers: BTreeMap<NodeId, Carrier>,
    floor_len: usize,
    persistent: bool,
    sealed: Option<u64>,
    fail_seal: bool,
    reflexive: bool,
    /// Everything the machine did, in order, for the determinism check and the sent-frame checks.
    log: Vec<String>,
    sent: Vec<(NodeId, Route, Vec<u8>)>,
}

impl Session for Host {
    fn send(&mut self, peer: &NodeId, route: Route, frame: &[u8]) -> bool {
        self.sent.push((*peer, route, frame.to_vec()));
        self.log.push(format!("send {:?} {route:?} {frame:?}", peer[0]));
        self.sessions.contains(peer)
    }
    fn evidence(&self, peer: &NodeId) -> Option<Evidence> {
        self.ev.get(peer).copied()
    }
    fn carrier(&self, member: &NodeId) -> Carrier {
        self.carriers.get(member).copied().unwrap_or_default()
    }
    fn close(&mut self, peer: &NodeId, reason: CloseReason) {
        self.log.push(format!("close {:?} {reason:?}", peer[0]));
    }
}

impl Broadcast for Host {
    fn floor(&mut self, member: &NodeId, out: &mut [u8]) -> usize {
        // A broadcast layer may claim more than the buffer holds; the machine must cap it.
        let n = self.floor_len.min(out.len());
        out[..n].fill(member[0]);
        self.floor_len
    }
    fn frame(&mut self, from: &NodeId, ty: u8, topic: &[u8], rest: &[u8]) {
        self.log.push(format!("frame {:?} {ty} {topic:?} {}", from[0], rest.len()));
    }
    fn hold(&mut self, member: &NodeId) {
        self.log.push(format!("hold {:?}", member[0]));
    }
    fn restore(&mut self, member: &NodeId) {
        self.log.push(format!("restore {:?}", member[0]));
    }
    fn release(&mut self, member: &NodeId) {
        self.log.push(format!("release {:?}", member[0]));
    }
    fn resubscribe(&mut self, hub: &NodeId) {
        self.log.push(format!("resub {:?}", hub[0]));
    }
    fn primary_changed(&mut self, old: Option<&NodeId>, new: &NodeId) {
        self.log.push(format!("primary {:?} {:?}", old.map(|o| o[0]), new[0]));
    }
}

impl Local for Host {
    fn version(&self) -> u16 {
        7
    }
    fn reflexive_known(&self) -> bool {
        self.reflexive
    }
    fn address_hash(&self, moves: u8) -> [u8; 8] {
        [moves, 0, 0, 0, 0, 0, 0, 9]
    }
    fn persistent(&self) -> bool {
        self.persistent
    }
    fn unseal_counter(&mut self) -> Result<Option<u64>, StoreError> {
        Ok(self.sealed)
    }
    fn seal_counter(&mut self, epoch: u64) -> Result<(), StoreError> {
        if self.fail_seal {
            return Err(StoreError);
        }
        self.sealed = Some(epoch);
        Ok(())
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The incarnation.

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum IncOp {
    Next,
    /// Observe a word relative to the current one (`delta` added, wrapping) or an absolute edge.
    Observe(i32, #[ephyra(gen = gens::int(0u8..=4))] u8),
    FailSeal(bool),
}

fn inc_cases() -> impl Gen<Value = ((bool, u64, u64, Option<u64>), Vec<IncOp>)> {
    let big = gens::frequency(vec![
        (4, gens::int(0u64..=2_000).boxed()),
        (1, gens::int((1u64 << 48) - 4..=(1u64 << 48) + 2).boxed()),
        (1, gens::edges(0u64..=u64::MAX).boxed()),
    ])
    .boxed();
    let sealed = gens::frequency(vec![
        (2, gens::constant(None).boxed()),
        (1, gens::int(0u64..=2_000).map(Some).boxed()),
        (1, gens::int((1u64 << 48) - 3..=(1u64 << 48) + 1).map(Some).boxed()),
    ]);
    (
        (gens::bool(), big.clone(), big, sealed),
        gens::vec(ephyra::any::<IncOp>()).len(0..=80),
    )
}

/// The incarnation word never decreases, an error leaves it unchanged, the epoch is sealed before a word carrying it
/// is returned, and the sequence never wraps within an epoch.
#[ephyra::test(gen = inc_cases(), tests = 10_000)]
fn incarnation_only_goes_up(case: ((bool, u64, u64, Option<u64>), Vec<IncOp>)) {
    let ((persistent, wall_ms, floor, sealed), ops) = case;
    let mut host = Host { persistent, sealed, ..Host::default() };
    let Ok(mut inc) = Incarnation::start(&mut host, wall_ms, floor) else {
        return;
    };
    let base = sealed.filter(|_| persistent).unwrap_or(0).max(floor);
    assert!(inc.epoch() > base, "the first epoch is above every remembered one");
    if !persistent {
        assert!(inc.epoch() > wall_ms, "a clock epoch is above the wall clock");
    }
    for (i, op) in ops.iter().enumerate() {
        let before = inc;
        let word = inc.word();
        let got: Result<bool, IncarnationError> = match op {
            IncOp::Next => inc.next_record(&mut host).map(|w| {
                assert_eq!(w, inc.word(), "step {i}: the returned word is the current one");
                true
            }),
            IncOp::Observe(delta, kind) => {
                let seen = match kind {
                    0 => word.wrapping_add_signed(i64::from(*delta)),
                    1 => (word | 0xffff).wrapping_add_signed(i64::from(*delta)),
                    2 => u64::MAX.wrapping_add_signed(i64::from(*delta).min(0)),
                    3 => ((1u64 << 48) - 1) << 16,
                    _ => word.wrapping_add(1u64 << 16),
                };
                let r = inc.observe(&mut host, seen);
                if let Ok(changed) = r {
                    assert_eq!(changed, seen > word, "step {i}: observe changes the word exactly when it is above");
                    assert!(inc.word() > seen || !changed, "step {i}: the word moved above the observed one");
                }
                r
            },
            IncOp::FailSeal(f) => {
                host.fail_seal = *f;
                Ok(false)
            },
        };
        match got {
            Ok(_) => assert!(inc.word() >= word, "step {i}: {op:?}: the word went down"),
            Err(_) => assert_eq!(inc, before, "step {i}: {op:?}: an error changed the value"),
        }
        assert!(inc.epoch() < 1 << 48, "step {i}: the epoch fits 48 bits");
        assert_eq!(inc.word() >> 16, inc.epoch(), "step {i}: the word carries the epoch");
        if persistent && inc.epoch() != before.epoch() {
            assert_eq!(host.sealed, Some(inc.epoch()), "step {i}: a new epoch was used before it was sealed");
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Frames.

/// A frame described by small numbers, built with the codec's own constructors so it is valid by construction.
#[derive(Debug, Clone, ephyra::Arbitrary)]
enum FrameSpec {
    Hello(#[ephyra(gen = rec_spec())] RecSpec, bool, bool),
    Ack,
    Probe,
    Delta(#[ephyra(gen = peer())] u8, #[ephyra(gen = rec_spec())] RecSpec, #[ephyra(gen = gens::int(0u8..=2))] u8),
    Snap(bool, bool, #[ephyra(gen = gens::vec((peer(), rec_spec())).len(0..=6))] Vec<(u8, RecSpec)>),
    Down(
        #[ephyra(gen = peer())] u8,
        #[ephyra(gen = rec_spec())] RecSpec,
        u32,
        #[ephyra(gen = gens::vec((gens::int(0u32..=20_000), gens::int(0u8..=2))).len(1..=4))] Vec<(u32, u8)>,
    ),
    Other(#[ephyra(gen = gens::int(0u8..=20))] u8, #[ephyra(gen = gens::int(0usize..=4))] usize, #[ephyra(gen = gens::int(0usize..=40))] usize),
}

/// A peer index: mostly the two default hubs and two members, sometimes any id (0 is the node itself).
fn peer() -> BoxGen<u8> {
    gens::frequency(vec![(3, gens::int(1u8..=4).boxed()), (1, gens::int(0u8..=7).boxed())]).boxed()
}

/// A record: the incarnation chosen relative to what the machine knows (its own word, or a fixed small one) so that
/// older, equal and newer records all appear.
#[derive(Debug, Clone, Copy)]
struct RecSpec {
    kind: u8,
    delta: i8,
    ver: u8,
    thash: u8,
}

fn rec_spec() -> impl Gen<Value = RecSpec> {
    (gens::int(0u8..=4), gens::int(-3i8..=3), gens::int(6u8..=8), gens::int(0u8..=2))
        .map(|(kind, delta, ver, thash)| RecSpec { kind, delta, ver, thash })
}

fn rec_of(s: RecSpec, mine: u64) -> Record {
    let base = match s.kind {
        0 => mine,
        1 => 5 << 16,
        2 => 9 << 16,
        3 => u64::MAX,
        _ => mine.wrapping_add(1 << 16),
    };
    Record { inc: base.wrapping_add_signed(i64::from(s.delta)), ver: u16::from(s.ver), thash: [s.thash; 8] }
}

fn alive_of(a: u8) -> Alive {
    match a {
        0 => Alive::Down,
        1 => Alive::Alive,
        _ => Alive::Left,
    }
}

fn path_of(p: u8) -> Path {
    match p {
        0 => Path::Session,
        1 => Path::Direct,
        _ => Path::Relay,
    }
}

/// The encoded frame, length prefix included.
fn encode_spec(spec: &FrameSpec, mine: u64) -> Vec<u8> {
    let mut out = vec![0u8; 4096];
    let members: Vec<NodeId> = (0..8).map(id).collect();
    let mut entries = Vec::new();
    let topic = [0x41u8; 4];
    let rest = [0x52u8; 40];
    let f = match spec {
        FrameSpec::Hello(r, snap, homed) => Frame::Hello(Hello { rec: rec_of(*r, mine), snap: *snap, homed: *homed }),
        FrameSpec::Ack => Frame::Ack,
        FrameSpec::Probe => Frame::Probe,
        FrameSpec::Delta(m, r, a) => {
            Frame::Delta(Entry { member: &members[usize::from(*m)], rec: rec_of(*r, mine), alive: alive_of(*a) })
        },
        FrameSpec::Snap(partial, more, es) => {
            for (m, r) in es {
                entries.extend_from_slice(&entry_bytes(&members[usize::from(*m)], &rec_of(*r, mine), Alive::Alive));
            }
            Frame::Snap(Snap::new(*partial, *more, &entries).expect("whole alive entries"))
        },
        FrameSpec::Down(m, r, silence, ps) => {
            let probes: Vec<Probe> = ps.iter().map(|&(age_ms, p)| Probe { age_ms, path: path_of(p) }).collect();
            Frame::Down(pinc_membership::codec::Down {
                member: &members[usize::from(*m)],
                inc: rec_of(*r, mine).inc,
                proof: Proof::new(*silence, &probes).expect("one to four probes"),
            })
        },
        FrameSpec::Other(t, tl, rl) => {
            // Types the membership owns are skipped, as is a topic on them: those are not `Other` frames.
            let t = if matches!(*t, ty::HELLO | ty::ACK | ty::DELTA | ty::SNAP | ty::PROBE | ty::DOWN) { 0x20 } else { *t };
            Frame::Other(Other { ty: t, topic: &topic[..*tl], rest: &rest[..*rl] })
        },
    };
    let n = f.encode(&mut out).expect("a small frame encodes").len();
    out.truncate(n);
    out
}

// ---------------------------------------------------------------------------------------------------------------
// The codec on its own.

fn hostile_stream() -> impl Gen<Value = Vec<u8>> {
    let specs = gens::vec(ephyra::any::<FrameSpec>()).len(1..=4);
    (specs, gens::int(0usize..=3), gens::vec(gens::int(0usize..=400)).len(0..=3))
        .map(|(specs, mode, cuts)| {
            let mut b: Vec<u8> = specs.iter().flat_map(|s| encode_spec(s, 3 << 16)).collect();
            for c in cuts {
                if b.is_empty() {
                    break;
                }
                let at = c % b.len();
                match mode {
                    0 => b[at] ^= 0x01,
                    1 => b[at] = 0xff,
                    2 => b.truncate(at),
                    _ => b.insert(at, 0),
                }
            }
            b
        })
        .with_shrink(pinc_pbt::shrink_bytes)
}

/// A stream of frames, honest or damaged: reading never panics or reads past the input, each frame read uses its
/// length prefix plus its body, and each frame that parses encodes back to exactly the bytes it was read from.
#[ephyra::test(gen = hostile_stream(), tests = 20_000)]
fn frame_stream_reads_back_canonically(buf: Vec<u8>) {
    let mut at = 0usize;
    let mut out = vec![0u8; buf.len() + 16];
    for _ in 0..64 {
        let Some(rest) = buf.get(at..) else { break };
        match Frame::read(rest) {
            Ok(Some((f, n))) => {
                assert!(n >= 6 && n <= rest.len(), "the frame used {n} of {} bytes", rest.len());
                let body = u32::from_be_bytes(rest[..4].try_into().expect("four bytes")) as usize;
                assert_eq!(n, 4 + body, "the frame used its length prefix and body");
                assert!(body <= MAX_BODY);
                let enc = f.encode(&mut out).expect("a frame that parses encodes");
                assert_eq!(enc, &rest[..n], "the frame did not encode back to its bytes");
                at += n;
            },
            Ok(None) => {
                let short = rest.len() < 4 || 4 + u32::from_be_bytes(rest[..4].try_into().expect("four")) as usize > rest.len();
                assert!(short, "more bytes asked for with a whole frame present");
                break;
            },
            Err(_) => break,
        }
    }
}

/// `read_with` with a raised limit: what it accepts must still be a frame of the codec, so it encodes back to the
/// same bytes (the codec's invariant names no exception for the raised limit).
///
/// Triaged as intended: `Frame::read_with` and `Membership::set_max_frame` document the raised limit for frames of
/// the broadcast layer, which builds those frames itself; only the module sentence "the body of a frame is at most
/// MAX_BODY bytes" is stale. `Frame::encode` refuses them with `TooLarge` (codec.rs:452). Kept, ignored, as the record.
#[ephyra::test(gen = (gens::int(0usize..=3), gens::int(0u8..=1)), tests = 8)]
#[ignore = "intended: the raised read limit has no matching encode limit; see the doc comment"]
fn raised_limit_frames_encode_back(case: (usize, u8)) {
    let (extra, t) = case;
    let len = MAX_BODY + 1 + extra;
    let mut buf = Vec::with_capacity(4 + len);
    buf.extend_from_slice(&u32::try_from(len).expect("fits").to_be_bytes());
    buf.push(if t == 0 { ty::FLOOR } else { 0x30 });
    buf.push(0);
    buf.resize(4 + len, 0x5a);
    let Ok(Some((f, n))) = Frame::read_with(&buf, 2 * MAX_BODY) else {
        panic!("a raised limit refused a frame under it");
    };
    assert_eq!(n, buf.len());
    let mut out = vec![0u8; buf.len() + 8];
    let enc = f.encode(&mut out).map(<[u8]>::to_vec);
    assert_eq!(enc, Ok(buf), "a frame read under the raised limit does not encode back");
}

// ---------------------------------------------------------------------------------------------------------------
// The machine.

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum Op {
    Up(#[ephyra(gen = peer())] u8, bool),
    Down(#[ephyra(gen = peer())] u8, #[ephyra(gen = gens::int(0u8..=2))] u8),
    Frame(#[ephyra(gen = peer())] u8, FrameSpec),
    /// Several frames in one buffer, the last possibly cut.
    Frames(#[ephyra(gen = peer())] u8, #[ephyra(gen = gens::vec(ephyra::any::<FrameSpec>()).len(1..=3))] Vec<FrameSpec>, #[ephyra(gen = gens::int(0usize..=3))] usize),
    Raw(#[ephyra(gen = peer())] u8, #[ephyra(gen = pinc_pbt::bytes(24))] Vec<u8>),
    Advance(#[ephyra(gen = gens::frequency(vec![(6, gens::int(0u64..=3 * SEC).boxed()), (2, gens::int(3 * SEC..=100 * SEC).boxed()), (1, gens::constant(0u64).boxed())]))] u64),
    Timeout,
    Evidence(#[ephyra(gen = peer())] u8, #[ephyra(gen = gens::int(0u64..=90 * SEC))] u64, #[ephyra(gen = gens::int(0u32..=3))] u32, bool),
    NoEvidence(#[ephyra(gen = peer())] u8),
    Carrier(#[ephyra(gen = peer())] u8, #[ephyra(gen = gens::int(0u8..=3))] u8),
    CarrierGone(#[ephyra(gen = peer())] u8),
    CarrierReturn(#[ephyra(gen = peer())] u8),
    Revoke(#[ephyra(gen = peer())] u8),
    Unrevoke(#[ephyra(gen = peer())] u8),
    Snapshot(#[ephyra(gen = peer())] u8),
    PushFloor(#[ephyra(gen = peer())] u8),
    Moved,
    Reflexive(bool),
    FailSeal(bool),
    MaxFrame(#[ephyra(gen = gens::int(0usize..=2 * MAX_BODY))] usize),
    Leave,
    /// A member attaches: its session comes up (it dialed) and its HELLO asks for a snapshot.
    Attach(#[ephyra(gen = peer())] u8, #[ephyra(gen = rec_spec())] RecSpec, bool),
    /// A hub link: the session comes up (this node dialed), the transport hears the hub, and the hub answers with a
    /// snapshot of the given members.
    Link(#[ephyra(gen = peer())] u8, #[ephyra(gen = gens::vec((peer(), rec_spec())).len(0..=4))] Vec<(u8, RecSpec)>),
}

/// A node setup: whether it is a hub, its hub list (ids 1 and 2, possibly itself, possibly a member id), persistence
/// and its start clock.
fn machine_cases() -> impl Gen<Value = ((bool, u8, bool, u64, usize), Vec<Op>)> {
    (
        (gens::bool(), gens::int(0u8..=15), gens::bool(), gens::int(0u64..=5_000), gens::int(0usize..=5000)),
        gens::vec(ephyra::any::<Op>()).len(0..=100),
    )
}

/// The ids 0..8: 0 is the node itself, 1 and 2 hubs by default, the rest members.
fn hub_list(mask: u8) -> Vec<NodeId> {
    let mut v = vec![id(1), id(2)];
    if mask & 1 != 0 {
        v.push(id(0));
    }
    if mask & 2 != 0 {
        v.push(id(3));
    }
    if mask & 4 != 0 {
        v.swap(0, 1);
    }
    if mask & 8 != 0 {
        v.push(id(1));
    }
    v
}

/// The log of one run: every host call and every event, for the determinism check.
fn run_machine(setup: (bool, u8, bool, u64, usize), ops: &[Op]) -> Vec<String> {
    let (is_hub, mask, persistent, wall_ms, floor_len) = setup;
    let me = id(0);
    let hubs = hub_list(mask);
    let cfg = Config { me, is_hub, hubs: &hubs, trace: true };
    let mut h = Host { persistent, floor_len, reflexive: true, ..Host::default() };
    let mut now: u64 = 1_000 * SEC;
    let mut m = Membership::start(&cfg, &mut h, now, wall_ms, 0).expect("a valid start");
    let mut revoked: BTreeSet<NodeId> = BTreeSet::new();
    let mut epoch = m.view_epoch();
    let mut last_view_event: Option<u64> = None;
    let mut inc = m.incarnation();
    let mut log: Vec<String> = Vec::new();
    for (i, op) in ops.iter().enumerate() {
        let step = format!("step {i}: {op:?}");
        let mine = m.incarnation();
        let before: BTreeSet<NodeId> = m.members().map(|(k, _)| *k).collect();
        match op {
            Op::Up(p, incoming) => {
                if !revoked.contains(&id(*p)) {
                    h.sessions.insert(id(*p));
                }
                m.session_up(&mut h, now, &id(*p), *incoming);
            },
            Op::Down(p, c) => {
                h.sessions.remove(&id(*p));
                let code = [0, LEAVE_CODE, 3][usize::from(*c)];
                m.session_down(&mut h, now, &id(*p), code);
            },
            Op::Frame(p, spec) => {
                let b = encode_spec(spec, mine);
                let used = m.on_bytes(&mut h, now, &id(*p), &b);
                assert_eq!(used, Ok(b.len()), "{step}: a valid frame was not read whole");
            },
            Op::Frames(p, specs, cut) => {
                let mut b: Vec<u8> = specs.iter().flat_map(|s| encode_spec(s, mine)).collect();
                b.truncate(b.len().saturating_sub(*cut));
                let used = m.on_bytes(&mut h, now, &id(*p), &b);
                assert!(used.is_ok_and(|u| u <= b.len()), "{step}: {used:?}");
            },
            Op::Raw(p, b) => {
                let used = m.on_bytes(&mut h, now, &id(*p), b);
                assert!(used.is_err() || used.is_ok_and(|u| u <= b.len()), "{step}");
            },
            Op::Advance(dt) => {
                now += dt;
                m.on_timeout(&mut h, now);
            },
            Op::Timeout => {
                now = now.max(m.poll_timeout());
                m.on_timeout(&mut h, now);
            },
            Op::Evidence(p, ago, pto, direct) => {
                let e = Evidence { last_rx: now.saturating_sub(*ago), srtt: 30 * MS, pto: *pto, inflight: 0, direct: *direct };
                h.ev.insert(id(*p), e);
            },
            Op::NoEvidence(p) => {
                h.ev.remove(&id(*p));
            },
            Op::Carrier(p, c) => {
                let c = match c {
                    0 => Carrier::Unknown,
                    1 => Carrier::Open,
                    2 => Carrier::Gone { since: now, sleep: None },
                    _ => Carrier::Gone { since: now.saturating_sub(2 * SEC), sleep: Some(now.saturating_sub(SEC)) },
                };
                h.carriers.insert(id(*p), c);
            },
            Op::CarrierGone(p) => {
                h.carriers.insert(id(*p), Carrier::Gone { since: now, sleep: None });
                m.carrier_gone(&mut h, now, &id(*p));
            },
            Op::CarrierReturn(p) => {
                h.carriers.insert(id(*p), Carrier::Open);
                m.carrier_return(&mut h, now, &id(*p));
            },
            Op::Revoke(p) => {
                if m.revoke(&mut h, now, &id(*p)).is_ok() {
                    revoked.insert(id(*p));
                    h.sessions.remove(&id(*p));
                }
            },
            Op::Unrevoke(p) => {
                assert_eq!(m.unrevoke(&id(*p)), revoked.remove(&id(*p)), "{step}");
            },
            Op::Snapshot(p) => m.snapshot_to(&mut h, now, &id(*p)),
            Op::PushFloor(p) => m.push_floor(&mut h, &id(*p)),
            Op::Moved => m.address_changed(now),
            Op::Reflexive(r) => h.reflexive = *r,
            Op::FailSeal(f) => h.fail_seal = *f,
            Op::MaxFrame(n) => {
                m.set_max_frame(*n);
                assert_eq!(m.max_frame(), (*n).max(MAX_BODY), "{step}");
            },
            Op::Leave => m.leave(&mut h),
            Op::Attach(p, r, homed) => {
                if !revoked.contains(&id(*p)) {
                    h.sessions.insert(id(*p));
                }
                m.session_up(&mut h, now, &id(*p), true);
                let b = encode_spec(&FrameSpec::Hello(*r, true, *homed), mine);
                assert_eq!(m.on_bytes(&mut h, now, &id(*p), &b), Ok(b.len()), "{step}");
            },
            Op::Link(p, es) => {
                if !revoked.contains(&id(*p)) {
                    h.sessions.insert(id(*p));
                }
                m.session_up(&mut h, now, &id(*p), false);
                h.ev.insert(id(*p), Evidence { last_rx: now, srtt: 20 * MS, pto: 0, inflight: 0, direct: true });
                let b = encode_spec(&FrameSpec::Snap(false, false, es.clone()), mine);
                assert_eq!(m.on_bytes(&mut h, now, &id(*p), &b), Ok(b.len()), "{step}");
            },
        }
        // view.rs: "A snapshot never removes a member on its own."
        if matches!(op, Op::Frame(_, FrameSpec::Snap(..)) | Op::Link(..)) {
            let gone: Vec<u8> = before.iter().filter(|k| !m.in_view(k)).map(|k| k[0] - 1).collect();
            assert!(gone.is_empty(), "{step}: a snapshot removed members {gone:?}");
        }
        // What the machine sent in this step: a well-formed frame, to someone else, never to a revoked peer.
        for (peer, route, bytes) in h.sent.drain(..) {
            assert_ne!(peer, me, "{step}: the node sent to itself");
            assert!(!revoked.contains(&peer), "{step}: a frame went to a revoked peer");
            if let Route::Via(x) = route {
                assert_ne!(x, peer, "{step}: a frame relayed through its own target");
            }
            let read = Frame::read_with(&bytes, m.max_frame());
            let Ok(Some((f, n))) = read else {
                panic!("{step}: the node sent bytes that are not one frame: {read:?}");
            };
            assert_eq!(n, bytes.len(), "{step}: a send is exactly one frame");
            let _ = f;
        }
        assert!(m.view_epoch() >= epoch, "{step}: the view epoch went down");
        epoch = m.view_epoch();
        assert!(m.incarnation() >= inc, "{step}: the incarnation went down");
        inc = m.incarnation();
        assert!(!m.in_view(&me), "{step}: the view lists the node itself");
        for (member, _) in m.members() {
            assert_ne!(*member, me, "{step}: the view lists the node itself");
            assert!(!revoked.contains(member), "{step}: the view lists a revoked node");
        }
        assert!(m.member_count() <= MAX_TABLE && m.roster_len() <= MAX_TABLE, "{step}: a table over its bound");
        assert!(m.hubs().all(|x| *x != me), "{step}: hubs() lists the node itself");
        for r in &revoked {
            assert!(m.lease_of(r).is_none(), "{step}: a revoked member holds a lease");
        }
        let mut events = 0usize;
        while let Some(e) = m.poll_event() {
            events += 1;
            assert!(events <= QUEUE_CAP + 1, "{step}: more events than the queue holds");
            if let Event::ViewChanged { epoch: e_epoch, .. } = e {
                assert!(last_view_event.is_none_or(|l| e_epoch > l), "{step}: a view epoch event did not increase");
                assert!(e_epoch <= m.view_epoch(), "{step}: an event from the future");
                last_view_event = Some(e_epoch);
            }
            log.push(format!("{e:?}"));
        }
        let mut traces = 0usize;
        while let Some(t) = m.poll_trace() {
            traces += 1;
            assert!(traces <= QUEUE_CAP + 1, "{step}: more traces than the queue holds");
            log.push(format!("{t:?}"));
        }
        log.append(&mut h.log);
        log.push(format!("t{} e{} i{} p{:?}", m.poll_timeout(), m.view_epoch(), m.incarnation(), m.primary().map(|p| p[0])));
    }
    log
}

/// Any sequence of host events and remote frames: no panic, the documented invariants after every step, and the
/// same inputs give the same outputs.
#[ephyra::test(gen = machine_cases(), tests = 3_000)]
fn machine_keeps_its_invariants(case: ((bool, u8, bool, u64, usize), Vec<Op>)) {
    let (setup, ops) = case;
    let a = run_machine(setup, &ops);
    let b = run_machine(setup, &ops);
    assert_eq!(a, b, "the same inputs gave different outputs");
}
