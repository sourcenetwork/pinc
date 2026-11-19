//! Model-based tests of the endpoint's use of its tables: a real endpoint (`pinc-core`, built with the `trace` feature)
//! driven along every edge of the state graphs of `proofs/tla/MbtEndpoint.tla`.
//!
//! TLC enumerates the states the calls of the endpoint reach (a forged first flight, a later part of a first message,
//! a timer, a call on a stale session id, strays, dials to the node itself, reading events) within the bounds of a
//! config and writes the graph; `scripts/mbt.py` turns it into paths from the empty endpoint that take every edge,
//! which `scripts/proofs.sh` writes to the directory `PINC_MBT_DIR`: `endpoint.ndjson` from `MbtEndpoint.cfg`,
//! `endpoint_life.ndjson` from `MbtEndpoint_life.cfg` and `endpoint_stall.ndjson` from `MbtEndpoint_stall.cfg`. This
//! test runs each path on a fresh endpoint and, after every call, compares what the model keeps (the sessions with the
//! time, id and source that made them, the held parts, the length of the event queue) with what the endpoint holds,
//! read through the `trace` views, and checks what the model cannot see: the heap deadline, the routing entries and
//! the first id of each session in the table, none of them for a free slot, the counters, the timer, and the refusal of
//! every command on an id that names no live session with nothing changed. It stops at the first difference and names
//! the file, the case, the step and the calls that led there. Without `PINC_MBT_DIR` it checks nothing but the two plain
//! tests below.
//!
//! The model's numbers stand for the code's as `MbtEndpoint.tla` says: model time `t` is `origin + t * MS_NS` (the
//! largest model time is `u64::MAX`), where `origin` is `2 * HALF_OPEN_LIFE` or an odd millisecond past
//! `5 * HALF_OPEN_LIFE`, by case; a model id is an 8-byte destination id and a model source an address; a model part
//! length of 1 is 200 bytes and of 2 is 1501; the model's queue lengths `S - 1` and `S` are the real `2K + 960` and
//! `2K + 961`. The table of connection ids has `D = 10 K` entries, as the endpoint needs.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    unreachable_pub,
    clippy::needless_range_loop
)]

use std::fmt::Write as _;
use std::net::SocketAddr;
use std::rc::Rc;

use pinc_core::{
    Answer, Command, CommandError, ConnectFailure, Endpoint, EndpointConfig, Event, HALF_OPEN_LIFE, HalfOpenSlot,
    MAX_DATAGRAM, NodeStats, OrphanEntry, OrphanProbe, Query, Role, SessionId, Slot, Taken, TraceEvent, event_headroom,
    event_queue,
};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use pinc_security::message::FULL_INITIAL_MIN;
use pinc_security::{ConnId, KeyHandle, KeyResponse, LocalIdentity};
use pinc_tests::{ALPN_A, Caps, Json, MS_NS, MbtCase, big_stack, mbt_cases};
use pinc_transport::conn::{Held, Resources, Shared, Tables};
use pinc_transport::packet::{LongHeader, LongType};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{self, NoSource, Streams};
use pinc_wire::Writer;

type Ep<'s, const K: usize, const D: usize> = Endpoint<'s, 'static, Caps, NoSource, 1, 2, 16, 1, K, D, 4, 4, 2>;
type TSlot = Slot<'static, Caps, NoSource, 1, 2, 16, 1>;
/// What a slot holds in the test's own books: the model time, id and source that made it, and its session id.
type Made = (u64, u64, u64, SessionId);
/// Everything a call on a stale id must leave as it was.
type Snap = (
    NodeStats,
    Vec<(Option<HalfOpenSlot>, Option<u64>, usize, Option<ConnId>)>,
    Vec<Option<OrphanEntry>>,
    Option<u64>,
    Vec<SessionId>,
);

// A slot's memory, owned by the slot: every case builds a table of `K` slots, so none of it may outlive its case.
fn small_memory() -> Resources<'static, NoSource, 1, 2, 16> {
    let pool = BufferPool::new_boxed(4);
    let streams = Box::new(Streams::new(&stream::Config::new(false), &pool));
    Resources {
        pool,
        streams: Held::Owned(streams),
        loss: Shared::Counted(Rc::new(LossEstimate::new())),
        tables: Tables::new(),
    }
}

fn slots<const K: usize>() -> Box<[TSlot; K]> {
    let v: Vec<TSlot> = (0..K).map(|_| Slot::new(small_memory())).collect();
    v.into_boxed_slice().try_into().ok().unwrap()
}

// The endpoint of `mbt_halfopen.rs` over `slots`: a software provider, one registered protocol, one interface.
fn server<const K: usize, const D: usize>(now: u64, slots: &mut [TSlot; K]) -> (Box<Ep<'_, K, D>>, SocketAddr) {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let mut ep = Box::new(Endpoint::new(
        now,
        Caps(Software, true),
        Drbg::new(&[3; 32]),
        id,
        EndpointConfig::new(5),
        slots,
    ));
    assert!(ep.register_alpn(ALPN_A));
    let addr: SocketAddr = "10.0.0.1:4433".parse().unwrap();
    ep.add_iface(addr).unwrap();
    (ep, addr)
}

/// The destination id of model id `id`.
const fn dcid_num(id: u64) -> u64 {
    0xE1D0_0000_0000_0000u64 | id
}

fn dcid(id: u64) -> ConnId {
    ConnId::new(&dcid_num(id).to_be_bytes()).unwrap()
}

/// A long handshake datagram of exactly `len` bytes for `dcid` whose message (of 4095 bytes) starts at `off` with
/// `kind`, then a salt.
fn craft(dcid: u64, kind: u8, len: usize, off: u64) -> Vec<u8> {
    let mut d = vec![0u8; len];
    let mut h = LongHeader {
        ty: LongType::Handshake,
        dcid: ConnId::new(&dcid.to_be_bytes()).unwrap(),
        scid: ConnId::new(&[1, 2, 3, 4]).unwrap(),
        body_len: 0,
    };
    for _ in 0..3 {
        h.body_len = len - h.header_len();
    }
    let mut w = Writer::new(&mut d);
    h.write(&mut w, 0).unwrap();
    w.put_varint(4095).unwrap();
    w.put_varint(off).unwrap();
    w.put_u8(kind).unwrap();
    w.put_u8(dcid as u8).unwrap();
    d
}

fn src_addr(src: u64) -> SocketAddr {
    SocketAddr::from(([10, 2, 0, src as u8], 9))
}

/// The length in bytes of a part of model length `len`: 1 is 200, 2 is 1501 (over the largest held, 1500).
fn real_len(len: u64) -> usize {
    [200, 1501][(len - 1) as usize]
}

fn num(v: &Json) -> u64 {
    v.u64().unwrap()
}

/// The calls of `case` up to step `upto`, for a failure message.
fn calls(case: &MbtCase, upto: usize) -> String {
    let mut s = String::new();
    for (i, st) in case.steps.iter().take(upto + 1).enumerate() {
        let _ = write!(s, "\n  {i}: {st}");
    }
    s
}

/// How the model's numbers map onto the code's.
#[derive(Clone)]
struct Map {
    origin: u64,
    tmax: u64,
    s: u64,
    qb: u64,
    rs: usize,
    ids: Vec<u64>,
}

impl Map {
    fn real(&self, t: u64) -> u64 {
        if t >= self.tmax {
            assert_eq!(t, self.tmax, "a model time past the largest");
            u64::MAX
        } else {
            self.origin + t * MS_NS
        }
    }

    fn back(&self, x: u64) -> u64 {
        if x == u64::MAX {
            return self.tmax;
        }
        let d = x.checked_sub(self.origin).unwrap();
        assert_eq!(d % MS_NS, 0, "a time of the code that is no time of the model");
        d / MS_NS
    }

    /// The real length of the event queue for the model's `q`.
    fn real_q(&self, q: u64) -> usize {
        if q <= self.qb {
            q as usize
        } else {
            self.rs - (self.s - q) as usize
        }
    }
}

/// The model's variables, read from a state.
struct Model {
    live: Vec<(u64, u64, u64)>,
    o: Json,
    q: u64,
}

impl Model {
    fn of(st: &Json) -> Self {
        let mut live: Vec<(u64, u64, u64)> = st
            .get("live")
            .and_then(Json::arr)
            .unwrap()
            .iter()
            .map(|s| {
                let s = s.arr().unwrap();
                (num(&s[0]), num(&s[1]), num(&s[2]))
            })
            .collect();
        live.sort_unstable();
        Self {
            live,
            o: st.get("o").unwrap().clone(),
            q: num(st.get("q").unwrap()),
        }
    }

    fn count(&self, field: &str) -> u64 {
        num(self.o.get(field).unwrap())
    }
}

/// An endpoint and the test's books on it.
struct World<'e, const K: usize, const D: usize> {
    ep: Box<Ep<'e, K, D>>,
    addr: SocketAddr,
    map: Map,
    made: [Option<Made>; K],
    gone: Vec<SessionId>,
}

fn records(ep: &mut impl Records) -> Vec<TraceEvent> {
    let mut v = Vec::new();
    while let Some(e) = ep.next_event() {
        v.push(e);
    }
    v
}

/// Reads the trace ring of an endpoint of any size.
trait Records {
    fn next_event(&mut self) -> Option<TraceEvent>;
}

impl<const K: usize, const D: usize> Records for Ep<'_, K, D> {
    fn next_event(&mut self) -> Option<TraceEvent> {
        self.poll_trace().map(|r| r.event)
    }
}

fn demuxes(ev: &[TraceEvent]) -> Vec<u64> {
    ev.iter()
        .filter_map(|e| match e {
            TraceEvent::Demux { candidates, .. } => Some(*candidates),
            _ => None,
        })
        .collect()
}

fn half_opens(ev: &[TraceEvent]) -> Vec<(u64, u64, u64)> {
    ev.iter()
        .filter_map(|e| match e {
            TraceEvent::HalfOpen {
                admitted,
                half_open,
                resume,
                ..
            } => Some((*admitted, *half_open, *resume)),
            _ => None,
        })
        .collect()
}

fn expired(ev: &[TraceEvent]) -> Vec<u64> {
    ev.iter()
        .filter_map(|e| match e {
            TraceEvent::HalfOpenExpired { slot } => Some(*slot),
            _ => None,
        })
        .collect()
}

/// The `(slot, dialer)` of the session records of `step`.
fn sessions_at(ev: &[TraceEvent], step: u64) -> Vec<(u64, u64)> {
    ev.iter()
        .filter_map(|e| match e {
            TraceEvent::Session {
                slot, step: s, dialer, ..
            } if *s == step => Some((*slot, *dialer)),
            _ => None,
        })
        .collect()
}

fn sorted(mut v: Vec<usize>) -> Vec<usize> {
    v.sort_unstable();
    v.dedup();
    v
}

impl<'e, const K: usize, const D: usize> World<'e, K, D> {
    fn new(origin: u64, table: &'e mut [TSlot; K], map: Map) -> Self {
        let (mut ep, addr) = server::<K, D>(origin, table);
        while ep.poll_trace().is_some() {}
        Self {
            ep,
            addr,
            map: Map { origin, ..map },
            made: [None; K],
            gone: Vec::new(),
        }
    }

    /// The flood of `id` from `src` at `now`; the trace records it caused.
    fn flood(&mut self, now: u64, id: u64, src: u64) -> Vec<TraceEvent> {
        let mut d = craft(dcid_num(id), 1, FULL_INITIAL_MIN, 0);
        self.ep.handle_datagram(now, self.addr, src_addr(src), &mut d);
        records(&mut *self.ep)
    }

    /// A later part of the message of `id`, of model length `len`, from `src` at `now`.
    fn part(&mut self, now: u64, id: u64, src: u64, len: u64) -> Vec<TraceEvent> {
        let mut d = craft(dcid_num(id), 0, real_len(len), 2000);
        self.ep.handle_datagram(now, self.addr, src_addr(src), &mut d);
        records(&mut *self.ep)
    }

    /// The three strays: an empty datagram, one over the largest, a short header for an id nobody holds.
    fn stray(&mut self, now: u64) -> Vec<TraceEvent> {
        let from = src_addr(1);
        self.ep.handle_datagram(now, self.addr, from, &mut []);
        self.ep
            .handle_datagram(now, self.addr, from, &mut vec![0u8; MAX_DATAGRAM + 1]);
        let mut short = [0u8; 30];
        short[..5].copy_from_slice(&[0x40, 0xEE, 0xEE, 0xEE, 0xEE]);
        self.ep.handle_datagram(now, self.addr, from, &mut short);
        records(&mut *self.ep)
    }

    /// A dial of this node's own id at `now`.
    fn self_dial(&mut self, now: u64) -> Result<(), CommandError> {
        let own = self.ep.identity().node_id();
        self.ep
            .command(
                now,
                Command::Connect {
                    node: own,
                    alpn: ALPN_A,
                    addrs: &[],
                    role: Role::Other,
                },
            )
            .map(|_| ())
    }

    /// The slot and id of the session a flood just made, entered in the books.
    fn made_by(&mut self, ev: &[TraceEvent], t: u64, id: u64, src: u64, at: &dyn Fn() -> String) {
        let created = sessions_at(ev, 0);
        assert_eq!(created.len(), 1, "{}: one session is made: {created:?}", at());
        let (slot, dialer) = created[0];
        assert_eq!(dialer, 0, "{}: the session was not dialed here", at());
        let slot = usize::try_from(slot).unwrap();
        assert!(
            slot < K && self.made[slot].is_none(),
            "{}: the session took slot {slot}, which is not free in the books: {:?}",
            at(),
            self.made
        );
        let sid = self.ep.sessions().find(|s| s.slot() == slot).unwrap();
        self.made[slot] = Some((t, id, src, sid));
    }

    /// The stale ids of a `CallStale`.
    fn stale_ids(&self) -> Vec<SessionId> {
        let mut ids = self.gone.clone();
        ids.push(SessionId(K as u64));
        ids.push(SessionId(0));
        ids.extend(self.ep.sessions().map(|s| SessionId(s.0 + (2 << 32))));
        ids
    }
}

fn snapshot<const K: usize, const D: usize>(ep: &Ep<'_, K, D>) -> Snap {
    (
        ep.node_stats(),
        (0..K)
            .map(|i| {
                (
                    ep.half_open_slot(i),
                    ep.slot_deadline(i),
                    ep.slot_routes(i),
                    ep.slot_odcid(i),
                )
            })
            .collect(),
        (0..4).map(|k| ep.held_fragment(k)).collect(),
        ep.poll_timeout(),
        ep.sessions().collect(),
    )
}

/// Every command on `id`, which names no live session, is refused and changes nothing (`commands.rs`).
fn refused<const K: usize, const D: usize>(
    ep: &mut Ep<'_, K, D>,
    ids: &[SessionId],
    now: u64,
    at: &dyn Fn() -> String,
) {
    let before = snapshot(ep);
    let one = [src_addr(1)];
    for &id in ids {
        let session = id;
        let cmds: Vec<(&str, Command<'_, NoSource>)> = vec![
            ("OpenStream", Command::OpenStream { session, bidi: true }),
            (
                "Write",
                Command::Write {
                    session,
                    stream: 0,
                    data: b"x",
                },
            ),
            (
                "WriteSource",
                Command::WriteSource {
                    session,
                    stream: 0,
                    source: NoSource,
                    len: 1,
                },
            ),
            (
                "SetUrgency",
                Command::SetUrgency {
                    session,
                    stream: 0,
                    urgency: 3,
                },
            ),
            (
                "SendExtension",
                Command::SendExtension {
                    session,
                    ty: 0x7f00,
                    body: b"x",
                },
            ),
            ("Finish", Command::Finish { session, stream: 0 }),
            (
                "Reset",
                Command::Reset {
                    session,
                    stream: 0,
                    error: 1,
                },
            ),
            (
                "StopSending",
                Command::StopSending {
                    session,
                    stream: 0,
                    error: 1,
                },
            ),
            (
                "Consume",
                Command::Consume {
                    session,
                    stream: 0,
                    n: 1,
                },
            ),
            ("SendDatagram", Command::SendDatagram { session, data: b"x" }),
            ("Close", Command::Close { session, error: 0 }),
            (
                "KeyResponse",
                Command::KeyResponse {
                    session,
                    response: KeyResponse::Failed,
                },
            ),
            (
                "FlightPaths",
                Command::FlightPaths {
                    session,
                    addrs: &one,
                    skip_primary: false,
                },
            ),
            ("Pulse", Command::Pulse { session, sent: true }),
            ("SetPulse", Command::SetPulse { session, on: true }),
            ("FirstResend", Command::FirstResend { session, delay: 1 }),
            ("HoldFlight", Command::HoldFlight { session, hold: true }),
            ("ReachOut", Command::ReachOut { session, body: &[1] }),
            (
                "Punch",
                Command::Punch {
                    session,
                    addr: src_addr(1),
                },
            ),
            (
                "SetRole",
                Command::SetRole {
                    session,
                    role: Role::Hub,
                },
            ),
            ("Ping", Command::Ping { session }),
            ("CarrierHeard", Command::CarrierHeard { session, at: 1 }),
            ("SetGossip", Command::SetGossip { session, gossip: true }),
        ];
        for (name, cmd) in cmds {
            let r = ep.command(now, cmd).map(|_| ());
            assert!(
                matches!(r, Err(CommandError::NoSession)),
                "{}: {name} on the stale id {id:?} gave {r:?}, not NoSession",
                at()
            );
        }
        let r = ep.command(now, Command::ReachOut { session, body: &[] }).map(|_| ());
        assert!(
            matches!(r, Err(CommandError::BadAlpn)),
            "{}: ReachOut with an empty body on {id:?} gave {r:?}, not BadAlpn",
            at()
        );
        let r = ep.read_datagram(id, &mut [0u8; 64]);
        assert!(
            matches!(r, Err(CommandError::NoSession)),
            "{}: read_datagram on {id:?} gave {r:?}",
            at()
        );
        assert_eq!(ep.session_taken(id), Taken::Gone, "{}: session_taken on {id:?}", at());
        assert!(
            matches!(ep.query(Query::Stats(id)), Answer::None),
            "{}: the Stats query on {id:?} answered",
            at()
        );
    }
    assert_eq!(
        snapshot(ep),
        before,
        "{}: a command on a stale id changed the endpoint",
        at()
    );
    assert!(
        ep.poll_trace().is_none(),
        "{}: a command on a stale id left a trace record",
        at()
    );
}

/// The endpoint against the model's state `st`, and the invariants of the code the model cannot see.
fn same_state<const K: usize, const D: usize>(w: &World<'_, K, D>, st: &Json, at: &dyn Fn() -> String) {
    let (ep, map) = (&*w.ep, &w.map);
    let m = Model::of(st);
    let mut least: Option<u64> = None;
    for i in 0..K {
        if let Some(s) = ep.half_open_slot(i) {
            assert!(
                s.unauth && s.counted,
                "{}: slot {i} holds a session that is not an unauthenticated counted one: {s:?}",
                at()
            );
            assert_eq!(s.life, HALF_OPEN_LIFE, "{}: slot {i} has another life: {s:?}", at());
            let d = ep.slot_deadline(i);
            assert_eq!(
                d,
                s.deadline,
                "{}: slot {i}: the two views of its deadline differ",
                at()
            );
            let d = d.unwrap_or_else(|| panic!("{}: slot {i} holds a session and no deadline", at()));
            assert!(
                d <= s.created.saturating_add(s.life).saturating_add(1),
                "{}: slot {i} holds a deadline past the end of its session: {s:?}, {d}",
                at()
            );
            least = Some(least.map_or(d, |l| l.min(d)));
            assert!(
                ep.slot_routes(i) >= 1,
                "{}: slot {i} holds a session no routing entry names",
                at()
            );
            let Some((t, id, _, _)) = w.made[i] else {
                panic!("{}: slot {i} holds a session the model does not have: {s:?}", at());
            };
            assert_eq!(ep.slot_odcid(i), Some(dcid(id)), "{}: slot {i}: its first id", at());
            assert_eq!(map.back(s.created), t, "{}: slot {i}: the time it was made", at());
        } else {
            assert_eq!(ep.slot_deadline(i), None, "{}: free slot {i} holds a deadline", at());
            assert_eq!(ep.slot_routes(i), 0, "{}: free slot {i} is routed to", at());
            assert_eq!(ep.slot_odcid(i), None, "{}: free slot {i} holds an id", at());
            assert!(
                w.made[i].is_none(),
                "{}: slot {i} is free, the books say it is not",
                at()
            );
        }
    }
    let mut held: Vec<(u64, u64, u64)> = w.made.iter().flatten().map(|&(t, id, src, _)| (t, id, src)).collect();
    held.sort_unstable();
    assert_eq!(held, m.live, "{}: the sessions held differ from the model's", at());

    for &id in &map.ids {
        let (found, n) = ep.routes_of(&dcid(id));
        let want = sorted(
            m.live
                .iter()
                .filter(|s| s.1 == id)
                .map(|s| {
                    w.made
                        .iter()
                        .position(|x| x.is_some_and(|x| (x.0, x.1, x.2) == *s))
                        .unwrap()
                })
                .collect(),
        );
        let got: Vec<usize> = found.iter().take(n).map(|s| s.unwrap() as usize).collect();
        assert_eq!(
            (n, sorted(got)),
            (m.live.iter().filter(|s| s.1 == id).count(), want),
            "{}: the routing entries of id {id} differ from the sessions that hold it",
            at()
        );
    }

    let stats = ep.node_stats();
    let live = m.live.len();
    assert_eq!(
        (stats.half_open, stats.sessions, stats.owed),
        (live, live, live),
        "{}: half_open, sessions and owed differ from the model's",
        at()
    );
    assert_eq!(
        stats.events_queued,
        map.real_q(m.q),
        "{}: the event queue's length",
        at()
    );
    assert_eq!(
        ep.events_stalled(),
        m.q == map.s,
        "{}: whether the queue is stalled",
        at()
    );
    assert_eq!(
        (stats.events_dropped, stats.events_lost),
        (0, 0),
        "{}: events were lost",
        at()
    );
    let timeout = if m.q == map.s { None } else { least };
    assert_eq!(ep.poll_timeout(), timeout, "{}: poll_timeout", at());

    assert_eq!(
        [
            stats.fragments_held,
            stats.fragments_replayed,
            stats.fragments_expired,
            stats.fragments_evicted
        ],
        [
            m.count("held"),
            m.count("replayed"),
            m.count("expired"),
            m.count("evicted")
        ],
        "{}: the counters of held parts differ from the model's",
        at()
    );
    let o_slots = m.o.get("slots").and_then(Json::arr).unwrap();
    assert_eq!(
        stats.fragments_waiting,
        o_slots.iter().filter(|e| !e.arr().unwrap().is_empty()).count(),
        "{}: fragments_waiting",
        at()
    );
    for k in 0..4 {
        let e = o_slots[k].arr().unwrap();
        let got = ep.held_fragment(k);
        if e.is_empty() {
            assert_eq!(got, None, "{}: held entry {k} should be free", at());
            continue;
        }
        let key = e[2].arr().unwrap();
        let Some(got) = got else {
            panic!("{}: held entry {k} is free, the model holds {e:?}", at())
        };
        assert_eq!(
            (got.at, got.order, got.dcid, got.remote, got.local, got.total, got.len),
            (
                map.real(num(&e[0])),
                num(&e[1]),
                dcid(num(&key[0])),
                src_addr(num(&key[1])),
                w.addr,
                4095,
                real_len(num(&e[4]))
            ),
            "{}: held entry {k} differs from the model's {e:?}",
            at()
        );
    }
}

/// Reads `poll_event` as `CallRead` says: the refusal of a dial of this node itself.
fn read_refusal<const K: usize, const D: usize>(w: &mut World<'_, K, D>, at: &dyn Fn() -> String) {
    let own = w.ep.identity().node_id();
    let ev = w.ep.poll_event();
    assert!(
        matches!(
            ev,
            Some(Event::ConnectFailed {
                session: None,
                node,
                reason: ConnectFailure::Refused,
                ..
            }) if node == own
        ),
        "{}: the event read is not the refusal of a dial to this node: {ev:?}",
        at()
    );
}

/// Runs one case of `file` on a fresh endpoint; returns the number of calls.
fn run<const K: usize, const D: usize>(file: &str, case: &MbtCase, init: &Json, template: &Map) -> usize {
    let origin = [2 * HALF_OPEN_LIFE, 5 * HALF_OPEN_LIFE + 123 * MS_NS][(case.id % 2) as usize];
    let mut table = slots::<K>();
    let mut w = World::<K, D>::new(origin, &mut table, template.clone());
    let who = format!("{file} case {}", case.id);
    same_state(&w, init, &|| format!("{who}: the empty endpoint"));
    let mut prev = Model::of(init);
    for (i, st) in case.steps.iter().enumerate() {
        let at = || format!("{who} step {i} ({st}); calls:{}", calls(case, i));
        let next = Model::of(&st.state);
        let before = w.ep.node_stats();
        let a = st.args.as_slice();
        match (st.call.as_str(), a) {
            ("CallFlood", [t, id, src, dec]) => {
                let (t, id, src, dec) = (num(t), num(id), num(src), num(dec));
                let ev = w.flood(w.map.real(t), id, src);
                let after = w.ep.node_stats();
                let holders = prev.live.iter().filter(|s| s.1 == id).count() as u64;
                assert_eq!(demuxes(&ev), [holders], "{}: the demux records", at());
                if dec == 2 {
                    assert!(
                        half_opens(&ev).is_empty() && sessions_at(&ev, 0).is_empty(),
                        "{}: a stalled endpoint decided on a flight: {ev:?}",
                        at()
                    );
                } else {
                    assert_eq!(
                        half_opens(&ev),
                        [(1, prev.live.len() as u64, 0)],
                        "{}: the admission record (admitted, half_open, resume)",
                        at()
                    );
                    if dec == 1 {
                        w.made_by(&ev, t, id, src, &at);
                    } else {
                        assert!(sessions_at(&ev, 0).is_empty(), "{}: a session was made", at());
                    }
                }
                assert!(
                    expired(&ev).is_empty() && sessions_at(&ev, 2).is_empty(),
                    "{}: a flight freed a session",
                    at()
                );
                assert_eq!(
                    (
                        after.dropped_in - before.dropped_in,
                        after.stalled_in - before.stalled_in,
                        after.first_too_short - before.first_too_short,
                        after.fragments_replayed - before.fragments_replayed,
                    ),
                    (
                        u64::from(dec == 0),
                        u64::from(dec == 2),
                        0,
                        next.count("replayed") - prev.count("replayed")
                    ),
                    "{}: the counters (dropped_in, stalled_in, first_too_short, fragments_replayed) moved wrongly",
                    at()
                );
            }
            ("CallPart", [t, id, src, len, dec]) => {
                let (t, id, src, len, dec) = (num(t), num(id), num(src), num(len), num(dec));
                let ev = w.part(w.map.real(t), id, src, len);
                let after = w.ep.node_stats();
                assert_eq!(demuxes(&ev), [0], "{}: the demux records", at());
                assert!(
                    half_opens(&ev).is_empty() && sessions_at(&ev, 0).is_empty(),
                    "{}: a part started a session: {ev:?}",
                    at()
                );
                assert_eq!(
                    (
                        after.fragments_held - before.fragments_held,
                        after.dropped_in - before.dropped_in,
                        after.stalled_in - before.stalled_in
                    ),
                    (u64::from(dec == 1), u64::from(dec == 0), u64::from(dec == 2)),
                    "{}: the counters (fragments_held, dropped_in, stalled_in) moved wrongly",
                    at()
                );
            }
            ("CallTimer", [t]) => {
                let now = w.map.real(num(t));
                w.ep.handle_timeout(now);
                let ev = records(&mut *w.ep);
                let from_expired = sorted(expired(&ev).iter().map(|&s| s as usize).collect());
                let from_freed = sorted(sessions_at(&ev, 2).iter().map(|&(s, _)| s as usize).collect());
                let from_model = sorted(
                    prev.live
                        .iter()
                        .filter(|s| !next.live.contains(s))
                        .map(|s| {
                            w.made
                                .iter()
                                .position(|x| x.is_some_and(|x| (x.0, x.1, x.2) == *s))
                                .unwrap()
                        })
                        .collect(),
                );
                assert!(
                    from_expired == from_freed && from_freed == from_model,
                    "{}: the slots freed differ: expired {from_expired:?}, freed {from_freed:?}, model {from_model:?}",
                    at()
                );
                for &s in &from_model {
                    let (_, _, _, sid) = w.made[s].take().unwrap();
                    w.gone.push(sid);
                }
                if next.q != w.map.s && now != u64::MAX {
                    for s in 0..K {
                        if w.ep.half_open_slot(s).is_some() {
                            let d = w.ep.slot_deadline(s);
                            assert!(
                                d.is_some_and(|d| d > now),
                                "{}: slot {s} holds the deadline {d:?}, at or before the timer's {now}",
                                at()
                            );
                        }
                    }
                }
            }
            ("CallStale", [t]) => {
                let now = w.map.real(num(t));
                let ids = w.stale_ids();
                refused(&mut w.ep, &ids, now, &at);
            }
            ("CallStray", [t, dec]) => {
                let dec = num(dec);
                let ev = w.stray(w.map.real(num(t)));
                let after = w.ep.node_stats();
                assert_eq!(demuxes(&ev), [0], "{}: the demux records", at());
                assert_eq!(ev.len(), 1, "{}: a stray left more than a demux record: {ev:?}", at());
                assert_eq!(
                    (
                        after.datagrams_in - before.datagrams_in,
                        after.dropped_in - before.dropped_in,
                        after.stalled_in - before.stalled_in
                    ),
                    (3, if dec == 1 { 3 } else { 2 }, u64::from(dec == 2)),
                    "{}: the counters (datagrams_in, dropped_in, stalled_in) moved wrongly",
                    at()
                );
            }
            ("CallSelfDial", [t, res]) => {
                let res = num(res);
                let r = w.self_dial(w.map.real(num(t)));
                let queued = w.ep.node_stats().events_queued - before.events_queued;
                if res == 1 {
                    assert!(matches!(r, Err(CommandError::Refused)), "{}: the dial gave {r:?}", at());
                } else {
                    assert!(
                        matches!(r, Err(CommandError::EventsPending)),
                        "{}: the dial gave {r:?}",
                        at()
                    );
                }
                assert_eq!(queued, usize::from(res == 1), "{}: events queued by the dial", at());
            }
            ("CallFill", [t]) => {
                let now = w.map.real(num(t));
                let mut dials = 0;
                while !w.ep.events_stalled() {
                    let r = w.self_dial(now);
                    assert!(matches!(r, Err(CommandError::Refused)), "{}: a dial gave {r:?}", at());
                    dials += 1;
                    assert!(dials <= w.map.rs + 1, "{}: the queue does not stall", at());
                }
                assert_eq!(
                    w.ep.node_stats().events_queued,
                    w.map.rs,
                    "{}: the stalled queue's length",
                    at()
                );
            }
            ("CallRead", []) => read_refusal(&mut w, &at),
            ("CallDrain", []) => {
                for _ in 0..w.map.real_q(prev.q) {
                    read_refusal(&mut w, &at);
                }
                assert!(
                    w.ep.poll_event().is_none(),
                    "{}: the queue held more events than the model's",
                    at()
                );
            }
            _ => panic!("{who}: a call the test does not know: {st}"),
        }
        records(&mut *w.ep);
        same_state(&w, &st.state, &at);
        prev = next;
    }
    case.steps.len()
}

/// Walks every case of `file`; false when `PINC_MBT_DIR` is unset.
fn walk<const K: usize, const D: usize>(file: &str) -> bool {
    let Some(cases) = mbt_cases(file) else {
        return false;
    };
    let mut cases = cases.unwrap();
    let head = cases.head.clone();
    let c = head.get("constants").unwrap();
    let k = |n: &str| num(c.get(n).unwrap());
    assert_eq!(k("K"), K as u64, "{file}: the model's table is not the endpoint's");
    assert_eq!(
        k("LIFE") * MS_NS,
        HALF_OPEN_LIFE,
        "{file}: the model's lifetime is not the code's"
    );
    assert_eq!(
        k("OLIFE") * MS_NS,
        OrphanProbe::LIFE,
        "{file}: the model's life of a held part is not the code's"
    );
    assert!(
        k("OMAX") == 1 && OrphanProbe::MAX == 1500,
        "{file}: the model's lengths of parts do not straddle the code's largest held part"
    );
    assert!(k("S") - 1 > k("QB") + 1, "{file}: the model's queue bounds overlap");
    let ids = c.get("IDS").and_then(Json::arr).unwrap().iter().map(num).collect();
    let map = Map {
        origin: 0,
        tmax: k("TMAX"),
        s: k("S"),
        qb: k("QB"),
        rs: event_queue(K) - event_headroom(K) + 1,
        ids,
    };
    let init = head.get("init").unwrap();
    let (mut n, mut steps) = (0u64, 0usize);
    for case in &mut cases {
        steps += run::<K, D>(file, &case.unwrap(), init, &map);
        n += 1;
    }
    let count = |f: &str| num(head.get(f).unwrap());
    assert_eq!(
        (n, steps as u64),
        (count("cases"), count("steps")),
        "{file}: the file ends early"
    );
    eprintln!(
        "mbt_endpoint: {file}: {n} cases, {steps} calls, every one of the {} edges between the {} states of the graph",
        count("edges"),
        count("states")
    );
    true
}

#[test]
fn the_endpoint_keeps_its_tables_in_step_on_every_edge_of_the_model() {
    // MbtEndpoint.cfg, MbtEndpoint_life.cfg, MbtEndpoint_stall.cfg
    let walked = big_stack(|| {
        [
            walk::<2, 20>("endpoint.ndjson"),
            walk::<2, 20>("endpoint_life.ndjson"),
            walk::<1, 10>("endpoint_stall.ndjson"),
        ]
    });
    if walked == [false; 3] {
        eprintln!("mbt_endpoint: PINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)");
    }
}

fn plain_map() -> Map {
    Map {
        origin: 0,
        tmax: u64::MAX,
        s: 0,
        qb: 0,
        rs: 0,
        ids: Vec::new(),
    }
}

#[test]
fn a_timer_at_the_largest_time_frees_every_forged_session() {
    big_stack(|| {
        let origin = 2 * HALF_OPEN_LIFE;
        let mut table = slots::<2>();
        let mut w = World::<2, 20>::new(origin, &mut table, plain_map());
        let first = w.flood(origin, 1, 1);
        let second = w.flood(u64::MAX, 2, 2);
        assert_eq!(
            sessions_at(&first, 0).len() + sessions_at(&second, 0).len(),
            2,
            "both floods make a session"
        );
        w.ep.handle_timeout(u64::MAX);
        let ev = records(&mut *w.ep);
        assert_eq!(expired(&ev).len(), 2, "two sessions expire at the largest time: {ev:?}");
        assert!(
            (0..2).all(|i| w.ep.half_open_slot(i).is_none()),
            "a session is still held at the largest time"
        );
        assert_eq!(w.ep.poll_timeout(), None, "a timer is still due with no session held");
    });
}

#[test]
fn a_command_on_a_freed_session_changes_nothing() {
    big_stack(|| {
        let origin = 2 * HALF_OPEN_LIFE;
        let mut table = slots::<1>();
        let mut w = World::<1, 10>::new(origin, &mut table, plain_map());
        let ev = w.flood(origin, 1, 1);
        assert_eq!(sessions_at(&ev, 0).len(), 1, "the flood makes a session");
        let old = w.ep.sessions().next().unwrap();
        let now = origin + HALF_OPEN_LIFE + 1;
        w.ep.handle_timeout(now);
        assert!(w.ep.sessions().next().is_none(), "the session outlived its end");
        records(&mut *w.ep);
        let at = || "a command on a freed session".to_owned();
        refused(&mut w.ep, &[old], now, &at);
        let ev = w.flood(now, 2, 1);
        assert_eq!(sessions_at(&ev, 0).len(), 1, "the second flood makes a session");
        let new = w.ep.sessions().next().unwrap();
        assert_ne!(new, old, "the slot's new session has the old id");
        refused(&mut w.ep, &[old], now, &at);
    });
}
