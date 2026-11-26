//! `pinc-core`: an endpoint built on a connection table another endpoint used and gave back behaves as one built on a
//! fresh table.
//!
//! Where the expected behaviour comes from:
//! - `Endpoint::into_slots` (endpoint.rs): "End the endpoint and give its connection table back with every session
//!   closed and every slot's memory returned, so another endpoint can run in the same memory."
//! - `Endpoint::new`: "A new endpoint at time `now`, with `slots` as its connection table. Every slot must be free
//!   (built with [`Slot::new`])." A table `into_slots` gave back is such a table, or it would not be offered for reuse.
//! - `LossEstimate::reset`: "Forget every packet seen: the estimate of a new endpoint, for memory that is handed on to
//!   the next one": the one piece of a slot's memory the host owns and resets itself, as the simulator does
//!   (`pinc-sim` suite/node/mem.rs, `slots`). The host here resets it too.
//! - The crate is a deterministic state machine of its inputs ("There are no hidden wakeups", lib.rs): the same
//!   calls at the same instants with the same seeds give the same outputs.
//!
//! So the property: a history of dials, streams, writes, datagrams, closes and time runs on endpoint X over table T,
//! then `into_slots` gives T back. Endpoint A on a fresh table and endpoint B on T, built alike, each with a fresh
//! peer, run the same script on the same clock. Every output must agree: datagrams byte for byte (destination, time,
//! bytes), events, command replies, `poll_timeout`, the session and node statistics. Session ids are compared after
//! renaming them in order of first appearance: the id's generation half counts the sessions the slot held before
//! ("How many sessions the slot held before this one", api.rs), so it carries over on purpose; what a session does
//! must not. A control run (a second fresh table) checks that the driver itself is deterministic.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::fmt::Write as _;
use std::net::SocketAddr;
use std::rc::Rc;

use ephyra::{check_generator, gens};
use pinc_core::{Answer, Command, Endpoint, EndpointConfig, Event, Query, Role, SessionId, Slot, Taken, Value};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use pinc_security::{Env, KeyHandle, KeyResponse, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys};
use pinc_transport::conn::{Held, Machines, Resources, Shared, Tables};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{self, NoSource, Streams};

const N: usize = 8;
const C: usize = 17;
const F: usize = 128;
const NP: usize = 4;
const K: usize = 8;
const D: usize = 128;
const PK: usize = 8;
const TK: usize = 16;
const CT: usize = 8;
const CHUNKS: usize = 128;

const SEC: u64 = 1_000_000_000;
const MS: u64 = 1_000_000;
const ALPNS: [&[u8]; 2] = [b"pinc/a", b"pinc/b"];

type Ep<'s> = Endpoint<'s, 'static, Software, NoSource, N, C, F, NP, K, D, PK, TK, CT>;
type NSlot = Slot<'static, Software, NoSource, N, C, F, NP>;

/// A connection table of `K` free slots, each with memory of its own, and the loss estimate they share.
struct Table {
    slots: Box<[NSlot; K]>,
    loss: Rc<LossEstimate>,
}

fn table() -> Table {
    let loss = Rc::new(LossEstimate::new());
    let machines = Machines::new();
    let v: Vec<NSlot> = (0..K)
        .map(|_| {
            let pool = BufferPool::new_grown(CHUNKS);
            let streams = Box::new(Streams::new(&stream::Config::new(false), &pool));
            Slot::new(Resources {
                pool,
                streams: Held::Owned(streams),
                loss: Shared::Counted(Rc::clone(&loss)),
                tables: Tables::sharing(&machines),
            })
        })
        .collect();
    let slots: Box<[NSlot; K]> = v.into_boxed_slice().try_into().ok().unwrap();
    Table { slots, loss }
}

fn big_stack(f: impl FnOnce() + Send + 'static) {
    let r = std::thread::Builder::new().stack_size(512 << 20).spawn(f).unwrap().join();
    if let Err(e) = r {
        std::panic::resume_unwind(e);
    }
}

/// A seeded `SplitMix64`: the link's only randomness.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// A host of one endpoint: key answers, access answers (allow), reads of streams and datagrams, every `Incoming`
/// taken; everything the endpoint said, in order, as lines.
struct Host<'s> {
    ep: Box<Ep<'s>>,
    addr: SocketAddr,
    id: NodeId,
    kp: Keypair,
    prekeys: SoftPrekeys<Software>,
    drbg: Drbg,
    log: Vec<String>,
    sessions: Vec<SessionId>,
    streams: Vec<(SessionId, u64)>,
}

fn identity(tag: u8) -> (Keypair, LocalIdentity) {
    let alg = IdentityAlg::Ed25519;
    let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    (kp, id)
}

fn config(tag: u8) -> EndpointConfig {
    let mut c = EndpointConfig::new(u64::from(tag).wrapping_mul(0x9E37_79B9));
    c.conn.max_gso = 4;
    c
}

impl<'s> Host<'s> {
    /// `slots`: the table to run in; `None` for an endpoint that owns its table.
    fn new(tag: u8, now: u64, slots: Option<&'s mut [NSlot; K]>) -> Self {
        let (kp, ident) = identity(tag);
        let ep_drbg = Drbg::new(&[tag ^ 0xa5; 32]);
        let mut ep: Box<Ep<'s>> = match slots {
            Some(t) => Box::new(Endpoint::new(now, Software, ep_drbg, ident, config(tag), t)),
            None => Endpoint::new_owned(now, Software, ep_drbg, ident, config(tag), CHUNKS, 4),
        };
        let mut drbg = Drbg::new(&[tag ^ 0x5a; 32]);
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
        ep.set_prekey(prekeys.acquire(&mut env).unwrap());
        for a in ALPNS {
            assert!(ep.register_alpn(a));
        }
        let addr: SocketAddr = ([10, 0, 0, tag], 4433).into();
        assert!(ep.add_iface(addr).is_some());
        ep.set_backlog_room(K);
        Self {
            ep,
            addr,
            id: ident.node_id(),
            kp,
            prekeys,
            drbg,
            log: Vec::new(),
            sessions: Vec::new(),
            streams: Vec::new(),
        }
    }

    fn note(&mut self, s: SessionId) {
        if !self.sessions.contains(&s) {
            self.sessions.push(s);
        }
    }

    fn cmd(&mut self, now: u64, c: Command<'_, NoSource>) -> Option<Value> {
        let what = format!("{c:?}");
        let r = self.ep.command(now, c);
        self.log.push(format!("{now} cmd {what} -> {:?}", r.as_ref().map(|r| r.value)));
        let rep = r.ok()?;
        for e in rep.events.iter().copied().collect::<Vec<Event>>() {
            self.on_event(now, e);
        }
        Some(rep.value)
    }

    fn on_event(&mut self, now: u64, e: Event) {
        self.log.push(format!("{now} ev {e:?}"));
        if let Some(s) = e.session() {
            self.note(s);
        }
        match e {
            Event::KeyRequest { session } => self.answer_keys(now, session),
            Event::AcpCheck { check, .. } => {
                let _ = self.cmd(now, Command::AcpAnswer { check, allow: true });
            },
            Event::StreamReadable { session, stream } => {
                if !self.streams.contains(&(session, stream)) {
                    self.streams.push((session, stream));
                }
                self.read_stream(now, session, stream);
            },
            Event::DatagramReceived { session } => {
                let mut buf = vec![0u8; 65_536];
                for _ in 0..1000 {
                    match self.ep.read_datagram(session, &mut buf) {
                        Ok(Some(n)) => self.log.push(format!("{now} dgram {session:?} {:?}", &buf[..n])),
                        Ok(None) | Err(_) => break,
                    }
                }
            },
            Event::Incoming { session, .. } => {
                let t: Taken = self.ep.session_taken(session);
                self.log.push(format!("{now} taken {session:?} {t:?}"));
            },
            _ => {},
        }
    }

    fn answer_keys(&mut self, now: u64, session: SessionId) {
        let soft = SoftKeys {
            signer: Some((KeyHandle(1), &self.kp)),
            prekeys: Some(&self.prekeys),
        };
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut self.drbg,
        };
        let mut sig = [0u8; pinc_crypto::identity::MAX_SIGNATURE_LEN];
        let response = match self.ep.query(Query::KeyRequest(session)) {
            Answer::KeyRequest(req) => match soft.answer(&mut env, &req, &mut sig) {
                KeyResponse::Signature(s) => KeyResponse::Signature(s),
                KeyResponse::SharedSecret(s) => KeyResponse::SharedSecret(s),
                KeyResponse::Failed => KeyResponse::Failed,
            },
            _ => return,
        };
        let _ = self.cmd(now, Command::KeyResponse { session, response });
    }

    fn read_stream(&mut self, now: u64, session: SessionId, stream: u64) {
        for _ in 0..10_000 {
            let chunk = match self.ep.query(Query::Read { session, stream }) {
                Answer::Chunk(c) if !c.is_empty() => c.to_vec(),
                _ => break,
            };
            self.log.push(format!("{now} read {session:?} {stream} {chunk:?}"));
            if self.cmd(now, Command::Consume { session, stream, n: chunk.len() }).is_none() {
                break;
            }
        }
        let _ = self.cmd(now, Command::Consume { session, stream, n: 0 });
    }

    fn service(&mut self, now: u64) {
        for _ in 0..100_000 {
            let Some(e) = self.ep.poll_event() else { return };
            self.on_event(now, e);
        }
        panic!("poll_event never ran dry");
    }

    /// The statistics of every session the host knows of and of the node, as lines.
    fn snapshot(&mut self) {
        for s in self.sessions.clone() {
            let st = match self.ep.query(Query::Stats(s)) {
                Answer::Stats(st) => format!("{st:?}"),
                a => format!("{a:?}"),
            };
            self.log.push(format!("stats {s:?} {st}"));
        }
        let ns = self.ep.node_stats();
        self.log.push(format!("node {ns:?}"));
        self.log.push(format!("timeout {:?}", self.ep.poll_timeout()));
    }
}

type Wire = Reverse<(u64, u64, usize, Vec<u8>)>;

/// Two hosts on one link: a delay, a per-mille loss from a seeded generator. Host 0 is the subject.
struct Net<'s> {
    hosts: [Host<'s>; 2],
    wires: BinaryHeap<Wire>,
    now: u64,
    seq: u64,
    rng: Rng,
    loss: u16,
}

impl<'s> Net<'s> {
    fn new(subject: Host<'s>, peer: Host<'s>, seed: u64, loss: u16, now: u64) -> Self {
        Self {
            hosts: [subject, peer],
            wires: BinaryHeap::new(),
            now,
            seq: 0,
            rng: Rng(seed),
            loss,
        }
    }

    fn pump(&mut self, n: usize) {
        let mut buf = vec![0u8; 65_536];
        let now = self.now;
        for _ in 0..20_000 {
            self.hosts[n].service(now);
            let Some(tx) = self.hosts[n].ep.poll_transmit(now, &mut buf) else {
                self.hosts[n].service(now);
                return;
            };
            assert!(tx.len <= buf.len() && tx.segment_size > 0, "a transmit past the buffer");
            for chunk in buf[..tx.len].chunks(tx.segment_size) {
                self.hosts[n].log.push(format!("{now} tx {} {} {chunk:?}", tx.local, tx.remote));
                if self.loss > 0 && self.rng.next() % 1000 < u64::from(self.loss) {
                    continue;
                }
                let Some(to) = self.hosts.iter().position(|h| h.addr == tx.remote) else { continue };
                self.seq += 1;
                self.wires.push(Reverse((now + 5 * MS, self.seq, to, chunk.to_vec())));
            }
        }
        panic!("poll_transmit never returned None");
    }

    fn pump_all(&mut self) {
        for _ in 0..3 {
            self.pump(0);
            self.pump(1);
        }
    }

    /// Run the link and the timers until `until`, every step bounded.
    fn run_until(&mut self, until: u64) {
        self.pump_all();
        for _ in 0..50_000 {
            let w = self.wires.peek().map(|Reverse(w)| w.0);
            let t = self.hosts.iter().filter_map(|h| h.ep.poll_timeout()).min();
            let next = match (w, t) {
                (Some(a), Some(b)) => a.min(b),
                (a, b) => match a.or(b) {
                    Some(x) => x,
                    None => break,
                },
            }
            .max(self.now);
            if next > until {
                break;
            }
            self.now = next;
            while self.wires.peek().is_some_and(|Reverse(w)| w.0 <= self.now) {
                let Some(Reverse((_, _, to, mut data))) = self.wires.pop() else { break };
                let (local, from) = (self.hosts[to].addr, self.hosts[1 - to].addr);
                let now = self.now;
                self.hosts[to].ep.handle_datagram(now, local, from, &mut data);
                self.hosts[to].service(now);
            }
            for h in &mut self.hosts {
                if h.ep.poll_timeout().is_some_and(|d| d <= self.now) {
                    h.ep.handle_timeout(self.now);
                    h.service(self.now);
                }
            }
            self.pump_all();
        }
        self.now = self.now.max(until);
    }

    fn apply(&mut self, op: &Op) {
        let now = self.now;
        let pick = |v: &[SessionId], i: u8| (!v.is_empty()).then(|| v[usize::from(i) % v.len()]);
        match *op {
            Op::Run(ms) => self.run_until(now + u64::from(ms) * MS),
            Op::Pump => self.pump_all(),
            Op::Dial(a) => {
                let (node, to) = (self.hosts[1].id, self.hosts[1].addr);
                let alpn = ALPNS[usize::from(a) % 2];
                if let Some(Value::Session(s)) =
                    self.hosts[0].cmd(now, Command::Connect { node, alpn, addrs: &[to], role: Role::Other })
                {
                    self.hosts[0].note(s);
                }
            },
            Op::Open(who, s, bidi) => {
                let h = &mut self.hosts[usize::from(who % 2)];
                let Some(session) = pick(&h.sessions, s) else { return };
                if let Some(Value::Stream(id)) = h.cmd(now, Command::OpenStream { session, bidi }) {
                    h.streams.push((session, id));
                }
            },
            Op::Write(who, s, len, fin) => {
                let h = &mut self.hosts[usize::from(who % 2)];
                if h.streams.is_empty() {
                    return;
                }
                let (session, stream) = h.streams[usize::from(s) % h.streams.len()];
                let data: Vec<u8> = (0..usize::from(len) * 37).map(|i| (i as u8) ^ s).collect();
                let _ = h.cmd(now, Command::Write { session, stream, data: &data });
                if fin {
                    let _ = h.cmd(now, Command::Finish { session, stream });
                }
            },
            Op::Datagram(who, s, len) => {
                let h = &mut self.hosts[usize::from(who % 2)];
                let Some(session) = pick(&h.sessions, s) else { return };
                let data = vec![s; usize::from(len)];
                let _ = h.cmd(now, Command::SendDatagram { session, data: &data });
            },
            Op::Reset(who, s) | Op::StopSending(who, s) | Op::Urgency(who, s, _) => {
                let h = &mut self.hosts[usize::from(who % 2)];
                if h.streams.is_empty() {
                    return;
                }
                let (session, stream) = h.streams[usize::from(s) % h.streams.len()];
                let c = match *op {
                    Op::Reset(..) => Command::Reset { session, stream, error: u64::from(s) },
                    Op::StopSending(..) => Command::StopSending { session, stream, error: u64::from(s) },
                    Op::Urgency(_, _, u) => Command::SetUrgency { session, stream, urgency: u % 8 },
                    _ => return,
                };
                let _ = h.cmd(now, c);
            },
            Op::Suspend(who) => {
                let _ = self.hosts[usize::from(who % 2)].cmd(now, Command::Suspend);
            },
            Op::Resume(who, moved) => {
                let _ = self.hosts[usize::from(who % 2)].cmd(now, Command::Resume { moved });
            },
            Op::Shutdown(who) => {
                let _ = self.hosts[usize::from(who % 2)].cmd(now, Command::Shutdown);
            },
            Op::Close(who, s) => {
                let h = &mut self.hosts[usize::from(who % 2)];
                let Some(session) = pick(&h.sessions, s) else { return };
                let _ = h.cmd(now, Command::Close { session, error: u64::from(s) });
            },
        }
    }
}

/// One step of a script. Host 0 is the subject, host 1 its peer; `who` picks one by parity. Session and stream
/// picks index the host's own list (modulo its length).
#[derive(Debug, Clone, Copy, PartialEq, Eq, ephyra::Arbitrary)]
enum Op {
    Pump,
    Run(#[ephyra(gen = gens::int(1u16..=3000))] u16),
    Dial(u8),
    Open(u8, u8, bool),
    Write(u8, u8, #[ephyra(gen = gens::int(1u16..=600))] u16, bool),
    Datagram(u8, u8, #[ephyra(gen = gens::int(1u16..=900))] u16),
    Close(u8, u8),
    Reset(u8, u8),
    StopSending(u8, u8),
    Urgency(u8, u8, u8),
    Suspend(u8),
    Resume(u8, bool),
    Shutdown(u8),
}

/// A history on the table, how it ends, then a script run on a fresh table and on the used one.
#[derive(Debug, Clone, ephyra::Arbitrary)]
struct Case {
    #[ephyra(gen = gens::vec(ephyra::any::<Op>()).len(0..=30))]
    history: Vec<Op>,
    /// Let the history's endpoint send what it has before it ends (else it ends mid-step).
    drain: bool,
    #[ephyra(gen = gens::vec(ephyra::any::<Op>()).len(1..=24))]
    script: Vec<Op>,
    #[ephyra(gen = gens::frequency(vec![(3, gens::constant(0u16).boxed()), (1, gens::int(0u16..=300).boxed())]))]
    loss: u16,
    seed: u64,
}

const T0: u64 = 10 * SEC;

/// Run `script` with host 0 on `slots` (or a fresh owned table for the peer) and return both logs, session ids
/// renamed, and the table back.
fn play<'s>(slots: &'s mut [NSlot; K], c: &Case) -> (Vec<String>, Option<&'s mut [NSlot; K]>) {
    let subject = Host::new(1, T0, Some(slots));
    let peer = Host::new(2, T0, None);
    let mut net = Net::new(subject, peer, c.seed, c.loss, T0);
    // Every script starts with a dial, so a session exists for the rest to act on.
    net.apply(&Op::Dial(0));
    for op in &c.script {
        net.apply(op);
    }
    net.run_until(net.now + 2 * SEC);
    let [mut a, mut b] = net.hosts;
    a.snapshot();
    b.snapshot();
    let mut log: Vec<String> = a.log.iter().map(|l| format!("A {l}")).collect();
    log.extend(b.log.iter().map(|l| format!("B {l}")));
    (rename(&log), a.ep.into_slots())
}

/// Replace every `SessionId(n)` by `S<k>`, k counted per host side in order of first appearance.
fn rename(log: &[String]) -> Vec<String> {
    let mut seen: Vec<(char, u64)> = Vec::new();
    log.iter()
        .map(|l| {
            let side = l.chars().next().unwrap_or(' ');
            let mut out = String::with_capacity(l.len());
            let mut rest = l.as_str();
            while let Some(at) = rest.find("SessionId(") {
                out.push_str(&rest[..at]);
                let tail = &rest[at + 10..];
                let end = tail.find(')').unwrap_or(tail.len());
                let n: u64 = tail[..end].parse().unwrap_or(u64::MAX);
                let k = seen.iter().position(|x| *x == (side, n)).unwrap_or_else(|| {
                    seen.push((side, n));
                    seen.len() - 1
                });
                let _ = write!(out, "S{k}");
                rest = &tail[(end + 1).min(tail.len())..];
            }
            out.push_str(rest);
            out
        })
        .collect()
}

/// Run the history on endpoint X over `t` (tag 3, its own peer), end it as the case says and give the table back.
fn used<'s>(t: &'s mut [NSlot; K], c: &Case, drain: bool) -> &'s mut [NSlot; K] {
    let x = Host::new(3, T0, Some(t));
    let peer = Host::new(4, T0, None);
    let mut net = Net::new(x, peer, c.seed ^ 1, c.loss, T0);
    for op in &c.history {
        net.apply(op);
    }
    if c.drain || drain {
        net.pump_all();
    }
    let [x, _] = net.hosts;
    if drain {
        assert!(!x.ep.transmit_waiting(), "the history's endpoint still has something to send after poll_transmit said None");
    }
    let back = x.ep.into_slots();
    assert!(back.is_some(), "into_slots kept the table: a construction failed and took a slot's memory");
    back.unwrap()
}

fn first_difference(a: &[String], b: &[String]) -> String {
    let i = a.iter().zip(b).position(|(x, y)| x != y).unwrap_or(a.len().min(b.len()));
    let at = |v: &[String]| v.get(i).map_or("<end>".to_owned(), |s| s.chars().take(400).collect());
    format!("line {i} of {} / {}:\n  fresh: {}\n  used:  {}", a.len(), b.len(), at(a), at(b))
}

fn prop(c: &Case, drain: bool) {
    let mut fresh = table();
    let mut control = table();
    let mut usedt = table();
    let (want, _) = play(&mut fresh.slots, c);
    let (again, _) = play(&mut control.slots, c);
    assert!(want == again, "the driver is not deterministic: {}", first_difference(&want, &again));
    let back = used(&mut usedt.slots, c, drain);
    usedt.loss.reset();
    let (got, _) = play(back, c);
    if want != got {
        // Name the failure by what the first differing lines are (a datagram, an event, a reply, a statistic), so a
        // long run with several failures keeps distinct leaks apart.
        let i = want.iter().zip(&got).position(|(x, y)| x != y).unwrap_or(want.len().min(got.len()));
        let kind = |v: &[String]| v.get(i).and_then(|l| l.split(' ').nth(2)).unwrap_or("end").to_owned();
        ephyra::signature(format!("used table differs: {} vs {}", kind(&want), kind(&got)));
    }
    assert!(want == got, "an endpoint on a used table behaves otherwise: {}", first_difference(&want, &got));
}

#[test]
fn an_endpoint_on_a_used_table_behaves_as_on_a_fresh_one() {
    big_stack(|| {
        let config = ephyra::Config::default().tests(40).name("an_endpoint_on_a_used_table_behaves_as_on_a_fresh_one");
        ephyra::check(&config, ephyra::any::<Case>(), |c: Case| prop(&c, false)).assert_passed();
    });
}

/// The same, with the history's endpoint drained (`poll_transmit` until `None`) before it ends: a host that does
/// so avoids the known leak of a slot's send-queue mark (`repro_slots.rs`), so a failure here is another field.
#[test]
fn an_endpoint_on_a_table_given_back_drained_behaves_as_on_a_fresh_one() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(40)
            .name("an_endpoint_on_a_table_given_back_drained_behaves_as_on_a_fresh_one");
        ephyra::check(&config, ephyra::any::<Case>(), |c: Case| prop(&c, true)).assert_passed();
    });
}

#[test]
fn the_slot_case_generator_stays_in_support() {
    let ok = |c: &Case| c.history.len() <= 30 && (1..=24).contains(&c.script.len()) && c.loss <= 300;
    check_generator(&ephyra::Config::default().tests(300), ephyra::any::<Case>(), move |c: &Case| ok(c)).assert_passed();
}
