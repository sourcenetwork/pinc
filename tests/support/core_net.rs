//! A small deterministic pump for `vinc-core` endpoints: nodes, an in-memory network and the host duties a node
//! performs (answering key requests and access checks, reading streams).
//!
//! [`CoreNet`] carries datagrams between [`TNode`]s with one fixed one-way delay (and optional loss by a closure),
//! on virtual time. It does not depend on the simulator crate.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::missing_panics_doc,
    clippy::missing_errors_doc,
    clippy::must_use_candidate,
    clippy::new_without_default,
    clippy::large_stack_arrays
)]

use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap};
use std::fmt::Write as _;
use std::net::SocketAddr;

use vinc_core::{
    Answer, Command, CommandError, Endpoint, EndpointConfig, Event, Query, Reply, Role, SessionId, Slot, Transmit,
    Value,
};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use vinc_security::{Env, KeyHandle, KeyResponse, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys};
use vinc_transport::conn::{Machines, Resources, Tables};
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::BufferPool;
use vinc_transport::stream::{self, NoSource, RecvStatus, Streams};

use crate::{Caps, SplitMix64};

pub const CN: usize = 8;
pub const CC: usize = 17;
pub const CF: usize = 128;
pub const CNP: usize = 4;
pub const CK: usize = 8;
pub const CD: usize = 128;
pub const CPK: usize = 8;
pub const CTK: usize = 16;
pub const CCT: usize = 8;
pub const CHUNKS_PER_CONN: usize = 128;
pub const SEC_NS: u64 = 1_000_000_000;
pub const MS_NS: u64 = 1_000_000;

pub type CoreEp = Endpoint<'static, 'static, Caps, NoSource, CN, CC, CF, CNP, CK, CD, CPK, CTK, CCT>;
pub type CoreSlot = Slot<'static, Caps, NoSource, CN, CC, CF, CNP>;

pub const ALPN_A: &[u8] = b"vinc/a";
pub const ALPN_B: &[u8] = b"vinc/b";

/// The memory of one connection, leaked for the life of the test.
pub fn memory(client: bool) -> Resources<'static, NoSource, CN, CC, CF> {
    memory_sharing(client, &Machines::new())
}

/// The memory of one connection whose handshake machines come from the node's pool `machines`.
pub fn memory_sharing(client: bool, machines: &Machines) -> Resources<'static, NoSource, CN, CC, CF> {
    let pool = BufferPool::new_boxed(CHUNKS_PER_CONN);
    let streams: &'static mut Streams<NoSource, CN, CC> =
        Box::leak(Box::new(Streams::new(&stream::Config::new(client), &pool)));
    let loss: &'static LossEstimate = Box::leak(Box::new(LossEstimate::new()));
    Resources {
        pool,
        streams: streams.into(),
        loss: loss.into(),
        tables: Tables::sharing(machines),
    }
}

/// A leaked slot table of `CK` free slots.
pub fn slots() -> &'static mut [CoreSlot; CK] {
    let machines = Machines::new();
    let v: Vec<CoreSlot> = (0..CK).map(|_| Slot::new(memory_sharing(false, &machines))).collect();
    let b: Box<[CoreSlot; CK]> = v.into_boxed_slice().try_into().ok().unwrap();
    Box::leak(b)
}

/// How a node answers access checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Acp {
    Allow,
    Deny,
    /// Leave the check for the test to answer.
    Manual,
}

thread_local! {
    static METER: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static METERED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static METERED_BYTES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Count the heap allocations of every endpoint call from now on (needs the counting allocator in the test target).
pub fn meter_endpoint_calls(on: bool) {
    METER.with(|m| m.set(on));
}

/// The allocations counted since the counter was last taken; resets it.
pub fn take_metered_allocs() -> u64 {
    METERED.with(|c| c.replace(0))
}

/// The heap bytes requested since the counter was last taken; resets it.
pub fn take_metered_bytes() -> u64 {
    METERED_BYTES.with(|c| c.replace(0))
}

/// Run an endpoint call, counting its allocations while metering is on.
pub fn metered<R>(f: impl FnOnce() -> R) -> R {
    if !METER.with(std::cell::Cell::get) {
        return f();
    }
    let mut out = None;
    let st = crate::measure(|| out = Some(f()));
    METERED.with(|c| c.set(c.get() + st.count()));
    METERED_BYTES.with(|c| c.set(c.get() + st.bytes));
    out.unwrap()
}

/// A host: an endpoint with its key material, address and what it saw.
pub struct TNode {
    pub ep: Box<CoreEp>,
    pub addr: SocketAddr,
    /// Further local addresses the node answers on.
    pub extra: Vec<SocketAddr>,
    pub node: NodeId,
    pub prov: Caps,
    pub drbg: Drbg,
    pub kp: Keypair,
    pub prekeys: SoftPrekeys<Caps>,
    pub events: Vec<(u64, Event)>,
    pub acp: Acp,
    pub auto_read: bool,
    /// Close every incoming session as soon as it is reported, as a host that refuses a duplicate does.
    pub close_incoming: bool,
    /// Bytes written on a new stream of every dialed session as soon as it is reported connected.
    pub write_on_connect: Option<Vec<u8>>,
    pub read: HashMap<(SessionId, u64), Vec<u8>>,
    pub fin: Vec<(SessionId, u64)>,
    pub checks: Vec<(u64, NodeId)>,
    /// Datagrams sent: time, destination, length.
    pub sent: Vec<(u64, SocketAddr, usize)>,
}

impl TNode {
    pub fn new(tag: u8, addr: SocketAddr, now: u64) -> Self {
        Self::with_alg(tag, addr, now, IdentityAlg::Ed25519)
    }

    /// A node whose identity uses `alg`.
    pub fn with_alg(tag: u8, addr: SocketAddr, now: u64, alg: IdentityAlg) -> Self {
        Self::with_mtu(tag, addr, now, alg, 1500)
    }

    /// A node whose identity uses `alg` and whose interface carries datagrams of up to `mtu` bytes.
    pub fn with_mtu(tag: u8, addr: SocketAddr, now: u64, alg: IdentityAlg, mtu: u16) -> Self {
        let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
        let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
        let prov = Caps(Software, true);
        let mut drbg = Drbg::new(&[tag ^ 0x5a; 32]);
        let mut cfg = EndpointConfig::new(u64::from(tag) * 0x9E37_79B9);
        cfg.conn.max_gso = 4;
        cfg.conn.interface_mtu = mtu;
        let ep_drbg = Drbg::new(&[tag ^ 0xa5; 32]);
        let mut ep = Box::new(Endpoint::new(now, prov, ep_drbg, identity, cfg, slots()));
        let mut env = Env {
            provider: &prov,
            now,
            drbg: &mut drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
        ep.set_prekey(prekeys.acquire(&mut env).unwrap());
        assert!(ep.register_alpn(ALPN_A));
        assert!(ep.register_alpn(ALPN_B));
        let ifc = ep.add_iface(addr).unwrap();
        let _ = ifc;
        Self {
            ep,
            addr,
            extra: Vec::new(),
            node: identity.node_id(),
            prov,
            drbg,
            kp,
            prekeys,
            events: Vec::new(),
            acp: Acp::Allow,
            auto_read: true,
            close_incoming: false,
            write_on_connect: None,
            read: HashMap::new(),
            fin: Vec::new(),
            checks: Vec::new(),
            sent: Vec::new(),
        }
    }

    pub fn cmd(&mut self, now: u64, c: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        let r = metered(|| self.ep.command(now, c));
        if let Ok(rep) = &r {
            for e in rep.events.iter() {
                self.events.push((now, *e));
            }
            // Sync events also need the host duties (an ACP check can be raised at once).
            for e in rep.events.iter() {
                self.react(now, *e);
            }
        }
        r
    }

    pub fn connect(
        &mut self,
        now: u64,
        peer: NodeId,
        alpn: &[u8],
        to: SocketAddr,
        role: Role,
    ) -> Result<Reply, CommandError> {
        self.cmd(
            now,
            Command::Connect {
                node: peer,
                alpn,
                addrs: &[to],
                role,
            },
        )
    }

    pub fn session(&self, rep: &Reply) -> SessionId {
        match rep.value {
            Value::Session(s) => s,
            v => panic!("not a session: {v:?}"),
        }
    }

    /// Answer a key request of `session` with software keys.
    fn answer_keys(&mut self, now: u64, session: SessionId) {
        let soft = SoftKeys {
            signer: Some((KeyHandle(1), &self.kp)),
            prekeys: Some(&self.prekeys),
        };
        let mut env = Env {
            provider: &self.prov,
            now,
            drbg: &mut self.drbg,
        };
        let mut sig = [0u8; vinc_crypto::identity::MAX_SIGNATURE_LEN];
        let resp = match self.ep.query(Query::KeyRequest(session)) {
            Answer::KeyRequest(req) => match soft.answer(&mut env, &req, &mut sig) {
                KeyResponse::Signature(s) => KeyResponse::Signature(s),
                KeyResponse::SharedSecret(s) => KeyResponse::SharedSecret(s),
                KeyResponse::Failed => KeyResponse::Failed,
            },
            _ => return,
        };
        let r = metered(|| {
            self.ep.command(
                now,
                Command::KeyResponse {
                    session,
                    response: resp,
                },
            )
        });
        if let Ok(rep) = r {
            for e in rep.events.iter() {
                self.events.push((now, *e));
            }
            for e in rep.events.iter() {
                self.react(now, *e);
            }
        }
    }

    /// Host duties for one event.
    fn react(&mut self, now: u64, ev: Event) {
        match ev {
            Event::KeyRequest { session } => self.answer_keys(now, session),
            Event::AcpCheck { check, node, .. } => match self.acp {
                Acp::Allow => {
                    let _ = self.cmd(now, Command::AcpAnswer { check, allow: true });
                }
                Acp::Deny => {
                    let _ = self.cmd(now, Command::AcpAnswer { check, allow: false });
                }
                Acp::Manual => self.checks.push((check, node)),
            },
            Event::StreamReadable { session, stream } if self.auto_read => self.read_stream(now, session, stream),
            Event::Incoming { session, .. } if self.close_incoming => {
                let _ = self.cmd(now, Command::Close { session, error: 0 });
            }
            Event::Connected { session, .. } if self.write_on_connect.is_some() => {
                let data = self.write_on_connect.clone().unwrap_or_default();
                if let Ok(Value::Stream(stream)) = self
                    .cmd(now, Command::OpenStream { session, bidi: true })
                    .map(|r| r.value)
                {
                    let _ = self.cmd(
                        now,
                        Command::Write {
                            session,
                            stream,
                            data: &data,
                        },
                    );
                }
            }
            _ => {}
        }
    }

    pub fn read_stream(&mut self, now: u64, session: SessionId, stream: u64) {
        loop {
            let chunk = match metered(|| self.ep.query(Query::Read { session, stream })) {
                Answer::Chunk(c) if !c.is_empty() => c.to_vec(),
                _ => break,
            };
            self.read
                .entry((session, stream))
                .or_default()
                .extend_from_slice(&chunk);
            if let Ok(rep) = metered(|| {
                self.ep.command(
                    now,
                    Command::Consume {
                        session,
                        stream,
                        n: chunk.len(),
                    },
                )
            }) {
                for e in rep.events.iter() {
                    self.events.push((now, *e));
                }
                if rep.value == Value::Recv(RecvStatus::Finished) {
                    self.fin.push((session, stream));
                }
            }
        }
        if let Ok(rep) = metered(|| self.ep.command(now, Command::Consume { session, stream, n: 0 }))
            && rep.value == Value::Recv(RecvStatus::Finished)
            && !self.fin.contains(&(session, stream))
        {
            self.fin.push((session, stream));
        }
    }

    /// Drain events, performing host duties.
    pub fn service(&mut self, now: u64) {
        while let Some(e) = metered(|| self.ep.poll_event()) {
            self.events.push((now, e));
            self.react(now, e);
        }
    }

    pub fn saw(&self, f: impl Fn(&Event) -> bool) -> bool {
        self.events.iter().any(|(_, e)| f(e))
    }

    pub fn count(&self, f: impl Fn(&Event) -> bool) -> usize {
        self.events.iter().filter(|(_, e)| f(e)).count()
    }

    pub fn time_of(&self, f: impl Fn(&Event) -> bool) -> Option<u64> {
        self.events.iter().find(|(_, e)| f(e)).map(|(t, _)| *t)
    }
}

#[derive(Debug)]
struct Wire {
    at: u64,
    seq: u64,
    to: SocketAddr,
    from: SocketAddr,
    data: Vec<u8>,
}
impl PartialEq for Wire {
    fn eq(&self, o: &Self) -> bool {
        (self.at, self.seq) == (o.at, o.seq)
    }
}
impl Eq for Wire {}
impl PartialOrd for Wire {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Wire {
    fn cmp(&self, o: &Self) -> Ordering {
        (o.at, o.seq).cmp(&(self.at, self.seq))
    }
}

/// Decides whether a datagram `(from, to, data)` is lost.
pub type LossFn = Box<dyn FnMut(SocketAddr, SocketAddr, &[u8]) -> bool>;

/// Nodes on one network with a fixed one-way delay, on virtual time.
pub struct CoreNet {
    pub nodes: Vec<TNode>,
    wires: BinaryHeap<Wire>,
    pub now: u64,
    pub delay: u64,
    /// Up to this much extra delay per datagram, drawn independently, so datagrams may overtake each other.
    pub jitter: u64,
    seq: u64,
    pub loss: Option<LossFn>,
    /// A NAT in front of one node: `(inside, outside)`. Datagrams the node sends carry the outside address as their
    /// source, datagrams to the outside address reach the node, and datagrams to the inside address reach nobody.
    pub nat: Option<(SocketAddr, SocketAddr)>,
    pub rng: SplitMix64,
    pub delivered: u64,
    /// Transmits that carried more than one datagram.
    pub batches: u64,
    /// Keep a copy of every datagram sent (from, to, bytes).
    pub capture: bool,
    pub captured: Vec<(SocketAddr, SocketAddr, Vec<u8>)>,
    pub tapped: Vec<(u64, SocketAddr, SocketAddr, usize)>,
}

impl CoreNet {
    pub fn new(delay: u64) -> Self {
        Self {
            nodes: Vec::new(),
            wires: BinaryHeap::new(),
            now: 10 * SEC_NS,
            delay,
            jitter: 0,
            seq: 0,
            loss: None,
            nat: None,
            rng: SplitMix64::new(1),
            delivered: 0,
            batches: 0,
            capture: false,
            captured: Vec::new(),
            tapped: Vec::new(),
        }
    }

    pub fn add(&mut self, tag: u8) -> usize {
        self.add_with_alg(tag, IdentityAlg::Ed25519)
    }

    pub fn add_with_alg(&mut self, tag: u8, alg: IdentityAlg) -> usize {
        let addr: SocketAddr = ([10, 0, 0, tag], 4433).into();
        self.nodes.push(TNode::with_alg(tag, addr, self.now, alg));
        self.nodes.len() - 1
    }

    pub fn node_at(&self, a: SocketAddr) -> Option<usize> {
        self.nodes.iter().position(|n| n.addr == a || n.extra.contains(&a))
    }

    /// Put a datagram on the wire as if `from` had sent it (a spoofed or replayed packet).
    pub fn inject(&mut self, from: SocketAddr, to: SocketAddr, data: Vec<u8>, delay: u64) {
        self.seq += 1;
        self.wires.push(Wire {
            at: self.now + delay,
            seq: self.seq,
            to,
            from,
            data,
        });
    }

    /// Let node `n` send everything it has and handle its events.
    pub fn pump(&mut self, n: usize) {
        loop {
            let now = self.now;
            self.nodes[n].service(now);
            let mut buf = vec![0u8; 65_536];
            let node = &mut self.nodes[n];
            let Some(Transmit {
                local,
                remote,
                len,
                segment_size,
            }) = metered(|| node.ep.poll_transmit(now, &mut buf))
            else {
                node.service(now);
                if node.ep.poll_event().is_none() {
                    break;
                }
                continue;
            };
            if len > segment_size {
                self.batches += 1;
            }
            for chunk in buf[..len].chunks(segment_size) {
                node.sent.push((now, remote, chunk.len()));
                self.tapped.push((now, local, remote, chunk.len()));
                if self.capture {
                    self.captured.push((local, remote, chunk.to_vec()));
                }
                let lost = self.loss.as_mut().is_some_and(|f| f(local, remote, chunk));
                if !lost {
                    self.seq += 1;
                    let from = match self.nat {
                        Some((inside, outside)) if local == inside => outside,
                        _ => local,
                    };
                    let extra = if self.jitter > 0 {
                        self.rng.next_u64() % self.jitter
                    } else {
                        0
                    };
                    self.wires.push(Wire {
                        at: now + self.delay + extra,
                        seq: self.seq,
                        to: remote,
                        from,
                        data: chunk.to_vec(),
                    });
                }
            }
        }
    }

    pub fn pump_all(&mut self) {
        for _ in 0..8 {
            for n in 0..self.nodes.len() {
                self.pump(n);
            }
        }
    }

    fn next_time(&self) -> Option<u64> {
        let w = self.wires.peek().map(|w| w.at);
        let t = self.nodes.iter().filter_map(|n| n.ep.poll_timeout()).min();
        match (w, t) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        }
    }

    /// Run until `deadline` or until `stop` says so; returns whether `stop` fired.
    pub fn run(&mut self, deadline: u64, mut stop: impl FnMut(&mut Self) -> bool) -> bool {
        self.pump_all();
        let mut steps = 0u64;
        loop {
            steps += 1;
            if steps >= 200_000 {
                let mut tr = String::new();
                for (k, n) in self.nodes.iter_mut().enumerate() {
                    let mut v = Vec::new();
                    while let Some(r) = n.ep.poll_trace() {
                        v.push(r);
                    }
                    for r in v.iter().rev().take(12).rev() {
                        write!(tr, "node {k} ").unwrap();
                        r.write_ndjson(&mut tr).unwrap();
                    }
                }
                panic!(
                    "the pump spins at {}: timeouts {:?}\n{tr}",
                    self.now,
                    self.nodes.iter().map(|n| n.ep.poll_timeout()).collect::<Vec<_>>()
                );
            }
            if stop(self) {
                return true;
            }
            let Some(t) = self.next_time() else { return false };
            let t = t.max(self.now);
            if t > deadline {
                self.now = deadline;
                return stop(self);
            }
            self.now = t;
            while self.wires.peek().is_some_and(|w| w.at <= self.now) {
                let w = self.wires.pop().unwrap();
                let to = match self.nat {
                    Some((inside, outside)) if w.to == outside => inside,
                    Some((inside, _)) if w.to == inside => SocketAddr::from(([0, 0, 0, 0], 0)),
                    _ => w.to,
                };
                if let Some(i) = self.node_at(to) {
                    let mut data = w.data;
                    self.delivered += 1;
                    let (t, from) = (self.now, w.from);
                    metered(|| self.nodes[i].ep.handle_datagram(t, to, from, &mut data));
                    let now = self.now;
                    self.nodes[i].service(now);
                }
            }
            for n in 0..self.nodes.len() {
                if self.nodes[n].ep.poll_timeout().is_some_and(|t| t <= self.now) {
                    let now = self.now;
                    metered(|| self.nodes[n].ep.handle_timeout(now));
                }
            }
            self.pump_all();
        }
    }

    /// Dial from node `a` to node `b` for `alpn` and run until `a` reports Connected and `b` reports Incoming.
    pub fn connect_pair(&mut self, a: usize, b: usize, alpn: &[u8], role: Role) -> (SessionId, SessionId) {
        let (peer, to, now) = (self.nodes[b].node, self.nodes[b].addr, self.now);
        let na = self.nodes[a].count(|e| matches!(e, Event::Connected { .. }));
        let nb = self.nodes[b].count(|e| matches!(e, Event::Incoming { .. }));
        let rep = self.nodes[a].connect(now, peer, alpn, to, role).unwrap();
        let sa = self.nodes[a].session(&rep);
        let ok = self.run(now + 10 * SEC_NS, |n| {
            n.nodes[a].count(|e| matches!(e, Event::Connected { .. })) > na
                && n.nodes[b].count(|e| matches!(e, Event::Incoming { .. })) > nb
        });
        assert!(
            ok,
            "no session: {:?} / {:?}",
            self.nodes[a].events, self.nodes[b].events
        );
        let sb = self.nodes[b]
            .events
            .iter()
            .rev()
            .find_map(|(_, e)| {
                if let Event::Incoming { session, .. } = e {
                    Some(*session)
                } else {
                    None
                }
            })
            .unwrap();
        (sa, sb)
    }

    /// Run for `span` nanoseconds of virtual time.
    pub fn run_for(&mut self, span: u64) {
        let end = self.now + span;
        self.run(end, |_| false);
        self.now = end;
    }
}
