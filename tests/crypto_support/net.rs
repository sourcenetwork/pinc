//! The test network of the crypto scenario tests: endpoints on the tracked provider, a pump with one fixed delay,
//! and a scan of every datagram put on the wire.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::type_complexity,
    missing_docs,
    unreachable_pub,
    dead_code
)]

use std::cmp::Ordering;
use std::collections::{BTreeSet, BinaryHeap, HashMap};
use std::net::SocketAddr;

use pinc_core::{
    Answer, Command, Endpoint, EndpointConfig, Event, Query, Reply, Role, SessionId, Slot, Transmit, Value,
};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use pinc_security::{Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys};
use pinc_sim::suite::crypto::{MsgId, Registry, Term, TermId, Tracked};
use pinc_tests::{ALPN_A, CC, CCT, CD, CF, CK, CN, CNP, CPK, CTK, MS_NS, SEC_NS, memory};
use pinc_transport::stream::{NoSource, RecvStatus};

pub type Ep = Endpoint<'static, 'static, Tracked, NoSource, CN, CC, CF, CNP, CK, CD, CPK, CTK, CCT>;
pub type Sl = Slot<'static, Tracked, NoSource, CN, CC, CF, CNP>;

pub fn slots() -> &'static mut [Sl; CK] {
    let v: Vec<Sl> = (0..CK).map(|_| Slot::new(memory(false))).collect();
    let b: Box<[Sl; CK]> = v.into_boxed_slice().try_into().ok().unwrap();
    Box::leak(b)
}

pub struct Host {
    pub ep: Box<Ep>,
    pub addr: SocketAddr,
    pub node: NodeId,
    pub prov: Tracked,
    pub drbg: Drbg,
    pub kp: Keypair,
    pub identity_seed: Vec<u8>,
    pub prekeys: SoftPrekeys<Tracked>,
    pub events: Vec<Event>,
    pub read: HashMap<(SessionId, u64), Vec<u8>>,
    pub fin: Vec<(SessionId, u64)>,
}

impl Host {
    pub fn new(reg: &'static Registry, idx: usize, now: u64) -> Self {
        let tag = idx as u8 + 1;
        let addr: SocketAddr = ([10, 0, 0, tag], 4433).into();
        let identity_seed = vec![tag; IdentityAlg::Ed25519.seed_len()];
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &identity_seed).unwrap();
        let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
        let prov = Tracked::new(reg, idx, Software);
        let mut drbg = Drbg::new(&[tag ^ 0x5a; 32]);
        let mut cfg = EndpointConfig::new(u64::from(tag) * 0x9E37_79B9);
        cfg.conn.max_gso = 4;
        let mut ep = Box::new(Endpoint::new(
            now,
            prov,
            Drbg::new(&[tag ^ 0xa5; 32]),
            identity,
            cfg,
            slots(),
        ));
        let mut env = Env {
            provider: &prov,
            now,
            drbg: &mut drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
        ep.set_prekey(prekeys.acquire(&mut env).unwrap());
        assert!(ep.register_alpn(ALPN_A));
        ep.add_iface(addr).unwrap();
        Self {
            node: identity.node_id(),
            ep,
            addr,
            prov,
            drbg,
            kp,
            identity_seed,
            prekeys,
            events: Vec::new(),
            read: HashMap::new(),
            fin: Vec::new(),
        }
    }

    pub fn cmd(&mut self, now: u64, c: Command<'_, NoSource>) -> Reply {
        let rep = self.ep.command(now, c).unwrap();
        for e in rep.events.iter() {
            self.events.push(*e);
            self.react(now, *e);
        }
        rep
    }

    fn react(&mut self, now: u64, ev: Event) {
        match ev {
            Event::KeyRequest { session } => {
                let soft = SoftKeys {
                    signer: Some((KeyHandle(1), &self.kp)),
                    prekeys: Some(&self.prekeys),
                };
                let mut env = Env {
                    provider: &self.prov,
                    now,
                    drbg: &mut self.drbg,
                };
                let mut sig = [0u8; pinc_crypto::identity::MAX_SIGNATURE_LEN];
                let Answer::KeyRequest(req) = self.ep.query(Query::KeyRequest(session)) else {
                    return;
                };
                let response = soft.answer(&mut env, &req, &mut sig);
                self.prov.registry().note_sign(self.prov.node(), 64);
                if let Ok(rep) = self.ep.command(now, Command::KeyResponse { session, response }) {
                    for e in rep.events.iter() {
                        self.events.push(*e);
                        self.react(now, *e);
                    }
                }
            }
            Event::AcpCheck { check, .. } => {
                let _ = self.cmd(now, Command::AcpAnswer { check, allow: true });
            }
            Event::StreamReadable { session, stream } => self.read_stream(now, session, stream),
            _ => {}
        }
    }

    fn read_stream(&mut self, now: u64, session: SessionId, stream: u64) {
        while let Answer::Chunk(c) = self.ep.query(Query::Read { session, stream }) {
            if c.is_empty() {
                break;
            }
            let chunk = c.to_vec();
            self.read
                .entry((session, stream))
                .or_default()
                .extend_from_slice(&chunk);
            let rep = self
                .ep
                .command(
                    now,
                    Command::Consume {
                        session,
                        stream,
                        n: chunk.len(),
                    },
                )
                .unwrap();
            if rep.value == Value::Recv(RecvStatus::Finished) {
                self.fin.push((session, stream));
            }
        }
        if let Ok(rep) = self.ep.command(now, Command::Consume { session, stream, n: 0 })
            && rep.value == Value::Recv(RecvStatus::Finished)
            && !self.fin.contains(&(session, stream))
        {
            self.fin.push((session, stream));
        }
    }

    fn service(&mut self, now: u64) {
        while let Some(e) = self.ep.poll_event() {
            self.events.push(e);
            self.react(now, e);
        }
    }
}

pub struct Wire {
    at: u64,
    pub seq: u64,
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

/// What the datagram scans of a run found.
#[derive(Default, Debug)]
pub struct WireLog {
    pub datagrams: usize,
    pub plaintext: usize,
    pub third_party: usize,
}

pub struct Net {
    pub reg: &'static Registry,
    pub hosts: Vec<Host>,
    pub wires: BinaryHeap<Wire>,
    pub now: u64,
    pub seq: u64,
    pub log: WireLog,
}

impl Net {
    pub fn new(seed: u64) -> Self {
        let net = Self::untraced(seed);
        net.reg.install();
        net
    }

    /// A network whose ledger does not observe the key derivations.
    pub fn untraced(seed: u64) -> Self {
        let reg = Registry::leak(seed);
        Self {
            reg,
            hosts: Vec::new(),
            wires: BinaryHeap::new(),
            now: 10 * SEC_NS,
            seq: 0,
            log: WireLog::default(),
        }
    }

    pub fn add(&mut self) -> usize {
        let idx = self.hosts.len();
        self.hosts.push(Host::new(self.reg, idx, self.now));
        idx
    }

    pub fn pump(&mut self, n: usize) {
        loop {
            let now = self.now;
            self.reg.now.set(now);
            self.reg.enter(n);
            self.hosts[n].service(now);
            let mut buf = vec![0u8; 65_536];
            let h = &mut self.hosts[n];
            let Some(Transmit {
                local,
                remote,
                len,
                segment_size,
            }) = h.ep.poll_transmit(now, &mut buf)
            else {
                h.service(now);
                if h.ep.poll_event().is_none() {
                    break;
                }
                continue;
            };
            for chunk in buf[..len].chunks(segment_size) {
                let scan = self.reg.scan_wire(n, chunk);
                self.log.datagrams += 1;
                self.log.plaintext += usize::from(scan.plaintext_payload);
                self.log.third_party += usize::from(scan.third_party);
                self.seq += 1;
                self.wires.push(Wire {
                    at: now + 5 * MS_NS,
                    seq: self.seq,
                    to: remote,
                    from: local,
                    data: chunk.to_vec(),
                });
            }
        }
    }

    pub fn pump_all(&mut self) {
        for _ in 0..8 {
            for n in 0..self.hosts.len() {
                self.pump(n);
            }
        }
    }

    pub fn run(&mut self, deadline: u64, mut stop: impl FnMut(&mut Self) -> bool) -> bool {
        self.pump_all();
        for _ in 0..200_000 {
            if stop(self) {
                return true;
            }
            let w = self.wires.peek().map(|w| w.at);
            let t = self.hosts.iter().filter_map(|h| h.ep.poll_timeout()).min();
            let Some(t) = [w, t].into_iter().flatten().min() else {
                return false;
            };
            let t = t.max(self.now);
            if t > deadline {
                self.now = deadline;
                return stop(self);
            }
            self.now = t;
            self.reg.now.set(t);
            while self.wires.peek().is_some_and(|w| w.at <= self.now) {
                let mut w = self.wires.pop().unwrap();
                if let Some(i) = self.hosts.iter().position(|h| h.addr == w.to) {
                    self.reg.enter(i);
                    self.hosts[i].ep.handle_datagram(self.now, w.to, w.from, &mut w.data);
                    let now = self.now;
                    self.hosts[i].service(now);
                }
            }
            for n in 0..self.hosts.len() {
                if self.hosts[n].ep.poll_timeout().is_some_and(|t| t <= self.now) {
                    self.reg.enter(n);
                    let now = self.now;
                    self.hosts[n].ep.handle_timeout(now);
                }
            }
            self.pump_all();
        }
        panic!("the pump spins");
    }

    pub fn connect(&mut self, a: usize, b: usize) -> (SessionId, SessionId) {
        let (peer, to, now) = (self.hosts[b].node, self.hosts[b].addr, self.now);
        let na = self.hosts[a]
            .events
            .iter()
            .filter(|e| matches!(e, Event::Connected { .. }))
            .count();
        let rep = self.hosts[a].cmd(
            now,
            Command::Connect {
                node: peer,
                alpn: ALPN_A,
                addrs: &[to],
                role: Role::Other,
            },
        );
        let Value::Session(sa) = rep.value else {
            panic!("no session")
        };
        self.dial_done(a, b, na);
        let sb = self.hosts[b]
            .events
            .iter()
            .rev()
            .find_map(|e| {
                if let Event::Incoming { session, .. } = e {
                    Some(*session)
                } else {
                    None
                }
            })
            .unwrap();
        (sa, sb)
    }

    pub fn dial_done(&mut self, a: usize, b: usize, na: usize) {
        let nb = self.hosts[b]
            .events
            .iter()
            .filter(|e| matches!(e, Event::Incoming { .. }))
            .count();
        let end = self.now + 10 * SEC_NS;
        assert!(self.run(end, |n| {
            n.hosts[a]
                .events
                .iter()
                .filter(|e| matches!(e, Event::Connected { .. }))
                .count()
                > na
                && n.hosts[b]
                    .events
                    .iter()
                    .filter(|e| matches!(e, Event::Incoming { .. }))
                    .count()
                    >= nb.max(1)
        }));
    }

    /// Send the bytes of `msg` on a new stream of `session` from host `n`.
    pub fn send_msg(&mut self, n: usize, session: SessionId, msg: MsgId, len: usize) -> u64 {
        let mut data = vec![0u8; len];
        self.reg.fill(msg, 0, &mut data).unwrap();
        let now = self.now;
        self.reg.now.set(now);
        self.reg.enter(n);
        let Value::Stream(id) = self.hosts[n]
            .cmd(now, Command::OpenStream { session, bidi: false })
            .value
        else {
            panic!("no stream")
        };
        self.hosts[n].cmd(
            now,
            Command::Write {
                session,
                stream: id,
                data: &data,
            },
        );
        self.hosts[n].cmd(now, Command::Finish { session, stream: id });
        id
    }

    pub fn expect_msg(&mut self, to: usize, msg: MsgId, len: usize) {
        let mut expect = vec![0u8; len];
        self.reg.fill(msg, 0, &mut expect).unwrap();
        let end = self.now + 10 * SEC_NS;
        let got = |n: &Self| n.hosts[to].read.values().any(|v| *v == expect);
        assert!(self.run(end, |n| got(n)) || got(self), "message not delivered");
    }
}

/// The secret terms a term was derived from, transitively, including itself.
pub fn ancestry(reg: &Registry, id: TermId) -> BTreeSet<TermId> {
    let mut seen = BTreeSet::new();
    let mut todo = vec![id];
    while let Some(t) = todo.pop() {
        if !seen.insert(t) {
            continue;
        }
        match reg.term(t).unwrap() {
            Term::Hkdf { inputs, .. } => todo.extend(inputs),
            Term::Dh(a, b) => todo.extend([a, b]),
            Term::KemSs { owner, .. } => todo.push(owner),
            _ => {}
        }
    }
    seen
}

pub fn has(reg: &Registry, id: TermId, f: impl Fn(&Term) -> bool) -> bool {
    ancestry(reg, id).into_iter().any(|t| f(&reg.term(t).unwrap()))
}

impl Net {
    pub fn run_for(&mut self, span: u64) {
        let end = self.now + span;
        self.run(end, |_| false);
        self.now = end;
    }
}
