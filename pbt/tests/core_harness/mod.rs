//! A small deterministic driver of real `pinc-core` endpoints, written from the public API only: hosts that perform the
//! host duties the endpoint documents (answer key requests and access checks, read streams and datagrams until empty,
//! take every `Incoming` with `session_taken`), a scripted link between them on virtual time (delay, jitter, loss,
//! duplication, a NAT that can rebind, a partition), and a record of everything the endpoints did that the oracles
//! read: violations of the documented invariants are collected, each with a signature, and the property fails on the
//! first.
//!
//! Where the checked invariants come from (quoted in `check_stats`, `on_event` and `cmd`): the `pinc_core` crate and
//! module documentation (`lib.rs`, `api.rs`, `commands.rs`, `queue.rs`, `rx.rs`, `ledger.rs`, `timers.rs`).
#![allow(
    dead_code,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap};
use std::net::SocketAddr;

use pinc_core::{
    Answer, Command, CommandError, Endpoint, EndpointConfig, Event, LEDGER_ENTRIES, MAX_HALF_OPEN, NodeStats, Query,
    Role, SessionId, Taken, Transmit, Value, event_queue,
};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use pinc_security::{Env, Failure, KeyHandle, KeyResponse, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys};
use pinc_transport::stream::{NoSource, RecvStatus};

pub const CN: usize = 8;
pub const CC: usize = 17;
pub const CF: usize = 128;
pub const CNP: usize = 4;
/// Sessions in the table: small, so a flood can reach the limit.
pub const K: usize = 8;
pub const D: usize = 128;
pub const PK: usize = 8;
pub const TK: usize = 16;
pub const CT: usize = 8;
pub const CHUNKS: usize = 128;

pub const SEC: u64 = 1_000_000_000;
pub const MS: u64 = 1_000_000;
pub const ALPN_A: &[u8] = b"pinc/a";
pub const ALPN_B: &[u8] = b"pinc/b";

pub type Ep = Endpoint<'static, 'static, Software, NoSource, CN, CC, CF, CNP, K, D, PK, TK, CT>;

/// Runs `f` on a thread with a large stack: an endpoint is built on the stack before it is boxed.
pub fn big_stack(f: impl FnOnce() + Send + 'static) {
    let r = std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(f)
        .unwrap()
        .join();
    if let Err(e) = r {
        std::panic::resume_unwind(e);
    }
}

/// A seeded `SplitMix64`, the only randomness of a run.
#[derive(Debug, Clone)]
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// True with probability `per_mille / 1000`.
    pub fn chance(&mut self, per_mille: u16) -> bool {
        per_mille > 0 && self.next() % 1000 < u64::from(per_mille)
    }
}

/// A broken documented invariant: a signature that names the rule (so distinct rules are distinct failures) and the
/// detail.
#[derive(Debug, Clone)]
pub struct Violation {
    pub sig: &'static str,
    pub detail: String,
}

/// The identity a host of tag `tag` has.
pub fn identity_of(tag: u8) -> (Keypair, LocalIdentity) {
    let alg = IdentityAlg::Ed25519;
    let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    (kp, id)
}

/// How a host is built.
#[derive(Debug, Clone, Copy)]
pub struct HostCfg {
    /// The first flight is cut to minimum-size datagrams (several datagrams) instead of leaving whole.
    pub split: bool,
    /// `set_backlog_room(K)` and a `session_taken` for every `Incoming`, as rx.rs asks of a host that sets a room.
    pub room: bool,
    pub tickets: u8,
}

impl Default for HostCfg {
    fn default() -> Self {
        Self {
            split: false,
            room: true,
            tickets: 1,
        }
    }
}

/// An endpoint with its key material and what the host saw.
pub struct Host {
    pub ep: Box<Ep>,
    pub addr: SocketAddr,
    pub id: NodeId,
    pub tag: u8,
    pub cfg: HostCfg,
    kp: Keypair,
    prekeys: SoftPrekeys<Software>,
    drbg: Drbg,
    pub events: Vec<(u64, Event)>,
    pub read: BTreeMap<(SessionId, u64), Vec<u8>>,
    pub fin: BTreeSet<(SessionId, u64)>,
    pub reset: BTreeMap<(SessionId, u64), u64>,
    pub dgrams: Vec<(SessionId, Vec<u8>)>,
    pub opened: BTreeSet<SessionId>,
    pub closed: BTreeSet<SessionId>,
    /// Sessions this host was told of by a `Connect` reply.
    pub dialed: BTreeSet<SessionId>,
    /// Sessions `session_taken` called gone while no `Closed` had come yet.
    pub gone: BTreeSet<SessionId>,
    /// Writes not taken whole yet: (session, stream, bytes, taken so far, finish after).
    pub pending: Vec<(SessionId, u64, Vec<u8>, usize, bool)>,
    pub violations: Vec<Violation>,
    pub fed: u64,
    pub emitted: u64,
    last: Option<NodeStats>,
    /// Reads of streams, to bound a host loop that never ends.
    reads: u64,
    /// Whether the host answers the access check (false: deny).
    pub allow: bool,
    /// Whether to read stream bytes as they arrive.
    pub auto_read: bool,
}

impl Host {
    pub fn new(tag: u8, addr: SocketAddr, now: u64, cfg: HostCfg) -> Self {
        let (kp, identity) = identity_of(tag);
        let mut drbg = Drbg::new(&[tag ^ 0x5a; 32]);
        let mut ecfg = EndpointConfig::new(u64::from(tag).wrapping_mul(0x9E37_79B9));
        ecfg.conn.max_gso = 4;
        ecfg.conn.flight_split = cfg.split;
        ecfg.tickets_per_session = cfg.tickets;
        let ep_drbg = Drbg::new(&[tag ^ 0xa5; 32]);
        let mut ep: Box<Ep> = Endpoint::new_owned(now, Software, ep_drbg, identity, ecfg, CHUNKS, 4);
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
        ep.set_prekey(prekeys.acquire(&mut env).unwrap());
        assert!(ep.register_alpn(ALPN_A));
        assert!(ep.register_alpn(ALPN_B));
        assert!(ep.add_iface(addr).is_some());
        if cfg.room {
            ep.set_backlog_room(K);
        }
        Self {
            ep,
            addr,
            id: identity.node_id(),
            tag,
            cfg,
            kp,
            prekeys,
            drbg,
            events: Vec::new(),
            read: BTreeMap::new(),
            fin: BTreeSet::new(),
            reset: BTreeMap::new(),
            dgrams: Vec::new(),
            opened: BTreeSet::new(),
            closed: BTreeSet::new(),
            dialed: BTreeSet::new(),
            gone: BTreeSet::new(),
            pending: Vec::new(),
            violations: Vec::new(),
            fed: 0,
            emitted: 0,
            last: None,
            reads: 0,
            allow: true,
            auto_read: true,
        }
    }

    pub fn violate(&mut self, sig: &'static str, detail: String) {
        if self.violations.len() < 16 {
            self.violations.push(Violation {
                sig,
                detail: format!("host {}: {detail}", self.tag),
            });
        }
    }

    /// Apply a command, record its events and perform the host duties they ask for. "A command that fails changes no
    /// session and queues no event ... with three exceptions: a dial of the node's own id queues `ConnectFailed`, a
    /// sub-session whose open cannot be queued ... may queue events, and a key answer whose message did not
    /// authenticate goes on with the held handshake fragments" (commands.rs): a failed command other than a dial or
    /// such a key answer must leave the event queue as it was.
    pub fn cmd(&mut self, now: u64, c: Command<'_, NoSource>) -> Result<Reply2, CommandError> {
        let dial = matches!(c, Command::Connect { .. });
        let key_answer = matches!(c, Command::KeyResponse { .. });
        let before = self.ep.node_stats();
        let r = self.ep.command(now, c);
        match &r {
            Ok(rep) => {
                if let Value::Session(s) = rep.value
                    && dial
                {
                    self.dialed.insert(s);
                }
                let evs: Vec<Event> = rep.events.iter().copied().collect();
                for e in evs {
                    self.on_event(now, e);
                }
            }
            Err(e) => {
                let after = self.ep.node_stats();
                let replay = key_answer && matches!(e, CommandError::Failure(Failure::Authentication));
                if !dial && !replay && after.events_queued > before.events_queued {
                    self.violate(
                        "a failed command queued an event",
                        format!("{e:?}: queued {} -> {}", before.events_queued, after.events_queued),
                    );
                }
            }
        }
        r.map(|rep| Reply2 { value: rep.value })
    }

    /// One event: the per-event invariants and the host duties. api.rs: "an event names a session by [`SessionId`],
    /// which is never reused for another session"; a session's `Closed` is its last event (commands.rs: "A Closed in
    /// the reply reaches the host ahead of the session's events still queued from before the command: they would name
    /// the session after its Closed, so they go"). A session is reported open (`Connected` or `Incoming`) once.
    pub fn on_event(&mut self, now: u64, e: Event) {
        self.events.push((now, e));
        if let Some(s) = e.session()
            && self.closed.contains(&s)
        {
            self.violate("an event named a session after its Closed", format!("{e:?}"));
        }
        match e {
            Event::Connected { session, .. } | Event::Incoming { session, .. } => {
                if !self.opened.insert(session) {
                    self.violate("a session was reported open twice", format!("{e:?}"));
                }
            }
            Event::Closed { session, .. } => {
                self.closed.insert(session);
            }
            _ => {}
        }
        match e {
            Event::KeyRequest { session } => self.answer_keys(now, session),
            Event::AcpCheck { check, .. } => {
                let allow = self.allow;
                let _ = self.cmd(now, Command::AcpAnswer { check, allow });
            }
            Event::StreamReadable { session, stream } if self.auto_read => self.read_stream(now, session, stream),
            Event::StreamReset { session, stream, error } => {
                self.reset.insert((session, stream), error);
            }
            Event::DatagramReceived { session } => self.read_datagrams(session),
            Event::Incoming { session, .. } if self.cfg.room => {
                if self.ep.session_taken(session) == Taken::Gone && !self.closed.contains(&session) {
                    // rx.rs: a session that is Gone "ended before the host read its Incoming ... its Closed follows".
                    self.gone.insert(session);
                }
            }
            _ => {}
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
        let resp = match self.ep.query(Query::KeyRequest(session)) {
            Answer::KeyRequest(req) => match soft.answer(&mut env, &req, &mut sig) {
                KeyResponse::Signature(s) => KeyResponse::Signature(s),
                KeyResponse::SharedSecret(s) => KeyResponse::SharedSecret(s),
                KeyResponse::Failed => KeyResponse::Failed,
            },
            _ => return,
        };
        let _ = self.cmd(
            now,
            Command::KeyResponse {
                session,
                response: resp,
            },
        );
    }

    pub fn read_stream(&mut self, now: u64, session: SessionId, stream: u64) {
        for _ in 0..10_000 {
            self.reads += 1;
            let chunk = match self.ep.query(Query::Read { session, stream }) {
                Answer::Chunk(c) if !c.is_empty() => c.to_vec(),
                _ => break,
            };
            self.read
                .entry((session, stream))
                .or_default()
                .extend_from_slice(&chunk);
            match self.cmd(
                now,
                Command::Consume {
                    session,
                    stream,
                    n: chunk.len(),
                },
            ) {
                Ok(Reply2 {
                    value: Value::Recv(RecvStatus::Finished),
                }) => {
                    self.fin.insert((session, stream));
                }
                Ok(_) => {}
                Err(e) => {
                    self.violate(
                        "a consume of bytes just read failed",
                        format!("{session:?} {stream}: {e:?}"),
                    );
                    break;
                }
            }
        }
        if let Ok(Reply2 {
            value: Value::Recv(RecvStatus::Finished),
        }) = self.cmd(now, Command::Consume { session, stream, n: 0 })
        {
            self.fin.insert((session, stream));
        }
    }

    fn read_datagrams(&mut self, session: SessionId) {
        let mut buf = vec![0u8; 65_536];
        for _ in 0..10_000 {
            match self.ep.read_datagram(session, &mut buf) {
                Ok(Some(n)) => self.dgrams.push((session, buf[..n].to_vec())),
                Ok(None) | Err(_) => break,
            }
        }
    }

    /// Drain the event queue, performing the host duties, and offer the writes not taken whole yet again.
    pub fn service(&mut self, now: u64) {
        for _ in 0..100_000 {
            let Some(e) = self.ep.poll_event() else {
                self.flush_writes(now);
                return;
            };
            self.on_event(now, e);
        }
        self.violate("poll_event never ran dry", String::new());
    }

    /// Queue `data` on a stream (and its end when `finish`), offered again on every service until taken whole.
    pub fn write(&mut self, now: u64, session: SessionId, stream: u64, data: Vec<u8>, finish: bool) {
        self.pending.push((session, stream, data, 0, finish));
        self.flush_writes(now);
    }

    fn flush_writes(&mut self, now: u64) {
        let mut pending = std::mem::take(&mut self.pending);
        pending.retain_mut(|(session, stream, data, done, finish)| {
            let (session, stream) = (*session, *stream);
            if self.closed.contains(&session) {
                return false;
            }
            while *done < data.len() {
                match self.cmd(
                    now,
                    Command::Write {
                        session,
                        stream,
                        data: &data[*done..],
                    },
                ) {
                    Ok(Reply2 {
                        value: Value::Written(0),
                    }) => return true,
                    Ok(Reply2 {
                        value: Value::Written(n),
                    }) => {
                        if n > data.len() - *done {
                            self.violate("a write took more bytes than it was given", format!("{n}"));
                            return false;
                        }
                        *done += n;
                    }
                    Ok(_) => return true,
                    Err(_) => return true,
                }
            }
            if *finish {
                return self.cmd(now, Command::Finish { session, stream }).is_err();
            }
            false
        });
        pending.append(&mut self.pending);
        self.pending = pending;
    }

    /// The node-wide invariants, checked after every step.
    ///
    /// - "Every table has a fixed bound" (lib.rs): at most `K` sessions, at most [`MAX_HALF_OPEN`] of them half open
    ///   (rx.rs), "the queue never holds more than" `event_queue(K)` events (queue.rs), "Handshake datagrams held now
    ///   (at most 4)" (`NodeStats::fragments_waiting`), "the ledger holds at most [`LEDGER_ENTRIES`] addresses".
    /// - `events_lost`: "the endpoint keeps this at 0 by holding work back while the queue is near full".
    /// - With a room set: "while the owed sessions fill the room ... no first flight starts one" (rx.rs), so `owed`
    ///   never exceeds the room.
    /// - The counters only grow; `datagrams_in` counts every datagram handed to `handle_datagram` (rx.rs adds one per
    ///   call); `sessions` agrees with `Query::SessionAt` and `Endpoint::sessions`.
    pub fn check_stats(&mut self) {
        let s = self.ep.node_stats();
        let mut bad: Vec<(&'static str, String)> = Vec::new();
        if s.sessions > K {
            bad.push(("more sessions than the table holds", format!("{}", s.sessions)));
        }
        if s.half_open > s.sessions || s.half_open > MAX_HALF_OPEN {
            bad.push((
                "more half-open sessions than sessions",
                format!("{} of {}", s.half_open, s.sessions),
            ));
        }
        if s.events_queued > event_queue(K) {
            bad.push(("the event queue outgrew its bound", format!("{}", s.events_queued)));
        }
        if s.events_lost != 0 {
            bad.push(("an unrecoverable event was lost", format!("{}", s.events_lost)));
        }
        if s.fragments_waiting > 4 {
            bad.push((
                "more than four held handshake datagrams",
                format!("{}", s.fragments_waiting),
            ));
        }
        if s.ledger > LEDGER_ENTRIES {
            bad.push(("the ledger outgrew its bound", format!("{}", s.ledger)));
        }
        if self.cfg.room && s.owed > K {
            bad.push(("more sessions owed than the room", format!("{}", s.owed)));
        }
        if s.datagrams_in != self.fed {
            bad.push((
                "datagrams_in is not the datagrams handed in",
                format!("{} vs {}", s.datagrams_in, self.fed),
            ));
        }
        let listed = self.ep.sessions().count();
        if listed != s.sessions {
            bad.push((
                "sessions() and node_stats disagree",
                format!("{listed} vs {}", s.sessions),
            ));
        }
        let at_last = s.sessions.checked_sub(1).map(|i| self.ep.query(Query::SessionAt(i)));
        if at_last.is_some_and(|a| !matches!(a, Answer::Stats(_))) {
            bad.push(("SessionAt misses a live session", format!("{}", s.sessions)));
        }
        if !matches!(self.ep.query(Query::SessionAt(s.sessions)), Answer::None) {
            bad.push(("SessionAt answers past the live sessions", format!("{}", s.sessions)));
        }
        if let Some(l) = self.last {
            let pairs = [
                ("datagrams_in", l.datagrams_in, s.datagrams_in),
                ("datagrams_out", l.datagrams_out, s.datagrams_out),
                ("dropped_in", l.dropped_in, s.dropped_in),
                ("dropped_out", l.dropped_out, s.dropped_out),
                ("events_dropped", l.events_dropped, s.events_dropped),
                ("stalled_in", l.stalled_in, s.stalled_in),
                ("backlog_refused", l.backlog_refused, s.backlog_refused),
                ("stateless_rejects", l.stateless_rejects, s.stateless_rejects),
                ("fragments_held", l.fragments_held, s.fragments_held),
                ("held_by_ledger", l.held_by_ledger, s.held_by_ledger),
            ];
            for (name, a, b) in pairs {
                if b < a {
                    bad.push(("a node counter went down", format!("{name}: {a} -> {b}")));
                }
            }
        }
        self.last = Some(s);
        for (sig, d) in bad {
            self.violate(sig, d);
        }
    }

    pub fn session_of(&self, e: impl Fn(&Event) -> Option<SessionId>) -> Option<SessionId> {
        self.events.iter().rev().find_map(|(_, ev)| e(ev))
    }

    pub fn count(&self, f: impl Fn(&Event) -> bool) -> usize {
        self.events.iter().filter(|(_, e)| f(e)).count()
    }

    pub fn stats(&self, s: SessionId) -> Option<pinc_core::SessionStats> {
        match self.ep.query(Query::Stats(s)) {
            Answer::Stats(st) => Some(st),
            _ => None,
        }
    }
}

/// The value of a command's reply (the events were handled).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reply2 {
    pub value: Value,
}

/// The link's faults, per datagram.
#[derive(Debug, Clone, Copy, Default)]
pub struct Faults {
    pub loss: u16,
    pub dup: u16,
    /// Extra delay up to this much, so datagrams overtake each other.
    pub jitter: u64,
    /// Everything is dropped.
    pub cut: bool,
}

type Wire = Reverse<(u64, u64, SocketAddr, SocketAddr, Vec<u8>)>;

/// Hosts joined by one scripted link.
pub struct Net {
    pub hosts: Vec<Host>,
    wires: BinaryHeap<Wire>,
    pub now: u64,
    seq: u64,
    pub delay: u64,
    pub faults: Faults,
    pub rng: Rng,
    /// A NAT in front of hosts: inside address to outside address.
    pub nat: BTreeMap<SocketAddr, SocketAddr>,
    /// Every datagram the hosts sent, oldest first, kept up to `capture_max`.
    pub captured: Vec<(SocketAddr, SocketAddr, Vec<u8>)>,
    pub capture_max: usize,
    /// Bytes (with 28 bytes of headers per datagram) host `i` sent to an address.
    pub sent_to: BTreeMap<(usize, SocketAddr), u64>,
    /// Bytes host `i` received from an address.
    pub got_from: BTreeMap<(usize, SocketAddr), u64>,
    /// Every datagram a host sent: (time, host, destination, length), kept up to `capture_max * 20`.
    pub tapped: Vec<(u64, usize, SocketAddr, usize)>,
    pub violations: Vec<Violation>,
    pub steps: u64,
}

impl Net {
    pub fn new(seed: u64) -> Self {
        Self {
            hosts: Vec::new(),
            wires: BinaryHeap::new(),
            now: 10 * SEC,
            seq: 0,
            delay: 5 * MS,
            faults: Faults::default(),
            rng: Rng::new(seed),
            nat: BTreeMap::new(),
            captured: Vec::new(),
            capture_max: 600,
            sent_to: BTreeMap::new(),
            got_from: BTreeMap::new(),
            tapped: Vec::new(),
            violations: Vec::new(),
            steps: 0,
        }
    }

    pub fn add(&mut self, tag: u8, cfg: HostCfg) -> usize {
        let addr: SocketAddr = ([10, 0, 0, tag], 4433).into();
        let now = self.now;
        self.hosts.push(Host::new(tag, addr, now, cfg));
        self.hosts.len() - 1
    }

    pub fn violate(&mut self, sig: &'static str, detail: String) {
        if self.violations.len() < 16 {
            self.violations.push(Violation { sig, detail });
        }
    }

    /// The first violation of the net or of a host.
    pub fn first_violation(&self) -> Option<Violation> {
        self.violations
            .first()
            .cloned()
            .or_else(|| self.hosts.iter().find_map(|h| h.violations.first().cloned()))
    }

    fn host_at(&self, a: SocketAddr) -> Option<usize> {
        let inside = self.nat.iter().find(|(_, o)| **o == a).map(|(i, _)| *i);
        match inside {
            Some(i) => self.hosts.iter().position(|h| h.addr == i),
            // A host behind a NAT is not reachable at its inside address.
            None if self.nat.contains_key(&a) => None,
            None => self.hosts.iter().position(|h| h.addr == a),
        }
    }

    /// Hand a datagram to the host at `to` now, as if `from` had sent it (the injection of an attacker).
    pub fn deliver(&mut self, from: SocketAddr, to: SocketAddr, mut data: Vec<u8>) {
        let Some(i) = self.host_at(to) else { return };
        let local = self.hosts[i].addr;
        *self.got_from.entry((i, from)).or_default() += data.len() as u64;
        let now = self.now;
        let h = &mut self.hosts[i];
        h.fed += 1;
        h.ep.handle_datagram(now, local, from, &mut data);
        h.service(now);
    }

    /// Put a datagram on the wire to arrive after `delay`.
    pub fn inject(&mut self, from: SocketAddr, to: SocketAddr, data: Vec<u8>, delay: u64) {
        self.seq += 1;
        self.wires.push(Reverse((self.now + delay, self.seq, from, to, data)));
    }

    /// Let host `n` send everything it has ("After any input call `poll_transmit` until it returns `None`").
    pub fn pump(&mut self, n: usize) {
        let mut buf = vec![0u8; 65_536];
        for _ in 0..20_000 {
            let now = self.now;
            self.hosts[n].service(now);
            let Some(Transmit {
                local,
                remote,
                len,
                segment_size,
            }) = self.hosts[n].ep.poll_transmit(now, &mut buf)
            else {
                self.hosts[n].service(now);
                return;
            };
            if len == 0 || segment_size == 0 || len > buf.len() {
                self.violate(
                    "a transmit of no bytes or past the buffer",
                    format!("{len} {segment_size}"),
                );
                return;
            }
            if local != self.hosts[n].addr {
                self.violate(
                    "a transmit from an address the host has no interface on",
                    format!("{local}"),
                );
            }
            for chunk in buf[..len].chunks(segment_size) {
                self.hosts[n].emitted += 1;
                *self.sent_to.entry((n, remote)).or_default() += chunk.len() as u64 + 28;
                if self.tapped.len() < self.capture_max * 20 {
                    self.tapped.push((now, n, remote, chunk.len()));
                }
                if self.captured.len() < self.capture_max {
                    self.captured.push((local, remote, chunk.to_vec()));
                }
                if self.faults.cut || self.rng.chance(self.faults.loss) {
                    continue;
                }
                let from = self.nat.get(&local).copied().unwrap_or(local);
                let copies = if self.rng.chance(self.faults.dup) { 2 } else { 1 };
                for _ in 0..copies {
                    let extra = if self.faults.jitter > 0 {
                        self.rng.next() % self.faults.jitter
                    } else {
                        0
                    };
                    self.seq += 1;
                    self.wires.push(Reverse((
                        now + self.delay + extra,
                        self.seq,
                        from,
                        remote,
                        chunk.to_vec(),
                    )));
                }
            }
        }
        self.violate("poll_transmit never returned None", format!("host {n}"));
    }

    pub fn pump_all(&mut self) {
        for _ in 0..4 {
            for n in 0..self.hosts.len() {
                self.pump(n);
            }
        }
    }

    pub fn check(&mut self) {
        for h in &mut self.hosts {
            h.check_stats();
        }
    }

    fn next_time(&self) -> Option<u64> {
        let w = self.wires.peek().map(|Reverse(w)| w.0);
        let t = self.hosts.iter().filter_map(|h| h.ep.poll_timeout()).min();
        match (w, t) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        }
    }

    /// Run until `deadline` or until `stop` holds; returns whether `stop` held. "There are no hidden wakeups": the
    /// next instant is the earliest datagram or `poll_timeout`. A timer that stays due at one instant without the
    /// clock moving is a spin, and so is a run that never reaches its deadline in a bounded number of steps.
    pub fn run(&mut self, deadline: u64, mut stop: impl FnMut(&mut Self) -> bool) -> bool {
        self.pump_all();
        let mut same = 0u32;
        let mut last = self.now;
        for _ in 0..400_000u32 {
            self.steps += 1;
            if stop(self) {
                return true;
            }
            let Some(t) = self.next_time() else {
                self.now = self.now.max(deadline);
                return stop(self);
            };
            let t = t.max(self.now);
            if t > deadline {
                self.now = deadline;
                return stop(self);
            }
            self.now = t;
            if t == last {
                same += 1;
                if same > 5_000 {
                    let due: Vec<Option<u64>> = self.hosts.iter().map(|h| h.ep.poll_timeout()).collect();
                    self.violate("a timer stays due without the clock moving", format!("at {t}: {due:?}"));
                    return false;
                }
            } else {
                same = 0;
                last = t;
            }
            while self.wires.peek().is_some_and(|Reverse(w)| w.0 <= self.now) {
                let Some(Reverse((_, _, from, to, data))) = self.wires.pop() else {
                    break;
                };
                self.deliver(from, to, data);
            }
            for n in 0..self.hosts.len() {
                if self.hosts[n].ep.poll_timeout().is_some_and(|d| d <= self.now) {
                    let now = self.now;
                    self.hosts[n].ep.handle_timeout(now);
                    self.hosts[n].service(now);
                }
            }
            self.pump_all();
            self.check();
            if self.first_violation().is_some() {
                return false;
            }
        }
        self.violate("the run never reached its deadline", format!("at {}", self.now));
        false
    }

    pub fn run_for(&mut self, span: u64) {
        let end = self.now + span;
        self.run(end, |_| false);
        self.now = self.now.max(end);
    }

    /// Dial from `a` to `b` and run until `a` reports `Connected` and `b` `Incoming`; the two sessions.
    pub fn connect_pair(&mut self, a: usize, b: usize, alpn: &[u8]) -> Option<(SessionId, SessionId)> {
        let (peer, to, now) = (self.hosts[b].id, self.hosts[b].addr, self.now);
        let nb = self.hosts[b].count(|e| matches!(e, Event::Incoming { .. }));
        let rep = self.hosts[a]
            .cmd(
                now,
                Command::Connect {
                    node: peer,
                    alpn,
                    addrs: &[to],
                    role: Role::Other,
                },
            )
            .ok()?;
        let Value::Session(sa) = rep.value else { return None };
        let ok = self.run(now + 20 * SEC, |n| {
            n.hosts[a].opened.contains(&sa) && n.hosts[b].count(|e| matches!(e, Event::Incoming { .. })) > nb
        });
        if !ok {
            return None;
        }
        let sb = self.hosts[b].session_of(|e| match e {
            Event::Incoming { session, .. } => Some(*session),
            _ => None,
        })?;
        Some((sa, sb))
    }
}

/// One edit of a captured datagram: (where, as a fraction of the length in 1/65536; how; a byte).
#[derive(Debug, Clone, Copy, PartialEq, Eq, ephyra::Arbitrary)]
pub struct Edit(pub u16, pub u8, pub u8);

pub fn apply_edit(d: &mut Vec<u8>, e: Edit) {
    if d.is_empty() {
        d.push(e.2);
        return;
    }
    let at = (usize::from(e.0) * d.len()) >> 16;
    match e.1 % 7 {
        0 => d[at] ^= 1 << (e.2 % 8),
        1 => d[at] = e.2,
        2 => d.truncate(at.max(1)),
        3 => {
            let end = (at + usize::from(e.2 % 16) + 1).min(d.len());
            let run = d[at..end].to_vec();
            d.splice(at..at, run);
        }
        4 => d.insert(at, e.2),
        5 => d[at] = [0x00, 0x01, 0x3f, 0x40, 0x7f, 0x80, 0xbf, 0xc0, 0xff][usize::from(e.2) % 9],
        _ => d.extend(std::iter::repeat_n(e.2, usize::from(e.2 % 32) + 1)),
    }
}

/// The datagrams of first flights from dialers that never hear an answer, to host 0 and to host 1.
pub fn ghost_flights(now: u64, targets: &[(SocketAddr, pinc_crypto::NodeId)], split: bool) -> Vec<(usize, Vec<u8>)> {
    let mut out = Vec::new();
    for (k, tag) in [40u8, 41].into_iter().enumerate() {
        let cfg = HostCfg {
            split: split ^ (k == 1),
            ..HostCfg::default()
        };
        let mut g = Host::new(tag, ([10, 0, 9, tag], 4433).into(), now, cfg);
        let mut buf = vec![0u8; 65_536];
        for (t, (addr, node)) in targets.iter().enumerate() {
            let _ = g.cmd(
                now,
                Command::Connect {
                    node: *node,
                    alpn: ALPN_A,
                    addrs: &[*addr],
                    role: Role::Other,
                },
            );
            // The first flight and the resends of the next seconds.
            for step in 0..4u64 {
                let at = now + step * 700 * MS;
                g.ep.handle_timeout(at);
                g.service(at);
                for _ in 0..64 {
                    let Some(tx) = g.ep.poll_transmit(at, &mut buf) else {
                        break;
                    };
                    for c in buf[..tx.len].chunks(tx.segment_size.max(1)) {
                        out.push((t, c.to_vec()));
                    }
                }
            }
        }
    }
    out
}
