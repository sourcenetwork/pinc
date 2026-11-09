//! A simulated client node: a `vinc-core` endpoint plus the connectivity layer, driven by the simulator through the
//! host loop the layer documents, with the real protected carrier running over simulated TCP and WebSocket streams.
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
    clippy::large_stack_arrays
)]

use std::collections::VecDeque;
use std::net::SocketAddr;

use vinc_connect::carrier::ws::{self, Decoder, Opcode, Role as WsRole, WsFrame};
use vinc_connect::client::{Config, Connectivity, Io, Kind, RelayCfg};
use vinc_core::{Command, Role, SessionId, Value};
use vinc_crypto::NodeId;
use vinc_security::Env;
use vinc_sim::{IfaceEvent, StreamEvent, StreamId, StreamKind, StreamOp, Time};

use crate::Caps;
use crate::connect_host::{Answer, Ev, Host, Outbox, answer_parts};

pub const NR: usize = 2;
pub const PEERS: usize = 8;
pub type CConn = Connectivity<Caps, NR, PEERS>;

/// Where a relay is reachable.
#[derive(Debug, Clone, Copy)]
pub struct RelaySpec {
    pub id: NodeId,
    pub udp: Option<SocketAddr>,
    pub tcp: Option<SocketAddr>,
    pub ws: Option<SocketAddr>,
}

/// How a client is built.
#[derive(Debug, Clone)]
pub struct ClientSpec {
    pub tag: u8,
    pub addr: SocketAddr,
    pub relays: Vec<RelaySpec>,
    pub phone: bool,
    pub keep_learn: bool,
    pub restarted: bool,
    pub start: u64,
}

/// A command from the scenario.
#[derive(Debug, Clone)]
pub enum Cmd {
    Dial {
        node: NodeId,
        hints: Vec<SocketAddr>,
        role: Role,
    },
    /// Open a stream on the session and write the bytes.
    Send {
        session: SessionId,
        data: Vec<u8>,
    },
    Suspend,
    Resume {
        moved: bool,
    },
    /// A beacon the scenario carried over the local link.
    Beacon(Vec<u8>),
    Lookup(NodeId),
    LinkChanged,
    /// Send a packet to `peer` through relay `relay`'s carrier, as the endpoint does.
    Raw {
        relay: usize,
        peer: NodeId,
        data: Vec<u8>,
    },
    /// Run the host loop (a new node starts with it).
    Tick,
}

pub struct Client {
    pub host: Host,
    pub conn: Box<CConn>,
    pub addr: SocketAddr,
    streams: [Option<StreamId>; NR],
    opening: [Option<SocketAddr>; NR],
    kinds: [Kind; NR],
    ws: [Option<Decoder>; NR],
    pub out: Outbox,
    pub events: VecDeque<Ev>,
    now: Time,
    /// Beacons the node sent, for the scenario to carry over the local link.
    pub beacons: Vec<Vec<u8>>,
    /// The sessions `dial` returned, in order.
    pub dialed: Vec<SessionId>,
    /// Carrier streams opened, with the time, the relay and the kind.
    pub opened: Vec<(Time, usize, Kind)>,
    pub datagrams_sent: u64,
    pub datagrams_routed: u64,
    /// Every datagram the endpoint transmitted: time, destination and length (relay paths included).
    pub tx_log: Vec<(Time, SocketAddr, usize)>,
}

impl Client {
    pub fn new(spec: &ClientSpec) -> Self {
        let host = Host::new(spec.tag, spec.addr, spec.start);
        let mut relays: [Option<RelayCfg>; NR] = [None; NR];
        for (d, r) in relays.iter_mut().zip(&spec.relays) {
            *d = Some(RelayCfg {
                id: r.id,
                udp: r.udp,
                tcp: r.tcp,
                ws: r.ws,
            });
        }
        let cfg = Config {
            me: host.me,
            identity: host.identity,
            relays,
            phone: spec.phone,
            restarted: spec.restarted,
            start: spec.start,
            v6: false,
            keep_learn: spec.keep_learn,
        };
        let mut conn = Box::new(CConn::new(
            cfg,
            host.prekey_info.clone(),
            host.prov,
            u64::from(spec.tag) << 32,
        ));
        conn.set_local(&[spec.addr]);
        Self {
            host,
            conn,
            addr: spec.addr,
            streams: [None; NR],
            opening: [None; NR],
            kinds: [Kind::Tcp; NR],
            ws: [None; NR],
            out: Outbox::default(),
            events: VecDeque::new(),
            now: spec.start,
            beacons: Vec::new(),
            dialed: Vec::new(),
            opened: Vec::new(),
            datagrams_sent: 0,
            datagrams_routed: 0,
            tx_log: Vec::new(),
        }
    }

    fn relay_of_stream(&self, s: StreamId) -> Option<usize> {
        self.streams.iter().position(|x| *x == Some(s))
    }

    /// One turn of the host loop, repeated until nothing moves.
    pub fn pump(&mut self, now: Time) {
        self.now = now;
        for _ in 0..64 {
            let mut busy = self.events_step(now);
            {
                let prov = self.host.prov;
                let mut env = Env {
                    provider: &prov,
                    now,
                    drbg: &mut self.host.drbg,
                };
                self.conn
                    .drive(now, &mut *self.host.ep, &mut env, Some(now / 1_000_000));
            }
            busy |= self.keys_step(now);
            busy |= self.io_step(now);
            busy |= self.tx_step(now);
            busy |= self.udp_step();
            busy |= self.inbound_step(now);
            busy |= self.streams_out_step();
            if !busy {
                return;
            }
        }
        panic!("the host loop of a client does not settle at {now}");
    }

    fn events_step(&mut self, now: u64) -> bool {
        let mut did = false;
        loop {
            let ev = match self.conn.poll_event() {
                Some(e) => e,
                None => match self.host.next_event() {
                    Some(e) => e,
                    None => break,
                },
            };
            did = true;
            self.conn.observe(now, &mut *self.host.ep, &ev);
            self.host.duty(now, &ev);
            self.events.push_back(Ev::Ep(ev));
        }
        while let Some(n) = self.conn.poll_notice() {
            self.events.push_back(Ev::Notice(n));
            did = true;
        }
        did
    }

    fn keys_step(&mut self, now: u64) -> bool {
        let mut did = false;
        for i in 0..NR {
            for _ in 0..8 {
                let owned = {
                    let Host {
                        prov,
                        kp,
                        prekeys,
                        drbg,
                        ..
                    } = &mut self.host;
                    self.conn
                        .key_request(i)
                        .map(|r| answer_parts(prov, kp, prekeys, drbg, now, &r))
                };
                let Some(owned) = owned else { break };
                did = true;
                let prov = self.host.prov;
                let mut env = Env {
                    provider: &prov,
                    now,
                    drbg: &mut self.host.drbg,
                };
                self.conn.key_response(now, &mut env, i, owned.response());
            }
        }
        for _ in 0..8 {
            let owned: Option<Answer> = {
                let Host {
                    prov,
                    kp,
                    prekeys,
                    drbg,
                    ..
                } = &mut self.host;
                self.conn
                    .sign_request()
                    .map(|r| answer_parts(prov, kp, prekeys, drbg, now, &r))
            };
            let Some(owned) = owned else { break };
            did = true;
            self.conn.sign_response(now, owned.response());
        }
        did
    }

    fn io_step(&mut self, now: u64) -> bool {
        let mut did = false;
        while let Some(io) = self.conn.poll_io() {
            did = true;
            match io {
                Io::Open { relay, kind, to } => {
                    self.kinds[relay] = kind;
                    self.opening[relay] = Some(to);
                    self.opened.push((now, relay, kind));
                    self.out.ops.push_back((
                        StreamOp::Connect {
                            local: self.addr,
                            remote: to,
                            kind: match kind {
                                Kind::Tcp => StreamKind::Tcp,
                                Kind::Ws => StreamKind::Ws,
                            },
                            simultaneous: false,
                        },
                        Vec::new(),
                    ));
                }
                Io::Close { relay } => {
                    if let Some(s) = self.streams[relay].take() {
                        self.out.ops.push_back((StreamOp::Close { stream: s }, Vec::new()));
                    }
                    self.opening[relay] = None;
                    self.ws[relay] = None;
                }
            }
        }
        did
    }

    fn tx_step(&mut self, now: u64) -> bool {
        let mut did = false;
        let mut buf = vec![0u8; 2048];
        loop {
            let Some(t) = self.host.ep.poll_transmit(now, &mut buf) else {
                break;
            };
            did = true;
            self.tx_log.push((now, t.remote, t.len));
            if self.conn.route(now, &*self.host.ep, t.remote, &buf[..t.len]) {
                self.datagrams_routed += 1;
                continue;
            }
            self.datagrams_sent += 1;
            self.out.datagrams.push_back((t.local, t.remote, buf[..t.len].to_vec()));
        }
        did
    }

    fn udp_step(&mut self) -> bool {
        let mut did = false;
        let mut buf = vec![0u8; 2048];
        while let Some((to, n)) = self.conn.poll_udp(&mut buf) {
            did = true;
            if to.port() == vinc_connect::local::PORT {
                self.beacons.push(buf[..n].to_vec());
                continue;
            }
            self.datagrams_sent += 1;
            self.out.datagrams.push_back((self.addr, to, buf[..n].to_vec()));
        }
        did
    }

    fn inbound_step(&mut self, now: u64) -> bool {
        let mut got = Vec::new();
        self.conn.deliver_inbound(|from, data| got.push((from, data.to_vec())));
        let did = !got.is_empty();
        for (from, mut data) in got {
            self.host.ep.handle_datagram(now, self.addr, from, &mut data);
        }
        did
    }

    fn streams_out_step(&mut self) -> bool {
        let mut did = false;
        let mut buf = vec![0u8; 20_000];
        for i in 0..NR {
            let Some(stream) = self.streams[i] else { continue };
            loop {
                let n = self.conn.poll_stream(i, &mut buf);
                if n == 0 {
                    break;
                }
                did = true;
                let data = if self.kinds[i] == Kind::Ws {
                    let mut f = vec![0u8; n + 16];
                    let mask = [0x11, 0x22, 0x33, 0x44];
                    let m = ws::encode(Opcode::Binary, &buf[..n], Some(mask), &mut f).unwrap();
                    f.truncate(m);
                    f
                } else {
                    buf[..n].to_vec()
                };
                self.out.ops.push_back((
                    StreamOp::Write {
                        stream,
                        len: data.len(),
                        send_at: None,
                    },
                    data,
                ));
            }
        }
        did
    }

    fn feed(&mut self, now: u64, relay: usize, mut bytes: &[u8]) {
        for _ in 0..64 {
            let n = {
                let prov = self.host.prov;
                let mut env = Env {
                    provider: &prov,
                    now,
                    drbg: &mut self.host.drbg,
                };
                self.conn.stream_data(now, &mut env, relay, bytes)
            };
            bytes = &bytes[n..];
            self.keys_step(now);
            if bytes.is_empty() || (n == 0 && self.conn.key_request(relay).is_none()) {
                return;
            }
        }
    }

    pub fn cmd(&mut self, now: Time, cmd: Cmd) {
        self.now = now;
        match cmd {
            Cmd::Dial { node, hints, role } => {
                if let Ok(id) = self.conn.dial(
                    now,
                    &mut *self.host.ep,
                    node,
                    crate::connect_host::HUB_ALPN,
                    role,
                    &hints,
                ) {
                    self.dialed.push(id);
                }
            }
            Cmd::Send { session, data } => {
                let ep = &mut self.host;
                if let Ok(r) = ep.command(now, Command::OpenStream { session, bidi: true })
                    && let Value::Stream(stream) = r.value
                {
                    let _ = ep.command(
                        now,
                        Command::Write {
                            session,
                            stream,
                            data: &data,
                        },
                    );
                    let _ = ep.command(now, Command::Finish { session, stream });
                }
            }
            Cmd::Suspend => self.conn.suspend_all(now, &mut *self.host.ep, now / 1_000_000),
            Cmd::Resume { moved } => self.conn.resume_all(now, &mut *self.host.ep, moved),
            Cmd::Beacon(b) => {
                let _ = self.conn.handle_beacon(now, &b);
            }
            Cmd::Lookup(p) => self.conn.lookup(now, &p),
            Cmd::LinkChanged => self.conn.link_changed(now),
            Cmd::Raw { relay, peer, data } => {
                let a = self.conn.path_addr(relay, &peer);
                self.conn.route(now, &*self.host.ep, a, &data);
            }
            Cmd::Tick => {}
        }
        self.pump(now);
    }

    // ---- the simulator's node contract ----

    pub fn handle_datagram(&mut self, now: Time, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        if !self.conn.handle_udp(now, remote, data) {
            self.host.ep.handle_datagram(now, local, remote, data);
        }
        self.pump(now);
    }

    pub fn poll_transmit(&mut self, buf: &mut [u8]) -> Option<vinc_sim::Transmit> {
        let (local, remote, d) = self.out.datagrams.pop_front()?;
        buf[..d.len()].copy_from_slice(&d);
        Some(vinc_sim::Transmit {
            local,
            remote,
            len: d.len(),
            send_at: None,
        })
    }

    pub fn poll_timeout(&self) -> Option<Time> {
        [self.host.ep.poll_timeout(), self.conn.next_deadline(self.now)]
            .into_iter()
            .flatten()
            .min()
    }

    pub fn handle_timeout(&mut self, now: Time) {
        self.host.ep.handle_timeout(now);
        self.pump(now);
    }

    pub fn poll_stream(&mut self, buf: &mut [u8]) -> Option<StreamOp> {
        let (op, data) = self.out.ops.pop_front()?;
        buf[..data.len()].copy_from_slice(&data);
        Some(op)
    }

    pub fn handle_stream_event(&mut self, now: Time, event: StreamEvent) {
        self.events.push_back(Ev::Stream(event));
        match event {
            StreamEvent::Pending { stream, remote } => {
                if let Some(i) = self.opening.iter().position(|o| *o == Some(remote)) {
                    self.streams[i] = Some(stream);
                    self.opening[i] = None;
                }
            }
            StreamEvent::Opened { stream, .. } => {
                if let Some(i) = self.relay_of_stream(stream) {
                    self.ws[i] = (self.kinds[i] == Kind::Ws).then(|| Decoder::new(WsRole::Server));
                    let prov = self.host.prov;
                    let mut env = Env {
                        provider: &prov,
                        now,
                        drbg: &mut self.host.drbg,
                    };
                    self.conn.stream_opened(now, &mut env, i);
                }
            }
            StreamEvent::Failed { stream } | StreamEvent::Closed { stream } => {
                if let Some(i) = self.relay_of_stream(stream) {
                    self.streams[i] = None;
                    self.ws[i] = None;
                    self.conn.stream_closed(now, i);
                }
            }
        }
        self.pump(now);
    }

    pub fn handle_stream_record(&mut self, now: Time, stream: StreamId, data: &mut [u8]) {
        let Some(i) = self.relay_of_stream(stream) else { return };
        if let Some(dec) = self.ws[i].as_mut() {
            let mut rest: &mut [u8] = data;
            let mut payloads: Vec<Vec<u8>> = Vec::new();
            while let Ok(Some((frame, used))) = dec.decode(rest) {
                if let WsFrame::Data(p) = frame {
                    payloads.push(p.to_vec());
                }
                let (_, tail) = std::mem::take(&mut rest).split_at_mut(used);
                rest = tail;
            }
            for p in payloads {
                self.feed(now, i, &p);
            }
        } else {
            let d = data.to_vec();
            self.feed(now, i, &d);
        }
        self.pump(now);
    }

    pub fn resume(&mut self, now: Time) {
        self.conn.resume_all(now, &mut *self.host.ep, false);
        self.pump(now);
    }

    pub fn iface_event(&mut self, now: Time, event: IfaceEvent) {
        if let IfaceEvent::Changed { new, .. } = event {
            self.addr = SocketAddr::new(new, self.addr.port());
        }
        self.conn.link_changed(now);
        self.pump(now);
    }

    pub fn session_stats(&self, s: SessionId) -> Option<vinc_core::SessionStats> {
        match self.host.ep.query(vinc_core::Query::Stats(s)) {
            vinc_core::Answer::Stats(st) => Some(st),
            _ => None,
        }
    }
}
