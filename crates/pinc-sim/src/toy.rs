//! A toy node for testing the engine: an echo over a trivial reliable protocol.
//!
//! A client sends `total` numbered messages with a sliding window and retransmits each after a fixed timeout; a server
//! echoes every message back. The client finishes when every message has been echoed. The client persists which
//! messages are done, so a crash and restart resumes where it left off.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::net::{IpAddr, SocketAddr};

use crate::Time;
use crate::node::{IfaceEvent, Node, Transmit, Work};

const DATA: u8 = 1;
const ECHO: u8 = 2;
const HEADER: usize = 5;

/// How a [`Toy`] node behaves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ToyConfig {
    /// The node's own address.
    pub local: SocketAddr,
    /// The server to talk to; `None` makes this node a server.
    pub peer: Option<SocketAddr>,
    /// Messages the client sends in all.
    pub total: u32,
    /// Messages in flight at once.
    pub window: u32,
    /// Bytes per message (at least 5).
    pub msg_len: usize,
    /// Retransmission timeout in nanoseconds.
    pub rto: Time,
}

/// A command to a [`Toy`] node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ToyCmd {
    /// The client begins sending.
    Start,
}

/// An event of a [`Toy`] node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ToyEvent {
    /// The client received the echo of message `seq` for the first time.
    Echoed(u32),
    /// Every message was echoed.
    Complete,
    /// The server saw message `seq` for the first time.
    Served(u32),
    /// The client retransmitted message `seq`.
    Retransmit(u32),
}

/// The toy echo node.
pub struct Toy {
    cfg: ToyConfig,
    started: bool,
    done: Vec<bool>,
    done_count: u32,
    next: u32,
    inflight: BTreeMap<u32, Time>,
    seen: BTreeSet<u32>,
    out: VecDeque<(SocketAddr, SocketAddr, Vec<u8>)>,
    events: VecDeque<ToyEvent>,
    /// The node's current local address (it follows interface address changes).
    pub local: SocketAddr,
    /// How many bytes of persisted state the last restart received.
    pub restored_len: usize,
    /// How many times the node was suspended.
    pub suspends: u32,
    /// How many times the node was resumed.
    pub resumes: u32,
}

impl Toy {
    /// A node with the given behaviour.
    pub fn new(cfg: ToyConfig) -> Self {
        Self {
            started: false,
            done: vec![false; cfg.total as usize],
            done_count: 0,
            next: 0,
            inflight: BTreeMap::new(),
            seen: BTreeSet::new(),
            out: VecDeque::new(),
            events: VecDeque::new(),
            local: cfg.local,
            restored_len: 0,
            suspends: 0,
            resumes: 0,
            cfg,
        }
    }

    /// Whether every message has been echoed.
    pub const fn is_complete(&self) -> bool {
        self.cfg.total > 0 && self.done_count == self.cfg.total
    }

    /// How many messages have been echoed.
    pub const fn done_count(&self) -> u32 {
        self.done_count
    }

    fn message(&self, kind: u8, seq: u32) -> Vec<u8> {
        let mut m = vec![0; self.cfg.msg_len.max(HEADER)];
        m[0] = kind;
        m[1..HEADER].copy_from_slice(&seq.to_le_bytes());
        m
    }

    fn send_data(&mut self, seq: u32, now: Time) {
        let Some(peer) = self.cfg.peer else { return };
        let m = self.message(DATA, seq);
        self.out.push_back((self.local, peer, m));
        self.inflight.insert(seq, now);
    }

    fn pump(&mut self, now: Time) {
        if !self.started {
            return;
        }
        while self.inflight.len() < self.cfg.window as usize && self.next < self.cfg.total {
            while self.done.get(self.next as usize) == Some(&true) {
                self.next += 1;
            }
            if self.next >= self.cfg.total {
                break;
            }
            let seq = self.next;
            self.next += 1;
            self.send_data(seq, now);
        }
    }
}

impl Node for Toy {
    type Cmd = ToyCmd;
    type Event = ToyEvent;

    fn handle_datagram(&mut self, now: Time, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        let (Some(&kind), Some(seq)) = (
            data.first(),
            data.get(1..HEADER).and_then(|b| <[u8; 4]>::try_from(b).ok()),
        ) else {
            return;
        };
        let seq = u32::from_le_bytes(seq);
        match kind {
            DATA if self.cfg.peer.is_none() => {
                if self.seen.insert(seq) {
                    self.events.push_back(ToyEvent::Served(seq));
                }
                data[0] = ECHO;
                self.out.push_back((local, remote, data.to_vec()));
            }
            ECHO if self.cfg.peer.is_some() => {
                let Some(d) = self.done.get_mut(seq as usize) else {
                    return;
                };
                if !*d {
                    *d = true;
                    self.done_count += 1;
                    self.inflight.remove(&seq);
                    self.events.push_back(ToyEvent::Echoed(seq));
                    if self.is_complete() {
                        self.events.push_back(ToyEvent::Complete);
                    }
                }
                self.pump(now);
            }
            _ => {}
        }
    }

    fn poll_transmit(&mut self, _now: Time, buf: &mut [u8]) -> Option<Transmit> {
        let (local, remote, m) = self.out.pop_front()?;
        let dst = buf.get_mut(..m.len())?;
        dst.copy_from_slice(&m);
        Some(Transmit {
            local,
            remote,
            len: m.len(),
            send_at: None,
        })
    }

    fn poll_timeout(&mut self) -> Option<Time> {
        self.inflight.values().min().map(|t| t + self.cfg.rto)
    }

    fn handle_timeout(&mut self, now: Time) {
        let due: Vec<u32> = self
            .inflight
            .iter()
            .filter(|(_, t)| **t + self.cfg.rto <= now)
            .map(|(s, _)| *s)
            .collect();
        for seq in due {
            self.events.push_back(ToyEvent::Retransmit(seq));
            self.send_data(seq, now);
        }
    }

    fn command(&mut self, now: Time, cmd: ToyCmd) {
        match cmd {
            ToyCmd::Start => {
                self.started = true;
                self.pump(now);
            }
        }
    }

    fn poll_event(&mut self) -> Option<ToyEvent> {
        self.events.pop_front()
    }

    fn crash(&mut self, _now: Time) -> Vec<u8> {
        let mut bytes = vec![u8::from(self.started)];
        bytes.extend(self.done.iter().map(|d| u8::from(*d)));
        self.out.clear();
        self.inflight.clear();
        self.seen.clear();
        self.events.clear();
        self.started = false;
        self.done.iter_mut().for_each(|d| *d = false);
        self.done_count = 0;
        self.next = 0;
        bytes
    }

    fn restart(&mut self, now: Time, persisted: &[u8]) {
        self.restored_len = persisted.len();
        self.local = self.cfg.local;
        if let Some((s, done)) = persisted.split_first() {
            self.started = *s == 1;
            for (d, b) in self.done.iter_mut().zip(done) {
                *d = *b == 1;
            }
            self.done_count = self.done.iter().filter(|d| **d).count() as u32;
        }
        self.pump(now);
    }

    fn suspend(&mut self, _now: Time) {
        self.suspends += 1;
    }

    fn resume(&mut self, _now: Time) {
        self.resumes += 1;
    }

    fn iface_event(&mut self, _now: Time, event: IfaceEvent) {
        if let IfaceEvent::Changed { new, .. } = event {
            self.local = SocketAddr::new(new, self.local.port());
        }
    }
}

/// A convenience for tests: the socket address of `ip` and `port`.
pub const fn sock(ip: IpAddr, port: u16) -> SocketAddr {
    SocketAddr::new(ip, port)
}

/// A command to a [`Probe`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProbeCmd {
    /// Send `data` from `local` to `remote`.
    Send {
        /// Source address.
        local: SocketAddr,
        /// Destination address.
        remote: SocketAddr,
        /// The datagram.
        data: Vec<u8>,
    },
    /// Like `Send`, but the datagram leaves no earlier than the true time `at`.
    SendAt {
        /// Source address.
        local: SocketAddr,
        /// Destination address.
        remote: SocketAddr,
        /// The datagram.
        data: Vec<u8>,
        /// Earliest departure.
        at: Time,
    },
    /// Ask for a timeout at this time.
    Timer(Time),
    /// Set the bytes the node will report as durable when it crashes.
    Persist(Vec<u8>),
}

/// An event of a [`Probe`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProbeEvent {
    /// A datagram arrived.
    Recv {
        /// The address it arrived at.
        local: SocketAddr,
        /// The address it came from.
        remote: SocketAddr,
        /// The datagram.
        data: Vec<u8>,
    },
    /// A requested timeout fired at this time.
    Timer(Time),
}

/// A scripted node: it sends what commands tell it to and reports what it receives.
#[derive(Default)]
pub struct Probe {
    out: VecDeque<(SocketAddr, SocketAddr, Vec<u8>, Option<Time>)>,
    events: VecDeque<ProbeEvent>,
    timer: Option<Time>,
    durable: Vec<u8>,
    /// The bytes the last restart received.
    pub restored: Vec<u8>,
    /// How many restarts happened.
    pub restarts: u32,
    /// Interface events received, in order.
    pub ifaces: Vec<IfaceEvent>,
    /// Times of suspend and resume calls, as `(time, true for suspend)`.
    pub sleeps: Vec<(Time, bool)>,
    /// Work the node reports per call (ticks), for cost-model tests.
    pub ticks_per_call: u64,
    /// When true a requested timeout is not cleared when it fires, so the node keeps asking for a past time.
    pub sticky: bool,
    /// Timer calls that name their own time as the next deadline before the timer clears.
    pub again: u32,
    /// The time of every call to `handle_datagram`, which shows when the node actually ran.
    pub call_times: Vec<Time>,
    /// A datagram the node queues when it is suspended (a farewell), as `(local, remote, data)`.
    pub farewell: Option<(SocketAddr, SocketAddr, Vec<u8>)>,
}

impl Probe {
    /// A node with nothing to do.
    pub fn new() -> Self {
        Self::default()
    }
}

impl Node for Probe {
    type Cmd = ProbeCmd;
    type Event = ProbeEvent;

    fn handle_datagram(&mut self, now: Time, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        self.call_times.push(now);
        self.events.push_back(ProbeEvent::Recv {
            local,
            remote,
            data: data.to_vec(),
        });
    }

    fn poll_transmit(&mut self, _now: Time, buf: &mut [u8]) -> Option<Transmit> {
        let (local, remote, m, send_at) = self.out.pop_front()?;
        buf.get_mut(..m.len())?.copy_from_slice(&m);
        Some(Transmit {
            local,
            remote,
            len: m.len(),
            send_at,
        })
    }

    fn poll_timeout(&mut self) -> Option<Time> {
        self.timer
    }

    fn handle_timeout(&mut self, now: Time) {
        if self.again > 0 {
            self.again -= 1;
            self.timer = Some(now);
        } else if !self.sticky {
            self.timer = None;
        }
        self.events.push_back(ProbeEvent::Timer(now));
    }

    fn command(&mut self, _now: Time, cmd: ProbeCmd) {
        match cmd {
            ProbeCmd::Send { local, remote, data } => self.out.push_back((local, remote, data, None)),
            ProbeCmd::SendAt {
                local,
                remote,
                data,
                at,
            } => self.out.push_back((local, remote, data, Some(at))),
            ProbeCmd::Timer(t) => self.timer = Some(t),
            ProbeCmd::Persist(b) => self.durable = b,
        }
    }

    fn poll_event(&mut self) -> Option<ProbeEvent> {
        self.events.pop_front()
    }

    fn crash(&mut self, _now: Time) -> Vec<u8> {
        self.out.clear();
        self.events.clear();
        self.timer = None;
        std::mem::take(&mut self.durable)
    }

    fn restart(&mut self, _now: Time, persisted: &[u8]) {
        self.restarts += 1;
        self.restored = persisted.to_vec();
        self.durable = persisted.to_vec();
    }

    fn suspend(&mut self, now: Time) {
        self.sleeps.push((now, true));
        if let Some((local, remote, data)) = self.farewell.take() {
            self.out.push_back((local, remote, data, None));
        }
    }

    fn resume(&mut self, now: Time) {
        self.sleeps.push((now, false));
    }

    fn iface_event(&mut self, _now: Time, event: IfaceEvent) {
        self.ifaces.push(event);
    }

    fn take_work(&mut self) -> Work {
        Work {
            ticks: self.ticks_per_call,
            ns: 0,
        }
    }
}
