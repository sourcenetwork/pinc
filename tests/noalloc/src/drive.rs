//! The exchange: a dialer and a listener, each an endpoint on borrowed storage, a handshake between them and one
//! stream from the dialer to the listener.
//!
//! The host loop is the sans-IO one: serve the events of each side, carry every datagram one side sends to the
//! other, and when nothing moves jump the clock to the next deadline. It holds its datagram buffers and both
//! endpoints in its frame and the pool chunks in the static slabs; it allocates nothing.
//!
//! Invariants: every loop is bounded; a failure is a [`Stage`], never a panic.

use core::net::{IpAddr, Ipv4Addr, SocketAddr};

use vinc_core::{
    Answer, Command, CommandError, Endpoint, EndpointConfig, Event, MAX_DATAGRAM, Query, Role, SessionId, Slot,
    Transmit, Value,
};
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use vinc_security::{Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys};
use vinc_transport::conn::{Resources, Tables};
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::{BufferPool, RawChunk};
use vinc_transport::stream::{self, NoSource, RecvStatus, Streams};

use crate::mem::{self, CHUNKS, SLOTS};

const STREAMS: usize = 8;
const CHUNK_RING: usize = 17;
const IN_FLIGHT: usize = 128;
const PATHS: usize = 4;
const LOOKUP: usize = 32;
const PREKEYS: usize = 8;
const TICKETS: usize = 16;
const CLIENT_TICKETS: usize = 8;

type Stack = Streams<NoSource, STREAMS, CHUNK_RING>;
type Seat<'a> = Slot<'a, Software, NoSource, STREAMS, CHUNK_RING, IN_FLIGHT, PATHS>;
type Ep<'s, 'a> = Endpoint<
    's,
    'a,
    Software,
    NoSource,
    STREAMS,
    CHUNK_RING,
    IN_FLIGHT,
    PATHS,
    SLOTS,
    LOOKUP,
    PREKEYS,
    TICKETS,
    CLIENT_TICKETS,
>;

const ALPN: &[u8] = b"vinc/noalloc";
const PAYLOAD: &[u8] = b"one stream, no heap";
const DIALER: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1)), 4433);
const LISTENER: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2)), 4433);
const SEC: u64 = 1_000_000_000;
/// Clock jumps before the exchange is called stuck.
const STEPS: usize = 4096;
/// Hand-offs in one settle before it is called stuck.
const ROUNDS: usize = 256;
/// Datagrams one side sends in one hand-off.
const BURST: usize = 256;
const PENDING: usize = 32;

/// Where the exchange stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Stage {
    /// The static storage was already in use.
    Storage,
    /// An endpoint could not be set up.
    Setup,
    /// A command was refused (with why), or an event was lost (`None`).
    Command(Option<CommandError>),
    /// The datagram buffers did not fit what an endpoint sent.
    Wire,
    /// The two sessions did not come up.
    Handshake,
    /// The stream did not arrive whole and finished.
    Stream,
    /// The bytes that arrived are not the bytes sent.
    Data,
}

/// A fixed first-in first-out queue of events.
struct Pending {
    items: [Option<Event>; PENDING],
    head: usize,
    len: usize,
}

impl Pending {
    const fn new() -> Self {
        Self {
            items: [None; PENDING],
            head: 0,
            len: 0,
        }
    }

    fn push(&mut self, ev: Event) -> bool {
        let at = (self.head + self.len) % PENDING;
        match self.items.get_mut(at) {
            Some(slot) if self.len < PENDING => {
                *slot = Some(ev);
                self.len += 1;
                true
            }
            _ => false,
        }
    }

    fn pop(&mut self) -> Option<Event> {
        if self.len == 0 {
            return None;
        }
        let ev = self.items.get_mut(self.head)?.take();
        self.head = (self.head + 1) % PENDING;
        self.len -= 1;
        ev
    }
}

/// One host: an endpoint, its keys and what it saw.
struct Side<'s, 'a> {
    ep: Ep<'s, 'a>,
    kp: Keypair,
    prekeys: SoftPrekeys<Software>,
    drbg: Drbg,
    addr: SocketAddr,
    node: NodeId,
    pending: Pending,
    /// The session, once it is open for the application.
    up: Option<SessionId>,
    got: [u8; PAYLOAD.len()],
    got_len: usize,
    finished: bool,
    failed: Option<Stage>,
}

impl<'s, 'a> Side<'s, 'a> {
    fn new(tag: u8, addr: SocketAddr, now: u64, slots: &'s mut [Seat<'a>; SLOTS]) -> Option<Self> {
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[tag; 32]).ok()?;
        let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).ok()?;
        let mut drbg = Drbg::new(&[tag ^ 0x5a; 32]);
        let cfg = EndpointConfig::new(u64::from(tag) * 0x9E37_79B9);
        let mut ep = Endpoint::new(now, Software, Drbg::new(&[tag ^ 0xa5; 32]), identity, cfg, slots);
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).ok()?;
        ep.set_prekey(prekeys.acquire(&mut env).ok()?);
        if !ep.register_alpn(ALPN) {
            return None;
        }
        ep.add_iface(addr)?;
        Some(Self {
            ep,
            kp,
            prekeys,
            drbg,
            addr,
            node: identity.node_id(),
            pending: Pending::new(),
            up: None,
            got: [0; PAYLOAD.len()],
            got_len: 0,
            finished: false,
            failed: None,
        })
    }

    /// Run a command; the events it answers with are kept for [`Self::service`]. A refusal marks the side failed.
    fn run(&mut self, now: u64, cmd: Command<'_>) -> Option<Value> {
        match self.ep.command(now, cmd) {
            Ok(rep) => {
                for ev in rep.events.iter() {
                    if !self.pending.push(*ev) {
                        self.failed = Some(Stage::Command(None));
                    }
                }
                Some(rep.value)
            }
            Err(e) => {
                self.failed = Some(Stage::Command(Some(e)));
                None
            }
        }
    }

    /// Serve every event the side holds, the host duties of a node: keys, the access check, reading streams.
    fn service(&mut self, now: u64) {
        while let Some(ev) = self.pending.pop().or_else(|| self.ep.poll_event()) {
            match ev {
                Event::KeyRequest { session } => self.answer_keys(now, session),
                Event::AcpCheck { check, .. } => {
                    self.run(now, Command::AcpAnswer { check, allow: true });
                }
                Event::Connected { session, .. } | Event::Incoming { session, .. } => self.up = Some(session),
                Event::StreamReadable { session, stream } if !self.finished => self.read(now, session, stream),
                _ => {}
            }
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
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let response = match self.ep.query(Query::KeyRequest(session)) {
            Answer::KeyRequest(req) => soft.answer(&mut env, &req, &mut sig),
            _ => return,
        };
        self.run(now, Command::KeyResponse { session, response });
    }

    fn read(&mut self, now: u64, session: SessionId, stream: u64) {
        loop {
            let n = match self.ep.query(Query::Read { session, stream }) {
                Answer::Chunk(chunk) if !chunk.is_empty() => {
                    let room = self.got.get_mut(self.got_len..).unwrap_or_default();
                    let k = chunk.len().min(room.len());
                    room.iter_mut().zip(chunk).for_each(|(to, from)| *to = *from);
                    self.got_len += k;
                    chunk.len()
                }
                _ => 0,
            };
            let done = self.run(now, Command::Consume { session, stream, n });
            self.finished |= done == Some(Value::Recv(RecvStatus::Finished));
            if n == 0 || self.finished {
                return;
            }
        }
    }

    fn received(&self) -> &[u8] {
        self.got.get(..self.got_len).unwrap_or_default()
    }
}

/// Carry what `from` has to send into `to`; whether any datagram moved. `None` when a datagram does not fit `buf`.
fn forward(from: &mut Side<'_, '_>, to: &mut Side<'_, '_>, now: u64, buf: &mut [u8], rx: &mut [u8]) -> Option<bool> {
    let mut moved = false;
    for _ in 0..BURST {
        let Some(Transmit { len, segment_size, .. }) = from.ep.poll_transmit(now, buf) else {
            break;
        };
        if segment_size == 0 {
            return None;
        }
        for chunk in buf.get(..len)?.chunks(segment_size) {
            let datagram = rx.get_mut(..chunk.len())?;
            datagram.copy_from_slice(chunk);
            to.ep.handle_datagram(now, to.addr, from.addr, datagram);
        }
        moved = true;
    }
    Some(moved)
}

/// Serve and carry until nothing moves at `now`.
fn settle(a: &mut Side<'_, '_>, b: &mut Side<'_, '_>, now: u64, buf: &mut [u8], rx: &mut [u8]) -> Option<()> {
    for _ in 0..ROUNDS {
        a.service(now);
        b.service(now);
        let moved = forward(a, b, now, buf, rx)?;
        if !(forward(b, a, now, buf, rx)? | moved) {
            return Some(());
        }
    }
    None
}

/// A session slot running in `chunks`, with its stream table kept in `streams`.
fn seat<'a>(chunks: &'a mut [RawChunk; CHUNKS], streams: &'a mut Option<Stack>, loss: &'a LossEstimate) -> Seat<'a> {
    let pool = BufferPool::from_slab(chunks);
    let table = streams.insert(Streams::new(&stream::Config::new(false), &pool));
    Slot::new(Resources {
        pool,
        streams: table.into(),
        loss: loss.into(),
        tables: Tables::new(),
    })
}

// The seats cannot move to the static slabs: a seat borrows the endpoint's loss estimate, which is not `Sync` on a
// target without compare-and-swap and so cannot be a static, and building one is not a `const` operation.
/// Run the exchange: connect, send [`PAYLOAD`] on a new stream, finish it, and compare what arrived.
#[allow(
    clippy::large_stack_arrays,
    reason = "the two seats of a side live in this frame, which the program sizes (a 64 MiB thread, or the linker's stack)"
)]
pub(crate) fn drive() -> Result<(), Stage> {
    let slabs = mem::take().ok_or(Stage::Storage)?;
    let [d0, d1, l0, l1] = slabs.each_mut();
    let (loss_d, loss_l) = (LossEstimate::new(), LossEstimate::new());
    let mut tables_d: [Option<Stack>; SLOTS] = [None, None];
    let mut tables_l: [Option<Stack>; SLOTS] = [None, None];
    let [dial_a, dial_b] = &mut tables_d;
    let [lis_a, lis_b] = &mut tables_l;
    let mut seats_d = [seat(d0, dial_a, &loss_d), seat(d1, dial_b, &loss_d)];
    let mut seats_l = [seat(l0, lis_a, &loss_l), seat(l1, lis_b, &loss_l)];

    let mut now = SEC;
    let mut dialer = Side::new(1, DIALER, now, &mut seats_d).ok_or(Stage::Setup)?;
    let mut listener = Side::new(2, LISTENER, now, &mut seats_l).ok_or(Stage::Setup)?;
    let (mut buf, mut rx) = ([0u8; MAX_DATAGRAM], [0u8; MAX_DATAGRAM]);

    let dial = Command::Connect {
        node: listener.node,
        alpn: ALPN,
        addrs: &[LISTENER],
        role: Role::Other,
    };
    if !matches!(dialer.run(now, dial), Some(Value::Session(_))) {
        return Err(dialer.failed.unwrap_or(Stage::Command(None)));
    }
    let mut sent = false;
    for _ in 0..STEPS {
        settle(&mut dialer, &mut listener, now, &mut buf, &mut rx).ok_or(Stage::Wire)?;
        if let Some(stage) = dialer.failed.or(listener.failed) {
            return Err(stage);
        }
        if let (false, Some(session), Some(_)) = (sent, dialer.up, listener.up) {
            send(&mut dialer, session, now)?;
            sent = true;
            continue;
        }
        if listener.finished {
            return if listener.received() == PAYLOAD {
                Ok(())
            } else {
                Err(Stage::Data)
            };
        }
        let deadlines = [dialer.ep.poll_timeout(), listener.ep.poll_timeout()];
        let Some(next) = deadlines.into_iter().flatten().min() else {
            break;
        };
        now = now.max(next);
        dialer.ep.handle_timeout(now);
        listener.ep.handle_timeout(now);
    }
    Err(if sent { Stage::Stream } else { Stage::Handshake })
}

/// Open a stream on `session`, write [`PAYLOAD`] and finish it.
fn send(dialer: &mut Side<'_, '_>, session: SessionId, now: u64) -> Result<(), Stage> {
    let Some(Value::Stream(stream)) = dialer.run(now, Command::OpenStream { session, bidi: false }) else {
        return Err(Stage::Stream);
    };
    let data = PAYLOAD;
    if dialer.run(now, Command::Write { session, stream, data }) != Some(Value::Written(PAYLOAD.len())) {
        return Err(Stage::Stream);
    }
    dialer.run(now, Command::Finish { session, stream });
    Ok(())
}
