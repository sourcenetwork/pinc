#![allow(clippy::doc_markdown, reason = "frame names such as REKEY are prose, not code")]

//! The connection: the handshake over `vinc-security`, packet assembly and dispatch, paths and migration, path MTU,
//! key rolls, the fixed idle timeout, close, and sleep and wake, over the packet layer, recovery and the stream
//! layer of this crate.
//!
//! # Driving a connection
//!
//! The connection is a SANS-IO state machine. Time and randomness come in through `&mut` [`Env`] on every call that
//! needs them; received datagrams go to [`Connection::handle_datagram`]; datagrams to send come out of
//! [`Connection::poll_transmit`] into a caller buffer, with a `segment_size` when several same-size datagrams to one
//! path are batched for GSO; [`Connection::poll_timeout`] says when to call [`Connection::handle_timeout`]; and
//! [`Connection::poll_event`] yields what happened. After any input, call `poll_transmit` until it returns `None`.
//!
//! # Storage
//!
//! The connection borrows its stream table: `&'a mut Streams`. A default table is about 820 KiB, so a connection
//! that owned it would be unusable on a small stack and impossible without a heap; borrowing lets the caller choose
//! the place (a static slab, a `Box`, an arena) and reuse one table across connections, and it works with and
//! without the `alloc` feature. The buffer pool is passed by value ([`Resources`]) and every buffer the connection
//! holds is charged to it.
//!
//! # Handshake and early data
//!
//! Handshake messages travel in long Handshake packets, cut into datagram-sized fragments (see the `handshake`
//! module). With a ticket the client sends ZeroRtt packets under the early keys in the same datagrams as its Hello;
//! if the server rejects the ticket, everything sent early is declared lost without a congestion response and goes
//! out again under the 1-RTT keys. A connection holds at most 8 packets that
//! arrived ahead of their keys (a 0-RTT or 1-RTT packet reordered ahead of the handshake message that brings the keys)
//! and processes them once the keys exist.
//!
//! # Extension frames
//!
//! A frame of type 0x40 and up is not parsed here. Its body is copied into a bounded queue held in the buffer pool and
//! handed out as [`Event::Extension`], borrowed from the connection until the next
//! [`poll_event`](Connection::poll_event) call. When the queue is full the oldest entry is dropped and counted. A
//! frame sent with [`send_extension`](Connection::send_extension) is kept (up to what fits one packet at the path MTU) and
//! sent again until its packet is acknowledged, so the receiver may see it more than once.
//!
//! # Invariants
//!
//! One packet-number space serves 0-RTT and 1-RTT packets; numbers strictly increase and are never reused. A
//! datagram never exceeds the datagram size of its path, and an unvalidated path never receives more than three
//! times what it sent us. Every buffer is charged to the pool; running out drops data (a received packet is not
//! acknowledged, so the peer sends it again) and never overflows. Nothing allocates per packet and no input panics.

/// Define methods on [`Connection`] without repeating its generics in every file.
macro_rules! conn_impl {
    ($($body:tt)*) => {
        impl<'a, P, S, const N: usize, const C: usize, const F: usize, const NP: usize> Connection<'a, P, S, N, C, F, NP>
        where
            P: Provider,
            S: StreamSource,
        {
            $($body)*
        }
    };
}

mod api;
mod cid;
mod config;
mod ctl;
mod drive;
mod event;
mod handshake;
mod held;
mod hooks;
mod keys;
mod life;
mod mtu;
mod params;
mod path;
mod reasm;
mod recv;
mod send;
mod tables;
mod timer;

use vinc_crypto::Provider;
use vinc_security::{
    AmpBudget, ConnId, Env, Established, Failure, Initiator, InitiatorParams, Responder, ResponderConfig,
};

pub use api::ExtensionError;
#[cfg(feature = "trace")]
pub use cid::trace::{CidTable, CidView};
pub use config::{
    ClientParams, Config, DEFAULT_SEND_WINDOW, IDLE_TIMEOUT, JUMBO_MTU, MIN_MTU, PROBE_MTU, PathId, PathInfo,
    ServerParams, Stats,
};
pub use event::{CloseReason, Drop, Event, EventTable, code};
pub use handshake::Machines;
pub use held::{Held, Shared};
pub use hooks::{SubOpen, SubWait};
#[cfg(feature = "trace")]
pub use keys::trace::{KeyEvent, KeysView, Slot};
#[cfg(feature = "trace")]
pub use mtu::trace::{MtuProbe, MtuView};
pub use params::{CreditRecord, credit_for_streams, peer_limits};
pub use path::{PathError, RJ_THIN_GAP};
#[cfg(feature = "trace")]
pub use reasm::trace::{FragmentView, ReasmProbe, ReasmView};
pub use send::Transmit;
#[cfg(feature = "trace")]
pub use send::trace::{PackKind, PackMode, PackProbe, PackRecord};
pub use tables::Tables;
#[cfg(feature = "trace")]
pub use timer::trace::{CarrierView, TimerView};

use self::cid::Cids;
use self::ctl::Ctl;
use self::event::{Ev, EvQueue};
use self::handshake::{Handshake, Machine, Timing};
use self::keys::Keys;
use self::life::Life;
use self::path::Paths;
use crate::packet::PN_LEN_BASE;
use crate::recovery::{LossEstimate, ReceivedPackets, Recovery, TailRepair};
use crate::stream::datagram::{Datagrams, EarlyData};
use crate::stream::pool::BufferPool;
use crate::stream::{NoSource, StreamSource, Streams};

/// The received packet-number ranges tracked. Below the floor a packet counts as a duplicate, so this must hold the
/// holes that deep reordering leaves open. The deepest of the reordering scenarios measured (5 ms of independent
/// jitter on top of 5% of the packets held back 20 ms, at a window of megabytes) needs 116 at once; 96 and below
/// forgot holes and judged new packets duplicates (32 did in most of the scenarios), 128 and above never did.
/// Acknowledgements still report at most `MAX_ACK_RANGES`.
const RX_RANGES: usize = 128;

/// Everything a connection borrows or is handed: the buffer pool, the stream table and the shared loss average.
pub struct Resources<'a, S: StreamSource, const N: usize, const C: usize, const F: usize> {
    /// The pool every buffer of the connection is charged to.
    pub pool: BufferPool<'a>,
    /// The stream table, created with `Config::new(is_client)` of the stream layer.
    pub streams: Held<'a, Streams<S, N, C>>,
    /// The node-wide loss average that decides tail repair.
    pub loss: Shared<'a, LossEstimate>,
    /// The tables the connection builds on, cleared (see [`Tables::clear`]): it records at most `F` packets in flight.
    pub tables: Tables<F>,
}

/// Where the connection is in its life.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Phase {
    Handshaking,
    Connected,
    Closing,
    Closed,
}

/// A VINCER connection, client or server.
///
/// Type parameters: the crypto provider `P`, the source type `S` of source-backed streams, `N` stream slots, `C`
/// chunk-ring entries per stream half, `F` sent packets tracked in flight and `NP` paths.
#[allow(clippy::struct_excessive_bools, reason = "independent protocol flags")]
pub struct Connection<
    'a,
    P: Provider,
    S: StreamSource = NoSource,
    const N: usize = 100,
    const C: usize = 1025,
    const F: usize = 512,
    const NP: usize = 4,
> {
    client: bool,
    cfg: Config,
    phase: Phase,
    pool: BufferPool<'a>,
    streams: Held<'a, Streams<S, N, C>>,
    loss: Shared<'a, LossEstimate>,
    dgrams: Datagrams,
    ext: Datagrams<16, 4>,
    early: EarlyData,
    hs: Handshake,
    est: Option<Established>,
    keys: Keys<P>,
    rec: Recovery<F>,
    rx: ReceivedPackets<RX_RANGES>,
    ctl: Ctl,
    tail: TailRepair,
    cids: Cids,
    paths: Paths<NP>,
    sess_amp: AmpBudget,
    pn_len: usize,
    events: EvQueue,
    gated: bool,
    life: Life,
    stats: Stats,
    next_pn: u64,
    started: u64,
    odcid: ConnId,
    resumed: bool,
    confirmed: bool,
    ext_release: bool,
    /// Kinds of stream (bit 0 unidirectional, bit 1 bidirectional) whose open was refused for want of credit or room.
    open_wait: u8,
    paced_until: Option<u64>,
    degraded_told: bool,
    local_credit: CreditRecord,
    peer_credit: CreditRecord,
    /// Path slots that receive a copy of every handshake flight, those still owed the current flight, and the one
    /// being served now.
    fan_set: u16,
    fan_mask: u16,
    fan_target: Option<usize>,
    fan_skip: bool,
    /// The log of the packet builder (trace validation only).
    #[cfg(feature = "trace")]
    pack: send::trace::PackLog,
}

impl<'a, P, S, const N: usize, const C: usize, const F: usize, const NP: usize> Connection<'a, P, S, N, C, F, NP>
where
    P: Provider,
    S: StreamSource,
{
    #[allow(clippy::too_many_arguments, reason = "the fields both constructors fix, passed once")]
    fn base(
        client: bool,
        cfg: Config,
        res: Resources<'a, S, N, C, F>,
        machine: Machine,
        first_cid: ConnId,
        odcid: ConnId,
        now: u64,
        local_credit: CreditRecord,
    ) -> Result<Self, Failure> {
        const {
            assert!(
                event::queue_fits(N, NP),
                "the event queue is too small for the stream slots and paths"
            );
        };
        let Resources {
            mut pool,
            mut streams,
            loss,
            tables,
        } = res;
        streams.set_advertised(u64::from(local_credit.max_streams));
        let timing = Timing {
            thin: cfg.thin,
            remembered_rtt: cfg.remembered_rtt,
            node_rtt: cfg.node_rtt,
            node_peak_rtt: cfg.node_peak_rtt,
        };
        let Tables { sent, events, machines } = tables;
        let hs = Handshake::new(machine, machines, &mut pool, now, timing)?;
        let mut life = Life::new(now);
        life.keepalive = cfg.keepalive;
        let mut rec = Recovery::with_ring(u64::from(MIN_MTU), sent);
        if let Some(r) = cfg.node_peak_rtt {
            rec.set_node_rtt(r);
        }
        if let Some(r) = cfg.node_rtt {
            rec.set_handshake_rtt(r);
        }
        if let Some(b) = cfg.gate_slack {
            rec.set_gate_slack(b);
        }
        Ok(Self {
            client,
            cfg,
            phase: Phase::Handshaking,
            pool,
            streams,
            loss,
            dgrams: Datagrams::new(),
            ext: Datagrams::new(),
            early: EarlyData::new(),
            hs,
            est: None,
            keys: Keys::new(client),
            rec,
            rx: {
                let mut rx = ReceivedPackets::new();
                rx.set_every(cfg.ack_every);
                rx
            },
            ctl: Ctl::new(),
            tail: TailRepair::new(),
            cids: Cids::new(client, first_cid),
            paths: Paths::new(),
            sess_amp: AmpBudget::new(),
            pn_len: PN_LEN_BASE,
            events: EvQueue::new(events),
            gated: false,
            life,
            stats: Stats::default(),
            next_pn: 0,
            started: now,
            odcid,
            resumed: false,
            confirmed: false,
            ext_release: false,
            open_wait: 0,
            paced_until: None,
            degraded_told: false,
            local_credit,
            peer_credit: CreditRecord::NONE,
            fan_set: 0,
            fan_mask: 0,
            fan_target: None,
            fan_skip: false,
            #[cfg(feature = "trace")]
            pack: send::trace::PackLog::new(),
        })
    }

    /// What this endpoint advertises, which its stream table then runs with: the configured credit record with the
    /// stream window clamped to what this stream table and pool can hold, and the stream limit to the table's slots
    /// and to the streams the pool has room to promise. One record for both, so the window a peer is told is the one
    /// enforced and counted here, and the configured stream limit is the most streams the peer ever has live.
    fn advertise(cfg: &Config, streams: &mut Streams<S, N, C>, pool: &BufferPool<'_>) -> CreditRecord {
        let slots = cfg.credit.max_streams.min(u16::try_from(N).unwrap_or(u16::MAX));
        streams.adopt(pool, cfg.credit.window_bytes(), u64::from(slots));
        CreditRecord {
            window_units: cfg
                .credit
                .window_units
                .min(CreditRecord::new(streams.recv_window(), 0, 0).window_units),
            max_streams: slots.min(u16::try_from(streams.advertised_streams()).unwrap_or(u16::MAX)),
            max_datagram: cfg.credit.max_datagram,
        }
    }

    fn random_cid(env: &mut Env<'_, P>, len: usize) -> Result<ConnId, Failure> {
        let mut bytes = [0u8; crate::packet::MAX_CID_LEN];
        if len == 0 {
            return Err(Failure::InvalidParameter);
        }
        let raw = bytes.get_mut(..len).ok_or(Failure::InvalidParameter)?;
        env.drbg.fill(raw).map_err(|_| Failure::Randomness)?;
        ConnId::new(raw).ok_or(Failure::InvalidParameter)
    }

    /// Dial a node. The first flight is ready for [`poll_transmit`](Self::poll_transmit) at once; with a ticket the
    /// client may also write stream and datagram data before the handshake completes (0-RTT).
    ///
    /// # Errors
    /// A [`Failure`] if the parameters are invalid (a connection id length outside 1 to 20) or
    /// the random generator refuses.
    pub fn client(
        cfg: Config,
        params: ClientParams<'_>,
        mut res: Resources<'a, S, N, C, F>,
        env: &mut Env<'_, P>,
    ) -> Result<Self, Failure> {
        let cid = Self::random_cid(env, cfg.cid_len)?;
        let odcid = Self::random_cid(env, 8)?;
        let local = Self::advertise(&cfg, &mut res.streams, &res.pool);
        let remembered = params.ticket.as_ref().map(|t| *t.peer_credit());
        let init = Initiator::new(
            env,
            InitiatorParams {
                peer: params.peer,
                alpn: params.alpn,
                scid: cid,
                identity: params.identity,
                prekey: params.prekey,
                peer_has_prekey: params.peer_has_prekey,
                ticket: params.ticket,
                credit: local,
            },
        )?;
        let mut c = Self::base(true, cfg, res, Machine::Client(init), cid, odcid, env.now, local)?;
        // Until the server's parameters arrive, the minimum holds; with a ticket, 0-RTT data may rely on what the
        // server advertised in the session that issued it.
        if let Some(p) = remembered {
            c.streams.set_peer_limits(&peer_limits(&p));
            c.peer_credit = p;
        }
        c.new_path_slot(params.path, params.path_info, env.now);
        if let Some(p) = c.paths.active_mut() {
            p.validated = true;
            p.amp.validate();
        }
        c.sess_amp.validate();
        c.pump(env);
        Ok(c)
    }

    /// Accept a connection. The first datagram of the client goes to
    /// [`handle_datagram_with`](Self::handle_datagram_with), which tells the connection its path.
    ///
    /// # Errors
    /// A [`Failure`] if the connection id length is outside 1 to 20 or the random generator refuses.
    pub fn server(
        cfg: Config,
        params: &ServerParams,
        mut res: Resources<'a, S, N, C, F>,
        env: &mut Env<'_, P>,
    ) -> Result<Self, Failure> {
        let cid = Self::random_cid(env, cfg.cid_len)?;
        let odcid = ConnId::default();
        let local = Self::advertise(&cfg, &mut res.streams, &res.pool);
        let mut rc = ResponderConfig::new(params.identity, cid, params.alpns);
        rc.tickets_per_session = params.tickets_per_session;
        rc.ticket_lifetime_s = params.ticket_lifetime_s;
        rc.credit = local;
        let c = Self::base(
            false,
            cfg,
            res,
            Machine::Server(Responder::new(rc)),
            cid,
            odcid,
            env.now,
            local,
        )?;
        Ok(c)
    }

    /// Whether the handshake completed and the connection is open.
    pub const fn is_connected(&self) -> bool {
        matches!(self.phase, Phase::Connected)
    }

    /// Whether the connection ended: closed, or closing with its CLOSE still to leave.
    pub const fn is_closed(&self) -> bool {
        matches!(self.phase, Phase::Closed | Phase::Closing)
    }

    /// Whether this endpoint dialed.
    pub const fn is_client(&self) -> bool {
        self.client
    }

    /// The counters of the connection, with the congestion window, round trip and datagram size filled in.
    pub fn stats(&self) -> Stats {
        let mut s = self.stats;
        s.cwnd = self.rec.cwnd();
        s.srtt = if self.rec.rtt().has_sample() {
            self.rec.rtt().smoothed()
        } else {
            0
        };
        s.mtu = self.paths.active().map_or(MIN_MTU, |p| p.mtu.current);
        s.datagrams_dropped_send = self.dgrams.send_dropped();
        s.datagrams_dropped_recv = self.dgrams.recv_dropped();
        s.events_lost = self.events.lost;
        s.held_back = self.streams.stats().held_back;
        s
    }

    /// The buffer pool the connection charges.
    pub const fn pool(&self) -> &BufferPool<'a> {
        &self.pool
    }

    /// The loss recovery state, for inspection.
    pub const fn recovery(&self) -> &Recovery<F> {
        &self.rec
    }

    /// The authenticated session, once the handshake completed.
    pub const fn session(&self) -> Option<&Established> {
        self.est.as_ref()
    }

    /// Every connection id this side accepts now. An endpoint that serves many connections routes a datagram to the
    /// connection whose list holds its destination id; two connections may hold the same id by chance, and the one
    /// whose keys open the packet owns it.
    pub fn local_cids(&self) -> impl Iterator<Item = ConnId> + '_ {
        self.cids.local()
    }

    /// Whether `cid` is one this side accepts now.
    pub fn accepts_cid(&self, cid: &ConnId) -> bool {
        self.cids.is_local(cid)
    }

    fn push(&mut self, ev: Ev) {
        self.events.push(ev);
    }
}
