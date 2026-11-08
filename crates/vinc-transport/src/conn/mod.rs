#![allow(clippy::doc_markdown, reason = "frame names such as NEW_TOKEN are prose, not code")]

//! The connection: the handshake over `vinc-security`, packet assembly and dispatch, paths and migration, path MTU,
//! key updates, idle timeout, close and drain, and sleep and wake, over the packet layer, recovery and the stream
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
//! out again under the 1-RTT keys. A server buffers at most 8 early 1-RTT packets until the peer is authenticated.
//!
//! # Extension frames
//!
//! A frame of type 0x40 and up (and NEW_TOKEN) is not parsed here. Its body is copied into a bounded queue held in
//! the buffer pool and handed out as [`Event::Extension`], borrowed from the connection until the next
//! [`poll_event`](Connection::poll_event) call. When the queue is full the oldest entry is dropped and counted.
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
mod keys;
mod life;
mod mtu;
mod path;
mod recv;
mod send;
mod timer;

use vinc_crypto::Provider;
use vinc_security::{ConnId, Env, Established, Failure, Initiator, InitiatorParams, Responder, ResponderConfig};

pub use cid::reset_token;
pub use config::{
    ClientParams, Config, DEFAULT_IDLE, JUMBO_MTU, MIN_MTU, PROBE_MTU, PathId, PathInfo, ServerParams, Stats,
};
pub use event::{CloseReason, Drop, Event, code};
pub use path::PathError;
pub use send::Transmit;

use self::cid::Cids;
use self::ctl::Ctl;
use self::event::{Ev, EvQueue};
use self::handshake::{Handshake, Machine};
use self::keys::Keys;
use self::life::Life;
use self::path::Paths;
use crate::recovery::{LossEstimate, ReceivedPackets, Recovery};
use crate::stream::datagram::{Datagrams, EarlyData};
use crate::stream::pool::BufferPool;
use crate::stream::{NoSource, StreamSource, Streams};

/// Everything a connection borrows or is handed: the buffer pool, the stream table and the shared loss average.
pub struct Resources<'a, S: StreamSource, const N: usize, const C: usize> {
    /// The pool every buffer of the connection is charged to.
    pub pool: BufferPool<'a>,
    /// The stream table, created with `Config::new(is_client)` of the stream layer.
    pub streams: &'a mut Streams<S, N, C>,
    /// The node-wide loss average that decides tail repair.
    pub loss: &'a LossEstimate,
}

/// Where the connection is in its life.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Phase {
    Handshaking,
    Connected,
    Closing,
    Draining,
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
    streams: &'a mut Streams<S, N, C>,
    loss: &'a LossEstimate,
    dgrams: Datagrams,
    ext: Datagrams<16, 4>,
    early: EarlyData,
    hs: Handshake,
    est: Option<Established>,
    keys: Keys<P>,
    rec: Recovery<F>,
    rx: ReceivedPackets<64>,
    ctl: Ctl,
    cids: Cids,
    paths: Paths<NP>,
    events: EvQueue,
    life: Life,
    stats: Stats,
    next_pn: u64,
    started: u64,
    migrate_to: Option<usize>,
    highest_nonprobing: Option<u64>,
    odcid: ConnId,
    resumed: bool,
    confirmed: bool,
    ext_release: bool,
    paced_until: Option<u64>,
    degraded_told: bool,
}

impl<'a, P, S, const N: usize, const C: usize, const F: usize, const NP: usize> Connection<'a, P, S, N, C, F, NP>
where
    P: Provider,
    S: StreamSource,
{
    fn base(
        client: bool,
        cfg: Config,
        res: Resources<'a, S, N, C>,
        machine: Machine,
        first_cid: ConnId,
        odcid: ConnId,
        now: u64,
    ) -> Self {
        let Resources { pool, streams, loss } = res;
        let hs = Handshake::new(machine, now, cfg.thin, cfg.remembered_rtt);
        let mut life = Life::new(now);
        life.keepalive = cfg.keepalive;
        let c = Self {
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
            keys: Keys::new(),
            rec: Recovery::new(u64::from(MIN_MTU)),
            rx: ReceivedPackets::new(),
            ctl: Ctl::new(),
            cids: Cids::new(first_cid),
            paths: Paths::new(),
            events: EvQueue::new(),
            life,
            stats: Stats::default(),
            next_pn: 0,
            started: now,
            migrate_to: None,
            highest_nonprobing: None,
            odcid,
            resumed: false,
            confirmed: false,
            ext_release: false,
            paced_until: None,
            degraded_told: false,
        };
        c.streams.set_peer_limits(&cfg.peer_limits);
        c
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
    /// A [`Failure`] if the parameters are invalid (an over-long token, a connection id length outside 1 to 20) or
    /// the random generator refuses.
    pub fn client(
        cfg: Config,
        params: ClientParams<'_>,
        res: Resources<'a, S, N, C>,
        env: &mut Env<'_, P>,
    ) -> Result<Self, Failure> {
        let cid = Self::random_cid(env, cfg.cid_len)?;
        let odcid = Self::random_cid(env, 8)?;
        let init = Initiator::new(
            env,
            InitiatorParams {
                peer: params.peer,
                alpn: params.alpn,
                scid: cid,
                identity: params.identity,
                prekey: params.prekey,
                peer_has_prekey: params.peer_has_prekey,
                token: params.token,
                ticket: params.ticket,
            },
        )?;
        let mut c = Self::base(true, cfg, res, Machine::Client(init), cid, odcid, env.now);
        c.new_path_slot(params.path, params.path_info, env.now);
        if let Some(p) = c.paths.active_mut() {
            p.state = path::PathState::Validated;
            p.amp.validate();
        }
        c.pump(env);
        Ok(c)
    }

    /// Accept a connection. The first datagram of the client goes to
    /// [`handle_datagram`](Self::handle_datagram), which tells the connection its path.
    ///
    /// # Errors
    /// A [`Failure`] if the connection id length is outside 1 to 20 or the random generator refuses.
    pub fn server(
        cfg: Config,
        params: &ServerParams,
        res: Resources<'a, S, N, C>,
        env: &mut Env<'_, P>,
    ) -> Result<Self, Failure> {
        let cid = Self::random_cid(env, cfg.cid_len)?;
        let odcid = ConnId::default();
        let mut rc = ResponderConfig::new(params.identity, cid, params.alpns);
        rc.tickets_per_session = params.tickets_per_session;
        rc.ticket_lifetime_s = params.ticket_lifetime_s;
        Ok(Self::base(
            false,
            cfg,
            res,
            Machine::Server(Responder::new(rc)),
            cid,
            odcid,
            env.now,
        ))
    }

    /// Whether the handshake completed and the connection is open.
    pub const fn is_connected(&self) -> bool {
        matches!(self.phase, Phase::Connected)
    }

    /// Whether the connection ended: closed, or draining and no longer sending.
    pub const fn is_closed(&self) -> bool {
        matches!(self.phase, Phase::Closed | Phase::Draining)
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

    fn push(&mut self, ev: Ev) {
        self.events.push(ev);
    }
}
