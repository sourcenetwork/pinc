//! Delay-tolerant delivery over real sessions: creating a bundle, handing copies to the peers met, taking custody.
//!
//! The node composes the pieces of `vinc-dtn` with the host's bundle store and clock. A bundle is created here
//! ([`Node::dtn_send`]), charged to the ledger as custody and held by the forwarder with its copy budget. Whenever a
//! peer is in contact (a session of the delay-tolerant protocol is up and the host's rule allows it) the forwarder
//! hands half of the copies to it (binary spray and wait), or the bundle itself if the peer is the destination. A
//! hand-over is a transfer on one stream: the holder offers the signed head, the receiver asks for the symbols it
//! lacks, the holder sends them with range proofs, the receiver checks every symbol against the signed root, and when
//! the bundle is whole it takes custody and writes a signed acknowledgement; the holder, once acknowledged, is
//! relieved of custody (if the receiver ranks above it) and stops retransmitting. Retransmission timers count only the
//! time a link is up, and a bundle ends at its expiry by the wall clock.
//!
//! Receiving charges the ledger the full size of the bundle before a byte arrives, so a node never holds more than
//! the host's budget, partial bundles included. A partial bundle outlives a broken stream: the next offer resumes it.
//!
//! Invariants: copies are conserved (the forwarder's); custody leaves a node only by a valid acknowledgement from
//! the node it was offered to, by delivery, or by expiry; a symbol enters a buffer only after it hashed to the signed
//! root; every table is bounded; the ledger's used bytes never exceed the host's budget.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;
use core::fmt;

use vinc_core::{Command, SessionId};
use vinc_crypto::NodeId as FullId;
use vinc_crypto::Secret;
use vinc_dag::ranges::VerifiedRanges;
use vinc_dtn::DtnError as DtnLibError;
use vinc_dtn::bundle::{Outgoing, Plan, Reception, seal_bundle, serve, serve_len};
use vinc_dtn::custody::{CustodyAck, CustodyBook, Incoming};
use vinc_dtn::forward::{Action, Forwarder, Held, Input, Policy};
use vinc_dtn::head::{BundleId, Erasure, SignedHead};
use vinc_dtn::hlc::Hlc;
use vinc_dtn::layout::SliceLayout;
use vinc_dtn::seal::{RecipientKeys, SealSeeds, decapsulate};
use vinc_dtn::store::{Class, Key, Ledger, Space};
use vinc_membership::NodeId;
use vinc_transport::stream::StreamId;

use crate::apps::{Apps, DtnApp, ServeSource};
use crate::config::{Nanos, Store};
use crate::dtn_wire::{self as wire, Refusal};
use crate::ep::Ep;
use crate::event::NodeEvent;
use crate::layer::Layer;
use crate::node::Node;
use crate::trace::{NodeTrace, btag, tag};

/// The most bundles held (as custody or in transit) at once.
pub const BUNDLES: usize = 32;
/// The most bundle ledger entries, partial receptions included.
const LEDGER: usize = 64;
/// The most transfer streams open at once.
const STREAMS: usize = 64;
/// The most disjoint intervals a partial reception tracks.
const INTERVALS: usize = 64;
/// The bytes of symbols one request asks for.
const CHUNK_BYTES: u64 = 64 << 10;
/// The wall-clock interval of the expiry and contact sweep while the node holds bundles.
const TICK_MS: u64 = 1000;

type Fwd = Forwarder<BUNDLES, 32, 64, 64>;
type Book = CustodyBook<BUNDLES>;
type Led = Ledger<LEDGER>;

/// How a bundle is cut and how long it lives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DtnPlan {
    /// The lifetime in milliseconds from creation.
    pub lifetime_ms: u64,
    /// The copy budget of spray and wait.
    pub copies: u16,
    /// Data symbols per erasure block.
    pub k: u8,
    /// Parity symbols per erasure block.
    pub m: u8,
    /// The slice size log, 0 to 4: slices of 1 KiB to 16 KiB.
    pub slice_log: u8,
}

/// Why a bundle could not be created.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DtnSendError {
    /// The host did not enable delay-tolerant delivery.
    Off,
    /// The host gave no key to sign with.
    NoSigner,
    /// The node's entropy source failed.
    Entropy,
    /// The parameters or the payload are not valid, or sealing failed.
    Seal(DtnLibError),
    /// The ledger or the store has no room for the bundle.
    NoRoom,
}

impl fmt::Display for DtnSendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Off => f.write_str("delay-tolerant delivery is not enabled on this node"),
            Self::NoSigner => f.write_str("the host gave no key to sign bundles with"),
            Self::Entropy => f.write_str("the entropy source failed"),
            Self::Seal(e) => write!(f, "the bundle could not be sealed: {e:?}"),
            Self::NoRoom => f.write_str("no room for the bundle without dropping custody"),
        }
    }
}

impl core::error::Error for DtnSendError {}

/// A bundle being received: the verified symbols so far.
pub(crate) struct Partial {
    signed: SignedHead,
    sealed: Vec<u8>,
    outboard: Vec<u8>,
    have: VerifiedRanges<INTERVALS>,
    /// The index of the first data symbol that may still be missing.
    cursor: u64,
}

/// Which side of a transfer a stream is.
enum Role {
    /// This node offered the bundle.
    Sender { bundle: BundleId, peer: NodeId },
    /// A peer offered a bundle; `rx` is set once the offer was taken.
    Receiver { rx: Option<RxCtx> },
}

/// What a receiving stream knows of its transfer.
#[derive(Clone, Copy)]
struct RxCtx {
    bundle: BundleId,
    from: FullId,
    copies: u16,
    offer: u64,
    ask: Option<(u64, u64)>,
}

/// A transfer stream and the bytes read from it and not yet parsed.
pub(crate) struct DStream {
    role: Role,
    inb: Vec<u8>,
}

/// The state of the delay-tolerant layer.
pub(crate) struct Dtn {
    fwd: Fwd,
    book: Book,
    led: Led,
    hlc: Hlc,
    heads: BTreeMap<BundleId, SignedHead>,
    offers: BTreeMap<(NodeId, BundleId), u64>,
    confirmed: BTreeSet<BundleId>,
    received: BTreeMap<BundleId, u64>,
    partials: BTreeMap<BundleId, Partial>,
    streams: BTreeMap<(SessionId, StreamId), DStream>,
    next_tick: u64,
    tx: Vec<u8>,
}

impl Dtn {
    pub(crate) fn new(policy: Policy, budget: u64, wall_ms: u64) -> Self {
        Self {
            fwd: Fwd::new(policy, wall_ms),
            book: Book::new(),
            led: Led::new(budget),
            hlc: Hlc::new(wall_ms, 0),
            heads: BTreeMap::new(),
            offers: BTreeMap::new(),
            confirmed: BTreeSet::new(),
            received: BTreeMap::new(),
            partials: BTreeMap::new(),
            streams: BTreeMap::new(),
            next_tick: wall_ms,
            tx: Vec::new(),
        }
    }

    fn has_work(&self) -> bool {
        !self.heads.is_empty() || !self.partials.is_empty()
    }

    /// Forget a bundle everywhere: heads, partial reception, offers, the forwarder and the host's store.
    fn forget<P: vinc_crypto::Provider>(&mut self, app: &mut impl DtnApp<P>, wall: u64, id: &BundleId) -> bool {
        let held = self.heads.remove(id).is_some();
        self.partials.remove(id);
        self.confirmed.remove(id);
        self.offers.retain(|(_, b), _| b != id);
        // The forwarder may not know it (a partial reception): nothing to forget then.
        let _ = self.fwd.step(wall, Input::Forget(*id));
        app.remove(id);
        held
    }

    /// The first run of data symbols not yet held, at most `CHUNK_BYTES` of them.
    fn want(layout: &SliceLayout, p: &mut Partial) -> Option<(u64, u64)> {
        let g = layout.slice_len();
        let held = |s: u64| p.have.contains_range(s * g..(s + 1) * g);
        let total = layout.data_symbols();
        let mut d = p.cursor;
        let first = loop {
            if d >= total {
                p.cursor = total;
                return None;
            }
            let s = layout.data_symbol(d)?;
            if !held(s) {
                break s;
            }
            d += 1;
        };
        p.cursor = d;
        let max = (CHUNK_BYTES / g).max(1);
        let mut end = first + 1;
        let mut n = d + 1;
        while end - first < max && n < total && layout.data_symbol(n) == Some(end) && !held(end) {
            end += 1;
            n += 1;
        }
        Some((first, end))
    }
}

/// Why a frame handler gave up on its stream.
enum Stop {
    /// A protocol break: reset the stream, say nothing.
    Break,
    /// Refuse the bundle: tell the holder why, then end the stream.
    Refuse(BundleId, Refusal),
    /// The transfer is over: end the stream.
    Done,
}

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: vinc_crypto::Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: ServeSource<A::Values>,
{
    // ---------------------------------------------------------------- the host's commands

    /// Create a bundle for `to` carrying `payload`, and start handing out its copies. Returns the bundle id. The
    /// events of its life come out of [`Node::poll_event`]: [`NodeEvent::DtnHandedOff`] when a peer relieves this node
    /// of custody, [`NodeEvent::DtnDelivered`] when the destination acknowledges it, [`NodeEvent::DtnExpired`] when
    /// it ends undelivered.
    ///
    /// # Errors
    /// [`DtnSendError`]; nothing was created.
    pub fn dtn_send(
        &mut self,
        now: Nanos,
        to: &RecipientKeys,
        payload: &[u8],
        plan: &DtnPlan,
    ) -> Result<[u8; 32], DtnSendError> {
        self.begin(now);
        let r = self.create_bundle(to, payload, plan);
        self.settle(now);
        r
    }

    fn create_bundle(&mut self, to: &RecipientKeys, payload: &[u8], plan: &DtnPlan) -> Result<[u8; 32], DtnSendError> {
        let wall = self.io.wall_ms();
        let me = self.ident;
        let Some(d) = self.dtn.as_deref_mut() else {
            return Err(DtnSendError::Off);
        };
        let mut seeds = ([0u8; 32], [0u8; 32]);
        self.drbg.fill(&mut seeds.0).map_err(|_| DtnSendError::Entropy)?;
        self.drbg.fill(&mut seeds.1).map_err(|_| DtnSendError::Entropy)?;
        let seeds = SealSeeds {
            eph_x25519: Secret::new(seeds.0),
            kem_m: Secret::new(seeds.1),
        };
        let layout = SliceLayout::new(plan.k, plan.m, plan.slice_log, payload.len() as u64).map_err(DtnSendError::Seal)?;
        let total = layout.total_len();
        let (Ok(sealed_len), Ok(outboard_len)) = (
            usize::try_from(total),
            layout.outboard_len().map_err(DtnSendError::Seal).and_then(|n| usize::try_from(n).map_err(|_| DtnSendError::NoRoom)),
        ) else {
            return Err(DtnSendError::NoRoom);
        };
        if total > d.led.budget() {
            return Err(DtnSendError::NoRoom);
        }
        let created = d.hlc.tick(wall);
        let out = Outgoing {
            recipient: to,
            plan: Plan {
                created,
                lifetime_ms: plan.lifetime_ms,
                copies: plan.copies,
                erasure: Erasure { k: plan.k, m: plan.m },
                slice_log: plan.slice_log,
            },
            seeds: &seeds,
        };
        let mut sealed = alloc::vec![0u8; sealed_len];
        let mut outboard = alloc::vec![0u8; outboard_len];
        let signer = self.apps.dtn().signer().ok_or(DtnSendError::NoSigner)?;
        let signed = seal_bundle(&self.prov, signer, &out, payload, &mut sealed, &mut outboard)
            .map_err(DtnSendError::Seal)?;
        d.hlc = created;
        let head = *signed.head();
        let id = head.id;
        let expires = head.expires_at();
        let mut evicted: Vec<Key> = Vec::new();
        d.book
            .accept(
                &mut d.led,
                Incoming {
                    bundle: id,
                    bytes: total,
                    expires,
                    previous: me,
                    offer: 0,
                },
                wall,
                |e| evicted.push(e.key),
            )
            .map_err(|_| DtnSendError::NoRoom)?;
        let app = self.apps.dtn();
        for k in &evicted {
            if k.space == Space::DTN {
                d.forget(app, wall, &BundleId(k.id));
            }
        }
        if !app.put(&id, &sealed, &outboard) {
            let _ = d.book.delivered(&mut d.led, &id);
            return Err(DtnSendError::NoRoom);
        }
        let held = Held {
            id,
            destination: head.destination,
            expires,
            copies: plan.copies,
        };
        if d.fwd.step(wall, Input::Hold(held)).is_err() {
            let _ = d.book.delivered(&mut d.led, &id);
            app.remove(&id);
            return Err(DtnSendError::NoRoom);
        }
        d.heads.insert(id, signed);
        self.io.trace(NodeTrace::DtnCreated {
            bundle: btag(&id.0),
            copies: u64::from(plan.copies),
        });
        Ok(id.0)
    }

    /// How many bundles this node holds, as custody or in transit.
    pub fn dtn_held(&self) -> usize {
        self.dtn.as_deref().map_or(0, |d| d.heads.len())
    }

    // ---------------------------------------------------------------- sessions

    /// A session of the delay-tolerant protocol came up: if the host's rule allows the contact, the link is up.
    pub(crate) fn dtn_up(&mut self, _now: Nanos, _session: SessionId, peer: &NodeId, _incoming: bool) {
        let wall = self.io.wall_ms();
        let full = self.io.full_id(peer);
        if !self.apps.dtn().in_contact(&full, wall) {
            self.close_layer_sessions(Layer::Dtn, peer);
            return;
        }
        if let Some(d) = self.dtn.as_deref_mut() {
            // A full link table leaves the peer out of the forwarder's contacts; it is met again at the next session.
            let _ = d.fwd.step(wall, Input::LinkUp(full));
        }
    }

    /// A session of the delay-tolerant protocol ended: its transfers go, and the link goes down if it was the last.
    pub(crate) fn dtn_down(&mut self, _now: Nanos, session: SessionId, peer: &NodeId) {
        let wall = self.io.wall_ms();
        let full = self.io.full_id(peer);
        let last = self.layer_session(Layer::Dtn, peer).is_none();
        let Some(d) = self.dtn.as_deref_mut() else {
            return;
        };
        d.streams.retain(|(s, _), _| *s != session);
        if last {
            let _ = d.fwd.step(wall, Input::LinkDown(full));
        }
    }

    pub(crate) fn dtn_stream_opened(&mut self, session: SessionId, stream: StreamId) {
        let Some(d) = self.dtn.as_deref_mut() else {
            return;
        };
        if d.streams.contains_key(&(session, stream)) {
            return;
        }
        if d.streams.len() >= STREAMS {
            let _ = self.io.cmd(Command::Reset {
                session,
                stream,
                error: wire::Refusal::Busy as u64,
            });
            return;
        }
        self.io.register_stream(session, stream);
        d.streams.insert(
            (session, stream),
            DStream {
                role: Role::Receiver { rx: None },
                inb: Vec::new(),
            },
        );
    }

    pub(crate) fn dtn_stream_gone(&mut self, session: SessionId, stream: StreamId) {
        if let Some(d) = self.dtn.as_deref_mut() {
            d.streams.remove(&(session, stream));
        }
    }

    // ---------------------------------------------------------------- the clock

    /// Run the expiry and contact sweep if it is due.
    pub(crate) fn dtn_timeout(&mut self, now: Nanos) {
        let wall = self.io.wall_ms();
        let Some(d) = self.dtn.as_deref_mut() else {
            return;
        };
        if wall < d.next_tick {
            return;
        }
        d.next_tick = wall.saturating_add(TICK_MS);
        let _ = d.fwd.step(wall, Input::Tick);
        let mut evicted: Vec<Key> = Vec::new();
        d.book.expire(&mut d.led, wall, |e| evicted.push(e.key));
        d.received.retain(|_, exp| *exp > wall);
        let app = self.apps.dtn();
        let mut expired: Vec<BundleId> = Vec::new();
        for k in evicted.iter().filter(|k| k.space == Space::DTN) {
            let id = BundleId(k.id);
            if d.forget(app, wall, &id) {
                expired.push(id);
            }
        }
        for id in expired {
            self.io.trace(NodeTrace::DtnReleased {
                bundle: btag(&id.0),
                delivered: 0,
            });
            self.io.emit(NodeEvent::DtnExpired { bundle: id.0 });
        }
        self.dtn_contacts(now, wall);
    }

    /// Dial the peers in contact while bundles are held, and end the sessions of peers no longer in contact.
    fn dtn_contacts(&mut self, _now: Nanos, wall: u64) {
        let holding = self.dtn.as_deref().is_some_and(|d| !d.heads.is_empty());
        let peers: Vec<NodeId> = self
            .mem
            .members()
            .map(|(m, _)| *m)
            .filter(|m| *m != self.io.me && !self.io.is_hub_id(m))
            .collect();
        for peer in peers {
            let full = self.io.full_id(&peer);
            let contact = self.apps.dtn().in_contact(&full, wall);
            let has = self.layer_session(Layer::Dtn, &peer).is_some();
            if contact && !has && holding {
                let key = (Layer::Dtn, peer);
                if !self.io.lconn.contains(&key) && !self.io.ldials.contains(&key) {
                    self.io.ldials.push(key);
                }
            } else if !contact && has {
                if let Some(d) = self.dtn.as_deref_mut() {
                    let _ = d.fwd.step(wall, Input::LinkDown(full));
                }
                self.close_layer_sessions(Layer::Dtn, &peer);
            }
        }
    }

    /// When the sweep is next due (node time), while the node has anything to look after.
    pub(crate) fn dtn_deadline(&self) -> Option<Nanos> {
        let d = self.dtn.as_deref().filter(|d| d.has_work())?;
        let wait = d.next_tick.saturating_sub(self.io.wall_ms()).saturating_mul(1_000_000);
        Some(self.io.now.saturating_add(wait))
    }

    // ---------------------------------------------------------------- the holder

    /// Run what the forwarder decided: hand copies to the peers in contact, retransmit, release.
    pub(crate) fn dtn_step(&mut self, _now: Nanos) -> bool {
        let mut did = false;
        loop {
            let Some(d) = self.dtn.as_deref_mut() else {
                return did;
            };
            if d.heads.is_empty() {
                return did;
            }
            let Some(action) = d.fwd.poll() else {
                return did;
            };
            did = true;
            match action {
                Action::Send {
                    peer,
                    bundle,
                    copies,
                    retransmit,
                } => self.dtn_offer(peer, bundle, copies, retransmit),
                Action::Release(id) => self.dtn_release(&id),
            }
        }
    }

    /// A bundle ended here: delivered (the destination acknowledged it), or expired.
    fn dtn_release(&mut self, id: &BundleId) {
        let wall = self.io.wall_ms();
        let Some(d) = self.dtn.as_deref_mut() else {
            return;
        };
        let delivered = d.confirmed.contains(id);
        // A delivered bundle's custody is released with it; an expired one's ledger entry goes at the sweep too.
        let _ = d.book.delivered(&mut d.led, id);
        let held = d.forget(self.apps.dtn(), wall, id);
        if held {
            self.io.trace(NodeTrace::DtnReleased {
                bundle: btag(&id.0),
                delivered: u64::from(delivered),
            });
            if !delivered {
                self.io.emit(NodeEvent::DtnExpired { bundle: id.0 });
            }
        }
    }

    /// Offer `bundle` to `peer` on a new stream.
    fn dtn_offer(&mut self, peer: FullId, bundle: BundleId, copies: u16, retransmit: bool) {
        let me = self.io.me;
        let Some(session) = self.layer_session(Layer::Dtn, &peer.bytes) else {
            return;
        };
        let Some(d) = self.dtn.as_deref_mut() else {
            return;
        };
        let Some(signed) = d.heads.get(&bundle) else {
            return;
        };
        let offer = if retransmit {
            d.offers.get(&(peer.bytes, bundle)).copied().unwrap_or(0)
        } else if copies > 0 && peer.bytes > me {
            // Custody moves only to a peer that ranks above this node, so it cannot circle back.
            match d.book.offer(&bundle, peer) {
                Ok(id) => {
                    d.offers.insert((peer.bytes, bundle), id);
                    id
                }
                Err(_) => 0,
            }
        } else {
            0
        };
        wire::start(&mut d.tx, wire::OFFER);
        d.tx.extend_from_slice(&copies.to_be_bytes());
        d.tx.extend_from_slice(&offer.to_be_bytes());
        let at = d.tx.len();
        d.tx.resize(at + signed.encoded_len(), 0);
        let Some(dst) = d.tx.get_mut(at..) else {
            return;
        };
        if signed.encode(dst).is_err() {
            return;
        }
        wire::finish(&mut d.tx);
        let Some(stream) = self.io.open_stream(session) else {
            return;
        };
        if d.streams.len() >= STREAMS || !self.io.write(session, stream, &d.tx) {
            self.io.drop_strm(session, stream);
            return;
        }
        d.streams.insert(
            (session, stream),
            DStream {
                role: Role::Sender {
                    bundle,
                    peer: peer.bytes,
                },
                inb: Vec::new(),
            },
        );
        self.io.trace(NodeTrace::DtnOffer {
            bundle: btag(&bundle.0),
            peer: tag(&peer.bytes),
            copies: u64::from(copies),
        });
    }

    // ---------------------------------------------------------------- frames

    /// Bytes arrived on a transfer stream: parse the whole frames and act on them.
    pub(crate) fn dtn_readable(&mut self, _now: Nanos, session: SessionId, stream: StreamId) {
        if !self
            .dtn
            .as_deref()
            .is_some_and(|d| d.streams.contains_key(&(session, stream)))
        {
            self.dtn_stream_opened(session, stream);
        }
        let Some(d) = self.dtn.as_deref_mut() else {
            return;
        };
        let Some(mut ds) = d.streams.remove(&(session, stream)) else {
            return;
        };
        let mut buf = core::mem::take(&mut ds.inb);
        let (_, over) = self.io.drain_stream(session, stream, &mut buf, wire::BODY_MAX * 2);
        let mut stop = if over { Some(Stop::Break) } else { None };
        let mut used = 0;
        while stop.is_none() {
            let rest = buf.get(used..).unwrap_or_default();
            let (ty, total) = match wire::next(rest) {
                Ok(Some(f)) => f,
                Ok(None) => break,
                Err(()) => {
                    stop = Some(Stop::Break);
                    break;
                }
            };
            let body = rest.get(wire::HDR..total).unwrap_or_default();
            stop = self.dtn_frame(session, stream, &mut ds, ty, body).err();
            used += total;
        }
        match stop {
            None => {
                buf.drain(..used);
                ds.inb = buf;
                if let Some(d) = self.dtn.as_deref_mut() {
                    d.streams.insert((session, stream), ds);
                }
            }
            Some(Stop::Break) => {
                let _ = self.io.cmd(Command::Reset {
                    session,
                    stream,
                    error: 1,
                });
                let _ = self.io.cmd(Command::StopSending {
                    session,
                    stream,
                    error: 1,
                });
                self.io.drop_strm(session, stream);
            }
            Some(Stop::Refuse(bundle, why)) => self.dtn_refuse(session, stream, &ds, &bundle, why),
            // The transfer is over; ending our half lets the stream close.
            Some(Stop::Done) => self.io.close_stream(session, stream),
        }
    }

    fn dtn_frame(
        &mut self,
        session: SessionId,
        stream: StreamId,
        ds: &mut DStream,
        ty: u8,
        body: &[u8],
    ) -> Result<(), Stop> {
        match &mut ds.role {
            Role::Sender { bundle, peer } => {
                let (bundle, peer) = (*bundle, *peer);
                match ty {
                    wire::WANT => self.dtn_serve(session, stream, &bundle, body),
                    wire::ACK => self.dtn_acked(&bundle, &peer, body),
                    wire::REFUSE => {
                        self.io.trace(NodeTrace::DtnRefused {
                            bundle: btag(&bundle.0),
                            peer: tag(&peer),
                            reason: u64::from(body.first().copied().unwrap_or(0)),
                        });
                        Err(Stop::Done)
                    }
                    _ => Err(Stop::Break),
                }
            }
            Role::Receiver { rx } => match (ty, rx.is_some()) {
                (wire::OFFER, false) => {
                    let ctx = self.dtn_offered(session, stream, body)?;
                    *rx = Some(ctx);
                    self.dtn_advance(session, stream, rx)
                }
                (wire::DATA, true) => self.dtn_data(session, stream, rx, body),
                _ => Err(Stop::Break),
            },
        }
    }

    /// The holder's side of a WANT: send the symbols asked for with their range proof.
    fn dtn_serve(&mut self, session: SessionId, stream: StreamId, bundle: &BundleId, body: &[u8]) -> Result<(), Stop> {
        let (Some((first, rest)), Some(d)) = (wire::take_u64(body), self.dtn.as_deref_mut()) else {
            return Err(Stop::Break);
        };
        let Some((end, _)) = wire::take_u64(rest) else {
            return Err(Stop::Break);
        };
        let Some(layout) = d.heads.get(bundle).and_then(|s| s.head().layout().ok()) else {
            return Err(Stop::Break);
        };
        let max = (CHUNK_BYTES / layout.slice_len()).max(1);
        if first >= end || end > layout.total_symbols() || end - first > max {
            return Err(Stop::Break);
        }
        let range = first..end;
        let Some((sealed, outboard)) = self.apps.dtn().get(bundle) else {
            return Err(Stop::Break);
        };
        let Ok(n) = serve_len(&layout, &range) else {
            return Err(Stop::Break);
        };
        wire::start(&mut d.tx, wire::DATA);
        d.tx.extend_from_slice(&first.to_be_bytes());
        d.tx.extend_from_slice(&end.to_be_bytes());
        let at = d.tx.len();
        d.tx.resize(at + n, 0);
        let Some(dst) = d.tx.get_mut(at..) else {
            return Err(Stop::Break);
        };
        if serve(&layout, sealed, outboard, &range, dst).is_err() {
            return Err(Stop::Break);
        }
        wire::finish(&mut d.tx);
        if self.io.write(session, stream, &d.tx) {
            Ok(())
        } else {
            Err(Stop::Break)
        }
    }

    /// The holder's side of an ACK: the receiver took the bundle.
    fn dtn_acked(&mut self, bundle: &BundleId, peer: &NodeId, body: &[u8]) -> Result<(), Stop> {
        let wall = self.io.wall_ms();
        let me = self.ident;
        let Some(d) = self.dtn.as_deref_mut() else {
            return Err(Stop::Break);
        };
        let Ok(ack) = CustodyAck::decode(body) else {
            return Err(Stop::Break);
        };
        if ack.verify().is_err()
            || ack.bundle != *bundle
            || ack.custodian.bytes != *peer
            || ack.previous.bytes != me.bytes
        {
            return Err(Stop::Break);
        }
        let _ = d.fwd.step(
            wall,
            Input::Acked {
                peer: ack.custodian,
                bundle: *bundle,
            },
        );
        let relieved = d.book.on_ack(&mut d.led, &ack).is_ok();
        let to_destination = d.heads.get(bundle).is_some_and(|s| s.head().destination == ack.custodian);
        if to_destination {
            d.confirmed.insert(*bundle);
        }
        self.io.trace(NodeTrace::DtnAcked {
            bundle: btag(&bundle.0),
            peer: tag(peer),
            relieved: u64::from(relieved),
        });
        if relieved {
            self.io.emit(NodeEvent::DtnHandedOff {
                bundle: bundle.0,
                to: *peer,
            });
        }
        if to_destination {
            self.io.emit(NodeEvent::DtnDelivered { bundle: bundle.0 });
        }
        Err(Stop::Done)
    }

    // ---------------------------------------------------------------- the receiver

    /// A holder offered a bundle: check it, charge it, and keep a place for its symbols.
    fn dtn_offered(&mut self, session: SessionId, stream: StreamId, body: &[u8]) -> Result<RxCtx, Stop> {
        let wall = self.io.wall_ms();
        let Some(peer) = self.io.lsess.get(&session).map(|s| s.peer) else {
            return Err(Stop::Break);
        };
        let from = self.io.full_id(&peer);
        let Some((copies, rest)) = wire::take_u16(body) else {
            return Err(Stop::Break);
        };
        let Some((offer, head)) = wire::take_u64(rest) else {
            return Err(Stop::Break);
        };
        let Ok(signed) = SignedHead::decode(head) else {
            return Err(Stop::Break);
        };
        let h = *signed.head();
        let id = h.id;
        let refuse = |why| Stop::Refuse(id, why);
        if signed.verify().is_err() {
            return Err(refuse(Refusal::Malformed));
        }
        if h.is_expired(wall) {
            return Err(refuse(Refusal::Expired));
        }
        let layout = h.layout().map_err(|_| refuse(Refusal::Malformed))?;
        let Some(d) = self.dtn.as_deref_mut() else {
            return Err(Stop::Break);
        };
        let ctx = RxCtx {
            bundle: id,
            from,
            copies,
            offer,
            ask: None,
        };
        // Already whole here: take custody again (a repeated offer or a hand-back) and acknowledge.
        if d.heads.contains_key(&id) || d.received.contains_key(&id) {
            return Err(self.dtn_complete(session, stream, &ctx, &signed, None));
        }
        if !d.partials.contains_key(&id) {
            let total = layout.total_len();
            let mut evicted: Vec<Key> = Vec::new();
            let admitted = d.led.admit(
                id.store_key(),
                total,
                Class::Transit,
                h.expires_at(),
                wall,
                |e| evicted.push(e.key),
            );
            let app = self.apps.dtn();
            for k in evicted.iter().filter(|k| k.space == Space::DTN) {
                d.forget(app, wall, &BundleId(k.id));
            }
            if admitted.is_err() {
                return Err(refuse(Refusal::NoRoom));
            }
            let sealed_len = usize::try_from(total).ok();
            let outboard_len = layout.outboard_len().ok().and_then(|n| usize::try_from(n).ok());
            let (Some(sealed_len), Some(outboard_len)) = (sealed_len, outboard_len) else {
                let _ = d.led.release(&id.store_key());
                return Err(refuse(Refusal::Malformed));
            };
            d.partials.insert(
                id,
                Partial {
                    signed,
                    sealed: alloc::vec![0; sealed_len],
                    outboard: alloc::vec![0; outboard_len],
                    have: VerifiedRanges::new(),
                    cursor: 0,
                },
            );
        }
        Ok(ctx)
    }

    /// Ask for the next run of symbols, or finish the bundle if every data symbol is held.
    fn dtn_advance(&mut self, session: SessionId, stream: StreamId, rx: &mut Option<RxCtx>) -> Result<(), Stop> {
        let Some(ctx) = rx.as_mut() else {
            return Err(Stop::Break);
        };
        let Some(d) = self.dtn.as_deref_mut() else {
            return Err(Stop::Break);
        };
        let Some(p) = d.partials.get_mut(&ctx.bundle) else {
            return Err(Stop::Break);
        };
        let Ok(layout) = p.signed.head().layout() else {
            return Err(Stop::Break);
        };
        if let Some((first, end)) = Dtn::want(&layout, p) {
            ctx.ask = Some((first, end));
            wire::start(&mut d.tx, wire::WANT);
            d.tx.extend_from_slice(&first.to_be_bytes());
            d.tx.extend_from_slice(&end.to_be_bytes());
            wire::finish(&mut d.tx);
            return if self.io.write(session, stream, &d.tx) {
                Ok(())
            } else {
                Err(Stop::Break)
            };
        }
        ctx.ask = None;
        let ctx = *ctx;
        Err(self.dtn_finish(session, stream, &ctx))
    }

    /// A DATA frame: the symbols asked for, with their proof.
    fn dtn_data(
        &mut self,
        session: SessionId,
        stream: StreamId,
        rx: &mut Option<RxCtx>,
        body: &[u8],
    ) -> Result<(), Stop> {
        let wall = self.io.wall_ms();
        let Some(ctx) = rx.as_mut() else {
            return Err(Stop::Break);
        };
        let id = ctx.bundle;
        let (Some((first, rest)), Some(d)) = (wire::take_u64(body), self.dtn.as_deref_mut()) else {
            return Err(Stop::Break);
        };
        let Some((end, proof)) = wire::take_u64(rest) else {
            return Err(Stop::Break);
        };
        if ctx.ask != Some((first, end)) {
            return Err(Stop::Break);
        }
        let Some(p) = d.partials.get_mut(&id) else {
            return Err(Stop::Break);
        };
        let have = core::mem::take(&mut p.have);
        let fed = match Reception::resume(&p.signed, &mut p.sealed, have, wall) {
            Ok(mut r) => {
                let res = r.feed(first..end, proof);
                let kept = r.have().clone();
                drop(r);
                p.have = kept;
                res
            }
            Err(e) => Err(e),
        };
        if let Err(e) = fed {
            return Err(Stop::Refuse(
                id,
                if e == DtnLibError::Expired {
                    Refusal::Expired
                } else {
                    Refusal::BadProof
                },
            ));
        }
        self.io.trace(NodeTrace::DtnSymbols {
            bundle: btag(&id.0),
            peer: tag(&ctx.from.bytes),
            first,
        });
        self.dtn_advance(session, stream, rx)
    }

    /// Every data symbol is held: rebuild the rest, check the root, and take the bundle in.
    fn dtn_finish(&mut self, session: SessionId, stream: StreamId, ctx: &RxCtx) -> Stop {
        let wall = self.io.wall_ms();
        let Some(d) = self.dtn.as_deref_mut() else {
            return Stop::Break;
        };
        let id = ctx.bundle;
        let Some(mut p) = d.partials.remove(&id) else {
            return Stop::Break;
        };
        let refuse = |why| Stop::Refuse(id, why);
        let signed = p.signed.clone();
        let Ok(layout) = signed.head().layout() else {
            let _ = d.led.release(&id.store_key());
            return refuse(Refusal::Malformed);
        };
        let have = core::mem::take(&mut p.have);
        let Ok(mut rx) = Reception::resume(&p.signed, &mut p.sealed, have, wall) else {
            let _ = d.led.release(&id.store_key());
            return refuse(Refusal::Expired);
        };
        let Ok(scratch_len) = rx.scratch_len() else {
            let _ = d.led.release(&id.store_key());
            return refuse(Refusal::Malformed);
        };
        let mut scratch = alloc::vec![0u8; scratch_len];
        if let Err(e) = rx.finish(&mut p.outboard, &mut scratch) {
            let _ = d.led.release(&id.store_key());
            return refuse(if e == DtnLibError::Inconsistent {
                Refusal::Inconsistent
            } else {
                Refusal::Malformed
            });
        }
        self.io.trace(NodeTrace::DtnComplete {
            bundle: btag(&id.0),
            peer: tag(&ctx.from.bytes),
        });
        if signed.head().destination.bytes == self.ident.bytes {
            // This node is the destination: open the payload.
            let Some(keys) = self.apps.dtn().recipient() else {
                let _ = d.led.release(&id.store_key());
                return refuse(Refusal::CannotOpen);
            };
            let opened = decapsulate(&self.prov, keys.own, keys.kem_dk, keys.x25519, signed.head()).and_then(|cipher| {
                let padded = usize::try_from(layout.padded_len()).map_err(|_| DtnLibError::Buffer)?;
                let mut out = alloc::vec![0u8; padded];
                let n = rx.open(&self.prov, &cipher, &mut out)?;
                out.truncate(n);
                Ok(out)
            });
            drop(rx);
            let _ = d.led.release(&id.store_key());
            let Ok(payload) = opened else {
                return refuse(Refusal::CannotOpen);
            };
            d.received.insert(id, signed.head().expires_at());
            self.io.emit(NodeEvent::DtnReceived {
                bundle: id.0,
                source: signed.head().source.bytes,
                payload,
            });
            return self.dtn_complete(session, stream, ctx, &signed, None);
        }
        drop(rx);
        if !self.apps.dtn().put(&id, &p.sealed, &p.outboard) {
            let _ = d.led.release(&id.store_key());
            return refuse(Refusal::NoRoom);
        }
        self.dtn_complete(session, stream, ctx, &signed, Some(layout.total_len()))
    }

    /// The bundle is here whole: take custody (a relay), hold the copies, and write the acknowledgement. `bytes` is
    /// the charge of a bundle that has just been stored; a bundle already held is acknowledged again. Returns how
    /// the transfer ends: [`Stop::Done`] after the acknowledgement was written.
    fn dtn_complete(
        &mut self,
        session: SessionId,
        stream: StreamId,
        ctx: &RxCtx,
        signed: &SignedHead,
        bytes: Option<u64>,
    ) -> Stop {
        let wall = self.io.wall_ms();
        let id = ctx.bundle;
        let h = *signed.head();
        let refuse = |why| Stop::Refuse(id, why);
        let to_me = h.destination.bytes == self.ident.bytes;
        let Some(d) = self.dtn.as_deref_mut() else {
            return Stop::Break;
        };
        d.hlc = d.hlc.tick(wall);
        let due = if to_me {
            None
        } else {
            let total = bytes.or_else(|| d.led.get(&id.store_key()).map(|e| e.bytes)).unwrap_or(0);
            let mut evicted: Vec<Key> = Vec::new();
            let accepted = d.book.accept(
                &mut d.led,
                Incoming {
                    bundle: id,
                    bytes: total,
                    expires: h.expires_at(),
                    previous: ctx.from,
                    offer: ctx.offer,
                },
                wall,
                |e| evicted.push(e.key),
            );
            for k in evicted.iter().filter(|k| k.space == Space::DTN && k.id != id.0) {
                d.forget(self.apps.dtn(), wall, &BundleId(k.id));
            }
            let Ok(due) = accepted else {
                self.apps.dtn().remove(&id);
                return refuse(Refusal::NoRoom);
            };
            // A repeated hold is ignored by the forwarder: the copies it would add are not new.
            let _ = d.fwd.step(
                wall,
                Input::Hold(Held {
                    id,
                    destination: h.destination,
                    expires: h.expires_at(),
                    copies: ctx.copies,
                }),
            );
            d.heads.entry(id).or_insert_with(|| signed.clone());
            Some(due)
        };
        let Some(signer) = self.apps.dtn().signer() else {
            return refuse(Refusal::NoSigner);
        };
        let ack = match due {
            Some(due) => due.sign(d.hlc, signer),
            None => CustodyAck::sign(id, ctx.from, ctx.offer, d.hlc, signer),
        };
        let Ok(ack) = ack else {
            return refuse(Refusal::NoSigner);
        };
        wire::start(&mut d.tx, wire::ACK);
        let at = d.tx.len();
        d.tx.resize(at + ack.encoded_len(), 0);
        let encoded = d.tx.get_mut(at..).is_some_and(|dst| ack.encode(dst).is_ok());
        wire::finish(&mut d.tx);
        if !encoded || !self.io.write(session, stream, &d.tx) {
            return Stop::Break;
        }
        self.io.trace(NodeTrace::DtnCustody {
            bundle: btag(&id.0),
            peer: tag(&ctx.from.bytes),
        });
        if !to_me {
            self.io.emit(NodeEvent::DtnCustody {
                bundle: id.0,
                from: ctx.from.bytes,
            });
        }
        Stop::Done
    }

    /// Tell the holder this bundle is refused, and end the transfer.
    fn dtn_refuse(&mut self, session: SessionId, stream: StreamId, ds: &DStream, bundle: &BundleId, why: Refusal) {
        let peer = match &ds.role {
            Role::Sender { peer, .. } => *peer,
            Role::Receiver { rx } => rx.as_ref().map_or([0; 32], |c| c.from.bytes),
        };
        self.io.trace(NodeTrace::DtnRefused {
            bundle: btag(&bundle.0),
            peer: tag(&peer),
            reason: why as u64,
        });
        let Some(d) = self.dtn.as_deref_mut() else {
            return;
        };
        wire::start(&mut d.tx, wire::REFUSE);
        d.tx.push(why as u8);
        wire::finish(&mut d.tx);
        let _ = self.io.write(session, stream, &d.tx);
        self.io.close_stream(session, stream);
    }
}
