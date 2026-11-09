//! Values over real sessions: the fetcher and the server of `vinc-values`, joined to the node's sessions.
//!
//! A fetch asks up to four providers, by node id, for the ranges of a value it lacks; the fetcher stripes, steals,
//! evicts a provider whose bytes fail verification, holds the first granule back and redials a stalled provider (all of
//! `vinc-values`). A provider answers a request stream with a response read from the host's store at the moment a
//! packet is built (the endpoint's stream source), so serving buffers nothing.
//!
//! The values protocol rides sessions of its own (protocol id [`VALUES_ALPN`](crate::VALUES_ALPN)). A fetch uses the
//! session this node dialed to a provider; a peer's requests arrive on any session. A peer that dials again supersedes
//! its older incoming session (it restarted, or lost the session and would keep receiving bytes it already holds), and
//! a newer request for bytes an older response from the same peer is still sending supersedes that response; the
//! second rule is the server's, the first is here.
//!
//! The endpoint hands the node the in-order bytes of a stream only, so the node keeps what the verifier has not
//! released in a buffer of its own per stream, and the out-of-order write-through of range proofs is not used: a lost
//! packet delays the groups behind it until its retransmission.
//!
//! Invariants: every table is bounded; a stream buffer never exceeds [`STREAM_CAP`]; only bytes the fetcher verified
//! reach the store; a fetch that finished leaves no stream behind.

use alloc::boxed::Box;
use alloc::collections::{BTreeMap, VecDeque};
use alloc::vec::Vec;
use core::fmt;

use vinc_core::{Command, SessionId};
use vinc_membership::NodeId;
use vinc_transport::stream::{RecvStatus, StreamId};
use vinc_values::fetch::{Fetch, FetchSpec, In, Io as FetchIo, StartError};
use vinc_values::knobs::MAX_PROVIDERS;
use vinc_values::server::{Server, ServerIn};
use vinc_values::session::{Inbound, OpenError, Outbound, PeerInfo, Provider, Session};
use vinc_values::source::ValueSource;
use vinc_values::span::Span;
use vinc_values::store::ValueRead;
use vinc_values::trace::{Event as VEvent, Out, Trace};

use crate::apps::{Apps, ServeSource};
use crate::config::{Nanos, Store, TABLE_MAX};
use crate::ep::Ep;
use crate::event::NodeEvent;
use crate::io::Io;
use crate::layer::Layer;
use crate::node::Node;
use crate::trace::{Body, NodeTrace, tag};

/// The most fetches running at once.
pub const FETCHES: usize = 8;
/// The most requests the server holds at once.
const SERVERS: usize = 32;
/// The most bytes a stream's receive buffer holds before the stream is reset.
const STREAM_CAP: usize = 4 << 20;
/// The reset code of a stream that overflowed its buffer.
const OVERFLOW: u64 = 5;

/// What a fetch is asked to get.
#[derive(Debug, Clone, Copy)]
pub struct ValuesRequest<'a> {
    /// The root of the value.
    pub root: [u8; 32],
    /// The value length in bytes.
    pub length: u64,
    /// The byte ranges wanted; empty means the whole value.
    pub ranges: &'a [Span],
    /// The providers, by node id; the first four count.
    pub providers: &'a [NodeId],
    /// The node time after which the fetch fails, if any.
    pub deadline: Option<Nanos>,
}

/// Why a fetch could not start or be found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValuesError {
    /// The host did not enable the values layer.
    Off,
    /// [`FETCHES`] fetches are running.
    Busy,
    /// More than 32 ranges were asked for.
    TooManyRanges,
    /// A range runs past the end of the value.
    OutOfBounds,
    /// The provider table is full.
    Providers,
}

impl fmt::Display for ValuesError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Off => "the values layer is not enabled on this node",
            Self::Busy => "too many fetches are running",
            Self::TooManyRanges => "a fetch takes at most 32 ranges",
            Self::OutOfBounds => "a range runs past the end of the value",
            Self::Providers => "too many providers are known to this node",
        })
    }
}

impl core::error::Error for ValuesError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Owner {
    Fetch(u32),
    Serve,
}

/// A stream of the values protocol and the bytes the value layer has not released.
#[derive(Debug)]
struct VStream {
    session: SessionId,
    stream: StreamId,
    owner: Owner,
    buf: Vec<u8>,
    /// The absolute stream offset of `buf[0]`.
    base: u64,
    /// The absolute offset of the end of the stream, once its end arrived.
    fin: Option<u64>,
    announced: bool,
}

/// The streams of the layer, found by a node-wide number (the value layer's stream handle) or by session and stream.
#[derive(Debug, Default)]
pub(crate) struct Net {
    streams: BTreeMap<u64, VStream>,
    by_real: BTreeMap<(SessionId, StreamId), u64>,
    next: u64,
    provs: Vec<NodeId>,
    served: VecDeque<u64>,
}

impl Net {
    fn provider(&mut self, peer: &NodeId) -> Option<Provider> {
        let i = match self.provs.iter().position(|p| p == peer) {
            Some(i) => i,
            None if self.provs.len() < TABLE_MAX => {
                self.provs.push(*peer);
                self.provs.len() - 1
            }
            None => return None,
        };
        u32::try_from(i).ok().map(Provider)
    }

    fn peer_of(&self, p: Provider) -> Option<NodeId> {
        self.provs.get(p.0 as usize).copied()
    }

    fn add(&mut self, session: SessionId, stream: StreamId, owner: Owner) -> Option<u64> {
        if self.streams.len() >= TABLE_MAX {
            return None;
        }
        self.next += 1;
        let lid = self.next;
        self.streams.insert(
            lid,
            VStream {
                session,
                stream,
                owner,
                buf: Vec::new(),
                base: 0,
                fin: None,
                announced: false,
            },
        );
        self.by_real.insert((session, stream), lid);
        Some(lid)
    }

    fn drop_stream(&mut self, lid: u64) -> Option<VStream> {
        let s = self.streams.remove(&lid)?;
        self.by_real.remove(&(s.session, s.stream));
        self.served.retain(|x| *x != lid);
        Some(s)
    }

    fn of_session(&self, session: SessionId) -> Vec<u64> {
        self.streams
            .iter()
            .filter(|(_, s)| s.session == session)
            .map(|(lid, _)| *lid)
            .collect()
    }
}

/// The events and traces a fetcher or the server reported during one call, taken out after it.
#[derive(Debug, Default)]
pub(crate) struct Sink {
    fetch: u32,
    trace_on: bool,
    events: Vec<(u32, VEvent)>,
    traces: Vec<(u32, Nanos, Trace)>,
}

impl Out for Sink {
    fn event(&mut self, _now: u64, ev: VEvent) {
        self.events.push((self.fetch, ev));
    }

    fn trace(&mut self, now: u64, t: Trace) {
        if self.trace_on {
            self.traces.push((self.fetch, now, t));
        }
    }
}

/// The state of the values layer: the server, the running fetches and the streams.
pub(crate) struct Values<H: ValueRead + Clone> {
    server: Server<H, SERVERS>,
    fetches: Vec<(u32, Box<Fetch>)>,
    next_fetch: u32,
    net: Net,
    sink: Sink,
}

impl<H: ValueRead + Clone> Values<H> {
    pub(crate) fn new(store: H, trace: bool) -> Self {
        Self {
            server: Server::new(store),
            fetches: Vec::with_capacity(FETCHES),
            next_fetch: 0,
            net: Net::default(),
            sink: Sink {
                trace_on: trace,
                ..Sink::default()
            },
        }
    }
}

/// The session the value layer sees: the node's streams of the values protocol.
pub(crate) struct VSess<'a, E: Ep, St: Store> {
    io: &'a mut Io<E, St>,
    net: &'a mut Net,
    owner: Owner,
}

impl<E: Ep, St: Store> VSess<'_, E, St> {
    /// Abandon a stream in both directions and forget it.
    fn abandon(&mut self, lid: u64, code: u64) {
        let Some(s) = self.net.drop_stream(lid) else {
            return;
        };
        let (session, stream) = (s.session, s.stream);
        // A refused reset leaves the stream to the peer's reset or the session's end.
        let _ = self.io.cmd(Command::Reset {
            session,
            stream,
            error: code,
        });
        let _ = self.io.cmd(Command::StopSending {
            session,
            stream,
            error: code,
        });
        self.io.drop_strm(session, stream);
    }
}

impl<E: Ep, St: Store> Session for VSess<'_, E, St> {
    fn visit<F: FnMut(&[u8]) -> usize>(&mut self, stream: StreamId, from: u64, mut f: F) {
        let Some(s) = self.net.streams.get(&stream) else {
            return;
        };
        let Some(rel) = from.checked_sub(s.base).and_then(|r| usize::try_from(r).ok()) else {
            return;
        };
        if let Some(rest) = s.buf.get(rel..).filter(|r| !r.is_empty()) {
            f(rest);
        }
    }

    fn has(&self, stream: StreamId, from: u64, len: u64) -> bool {
        self.net
            .streams
            .get(&stream)
            .is_some_and(|s| from >= s.base && from.saturating_add(len) <= s.base + s.buf.len() as u64)
    }

    fn consume(&mut self, stream: StreamId, upto: u64) {
        let Some(s) = self.net.streams.get_mut(&stream) else {
            return;
        };
        let n = usize::try_from(upto.saturating_sub(s.base)).map_or(s.buf.len(), |n| n.min(s.buf.len()));
        s.buf.drain(..n);
        s.base += n as u64;
    }

    fn write(&mut self, stream: StreamId, data: &[u8], fin: bool) -> bool {
        let Some((session, real)) = self.net.streams.get(&stream).map(|s| (s.session, s.stream)) else {
            return false;
        };
        self.io.write(session, real, data) && (!fin || self.io.finish(session, real))
    }

    fn reset(&mut self, stream: StreamId, code: u64) {
        self.abandon(stream, code);
    }

    // vertexia: the endpoint has no command for a range-proof frame, so write-through is off and a lost packet
    // delays the groups behind it; a `send_extension` command on the endpoint turns it on.
    fn send_ext(&mut self, _stream: StreamId, _ty: u64, _body: &[u8]) -> bool {
        false
    }
}

impl<E: Ep, St: Store> Outbound for VSess<'_, E, St> {
    fn is_connected(&self, provider: Provider) -> bool {
        self.net
            .peer_of(provider)
            .is_some_and(|peer| self.io.lout.contains_key(&(Layer::Values, peer)))
    }

    fn dial(&mut self, provider: Provider) {
        let Some(peer) = self.net.peer_of(provider) else {
            return;
        };
        let key = (Layer::Values, peer);
        if !self.io.lconn.contains(&key) && !self.io.ldials.contains(&key) {
            self.io.ldials.push(key);
        }
    }

    fn hangup(&mut self, provider: Provider) {
        let Some(peer) = self.net.peer_of(provider) else {
            return;
        };
        if let Some(session) = self.io.lout.remove(&(Layer::Values, peer)) {
            let _ = self.io.cmd(Command::Close { session, error: 0 });
        }
    }

    // vertexia: the endpoint has no stream urgency command, so every request stream runs at its default urgency;
    // the second class of the reference needs that command.
    fn open_stream(&mut self, provider: Provider, _urgency: u8) -> Result<StreamId, OpenError> {
        let peer = self.net.peer_of(provider).ok_or(OpenError::NotConnected)?;
        let session = *self
            .io
            .lout
            .get(&(Layer::Values, peer))
            .ok_or(OpenError::NotConnected)?;
        let real = self.io.open_stream(session).ok_or(OpenError::Busy)?;
        match self.net.add(session, real, self.owner) {
            Some(lid) => Ok(lid),
            None => {
                self.io.drop_strm(session, real);
                Err(OpenError::Busy)
            }
        }
    }

    fn peer_info(&self, provider: Provider) -> Option<PeerInfo> {
        let peer = self.net.peer_of(provider)?;
        let session = *self.io.lout.get(&(Layer::Values, peer))?;
        let st = self.io.ep.stats(session)?;
        let seen = self.io.rx_seen.get(&session).map_or(0, |e| e.1);
        Some(PeerInfo {
            rtt_ns: (st.transport.srtt > 0).then_some(st.transport.srtt),
            pto: st.pto_count > 0,
            last_rx: st.heard.max(seen),
        })
    }
}

impl<H: ValueRead, E: Ep, St: Store> Inbound<H> for VSess<'_, E, St>
where
    E::Src: ServeSource<H>,
{
    fn serve(&mut self, stream: StreamId, source: ValueSource<H>, len: u64) -> bool {
        let Some((session, real)) = self.net.streams.get(&stream).map(|s| (s.session, s.stream)) else {
            return false;
        };
        let Some(source) = <E::Src as ServeSource<H>>::from_source(source) else {
            return false;
        };
        let ok = self
            .io
            .cmd(Command::WriteSource {
                session,
                stream: real,
                source,
                len,
            })
            .is_ok();
        if ok {
            self.net.served.push_back(stream);
        }
        ok
    }
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

    /// Start fetching a value from the providers named; the progress comes out of [`Node::poll_event`] as
    /// [`NodeEvent::ValueReadable`], then [`NodeEvent::ValueComplete`] or [`NodeEvent::ValueFailed`]. Bytes the store
    /// has verified are not asked for again, so a fetch after a restart resumes where the store stands.
    ///
    /// # Errors
    /// [`ValuesError`] for a layer that is off, too many fetches or providers, or a bad range; nothing started.
    pub fn values_fetch(&mut self, now: Nanos, req: &ValuesRequest<'_>) -> Result<u32, ValuesError> {
        self.begin(now);
        let r = self.start_fetch(now, req);
        self.settle(now);
        r
    }

    fn start_fetch(&mut self, now: Nanos, req: &ValuesRequest<'_>) -> Result<u32, ValuesError> {
        let Some(v) = self.vals.as_deref_mut() else {
            return Err(ValuesError::Off);
        };
        if v.fetches.len() >= FETCHES {
            return Err(ValuesError::Busy);
        }
        let mut provs: Vec<Provider> = Vec::with_capacity(MAX_PROVIDERS);
        for peer in req.providers.iter().take(MAX_PROVIDERS) {
            provs.push(v.net.provider(peer).ok_or(ValuesError::Providers)?);
        }
        v.next_fetch = v.next_fetch.wrapping_add(1);
        let fid = v.next_fetch;
        let mut fetch = Box::new(Fetch::new());
        v.sink.fetch = fid;
        let spec = FetchSpec {
            root: req.root,
            length: req.length,
            ranges: req.ranges,
            providers: &provs,
            deadline: req.deadline,
        };
        let mut se = VSess {
            io: &mut self.io,
            net: &mut v.net,
            owner: Owner::Fetch(fid),
        };
        let mut env = FetchIo {
            session: &mut se,
            store: self.apps.values(),
            out: &mut v.sink,
        };
        match fetch.start(&mut env, now, &spec) {
            Ok(()) => {}
            Err(StartError::Busy) => return Err(ValuesError::Busy),
            Err(StartError::TooManyRanges) => return Err(ValuesError::TooManyRanges),
            Err(StartError::OutOfBounds) => return Err(ValuesError::OutOfBounds),
        }
        self.io.trace(NodeTrace::ValuesFetch {
            fetch: u64::from(fid),
            providers: provs.len() as u64,
        });
        if !fetch.is_done() {
            v.fetches.push((fid, fetch));
        }
        self.values_drain();
        Ok(fid)
    }

    /// Stop a fetch: its streams are abandoned and it reports nothing more. False if no such fetch runs.
    pub fn values_cancel(&mut self, now: Nanos, fetch: u32) -> bool {
        self.begin(now);
        let found = self.cancel_fetch(fetch);
        self.settle(now);
        found
    }

    fn cancel_fetch(&mut self, fetch: u32) -> bool {
        let Some(v) = self.vals.as_deref_mut() else {
            return false;
        };
        let Some(i) = v.fetches.iter().position(|(id, _)| *id == fetch) else {
            return false;
        };
        v.fetches.remove(i);
        let owned: Vec<u64> = v
            .net
            .streams
            .iter()
            .filter(|(_, s)| s.owner == Owner::Fetch(fetch))
            .map(|(lid, _)| *lid)
            .collect();
        let mut se = VSess {
            io: &mut self.io,
            net: &mut v.net,
            owner: Owner::Serve,
        };
        for lid in owned {
            se.abandon(lid, 0);
        }
        self.io.trace(NodeTrace::ValuesCancel {
            fetch: u64::from(fetch),
        });
        true
    }

    /// How many fetches are running.
    pub fn values_running(&self) -> usize {
        self.vals.as_deref().map_or(0, |v| v.fetches.len())
    }

    // ---------------------------------------------------------------- the node's events

    /// A session of the values protocol came up.
    pub(crate) fn values_up(&mut self, now: Nanos, session: SessionId, peer: &NodeId, incoming: bool) {
        let Some(prov) = self.vals.as_deref_mut().and_then(|v| v.net.provider(peer)) else {
            return;
        };
        if incoming {
            self.supersede(now, session, peer, prov);
        } else {
            self.fetches_in(now, &In::Connected(prov));
        }
    }

    /// SUPERSEDE: a peer that dials again supersedes its older incoming values session, which would keep resending
    /// bytes the peer already holds. The sessions this node dialed are not touched.
    fn supersede(&mut self, now: Nanos, session: SessionId, peer: &NodeId, _prov: Provider) {
        let old: Vec<SessionId> = self
            .io
            .lsess
            .iter()
            .filter(|(sid, s)| s.layer == Layer::Values && s.peer == *peer && s.incoming && **sid != session)
            .map(|(sid, _)| *sid)
            .collect();
        for sid in old {
            let lids = self.vals.as_deref().map(|v| v.net.of_session(sid)).unwrap_or_default();
            for lid in lids {
                self.server_in(now, &ServerIn::Reset(lid));
                if let Some(v) = self.vals.as_deref_mut() {
                    v.net.drop_stream(lid);
                }
            }
            let _ = self.io.cmd(Command::Close {
                session: sid,
                error: 0,
            });
            self.io.trace(NodeTrace::ValuesSuperseded { peer: tag(peer) });
        }
    }

    /// A dial for the values protocol failed.
    pub(crate) fn values_failed(&mut self, now: Nanos, peer: &NodeId) {
        let Some(prov) = self.vals.as_deref_mut().and_then(|v| v.net.provider(peer)) else {
            return;
        };
        self.fetches_in(now, &In::ConnectFailed(prov));
    }

    /// A session of the values protocol ended; `ours` says this node dialed it.
    pub(crate) fn values_down(&mut self, now: Nanos, session: SessionId, peer: &NodeId, ours: bool) {
        let Some(v) = self.vals.as_deref_mut() else {
            return;
        };
        let lids = v.net.of_session(session);
        let prov = v.net.provider(peer);
        let more = self
            .io
            .lsess
            .values()
            .any(|s| s.layer == Layer::Values && s.peer == *peer);
        for lid in lids {
            let serve = self
                .vals
                .as_deref()
                .and_then(|v| v.net.streams.get(&lid))
                .is_some_and(|s| s.owner == Owner::Serve);
            if serve {
                self.server_in(now, &ServerIn::Reset(lid));
            }
            if let Some(v) = self.vals.as_deref_mut() {
                v.net.drop_stream(lid);
            }
        }
        let Some(prov) = prov else { return };
        if !more {
            self.server_in(now, &ServerIn::Closed(prov));
        }
        if ours {
            self.fetches_in(now, &In::Closed(prov));
        }
    }

    /// The peer opened a stream on a session of the values protocol: it is a request.
    pub(crate) fn values_stream_opened(&mut self, now: Nanos, session: SessionId, stream: StreamId) {
        let Some(peer) = self.io.lsess.get(&session).map(|s| s.peer) else {
            return;
        };
        let Some(v) = self.vals.as_deref_mut() else {
            return;
        };
        if v.net.by_real.contains_key(&(session, stream)) {
            return;
        }
        let Some(prov) = v.net.provider(&peer) else {
            return;
        };
        // The endpoint tells us nothing when a response is fully acknowledged, so a full server recycles its oldest
        // response: the response itself goes on in the endpoint, only the bookkeeping for proofs and for superseding
        // it is dropped.
        if v.server.held() >= SERVERS
            && let Some(old) = v.net.served.pop_front()
        {
            self.server_in(now, &ServerIn::Done(old));
            if let Some(v) = self.vals.as_deref_mut() {
                v.net.drop_stream(old);
            }
        }
        let Some(v) = self.vals.as_deref_mut() else {
            return;
        };
        let Some(lid) = v.net.add(session, stream, Owner::Serve) else {
            let _ = self.io.cmd(Command::Reset {
                session,
                stream,
                error: vinc_values::knobs::code::BUSY,
            });
            return;
        };
        self.server_in(
            now,
            &ServerIn::Opened {
                stream: lid,
                peer: prov,
            },
        );
    }

    /// Bytes or the end arrived on a stream of the values protocol.
    pub(crate) fn values_readable(&mut self, now: Nanos, session: SessionId, stream: StreamId) {
        let known = self
            .vals
            .as_deref()
            .is_some_and(|v| v.net.by_real.contains_key(&(session, stream)));
        if !known {
            self.values_stream_opened(now, session, stream);
        }
        let Some(v) = self.vals.as_deref_mut() else {
            return;
        };
        let Some(lid) = v.net.by_real.get(&(session, stream)).copied() else {
            return;
        };
        let Some(s) = v.net.streams.get_mut(&lid) else {
            return;
        };
        let before = s.buf.len();
        let (status, over) = self.io.drain_stream(session, stream, &mut s.buf, STREAM_CAP);
        let added = s.buf.len() - before;
        if status == RecvStatus::Finished {
            s.fin = Some(s.base + s.buf.len() as u64);
        }
        let owner = s.owner;
        if over {
            let mut se = VSess {
                io: &mut self.io,
                net: &mut v.net,
                owner,
            };
            se.abandon(lid, OVERFLOW);
            if let Owner::Fetch(fid) = owner {
                self.fetch_in(now, fid, &In::Reset {
                    stream: lid,
                    code: OVERFLOW,
                });
            } else {
                self.server_in(now, &ServerIn::Reset(lid));
            }
            return;
        }
        match owner {
            Owner::Serve => self.server_in(now, &ServerIn::Readable(lid)),
            Owner::Fetch(fid) => {
                if added > 0 {
                    self.fetch_in(
                        now,
                        fid,
                        &In::Readable {
                            stream: lid,
                            bytes: added,
                        },
                    );
                }
                self.announce_end(now, lid);
            }
        }
    }

    /// Tell the fetch a stream ended, once the end arrived and the value layer released every byte before it.
    fn announce_end(&mut self, now: Nanos, lid: u64) {
        let Some(v) = self.vals.as_deref_mut() else {
            return;
        };
        let Some(s) = v.net.streams.get_mut(&lid) else {
            return;
        };
        let Owner::Fetch(fid) = s.owner else { return };
        if s.announced || s.fin.is_none_or(|end| s.base < end) {
            return;
        }
        s.announced = true;
        self.fetch_in(now, fid, &In::Finished(lid));
        if let Some(v) = self.vals.as_deref_mut()
            && let Some(s) = v.net.drop_stream(lid)
        {
            self.io.drop_strm(s.session, s.stream);
        }
    }

    /// The peer reset a stream of the values protocol, or asked this side to stop sending on it.
    pub(crate) fn values_stream_gone(&mut self, now: Nanos, session: SessionId, stream: StreamId, error: u64) {
        let Some(v) = self.vals.as_deref_mut() else {
            return;
        };
        let Some(lid) = v.net.by_real.get(&(session, stream)).copied() else {
            return;
        };
        let Some(s) = v.net.drop_stream(lid) else {
            return;
        };
        match s.owner {
            Owner::Fetch(fid) => self.fetch_in(now, fid, &In::Reset { stream: lid, code: error }),
            Owner::Serve => self.server_in(now, &ServerIn::Reset(lid)),
        }
    }

    // ---------------------------------------------------------------- timers

    /// Run the fetches whose timers are due.
    pub(crate) fn values_timeout(&mut self, now: Nanos) {
        let Some(v) = self.vals.as_deref() else {
            return;
        };
        let due: Vec<u32> = v
            .fetches
            .iter()
            .filter(|(_, f)| f.poll_timeout().is_some_and(|t| t <= now))
            .map(|(id, _)| *id)
            .collect();
        for fid in due {
            self.with_fetch(fid, |f, env| f.on_timeout(env, now));
        }
        self.values_drain();
    }

    /// When the earliest fetch timer is due.
    pub(crate) fn values_deadline(&self) -> Option<Nanos> {
        self.vals
            .as_deref()
            .and_then(|v| v.fetches.iter().filter_map(|(_, f)| f.poll_timeout()).min())
    }

    // ---------------------------------------------------------------- plumbing

    /// Run `f` on fetch `fid` with the node's session, the host's store and the event sink.
    fn with_fetch<T>(
        &mut self,
        fid: u32,
        f: impl FnOnce(&mut Fetch, &mut FetchIo<'_, VSess<'_, E, St>, A::Values, Sink>) -> T,
    ) -> Option<T> {
        let v = self.vals.as_deref_mut()?;
        let i = v.fetches.iter().position(|(id, _)| *id == fid)?;
        let (_, fetch) = v.fetches.get_mut(i)?;
        v.sink.fetch = fid;
        let mut se = VSess {
            io: &mut self.io,
            net: &mut v.net,
            owner: Owner::Fetch(fid),
        };
        let mut env = FetchIo {
            session: &mut se,
            store: self.apps.values(),
            out: &mut v.sink,
        };
        Some(f(fetch, &mut env))
    }

    /// Feed one input to a fetch.
    fn fetch_in(&mut self, now: Nanos, fid: u32, ev: &In<'_>) {
        self.with_fetch(fid, |f, env| f.on_event(env, now, ev));
        self.values_drain();
    }

    /// Feed one session input to every running fetch.
    fn fetches_in(&mut self, now: Nanos, ev: &In<'_>) {
        let ids: Vec<u32> = self
            .vals
            .as_deref()
            .map(|v| v.fetches.iter().map(|(id, _)| *id).collect())
            .unwrap_or_default();
        for fid in ids {
            self.fetch_in(now, fid, ev);
        }
    }

    /// Feed one input to the server.
    fn server_in(&mut self, now: Nanos, ev: &ServerIn<'_>) {
        let Some(v) = self.vals.as_deref_mut() else {
            return;
        };
        let Values { server, net, sink, .. } = v;
        sink.fetch = 0;
        let mut se = VSess {
            io: &mut self.io,
            net,
            owner: Owner::Serve,
        };
        server.on_event(&mut se, sink, now, ev);
        self.values_drain();
    }

    /// Take the events and traces the last call reported, and drop the fetches that finished.
    fn values_drain(&mut self) {
        let Some(v) = self.vals.as_deref_mut() else {
            return;
        };
        for (fid, now, t) in v.sink.traces.drain(..) {
            self.io.tq.push(now, Body::Values(fid, t));
        }
        for (fetch, ev) in v.sink.events.drain(..) {
            self.io.emit(match ev {
                VEvent::Readable { off, len } => NodeEvent::ValueReadable { fetch, off, len },
                VEvent::Complete => NodeEvent::ValueComplete { fetch },
                VEvent::Failed(reason) => NodeEvent::ValueFailed { fetch, reason },
            });
        }
        v.fetches.retain(|(_, f)| !f.is_done());
    }
}
