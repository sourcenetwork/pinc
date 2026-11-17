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
//! The bytes of a response stay where the endpoint received them: the verifier reads them in place (the endpoint hands
//! out borrowed slices, also of bytes that arrived beyond a hole) and releases them as it verifies, so the node copies
//! nothing. Write-through: bytes beyond a hole are reported to the fetch, which asks the provider for range proofs
//! (extension frames), and a provider that sees bytes lost sends proofs ahead of the retransmission, so the groups
//! behind a lost packet verify without waiting for it. The stream id in a proof frame is the endpoint's stream id,
//! which both ends share; the layer's own handle for a stream is local to the node.
//!
//! Invariants: every table is bounded, the provider table by the providers in use; only bytes the fetcher verified reach the store; a fetch that finished leaves
//! no stream behind; a served response slot is freed when the response is acknowledged.

use alloc::boxed::Box;
use alloc::vec::Vec;

use vinc_core::{Command, SessionId};
use vinc_membership::NodeId;
use vinc_transport::stream::{RecvStatus, StreamId};
use vinc_values::fetch::{Fetch, FetchSpec, In, Io as FetchIo, StartError};
use vinc_values::knobs::MAX_PROVIDERS;
use vinc_values::server::{Server, ServerIn};
use vinc_values::session::{Inbound, OpenError, Outbound, PeerInfo, Provider, Session};
use vinc_values::source::ValueSource;
use vinc_values::store::ValueRead;
use vinc_values::trace::{Event as VEvent, Out, Trace};

use crate::apps::{Apps, ServeSource};
use crate::config::{Nanos, Store};
use crate::ep::Ep;
use crate::event::NodeEvent;
use crate::io::Io;
use crate::layer::Layer;
use crate::node::Node;
use crate::trace::{Body, NodeTrace, tag};
use crate::values_frames::{AHEAD_RUNS, EXT_MAX, head_sid, new_parts, stored_runs, with_sid};
use crate::values_net::{Net, Owner, Pace};
use crate::values_types::{FETCHES, ValuesError, ValuesRequest, ValuesStats};

/// The most requests the server holds at once.
const SERVERS: usize = 32;

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
    pub(crate) net: Net,
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

impl<E: Ep, St: Store> VSess<'_, E, St> {
    /// The endpoint's session and stream of a layer stream.
    fn real(&self, stream: StreamId) -> Option<(SessionId, StreamId)> {
        self.net.streams.get(&stream).map(|s| (s.session, s.stream))
    }
}

impl<E: Ep, St: Store> Session for VSess<'_, E, St> {
    fn visit<F: FnMut(&[u8]) -> usize>(&mut self, stream: StreamId, from: u64, mut f: F) {
        let Some((session, real)) = self.real(stream) else {
            return;
        };
        let mut at = from;
        while let Some(piece) = self.io.ep.read_at(session, real, at).filter(|p| !p.is_empty()) {
            let n = f(piece);
            at = at.saturating_add(n as u64);
            if n < piece.len() {
                break;
            }
        }
    }

    fn has(&self, stream: StreamId, from: u64, len: u64) -> bool {
        let Some((session, real)) = self.real(stream) else {
            return false;
        };
        let (mut at, end) = (from, from.saturating_add(len));
        while at < end {
            let Some(piece) = self.io.ep.read_at(session, real, at).filter(|p| !p.is_empty()) else {
                return false;
            };
            at = at.saturating_add(piece.len() as u64);
        }
        true
    }

    fn consume(&mut self, stream: StreamId, upto: u64) {
        let Some((session, real)) = self.real(stream) else {
            return;
        };
        let Some(s) = self.net.streams.get_mut(&stream) else {
            return;
        };
        let mut want = upto.saturating_sub(s.base);
        while want > 0 {
            let Some(n) = self
                .io
                .ep
                .read_chunk(session, real)
                .map(|c| c.len().min(usize::try_from(want).unwrap_or(usize::MAX)))
                .filter(|n| *n > 0)
            else {
                break;
            };
            let Some(st) = self.io.consume(session, real, n) else {
                break;
            };
            s.ended |= st == RecvStatus::Finished;
            s.base += n as u64;
            want -= n as u64;
        }
    }

    fn write(&mut self, stream: StreamId, data: &[u8], fin: bool) -> bool {
        let Some((session, real)) = self.real(stream) else {
            return false;
        };
        self.io.write(session, real, data) && (!fin || self.io.finish(session, real))
    }

    fn reset(&mut self, stream: StreamId, code: u64) {
        self.abandon(stream, code);
    }

    fn send_ext(&mut self, stream: StreamId, ty: u64, body: &[u8]) -> bool {
        let Some((session, real)) = self.real(stream) else {
            return false;
        };
        let mut out = [0u8; EXT_MAX];
        let Some(n) = with_sid(body, real, &mut out) else {
            return false;
        };
        let Some(frame) = out.get(..n) else { return false };
        self.io
            .cmd(Command::SendExtension {
                session,
                ty,
                body: frame,
            })
            .is_ok()
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

    fn open_stream(&mut self, provider: Provider, urgency: u8) -> Result<StreamId, OpenError> {
        let peer = self.net.peer_of(provider).ok_or(OpenError::NotConnected)?;
        let session = *self
            .io
            .lout
            .get(&(Layer::Values, peer))
            .ok_or(OpenError::NotConnected)?;
        let real = self.io.open_stream_at(session, urgency).ok_or(OpenError::Busy)?;
        if let Some(lid) = self.net.add_for(session, real, self.owner, provider) {
            Ok(lid)
        } else {
            self.io.drop_strm(session, real);
            Err(OpenError::Busy)
        }
    }

    fn peer_info(&self, provider: Provider) -> Option<PeerInfo> {
        let peer = self.net.peer_of(provider)?;
        let session = *self.io.lout.get(&(Layer::Values, peer))?;
        let st = self.io.ep.stats(session)?;
        Some(PeerInfo {
            rtt_ns: (st.transport.srtt > 0).then_some(st.transport.srtt),
            pto: st.pto_count > 0,
            last_rx: st.heard.max(st.heard_any),
        })
    }
}

impl<H: ValueRead, E: Ep, St: Store> Inbound<H> for VSess<'_, E, St>
where
    E::Src: ServeSource<H>,
{
    fn provided(&self, root: &[u8; 32]) -> bool {
        self.net.provided.contains(root)
    }

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
        let provs = v
            .net
            .acquire_all(req.providers.get(..MAX_PROVIDERS).unwrap_or(req.providers))?;
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
        if let Err(e) = fetch.start(&mut env, now, &spec) {
            v.net.release_all(&provs);
            return Err(match e {
                StartError::Busy => ValuesError::Busy,
                StartError::TooManyRanges => ValuesError::TooManyRanges,
                StartError::OutOfBounds => ValuesError::OutOfBounds,
            });
        }
        self.io.trace(NodeTrace::ValuesFetch {
            fetch: u64::from(fid),
            providers: provs.len() as u64,
        });
        if fetch.is_done() {
            v.net.release_all(&provs);
        } else {
            v.fetches.push((fid, fetch));
            v.net.begin_fetch(fid, provs);
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
        v.net.end_fetch(fetch);
        self.io.trace(NodeTrace::ValuesCancel {
            fetch: u64::from(fetch),
        });
        true
    }

    /// How many fetches are running.
    pub fn values_running(&self) -> usize {
        self.vals.as_deref().map_or(0, |v| v.fetches.len())
    }

    /// The providers in use and the fetches refused at the provider limit; zero while the layer is off.
    pub fn values_stats(&self) -> ValuesStats {
        self.vals.as_deref().map_or_else(ValuesStats::default, |v| ValuesStats {
            providers_in_use: v.net.in_use(),
            providers_refused: v.net.refused(),
        })
    }

    // ---------------------------------------------------------------- the node's events

    /// A session of the values protocol came up.
    pub(crate) fn values_up(&mut self, now: Nanos, session: SessionId, peer: &NodeId, incoming: bool) {
        if incoming {
            self.supersede(now, session, peer);
        } else if let Some(prov) = self.vals.as_deref().and_then(|v| v.net.lookup(peer)) {
            self.fetches_in(now, &In::Connected(prov));
        }
    }

    /// SUPERSEDE: a peer that dials again supersedes its older incoming values session, which would keep resending
    /// bytes the peer already holds. The sessions this node dialed are not touched.
    fn supersede(&mut self, now: Nanos, session: SessionId, peer: &NodeId) {
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
            let _ = self.io.cmd(Command::Close { session: sid, error: 0 });
            self.io.trace(NodeTrace::ValuesSuperseded { peer: tag(peer) });
        }
    }

    /// A dial for the values protocol failed.
    pub(crate) fn values_failed(&mut self, now: Nanos, peer: &NodeId) {
        // Only a running fetch refers to a provider whose dial failed, and it holds the provider.
        let Some(prov) = self.vals.as_deref().and_then(|v| v.net.lookup(peer)) else {
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
        // A provider nothing uses any more has no fetch and no served request to tell.
        let Some(prov) = self.vals.as_deref().and_then(|v| v.net.lookup(peer)) else {
            return;
        };
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
        let Some(prov) = v.net.acquire(&peer) else {
            return;
        };
        let Some(lid) = v.net.add(session, stream, Owner::Serve, prov) else {
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
        let owner = s.owner;
        let Owner::Fetch(fid) = owner else {
            self.server_in(now, &ServerIn::Readable(lid));
            return;
        };
        let (contig, runs, n) = stored_runs(&self.io.ep, session, stream, s.base);
        let added = contig.saturating_sub(s.seen.max(s.base));
        s.seen = s.seen.max(contig);
        let mut fresh = [(0u64, 0u64); AHEAD_RUNS * 4];
        let fresh_n = new_parts(runs.get(..n).unwrap_or_default(), &s.ahead, &mut fresh);
        s.ahead = [(0, 0); AHEAD_RUNS];
        for (d, r) in s.ahead.iter_mut().zip(runs.iter().take(n)) {
            *d = *r;
        }
        if added > 0 {
            self.fetch_in(
                now,
                fid,
                &In::Readable {
                    stream: lid,
                    bytes: usize::try_from(added).unwrap_or(usize::MAX),
                },
            );
        }
        for (off, end) in fresh.iter().take(fresh_n) {
            self.fetch_in(
                now,
                fid,
                &In::Ahead {
                    stream: lid,
                    offset: *off,
                    len: end - off,
                },
            );
        }
        self.announce_end(now, session, stream, lid);
    }

    /// Tell the fetch a stream ended, once the end arrived and the value layer released every byte before it.
    fn announce_end(&mut self, now: Nanos, session: SessionId, real: StreamId, lid: u64) {
        let Some(v) = self.vals.as_deref_mut() else {
            return;
        };
        let Some(s) = v.net.streams.get_mut(&lid) else {
            return;
        };
        let Owner::Fetch(fid) = s.owner else { return };
        if s.announced {
            return;
        }
        if !s.ended && self.io.consume(session, real, 0) != Some(RecvStatus::Finished) {
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
            Owner::Fetch(fid) => self.fetch_in(
                now,
                fid,
                &In::Reset {
                    stream: lid,
                    code: error,
                },
            ),
            Owner::Serve => self.server_in(now, &ServerIn::Reset(lid)),
        }
    }

    // ---------------------------------------------------------------- frames and pacing

    /// What the endpoint holds for the layer: the range-proof frames that arrived, and the sending state of the
    /// responses being served (a response fully acknowledged frees its slot; bytes found lost make the server send
    /// proofs ahead of the retransmission). True if anything was fed to the layer.
    pub(crate) fn values_step(&mut self, now: Nanos) -> bool {
        if self.vals.is_none() {
            return false;
        }
        let a = self.values_extensions(now);
        let b = self.values_pacing(now);
        a | b
    }

    /// Route the extension frames the endpoint holds to the stream they name.
    fn values_extensions(&mut self, now: Nanos) -> bool {
        let mut did = false;
        let mut buf = [0u8; vinc_core::EXT_BODY_MAX];
        while let Ok(Some((session, ty, len))) = self.io.ep.read_extension(&mut buf) {
            did = true;
            let Some(body) = buf.get(..len) else { continue };
            if self.io.lsess.get(&session).map(|s| s.layer) != Some(Layer::Values) {
                continue;
            }
            let Some(v) = self.vals.as_deref() else { continue };
            let Some(lid) = head_sid(body).and_then(|real| v.net.by_real.get(&(session, real)).copied()) else {
                continue;
            };
            let Some(owner) = v.net.streams.get(&lid).map(|s| s.owner) else {
                continue;
            };
            let mut local = [0u8; EXT_MAX];
            let Some(frame) = with_sid(body, lid, &mut local).and_then(|n| local.get(..n)) else {
                continue;
            };
            match owner {
                Owner::Fetch(fid) => self.fetch_in(now, fid, &In::Ext { ty, body: frame }),
                Owner::Serve => self.server_in(now, &ServerIn::Ext { ty, body: frame }),
            }
        }
        did
    }

    /// Tell the server how each served response is going, and free the ones the peer fully acknowledged.
    fn values_pacing(&mut self, now: Nanos) -> bool {
        let Some(v) = self.vals.as_deref() else {
            return false;
        };
        if v.net.served.is_empty() {
            return false;
        }
        let mut lids = [0u64; SERVERS];
        let mut n = 0;
        for (d, l) in lids.iter_mut().zip(v.net.served.iter()) {
            *d = *l;
            n += 1;
        }
        let mut did = false;
        for lid in lids.iter().take(n) {
            let Some(v) = self.vals.as_deref_mut() else { break };
            let Some(s) = v.net.streams.get_mut(lid) else {
                v.net.served.retain(|x| x != lid);
                continue;
            };
            let (session, real, pace) = (s.session, s.stream, s.pace);
            let state = self.io.ep.send_state(session, real);
            if state.is_none_or(|st| st.done) {
                did = true;
                self.server_in(now, &ServerIn::Done(*lid));
                if let Some(v) = self.vals.as_deref_mut() {
                    v.net.drop_stream(*lid);
                }
                self.io.drop_strm(session, real);
                continue;
            }
            let Some(st) = state else { continue };
            let ev = if st.lost.is_some() && st.lost != pace.lost {
                st.lost.map(|offset| ServerIn::Loss {
                    stream: *lid,
                    offset,
                    sent: st.sent,
                    window: st.window,
                })
            } else if st.sent > pace.sent {
                Some(ServerIn::Sent {
                    stream: *lid,
                    sent: st.sent,
                    window: st.window,
                })
            } else {
                None
            };
            if let Some(s) = self.vals.as_deref_mut().and_then(|v| v.net.streams.get_mut(lid)) {
                s.pace = Pace {
                    sent: st.sent,
                    lost: st.lost,
                };
            }
            if let Some(ev) = ev {
                did = true;
                self.server_in(now, &ev);
            }
        }
        did
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
        let Values { fetches, net, .. } = v;
        fetches.retain(|(fid, f)| {
            let done = f.is_done();
            if done {
                net.end_fetch(*fid);
            }
            !done
        });
    }
}
