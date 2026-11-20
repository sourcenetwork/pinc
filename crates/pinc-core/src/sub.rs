//! Sub-sessions: a second protocol to a connected peer at no cost in round trips.
//!
//! Dialing a peer that already has an established session with live keys opens a sub-session instead of a handshake.
//! The dialer picks two 4-byte connection ids `cc` and `cs`, derives the sub-session's keys from the parent's secrets
//! with those ids and the protocol name, reports `Connected` at once, and queues one sub-session open extension frame
//! (`alen alpn cc cs`) in the parent. The data it writes goes out in the next datagrams, so the peer sees the open and
//! the first bytes in the same flight. The peer derives the same keys from the frame, finds the protocol in its
//! registry and opens the matching session.
//!
//! The parent must have been heard from within [`PARENT_RX`]. One that went quiet may be a peer that restarted, so a
//! dial to it asks first (`QUIET_PROBE`): the dial's slot holds its memory and no connection, and the quiet session
//! sends one ping at once. As soon as any packet comes back the dial rides the session as a sub-session, with the id it
//! already gave the application. When the wait (two of the session's probe timeouts, or `EndpointConfig::probe_window`)
//! runs out unanswered, the dial makes its own handshake in the same slot, to the session's own direct address and then
//! the addresses the caller gave, and closes the quiet session when it is still the one probed and nothing was in
//! flight on it. While the probe runs the dial's id holds no session: a write on it fails at once, and closing it ends
//! the dial. At most [`MAX_WAITERS`] dials probe one session; past that a dial makes its own handshake.
//!
//! The extension frame is repeated by the transport until its packet is acknowledged, so the peer may see it twice;
//! the ids of the opens it accepted are remembered (1024 of them) and a repeat is ignored.
//!
//! Dialing a peer with a session for another protocol that is not yet allowed (its handshake still runs, or its access
//! check is open) opens a waiting sub-session instead: it reports `Connected` at once and takes writes, and gets its
//! keys, and its open goes out, when the parent is allowed. If the parent fails first, it closes as orphaned and the
//! application dials again.
//!
//! A sub-session that never heard its peer while its parent closes may never have been accepted (the parent died before
//! the frame arrived), so it is closed with its parent and the application dials again.
//!
//! Invariants: the keys of two sub-sessions differ whenever their ids or protocols differ; a sub-session is allowed
//! while its parent may release events (it is allowed and its peer's answer stands); an open whose ids are already used here, whose protocol is not in the registry or that finds no
//! free slot is dropped without effect.

use core::net::SocketAddr;

use pinc_crypto::NodeId;
use pinc_security::{Alpn, ConnId, Established, Failure};
use pinc_transport::conn::{Connection, PathId, PathInfo, SubOpen, SubWait, code};
use pinc_transport::frame::ext;

use crate::api::{CommandError, ConnectFailure, Event, SessionId};
use crate::endpoint::{CID_LEN, env, ep_impl, lent};
use crate::keepalive::Role;
use crate::slot::{NIL, State};

/// The most sub-sessions that wait for one parent.
const MAX_WAITERS: usize = 8;
/// The wait of a quiet-parent dial whose probed session has no probe timeout to take (never reached in practice:
/// a probed session always has a connection), and the fallback when a configured wait is zero.
const PROBE_WINDOW: u64 = 2_000_000_000;
/// The most sessions that have waiters at one time.
const MAX_WAITING_PARENTS: usize = 256;
/// How recently a parent must have been heard from to carry a sub-session, in nanoseconds.
pub(crate) const PARENT_RX: u64 = 20_000_000_000;
use crate::trace::trace;

ep_impl! {
    /// The established session of `peer` a new session can be opened over, if any: an allowed, live one with a path,
    /// heard from within [`PARENT_RX`], a root one first.
    pub(crate) fn find_parent(&self, peer: &NodeId, now: u64) -> Option<usize> {
        let live = |i: &usize| {
            self.slots.get(*i).is_some_and(|s| {
                s.m.state == State::Established
                    && s.m.allowed
                    && now.saturating_sub(s.m.last_rx) < PARENT_RX
                    && s.conn.as_ref().is_some_and(|c| c.is_connected() && c.session().is_some() && c.active_path().is_some())
            })
        };
        self.peer_sessions(peer)
            .filter(live)
            .min_by_key(|i| self.slots.get(*i).map_or(1, |s| u8::from(s.m.parent.is_some())))
    }

    /// The established session of `peer` a dial may probe (`QUIET_PROBE`): the same live session [`find_parent`]
    /// rides, only that it has not been heard from within [`PARENT_RX`]: a quiet parent. It may be a peer that went
    /// silent or restarted, so the dial first asks the session for a ping before it makes its own handshake. None
    /// once [`MAX_WAITERS`] dials probe it.
    pub(crate) fn find_quiet_parent(&self, peer: &NodeId, now: u64) -> Option<usize> {
        let live = |i: &usize| {
            self.slots.get(*i).is_some_and(|s| {
                s.m.state == State::Established
                    && s.m.allowed
                    && now.saturating_sub(s.m.last_rx) >= PARENT_RX
                    && s.conn.as_ref().is_some_and(|c| c.is_connected() && c.session().is_some() && c.active_path().is_some())
            })
        };
        self.peer_sessions(peer)
            .filter(live)
            .min_by_key(|i| self.slots.get(*i).map_or(1, |s| u8::from(s.m.parent.is_some())))
            // Past the waiter bound the dial makes its own handshake, as one past the waiting bounds does.
            .filter(|p| self.probes_of(*p).nth(MAX_WAITERS - 1).is_none())
    }

    fn random_cid(&mut self) -> Result<ConnId, CommandError> {
        for _ in 0..8 {
            let mut b = [0u8; CID_LEN];
            self.drbg.fill(&mut b).map_err(|_| CommandError::Failure(Failure::Randomness))?;
            if let Some(c) = ConnId::new(&b)
                && !self.demux.contains(&c)
            {
                return Ok(c);
            }
        }
        Err(CommandError::Failure(Failure::Randomness))
    }

    /// Open a sub-session over session `parent` towards `peer` for `alpn` and return it.
    // Out of line, as `free_slot`: a whole connection moves here.
    #[inline(never)]
    pub(crate) fn open_sub(
        &mut self,
        parent: usize,
        peer: NodeId,
        alpn: &[u8],
        role: Role,
        now: u64,
    ) -> Result<SessionId, CommandError> {
        let alpn = Alpn::new(alpn).ok_or(CommandError::BadAlpn)?;
        let parts = self.sub_parts(parent)?;
        let (child, mem) = self.alloc_slot(true, now).ok_or(CommandError::Full)?;
        self.open_sub_over(parent, child, mem, parts, peer, alpn, role, now)
    }

    /// What a sub-session over `parent` needs before a slot or its memory is taken: its two connection ids, the
    /// parent's session and its active path. Nothing is held when it fails.
    fn sub_parts(&mut self, parent: usize) -> Result<(ConnId, ConnId, Established, PathId), CommandError> {
        let cc = self.random_cid()?;
        let cs = self.random_cid()?;
        let conn = self.slots.get(parent).and_then(|s| s.conn.as_ref()).ok_or(CommandError::NoSession)?;
        let est = conn.session().ok_or(CommandError::NoSession)?.clone();
        Ok((cc, cs, est, conn.active_path().ok_or(CommandError::NoRoute)?))
    }

    /// Build the sub-session of slot `child` over `mem` to run over session `parent`, towards `peer` for `alpn`.
    /// This is the body [`open_sub`] shares with the ride of a quiet-parent probe, whose slot and memory already
    /// exist: the parent's session and path are named in the open, the child takes the parent's paths, and the open
    /// leaves in the parent ahead of anything the child sends.
    #[inline(never)]
    #[allow(clippy::too_many_arguments, reason = "the parent, child, their memory and the open's parts, named once")]
    fn open_sub_over(
        &mut self,
        parent: usize,
        child: usize,
        mem: pinc_transport::conn::Resources<'a, S, N, C, F>,
        (cc, cs, est, path): (ConnId, ConnId, Established, PathId),
        peer: NodeId,
        alpn: Alpn,
        role: Role,
        now: u64,
    ) -> Result<SessionId, CommandError> {
        let cfg = self.conn_config(Some(&peer));
        let open = SubOpen {
            client: true,
            parent: &est,
            alpn,
            cc,
            cs,
            identity: self.identity,
            path,
            path_info: PathInfo { interface_mtu: self.cfg.conn.interface_mtu, ..PathInfo::default() },
        };
        let mut env = env!(self, now);
        let conn = match Connection::sub_session(cfg, open, mem, &mut env) {
            Ok(c) => c,
            Err(e) => {
                self.retire_slot(child);
                return Err(CommandError::Failure(e));
            }
        };
        let pid = self.session_id(parent);
        if let Some(s) = self.slots.get_mut(child) {
            s.conn = Some(conn);
            s.m.peer = Some(peer);
            s.m.alpn = Some(alpn);
            s.m.parent = Some(pid);
            s.m.sub = true;
            s.m.role = role;
            // The slot may be a quiet-parent probe that rides: its probe ends here.
            s.m.probing = false;
        }
        self.follow_parent_paths(parent, child, now);
        self.sync_cids(child, true);
        self.sync_ack_every(child);
        // The open leaves in the parent ahead of anything the child sends.
        let queued = self.queue_sub_open(parent, alpn, cc, cs, now);
        trace!(self, now, Sub { step: 0, parent: parent as u64, child: child as u64 });
        self.settle(parent, now);
        self.settle(child, now);
        if queued {
            return Ok(self.session_id(child));
        }
        // The open could not be queued: the child would never be accepted. Undo it.
        if let Some(s) = self.slots.get_mut(child) {
            s.m.orphaned = true;
        }
        self.redial(child, now);
        Err(CommandError::NoSession)
    }

    /// Start the probe of a dial to a quiet parent (`QUIET_PROBE`): the dial's slot takes its memory back and holds no
    /// connection, nothing goes on the wire from the dial, and the application holds its id until the probe
    /// resolves. The probed session pings at once (its `probed_until` makes one due), so the probe learns whether
    /// the peer lives. The dial rides the parent when any packet comes back, else it lapses into its own handshake
    /// at `probe_until`: the window is `EndpointConfig::probe_window` when set, else two of the session's probe
    /// timeouts (its round trip plus margin, capped). `addrs` are the dial's routable addresses, kept for the lapse.
    // Out of line, as `free_slot`: a whole connection moves here.
    #[inline(never)]
    pub(crate) fn open_probe(
        &mut self,
        parent: usize,
        peer: NodeId,
        alpn: &[u8],
        addrs: [Option<SocketAddr>; NP],
        role: Role,
        now: u64,
    ) -> Result<SessionId, CommandError> {
        let alpn = Alpn::new(alpn).ok_or(CommandError::BadAlpn)?;
        let (i, mem) = self.alloc_slot(true, now).ok_or(CommandError::Full)?;
        // Nothing may be lost by closing the probed session on a lapse: it is quiet, so nothing of the
        // application's should be in flight on it; noted now, before the probe's own ping leaves, and checked
        // again when the probe resolves.
        let quiet = self
            .slots
            .get(parent)
            .and_then(|s| s.conn.as_ref())
            .is_some_and(|c| c.recovery().packets_in_flight() == 0);
        let pidx = u32::try_from(parent).unwrap_or(NIL);
        let pid = self.session_id(parent);
        let probed_gen = self.slots.get(parent).map_or(0, |s| s.m.generation);
        // The wait is two of the session's probe timeouts, the bound the issue sets from its round trip; a
        // configured wait stands in for it.
        let wait = if self.cfg.probe_window > 0 {
            self.cfg.probe_window
        } else {
            self.slots
                .get(parent)
                .and_then(|s| s.conn.as_ref())
                .map_or(PROBE_WINDOW, |c| c.recovery().pto_duration().saturating_mul(2))
        };
        if let Some(s) = self.slots.get_mut(i) {
            s.mem = Some(mem);
            s.m.peer = Some(peer);
            s.m.alpn = Some(alpn);
            s.m.role = role;
            s.m.parent = Some(pid);
            s.m.probing = true;
            s.m.probe_parent = pidx;
            s.m.probe_of_gen = probed_gen;
            s.m.probe_until = now.saturating_add(wait);
            s.m.probe_quiet = quiet;
            s.m.dial_addrs = addrs;
        }
        trace!(self, now, Sub { step: 3, parent: parent as u64, child: i as u64 });
        self.recompute_probed(parent, now);
        self.settle(i, now);
        Ok(self.session_id(i))
    }

    /// The probe of slot `i` reached its end: ride the parent when one qualifies (the dial's sub-session is built
    /// here from the memory the probe stashed, and the id the application holds is the id that connects), else
    /// lapse into the dial's own handshake on the addresses the dial gave and close the probed session as dead
    /// when nothing was in flight on it.
    // Out of line, as `free_slot`: a whole connection moves here.
    #[inline(never)]
    pub(crate) fn resolve_probe(&mut self, i: usize, now: u64) {
        let session = self.session_id(i);
        let Some((peer, alpn, role, pidx, probed_gen, was_quiet, addrs)) = self.slots.get(i).and_then(|s| {
            Some((s.m.peer?, s.m.alpn?, s.m.role, s.m.probe_parent, s.m.probe_of_gen, s.m.probe_quiet, s.m.dial_addrs))
        }) else {
            self.free_slot(i, now);
            return;
        };
        let probed = pidx as usize;
        // The lapse only ever touches the session it probed: the slot may have been freed and reused since, and
        // the session there now is somebody else's.
        let same = self.slots.get(probed).is_some_and(|s| s.m.in_use && s.m.generation == probed_gen);
        // The ride's parts are drawn before the probe's memory is taken: when they fail, the dial lapses instead.
        if let Some(parent) = self.find_parent(&peer, now)
            && let Ok(parts) = self.sub_parts(parent)
            && let Some(mem) = self.slots.get_mut(i).and_then(|s| s.mem.take())
        {
            trace!(self, now, Sub { step: 4, parent: parent as u64, child: i as u64 });
            // A failed construction retired the slot with its memory; an open that could not be queued is undone
            // by the redial of `open_sub_over`, which reports the dial.
            if self.open_sub_over(parent, i, mem, parts, peer, alpn, role, now).is_err()
                && self.slots.get(i).is_some_and(|s| !s.m.in_use)
            {
                self.fail_probe(i, session, now);
            }
            if same {
                self.recompute_probed(probed, now);
            }
            return;
        }
        // The parent stayed silent: the dial makes its own handshake, to the addresses the dial gave, with the
        // probed session's own direct address ahead of them when it has one left (a relay's address is the
        // relay's, not the peer's). The probed session is closed as dead when it is still the one probed and
        // nothing was in flight on it when the probe started or now (a quiet session the peer stopped answering);
        // with something in flight it is left to its own keepalive, and its end closes as usual.
        trace!(self, now, Sub { step: 5, parent: probed as u64, child: i as u64 });
        let learned = same
            .then(|| {
                self.slots.get(probed).and_then(|s| s.conn.as_ref()).and_then(|c| {
                    (!c.active_is_relay()).then(|| c.active_path()).flatten().and_then(|p| self.path_addrs(p)).map(|(_, r)| r)
                })
            })
            .flatten();
        let quiet = was_quiet
            && same
            && self
                .slots
                .get(probed)
                .and_then(|s| s.conn.as_ref())
                .is_some_and(|c| c.recovery().packets_in_flight() == 0);
        if quiet
            && let Some(conn) = self.slots.get_mut(probed).and_then(|s| s.conn.as_mut())
        {
            let mut env = env!(self, now);
            conn.close(&mut env, &mut lent!(self), code::NO_ERROR);
            self.settle(probed, now);
        }
        if same {
            self.recompute_probed(probed, now);
        }
        // The addresses the lapse dials: the session's own first, then the dial's, none twice.
        let mut list = [SocketAddr::from(([0, 0, 0, 0], 0)); NP];
        let mut n = 0;
        for a in learned.into_iter().chain(addrs.into_iter().flatten()) {
            if !list.get(..n).unwrap_or_default().contains(&a)
                && let Some(d) = list.get_mut(n)
            {
                *d = a;
                n += 1;
            }
        }
        let list = list.get(..n).unwrap_or_default();
        // The dial keeps its slot: the memory the probe held becomes the handshake's. Everything that can refuse
        // is asked before the memory is taken, so a refusal frees the slot with its memory.
        let route = list.iter().find_map(|a| self.route_for(a).map(|l| (*a, l)));
        let (Some((first, local)), Some(prekey)) = (route, self.prekey.clone()) else {
            self.fail_probe(i, session, now);
            return;
        };
        let Some(mem) = self.slots.get_mut(i).and_then(|s| s.mem.take()) else {
            self.fail_probe(i, session, now);
            return;
        };
        if self.dial_fresh(i, mem, now, peer, alpn, &prekey, list, role, first, local).is_err() {
            self.fail_probe(i, session, now);
        }
    }

    /// End probe `i`, whose application holds `session`, without a session: the application is told the dial was
    /// refused. A slot a failed construction already retired is not freed again.
    fn fail_probe(&mut self, i: usize, session: SessionId, now: u64) {
        let (node, alpn) = self.slots.get(i).map_or((None, None), |s| (s.m.peer, s.m.alpn));
        if let (Some(node), Some(alpn)) = (node, alpn) {
            self.emit(Event::ConnectFailed {
                session: Some(session),
                node,
                alpn,
                reason: ConnectFailure::Refused,
            });
        }
        self.free_slot(i, now);
    }

    /// End probe `i` at the application's request (a close of the dial's id while it probes): the dial it holds
    /// never connected, so it is reported failed and the slot freed.
    pub(crate) fn end_probe(&mut self, i: usize, now: u64) {
        let session = self.session_id(i);
        let (node, alpn) = self.slots.get(i).map_or((None, None), |s| (s.m.peer, s.m.alpn));
        let pidx = self.slots.get(i).map_or(NIL, |s| s.m.probe_parent);
        trace!(self, now, Sub { step: 6, parent: u64::from(pidx), child: i as u64 });
        if let (Some(node), Some(alpn)) = (node, alpn) {
            self.emit(Event::ConnectFailed {
                session: Some(session),
                node,
                alpn,
                reason: ConnectFailure::Closed,
            });
        }
        self.free_slot(i, now);
        self.recompute_probed(pidx as usize, now);
    }

    /// The slot of `id` if the session is live, connection or not: a quiet-parent probe holds none (`QUIET_PROBE`).
    pub(crate) fn slot_of_any(&self, id: SessionId) -> Option<usize> {
        let s = self.slots.get(id.slot())?;
        (s.m.in_use && s.m.generation == id.generation()).then_some(id.slot())
    }

    /// The probes waiting on the session now in slot `parent` (`QUIET_PROBE`), at most [`MAX_WAITERS`] of them.
    // vertexia: a scan of the table per probe started, resolved or ended (never per packet: the early resolution of
    // `settle_core` is gated on the probed mark), a list per parent if probes get hot
    pub(crate) fn probes_of(&self, parent: usize) -> impl Iterator<Item = usize> + '_ {
        let idx = u32::try_from(parent).unwrap_or(NIL);
        let generation = self.slots.get(parent).map_or(0, |s| s.m.generation);
        self.slots.iter().enumerate().filter_map(move |(i, s)| {
            (s.m.in_use && s.m.probing && s.m.probe_parent == idx && s.m.probe_of_gen == generation).then_some(i)
        })
    }

    /// Mark the probed session of a new probe so its next ping is due at once, and recompute the mark when the
    /// probes of `parent` end: with none left, the session's keepalive returns to its own schedule.
    fn recompute_probed(&mut self, parent: usize, now: u64) {
        let until = self.probes_of(parent).filter_map(|w| self.slots.get(w).map(|s| s.m.probe_until)).max();
        if let Some(s) = self.slots.get_mut(parent).filter(|s| s.m.in_use) {
            s.m.probed_until = until.unwrap_or(0);
        }
        self.settle(parent, now);
    }

    /// Sub-session `child` runs where session `parent` runs: it takes the parent's paths, with what the endpoint said
    /// of each and whether each is validated, its active path, its round-trip estimate, and when the endpoint last
    /// sent and heard on each (so a standby path the parent kept alive is not pinged again at once).
    fn follow_parent_paths(&mut self, parent: usize, child: usize, now: u64) {
        let Some(ps) = self.slots.get(parent) else { return };
        let stamps = ps.m.paths;
        let Some(pc) = ps.conn.as_ref() else { return };
        let Some(active) = pc.active_path() else { return };
        let mut list = [(PathId(0), PathInfo::default(), false); NP];
        let mut n = 0;
        for (d, p) in list.iter_mut().zip(pc.path_list()) {
            *d = p;
            n += 1;
        }
        let rtt = pc.rtt_estimate();
        let mut env = env!(self, now);
        if let Some(s) = self.slots.get_mut(child) {
            s.m.paths = stamps;
            if let Some(k) = s.conn.as_mut() {
                k.adopt_paths(&mut env, list.get(..n).unwrap_or_default(), active);
                k.adopt_rtt(rtt);
            }
        }
    }

    /// Queue the sub-session open extension in `parent`. Returns whether it was queued.
    fn queue_sub_open(&mut self, parent: usize, alpn: Alpn, cc: ConnId, cs: ConnId, now: u64) -> bool {
        let mut body = [0u8; 1 + pinc_security::ids::MAX_ALPN_LEN + 2 * CID_LEN];
        let a = alpn.as_bytes();
        let used = 1 + a.len() + 2 * CID_LEN;
        if let Some(b) = body.get_mut(..used) {
            let (head, tail) = b.split_at_mut(1 + a.len());
            if let Some(l) = head.first_mut() {
                *l = u8::try_from(a.len()).unwrap_or(0);
            }
            if let Some(d) = head.get_mut(1..) {
                d.copy_from_slice(a);
            }
            let (c1, c2) = tail.split_at_mut(CID_LEN);
            c1.copy_from_slice(cc.as_bytes());
            c2.copy_from_slice(cs.as_bytes());
        }
        let queued = self.slots.get_mut(parent).and_then(|s| {
            s.m.has_sub = true;
            s.m.ctrl_pending = true;
            s.conn.as_mut().map(|c| c.send_extension(ext::SUB_SESSION_OPEN, body.get(..used).unwrap_or_default()))
        });
        let ok = matches!(queued, Some(Ok(())));
        if ok {
            self.dirty_promote(parent, now);
        }
        ok
    }

    /// A session of `peer` that is not yet allowed, whatever its role and state, that a dial for another protocol can
    /// wait for: not itself a waiting sub-session, not a quiet-parent probe (it holds no connection to carry the
    /// waiter's keys), with room for another waiter, and while fewer than [`MAX_WAITING_PARENTS`] sessions have
    /// waiters.
    pub(crate) fn find_waiting_parent(&self, peer: &NodeId, alpn: &[u8]) -> Option<usize> {
        let parent = self.peer_find(peer, |e, i| {
            e.slots.get(i).is_some_and(|s| {
                s.m.state != State::Closing
                    && !s.m.allowed
                    && !s.m.denied
                    && !s.m.waiting
                    && !s.m.probing
                    && s.m.alpn.is_some_and(|a| a.as_bytes() != alpn)
                    && e.waiters(i) < MAX_WAITERS
            })
        })?;
        (self.waiting_parents() < MAX_WAITING_PARENTS).then_some(parent)
    }

    /// How many sessions have a sub-session waiting for them.
    // vertexia: a scan of the table per waiting dial, a counter kept by the open and the release if dials get hot
    fn waiting_parents(&self) -> usize {
        let seen = self.slots.iter().enumerate().filter(|(_, s)| s.m.waiting);
        seen.clone()
            .filter(|(i, s)| !seen.clone().take_while(|(j, _)| j < i).any(|(_, o)| o.m.parent == s.m.parent))
            .count()
    }

    /// How many sub-sessions wait for session `parent`.
    fn waiters(&self, parent: usize) -> usize {
        let Some(peer) = self.slots.get(parent).and_then(|s| s.m.peer) else { return 0 };
        let pid = self.session_id(parent);
        self.peer_sessions(&peer)
            .filter(|c| self.slots.get(*c).is_some_and(|s| s.m.waiting && s.m.parent == Some(pid)))
            .count()
    }

    /// Open a sub-session towards `peer` for `alpn` over session `parent`, which is still in its handshake. The
    /// application is told `Connected` at once and may write; the keys come when the parent is allowed.
    // Out of line, as `free_slot`: a whole connection moves here.
    #[inline(never)]
    pub(crate) fn open_sub_wait(
        &mut self,
        parent: usize,
        peer: NodeId,
        alpn: &[u8],
        role: Role,
        now: u64,
    ) -> Result<SessionId, CommandError> {
        let alpn = Alpn::new(alpn).ok_or(CommandError::BadAlpn)?;
        let cc = self.random_cid()?;
        let cs = self.random_cid()?;
        let path = self
            .slots
            .get(parent)
            .and_then(|s| s.conn.as_ref())
            .and_then(Connection::active_path)
            .ok_or(CommandError::NoRoute)?;
        let (child, mem) = self.alloc_slot(true, now).ok_or(CommandError::Full)?;
        let cfg = self.conn_config(Some(&peer));
        let open = SubWait { alpn, cc, cs, identity: self.identity, path, path_info: PathInfo { interface_mtu: self.cfg.conn.interface_mtu, ..PathInfo::default() } };
        let mut env = env!(self, now);
        let conn = match Connection::sub_pending(cfg, open, mem, &mut env) {
            Ok(c) => c,
            Err(e) => {
                self.retire_slot(child);
                return Err(CommandError::Failure(e));
            }
        };
        let pid = self.session_id(parent);
        if let Some(s) = self.slots.get_mut(child) {
            s.conn = Some(conn);
            s.m.peer = Some(peer);
            s.m.alpn = Some(alpn);
            s.m.parent = Some(pid);
            s.m.sub = true;
            s.m.waiting = true;
            s.m.optimistic = true;
            s.m.sub_ids = Some((cc, cs));
            s.m.role = role;
        }
        if let Some(s) = self.slots.get_mut(parent) {
            s.m.has_sub = true;
        }
        self.link_peer(peer, u32::try_from(child).unwrap_or(0));
        self.sync_cids(child, true);
        self.sync_ack_every(child);
        trace!(self, now, Sub { step: 0, parent: parent as u64, child: child as u64 });
        self.announce(child);
        self.settle(child, now);
        Ok(self.session_id(child))
    }

    /// Session `parent` was allowed: the sub-sessions that waited for it get their keys and their open goes out.
    pub(crate) fn release_waiting(&mut self, parent: usize, now: u64) {
        let Some(peer) = self.slots.get(parent).and_then(|s| s.m.peer) else { return };
        let pid = self.session_id(parent);
        let Some(est) = self.slots.get(parent).and_then(|s| s.conn.as_ref()).and_then(|c| c.session().cloned()) else {
            return;
        };
        while let Some(c) = self.peer_find(&peer, |e, c| {
            e.slots.get(c).is_some_and(|s| s.m.waiting && s.m.parent == Some(pid))
        }) {
            let Some((alpn, ids)) = self.slots.get(c).and_then(|s| Some((s.m.alpn?, s.m.sub_ids?))) else { break };
            let mut env = env!(self, now);
            let activated = self
                .slots
                .get_mut(c)
                .and_then(|s| s.conn.as_mut())
                .is_some_and(|k| k.activate_sub(&mut env, &est, alpn).is_ok());
            if let Some(s) = self.slots.get_mut(c) {
                s.m.waiting = false;
            }
            if activated {
                self.follow_parent_paths(parent, c, now);
            }
            if activated && self.queue_sub_open(parent, alpn, ids.0, ids.1, now) {
                self.settle(parent, now);
            } else {
                // It cannot be opened: close it so the application dials again.
                if let Some(s) = self.slots.get_mut(c) {
                    s.m.orphaned = true;
                    if let Some(k) = s.conn.as_mut() {
                        k.close(&mut env!(self, now), &mut lent!(self), pinc_transport::conn::code::NO_ERROR);
                    }
                }
            }
            self.settle(c, now);
        }
    }

    /// Accept a sub-session open that arrived in session `parent`.
    // Out of line, as `free_slot`: a whole connection moves here.
    #[inline(never)]
    pub(crate) fn sub_accept(&mut self, parent: usize, now: u64, body: &[u8]) {
        let Some(&alen) = body.first() else { return };
        let alen = usize::from(alen);
        if body.len() != 1 + alen + 2 * CID_LEN {
            return;
        }
        let (Some(a), Some(cc), Some(cs)) = (
            body.get(1..1 + alen),
            body.get(1 + alen..1 + alen + CID_LEN).and_then(ConnId::new),
            body.get(1 + alen + CID_LEN..).and_then(ConnId::new),
        ) else {
            return;
        };
        if alen == 0 || !self.accepts(a) || self.demux.contains(&cs) || self.subs_seen.contains(&cs) {
            return;
        }
        let Some(proto) = Alpn::new(a) else { return };
        let Some((est, path, peer)) = self
            .slots
            .get(parent)
            .and_then(|s| s.conn.as_ref().filter(|c| c.is_connected()))
            .and_then(|c| Some((c.session()?.clone(), c.active_path()?, c.session()?.peer)))
        else {
            return;
        };
        let Some((child, mem)) = self.alloc_slot(false, now) else { return };
        let cfg = self.conn_config(Some(&peer));
        let open = SubOpen {
            client: false,
            parent: &est,
            alpn: proto,
            cc,
            cs,
            identity: self.identity,
            path,
            path_info: PathInfo { interface_mtu: self.cfg.conn.interface_mtu, ..PathInfo::default() },
        };
        let mut env = env!(self, now);
        let Ok(conn) = Connection::sub_session(cfg, open, mem, &mut env) else {
            self.retire_slot(child);
            return;
        };
        self.subs_seen.insert(cs, ());
        let pid = self.session_id(parent);
        if let Some(s) = self.slots.get_mut(child) {
            s.conn = Some(conn);
            s.m.peer = Some(peer);
            s.m.alpn = Some(proto);
            s.m.parent = Some(pid);
            s.m.sub = true;
        }
        if let Some(s) = self.slots.get_mut(parent) {
            s.m.has_sub = true;
        }
        self.follow_parent_paths(parent, child, now);
        self.sync_cids(child, true);
        trace!(self, now, Sub { step: 1, parent: parent as u64, child: child as u64 });
        self.settle(child, now);
    }
}
