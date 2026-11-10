//! The receive path: split a datagram into packets, unprotect and open each, and dispatch its frames to the layers.
//!
//! Order of work for a packet: header (route by connection id), header unprotection, key choice by phase bit,
//! authentication, a first pass over the frames (what the packet is: ack-eliciting, a ping, stream bytes, whether it
//! carries data that moves the peer's path) and the duplicate check, a second pass that applies each frame, and last
//! the bookkeeping that depends on the whole packet (the received-packet record, following the peer, the handshake
//! confirmation).
//!
//! Invariants: nothing is acted on before it authenticated, so a forged packet changes nothing (a new path is added
//! only after a packet from it authenticated); a packet whose frames could not be stored for lack of memory is not
//! recorded as received, so the peer sends it again; any authenticated packet ends the peer's sleep.

use vinc_crypto::Provider;
use vinc_security::{Env, ResponderStores};
use vinc_wire::varint;

use super::config::{MIN_MTU, PathId};
use super::ctl::{Outcome, apply};
use super::event::{Drop, Ev, code};
use super::path::RJ_THIN_GAP;
use super::{Connection, Phase};
use crate::frame::{Ack, Frame, FrameIter};
use crate::packet::{Header, LongHeader, LongType, Packet, PacketError, decode_pn, open, packets, unprotect_header};
use crate::recovery::PathKind;
use crate::recovery::{RxOutcome, RxPacket};
use crate::stream::{StreamError, StreamSource};

/// The largest extension body kept: a datagram of the biggest path size.
const EXT_MAX: usize = 9300;

/// What the datagram being processed is known to be.
#[derive(Debug, Clone, Copy)]
pub(super) struct Rx {
    pub(super) path_id: PathId,
    pub(super) path: Option<usize>,
    pub(super) dlen: usize,
    pub(super) now: u64,
    /// The packet in hand opened under the previous generation's key.
    pub(super) old_key: bool,
}

/// Why a frame could not be applied.
#[derive(Debug, Clone, Copy)]
enum Fault {
    /// A rule was broken: close with this code.
    Violation(u64),
    /// The connection is gated and the frame would raise an event: drop the packet unacknowledged.
    Gated,
    /// Memory is short: drop the packet unacknowledged.
    Shortage,
}

/// Whether applying the frame can queue an event for the application. ACK, PING, PADDING, CLOSE and the frames that
/// only make the connection answer or probe are not among them: a gated connection still takes those.
const fn raises_event(f: &Frame<'_>) -> bool {
    matches!(
        f,
        Frame::ResetStream { .. }
            | Frame::StopSending { .. }
            | Frame::Stream { .. }
            | Frame::MaxStreamData { .. }
            | Frame::MaxStreams { .. }
            | Frame::PathResponse(_)
            | Frame::Datagram { .. }
            | Frame::Sleep
            | Frame::Wake
            | Frame::Ready
            | Frame::NewTickets(_)
            | Frame::Extension { .. }
    )
}

fn stream_fault(e: StreamError) -> Fault {
    match e {
        StreamError::StreamState | StreamError::UnknownStream => Fault::Violation(code::STREAM_STATE),
        StreamError::FlowControl => Fault::Violation(code::FLOW_CONTROL),
        StreamError::FinalSize => Fault::Violation(code::FINAL_SIZE),
        StreamError::Exhausted | StreamError::Fragmented => Fault::Shortage,
        _ => Fault::Violation(code::PROTOCOL_VIOLATION),
    }
}

/// What a first pass over the frames of a packet found.
#[derive(Debug, Default, Clone, Copy)]
#[allow(clippy::struct_excessive_bools, reason = "independent facts about one packet")]
struct Props {
    eliciting: bool,
    ping: bool,
    padding: bool,
    /// The packet carries STREAM, DATAGRAM or WAKE: the frames that move the peer's path.
    nonprobing: bool,
    wake: bool,
    stream_bytes: u32,
    /// The largest data payload (stream or datagram bytes).
    payload: usize,
}

fn scan(payload: &[u8]) -> Result<Props, crate::frame::FrameError> {
    let mut p = Props::default();
    for f in FrameIter::new(payload) {
        match f? {
            Frame::Padding { .. } => p.padding = true,
            Frame::Ack(_) => {}
            Frame::Ping => {
                p.eliciting = true;
                p.ping = true;
            }
            Frame::Stream { data, .. } => {
                p.eliciting = true;
                p.nonprobing = true;
                p.payload += data.len();
                p.stream_bytes = p
                    .stream_bytes
                    .saturating_add(u32::try_from(data.len()).unwrap_or(u32::MAX));
            }
            Frame::Datagram { data, .. } => {
                p.eliciting = true;
                p.nonprobing = true;
                p.payload += data.len();
            }
            Frame::Wake => {
                p.eliciting = true;
                p.nonprobing = true;
                p.wake = true;
            }
            _ => p.eliciting = true,
        }
    }
    Ok(p)
}

conn_impl! {
    /// Process a received datagram from `path`. Returns `Ok` if at least one packet of it was used.
    ///
    /// A server connection needs the endpoint's shared handshake caches: use
    /// [`handle_datagram_with`](Self::handle_datagram_with). Here a server cannot answer handshake messages and
    /// refuses them.
    ///
    /// # Errors
    /// A [`Drop`] naming why no packet of the datagram was used; none is fatal.
    pub fn handle_datagram(&mut self, env: &mut Env<'_, P>, path: PathId, dgram: &mut [u8]) -> Result<(), Drop> {
        self.handle_inner(env, None::<&mut ResponderStores<0, 0>>, path, dgram)
    }

    /// As [`handle_datagram`](Self::handle_datagram) for a server: `stores` are the prekey cache and ticket store
    /// every connection of the endpoint shares.
    ///
    /// # Errors
    /// A [`Drop`] naming why no packet of the datagram was used.
    pub fn handle_datagram_with<const PK: usize, const TK: usize>(
        &mut self,
        env: &mut Env<'_, P>,
        stores: &mut ResponderStores<PK, TK>,
        path: PathId,
        dgram: &mut [u8],
    ) -> Result<(), Drop> {
        self.handle_inner(env, Some(stores), path, dgram)
    }

    fn handle_inner<const PK: usize, const TK: usize>(
        &mut self,
        env: &mut Env<'_, P>,
        mut stores: Option<&mut ResponderStores<PK, TK>>,
        path: PathId,
        dgram: &mut [u8],
    ) -> Result<(), Drop> {
        let now = env.now;
        match self.phase {
            Phase::Closed | Phase::Closing => return Err(Drop::Closed),
            _ => {}
        }
        let dlen = dgram.len();
        let mut known = self.paths.find(path);
        if known.is_none() && !self.client && self.paths.iter().next().is_none() {
            known = self.new_path_slot(path, self.learned_path(), now);
        }
        if let Some(p) = known.and_then(|i| self.paths.get_mut(i)) {
            p.amp.on_receive(dlen as u64);
        }
        self.sess_amp.on_receive(dlen as u64);
        self.stats.datagrams_received += 1;
        self.stats.bytes_received += dlen as u64;
        let mut ctx = Rx { path_id: path, path: known, dlen, now, old_key: false };
        self.life.clock = now;
        let (mut ok, mut first_err) = (false, None);
        for pkt in packets(dgram, self.cfg.cid_len) {
            let r = match pkt {
                Ok(mut pkt) => self.on_packet(env, stores.as_deref_mut(), &mut ctx, &mut pkt),
                Err(e) => Err(Drop::Malformed(e)),
            };
            match r {
                Ok(()) => ok = true,
                Err(e) => {
                    first_err.get_or_insert(e);
                }
            }
            if matches!(self.phase, Phase::Closed | Phase::Closing) {
                break;
            }
        }
        if ok { Ok(()) } else { Err(first_err.unwrap_or(Drop::Empty)) }
    }

    fn on_packet<const PK: usize, const TK: usize>(
        &mut self,
        env: &mut Env<'_, P>,
        stores: Option<&mut ResponderStores<PK, TK>>,
        ctx: &mut Rx,
        pkt: &mut Packet<'_>,
    ) -> Result<(), Drop> {
        let pn_off = pkt.pn_off();
        match pkt.header {
            Header::Long { header, header_len } => match header.ty {
                LongType::Handshake => self.on_handshake(env, stores, ctx, &header, header_len, pkt.bytes),
                LongType::ZeroRtt => self.on_zero_rtt(env, ctx, pn_off, pkt.bytes),
            },
            Header::Short { dcid } => {
                if !self.cids.is_local(&dcid) {
                    return Err(Drop::Unroutable);
                }
                self.on_short(env, ctx, pn_off, pkt.bytes)
            }
        }
    }

    fn on_handshake<const PK: usize, const TK: usize>(
        &mut self,
        env: &mut Env<'_, P>,
        stores: Option<&mut ResponderStores<PK, TK>>,
        ctx: &mut Rx,
        header: &LongHeader,
        header_len: usize,
        bytes: &[u8],
    ) -> Result<(), Drop> {
        // A resumed server keeps answering a repeated Hello (or a full Initial under the same ids) until the first
        // 1-RTT packet shows the client holds the session.
        if self.phase != Phase::Handshaking && !(self.phase == Phase::Connected && self.hs.keeps_reply()) {
            return Err(Drop::Empty);
        }
        let Some(pi) = ctx.path else { return Err(Drop::NoPath) };
        if self.client && self.cids.first_local() != header.dcid {
            return Err(Drop::Unroutable);
        }
        self.cids.set_first_remote(header.scid);
        if let Some(p) = self.paths.get_mut(pi) {
            p.last_rx = ctx.now;
        }
        if self.client && self.phase == Phase::Handshaking && pi != self.paths.active {
            // The answer to a flight sent on several paths came back on this one: the session continues here, and
            // the path that did not answer is validated only when a challenge on it is answered.
            let old = self.paths.active;
            if let Some(p) = self.paths.get_mut(old) {
                p.validated = false;
            }
            if let Some(p) = self.paths.get_mut(pi) {
                p.validated = true;
                p.amp.validate();
            }
            self.switch_active(pi);
        }
        self.note_heard(ctx.now);
        let body = bytes.get(header_len..).ok_or(Drop::Malformed(PacketError::Length))?;
        let Some(len) = self.hs.on_fragment(&mut self.pool, body) else { return Ok(()) };
        let r = self.hs.feed(&self.pool, env, stores, len);
        self.pump(env);
        r.map_err(Drop::Handshake)
    }

    fn on_zero_rtt(&mut self, env: &mut Env<'_, P>, ctx: &mut Rx, pn_off: usize, bytes: &mut [u8]) -> Result<(), Drop> {
        let p = env.provider;
        ctx.old_key = false;
        let Some(dir) = self.keys.early_recv.as_mut() else { return Err(Drop::Undecryptable) };
        let un = unprotect_header(&dir.hk, p, bytes, pn_off, true).map_err(|_| Drop::Undecryptable)?;
        if un.pn_len != crate::packet::PN_LEN_BASE {
            return Err(Drop::Undecryptable);
        }
        let opened = open(&mut dir.pk, p, bytes, pn_off, &un, self.rx.largest()).map_err(|_| Drop::Undecryptable)?;
        let payload = bytes.get(opened.payload_start..opened.payload_end).ok_or(Drop::Undecryptable)?;
        self.process_payload(env, ctx, opened.pn, payload)
    }

    pub(super) fn on_short(&mut self, env: &mut Env<'_, P>, ctx: &mut Rx, pn_off: usize, bytes: &mut [u8]) -> Result<(), Drop> {
        let p = env.provider;
        let now = ctx.now;
        if self.keys.recv.is_none() {
            if !self.client && self.phase == Phase::Handshaking {
                if self.early.push(&mut self.pool, bytes) {
                    self.stats.early_buffered += 1;
                    return Err(Drop::Buffered);
                }
                self.stats.early_dropped += 1;
            }
            return Err(Drop::Undecryptable);
        }
        ctx.old_key = false;
        let largest = self.rx.largest();
        let mut failed = false;
        let mut opened = None;
        let mut promoted = false;
        #[cfg(feature = "trace")]
        let mut seen = (0u64, false, None);
        // The hold of a previous key is computed from the probe timeout before the packet's frames change it.
        #[cfg(feature = "trace")]
        let pto_in = self.rec.pto_duration();
        if let Some(rk) = self.keys.recv.as_mut() {
            rk.expire(now);
            match unprotect_header(&rk.hk, p, bytes, pn_off, false) {
                Ok(un) if un.pn_len == self.pn_len => {
                    let pn_est = decode_pn(un.truncated, un.pn_len, largest);
                    #[cfg(feature = "trace")]
                    {
                        seen = (pn_est, un.key_phase(), None);
                    }
                    match rk.select(p, un.key_phase(), pn_est) {
                        Ok(sel) => {
                            ctx.old_key = sel == super::keys::Sel::Previous;
                            #[cfg(feature = "trace")]
                            {
                                seen.2 = Some(sel);
                            }
                            if let Some(key) = rk.key_mut(sel) {
                                match open(key, p, bytes, pn_off, &un, largest) {
                                    Ok(o) => {
                                        opened = Some(o);
                                        if sel == super::keys::Sel::Next {
                                            promoted = true;
                                            rk.promote(o.pn, now.saturating_add(self.rec.pto_duration()));
                                        } else if sel == super::keys::Sel::Current {
                                            rk.note(o.pn);
                                        }
                                    }
                                    Err(_) => failed = true,
                                }
                            } else {
                                failed = true;
                            }
                        }
                        Err(_) => failed = true,
                    }
                }
                _ => failed = true,
            }
        }
        let Some(opened) = opened.filter(|_| !failed) else {
            self.stats.undecryptable += 1;
            #[cfg(feature = "trace")]
            self.trace_rx_event(now, pto_in, seen, false, false, false);
            return Err(Drop::Undecryptable);
        };
        if promoted {
            self.stats.key_updates += 1;
            if self.keys.behind_peer() && self.keys.update_send(now).is_err() {
                self.violation(now, code::INTERNAL);
                return Err(Drop::Closed);
            }
        }
        // A 1-RTT packet authenticated: the early keys have done their job, and a resumed server may let go of the
        // Reply it kept for a repeated Hello.
        self.keys.early_recv = None;
        if !self.client && !self.confirmed {
            self.confirmed = true;
            self.hs.confirm(&mut self.pool);
        }
        if let Some(dcid) = bytes.get(1..1 + self.cfg.cid_len).and_then(vinc_security::ConnId::new) {
            self.cids.on_authenticated(&dcid);
        }
        let payload = bytes.get(opened.payload_start..opened.payload_end).ok_or(Drop::Undecryptable)?;
        let result = self.process_payload(env, ctx, opened.pn, payload);
        #[cfg(feature = "trace")]
        self.trace_rx_event(now, pto_in, (opened.pn, seen.1, seen.2), true, matches!(result, Err(Drop::Duplicate)), promoted);
        result
    }

    /// Process `payload` as the frames of an authenticated packet `pn` that arrived on `path` (test hook: no sealing).
    ///
    /// # Errors
    /// The [`Drop`] reason if the packet is refused.
    #[cfg(feature = "inject")]
    pub fn inject_payload(&mut self, env: &mut Env<'_, P>, path: PathId, now: u64, pn: u64, payload: &[u8]) -> Result<(), Drop> {
        let mut ctx = Rx { path_id: path, path: None, dlen: payload.len(), now, old_key: false };
        self.process_payload(env, &mut ctx, pn, payload)
    }

    /// Authenticated packet `pn` with `payload` frames.
    fn process_payload(&mut self, env: &mut Env<'_, P>, ctx: &mut Rx, pn: u64, payload: &[u8]) -> Result<(), Drop> {
        let now = ctx.now;
        let Ok(props) = scan(payload) else {
            self.violation(now, code::FRAME_ENCODING);
            return Err(Drop::Closed);
        };
        if self.rx.contains(pn) {
            self.stats.duplicates += 1;
            return Err(Drop::Duplicate);
        }
        let pi = if let Some(i) = ctx.path {
            i
        } else {
            let i = self.new_path_slot(ctx.path_id, self.learned_path(), now).ok_or(Drop::NoPath)?;
            ctx.path = Some(i);
            if let Some(p) = self.paths.get_mut(i) {
                p.amp.on_receive(ctx.dlen as u64);
            }
            i
        };
        let prev_largest = self.rx.largest();
        self.stats.packets_received += 1;
        self.note_heard(now);
        self.rec.note_peer_activity(now);
        if let Some(p) = self.paths.get_mut(pi) {
            p.last_rx = now;
        }
        let was_asleep = self.life.peer_asleep.take().is_some();
        if was_asleep {
            self.suspend_probes();
        }
        // A frame held back for want of room leaves the packet unacknowledged, but the frames behind it are still
        // taken: the room it waits for may only come from them, and a retransmission repeats the same order.
        let mut held = false;
        for f in FrameIter::new(payload) {
            let Ok(f) = f else { break };
            if let Err(fault) = self.on_frame(env, pi, now, ctx.old_key, f) {
                match fault {
                    Fault::Violation(c) => {
                        self.violation(now, c);
                        return Err(Drop::Closed);
                    }
                    Fault::Shortage => held = true,
                    Fault::Gated => return Err(Drop::Gated),
                }
            }
            if matches!(self.phase, Phase::Closed | Phase::Closing) {
                return Ok(());
            }
        }
        if was_asleep && self.life.peer_asleep.is_none() {
            self.push(Ev::PeerAwake);
        }
        if held {
            return Err(Drop::Empty);
        }
        // `contains` was false above and nothing recorded it since, so this is always `New`; a number beyond 2^62 was
        // refused by `open`.
        let recorded = self.rx.on_packet_received(RxPacket {
            pn,
            now,
            ack_eliciting: props.eliciting,
            stream_bytes: props.stream_bytes,
        });
        debug_assert!(matches!(recorded, Ok(RxOutcome::New)));
        if props.ping && props.padding && ctx.dlen > usize::from(MIN_MTU)
            && let Some(p) = self.paths.get_mut(pi)
        {
            p.echo = Some(u16::try_from(ctx.dlen).unwrap_or(u16::MAX));
        }
        if props.nonprobing {
            self.follow_peer(env, pi, pn, prev_largest, props.wake, now);
        }
        if props.wake && self.on_wake(now) {
            self.suspend_probes();
        }
        if self.client && self.phase == Phase::Connected && !self.confirmed {
            self.confirmed = true;
            self.hs.confirm(&mut self.pool);
        }
        Ok(())
    }

    /// Both ends follow the highest-numbered packet that carries data to the path it came from, and challenge a new
    /// UDP path in parallel.
    fn follow_peer(&mut self, env: &mut Env<'_, P>, pi: usize, pn: u64, prev_largest: Option<u64>, wake: bool, now: u64) {
        if prev_largest.is_some_and(|l| pn < l) || self.phase != Phase::Connected || pi == self.paths.active {
            return;
        }
        let Some(p) = self.paths.get(pi).copied() else { return };
        if p.info.kind == PathKind::Direct && !p.validated {
            let node = self.rec.peak_rtt().max(if self.rec.rtt().has_sample() { self.rec.rtt().smoothed() } else { 0 });
            let fresh = self.cfg.thin
                && p.challenge.is_some()
                && now.saturating_sub(p.challenge_at) < RJ_THIN_GAP.max(node.saturating_mul(2));
            if !fresh {
                self.queue_challenge(env, pi);
            }
        }
        let cur_relay = self.paths.active().is_none_or(|c| c.info.kind == PathKind::Relay);
        if cur_relay || p.info.kind == PathKind::Direct || wake {
            self.follow_active(pi);
        }
    }

    fn on_frame(&mut self, env: &mut Env<'_, P>, pi: usize, now: u64, old_key: bool, f: Frame<'_>) -> Result<(), Fault> {
        if self.gated && raises_event(&f) {
            return Err(Fault::Gated);
        }
        match f {
            // WAKE is acted on once the whole packet is known (see `process_payload`): it moves the path first.
            Frame::Padding { .. } | Frame::Ping | Frame::Wake => {}
            Frame::Ack(ack) => self.on_ack(pi, now, &ack)?,
            Frame::ResetStream { id, error, final_size } => {
                let first = self.first_unopened(id);
                match self.streams.on_reset_stream(&mut self.pool, id, error, final_size) {
                    Ok(()) => {}
                    Err(e) => return Err(stream_fault(e)),
                }
                self.push_opened(id, first);
                self.push(Ev::Reset(id, error));
            }
            Frame::StopSending { id, error } => {
                let first = self.first_unopened(id);
                match self.streams.on_stop_sending(&mut self.pool, id, error) {
                    Ok(fresh) => {
                        self.push_opened(id, first);
                        if fresh {
                            self.push(Ev::Stopped(id, error));
                        }
                    }
                    Err(e) => return Err(stream_fault(e)),
                }
            }
            Frame::Stream { id, offset, fin, data, .. } => {
                let first = self.first_unopened(id);
                match self.streams.on_stream_frame(&mut self.pool, id, offset, data, fin) {
                    Ok(()) => {}
                    Err(e) => return Err(stream_fault(e)),
                }
                self.push_opened(id, first);
                self.push(Ev::Readable(id));
            }
            Frame::MaxStreamData { id, max } => {
                match self.streams.on_max_stream_data(&self.pool, id, max) {
                    Ok(()) => self.push(Ev::Writable(id)),
                    Err(e) => return Err(stream_fault(e)),
                }
            }
            Frame::MaxStreams { limit } => self.streams.on_max_streams(limit),
            Frame::PathChallenge(d) => {
                if let Some(p) = self.paths.get_mut(pi) {
                    p.response = Some(d);
                }
            }
            Frame::PathResponse(d) => self.on_path_response(pi, d, now),
            Frame::Close { error } => self.on_peer_close(error),
            Frame::Datagram { data, .. } => {
                self.dgrams.on_datagram_frame(&mut self.pool, data);
                self.push(Ev::Datagram);
            }
            Frame::MtuProbeEcho { mtu } => self.mtu_raise(pi, mtu),
            Frame::Sleep => {
                if self.life.peer_asleep.is_none() {
                    self.life.peer_asleep = Some(now);
                    self.suspend_probes();
                    self.push(Ev::PeerAsleep);
                }
            }
            Frame::Rekey(rekey) => self.on_rekey(env, &rekey, old_key),
            Frame::Ready => self.push(Ev::Ready),
            Frame::NewTickets(batch) => {
                if !batch.entries().is_empty() {
                    self.events.push_tickets(batch);
                }
            }
            Frame::Extension { ty, body } => self.queue_ext(ty, body),
        }
        Ok(())
    }

    /// For a stream the peer opens: the index of the first stream of its kind not yet reported as opened.
    fn first_unopened(&self, id: u64) -> Option<u64> {
        (crate::stream::is_client_initiated(id) != self.client).then(|| self.streams.peer_opened(id))
    }

    /// Report every stream the arrival of `id` opened: the peer opens streams in order, so a stream that arrives
    /// first opens each lower one of its kind that was not opened yet.
    fn push_opened(&mut self, id: u64, first: Option<u64>) {
        for n in first.into_iter().flat_map(|f| f..=id >> 2) {
            self.push(Ev::Opened((n << 2) | (id & 3)));
        }
    }

    /// Copy an extension body into the bounded queue, with its type in front.
    fn queue_ext(&mut self, ty: u64, body: &[u8]) {
        let mut buf = [0u8; EXT_MAX];
        let head = varint::encode(ty, &mut buf).unwrap_or(0);
        let Some(dst) = buf.get_mut(head..head + body.len()) else { return };
        dst.copy_from_slice(body);
        if let Some(entry) = buf.get(..head + body.len()) {
            self.ext.on_datagram_frame(&mut self.pool, entry);
            self.push(Ev::Extension);
        }
    }

    fn on_ack(&mut self, pi: usize, now: u64, ack: &Ack<'_>) -> Result<(), Fault> {
        let mut out = Outcome::default();
        let (streams, pool, ctl) = (&mut *self.streams, &mut self.pool, &mut self.ctl);
        let result = self.rec.on_ack_received(now, ack.ranges(), |ev| apply(&ev, streams, pool, ctl, &mut out));
        match result {
            Ok(summary) => {
                self.rx.on_peer_ack(now, &ack.ranges());
                self.stats.packets_acked += u64::from(summary.acked_packets);
                if let Some(b) = out.big_acked
                    && let Some(p) = self.paths.get_mut(pi)
                {
                    p.mtu.big_acked = p.mtu.big_acked.max(Some(b));
                }
                if let Some(ping) = self.life.small_ping
                    && ack.ranges().any(|r| r.contains(&ping))
                {
                    self.life.small_ping = None;
                    self.mtu_black_hole(now);
                }
                self.mtu_black_hole_check(now);
                self.after_feedback(out, now);
                self.after_ack(now);
                Ok(())
            }
            Err(_) => Err(Fault::Violation(code::PROTOCOL_VIOLATION)),
        }
    }

    /// Fold recovery feedback into the loss average, the path MTU state and the counters.
    pub(super) fn after_feedback(&mut self, out: Outcome, now: u64) {
        self.stats.packets_lost += u64::from(out.lost_packets);
        self.loss.record(out.loss_lost, out.loss_acked);
        let active = self.paths.active;
        if let Some(size) = out.probe_acked.and_then(|s| u16::try_from(s).ok()) {
            self.mtu_raise(active, size);
        }
        if let Some(size) = out.probe_lost.and_then(|s| u16::try_from(s).ok()) {
            self.mtu_probe_lost(active, size, now);
        }
        if out.tickets_acked {
            self.ctl.tickets_pending = false;
        }
        if out.rekey_answer_lost {
            self.keys.requeue_answer();
        }
        if out.rekey_request_lost {
            self.keys.request_lost();
        }
    }

    fn after_ack(&mut self, now: u64) {
        self.update_path_rtts();
        self.rx.set_min_rtt(self.rec.rtt().min_rtt());
        if self.rec.pto_count() == 0 {
            self.degraded_told = false;
        }
        let cap = self.send_buffer_cap();
        while let Some(id) = self.streams.poll_writable(cap) {
            self.push(Ev::Writable(id));
        }
        let _ = now;
    }
}
