//! The receive path: split a datagram into packets, unprotect and open each, and dispatch its frames to the layers.
//!
//! Order of work for a packet: header (route by connection id), header unprotection, key choice by phase bit,
//! authentication, a first pass over the frames (what the packet is: ack-eliciting, probing, a ping, stream bytes)
//! and the duplicate check, a second pass that applies each frame, and last the bookkeeping that depends on the whole
//! packet (the received-packet record, migration, the handshake confirmation).
//!
//! Invariants: nothing is acted on before it authenticated, so a forged packet changes nothing (a new path is added
//! only after a packet from it authenticated); a packet whose frames could not be stored for lack of memory is not
//! recorded as received, so the peer sends it again; a stateless reset is looked for only when a short packet failed
//! to open.

use vinc_crypto::Provider;
use vinc_security::{Env, ResponderStores};
use vinc_wire::varint;

use super::config::{MIN_MTU, PathId, PathInfo};
use super::ctl::{Outcome, apply};
use super::event::{Drop, Ev, code};
use super::path::PathState;
use super::{Connection, Phase};
use crate::frame::{ACK_DELAY_UNIT_NS, Ack, Frame, FrameIter};
use crate::packet::{
    Header, LongHeader, LongType, Packet, PacketError, decode_pn, is_stateless_reset, open, packets, unprotect_header,
};
use crate::recovery::{RecoveryError, RxOutcome, RxPacket};
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
}

/// Why a frame could not be applied.
#[derive(Debug, Clone, Copy)]
enum Fault {
    /// A rule was broken: close with this code.
    Violation(u64, &'static str),
    /// Memory is short: drop the packet unacknowledged.
    Shortage,
}

fn stream_fault(e: StreamError) -> Fault {
    match e {
        StreamError::StreamLimit | StreamError::TableFull => Fault::Violation(code::STREAM_LIMIT, "too many streams"),
        StreamError::StreamState | StreamError::UnknownStream => {
            Fault::Violation(code::STREAM_STATE, "frame does not fit the stream")
        }
        StreamError::FlowControl => Fault::Violation(code::FLOW_CONTROL, "flow control credit exceeded"),
        StreamError::FinalSize => Fault::Violation(code::FINAL_SIZE, "final size violated"),
        StreamError::Exhausted | StreamError::Fragmented => Fault::Shortage,
        _ => Fault::Violation(code::PROTOCOL_VIOLATION, "stream data refused"),
    }
}

/// What a first pass over the frames of a packet found.
#[derive(Debug, Default, Clone, Copy)]
#[allow(clippy::struct_excessive_bools, reason = "independent facts about one packet")]
struct Props {
    eliciting: bool,
    probing: bool,
    ping: bool,
    padding: bool,
    stream_bytes: u32,
}

fn scan(payload: &[u8]) -> Result<Props, crate::frame::FrameError> {
    let mut p = Props {
        probing: true,
        ..Props::default()
    };
    for f in FrameIter::new(payload) {
        match f? {
            Frame::Padding { .. } => p.padding = true,
            Frame::Ack(_) => p.probing = false,
            Frame::Ping => {
                p.eliciting = true;
                p.ping = true;
                p.probing = false;
            }
            Frame::PathChallenge(_) | Frame::PathResponse(_) | Frame::NewConnectionId { .. } => p.eliciting = true,
            Frame::Stream { data, .. } => {
                p.eliciting = true;
                p.probing = false;
                p.stream_bytes = p
                    .stream_bytes
                    .saturating_add(u32::try_from(data.len()).unwrap_or(u32::MAX));
            }
            _ => {
                p.eliciting = true;
                p.probing = false;
            }
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
            Phase::Closed => return Err(Drop::Closed),
            Phase::Draining => return Err(Drop::Draining),
            Phase::Closing => self.on_packet_while_closing(),
            _ => {}
        }
        let dlen = dgram.len();
        let mut known = self.paths.find(path);
        if known.is_none() && !self.client && self.paths.iter().next().is_none() {
            known = self.new_path_slot(path, PathInfo::default(), now);
        }
        if let Some(p) = known.and_then(|i| self.paths.get_mut(i)) {
            p.amp.on_receive(dlen as u64);
        }
        self.stats.datagrams_received += 1;
        self.stats.bytes_received += dlen as u64;
        let mut ctx = Rx { path_id: path, path: known, dlen, now };
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
            if matches!(self.phase, Phase::Closed | Phase::Draining) {
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
                LongType::Retry => Err(Drop::Empty),
            },
            Header::Short { dcid } => {
                if !self.cids.is_local(&dcid) {
                    // A stateless reset names an id we never issued.
                    if is_stateless_reset(pkt.bytes, self.cids.peer_tokens()) {
                        self.push(Ev::StatelessReset);
                        self.silent_close(super::CloseReason::StatelessReset);
                        return Ok(());
                    }
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
        if self.phase != Phase::Handshaking {
            return Err(Drop::Empty);
        }
        let Some(pi) = ctx.path else { return Err(Drop::NoPath) };
        if self.client && self.cids.first_local() != Some(header.dcid) {
            return Err(Drop::Unroutable);
        }
        let first_remote = self.cids.remote_cid(0).is_none();
        self.cids.set_first_remote(header.scid);
        if first_remote
            && let (Some(p), Ok(slot)) = (self.paths.get_mut(pi), u8::try_from(pi))
            && p.cid_seq.is_none()
        {
            p.cid_seq = self.cids.claim_remote(slot);
        }
        if let Some(p) = self.paths.get_mut(pi) {
            p.last_heard = ctx.now;
        }
        self.note_heard(ctx.now);
        let body = bytes.get(header_len..).ok_or(Drop::Malformed(PacketError::Length))?;
        let Some(len) = self.hs.on_fragment(body) else { return Ok(()) };
        let r = self.hs.feed(env, stores, len);
        self.pump(env);
        r.map_err(Drop::Handshake)
    }

    fn on_zero_rtt(&mut self, env: &mut Env<'_, P>, ctx: &mut Rx, pn_off: usize, bytes: &mut [u8]) -> Result<(), Drop> {
        let p = env.provider;
        let Some(dir) = self.keys.early_recv.as_mut() else { return Err(Drop::Undecryptable) };
        let un = unprotect_header(&dir.hk, p, bytes, pn_off, true).map_err(|_| Drop::Undecryptable)?;
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
        let largest = self.rx.largest();
        let mut failed = false;
        let mut opened = None;
        let mut promoted = false;
        if let Some(rk) = self.keys.recv.as_mut() {
            rk.expire(now);
            match unprotect_header(&rk.hk, p, bytes, pn_off, false) {
                Ok(un) => {
                    let pn_est = decode_pn(un.truncated, un.pn_len, largest);
                    match rk.select(p, un.key_phase(), pn_est) {
                        Ok(sel) => {
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
                Err(_) => failed = true,
            }
        }
        let Some(opened) = opened.filter(|_| !failed) else {
            self.stats.undecryptable += 1;
            if is_stateless_reset(bytes, self.cids.peer_tokens()) {
                self.push(Ev::StatelessReset);
                self.silent_close(super::CloseReason::StatelessReset);
            }
            return Err(Drop::Undecryptable);
        };
        if promoted {
            self.stats.key_updates += 1;
            if self.keys.behind_peer() && self.keys.update_send(p).is_err() {
                self.violation(now, code::INTERNAL, "key update failed");
                return Err(Drop::Closed);
            }
        }
        // A 1-RTT packet authenticated: the early keys have done their job.
        self.keys.early_recv = None;
        let payload = bytes.get(opened.payload_start..opened.payload_end).ok_or(Drop::Undecryptable)?;
        self.process_payload(env, ctx, opened.pn, payload)
    }

    /// Authenticated packet `pn` with `payload` frames.
    fn process_payload(&mut self, env: &mut Env<'_, P>, ctx: &mut Rx, pn: u64, payload: &[u8]) -> Result<(), Drop> {
        let now = ctx.now;
        let Ok(props) = scan(payload) else {
            self.violation(now, code::FRAME_ENCODING, "malformed frame");
            return Err(Drop::Closed);
        };
        if self.rx.contains(pn) {
            self.stats.duplicates += 1;
            return Err(Drop::Duplicate);
        }
        let pi = if let Some(i) = ctx.path {
            i
        } else {
            let i = self.new_path_slot(ctx.path_id, PathInfo::default(), now).ok_or(Drop::NoPath)?;
            ctx.path = Some(i);
            if let Some(p) = self.paths.get_mut(i) {
                p.amp.on_receive(ctx.dlen as u64);
            }
            if self.phase == Phase::Connected {
                self.start_challenge(env, i, false);
            }
            i
        };
        self.stats.packets_received += 1;
        self.note_heard(now);
        self.rec.note_peer_activity(now);
        if let Some(p) = self.paths.get_mut(pi) {
            p.last_heard = now;
        }
        if self.phase == Phase::Closing {
            for f in FrameIter::new(payload).flatten() {
                match f {
                    Frame::Close { error, .. } => self.on_peer_close(now, false, error),
                    Frame::ApplicationClose { error, .. } => self.on_peer_close(now, true, error),
                    _ => {}
                }
            }
            return Ok(());
        }
        for f in FrameIter::new(payload) {
            let Ok(f) = f else { break };
            if let Err(fault) = self.on_frame(env, pi, now, f) {
                return match fault {
                    Fault::Violation(c, why) => {
                        self.violation(now, c, why);
                        Err(Drop::Closed)
                    }
                    Fault::Shortage => Err(Drop::Empty),
                };
            }
            if matches!(self.phase, Phase::Closed | Phase::Draining) {
                return Ok(());
            }
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
        if !props.probing {
            self.on_nonprobing(pi, pn);
        }
        if self.client && self.phase == Phase::Connected && !self.confirmed {
            self.confirmed = true;
            self.hs.confirm();
        }
        Ok(())
    }

    /// The server follows the highest-numbered non-probing packet to its path.
    fn on_nonprobing(&mut self, pi: usize, pn: u64) {
        if self.highest_nonprobing.is_some_and(|h| pn <= h) {
            return;
        }
        self.highest_nonprobing = Some(pn);
        if self.client || pi == self.paths.active || self.phase != Phase::Connected {
            return;
        }
        match self.paths.get(pi).map(|p| p.state) {
            Some(PathState::Validated) => self.switch_active(pi),
            Some(PathState::Unvalidated) => self.migrate_to = Some(pi),
            _ => {}
        }
    }

    fn on_frame(&mut self, env: &mut Env<'_, P>, pi: usize, now: u64, f: Frame<'_>) -> Result<(), Fault> {
        match f {
            Frame::Padding { .. } | Frame::Ping => {}
            Frame::Ack(ack) => self.on_ack(pi, now, &ack)?,
            Frame::ResetStream { id, error, final_size } => {
                let new = self.is_new_peer_stream(id);
                self.streams.on_reset_stream(&mut self.pool, id, error, final_size).map_err(stream_fault)?;
                if new {
                    self.push(Ev::Opened(id));
                }
                self.push(Ev::Reset(id, error));
            }
            Frame::StopSending { id, error } => {
                self.streams.on_stop_sending(&mut self.pool, id, error).map_err(stream_fault)?;
                self.push(Ev::Stopped(id, error));
            }
            Frame::NewToken { token } => self.queue_ext(crate::frame::ty::NEW_TOKEN, token),
            Frame::Stream { id, offset, fin, data, .. } => {
                let new = self.is_new_peer_stream(id);
                self.streams.on_stream_frame(&mut self.pool, id, offset, data, fin).map_err(stream_fault)?;
                if new {
                    self.push(Ev::Opened(id));
                }
                self.push(Ev::Readable(id));
            }
            Frame::MaxData { max } => self.streams.on_max_data(max),
            Frame::MaxStreamData { id, max } => {
                self.streams.on_max_stream_data(id, max).map_err(stream_fault)?;
                self.push(Ev::Writable(id));
            }
            Frame::MaxStreams { bidi, max } => self.streams.on_max_streams(bidi, max),
            Frame::DataBlocked { limit } => self.streams.on_data_blocked(limit),
            Frame::StreamDataBlocked { id, limit } => {
                self.streams.on_stream_data_blocked(id, limit).map_err(stream_fault)?;
            }
            Frame::StreamsBlocked { bidi, limit } => self.streams.on_streams_blocked(bidi, limit),
            Frame::NewConnectionId { seq, retire_prior_to, cid, token } => {
                self.cids
                    .on_new_remote(seq, retire_prior_to, cid, token)
                    .map_err(|()| Fault::Violation(code::CONNECTION_ID, "connection id limit exceeded"))?;
                self.reassign_retired_cids();
            }
            Frame::RetireConnectionId { seq } => {
                if self.cids.on_retire(seq) {
                    let (len, key) = (self.cfg.cid_len, self.cfg.reset_key);
                    // A failing generator leaves the peer with fewer ids; the next retirement tries again.
                    let _ = self.cids.issue(env, len, &key, NP);
                }
            }
            Frame::PathChallenge(d) => {
                if let Some(p) = self.paths.get_mut(pi) {
                    p.response = Some(d);
                }
            }
            Frame::PathResponse(d) => self.on_path_response(pi, d, now),
            Frame::Close { error, .. } => self.on_peer_close(now, false, error),
            Frame::ApplicationClose { error, .. } => self.on_peer_close(now, true, error),
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
            Frame::Wake => {
                if self.life.peer_asleep.take().is_some() {
                    self.push(Ev::PeerAwake);
                }
                self.suspend_probes();
                self.flush_in_flight(now);
            }
            Frame::Ready => self.push(Ev::Ready),
            Frame::NewTickets(batch) => {
                if self.client && !batch.entries().is_empty() {
                    self.push(Ev::Tickets(batch));
                }
            }
            Frame::Extension { ty, body } => self.queue_ext(ty, body),
        }
        Ok(())
    }

    fn is_new_peer_stream(&self, id: u64) -> bool {
        crate::stream::is_client_initiated(id) != self.client && self.streams.recv_status(id).is_none()
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

    /// A retired peer id may still be the one a path sends with: move such paths to a fresh id.
    fn reassign_retired_cids(&mut self) {
        for i in 0..NP {
            let Some(seq) = self.paths.get(i).and_then(|p| p.cid_seq) else { continue };
            if !self.cids.is_retired(seq) {
                continue;
            }
            let fresh = u8::try_from(i).ok().and_then(|u| self.cids.claim_remote(u));
            if let Some(p) = self.paths.get_mut(i) {
                p.cid_seq = fresh;
            }
        }
    }

    fn on_ack(&mut self, pi: usize, now: u64, ack: &Ack<'_>) -> Result<(), Fault> {
        let mut out = Outcome::default();
        let delay = ack.delay().saturating_mul(ACK_DELAY_UNIT_NS);
        let (streams, pool, ctl, cids, rx) = (&mut *self.streams, &mut self.pool, &mut self.ctl, &mut self.cids, &mut self.rx);
        let result = self.rec.on_ack_received(now, ack.ranges(), delay, |ev| apply(&ev, now, streams, pool, ctl, cids, rx, &mut out));
        match result {
            Ok(summary) => {
                self.stats.packets_acked += u64::from(summary.acked_packets);
                self.after_feedback(out, now);
                self.after_ack(pi, now);
                Ok(())
            }
            Err(RecoveryError::AckOfUnsentPacket) => Err(Fault::Violation(code::PROTOCOL_VIOLATION, "acknowledged a packet never sent")),
            Err(_) => Err(Fault::Violation(code::PROTOCOL_VIOLATION, "malformed acknowledgement")),
        }
    }

    /// Fold recovery feedback into the loss average, the path MTU state and the counters.
    pub(super) fn after_feedback(&mut self, out: Outcome, now: u64) {
        self.stats.packets_lost += u64::from(out.lost_packets);
        self.loss.record(out.lost_packets, out.acked_packets);
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
    }

    fn after_ack(&mut self, pi: usize, now: u64) {
        let rtt = self.rec.rtt();
        if rtt.has_sample() && pi == self.paths.active
            && let Some(p) = self.paths.active_mut()
        {
            p.rtt = Some(self.rec.rtt().smoothed());
        }
        self.rx.set_min_rtt(self.rec.rtt().min_rtt());
        if self.rec.pto_count() == 0 {
            self.degraded_told = false;
        }
        if self.rec.bytes_in_flight() == 0 {
            self.life.repair_at = None;
            self.life.repair_due = false;
        }
        if self.client {
            self.evaluate_paths();
        }
        let _ = now;
    }
}
