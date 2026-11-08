//! The send path: pick a path, then fill a datagram with the handshake flight, a ZeroRtt or a short packet, or a
//! CLOSE.
//!
//! Frames go into a packet in priority order: ACK, control frames (flow control, connection ids, tickets, READY,
//! SLEEP and WAKE, MTU echo), PATH frames, retransmissions, new stream data, then datagrams. Stream retransmissions
//! come before new data inside the stream layer's own queue. Every packet that carries anything is recorded in
//! recovery with the descriptors needed to send its content again.
//!
//! Invariants: a datagram never exceeds the path's datagram size or the output buffer, and an unvalidated path
//! never gets more than its amplification budget; data and datagrams leave only while the congestion window and the
//! pacer allow (probes, acknowledgements and path frames are exempt); a packet number is used by exactly one packet;
//! when the sent ring is full the frames just taken are given back to their owners and nothing is sent.

use core::ops::RangeInclusive;

use vinc_crypto::Provider;
use vinc_security::Env;
use vinc_security::amp::{FACTOR, OVERHEAD};
use vinc_wire::Writer;

use super::config::{MIN_MTU, PathId};
use super::ctl::{K_ACK, K_NEW_CID, K_READY, K_RETIRE, K_STREAM_CTL, K_TICKETS};
use super::{Connection, Phase};
use crate::frame::{ACK_DELAY_UNIT_NS, Frame, MAX_ACK_RANGES, ack_len, stream_overhead, ty, write_ack};
use crate::packet::{ConnId, LongHeader, LongType, PnLayout, ShortHeader, encode_pn, seal};
use crate::recovery::{FrameRef, FrameRefs, MAX_FRAME_REFS, Sent};
use crate::stream::{ControlFrame, StreamSource};

/// The datagram a [`Connection::poll_transmit`] call wrote into the caller's buffer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Transmit {
    /// The path to send it on.
    pub path: PathId,
    /// The bytes written: one datagram, or several of `segment_size` bytes (the last may be shorter) for GSO.
    pub len: usize,
    /// The size of each datagram of a batch; equal to `len` for a single datagram.
    pub segment_size: usize,
}

/// The overhead budgeted for a STREAM frame whose size is not known before the stream layer picks the chunk:
/// type, a 4-byte stream id, a 4-byte offset and a 2-byte length.
const STREAM_BUDGET: usize = 11;
/// The smallest room worth a frame.
const MIN_ROOM: usize = 24;
/// The space a long header can take at most, with an 8-byte length field and a 4-byte packet number.
const LONG_HDR_MAX: usize = 1 + 4 + 1 + 20 + 1 + 20 + 8 + 4;
/// Ack-only packets in a row before a PING makes the peer acknowledge them, so the sent ring drains.
const ACK_ONLY_RUN: u8 = 8;
/// The most stream bytes a repair packet re-carries.
const REPAIR_BYTES: u64 = 600;
/// Stream frames remembered as the tail of the last packet.
const TAIL: usize = 4;

/// The kind of packet being built.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Short,
    ZeroRtt,
}

/// What a packet is built for.
#[derive(Clone, Copy)]
#[allow(clippy::struct_excessive_bools, reason = "independent switches of one packet build")]
struct Fill {
    now: u64,
    ti: usize,
    allow_cc: bool,
    force: bool,
    probe: Option<usize>,
    repair: bool,
    min_total: usize,
}

/// What filling a packet found.
#[derive(Default)]
#[allow(clippy::struct_excessive_bools, reason = "independent facts about one packet")]
struct Filled {
    len: usize,
    refs: FrameRefs,
    eliciting: bool,
    ack: bool,
    data: bool,
    streams: bool,
    drained: bool,
    tail: [Option<(u64, u64, u32, bool)>; TAIL],
}

fn put(buf: &mut [u8], pos: &mut usize, f: &Frame<'_>) -> bool {
    let Some(dst) = buf.get_mut(*pos..) else { return false };
    let mut w = Writer::new(dst);
    if f.write(&mut w).is_err() {
        return false;
    }
    *pos += w.written().len();
    true
}

conn_impl! {
    /// Write the next datagram into `out`. Returns `None` when there is nothing to send now (call again after the
    /// next input or timeout). With `Config::max_gso` above 1, several same-size datagrams to one path may be
    /// batched in `out`; `segment_size` is the size of each.
    pub fn poll_transmit(&mut self, env: &mut Env<'_, P>, out: &mut [u8]) -> Option<Transmit> {
        self.paced_until = None;
        match self.phase {
            Phase::Closed | Phase::Draining => return None,
            Phase::Closing => return self.build_close(env, out),
            Phase::Handshaking | Phase::Connected => {}
        }
        if self.life.link_down.is_some() || (self.life.local_asleep.is_some() && self.life.sleep_tx == 0) {
            return None;
        }
        if self.phase == Phase::Connected
            && self.keys.wants_update(self.cfg.key_update_after)
            && self.keys.update_send(env.provider).is_ok()
        {
            self.stats.key_updates += 1;
        }
        let order = self.target_order();
        for ti in order.into_iter().flatten() {
            let Some(first) = self.build_datagram(env, ti, out) else { continue };
            let seg = first;
            let mut total = first;
            let max_seg = self.paths.get(ti).map_or(0, |p| usize::from(p.mtu.current)).min(out.len());
            let mut batched = 1;
            while batched < self.cfg.max_gso && total == seg * batched && seg == max_seg && self.phase == Phase::Connected {
                let Some(window) = out.get_mut(total..) else { break };
                if window.len() < seg {
                    break;
                }
                let Some(n) = self.build_datagram(env, ti, window) else { break };
                total += n;
                batched += 1;
                if n != seg {
                    break;
                }
            }
            let id = self.paths.get(ti)?.id;
            return Some(Transmit { path: id, len: total, segment_size: seg });
        }
        None
    }

    /// Candidate paths for the next datagram: standby paths with path-specific work, then the active path.
    fn target_order(&self) -> [Option<usize>; 5] {
        let mut order = [None; 5];
        let mut n = 0;
        for (i, p) in self.paths.iter() {
            let work = p.challenge.is_some_and(|c| c.send) || p.response.is_some() || p.echo.is_some();
            if i != self.paths.active && work && n < 4 {
                if let Some(s) = order.get_mut(n) {
                    *s = Some(i);
                }
                n += 1;
            }
        }
        if let Some(s) = order.get_mut(n) {
            *s = Some(self.paths.active);
        }
        order
    }

    /// How many bytes an unvalidated path may still be sent.
    pub(super) fn amp_room(&self, ti: usize) -> usize {
        match self.paths.get(ti) {
            Some(p) if !p.amp.is_validated() => {
                let allowed = p.amp.received().saturating_mul(FACTOR);
                usize::try_from(allowed.saturating_sub(p.amp.sent()).saturating_sub(OVERHEAD as u64)).unwrap_or(usize::MAX)
            }
            Some(_) => usize::MAX,
            None => 0,
        }
    }

    /// Build one datagram for path `ti` into `out`; returns its length.
    fn build_datagram(&mut self, env: &mut Env<'_, P>, ti: usize, out: &mut [u8]) -> Option<usize> {
        let now = env.now;
        let probe = self.probe_size(ti, now, out.len());
        let mtu = probe.unwrap_or_else(|| usize::from(self.paths.get(ti).map_or(MIN_MTU, |p| p.mtu.current))).min(out.len());
        let max_len = mtu.min(self.amp_room(ti));
        if max_len < MIN_ROOM {
            return None;
        }
        let window = out.get_mut(..max_len)?;
        let mut used = 0;
        let mut hs_len = 0;
        if self.hs.has_tx() {
            hs_len = self.write_handshake(ti, window);
            used = hs_len;
        }
        if hs_len == 0 && self.hs.padding_owed() > 0 {
            let n = self.hs.padding_owed().min(max_len);
            window.get_mut(..n)?.fill(0);
            self.hs.account(0, n);
            return self.finish_datagram(ti, n, now);
        }
        let can_app = self.can_build_app();
        if can_app
            && let Some(rest) = window.get_mut(used..)
            && let Some(n) = self.build_app(env, ti, rest, probe)
        {
            used += n;
        }
        if used == 0 {
            return None;
        }
        if hs_len > 0 {
            let app = used - hs_len;
            let room = if app == 0 { max_len - used } else { 0 };
            let pad = self.hs.account(hs_len, room);
            if pad > 0 {
                window.get_mut(used..used + pad)?.fill(0);
                used += pad;
            }
        }
        self.finish_datagram(ti, used, now)
    }

    fn finish_datagram(&mut self, ti: usize, len: usize, now: u64) -> Option<usize> {
        let p = self.paths.get_mut(ti)?;
        debug_assert!(p.amp.can_send(len as u64));
        p.amp.on_send(len as u64);
        self.stats.datagrams_sent += 1;
        self.stats.bytes_sent += len as u64;
        self.life.last_sent = now;
        Some(len)
    }

    /// The size of an MTU probe to send on path `ti` now, if one is due and the caller's buffer can hold it.
    fn probe_size(&self, ti: usize, now: u64, room: usize) -> Option<usize> {
        let p = self.paths.get(ti)?;
        let cc_ok = self.rec.cwnd_available() > 0 && self.rec.pacer().next_release(now) <= now;
        let idle = self.life.probes == 0 && self.life.peer_asleep.is_none() && self.life.local_asleep.is_none();
        if ti != self.paths.active || self.phase != Phase::Connected || !cc_ok || !idle || p.mtu.next_at > now {
            return None;
        }
        self.mtu_target(ti).map(usize::from).filter(|s| *s <= room)
    }

    /// Whether an application packet can be built now: 1-RTT keys, or early keys on a client mid-handshake.
    fn can_build_app(&self) -> bool {
        self.keys.send.is_some() || (self.client && self.phase == Phase::Handshaking && self.keys.early_send.is_some())
    }

    /// Write the next fragment of the handshake flight as a long Handshake packet at the start of `window`.
    fn write_handshake(&mut self, ti: usize, window: &mut [u8]) -> usize {
        let dcid = self.long_dcid(ti);
        let Some(scid) = self.cids.first_local() else { return 0 };
        let fixed = 1 + 4 + 1 + dcid.as_bytes().len() + 1 + scid.as_bytes().len();
        // Leave a short packet's worth of room behind the flight only when the flight is short.
        let room = window.len().saturating_sub(fixed + 2 + self.hs.fragment_overhead());
        let Some((total, off, bytes)) = self.hs.next_fragment(room) else { return 0 };
        let body_len = vinc_wire::varint::encoded_len(total as u64) + vinc_wire::varint::encoded_len(off as u64) + bytes.len();
        let header = LongHeader { ty: LongType::Handshake, dcid, scid, body_len };
        let mut w = Writer::new(window);
        let ok = header.write(&mut w, 0).is_ok()
            && w.put_varint(total as u64).is_ok()
            && w.put_varint(off as u64).is_ok()
            && w.put_slice(bytes).is_ok();
        if ok { w.written().len() } else { 0 }
    }

    /// The destination id of a long header: the peer's id once known, else the one the client invented.
    fn long_dcid(&self, ti: usize) -> ConnId {
        let _ = ti;
        self.cids.remote_cid(0).unwrap_or(self.odcid)
    }

    /// The peer's connection id for sending on path `ti`, claiming one if the path has none yet.
    fn path_dcid(&mut self, ti: usize) -> Option<ConnId> {
        let need = self.paths.get(ti)?.cid_seq.is_none_or(|s| self.cids.is_retired(s));
        if need {
            let claim = u8::try_from(ti).ok().and_then(|u| self.cids.claim_remote(u));
            self.paths.get_mut(ti)?.cid_seq = claim;
        }
        self.cids.remote_cid(self.paths.get(ti)?.cid_seq?)
    }

    /// Build an application packet (short, or ZeroRtt on an early client) at the start of `window`.
    fn build_app(&mut self, env: &mut Env<'_, P>, ti: usize, window: &mut [u8], probe: Option<usize>) -> Option<usize> {
        let now = env.now;
        let kind = if self.keys.send.is_some() { Kind::Short } else { Kind::ZeroRtt };
        let suspended_data = self.life.peer_asleep.is_some() || self.life.local_asleep.is_some();
        let cc_ok = self.rec.cwnd_available() > 0 && self.rec.pacer().next_release(now) <= now;
        if !cc_ok && self.rec.cwnd_available() > 0 {
            self.paced_until = Some(self.rec.pacer().next_release(now));
        }
        let probes = self.life.probes > 0;
        let keepalive_due = self.life.keepalive.is_some_and(|k| now.saturating_sub(self.life.last_sent) >= k)
            && self.phase == Phase::Connected;
        let force = probes || self.life.ping_owed || keepalive_due;
        let mut fill = Fill {
            now,
            ti,
            allow_cc: (cc_ok || probes) && !suspended_data,
            force,
            probe: None,
            repair: false,
            min_total: 0,
        };
        let on_active = ti == self.paths.active;
        fill.probe = probe.filter(|_| !probes);
        if on_active && self.life.repair_due && cc_ok {
            fill.repair = true;
        }
        let r = self.build_packet(env, window, kind, fill);
        if r.is_some() && probes {
            self.life.probes -= 1;
        }
        r
    }

    /// Build one packet of `kind` into `window` and send it through recovery. Returns its length.
    #[allow(clippy::too_many_lines, reason = "one linear sequence: size, fill, pad, header, record, seal, commit")]
    fn build_packet(&mut self, env: &mut Env<'_, P>, window: &mut [u8], kind: Kind, fill: Fill) -> Option<usize> {
        let now = fill.now;
        let ti = fill.ti;
        let p = env.provider;
        let pn = self.next_pn;
        let (pn_bytes, pn_len) = encode_pn(pn, self.rec.largest_acked()).ok()?;
        let dcid = if kind == Kind::Short { self.path_dcid(ti)? } else { self.long_dcid(ti) };
        let hdr_cap = match kind {
            Kind::Short => 1 + dcid.as_bytes().len() + pn_len,
            Kind::ZeroRtt => LONG_HDR_MAX,
        };
        let size_cap = fill.probe.unwrap_or(window.len()).min(window.len());
        if size_cap < hdr_cap + 16 + 4 {
            return None;
        }
        let payload_cap = size_cap - hdr_cap - 16;
        let mut fill = fill;
        if let Some(size) = fill.probe {
            fill.min_total = size;
        }
        let payload = window.get_mut(hdr_cap..hdr_cap + payload_cap)?;
        let mut filled = self.fill_frames(env, payload, &fill, pn);
        if filled.len == 0 || (!filled.eliciting && filled.ack && !self.rx.ack_due(now) && !fill.force && fill.probe.is_none()) {
            self.requeue(&filled.refs);
            return None;
        }
        // Pad so the header-protection sample exists and any minimum size holds.
        let mut payload_len = filled.len;
        // With GSO on, a packet that leaves more stream data queued is padded to the full size so the next one can
        // follow it in the same batch.
        let batchable = self.cfg.max_gso > 1 && filled.streams && !filled.drained;
        let want_total = if batchable { size_cap } else { fill.min_total };
        let min_payload = want_total.saturating_sub(hdr_cap + 16).max(4usize.saturating_sub(pn_len));
        if payload_len < min_payload {
            window.get_mut(hdr_cap + payload_len..hdr_cap + min_payload)?.fill(0);
            payload_len = min_payload;
        }
        // Lay out the header; a long header's length depends on the payload, so the payload moves up against it.
        let (header_len, layout) = match kind {
            Kind::Short => {
                let phase = self.keys.send.as_ref()?.phase;
                let mut w = Writer::new(window.get_mut(..hdr_cap)?);
                ShortHeader { key_phase: phase, dcid }.write(&mut w, pn_bytes.get(..pn_len)?).ok()?;
                (hdr_cap, PnLayout { pn_off: 1 + dcid.as_bytes().len(), pn_len, long: false })
            }
            Kind::ZeroRtt => {
                let scid = self.cids.first_local()?;
                let header = LongHeader { ty: LongType::ZeroRtt, dcid, scid, body_len: pn_len + payload_len + 16 };
                let mut head = [0u8; LONG_HDR_MAX];
                let mut w = Writer::new(&mut head);
                header.write(&mut w, pn_len).ok()?;
                let pn_off = w.written().len();
                w.put_slice(pn_bytes.get(..pn_len)?).ok()?;
                let hlen = w.written().len();
                window.copy_within(hdr_cap..hdr_cap + payload_len, hlen);
                window.get_mut(..hlen)?.copy_from_slice(head.get(..hlen)?);
                (hlen, PnLayout { pn_off, pn_len, long: true })
            }
        };
        let total = header_len + payload_len + 16;
        let sent = Sent {
            pn,
            time: now,
            size: u32::try_from(total).ok()?,
            ack_eliciting: filled.eliciting,
            in_flight: filled.eliciting,
            path: u8::try_from(ti).ok()?,
            is_repair: fill.repair && filled.streams,
            is_mtu_probe: fill.probe.is_some(),
            frames: filled.refs,
        };
        if self.rec.on_packet_sent(sent).is_err() {
            self.requeue(&filled.refs);
            return None;
        }
        let packet = window.get_mut(..total)?;
        let sealed = match kind {
            Kind::Short => {
                let k = self.keys.send.as_mut()?;
                seal(&mut k.pk, &k.hk, p, packet, layout, payload_len, pn)
            }
            Kind::ZeroRtt => {
                let k = self.keys.early_send.as_mut()?;
                seal(&mut k.pk, &k.hk, p, packet, layout, payload_len, pn)
            }
        };
        if sealed.is_err() {
            // Recovery will time the unsent packet out and send its content again.
            self.next_pn += 1;
            return None;
        }
        self.next_pn += 1;
        self.stats.packets_sent += 1;
        if filled.ack {
            self.rx.on_ack_sent(pn, now);
        }
        if filled.data
            && let Some(p) = self.paths.get_mut(ti)
        {
            p.last_data = now;
        }
        if let Some(p) = self.paths.get_mut(ti) {
            if filled.eliciting {
                p.mtu.last_size = u16::try_from(total).unwrap_or(u16::MAX);
            }
            if let Some(size) = fill.probe {
                p.mtu.inflight = u16::try_from(size).ok();
            }
        }
        if filled.eliciting {
            self.life.ping_owed = false;
            self.life.ack_only_run = 0;
        } else {
            self.life.ack_only_run = self.life.ack_only_run.saturating_add(1);
        }
        if filled.streams {
            self.after_stream_send(&mut filled, now, fill.repair);
        }
        Some(total)
    }

    /// Give frames that were taken for a packet that will not be sent back to their owners.
    fn requeue(&mut self, refs: &FrameRefs) {
        for f in refs {
            match *f {
                FrameRef::Stream { id, offset, len, fin } => self.streams.on_lost(id, offset, u64::from(len), fin),
                FrameRef::Control { kind, id } => self.control_unsent(kind, id),
            }
        }
    }

    fn control_unsent(&mut self, kind: u8, id: u64) {
        match kind {
            K_STREAM_CTL => {
                if let Some(f) = self.ctl.untrack(id) {
                    self.streams.on_control_lost(&f);
                }
            }
            K_NEW_CID => self.cids.new_lost(id),
            K_RETIRE => self.cids.retire_lost(id),
            K_TICKETS => self.ctl.tickets_pending = self.ctl.tickets.is_some(),
            K_READY => self.ctl.ready = true,
            _ => {}
        }
    }

    /// Arm the tail repair after a packet that drained the stream queue.
    fn after_stream_send(&mut self, filled: &mut Filled, now: u64, repaired: bool) {
        self.life.last_stream_tx = now;
        if repaired {
            self.life.repair_due = false;
            self.life.repair_at = None;
            self.stats.repairs += 1;
            return;
        }
        if filled.drained {
            self.life.tail = filled.tail;
            let srtt = if self.rec.rtt().has_sample() { self.rec.rtt().smoothed() } else { 0 };
            self.life.repair_at = Some(now.saturating_add(srtt.saturating_mul(2).max(10 * crate::recovery::MS)));
        } else {
            self.life.repair_at = None;
        }
    }

    /// Fill `payload` with frames; the caller seals it.
    fn fill_frames(&mut self, env: &mut Env<'_, P>, payload: &mut [u8], fill: &Fill, pn: u64) -> Filled {
        let now = fill.now;
        let ti = fill.ti;
        let mut out = Filled::default();
        let mut pos = 0usize;
        let cap = payload.len();
        // ACK.
        // Only the active path carries acknowledgements: an ACK makes a packet non-probing, and the peer would
        // follow it to a path that is only being checked.
        if self.rx.ack_pending() && ti == self.paths.active {
            let mut ranges: [RangeInclusive<u64>; MAX_ACK_RANGES] = core::array::from_fn(|_| 0..=0);
            let mut n = 0;
            for (slot, r) in ranges.iter_mut().zip(self.rx.ack_ranges(now)) {
                *slot = r;
                n += 1;
            }
            let delay = self.rx.ack_delay(now) / ACK_DELAY_UNIT_NS;
            if let Some(used) = ranges.get(..n)
                && let it = used.iter().cloned()
                && let Ok(len) = ack_len(delay, it.clone())
                && len <= cap - pos
                && let Some(dst) = payload.get_mut(pos..)
            {
                let mut w = Writer::new(dst);
                if write_ack(&mut w, delay, it).is_ok() {
                    pos += w.written().len();
                    out.ack = true;
                    let _ = out.refs.push(FrameRef::Control { kind: K_ACK, id: 0 });
                }
            }
        }
        if let Some(size) = fill.probe {
            let _ = put(payload, &mut pos, &Frame::Ping);
            out.eliciting = true;
            let _ = size;
            out.len = pos;
            return out;
        }
        // Control frames.
        self.fill_control(env, payload, &mut pos, &mut out, fill);
        // PATH frames.
        self.fill_path(env, payload, &mut pos, &mut out, ti, now);
        // Retransmissions and new stream data.
        if fill.allow_cc {
            if fill.repair {
                self.requeue_tail();
            }
            self.fill_streams(payload, &mut pos, &mut out, fill);
            self.fill_datagrams(payload, &mut pos, &mut out);
        }
        if fill.force && !out.eliciting && put(payload, &mut pos, &Frame::Ping) {
            out.eliciting = true;
        }
        if !out.eliciting && out.ack && self.life.ack_only_run >= ACK_ONLY_RUN && put(payload, &mut pos, &Frame::Ping) {
            out.eliciting = true;
        }
        let _ = pn;
        out.len = pos;
        out
    }

    fn fill_control(&mut self, env: &mut Env<'_, P>, payload: &mut [u8], pos: &mut usize, out: &mut Filled, fill: &Fill) {
        let _ = fill;
        let _ = env;
        if self.life.sleep_tx > 0 && put(payload, pos, &Frame::Sleep) {
            self.life.sleep_tx -= 1;
            out.eliciting = true;
        }
        if self.life.wake_tx && put(payload, pos, &Frame::Wake) {
            self.life.wake_tx = false;
            out.eliciting = true;
        }
        if let Some(mtu) = self.paths.get_mut(fill.ti).and_then(|p| p.echo.take()) {
            let _ = put(payload, pos, &Frame::MtuProbeEcho { mtu });
        }
        if self.ctl.ready && out.refs.len() < MAX_FRAME_REFS && put(payload, pos, &Frame::Ready) {
            self.ctl.ready = false;
            let _ = out.refs.push(FrameRef::Control { kind: K_READY, id: 0 });
            out.eliciting = true;
        }
        if self.ctl.tickets_pending
            && out.refs.len() < MAX_FRAME_REFS
            && let Some(batch) = self.ctl.tickets
            && put(payload, pos, &Frame::NewTickets(batch))
        {
            self.ctl.tickets_pending = false;
            let _ = out.refs.push(FrameRef::Control { kind: K_TICKETS, id: 0 });
            out.eliciting = true;
        }
        while let Some(entry) = self.ext.peek_send(&self.pool) {
            let Ok((ty, n)) = vinc_wire::varint::decode(entry) else {
                self.ext.pop_send(&mut self.pool);
                continue;
            };
            let f = Frame::Extension { ty, body: entry.get(n..).unwrap_or_default() };
            if f.encoded_len() > payload.len().saturating_sub(*pos) || !put(payload, pos, &f) {
                break;
            }
            self.ext.pop_send(&mut self.pool);
            out.eliciting = true;
        }
        while out.refs.len() < MAX_FRAME_REFS && self.cids.has_pending_new() {
            let room = payload.len() - *pos;
            let Some(n) = self.cids.next_new() else { break };
            let f = Frame::NewConnectionId { seq: n.seq, retire_prior_to: n.retire_prior_to, cid: n.cid, token: n.token };
            if f.encoded_len() > room || !put(payload, pos, &f) {
                self.cids.new_lost(n.seq);
                break;
            }
            let _ = out.refs.push(FrameRef::Control { kind: K_NEW_CID, id: n.seq });
            out.eliciting = true;
        }
        while out.refs.len() < MAX_FRAME_REFS && self.cids.has_pending_retire() {
            let Some(seq) = self.cids.next_retire() else { break };
            if !put(payload, pos, &Frame::RetireConnectionId { seq }) {
                self.cids.retire_lost(seq);
                break;
            }
            let _ = out.refs.push(FrameRef::Control { kind: K_RETIRE, id: seq });
            out.eliciting = true;
        }
        while out.refs.len() < MAX_FRAME_REFS && payload.len() - *pos >= MIN_ROOM {
            let Some(cf) = self.streams.pending_control() else { break };
            let Some(key) = self.ctl.track(cf) else {
                self.streams.on_control_lost(&cf);
                break;
            };
            if !put(payload, pos, &control_frame(&cf)) {
                self.ctl.untrack(key);
                self.streams.on_control_lost(&cf);
                break;
            }
            let _ = out.refs.push(FrameRef::Control { kind: K_STREAM_CTL, id: key });
            out.eliciting = true;
        }
    }

    fn fill_path(&mut self, env: &mut Env<'_, P>, payload: &mut [u8], pos: &mut usize, out: &mut Filled, ti: usize, now: u64) {
        let _ = env;
        let Some(p) = self.paths.get(ti).copied() else { return };
        if let Some(d) = p.response
            && put(payload, pos, &Frame::PathResponse(d))
        {
            if let Some(pm) = self.paths.get_mut(ti) {
                pm.response = None;
            }
            out.eliciting = true;
        }
        if let Some(c) = p.challenge
            && c.send
            && put(payload, pos, &Frame::PathChallenge(c.data))
        {
            let rto = self.challenge_rto(ti, c.tries);
            if let Some(ch) = self.paths.get_mut(ti).and_then(|pm| pm.challenge.as_mut()) {
                ch.sent_at = now;
                ch.tries += 1;
                ch.send = false;
                ch.retry_at = now.saturating_add(rto);
            }
            out.eliciting = true;
            // A challenge also proves the path carries a full-size datagram.
            let pad = usize::from(MIN_MTU).saturating_sub(*pos + 16 + 20);
            let pad = pad.min(payload.len().saturating_sub(*pos));
            if pad > 0 {
                let _ = put(payload, pos, &Frame::Padding { len: pad });
            }
        }
    }

    /// Mark the stream ranges of the last packet's tail lost so they are sent again as a repair.
    fn requeue_tail(&mut self) {
        let mut left = REPAIR_BYTES;
        for t in self.life.tail.into_iter().flatten() {
            let (id, offset, len, fin) = t;
            let take = u64::from(len).min(left);
            if take == 0 {
                break;
            }
            let fin = fin && take == u64::from(len);
            self.streams.on_lost(id, offset + u64::from(len) - take, take, fin);
            left -= take;
        }
        self.life.tail = [None; TAIL];
    }

    fn fill_streams(&mut self, payload: &mut [u8], pos: &mut usize, out: &mut Filled, fill: &Fill) {
        let mut repaired = 0u64;
        for _ in 0..16 {
            if out.refs.len() >= MAX_FRAME_REFS {
                out.drained = false;
                return;
            }
            let room = payload.len().saturating_sub(*pos);
            if room < MIN_ROOM {
                out.drained = false;
                return;
            }
            let mut budget = room - STREAM_BUDGET;
            if fill.repair {
                budget = budget.min(usize::try_from(REPAIR_BYTES.saturating_sub(repaired)).unwrap_or(0));
                if budget == 0 {
                    return;
                }
            }
            let Some(chunk) = self.streams.next_stream_frame(budget) else {
                out.drained = true;
                return;
            };
            let hdr = stream_overhead(chunk.id, chunk.offset, chunk.len, false);
            let end = *pos + hdr + chunk.len;
            let ok = end <= payload.len()
                && payload
                    .get_mut(*pos + hdr..end)
                    .is_some_and(|dst| self.streams.copy_out(&self.pool, &chunk, dst).is_ok())
                && payload.get_mut(*pos..*pos + hdr).is_some_and(|h| put_stream_header(h, &chunk));
            if !ok {
                self.streams.on_lost(chunk.id, chunk.offset, chunk.len as u64, chunk.fin);
                out.drained = false;
                return;
            }
            *pos = end;
            repaired += chunk.len as u64;
            let len32 = u32::try_from(chunk.len).unwrap_or(u32::MAX);
            let _ = out.refs.push(FrameRef::Stream { id: chunk.id, offset: chunk.offset, len: len32, fin: chunk.fin });
            if let Some(slot) = out.tail.iter_mut().find(|t| t.is_none()) {
                *slot = Some((chunk.id, chunk.offset, len32, chunk.fin));
            }
            out.eliciting = true;
            out.data = true;
            out.streams = true;
        }
        out.drained = false;
    }

    fn fill_datagrams(&mut self, payload: &mut [u8], pos: &mut usize, out: &mut Filled) {
        while let Some(d) = self.dgrams.peek_send(&self.pool) {
            let f = Frame::Datagram { data: d, implicit_len: false };
            if f.encoded_len() > payload.len().saturating_sub(*pos) || !put(payload, pos, &f) {
                break;
            }
            self.dgrams.pop_send(&mut self.pool);
            out.eliciting = true;
            out.data = true;
        }
    }

    /// A packet carrying CLOSE (once, and again in answer to packets that keep arriving).
    fn build_close(&mut self, env: &mut Env<'_, P>, out: &mut [u8]) -> Option<Transmit> {
        if !self.life.close_owed {
            return None;
        }
        let frame = self.life.close?;
        let ti = self.paths.active;
        let now = env.now;
        let p = env.provider;
        let dcid = self.path_dcid(ti)?;
        let pn = self.next_pn;
        let (pn_bytes, pn_len) = encode_pn(pn, self.rec.largest_acked()).ok()?;
        let hdr = 1 + dcid.as_bytes().len() + pn_len;
        let mtu = usize::from(self.paths.get(ti)?.mtu.current).min(out.len()).min(self.amp_room(ti));
        let payload = out.get_mut(hdr..mtu.checked_sub(16)?)?;
        let reason = frame.reason.as_bytes();
        let reason = reason.get(..reason.len().min(64)).unwrap_or_default();
        let f = if frame.app {
            Frame::ApplicationClose { error: frame.error, reason }
        } else {
            Frame::Close { error: frame.error, frame_type: 0, reason }
        };
        let mut pos = 0;
        if !put(payload, &mut pos, &f) {
            return None;
        }
        let pad = 4usize.saturating_sub(pn_len + pos);
        if pad > 0 {
            payload.get_mut(pos..pos + pad)?.fill(0);
            pos += pad;
        }
        let phase = self.keys.send.as_ref()?.phase;
        ShortHeader { key_phase: phase, dcid }.write(&mut Writer::new(out.get_mut(..hdr)?), pn_bytes.get(..pn_len)?).ok()?;
        let k = self.keys.send.as_mut()?;
        let layout = PnLayout { pn_off: 1 + dcid.as_bytes().len(), pn_len, long: false };
        let len = seal(&mut k.pk, &k.hk, p, out, layout, pos, pn).ok()?;
        self.next_pn += 1;
        self.life.close_owed = false;
        self.stats.packets_sent += 1;
        let path = self.paths.get(ti)?.id;
        self.finish_datagram(ti, len, now)?;
        Some(Transmit { path, len, segment_size: len })
    }
}

/// The frame for a stream-layer control description.
fn control_frame(cf: &ControlFrame) -> Frame<'static> {
    match *cf {
        ControlFrame::MaxData(max) => Frame::MaxData { max },
        ControlFrame::MaxStreamData { id, max } => Frame::MaxStreamData { id, max },
        ControlFrame::MaxStreams { bidi, max } => Frame::MaxStreams { bidi, max },
        ControlFrame::DataBlocked(limit) => Frame::DataBlocked { limit },
        ControlFrame::StreamDataBlocked { id, limit } => Frame::StreamDataBlocked { id, limit },
        ControlFrame::StreamsBlocked { bidi, limit } => Frame::StreamsBlocked { bidi, limit },
        ControlFrame::ResetStream {
            id,
            error_code,
            final_size,
        } => Frame::ResetStream {
            id,
            error: error_code,
            final_size,
        },
        ControlFrame::StopSending { id, error_code } => Frame::StopSending { id, error: error_code },
    }
}

/// Write the header of a STREAM frame with an explicit length into exactly `dst`, which was sized with
/// [`stream_overhead`]. The encoding is the canonical one of [`Frame::write`]: OFF is set exactly when the offset is
/// not 0.
fn put_stream_header(dst: &mut [u8], c: &crate::stream::StreamChunk) -> bool {
    let flags = (if c.offset == 0 { 0 } else { ty::STREAM_OFF }) | ty::STREAM_LEN | u64::from(c.fin);
    let mut w = Writer::new(dst);
    let ok = w.put_varint(ty::STREAM | flags).is_ok()
        && w.put_varint(c.id).is_ok()
        && (c.offset == 0 || w.put_varint(c.offset).is_ok())
        && w.put_varint(c.len as u64).is_ok();
    ok && w.remaining() == 0
}
