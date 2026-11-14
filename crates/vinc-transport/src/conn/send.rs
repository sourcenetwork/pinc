//! The send path: pick a path, then fill a datagram with the handshake flight, a ZeroRtt or a short packet, or a
//! CLOSE.
//!
//! Frames go into a packet in priority order: ACK, control frames (SLEEP and WAKE, MTU echo, READY, tickets, REKEY,
//! extension frames, stream credit and resets), PATH frames, then stream data in order of urgency (each stream's
//! retransmissions before its new data) and datagrams, then the credit a stream gives back once its answer has left,
//! and last a PING if one is forced. The last STREAM frame of a packet leaves its length out.
//! Every packet that carries anything is recorded in recovery with the descriptors needed to send its content again.
//!
//! Invariants: a datagram never exceeds the path's datagram size or the output buffer, and an unvalidated path
//! never gets more than its amplification budget (each datagram counts 48 bytes more than its size, against the path
//! and against the whole session); data and datagrams leave only while the congestion window and the pacer allow
//! (probes, acknowledgements and path frames are exempt); a packet number is used by exactly one packet; when the
//! sent ring is full the frames just taken are given back to their owners and nothing is sent.
//!
//! The tail repair fill (`fill_repair`) is in `repair`, and the CLOSE packet (`build_close`) is in `close`.

use core::ops::RangeInclusive;

use vinc_crypto::Provider;
use vinc_security::AmpBudget;
use vinc_security::Env;
use vinc_security::amp::{FACTOR, OVERHEAD};
use vinc_wire::Writer;

use super::config::{MIN_MTU, PROBE_MTU, PathId};
use super::ctl::{EXT_BODY_MAX, K_EXT, K_READY, K_REKEY, K_STREAM_CTL, K_TICKETS};
use super::event::Ev;
use super::{Connection, Phase};
use crate::frame::{Frame, MAX_ACK_RANGES, ack_len, stream_overhead, ty, write_ack};
use crate::packet::{ConnId, LongHeader, LongType, PN_LEN_BASE, PnLayout, ShortHeader, encode_pn, seal};
use crate::recovery::{FrameRef, FrameRefs, MAX_FRAME_REFS, PathKind, REPAIR_FRAME_BYTES, Sent};
use crate::stream::{ControlFrame, StreamSource};

#[cfg(feature = "trace")]
pub(super) mod trace;

mod close;
mod repair;

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
const LONG_HDR_MAX: usize = 1 + 1 + 1 + 20 + 1 + 20 + 8 + 4;
/// The room a whole first handshake flight needs besides the flight itself (long header and fragment varints).
const FLIGHT_OVERHEAD: usize = 64;
// The Initial padding rule counts a Reply that a whole first flight carries as one datagram, and covers it cut into
// minimum-size datagrams only with short ids (see `vinc_security::message::SPLIT_CID_MAX`).
const _: () = assert!(vinc_security::message::WHOLE_REPLY_MAX == PROBE_MTU as usize - FLIGHT_OVERHEAD);
const _: () = assert!(vinc_security::message::MIN_DATAGRAM == MIN_MTU as usize);
const _: () = assert!(super::config::Config::new().cid_len <= vinc_security::message::SPLIT_CID_MAX);

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
    /// The packet is the probe timeout's PING: nothing else but an acknowledgement goes in, and it is not recorded.
    ping_only: bool,
    probe: Option<usize>,
    /// The packet re-carries the stream frames of this packet.
    repair: Option<u64>,
    min_total: usize,
}

/// What filling a packet found.
#[derive(Default)]
#[allow(clippy::struct_excessive_bools, reason = "independent facts about one packet")]
struct Filled {
    len: usize,
    refs: FrameRefs,
    eliciting: bool,
    /// Whether something that is recorded in flight rides in the packet (anything but path validation, SLEEP, WAKE
    /// and the probe timeout's PING).
    tracked: bool,
    ack: bool,
    data: bool,
    streams: bool,
    drained: bool,
    /// Every stream frame of the packet could be re-carried by a tail repair.
    plain: bool,
    /// A stream frame of the packet could not be (too long, or backed by a value source).
    ineligible: bool,
    /// Where the last STREAM frame starts, the size of its header, and where the packet's frames end.
    last_stream: Option<(usize, usize)>,
}

impl Filled {
    /// Something recorded in flight rides in the packet.
    fn strong(&mut self) {
        self.eliciting = true;
        self.tracked = true;
    }

    /// The packet needs an acknowledgement but carries only frames that are never recorded in flight.
    fn weak(&mut self) {
        self.eliciting = true;
    }
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
        self.life.clock = env.now;
        match self.phase {
            Phase::Closed => return None,
            Phase::Closing => return self.build_close(env, out),
            Phase::Handshaking | Phase::Connected => {}
        }
        self.apply_app_writes(env.now);
        if self.life.link_down.is_some() || (self.life.local_asleep.is_some() && self.life.sleep_tx == 0) {
            return None;
        }
        self.roll_tick(env);
        self.fan_step();
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
    fn target_order(&self) -> [Option<usize>; 6] {
        let mut order = [None; 6];
        let mut n = 0;
        if let Some(i) = self.fan_target.filter(|i| *i != self.paths.active) {
            if let Some(s) = order.first_mut() {
                *s = Some(i);
            }
            n = 1;
        }
        for (i, p) in self.paths.iter() {
            let work = p.send_challenge || p.send_ping || p.response.is_some() || p.echo.is_some();
            if i != self.paths.active && Some(i) != self.fan_target && work && n < 5 {
                if let Some(s) = order.get_mut(n) {
                    *s = Some(i);
                }
                n += 1;
            }
        }
        let skip_active = self.flight_skips_primary()
            && (self.fan_target.is_some_and(|t| t != self.paths.active) || self.fan_set == 0);
        if !skip_active && let Some(s) = order.get_mut(n) {
            *s = Some(self.paths.active);
        }
        order
    }

    /// How many bytes an unvalidated path, and an unvalidated session, may still be sent.
    pub(super) fn amp_room(&self, ti: usize) -> usize {
        let left = |b: &AmpBudget| {
            if b.is_validated() {
                return usize::MAX;
            }
            let allowed = b.received().saturating_mul(FACTOR);
            usize::try_from(allowed.saturating_sub(b.sent()).saturating_sub(OVERHEAD as u64)).unwrap_or(usize::MAX)
        };
        match self.paths.get(ti) {
            // Once the session is validated its peer is known to hold the keys, so a path it moved to is not limited by
            // what arrived on it: the budget would be spent before the challenge that validates the path is answered.
            Some(_) if self.sess_amp.is_validated() => usize::MAX,
            Some(p) => left(&p.amp).min(left(&self.sess_amp)),
            None => 0,
        }
    }

    /// Build one datagram for path `ti` into `out`; returns its length.
    fn build_datagram(&mut self, env: &mut Env<'_, P>, ti: usize, out: &mut [u8]) -> Option<usize> {
        let now = env.now;
        let probe = self.probe_size(ti, now, out.len());
        let path_mtu = self.paths.get(ti).map_or(MIN_MTU, |p| p.mtu.current);
        let whole = self.cfg.flight_split
            && self.hs.whole_len().is_some_and(|n| n + FLIGHT_OVERHEAD <= usize::from(PROBE_MTU));
        let base = if whole {
            let iface = self.paths.get(ti).map_or(MIN_MTU, |p| p.info.interface_mtu);
            usize::from(path_mtu.max(PROBE_MTU.min(iface)))
        } else {
            usize::from(path_mtu)
        };
        let mtu = probe.unwrap_or(base).min(out.len());
        let max_len = mtu.min(self.amp_room(ti));
        if max_len < MIN_ROOM {
            return None;
        }
        let window = out.get_mut(..max_len)?;
        let mut used = 0;
        let mut hs_len = 0;
        if self.hs.has_tx() {
            hs_len = self.write_handshake(window);
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

    /// Count a datagram against both amplification budgets (its size and 48 bytes of overhead) and note the send.
    fn finish_datagram(&mut self, ti: usize, len: usize, now: u64) -> Option<usize> {
        let charge = (len + OVERHEAD) as u64;
        let p = self.paths.get_mut(ti)?;
        debug_assert!(self.sess_amp.is_validated() || p.amp.can_send(len as u64));
        p.amp.on_send(charge);
        p.last_tx = now;
        self.sess_amp.on_send(charge);
        self.stats.datagrams_sent += 1;
        self.stats.bytes_sent += len as u64;
        self.life.last_sent = now;
        Some(len)
    }

    /// The size of an MTU probe to send on path `ti` now, if one is due and the caller's buffer can hold it.
    fn probe_size(&self, ti: usize, now: u64, room: usize) -> Option<usize> {
        let cc_ok = self.rec.can_send() && self.rec.pacer().next_release(now) <= now;
        let idle = self.life.probes == 0 && self.life.local_asleep.is_none();
        if ti != self.paths.active || self.phase != Phase::Connected || !cc_ok || !idle {
            return None;
        }
        self.mtu_target(ti, now).map(usize::from).filter(|s| *s <= room)
    }

    /// Whether an application packet can be built now: 1-RTT keys, or early keys on a client mid-handshake.
    fn can_build_app(&self) -> bool {
        self.keys.send.is_some() || self.early_client()
    }

    /// Whether this is a dialing side that resumes and still sends its data as early data.
    pub(super) fn early_client(&self) -> bool {
        self.client && self.phase == Phase::Handshaking && self.keys.early_send.is_some()
    }

    /// Write the next fragment of the handshake flight as a long Handshake packet at the start of `window`.
    fn write_handshake(&mut self, window: &mut [u8]) -> usize {
        let dcid = self.long_dcid();
        let scid = self.cids.first_local();
        let fixed = 1 + 1 + 1 + dcid.as_bytes().len() + 1 + scid.as_bytes().len();
        // Leave a short packet's worth of room behind the flight only when the flight is short.
        let room = window.len().saturating_sub(fixed + 2 + self.hs.fragment_overhead());
        let Some((total, off, bytes)) = self.hs.next_fragment(&self.pool, room) else { return 0 };
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
    fn long_dcid(&self) -> ConnId {
        self.cids.first_remote().unwrap_or(self.odcid)
    }

    /// The peer's connection id for sending on path `ti`, claimed the first time the path sends. The path keeps it
    /// while the peer answered on it or is still known to accept it, and claims again once the peer's window moved
    /// past an id that never got an answer.
    fn path_dcid(&mut self, ti: usize) -> Option<ConnId> {
        let p = self.paths.get(ti)?;
        if let Some(d) = p.dcid
            && (p.dcid_seen || self.cids.remote_usable(p.dcid_index))
        {
            return Some(d);
        }
        let (index, cid) = self.cids.claim_remote()?;
        let pn = self.next_pn;
        let p = self.paths.get_mut(ti)?;
        p.dcid = Some(cid);
        p.dcid_index = index;
        p.dcid_pn = pn;
        p.dcid_seen = false;
        Some(cid)
    }

    /// A packet with number `pn` was acknowledged on path slot `slot`: if it was sent with the path's current id, the
    /// peer accepts that id.
    pub(super) fn confirm_dcid(&mut self, slot: usize, pn: u64) {
        let Some(p) = self.paths.get_mut(slot) else { return };
        if p.dcid_seen || p.dcid.is_none() || pn < p.dcid_pn {
            return;
        }
        p.dcid_seen = true;
        let index = p.dcid_index;
        self.cids.confirm_remote(index);
    }

    /// Build an application packet (short, or ZeroRtt on an early client) at the start of `window`.
    fn build_app(&mut self, env: &mut Env<'_, P>, ti: usize, window: &mut [u8], probe: Option<usize>) -> Option<usize> {
        let now = env.now;
        let kind = if self.keys.send.is_some() { Kind::Short } else { Kind::ZeroRtt };
        let suspended_data = self.life.local_asleep.is_some();
        let cc_ok = self.rec.can_send() && self.rec.pacer().next_release(now) <= now;
        // The pacing timer is for data that waits for its turn: with nothing to send, a poll inside the pacing gap
        // would arm a timer that wakes the endpoint for no reason.
        if !cc_ok && self.rec.can_send() && (self.streams.has_data_to_send() || self.dgrams.peek_send(&self.pool).is_some()) {
            self.paced_until = Some(self.rec.pacer().next_release(now));
        }
        let probes = self.life.probes > 0;
        let keepalive_due = self.life.keepalive.is_some_and(|k| now.saturating_sub(self.life.last_sent) >= k)
            && self.phase == Phase::Connected;
        let force = probes || self.life.ping_owed || keepalive_due || self.life.ack_now;
        let on_active = ti == self.paths.active;
        let mut fill = Fill {
            now,
            ti,
            allow_cc: cc_ok && !suspended_data,
            force,
            ping_only: probes,
            probe: probe.filter(|_| !probes),
            repair: None,
            min_total: 0,
        };
        // A probe packet carries only its PING: the repair stays pending for the next packet. The repair is taken
        // when its packet is sealed, or dropped by the fill when nothing is left to repair.
        if on_active && !probes && fill.probe.is_none() {
            fill.repair = self.life.repair_pn;
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
        let pn_len = if kind == Kind::Short { self.pn_len } else { PN_LEN_BASE };
        let pn_bytes = encode_pn(pn, pn_len).ok()?;
        let dcid = if kind == Kind::Short { self.path_dcid(ti)? } else { self.long_dcid() };
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
        let mut filled = self.fill_frames(payload, &fill, pn);
        if filled.len == 0 || (!filled.eliciting && filled.ack && !self.rx.ack_due(now) && !fill.force && fill.probe.is_none()) {
            self.requeue(&filled.refs);
            return None;
        }
        #[cfg(feature = "trace")]
        let traced = self
            .pack
            .on
            .then(|| (payload.get(..filled.len).unwrap_or_default().to_vec(), filled.last_stream));
        // Pad so the header-protection sample exists and any minimum size holds.
        let mut payload_len = filled.len;
        // With GSO on, a packet that leaves more stream data queued is padded to the full size so the next one can
        // follow it in the same batch. A repair takes no new stream data, so nothing follows it.
        let batchable = self.cfg.max_gso > 1 && filled.streams && !filled.drained && fill.repair.is_none();
        let want_total = if batchable { size_cap } else { fill.min_total };
        let min_payload = want_total.saturating_sub(hdr_cap + 16).max(4usize.saturating_sub(pn_len));
        if payload_len < min_payload {
            window.get_mut(hdr_cap + payload_len..hdr_cap + min_payload)?.fill(0);
            payload_len = min_payload;
        } else if let Some((at, len_bytes)) = filled.last_stream.take_if(|(at, bytes)| *at + *bytes <= payload_len) {
            // The last frame runs to the end of the packet: its length is implicit.
            payload_len -= implicit_stream_len(window.get_mut(hdr_cap..hdr_cap + payload_len)?, at, len_bytes)?;
        }
        #[cfg(feature = "trace")]
        let traced = traced.map(|(frames, hint)| trace::PackRecord {
            kind: if kind == Kind::Short { trace::PackKind::Short } else { trace::PackKind::ZeroRtt },
            mode: trace::PackMode::of(fill.ping_only, fill.probe.is_some(), fill.repair.is_some()),
            client: self.client,
            repair_taken: fill.repair.is_some(),
            repair_left: fill.repair.is_none() && self.life.repair_pn.is_some(),
            active: ti == self.paths.active,
            pn,
            pn_len,
            frames,
            hint,
            min_payload,
            payload: window.get(hdr_cap..hdr_cap + payload_len).unwrap_or_default().to_vec(),
        });
        // Lay out the header; a long header's length depends on the payload, so the payload moves up against it.
        let (header_len, layout) = match kind {
            Kind::Short => {
                let phase = self.keys.send.as_ref()?.phase;
                let mut w = Writer::new(window.get_mut(..hdr_cap)?);
                ShortHeader { key_phase: phase, dcid }.write(&mut w, pn_bytes.get(..pn_len)?).ok()?;
                (hdr_cap, PnLayout { pn_off: 1 + dcid.as_bytes().len(), pn_len, long: false })
            }
            Kind::ZeroRtt => {
                let scid = self.cids.first_local();
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
        let size = u32::try_from(total).ok()?;
        let recorded = if filled.tracked {
            self.rec.on_packet_sent(Sent {
                pn,
                time: now,
                size,
                path: u8::try_from(ti).ok()?,
                is_repair: fill.repair.is_some() && filled.streams,
                is_mtu_probe: fill.probe.is_some(),
                frames: filled.refs,
            })
        } else {
            self.rec.on_packet_untracked(pn)
        };
        if recorded.is_err() {
            // A repair re-carries frames that are in flight in another packet: they are not queued again.
            if fill.repair.is_none() {
                self.requeue(&filled.refs);
            }
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
        if fill.repair.is_some() {
            self.life.repair_pn = None;
        }
        #[cfg(feature = "trace")]
        if kind == Kind::Short {
            self.trace_sent(now, pn);
        }
        #[cfg(feature = "trace")]
        if let Some(r) = traced {
            self.pack.log.push(r);
        }
        self.stats.packets_sent += 1;
        if filled.ack {
            self.rx.on_ack_sent(pn, now);
        }
        self.life.ack_now = false;
        if fill.ping_only && self.paths.get(ti).is_some_and(|p| p.mtu.current > MIN_MTU) {
            self.life.small_ping = Some(pn);
            if let Some(p) = self.paths.get_mut(ti) {
                p.mtu.ping_big = p.mtu.last_big;
            }
        }
        if total > usize::from(MIN_MTU)
            && let Some(p) = self.paths.get_mut(ti)
        {
            p.mtu.last_big = Some(pn);
        }
        if let Some(size) = fill.probe {
            self.mtu_probe_sent(ti, u16::try_from(size).unwrap_or(u16::MAX));
        }
        if filled.eliciting {
            self.life.ping_owed = false;
        }
        if filled.streams {
            self.after_stream_send(&filled, pn, ti, now, fill.repair.is_some());
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
            K_EXT => {
                if let Some(s) = self.ctl.ext_mut(id) {
                    s.pending = true;
                }
            }
            K_REKEY => {
                if id == 1 {
                    self.keys.requeue_answer();
                } else {
                    self.keys.request_lost();
                }
            }
            K_TICKETS => self.ctl.tickets_pending = self.ctl.tickets.is_some(),
            K_READY => self.ctl.ready = true,
            _ => {}
        }
    }

    /// Feed the tail repair after a packet that carried stream data: it tracks bursts, and when the send queue
    /// drained after a burst of one plain packet, that packet is the one the next packet repairs.
    fn after_stream_send(&mut self, filled: &Filled, pn: u64, ti: usize, now: u64, repaired: bool) {
        if repaired {
            self.stats.repairs += 1;
            return;
        }
        let direct = ti == self.paths.active && self.paths.get(ti).is_some_and(|p| p.info.kind == PathKind::Direct);
        let age = now.saturating_sub(self.started);
        if !self.cfg.tail_repair || !self.loss.should_send_repair(age, true, direct) {
            return;
        }
        self.tail.on_packet(pn, filled.plain, filled.ineligible);
        if filled.drained
            && let Some(repair) = self.tail.on_drain()
        {
            self.life.repair_pn = Some(repair);
        }
    }

    /// Fill `payload` with frames; the caller seals it.
    fn fill_frames(&mut self, payload: &mut [u8], fill: &Fill, pn: u64) -> Filled {
        let now = fill.now;
        let ti = fill.ti;
        let mut out = Filled::default();
        let mut pos = 0usize;
        let cap = payload.len();
        #[cfg(feature = "inject")]
        if let Some(raw) = self.inject_raw.0.get(..self.inject_raw.1).filter(|r| !r.is_empty())
            && let Some(dst) = payload.get_mut(..raw.len())
        {
            dst.copy_from_slice(raw);
            pos = raw.len();
            out.weak();
            self.inject_raw.1 = 0;
        }
        // ACK. It does not wait for the pacer or the window.
        // Only the active path carries acknowledgements: an ACK would otherwise be sent on a path that is only being
        // checked.
        if self.rx.ack_pending() && ti == self.paths.active {
            let mut ranges: [RangeInclusive<u64>; MAX_ACK_RANGES] = core::array::from_fn(|_| 0..=0);
            let mut n = 0;
            for (slot, r) in ranges.iter_mut().zip(self.rx.ack_ranges(now)) {
                *slot = r;
                n += 1;
            }
            if let Some(used) = ranges.get(..n)
                && let it = used.iter().cloned()
                && let Ok(len) = ack_len(it.clone())
                && len <= cap - pos
                && let Some(dst) = payload.get_mut(pos..)
            {
                let mut w = Writer::new(dst);
                if write_ack(&mut w, it).is_ok() {
                    pos += w.written().len();
                    out.ack = true;
                }
            }
        }
        if fill.ping_only {
            if now < self.life.wake_until && put(payload, &mut pos, &Frame::Wake) {
                out.weak();
            }
            if put(payload, &mut pos, &Frame::Ping) {
                out.weak();
            }
            out.len = pos;
            return out;
        }
        if let Some(size) = fill.probe {
            let _ = put(payload, &mut pos, &Frame::Ping);
            out.strong();
            let _ = size;
            out.len = pos;
            return out;
        }
        if let Some(repair) = fill.repair {
            self.fill_repair(payload, &mut pos, &mut out, repair, fill);
            out.len = pos;
            return out;
        }
        // Control frames. Every one of them is recorded in flight, so none is written while the ring has no slot for the
        // packet: the packet would be refused whole and the acknowledgement in it would never leave.
        let ring_room = self.rec.ring_has_room();
        if ring_room {
            self.fill_control(payload, &mut pos, &mut out, fill);
        }
        // PATH frames.
        self.fill_path(payload, &mut pos, &mut out, ti);
        // Retransmissions and new stream data.
        if fill.allow_cc {
            self.fill_streams(payload, &mut pos, &mut out);
            self.fill_datagrams(payload, &mut pos, &mut out);
        }
        // A peer stream whose answer just left gave its place back: the credit it frees rides in the same packet, so
        // the peer has it when it reads the answer.
        if ring_room && self.streams.take_released() {
            let before = pos;
            self.fill_stream_control(payload, &mut pos, &mut out);
            if pos != before {
                out.last_stream = None;
            }
        }
        if fill.force && ring_room && !out.eliciting && put(payload, &mut pos, &Frame::Ping) {
            if ti == self.paths.active {
                out.strong();
            } else {
                out.weak();
            }
        }
        let _ = pn;
        if out.last_stream.is_some_and(|(at, bytes)| at + bytes > pos) {
            out.last_stream = None;
        }
        out.len = pos;
        out
    }

    fn fill_control(&mut self, payload: &mut [u8], pos: &mut usize, out: &mut Filled, fill: &Fill) {
        if self.life.sleep_tx > 0 && put(payload, pos, &Frame::Sleep) {
            self.life.sleep_tx -= 1;
            out.weak();
        }
        if self.life.wake_tx && put(payload, pos, &Frame::Wake) {
            self.life.wake_tx = false;
            // The WAKE of a resume on the active path is recorded in flight (it carries nothing to send again), so
            // its acknowledgement is the first round trip sample after the wake and its loss reaches loss detection.
            if fill.ti == self.paths.active {
                out.strong();
            } else {
                out.weak();
            }
        }
        if let Some(mtu) = self.paths.get_mut(fill.ti).and_then(|p| p.echo.take()) {
            let _ = put(payload, pos, &Frame::MtuProbeEcho { mtu });
        }
        if self.ctl.ready && out.refs.len() < MAX_FRAME_REFS && put(payload, pos, &Frame::Ready) {
            self.ctl.ready = false;
            let _ = out.refs.push(FrameRef::Control { kind: K_READY, id: 0 });
            out.strong();
        }
        if self.ctl.tickets_pending
            && out.refs.len() < MAX_FRAME_REFS
            && let Some(batch) = self.ctl.tickets
            && put(payload, pos, &Frame::NewTickets(batch))
        {
            self.ctl.tickets_pending = false;
            let _ = out.refs.push(FrameRef::Control { kind: K_TICKETS, id: 0 });
            out.strong();
        }
        if out.refs.len() < MAX_FRAME_REFS
            && payload.len().saturating_sub(*pos) >= REKEY_MAX
            && let Some(rekey) = self.poll_rekey(fill.now)
        {
            if put(payload, pos, &Frame::Rekey(rekey)) {
                let _ = out.refs.push(FrameRef::Control { kind: K_REKEY, id: u64::from(rekey.answer) });
                out.strong();
                #[cfg(feature = "trace")]
                self.trace_tx(rekey);
            } else if rekey.answer {
                self.keys.requeue_answer();
            } else {
                self.keys.request_lost();
            }
        }
        self.fill_extensions(payload, pos, out);
        self.fill_stream_control(payload, pos, out);
    }

    /// The streams' control frames: window and stream credit, resets and stop requests.
    fn fill_stream_control(&mut self, payload: &mut [u8], pos: &mut usize, out: &mut Filled) {
        self.streams.regrant(&self.pool);
        while out.refs.len() < MAX_FRAME_REFS && payload.len().saturating_sub(*pos) >= MIN_ROOM {
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
            out.strong();
        }
    }

    /// Extension frames: queued ones move into the retransmission table as slots free up, and every slot waiting to
    /// go is sent, to stay in the table until its packet is acknowledged.
    fn fill_extensions(&mut self, payload: &mut [u8], pos: &mut usize, out: &mut Filled) {
        self.shed_extensions();
        while self.hold_queued_extension() {}
        for slot in self.ctl.ext.iter_mut().flatten() {
            if !slot.pending || out.refs.len() >= MAX_FRAME_REFS {
                continue;
            }
            let body = self.pool.bytes(&slot.chunk).get(..slot.len).unwrap_or_default();
            let f = Frame::Extension { ty: slot.ty, body };
            if f.encoded_len() > payload.len().saturating_sub(*pos) || !put(payload, pos, &f) {
                continue;
            }
            slot.pending = false;
            let _ = out.refs.push(FrameRef::Control { kind: K_EXT, id: slot.key });
            out.strong();
        }
    }

    /// Move the oldest queued extension frame into the retransmission table, or drop it if it cannot be sent at all.
    /// Returns whether the queue moved, so the caller tries the next; false when it is empty or the table has no room.
    // Out of line: its buffer for one frame body stays off the stack of every packet built.
    #[inline(never)]
    fn hold_queued_extension(&mut self) -> bool {
        let Some(entry) = self.ext.peek_send(&self.pool) else { return false };
        let Ok((ty, n)) = vinc_wire::varint::decode(entry) else {
            self.ext.pop_send(&mut self.pool);
            return true;
        };
        let len = entry.len() - n;
        if len > self.max_extension_size(ty) {
            self.ext.pop_send(&mut self.pool);
            self.events.push(Ev::ExtensionUndeliverable(ty, len));
            return true;
        }
        // The queue and the held slot both live in the pool: the body is copied out of the queue first.
        let mut body = [0u8; EXT_BODY_MAX];
        let Some(dst) = body.get_mut(..len) else { return false };
        dst.copy_from_slice(entry.get(n..).unwrap_or_default());
        if !self.ctl.hold_ext(&mut self.pool, ty, body.get(..len).unwrap_or_default()) {
            return false;
        }
        self.ext.pop_send(&mut self.pool);
        true
    }

    fn fill_path(&mut self, payload: &mut [u8], pos: &mut usize, out: &mut Filled, ti: usize) {
        let Some(p) = self.paths.get(ti).copied() else { return };
        if let Some(d) = p.response
            && put(payload, pos, &Frame::PathResponse(d))
        {
            if let Some(pm) = self.paths.get_mut(ti) {
                pm.response = None;
            }
            out.weak();
        }
        if p.send_ping && put(payload, pos, &Frame::Ping) {
            if let Some(pm) = self.paths.get_mut(ti) {
                pm.send_ping = false;
            }
            out.weak();
        }
        if p.send_challenge
            && let Some(data) = p.challenge
            && put(payload, pos, &Frame::PathChallenge(data))
        {
            if let Some(pm) = self.paths.get_mut(ti) {
                pm.send_challenge = false;
            }
            out.weak();
        }
    }

    fn fill_streams(&mut self, payload: &mut [u8], pos: &mut usize, out: &mut Filled) {
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
            let budget = room - STREAM_BUDGET;
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
            out.last_stream = Some((*pos, hdr - vinc_wire::varint::encoded_len(chunk.len as u64)));
            *pos = end;
            let len32 = u32::try_from(chunk.len).unwrap_or(u32::MAX);
            let _ = out.refs.push(FrameRef::Stream { id: chunk.id, offset: chunk.offset, len: len32, fin: chunk.fin });
            if chunk.len > 0 || chunk.fin {
                out.plain = true;
            }
            if chunk.len > REPAIR_FRAME_BYTES as usize || self.streams.is_source(chunk.id) {
                out.ineligible = true;
            }
            out.strong();
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
            out.strong();
            out.data = true;
            out.last_stream = None;
        }
    }
}

/// The most bytes a REKEY frame takes.
const REKEY_MAX: usize = 1 + 1 + 32 + vinc_security::keyroll::ECHO_LEN + 9;

/// Drop the length field of the STREAM frame that starts at `at` in `frames` and runs to the end of them, so its data
/// runs to the end of the packet. `len_bytes` is the size of the type-and-id-and-offset part before the length
/// varint. Returns how many bytes the frame shrank, or `None` if the frame does not end the payload.
fn implicit_stream_len(frames: &mut [u8], at: usize, head: usize) -> Option<usize> {
    let after = at + head;
    let (len, n) = vinc_wire::varint::decode(frames.get(after..)?).ok()?;
    let data = after + n;
    if usize::try_from(len).ok()? != frames.len().checked_sub(data)? {
        return None;
    }
    let len_bit = u8::try_from(ty::STREAM_LEN).ok()?;
    *frames.get_mut(at)? &= !len_bit;
    frames.copy_within(data.., after);
    Some(n)
}

/// The frame for a stream-layer control description.
fn control_frame(cf: &ControlFrame) -> Frame<'static> {
    match *cf {
        ControlFrame::MaxStreamData { id, max } => Frame::MaxStreamData { id, max },
        ControlFrame::MaxStreams { limit } => Frame::MaxStreams { limit },
        ControlFrame::StopSending { id, error_code } => Frame::StopSending { id, error: error_code },
        ControlFrame::ResetStream {
            id,
            error_code,
            final_size,
        } => Frame::ResetStream {
            id,
            error: error_code,
            final_size,
        },
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
