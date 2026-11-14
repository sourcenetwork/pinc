//! Receiving: draining request streams, storing verified groups, HEAD_HOLD and completion.
//!
//! A verified group is written to the store and committed at once (the first granule too: HEAD_HOLD withholds only
//! its announcement, so the bytes behind it count as the playout buffer and nothing unverified is ever kept). The
//! pieces the session retained are released only after the write.

use super::rx::Pump;
use super::{Env, Fetch, Head, State};
use crate::knobs::{ARK_PACE_CAP, BYTE_GAP_CAP, HOLD_B, HOLD_MAX, HOLD_NV, RESTREAM_DELAY};
use crate::session::Session;
use crate::store::ValueStore;
use crate::trace::{Event, FailReason, Out, Release, Trace};
use vinc_transport::stream::StreamId;

impl Fetch {
    pub(super) fn on_readable<E: Env>(&mut self, io: &mut E, now: u64, stream: StreamId, bytes: usize) {
        let Some(si) = self.rx_index(stream) else { return };
        if bytes > 0 {
            // BYTE_LIVE: bytes arriving count as progress; the stall wait follows the stream's own burst gaps and
            // its first-byte delay.
            if self.lastb != 0 {
                self.sw = self
                    .sw
                    .max(BYTE_GAP_CAP.min(now.saturating_sub(self.lastb).saturating_mul(3)));
            } else if self.treq != 0 {
                self.sw = self
                    .sw
                    .max(BYTE_GAP_CAP.min(now.saturating_sub(self.treq).saturating_mul(2)));
            }
            self.lastb = now;
        }
        self.drain(io, now, si);
    }

    /// Process every complete frame the stream holds.
    pub(super) fn drain<E: Env>(&mut self, io: &mut E, now: u64, si: usize) {
        let root = self.root;
        while self.state == State::Running {
            let (se, st, _) = io.split();
            let Some(rx) = self.rx.get_mut(si).and_then(Option::as_mut) else {
                return;
            };
            let (stream, from, pi) = (rx.stream, rx.pos, rx.provider);
            // WHOLE_GROUP: a group is hashed once all its bytes are here (they are kept until it ends either way), so
            // BLAKE3 takes them in runs of whole chunks, not one packet at a time.
            if rx.group_left().is_some_and(|left| !se.has(stream, from, left)) {
                return;
            }
            let mut found = Pump::More;
            se.visit(stream, from, |piece| {
                if found != Pump::More {
                    return 0;
                }
                let (n, p) = rx.pump(&*st, &root, piece);
                found = p;
                n
            });
            match found {
                Pump::More => return,
                Pump::Group => {}
                Pump::Bad(why) => return self.evict(io, now, pi, why),
                Pump::Frame {
                    off,
                    len,
                    data_start,
                    matched,
                } => {
                    self.arrival(now);
                    let upto = self.rx.get(si).and_then(Option::as_ref).map_or(from, |r| r.pos);
                    // Another stream (a write-through on the same group) may have stored it while this one was still
                    // hashing: the bytes are the same, so they are not written or announced a second time.
                    let again = matched && self.is_stored(io, off, len);
                    if matched && !again && !self.store_group(io, stream, off, len, data_start) {
                        self.state = State::Done;
                        self.drop_all_streams(io);
                        io.split().2.event(now, Event::Failed(FailReason::Store));
                        return;
                    }
                    io.split().0.consume(stream, upto);
                    if matched {
                        self.group_verified(io, now, pi, off, len, false, !again);
                    }
                }
            }
        }
    }

    /// Whether the store holds `[off, off + len)` verified.
    fn is_stored<E: Env>(&self, io: &mut E, off: u64, len: u64) -> bool {
        io.split()
            .1
            .verified_from(&self.root, off)
            .is_some_and(|v| v.start <= off && v.end >= off + len)
    }

    /// ARK_PACE: the stall timer follows this transfer's own granule pace.
    fn arrival(&mut self, now: u64) {
        if self.lastp != 0 && now.saturating_sub(self.lastp).saturating_mul(3) > self.sw {
            self.sw = ARK_PACE_CAP.min(now.saturating_sub(self.lastp).saturating_mul(3));
        }
        self.lastp = now;
    }

    /// Write the verified group at stream offset `data_start` to the store and commit it.
    pub(super) fn store_group<E: Env>(
        &mut self,
        io: &mut E,
        stream: StreamId,
        off: u64,
        len: u64,
        data_start: u64,
    ) -> bool {
        let (se, st, _) = io.split();
        let (mut at, mut left, mut ok) = (off, len, true);
        let root = self.root;
        se.visit(stream, data_start, |piece| {
            let n = usize::try_from(left).map_or(piece.len(), |l| l.min(piece.len()));
            if n == 0 {
                return 0;
            }
            ok &= piece.get(..n).is_some_and(|p| st.write_at(&root, at, p).is_ok());
            at += n as u64;
            left -= n as u64;
            if ok { n } else { 0 }
        });
        ok && left == 0 && st.commit(&root, off..off + len).is_ok()
    }

    /// A group is verified and stored: announce it (or hold the first), account for the provider, top it up. A group
    /// that is not `fresh` was already announced when another stream stored it, so only the accounting runs.
    #[allow(clippy::too_many_arguments, reason = "one verified group's fields, passed once")]
    pub(super) fn group_verified<E: Env>(
        &mut self,
        io: &mut E,
        now: u64,
        pi: usize,
        off: u64,
        len: u64,
        ahead: bool,
        fresh: bool,
    ) {
        if let Some(p) = self.provs.get(pi) {
            io.split().2.trace(
                now,
                Trace::Verified {
                    provider: p.id,
                    off,
                    len,
                    ahead,
                },
            );
        }
        if fresh && !self.released && off <= self.o0 && self.o0 < off + len {
            // HEAD_HOLD: the granule at the start of the request is verified now but announced only once a playout
            // buffer of verified bytes stands behind it.
            let t0 = self.head.map_or(now, |h| h.t0);
            self.head = Some(Head { off, len, t0 });
            self.nv = 0;
            io.split().2.trace(now, Trace::Held { off });
        } else if fresh {
            io.split().2.event(now, Event::Readable { off, len });
            if self.head.is_some() {
                self.nv += 1;
                self.hold_check(io, now, None);
            }
        }
        if self.striped {
            if let Some(p) = self.provs.get_mut(pi) {
                p.lp = Some(now);
                p.pt.get_or_insert(now);
                p.pb += len;
            }
            self.top_up(io, now, pi);
        }
        self.check_done(io, now);
    }

    /// HEAD_HOLD: release the held first granule when a buffer stands behind it, the value ends in the buffer, enough
    /// granules verified after it, or it waited long enough. `force` releases it unconditionally.
    pub(super) fn hold_check<E: Env>(&mut self, io: &mut E, now: u64, force: Option<Release>) {
        let Some(h) = self.head else { return };
        let (_, st, out) = io.split();
        let end = h.off + h.len;
        let buf = st
            .verified_from(&self.root, end)
            .filter(|v| v.start <= end)
            .map_or(0, |v| v.end - end);
        // The wanted ranges end where the last one in delivery order ends (the list keeps the order they were asked).
        let wanted_end = self.wanted_end();
        let why = force.or(if buf >= HOLD_B {
            Some(Release::Buffered)
        } else if end + buf >= wanted_end {
            Some(Release::Tail)
        } else if self.nv >= HOLD_NV {
            Some(Release::Granules)
        } else if now >= h.t0.saturating_add(HOLD_MAX) {
            Some(Release::Timeout)
        } else {
            None
        });
        let Some(why) = why else { return };
        self.head = None;
        self.released = true;
        out.trace(now, Trace::Released { off: h.off, why });
        out.event(now, Event::Readable { off: h.off, len: h.len });
    }

    /// Finish the fetch when nothing wanted is missing.
    pub(super) fn check_done<E: Env>(&mut self, io: &mut E, now: u64) {
        if self.head.is_some() {
            self.hold_check(io, now, None);
        }
        let (_, st, _) = io.split();
        if !self.want.missing(&*st, &self.root).is_empty() {
            return;
        }
        if self.head.is_some() {
            self.hold_check(io, now, Some(Release::Done));
        }
        self.state = State::Done;
        self.drop_all_streams(io);
        io.split().2.event(now, Event::Complete);
    }

    /// A request stream ended: the provider's next top-up, or a new request after a pause if none is left.
    pub(super) fn on_stream_end<E: Env>(&mut self, io: &mut E, now: u64, stream: StreamId) {
        let Some(si) = self.rx_index(stream) else { return };
        let Some(rx) = self.rx.get_mut(si).and_then(Option::take) else {
            return;
        };
        self.check_done(io, now);
        if self.state != State::Running {
            return;
        }
        if self.striped {
            self.top_up(io, now, rx.provider);
        }
        if self.state == State::Running
            && self.streams_of(rx.provider) == 0
            && let Some(p) = self.provs.get_mut(rx.provider)
        {
            p.retry = Some(now + RESTREAM_DELAY);
        }
    }
}
