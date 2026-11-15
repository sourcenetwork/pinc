//! The tail repair fill: the stream frames of an earlier packet that are not acknowledged yet, sent again from the
//! first byte that is not acknowledged for good (the part before it was released).

use super::{Fill, Filled, put_stream_header};
use crate::conn::Connection;
use crate::conn::config::MIN_MTU;
use crate::frame::stream_overhead;
use crate::recovery::{FrameRef, MAX_FRAME_REFS, REPAIR_OVERHEAD, REPAIR_PACKET_BYTES};
use crate::stream::StreamSource;
use pinc_crypto::Provider;

conn_impl! {

    /// A tail repair: the stream frames of packet `repair` that are not acknowledged yet, newest first, each from
    /// its first byte that is not acknowledged for good, up to `min(datagram size - 23, 600)` bytes of payload. The packet is a repair packet: its loss is neither resent
    /// nor a congestion signal. The repair stays pending for the packet that is sealed (the caller takes it then),
    /// unless nothing is left to repair, no frame can ever fit or the bytes cannot be read: then it is dropped here.
    pub(super) fn fill_repair(&mut self, payload: &mut [u8], pos: &mut usize, out: &mut Filled, repair: u64, fill: &Fill) {
        let Some(frames) = self.rec.sent_frames(repair).copied() else {
            self.life.repair_pn = None;
            return;
        };
        let mtu = self.paths.get(fill.ti).map_or(u32::from(MIN_MTU), |p| u32::from(p.mtu.current));
        let mut room = usize::try_from(mtu.saturating_sub(REPAIR_OVERHEAD).min(REPAIR_PACKET_BYTES)).unwrap_or(0);
        let mut short = false;
        for f in frames.as_slice().iter().rev() {
            let FrameRef::Stream { id, offset: first, len, fin } = *f else { continue };
            if (len > 0 || !fin) && self.streams.is_acked(&self.pool, id, first, u64::from(len)) {
                continue;
            }
            // A part of the frame that is acknowledged for good was released and is not sent again.
            let offset = self.streams.resend_from(id, first);
            let len = u32::try_from(u64::from(len).saturating_sub(offset - first)).unwrap_or(0);
            let dl = len as usize;
            if dl + 24 > room || out.refs.len() >= MAX_FRAME_REFS {
                break;
            }
            let hdr = stream_overhead(id, offset, dl, false);
            let end = *pos + hdr + dl;
            if end > payload.len() {
                short = true;
                break;
            }
            let chunk = crate::stream::StreamChunk { id, offset, len: dl, fin };
            let ok = payload
                    .get_mut(*pos + hdr..end)
                    .is_some_and(|dst| self.streams.copy_out(&mut self.pool, &chunk, dst).is_ok())
                && payload.get_mut(*pos..*pos + hdr).is_some_and(|h| put_stream_header(h, &chunk));
            if !ok {
                break;
            }
            *pos = end;
            room -= hdr + dl;
            let _ = out.refs.push(FrameRef::Stream { id, offset, len, fin });
            out.strong();
            out.streams = true;
        }
        if !out.streams && !short {
            self.life.repair_pn = None;
        }
    }
}
