//! The tail repair fill: the stream frames of an earlier packet that are not acknowledged yet, sent again whole.

use super::{Fill, Filled, put_stream_header};
use crate::conn::Connection;
use crate::conn::config::MIN_MTU;
use crate::frame::stream_overhead;
use crate::recovery::{FrameRef, MAX_FRAME_REFS, REPAIR_OVERHEAD, REPAIR_PACKET_BYTES};
use crate::stream::StreamSource;
use vinc_crypto::Provider;

conn_impl! {

    /// A tail repair: the stream frames of packet `repair` that are not acknowledged yet, newest first, whole, up to
    /// `min(datagram size - 23, 600)` bytes of payload. The packet is a repair packet: its loss is neither resent
    /// nor a congestion signal.
    pub(super) fn fill_repair(&mut self, payload: &mut [u8], pos: &mut usize, out: &mut Filled, repair: u64, fill: &Fill) {
        let Some(frames) = self.rec.sent_frames(repair).copied() else { return };
        let mtu = self.paths.get(fill.ti).map_or(u32::from(MIN_MTU), |p| u32::from(p.mtu.current));
        let mut room = usize::try_from(mtu.saturating_sub(REPAIR_OVERHEAD).min(REPAIR_PACKET_BYTES)).unwrap_or(0);
        for f in frames.as_slice().iter().rev() {
            let FrameRef::Stream { id, offset, len, fin } = *f else { continue };
            if (len > 0 || !fin) && self.streams.is_acked(id, offset, u64::from(len)) {
                continue;
            }
            let dl = len as usize;
            if dl + 24 > room || out.refs.len() >= MAX_FRAME_REFS {
                break;
            }
            let hdr = stream_overhead(id, offset, dl, false);
            let end = *pos + hdr + dl;
            let chunk = crate::stream::StreamChunk { id, offset, len: dl, fin };
            let ok = end <= payload.len()
                && payload
                    .get_mut(*pos + hdr..end)
                    .is_some_and(|dst| self.streams.copy_out(&self.pool, &chunk, dst).is_ok())
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
    }
}
