//! The packet carrying CLOSE.

use super::Transmit;
use super::put;
#[cfg(feature = "trace")]
use super::trace;
use crate::conn::{Connection, Phase};
use crate::frame::Frame;
use crate::packet::{PnLayout, ShortHeader, encode_pn, seal};
use crate::stream::StreamSource;
use pinc_crypto::Provider;
use pinc_security::Env;
use pinc_wire::Writer;

conn_impl! {
    /// The packet carrying CLOSE, sent once; the connection is over once it left.
    pub(super) fn build_close(&mut self, env: &mut Env<'_, P>, out: &mut [u8]) -> Option<Transmit> {
        let Some(error) = self.life.close else {
            self.phase = Phase::Closed;
            return None;
        };
        self.life.close_offered = true;
        let ti = self.paths.active;
        let now = env.now;
        let p = env.provider;
        let dcid = self.path_dcid(ti)?;
        let pn = self.next_pn;
        let pn_len = self.pn_len;
        let pn_bytes = encode_pn(pn, pn_len).ok()?;
        let hdr = 1 + dcid.as_bytes().len() + pn_len;
        let mtu = usize::from(self.paths.get(ti)?.mtu.current).min(out.len()).min(self.amp_room(ti));
        let payload = out.get_mut(hdr..mtu.checked_sub(16)?)?;
        let mut pos = 0;
        if !put(payload, &mut pos, &Frame::Close { error }) {
            return None;
        }
        #[cfg(feature = "trace")]
        let traced = self.pack.on.then(|| payload.get(..pos).unwrap_or_default().to_vec());
        let pad = 4usize.saturating_sub(pn_len + pos);
        if pad > 0 {
            payload.get_mut(pos..pos + pad)?.fill(0);
            pos += pad;
        }
        #[cfg(feature = "trace")]
        let traced = traced.map(|frames| trace::PackRecord {
            kind: trace::PackKind::Short,
            mode: trace::PackMode::Close,
            client: self.client,
            repair_taken: false,
            repair_left: self.life.repair_pn.is_some(),
            active: true,
            pn,
            pn_len,
            frames,
            hint: None,
            min_payload: 4usize.saturating_sub(pn_len),
            payload: payload.get(..pos).unwrap_or_default().to_vec(),
        });
        let phase = self.keys.send.as_ref()?.phase;
        ShortHeader { key_phase: phase, dcid }.write(&mut Writer::new(out.get_mut(..hdr)?), pn_bytes.get(..pn_len)?).ok()?;
        let k = self.keys.send.as_mut()?;
        let layout = PnLayout { pn_off: 1 + dcid.as_bytes().len(), pn_len, long: false };
        let len = seal(&mut k.pk, &k.hk, p, out, layout, pos, pn).ok()?;
        self.next_pn += 1;
        #[cfg(feature = "trace")]
        if let Some(r) = traced {
            self.pack.log.push(r);
        }
        self.life.close = None;
        self.phase = Phase::Closed;
        self.stats.packets_sent += 1;
        let path = self.paths.get(ti)?.id;
        self.finish_datagram(ti, len, now)?;
        Some(Transmit { path, len, segment_size: len })
    }
}
