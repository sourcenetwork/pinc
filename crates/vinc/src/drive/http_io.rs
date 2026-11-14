//! The HTTP exchanges of the port-mapping client (`UPnP`), carried over the host's carriers: open a TCP stream to the
//! gateway's control address, write the request, read until the gateway closes, hand the answer back.
//!
//! Invariants: at most one exchange runs at a time, held by the driving future; an answer is read up to
//! [`vinc_portmap::MAX_RESPONSE`] bytes and no further; a stream that fails ends the exchange with no answer, and an
//! exchange the host never finishes is dropped, stream and all, when the port-mapping client's own deadline passes.

use std::net::SocketAddr;

use vinc_crypto::NodeId;

use crate::carrier::CarrierKind;
use crate::carriers::{Carriers, Relay};
use crate::drive::Shared;
use crate::host::Hosted;

/// The longest request the port-mapping client builds.
pub(super) const MAX_REQUEST: usize = vinc_portmap::upnp::MAX_REQUEST;

impl<H: Hosted> Shared<H> {
    /// One exchange: the answer, or `None` if the stream could not be opened, written or read.
    pub(super) async fn http_exchange(&self, me: NodeId, to: SocketAddr, req: Vec<u8>) -> Option<Vec<u8>> {
        let c = self.host.carriers();
        let stream = c.open(&Relay::new(me).with_tcp(to), CarrierKind::Tcp).await.ok()?;
        let answer = exchange(c, &stream, req).await;
        c.close(stream).await;
        answer
    }
}

async fn exchange<C: Carriers>(c: &C, stream: &C::Stream, mut req: Vec<u8>) -> Option<Vec<u8>> {
    let mut sent = 0;
    while sent < req.len() {
        let (r, b) = c.write(stream, req, sent).await;
        req = b;
        match r {
            Ok(n) if n > 0 => sent += n,
            _ => return None,
        }
    }
    let mut answer = Vec::new();
    let mut buf = vec![0u8; 4096];
    while answer.len() < vinc_portmap::MAX_RESPONSE {
        let (r, b) = c.read(stream, buf).await;
        buf = b;
        match r {
            Ok(0) => break,
            Ok(n) => {
                let room = vinc_portmap::MAX_RESPONSE - answer.len();
                answer.extend_from_slice(buf.get(..n.min(room)).unwrap_or_default());
            }
            Err(_) => return None,
        }
    }
    Some(answer)
}
