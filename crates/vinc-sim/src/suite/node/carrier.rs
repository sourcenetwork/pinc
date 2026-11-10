//! The node as a client of its relays: key answers, carrier streams over the simulator's TCP and WebSocket
//! connections, and the connectivity layer's own datagrams.
//!
//! [`Wire`] holds what the node has queued for the simulator (datagrams and stream operations) and the state of the
//! carriers it opened toward its relays. The steps on [`Core`] serve what the node asks for after every call: a key
//! answer for the carrier handshake or a signature, a stream to open or close, bytes to write, a datagram to send.
//!
//! Invariants: a browser opens WebSocket carriers only and sends no direct datagram; a stream the simulator reports
//! closed is reported closed to the node exactly once; key answers use the node's own keys and are charged to the
//! node's ledger.

use std::collections::VecDeque;
use std::net::SocketAddr;

use vinc_connect::carrier::ws::{self, Decoder, Opcode, Role as WsRole, WsFrame};
use vinc_connect::client::{Io, Kind};
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_crypto::{Drbg, Keypair, Secret};
use vinc_security::{Env, KeyHandle, KeyRequest, KeyResponse, SoftKeys, SoftPrekeys};

use super::core::{Core, NRL};
use crate::suite::crypto::{Registry, Tracked};
use crate::{StreamEvent, StreamId, StreamKind, StreamOp};

/// A key answer that owns its bytes, so the request it answers can be dropped first.
#[allow(
    clippy::large_enum_variant,
    reason = "built once per key request and dropped at once"
)]
pub(super) enum Owned {
    Sig([u8; MAX_SIGNATURE_LEN], usize),
    Secret(Secret<32>),
    Failed,
}

impl Owned {
    pub(super) fn response(&self) -> KeyResponse<'_> {
        match self {
            Self::Sig(b, n) => KeyResponse::Signature(b.get(..*n).unwrap_or_default()),
            Self::Secret(s) => KeyResponse::SharedSecret(Secret::new(*s.expose())),
            Self::Failed => KeyResponse::Failed,
        }
    }
}

/// The keys a node answers with.
pub(super) struct Keys<'a> {
    pub(super) reg: &'static Registry,
    pub(super) idx: usize,
    pub(super) prov: Tracked,
    pub(super) kp: &'a Keypair,
    pub(super) prekeys: Option<&'a SoftPrekeys<Tracked>>,
}

impl Keys<'_> {
    /// Answers `req` from the node's software keys.
    pub(super) fn answer(&self, drbg: &mut Drbg, now: u64, req: &KeyRequest<'_>) -> Owned {
        if let KeyRequest::Sign { message, .. } = req {
            // Both ends sign and verify in the handshake, so a signature made is charged with one verified.
            self.reg.note_sign(self.idx, message.len());
            self.reg.note_verify(self.idx, message.len());
        }
        let soft = SoftKeys {
            signer: Some((KeyHandle(1), self.kp)),
            prekeys: self.prekeys,
        };
        let mut env = Env {
            provider: &self.prov,
            now,
            drbg,
        };
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        match soft.answer(&mut env, req, &mut sig) {
            KeyResponse::Signature(s) => {
                let mut out = [0u8; MAX_SIGNATURE_LEN];
                if let Some(d) = out.get_mut(..s.len()) {
                    d.copy_from_slice(s);
                }
                Owned::Sig(out, s.len())
            }
            KeyResponse::SharedSecret(s) => Owned::Secret(s),
            KeyResponse::Failed => Owned::Failed,
        }
    }
}

/// Who asked for a stream the simulator is opening.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Dial {
    /// The carrier of relay `n` of the node's client.
    Client(usize),
    /// A relay-to-relay carrier of a hub.
    Peer,
}

/// What the node has queued for the simulator and the state of its carriers.
#[derive(Default)]
pub(super) struct Wire {
    /// Datagrams to send: `(local, remote, bytes)`.
    pub(super) datagrams: VecDeque<(SocketAddr, SocketAddr, Vec<u8>)>,
    /// Stream operations, each with the record a write carries.
    pub(super) ops: VecDeque<(StreamOp, Vec<u8>)>,
    streams: [Option<StreamId>; NRL],
    /// Streams asked for and not yet named by the simulator, with their target.
    pub(super) connects: VecDeque<(Dial, SocketAddr)>,
    kinds: [Option<Kind>; NRL],
    decoders: [Option<Decoder>; NRL],
}

impl Wire {
    fn relay_of(&self, s: StreamId) -> Option<usize> {
        self.streams.iter().position(|x| *x == Some(s))
    }
}

/// The payloads of the WebSocket frames in `data`, in order.
pub(super) fn ws_payloads(dec: &mut Decoder, data: &mut [u8]) -> Vec<Vec<u8>> {
    let mut rest: &mut [u8] = data;
    let mut out = Vec::new();
    while let Ok(Some((frame, used))) = dec.decode(rest) {
        if let WsFrame::Data(p) = frame {
            out.push(p.to_vec());
        }
        let (_, tail) = std::mem::take(&mut rest).split_at_mut(used);
        rest = tail;
    }
    out
}

impl Core {
    /// How many carrier streams are open and being opened, for diagnosis.
    pub(super) fn wire_summary(&self) -> String {
        let open = self.wire.streams.iter().flatten().count();
        let opening = self.wire.connects.len();
        let hub = self.hub.as_ref().map_or(String::new(), |h| {
            format!(
                " hub: records {} peers up {} peers out {:?} streams {}",
                h.relay.record_count(),
                h.peer_by_node.len(),
                h.peers_out.iter().map(|p| p.stream.is_some()).collect::<Vec<_>>(),
                h.streams.len()
            )
        });
        format!("carriers open {open} opening {opening}{hub}")
    }

    /// Serves the key operations the node waits for: the carrier handshakes and its own signatures.
    pub(super) fn keys_step(&mut self) -> bool {
        let keys = Keys {
            reg: self.shared.registry,
            idx: self.idx,
            prov: self.provider(),
            kp: &self.kp,
            prekeys: self.prekeys.as_ref(),
        };
        let (local, Some(node)) = (self.local, self.node.as_mut()) else {
            return false;
        };
        let mut did = false;
        for relay in 0..NRL {
            for _ in 0..8 {
                let owned = node.key_request(relay).map(|r| keys.answer(&mut self.drbg, local, &r));
                let Some(owned) = owned else { break };
                did = true;
                node.key_response(local, relay, owned.response());
            }
        }
        for _ in 0..8 {
            let owned = node.sign_request().map(|r| keys.answer(&mut self.drbg, local, &r));
            let Some(owned) = owned else { break };
            did = true;
            node.sign_response(local, owned.response());
        }
        did
    }

    /// Opens and closes the carrier streams the node asks for.
    pub(super) fn io_step(&mut self) -> bool {
        let (local, from) = (self.local, self.stream_local());
        let browser = self.browser;
        let (Some(node), wire) = (self.node.as_mut(), &mut self.wire) else {
            return false;
        };
        let mut did = false;
        while let Some(io) = node.poll_io() {
            did = true;
            match io {
                Io::Open { relay, kind, to } => {
                    // A browser has no raw sockets: a TCP carrier fails at once, as the node expects of a refusal.
                    let Some(from) = from.filter(|_| !(browser && kind == Kind::Tcp)) else {
                        node.stream_closed(local, relay);
                        continue;
                    };
                    if let Some(k) = wire.kinds.get_mut(relay) {
                        *k = Some(kind);
                    }
                    wire.connects.push_back((Dial::Client(relay), to));
                    let kind = match kind {
                        Kind::Tcp => StreamKind::Tcp,
                        Kind::Ws => StreamKind::Ws,
                    };
                    let op = StreamOp::Connect {
                        local: from,
                        remote: to,
                        kind,
                        simultaneous: false,
                    };
                    wire.ops.push_back((op, Vec::new()));
                }
                Io::Close { relay } => {
                    if let Some(s) = wire.streams.get_mut(relay).and_then(Option::take) {
                        wire.ops.push_back((StreamOp::Close { stream: s }, Vec::new()));
                    }
                    wire.connects.retain(|(d, _)| *d != Dial::Client(relay));
                    if let Some(d) = wire.decoders.get_mut(relay) {
                        *d = None;
                    }
                }
            }
        }
        did
    }

    /// Sends the connectivity layer's own datagrams (relay probes, lookups, beacons).
    pub(super) fn udp_step(&mut self) -> bool {
        let from = self.udp_addr();
        let (Some(node), wire) = (self.node.as_mut(), &mut self.wire) else {
            return false;
        };
        let mut did = false;
        let mut buf = vec![0u8; 2048];
        while let Some((to, n)) = node.poll_udp(&mut buf) {
            did = true;
            if to.port() == vinc_connect::local::PORT {
                continue;
            }
            if let (Some(from), Some(d)) = (from, buf.get(..n)) {
                wire.datagrams.push_back((from, to, d.to_vec()));
            }
        }
        did
    }

    /// Writes the bytes the node has for its carrier streams.
    pub(super) fn streams_out_step(&mut self) -> bool {
        let (Some(node), wire) = (self.node.as_mut(), &mut self.wire) else {
            return false;
        };
        let mut did = false;
        let mut buf = vec![0u8; 20_000];
        for relay in 0..NRL {
            let Some(stream) = wire.streams.get(relay).copied().flatten() else {
                continue;
            };
            loop {
                let n = node.poll_stream(relay, &mut buf);
                let Some(bytes) = buf.get(..n).filter(|b| !b.is_empty()) else {
                    break;
                };
                did = true;
                let data = if wire.kinds.get(relay).copied().flatten() == Some(Kind::Ws) {
                    let mut f = vec![0u8; n + 16];
                    let mask = [0x11, 0x22, 0x33, 0x44];
                    let m = ws::encode(Opcode::Binary, bytes, Some(mask), &mut f).unwrap_or(0);
                    f.truncate(m);
                    f
                } else {
                    bytes.to_vec()
                };
                let op = StreamOp::Write {
                    stream,
                    len: data.len(),
                    send_at: None,
                };
                wire.ops.push_back((op, data));
            }
        }
        did
    }

    /// Feeds carrier bytes to the node, answering the key operations it stops at.
    fn feed(&mut self, relay: usize, mut bytes: &[u8]) {
        for _ in 0..64 {
            let local = self.local;
            let Some(node) = self.node.as_mut() else { return };
            let n = node.stream_data(local, relay, bytes);
            bytes = bytes.get(n..).unwrap_or_default();
            self.keys_step();
            let waiting = self.node.as_ref().is_some_and(|nd| nd.key_request(relay).is_some());
            if bytes.is_empty() || (n == 0 && !waiting) {
                return;
            }
        }
    }

    /// A stream event of the simulator: one of the node's carriers, or a carrier accepted by this hub.
    pub(super) fn stream_event(&mut self, event: StreamEvent) {
        let local = self.local;
        match event {
            StreamEvent::Pending { stream, remote } => {
                let w = &mut self.wire;
                if let Some(at) = w.connects.iter().position(|(_, a)| *a == remote)
                    && let Some((who, _)) = w.connects.remove(at)
                {
                    match who {
                        Dial::Client(i) => {
                            if let Some(s) = w.streams.get_mut(i) {
                                *s = Some(stream);
                            }
                        }
                        Dial::Peer => self.hub_peer_pending(stream, remote),
                    }
                }
            }
            StreamEvent::Opened { stream, .. } => {
                if let Some(i) = self.wire.relay_of(stream) {
                    let ws = self.wire.kinds.get(i).copied().flatten() == Some(Kind::Ws);
                    self.wire.decoders[i] = ws.then(|| Decoder::new(WsRole::Server));
                    if let Some(node) = self.node.as_mut() {
                        node.stream_opened(local, i);
                    }
                } else if self.hub_is_peer_dial(stream) {
                    self.hub_peer_dialed(stream);
                } else {
                    self.hub_accept(stream);
                }
            }
            StreamEvent::Failed { stream } | StreamEvent::Closed { stream } => {
                if let Some(i) = self.wire.relay_of(stream) {
                    self.wire.streams[i] = None;
                    self.wire.decoders[i] = None;
                    if let Some(node) = self.node.as_mut() {
                        node.stream_closed(local, i);
                    }
                } else {
                    self.hub_closed(stream);
                }
            }
        }
    }

    /// A record arrived on a stream of the node.
    pub(super) fn stream_record(&mut self, stream: StreamId, data: &mut [u8]) {
        let Some(relay) = self.wire.relay_of(stream) else {
            self.hub_record(stream, data);
            return;
        };
        let payloads = match self.wire.decoders.get_mut(relay).and_then(Option::as_mut) {
            Some(dec) => ws_payloads(dec, data),
            None => vec![data.to_vec()],
        };
        for p in payloads {
            self.feed(relay, &p);
        }
    }
}
