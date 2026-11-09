//! The member side of the hub tunnel, and the thin-node splice.
//!
//! A hub is both a relay and a node: a member keeps a VINC session with it over UDP. When the member's carrier to the
//! hub cannot be trusted, a packet for the relay goes in an SPU datagram over that session instead of (or as well as)
//! the carrier, and the hub delivers it ([`crate::relay`]). [`decide`] holds the rule:
//! - the carrier is not open: the packet goes by the tunnel and is not queued for the carrier (the dial goes on);
//! - the carrier has been silent for 15 s: the packet goes by the carrier and by the tunnel;
//! - the session is in loss recovery (one probe timeout in a row, two on a thin node) or still handshaking (from the
//!   second try, or at once on a node that is not thin): the packet goes by both.
//!
//! The tunnel is usable only over a validated direct UDP hub session that was heard within 20 s ([`hub_ok`]); if the
//! target relay has none, the home hub's session carries it and the home hub forwards. SPLICE_LIVE ([`Splices`]):
//! a SPL datagram from a hub in the last 30 s (or twice the node's round trip) proves its UDP session works down to
//! us, so the same validated active path carries our tunnel packets even when our own receive stamp on it is older
//! than 20 s (a slow uplink queues for tens of seconds). THIN_SPLICE ([`thin_splice`]): on a slow link, a packet to
//! a peer that reaches us by splice over a hub is not loaded onto a carrier that is backlogged or dialing, when the
//! tunnel took it and the session has fewer than 2 probe timeouts.
//!
//! General UDP splicing of every packet is not part of VINC.
//!
//! Invariants: every decision is a pure function of its arguments; the splice tables are bounded.

use core::net::SocketAddr;

use vinc_crypto::NodeId;

/// A carrier silent this long also gets a copy over the tunnel.
pub const TUNNEL_STALE: u64 = 15_000_000_000;
/// A hub session carries tunnel packets if it was heard within this long.
pub const HUB_TUNNEL_FRESH: u64 = 20_000_000_000;
/// A SPL from a hub keeps its UDP session usable for the tunnel this long.
pub const SPL_LIVE: u64 = 30_000_000_000;
/// THIN_SPLICE: a carrier heard within this long is not backlogged.
pub const THIN_SPLICE_FRESH: u64 = 2_000_000_000;
/// THIN_SPLICE: from this many probe timeouts on the carrier is used as well.
pub const THIN_SPLICE_PTO: u32 = 2;
/// How long a splice from a peer stays known for THIN_SPLICE.
pub const SPLICE_SPAN: u64 = 4_000_000_000;

/// The state of the session with a hub.
#[derive(Debug, Clone, Copy)]
pub struct HubSession {
    /// The session is established and its active path is a validated direct UDP path.
    pub validated_direct: bool,
    /// When a datagram last arrived on that path.
    pub heard: u64,
    /// The remote address of that path.
    pub remote: SocketAddr,
}

/// Whether the session can carry tunnel packets at `now`.
pub const fn hub_ok(s: &HubSession, now: u64) -> bool {
    s.validated_direct && now.saturating_sub(s.heard) < HUB_TUNNEL_FRESH
}

/// Where a packet for a relay goes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Via {
    /// Only the carrier.
    Carrier,
    /// Only the tunnel; nothing is queued for the carrier.
    Tunnel,
    /// The carrier and a copy over the tunnel.
    Both,
}

/// What the packet's session reads.
#[derive(Debug, Clone, Copy)]
pub struct Rides {
    /// Probe timeouts in a row.
    pub pto_count: u32,
    /// The session is still in handshake.
    pub handshaking: bool,
    /// Handshake tries so far.
    pub hs_tries: u32,
    /// The node is thin.
    pub thin: bool,
}

/// The tunnel rule: where a packet goes. `tunnel` says a usable hub session exists; `carrier_open` and `silent_for`
/// describe the carrier; `session` the packet's session, when it is a session packet.
pub const fn decide(carrier_open: bool, silent_for: u64, session: Option<Rides>, tunnel: bool) -> Via {
    if !tunnel {
        return Via::Carrier;
    }
    if !carrier_open {
        return Via::Tunnel;
    }
    if silent_for > TUNNEL_STALE {
        return Via::Both;
    }
    if let Some(s) = session {
        let loss = s.pto_count >= if s.thin { 2 } else { 1 };
        let hs = s.handshaking && (s.hs_tries >= 2 || !s.thin);
        if loss || hs {
            return Via::Both;
        }
    }
    Via::Carrier
}

/// What THIN_SPLICE reads about a packet to a peer that reaches this node by splice.
#[derive(Debug, Clone, Copy)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "independent facts the node reads, not a state"
)]
pub struct ThinSplice {
    /// The node is thin (a round trip of 250 ms or more).
    pub thin: bool,
    /// The packet's session is established.
    pub established: bool,
    /// The age of the splice from this peer over this hub, if one was seen ([`Splices::age`]).
    pub splice_age: Option<u64>,
    /// The node's round trip.
    pub rtt: u64,
    /// The carrier to the hub was heard within [`THIN_SPLICE_FRESH`] (it is not backlogged).
    pub carrier_fresh: bool,
    /// The tunnel took the packet.
    pub tunnel_took: bool,
    /// The session's probe timeouts in a row.
    pub pto_count: u32,
}

/// THIN_SPLICE: whether a packet to a peer is withheld from the carrier because the tunnel took it.
pub const fn thin_splice(t: &ThinSplice) -> bool {
    if !(t.thin && t.established && t.tunnel_took && !t.carrier_fresh && t.pto_count < THIN_SPLICE_PTO) {
        return false;
    }
    let span = if t.rtt.saturating_mul(2) > SPLICE_SPAN {
        t.rtt.saturating_mul(2)
    } else {
        SPLICE_SPAN
    };
    matches!(t.splice_age, Some(a) if a < span)
}

#[derive(Debug, Clone, Copy)]
struct Splice {
    peer: NodeId,
    relay: u8,
    at: u64,
}

/// Which peers reach this node by splice over a hub, and which hubs spliced to it lately.
#[derive(Debug, Clone, Copy)]
pub struct Splices<const P: usize, const R: usize> {
    peers: [Option<Splice>; P],
    next: usize,
    live: [Option<(u64, SocketAddr)>; R],
}

impl<const P: usize, const R: usize> Default for Splices<P, R> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const P: usize, const R: usize> Splices<P, R> {
    /// No splice seen.
    pub const fn new() -> Self {
        Self {
            peers: [None; P],
            next: 0,
            live: [None; R],
        }
    }

    /// A SPL datagram for a packet from `peer` arrived from the hub in table position `relay` over `from`.
    pub fn seen(&mut self, now: u64, relay: u8, peer: NodeId, from: SocketAddr) {
        if let Some(l) = self.live.get_mut(usize::from(relay)) {
            *l = Some((now, from));
        }
        let slot = self
            .peers
            .iter()
            .position(|s| s.is_some_and(|s| s.peer == peer))
            .unwrap_or(self.next);
        if let Some(s) = self.peers.get_mut(slot) {
            *s = Some(Splice { peer, relay, at: now });
        }
        if slot == self.next {
            self.next = (self.next + 1) % P.max(1);
        }
    }

    /// The age of the splice from `peer` over `relay`, if one was seen.
    pub fn age(&self, now: u64, relay: u8, peer: &NodeId) -> Option<u64> {
        self.peers
            .iter()
            .flatten()
            .find(|s| s.peer == *peer && s.relay == relay)
            .map(|s| now.saturating_sub(s.at))
    }

    /// SPLICE_LIVE: the address of the hub's UDP session if it spliced down to us within `max(30 s, 2 x rtt)`.
    pub fn live(&self, now: u64, relay: u8, rtt: u64) -> Option<SocketAddr> {
        let (at, a) = self.live.get(usize::from(relay)).copied().flatten()?;
        let span = if rtt.saturating_mul(2) > SPL_LIVE {
            rtt.saturating_mul(2)
        } else {
            SPL_LIVE
        };
        (now.saturating_sub(at) < span).then_some(a)
    }
}
