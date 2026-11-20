//! Configuration, path identity and the counters a connection exposes.

use pinc_security::LocalIdentity;
use pinc_security::{AlpnList, PrekeyInfo, Ticket};

use super::params::{CreditRecord, credit_for_streams};
use crate::recovery::{MS, PathKind, SECOND};
use crate::stream;

/// The smallest datagram every path must carry, and the size a path starts at.
pub const MIN_MTU: u16 = 1200;
/// The first size probed after the handshake: a 1500-byte interface less the IPv6 and UDP headers.
pub const PROBE_MTU: u16 = 1452;
/// The IPv4 and UDP headers an interface's datagram carries beyond its UDP payload.
pub const HEADERS_V4: u16 = 28;
/// The IPv6 and UDP headers an interface's datagram carries beyond its UDP payload.
pub const HEADERS_V6: u16 = 48;
/// The largest size probed on a low-latency path (UDP, round trip under 2 ms, and only above 2904 bytes).
pub const JUMBO_MTU: u16 = 8952;
/// A path whose minimum round trip is under this (2 ms) also probes the jumbo size.
pub(super) const JUMBO_RTT: u64 = 2 * MS;
/// Silence after which a connection closes without a CLOSE: fixed at 75 s, the same on every node.
pub const IDLE_TIMEOUT: u64 = 75 * SECOND;
/// A jumbo probe is only worth sending when the size is above this (twice the first probe size).
pub(super) const JUMBO_FLOOR: u16 = 2 * PROBE_MTU;

/// An opaque name for a network path, chosen by the endpoint (a UDP address, or a relay carrier).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PathId(pub u64);

/// The largest UDP payload an interface of `interface_mtu` bytes (IP and UDP headers included) carries on a path of
/// the given address family. Every size sent against the interface is bounded by it. A path still starts at
/// [`MIN_MTU`] whatever it returns: the callers take the larger of the two, so an interface below the minimum is not
/// a reason to send less.
#[must_use]
pub const fn interface_payload(interface_mtu: u16, v6: bool) -> u16 {
    interface_mtu.saturating_sub(if v6 { HEADERS_V6 } else { HEADERS_V4 })
}

/// What the endpoint knows about a path and the connection cannot learn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PathInfo {
    /// A direct path, or one through a relay (a relay carries a one second penalty when choosing the active path).
    pub kind: PathKind,
    /// Whether the path is IPv6 (it gets a 3 ms bonus when choosing the active path).
    pub v6: bool,
    /// The MTU of the local interface this path leaves by, IP and UDP headers included; the connection takes the
    /// headers off ([`interface_payload`]) before it bounds a datagram or a probe.
    pub interface_mtu: u16,
}

impl Default for PathInfo {
    fn default() -> Self {
        Self {
            kind: PathKind::Direct,
            v6: false,
            interface_mtu: 1500,
        }
    }
}

/// How a connection behaves. [`Config::new`] holds the defaults.
#[derive(Debug, Clone, Copy)]
#[allow(clippy::struct_excessive_bools, reason = "independent switches of one connection")]
pub struct Config {
    /// The length of the connection ids this endpoint issues, 1 to 20 (4 by default).
    pub cid_len: usize,
    /// Send a PING after this long without sending anything; `None` turns keepalives off.
    pub keepalive: Option<u64>,
    /// A node on a constrained link: caps the handshake back-off at `max(8 s, 2 x node_peak_rtt)`, gives an
    /// unestablished handshake 60 s instead of 30 s, and re-challenges idle direct paths.
    pub thin: bool,
    /// The round trip remembered from an earlier connection to the same peer; scales the handshake timer.
    pub remembered_rtt: Option<u64>,
    /// The node's average handshake round trip, in nanoseconds; the handshake timer uses it when no round trip is
    /// remembered for the peer, and its cap is `max(16 s, 4 x node_rtt)`. A node whose `node_rtt` or `node_peak_rtt`
    /// is 250 ms or more counts as thin.
    pub node_rtt: Option<u64>,
    /// The node's largest recent round trip, in nanoseconds; a thin node's handshake back-off stops at
    /// `max(8 s, 2 x node_peak_rtt)`.
    pub node_peak_rtt: Option<u64>,
    /// The most same-size datagrams one [`poll_transmit`](super::Connection::poll_transmit) call batches (1 = no GSO).
    pub max_gso: usize,
    /// Start a key roll after the sending key sealed this many packets.
    pub key_update_after: u64,
    /// Whether to probe larger datagram sizes after the handshake (UDP paths only, never on a thin node).
    pub probe_mtu: bool,
    /// Send the first handshake flight whole when it fits one datagram (1452 bytes or less), and split only the
    /// retransmissions into datagram-sized fragments. Off by default: every flight is fragmented to the minimum
    /// datagram size.
    pub flight_split: bool,
    /// Whether a burst that drained the send queue on a lossy direct path may be followed by a tail repair packet. Off
    /// for the sessions of a node that serves a relay.
    pub tail_repair: bool,
    /// The slack of the rate gate on round trips between 2 ms and 250 ms, in bytes; `None` keeps the default.
    pub gate_slack: Option<u64>,
    /// Acknowledge every this-many ack-eliciting packets instead of every 2nd (3rd for bulk): 4 for a member's
    /// session with a hub. `None` keeps the default policy.
    pub ack_every: Option<u32>,
    /// The most data the connection keeps written and not yet acknowledged, over all its streams: the cap is
    /// `min(send_window, max(192 KiB, 1.5 x the congestion window))`. A path whose bandwidth times round trip is larger
    /// than this needs a larger value.
    pub send_window: u64,
    /// The MTU of the host's interface, IP and UDP headers included (1500 unless the host says otherwise); the
    /// transport takes the headers off ([`interface_payload`]) to bound the datagram size probes and the whole first
    /// flight, on paths the connection learns of by receiving on them too.
    pub interface_mtu: u16,
    /// What this endpoint tells the peer about its limits (see [`CreditRecord`]); the window and the stream limit
    /// are clamped to what the stream table can hold, and the table runs with them: the window is the one every stream
    /// starts with, the stream limit the most streams the peer has live at once. The idle timeout is not part of it:
    /// it is the fixed [`IDLE_TIMEOUT`].
    pub credit: CreditRecord,
}

/// The default [`Config::send_window`] (1.25 MiB, the figure the reference's rule uses).
pub const DEFAULT_SEND_WINDOW: u64 = 1_310_720;

impl Config {
    /// The defaults.
    pub const fn new() -> Self {
        Self {
            cid_len: 4,
            keepalive: None,
            thin: false,
            remembered_rtt: None,
            node_rtt: None,
            node_peak_rtt: None,
            max_gso: 1,
            key_update_after: 1 << 21,
            probe_mtu: true,
            flight_split: false,
            tail_repair: true,
            gate_slack: None,
            ack_every: None,
            interface_mtu: 1500,
            send_window: DEFAULT_SEND_WINDOW,
            credit: credit_for_streams(&stream::Config::new(false)),
        }
    }
}

impl Default for Config {
    fn default() -> Self {
        Self::new()
    }
}

/// What a client needs to dial.
#[derive(Debug)]
pub struct ClientParams<'a> {
    /// The node being dialed.
    pub peer: pinc_crypto::NodeId,
    /// The application protocol.
    pub alpn: &'a [u8],
    /// This node's identity.
    pub identity: &'a LocalIdentity,
    /// The prekey for this handshake.
    pub prekey: &'a PrekeyInfo,
    /// Whether the peer is known to cache the prekey (try the short first flight).
    pub peer_has_prekey: bool,
    /// A ticket for this peer and protocol: the connection resumes and may send 0-RTT data.
    pub ticket: Option<Ticket>,
    /// The path the first flight leaves on.
    pub path: PathId,
    /// What the endpoint knows about that path.
    pub path_info: PathInfo,
}

/// What a server needs to answer.
#[derive(Debug, Clone)]
pub struct ServerParams {
    /// This node's identity.
    pub identity: LocalIdentity,
    /// The application protocols served.
    pub alpns: AlpnList,
    /// Tickets issued per full handshake (at most 4; 0 turns resumption off).
    pub tickets_per_session: u8,
    /// How long an issued ticket lives, in seconds.
    pub ticket_lifetime_s: u32,
}

/// Counters of one connection.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stats {
    /// Datagrams sent.
    pub datagrams_sent: u64,
    /// Datagrams received and attributed to the connection.
    pub datagrams_received: u64,
    /// Packets sent, long and short.
    pub packets_sent: u64,
    /// Packets received and authenticated.
    pub packets_received: u64,
    /// Bytes sent.
    pub bytes_sent: u64,
    /// Bytes received.
    pub bytes_received: u64,
    /// Packets declared lost.
    pub packets_lost: u64,
    /// Packets acknowledged.
    pub packets_acked: u64,
    /// Received packets dropped as duplicates.
    pub duplicates: u64,
    /// Received packets that did not authenticate.
    pub undecryptable: u64,
    /// Handshake messages dropped because they did not authenticate (forged or damaged): the handshake goes on.
    pub handshake_dropped: u64,
    /// Packets kept because they arrived before the handshake gave the keys to open them (0-RTT packets ahead of
    /// the Hello, 1-RTT packets ahead of the message that establishes the session).
    pub early_buffered: u64,
    /// Such packets dropped because the buffer was full.
    pub early_dropped: u64,
    /// 0-RTT packets dropped whole because they carried a frame that only an established session sends.
    pub early_refused: u64,
    /// Handshake flights sent again on the timer.
    pub handshake_retransmits: u64,
    /// Key updates, started here or by the peer.
    pub key_updates: u64,
    /// Probe timeouts that fired.
    pub ptos: u64,
    /// Peer streams held back for want of room (see `StreamStats::held_back`).
    pub held_back: u64,
    /// Repair packets sent.
    pub repairs: u64,
    /// Path MTU probe outcomes refused: an echo with no probe of that size in flight or above the path's ceiling, an
    /// acknowledgement or loss naming another probe than the one in flight.
    pub probe_outcomes_dropped: u64,
    /// Datagrams dropped from the send queue to make room.
    pub datagrams_dropped_send: u64,
    /// Datagrams dropped from the receive queue to make room.
    pub datagrams_dropped_recv: u64,
    /// Events the application cannot recover that were dropped because the event queue held nothing else to give up;
    /// 0 while the queue is sized for the stream slots and paths.
    pub events_lost: u64,
    /// The current congestion window in bytes.
    pub cwnd: u64,
    /// The smoothed round trip of the active path in nanoseconds, 0 before the first sample.
    pub srtt: u64,
    /// The datagram size of the active path.
    pub mtu: u16,
}
