//! Counters of a run: per-node traffic, per-node delivery latency and drops by reason.

use crate::Time;

/// Why the network discarded a datagram.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DropReason {
    /// The link was blocked (UDP blocked, an outage window).
    Blocked,
    /// The datagram was larger than the link MTU.
    Mtu,
    /// The loss model dropped it.
    Loss,
    /// The bandwidth queue was full.
    QueueFull,
    /// Sender and receiver were in different partition groups when it arrived.
    Partition,
    /// A NAT had no mapping, or the mapping's filter refused the sender.
    NatFilter,
    /// No link or no address to carry it.
    NoRoute,
    /// The interface was down or no longer has the destination address.
    NoIface,
    /// The receiving node was crashed.
    NodeDown,
    /// The receiving node was suspended.
    NodeAsleep,
    /// A middlebox dropped UDP (a UDP block or a captive portal).
    Middlebox,
}

impl DropReason {
    /// Every reason, in counter order.
    pub const ALL: [Self; 11] = [
        Self::Blocked,
        Self::Mtu,
        Self::Loss,
        Self::QueueFull,
        Self::Partition,
        Self::NatFilter,
        Self::NoRoute,
        Self::NoIface,
        Self::NodeDown,
        Self::NodeAsleep,
        Self::Middlebox,
    ];

    /// A short stable name, used in traces.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Blocked => "blocked",
            Self::Mtu => "mtu",
            Self::Loss => "loss",
            Self::QueueFull => "queue_full",
            Self::Partition => "partition",
            Self::NatFilter => "nat_filter",
            Self::NoRoute => "no_route",
            Self::NoIface => "no_iface",
            Self::NodeDown => "node_down",
            Self::NodeAsleep => "node_asleep",
            Self::Middlebox => "middlebox",
        }
    }
}

/// Delivery latency of datagrams that reached a node: send time to arrival time, in nanoseconds.
#[derive(Clone, Debug, Default)]
pub struct Latency {
    /// Datagrams measured.
    pub count: u64,
    /// Sum of the latencies.
    pub sum: u128,
    /// Smallest latency (meaningful when `count > 0`).
    pub min: Time,
    /// Largest latency.
    pub max: Time,
    /// Every latency in arrival order, kept only when the simulator is configured to.
    pub samples: Vec<Time>,
}

impl Latency {
    pub(crate) fn record(&mut self, v: Time, keep: bool) {
        self.min = if self.count == 0 { v } else { self.min.min(v) };
        self.max = self.max.max(v);
        self.count += 1;
        self.sum += u128::from(v);
        if keep {
            self.samples.push(v);
        }
    }

    /// The mean latency, or `None` when nothing was measured.
    pub fn mean(&self) -> Option<Time> {
        u64::try_from(self.sum.checked_div(u128::from(self.count))?).ok()
    }

    /// The `q` quantile (0 to 1) of the kept samples, or `None` when none were kept.
    pub fn quantile(&self, q: f64) -> Option<Time> {
        if self.samples.is_empty() {
            return None;
        }
        let mut s = self.samples.clone();
        s.sort_unstable();
        let i = ((s.len() - 1) as f64 * q.clamp(0.0, 1.0)).round() as usize;
        s.get(i).copied()
    }
}

/// Traffic and latency of one node.
#[derive(Clone, Debug, Default)]
pub struct NodeMetrics {
    /// Datagrams the node handed to the network.
    pub sent_packets: u64,
    /// Payload bytes the node handed to the network.
    pub sent_bytes: u64,
    /// Bytes on the wire the node produced: payload plus 28 (IPv4) or 48 (IPv6) header bytes per datagram. Counted
    /// before any drop in the network, but not for a datagram larger than the path MTU, which never leaves the node.
    pub wire_bytes: u64,
    /// Datagrams delivered to the node.
    pub recv_packets: u64,
    /// Bytes delivered to the node.
    pub recv_bytes: u64,
    /// Latency of the datagrams delivered to the node.
    pub latency: Latency,
}

/// All counters of a run.
#[derive(Clone, Debug, Default)]
pub struct Metrics {
    /// One entry per node, by node index.
    pub nodes: Vec<NodeMetrics>,
    pub(crate) drops: [u64; 11],
    /// Timeouts a node returned that were not strictly after a timer call (each was replaced by now plus 1 ms).
    pub timer_violations: u64,
    /// Datagrams the links duplicated.
    pub duplicated: u64,
    /// Datagrams adversaries injected (floods and replays).
    pub injected: u64,
}

impl Metrics {
    /// How many datagrams were discarded for `reason`.
    pub fn dropped(&self, reason: DropReason) -> u64 {
        self.drops.get(reason as usize).copied().unwrap_or(0)
    }

    /// Bytes on the wire from all nodes, counted before any drop in the network.
    pub fn wire_bytes(&self) -> u64 {
        self.nodes.iter().map(|n| n.wire_bytes).sum()
    }

    /// How many datagrams were discarded in all.
    pub fn total_dropped(&self) -> u64 {
        self.drops.iter().sum()
    }
}
