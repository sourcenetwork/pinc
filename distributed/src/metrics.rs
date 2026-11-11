//! What the kernel measures per node, read from files it keeps: CPU time from the node's cgroup (`cpu.stat`), peak
//! memory (`memory.peak`), bytes and packets per interface (`/proc/<pid>/net/dev` of the node's namespace) and the
//! shapers' counters (`tc -s -j qdisc show` in a router's namespace). Kept apart from what the node programs report.
//!
//! Invariants: parsing never fails on unknown lines or fields (they are skipped); a counter that is missing reads as
//! absent, never as zero.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// The counters of one interface.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Iface {
    /// Bytes received.
    pub rx_bytes: u64,
    /// Packets received.
    pub rx_packets: u64,
    /// Packets dropped on receive.
    pub rx_drops: u64,
    /// Bytes sent.
    pub tx_bytes: u64,
    /// Packets sent.
    pub tx_packets: u64,
    /// Packets dropped on send.
    pub tx_drops: u64,
}

impl Iface {
    /// What changed from `before` to `self`.
    #[must_use]
    pub fn since(&self, before: &Self) -> Self {
        Self {
            rx_bytes: self.rx_bytes.saturating_sub(before.rx_bytes),
            rx_packets: self.rx_packets.saturating_sub(before.rx_packets),
            rx_drops: self.rx_drops.saturating_sub(before.rx_drops),
            tx_bytes: self.tx_bytes.saturating_sub(before.tx_bytes),
            tx_packets: self.tx_packets.saturating_sub(before.tx_packets),
            tx_drops: self.tx_drops.saturating_sub(before.tx_drops),
        }
    }
}

/// Parse `/proc/net/dev`: interface name to counters.
pub fn parse_net_dev(text: &str) -> BTreeMap<String, Iface> {
    let mut out = BTreeMap::new();
    for line in text.lines() {
        let Some((name, rest)) = line.split_once(':') else { continue };
        let f: Vec<u64> = rest.split_whitespace().filter_map(|x| x.parse().ok()).collect();
        // receive: bytes packets errs drop fifo frame compressed multicast; transmit: bytes packets errs drop ...
        if f.len() < 12 {
            continue;
        }
        let g = |i: usize| f.get(i).copied().unwrap_or(0);
        out.insert(
            name.trim().to_owned(),
            Iface {
                rx_bytes: g(0),
                rx_packets: g(1),
                rx_drops: g(3),
                tx_bytes: g(8),
                tx_packets: g(9),
                tx_drops: g(11),
            },
        );
    }
    out
}

/// The CPU time a cgroup has used, in microseconds, from its `cpu.stat`.
pub fn parse_cpu_usec(text: &str) -> Option<u64> {
    text.lines().find_map(|l| l.strip_prefix("usage_usec ")?.trim().parse().ok())
}

/// The counters of one queueing discipline.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Qdisc {
    /// The device.
    pub dev: String,
    /// The kind (`netem`, `ingress`, ...).
    pub kind: String,
    /// Bytes sent through it.
    pub bytes: u64,
    /// Packets sent through it.
    pub packets: u64,
    /// Packets it dropped: emulated loss and a full queue both count.
    pub drops: u64,
    /// Bytes waiting in it now.
    pub backlog: u64,
    /// Packets waiting in it now.
    pub qlen: u64,
}

/// Parse `tc -s -j qdisc show`.
pub fn parse_tc(text: &str) -> Vec<Qdisc> {
    let Ok(serde_json::Value::Array(items)) = serde_json::from_str::<serde_json::Value>(text) else {
        return Vec::new();
    };
    items
        .iter()
        .filter_map(|q| {
            let n = |k: &str| q.get(k).and_then(serde_json::Value::as_u64).unwrap_or(0);
            Some(Qdisc {
                dev: q.get("dev")?.as_str()?.to_owned(),
                kind: q.get("kind")?.as_str()?.to_owned(),
                bytes: n("bytes"),
                packets: n("packets"),
                drops: n("drops"),
                backlog: n("backlog"),
                qlen: n("qlen"),
            })
        })
        .collect()
}

/// One reading of a node.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct Reading {
    /// CPU time of every process of the node, in microseconds.
    pub cpu_usec: Option<u64>,
    /// The node's interface.
    pub eth0: Option<Iface>,
}

/// What the kernel measured for a node over one run.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct NodeUse {
    /// CPU seconds.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cpu_s: Option<f64>,
    /// Peak memory of the node's cgroup (processes, page cache and socket buffers), MiB.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub peak_mib: Option<f64>,
    /// The interface's counters over the run.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub eth0: Option<Iface>,
}

impl NodeUse {
    /// The use between two readings, with the peak read separately.
    // CPU microseconds and memory bytes of one run fit an f64's integer range.
    #[allow(clippy::cast_precision_loss)]
    pub fn between(before: &Reading, after: &Reading, peak_bytes: Option<u64>) -> Self {
        Self {
            cpu_s: before
                .cpu_usec
                .zip(after.cpu_usec)
                .map(|(b, a)| a.saturating_sub(b) as f64 / 1e6),
            peak_mib: peak_bytes.map(|p| p as f64 / 1_048_576.0),
            eth0: before.eth0.zip(after.eth0).map(|(b, a)| a.since(&b)),
        }
    }
}
