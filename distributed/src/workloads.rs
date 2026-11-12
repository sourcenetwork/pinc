//! The real workloads of a scenario file: publish and subscribe, syncing a value, and reconciling two sets, with the
//! checks that tell the dashboard what is wrong with them. They run on node programs that stay up for a whole
//! repetition (see `node::app`), unlike the transport tests, which start a program per measurement.
//!
//! Invariants: a workload that validates names existing nodes, has a hub or relay node every other node can reach (every
//! stack joins through it), and asks for sizes the nodes' memory holds.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::scenario::{NodeSpec, Problem, Role, Scenario};

/// Publish and subscribe: some nodes publish messages at a rate, every node takes part in the topic, and the
/// subscribers' deliveries are counted.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Pubsub {
    /// The topic.
    #[serde(default = "topic_default")]
    pub topic: String,
    /// The nodes that publish.
    pub publishers: Vec<String>,
    /// The nodes whose deliveries count; empty means every node that is not a hub or relay (every node when there is
    /// none).
    #[serde(default)]
    pub subscribers: Vec<String>,
    /// Messages each publisher sends.
    pub messages: u32,
    /// Bytes of each message, including its 16-byte header.
    #[serde(default = "size_default")]
    pub size: u32,
    /// Messages per second from each publisher.
    #[serde(default = "rate_default")]
    pub rate_hz: f64,
    /// The longest wait for a node to join the topic, in seconds.
    #[serde(default = "join_default")]
    pub join_s: u64,
    /// Seconds between everyone having joined and the first message, for the group to settle.
    #[serde(default = "warmup_default")]
    pub warmup_s: f64,
    /// Seconds after the last message before the counts are read.
    #[serde(default = "drain_default")]
    pub drain_s: f64,
    /// The largest iroh gossip message, as an application on iroh sets it (defradb.rs keeps iroh-gossip's default of
    /// 4096 bytes); unset, the harness's 1 MiB. A message over it is not delivered, and the counts show that.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub iroh_gossip_max: Option<u32>,
}

fn topic_default() -> String {
    "bench".into()
}
fn size_default() -> u32 {
    256
}
fn rate_default() -> f64 {
    50.0
}
fn join_default() -> u64 {
    30
}
fn warmup_default() -> f64 {
    5.0
}
fn drain_default() -> f64 {
    5.0
}
fn timeout_default() -> u64 {
    600
}

/// Syncing a value: provider nodes hold a value, consumer nodes fetch it, for each size in turn.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ValueSync {
    /// The nodes that hold the value; several means the consumer may fetch from all of them.
    pub providers: Vec<String>,
    /// The nodes that fetch it, all at once.
    pub consumers: Vec<String>,
    /// The sizes, in bytes, one after the other.
    pub sizes: Vec<u64>,
    /// The longest one fetch may take, in seconds.
    #[serde(default = "timeout_default")]
    pub timeout_s: u64,
    /// Seconds between everyone having joined and the first fetch.
    #[serde(default = "warmup_default")]
    pub warmup_s: f64,
}

/// Reconciling two sets that differ in a few items.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Reconcile {
    /// One holder.
    pub a: String,
    /// The other, which starts the round.
    pub b: String,
    /// Set sizes, one after the other.
    pub items: Vec<u32>,
    /// How many items differ (on each side), one after the other.
    pub differences: Vec<u32>,
    /// The longest one round may take, in seconds.
    #[serde(default = "timeout_default")]
    pub timeout_s: u64,
    /// Seconds between everyone having joined and the first round.
    #[serde(default = "warmup_default")]
    pub warmup_s: f64,
}

/// A size as a test id and a heading show it: `1kib`, `64mib`, `1500b`.
pub fn size_id(bytes: u64) -> String {
    for (unit, name) in [(1u64 << 30, "gib"), (1 << 20, "mib"), (1 << 10, "kib")] {
        if bytes >= unit && bytes.is_multiple_of(unit) {
            return format!("{}{name}", bytes / unit);
        }
    }
    format!("{bytes}b")
}

impl Pubsub {
    /// The test id of the results.
    pub fn id(&self) -> String {
        "pubsub".into()
    }

    /// The subscribers: the named ones, or every node that is not a hub or relay, or every node.
    pub fn subscribers_of<'a>(&'a self, nodes: &'a [NodeSpec]) -> Vec<&'a str> {
        if !self.subscribers.is_empty() {
            return self.subscribers.iter().map(String::as_str).collect();
        }
        let peers: Vec<&str> = nodes
            .iter()
            .filter(|n| n.role == Role::Peer)
            .map(|n| n.name.as_str())
            .collect();
        if peers.is_empty() {
            nodes.iter().map(|n| n.name.as_str()).collect()
        } else {
            peers
        }
    }

    pub(crate) fn check(&self, sc: &Scenario, nodes: &BTreeMap<&str, &NodeSpec>, out: &mut Vec<Problem>) {
        check_names("workload.publishers", &self.publishers, nodes, out);
        check_names("workload.subscribers", &self.subscribers, nodes, out);
        if self.publishers.is_empty() {
            out.push(Problem::new("workload.publishers", "name at least one publishing node"));
        }
        if !(1..=1_000_000).contains(&self.messages) {
            out.push(Problem::new(
                "workload.messages",
                "use 1 to 1000000 messages per publisher",
            ));
        }
        if !(16..=(1 << 20)).contains(&self.size) {
            out.push(Problem::new("workload.size", "use 16 bytes to 1 MiB"));
        }
        if !(self.rate_hz.is_finite() && (0.01..=1_000_000.0).contains(&self.rate_hz)) {
            out.push(Problem::new(
                "workload.rate_hz",
                "use 0.01 to 1000000 messages per second",
            ));
        }
        if !(1..=3600).contains(&self.join_s) {
            out.push(Problem::new("workload.join_s", "use 1 to 3600 seconds"));
        }
        for (field, v) in [("warmup_s", self.warmup_s), ("drain_s", self.drain_s)] {
            if !(v.is_finite() && (0.0..=3600.0).contains(&v)) {
                out.push(Problem::new(format!("workload.{field}"), "use 0 to 3600 seconds"));
            }
        }
        if self.iroh_gossip_max.is_some_and(|m| !(512..=(1 << 20)).contains(&m)) {
            out.push(Problem::new("workload.iroh_gossip_max", "use 512 bytes to 1 MiB"));
        }
        if self.topic.is_empty() || self.topic.len() > 64 {
            out.push(Problem::new("workload.topic", "use a topic of 1 to 64 characters"));
        }
        check_group(sc, nodes, out);
    }
}

impl ValueSync {
    /// The test id of one size.
    pub fn id(size: u64) -> String {
        format!("sync_{}", size_id(size))
    }

    pub(crate) fn check(&self, sc: &Scenario, nodes: &BTreeMap<&str, &NodeSpec>, out: &mut Vec<Problem>) {
        check_names("workload.providers", &self.providers, nodes, out);
        check_names("workload.consumers", &self.consumers, nodes, out);
        if self.providers.is_empty() || self.consumers.is_empty() {
            out.push(Problem::new("workload", "name at least one provider and one consumer"));
        }
        if self.providers.iter().any(|p| self.consumers.contains(p)) {
            out.push(Problem::new(
                "workload.consumers",
                "a node cannot both provide and fetch",
            ));
        }
        if self.sizes.is_empty() {
            out.push(Problem::new("workload.sizes", "add at least one size"));
        }
        // The consumer holds the value and the stack's own copy while it verifies: keep well inside the node's memory.
        let room = u64::from(sc.resources.memory_mib) * (1 << 20) * 4 / 10;
        for (i, s) in self.sizes.iter().enumerate() {
            if !(1..=room).contains(s) {
                out.push(Problem::new(
                    format!("workload.sizes[{i}]"),
                    "use a size from 1 byte up to 40% of a node's memory",
                ));
            }
        }
        if !(1..=86_400).contains(&self.timeout_s) {
            out.push(Problem::new("workload.timeout_s", "use 1 to 86400 seconds"));
        }
        check_group(sc, nodes, out);
    }
}

impl Reconcile {
    /// The test id of one pair of numbers.
    pub fn id(items: u32, diff: u32) -> String {
        format!("reconcile_{items}_{diff}")
    }

    pub(crate) fn check(&self, sc: &Scenario, nodes: &BTreeMap<&str, &NodeSpec>, out: &mut Vec<Problem>) {
        check_names("workload", &[self.a.clone(), self.b.clone()], nodes, out);
        if self.a == self.b {
            out.push(Problem::new("workload.b", "the two holders are different nodes"));
        }
        if self.items.is_empty() || self.items.iter().any(|n| !(1..=1_000_000).contains(n)) {
            out.push(Problem::new(
                "workload.items",
                "use 1 to 1000000 items, at least one size",
            ));
        }
        if self.differences.is_empty() {
            out.push(Problem::new(
                "workload.differences",
                "add at least one number of differences",
            ));
        }
        let smallest = self.items.iter().min().copied().unwrap_or(0);
        if self.differences.iter().any(|d| *d > smallest) {
            out.push(Problem::new(
                "workload.differences",
                "no more items can differ than the smallest set holds",
            ));
        }
        if !(1..=86_400).contains(&self.timeout_s) {
            out.push(Problem::new("workload.timeout_s", "use 1 to 86400 seconds"));
        }
        check_group(sc, nodes, out);
    }
}

fn check_names(path: &str, names: &[String], nodes: &BTreeMap<&str, &NodeSpec>, out: &mut Vec<Problem>) {
    for (i, n) in names.iter().enumerate() {
        if !nodes.contains_key(n.as_str()) {
            out.push(Problem::new(format!("{path}[{i}]"), "no node has this name"));
        }
    }
}

/// Every stack joins through the hub and relay nodes, so one must exist and every node must reach one.
pub(crate) fn check_group(sc: &Scenario, nodes: &BTreeMap<&str, &NodeSpec>, out: &mut Vec<Problem>) {
    let hubs: Vec<&&NodeSpec> = nodes.values().filter(|n| n.role != Role::Peer).collect();
    let Some(first) = hubs.first() else {
        out.push(Problem::new(
            "nodes",
            "give one node the role hub or relay: every stack joins the group through it",
        ));
        return;
    };
    let reach: BTreeSet<usize> = hubs.iter().flat_map(|h| sc.reachable(h.site)).collect();
    let linked = sc.reachable(first.site);
    if nodes.values().any(|n| !reach.contains(&n.site)) || hubs.iter().any(|h| !linked.contains(&h.site)) {
        out.push(Problem::new(
            "links",
            "every node must have a path of links to a hub or relay node, and the hubs to each other",
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes_have_short_ids() {
        assert_eq!(size_id(1024), "1kib");
        assert_eq!(size_id(256 << 20), "256mib");
        assert_eq!(size_id(1500), "1500b");
        assert_eq!(size_id(3 << 30), "3gib");
        assert_eq!(ValueSync::id(1 << 20), "sync_1mib");
        assert_eq!(Reconcile::id(1000, 10), "reconcile_1000_10");
    }
}
