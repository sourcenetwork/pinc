//! The layers the node carries (broadcast and membership, values, reconcile) as [`OnTop`] slots of the application.
//!
//! The VINC node carries broadcast and membership itself, so this layer holds no protocol: it sends the application's
//! subscribe and publish commands to the node through the [`Host`] and turns the node's messages and membership
//! events into [`OnTopEvent`]s for the application's accounting.
//!
//! Invariants: events leave in the order the node reported them; a stopped node forgets the events it had not yet
//! handed over.

use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;

use super::shared::Shared;
use crate::suite::crypto::MsgId;

use crate::suite::proto::host::{Host, LayerEvent};
use crate::suite::proto::ontop::{Command, OnTop, OnTopEvent};

/// The broadcast and membership slot of a node; see the module docs.
#[derive(Debug, Default)]
pub struct NodeLayer {
    events: VecDeque<OnTopEvent>,
}

impl OnTop for NodeLayer {
    fn alpns(&self) -> Vec<&'static [u8]> {
        Vec::new()
    }

    fn boot(&mut self, _now: u64, _host: &mut dyn Host) {
        self.events.clear();
    }

    fn command(&mut self, _now: u64, host: &mut dyn Host, cmd: Command) {
        // A refused publish is recorded by the host; a refused subscribe leaves the topic without deliveries, which
        // the delivery gates report.
        match cmd {
            Command::Subscribe { topic } => {
                host.subscribe(&topic);
            }
            Command::Publish { topic, msg } => {
                host.publish(&topic, &msg);
            }
            Command::Provide { .. } | Command::Fetch { .. } | Command::Reconcile { .. } => {}
        }
    }

    fn event(&mut self, _now: u64, _host: &mut dyn Host, ev: LayerEvent<'_>) {
        match ev {
            LayerEvent::Message { origin, body } => self.events.push_back(OnTopEvent::Message {
                origin,
                msg: body.to_vec(),
            }),
            LayerEvent::Member(m) => self.events.push_back(OnTopEvent::Member(m)),
            _ => {}
        }
    }

    fn timeout(&mut self, _now: u64, _host: &mut dyn Host) {}

    fn poll_timeout(&self) -> Option<u64> {
        None
    }

    fn poll_event(&mut self) -> Option<OnTopEvent> {
        self.events.pop_front()
    }

    fn stop(&mut self) {
        self.events.clear();
    }
}

/// The values slot of a node: the application's fetches go to the node's values layer, and its progress comes back
/// as the application's fetch events.
///
/// Invariants: a fetch the node refuses is reported failed at once; a stopped node forgets its fetches, because the
/// application asks again with new numbers when it boots.
pub struct NodeValues {
    shared: Rc<Shared>,
    idx: usize,
    fetches: BTreeMap<u32, u64>,
    events: VecDeque<OnTopEvent>,
}

impl NodeValues {
    /// The values slot of node `idx`.
    pub fn new(shared: Rc<Shared>, idx: usize) -> Self {
        Self {
            shared,
            idx,
            fetches: BTreeMap::new(),
            events: VecDeque::new(),
        }
    }

    fn root_of(&self, value: MsgId) -> Option<[u8; 32]> {
        self.shared.catalog.get(value).map(|v| v.root)
    }
}

impl OnTop for NodeValues {
    fn alpns(&self) -> Vec<&'static [u8]> {
        Vec::new()
    }

    fn boot(&mut self, _now: u64, _host: &mut dyn Host) {
        self.fetches.clear();
        self.events.clear();
    }

    fn command(&mut self, _now: u64, host: &mut dyn Host, cmd: Command) {
        // The values this node serves were handed to its store when the run was built.
        if let Command::Fetch {
            fetch_id,
            value,
            providers,
            ranges,
            deadline,
            ..
        } = cmd
        {
            match host.fetch(value, ranges.as_deref().unwrap_or(&[]), &providers, deadline) {
                Some(n) => {
                    self.fetches.insert(n, fetch_id);
                }
                None => self.events.push_back(OnTopEvent::FetchFailed { fetch_id }),
            }
        }
    }

    fn event(&mut self, _now: u64, _host: &mut dyn Host, ev: LayerEvent<'_>) {
        match ev {
            LayerEvent::ValueReadable { fetch, off, len } => {
                if let Some(&fetch_id) = self.fetches.get(&fetch) {
                    self.events.push_back(OnTopEvent::ValueReadable {
                        fetch_id,
                        offset: off,
                        length: len,
                    });
                }
            }
            LayerEvent::ValueComplete { fetch } => {
                if let Some(fetch_id) = self.fetches.remove(&fetch) {
                    self.events.push_back(OnTopEvent::FetchComplete { fetch_id });
                }
            }
            LayerEvent::ValueFailed { fetch } => {
                if let Some(fetch_id) = self.fetches.remove(&fetch) {
                    self.events.push_back(OnTopEvent::FetchFailed { fetch_id });
                }
            }
            _ => {}
        }
    }

    fn timeout(&mut self, _now: u64, _host: &mut dyn Host) {}

    fn poll_timeout(&self) -> Option<u64> {
        None
    }

    fn poll_event(&mut self) -> Option<OnTopEvent> {
        self.events.pop_front()
    }

    fn holds(&self, value: MsgId, offset: u64, len: u64) -> bool {
        let store = self.shared.values_of(self.idx);
        self.root_of(value)
            .zip(store)
            .is_some_and(|(root, s)| s.holds(&root, offset, len))
    }

    fn contiguous_from(&self, value: MsgId, offset: u64) -> u64 {
        let store = self.shared.values_of(self.idx);
        self.root_of(value)
            .zip(store)
            .map_or(0, |(root, s)| s.contiguous_from(&root, offset))
    }

    fn stop(&mut self) {
        self.fetches.clear();
        self.events.clear();
    }
}

/// The reconcile slot of a node: the application's sessions go to the node's sets layer and the exact difference comes
/// back as the application's result.
///
/// Invariants: a round the node refuses reports nothing (the application's intent stays undelivered); a stopped node
/// forgets its rounds.
pub struct NodeSets {
    rounds: BTreeMap<u32, Vec<u8>>,
    events: VecDeque<OnTopEvent>,
}

impl NodeSets {
    /// The reconcile slot of a node.
    pub fn new() -> Self {
        Self {
            rounds: BTreeMap::new(),
            events: VecDeque::new(),
        }
    }
}

impl Default for NodeSets {
    fn default() -> Self {
        Self::new()
    }
}

/// A set's items as 40-byte items; an item of another length is dropped, which the exactness check then reports.
fn items(v: &[Vec<u8>]) -> Vec<[u8; 40]> {
    v.iter().filter_map(|i| <[u8; 40]>::try_from(i.as_slice()).ok()).collect()
}

impl OnTop for NodeSets {
    fn alpns(&self) -> Vec<&'static [u8]> {
        Vec::new()
    }

    fn boot(&mut self, _now: u64, _host: &mut dyn Host) {
        self.rounds.clear();
        self.events.clear();
    }

    fn command(&mut self, _now: u64, host: &mut dyn Host, cmd: Command) {
        if let Command::Reconcile { set_ref, peer } = cmd
            && let Some(n) = host.reconcile(peer, &set_ref)
        {
            self.rounds.insert(n, set_ref);
        }
    }

    fn event(&mut self, _now: u64, _host: &mut dyn Host, ev: LayerEvent<'_>) {
        match ev {
            LayerEvent::ReconcileDone {
                round,
                missing_here,
                missing_there,
            } => {
                if let Some(set_ref) = self.rounds.remove(&round) {
                    self.events.push_back(OnTopEvent::ReconcileResult {
                        set_ref,
                        missing_here: items(missing_here),
                        missing_there: items(missing_there),
                    });
                }
            }
            LayerEvent::ReconcileFailed { round } => {
                self.rounds.remove(&round);
            }
            _ => {}
        }
    }

    fn timeout(&mut self, _now: u64, _host: &mut dyn Host) {}

    fn poll_timeout(&self) -> Option<u64> {
        None
    }

    fn poll_event(&mut self) -> Option<OnTopEvent> {
        self.events.pop_front()
    }

    fn stop(&mut self) {
        self.rounds.clear();
        self.events.clear();
    }
}
