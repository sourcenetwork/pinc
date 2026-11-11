//! The broadcast and membership layers of the node as an [`OnTop`] slot of the application.
//!
//! The VINC node carries broadcast and membership itself, so this layer holds no protocol: it sends the application's
//! subscribe and publish commands to the node through the [`Host`] and turns the node's messages and membership
//! events into [`OnTopEvent`]s for the application's accounting.
//!
//! Invariants: events leave in the order the node reported them; a stopped node forgets the events it had not yet
//! handed over.

use std::collections::VecDeque;

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
