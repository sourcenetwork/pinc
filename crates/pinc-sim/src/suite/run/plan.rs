//! What of a world's workload can run: the layers a run has, the intents each needs, and the honest tally of the rest.
//!
//! [`plan`] decides, intent by intent, whether the run schedules it or lists it as waiting for a layer that does not
//! exist yet. A waiting intent is never scheduled, never recorded and never counted as delivered or failed, so a gate
//! that would need it has no samples instead of a verdict. The reasons are fixed strings: they are what the reports
//! print and what the tests compare.
//!
//! Invariants: planning is a pure function of the world and the layer set; every intent of the world lands in exactly
//! one of the scheduled list and the tally; a scenario with nothing runnable, or whose defining workload needs a
//! missing layer, is `Waiting` and is not run.

use std::collections::BTreeMap;

use crate::suite::world::model::{Intent, IntentKind, NodeSpec, World};

/// The reason of a publish intent while the broadcast layer is missing.
pub const WAIT_BROADCAST: &str = "waiting for the broadcast layer";
/// The reason of a fetch intent while the values layer is missing.
pub const WAIT_VALUES: &str = "waiting for the values layer";
/// The reason of a reconcile intent while the reconcile layer is missing.
pub const WAIT_RECONCILE: &str = "waiting for the reconcile layer";
/// The reason of an intent toward a node with no public address while the relay and rendezvous client is missing.
pub const WAIT_RELAY: &str = "waiting for connectivity (relay and rendezvous client)";
/// The reason of an intent with an end that cannot use UDP (a blocked host, a browser) while the carrier client is missing.
pub const WAIT_CARRIER: &str = "waiting for connectivity (carrier client side)";

/// The protocol layers a run has. A flag is true only when the runner registers the layer (see `Wiring` in the
/// runner); running with a flag set and no layer behind it is an error, never a silent pass.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LayerSet {
    /// Publish and subscribe.
    pub broadcast: bool,
    /// Value fetch and provide.
    pub values: bool,
    /// Set reconciliation.
    pub reconcile: bool,
    /// Membership events and the view (decides G-AWARE).
    pub membership: bool,
    /// The connectivity client side: direct paths through NAT, relay, hole punching and carriers.
    pub connectivity: bool,
}

impl LayerSet {
    /// No layer: the four harness protocols over core UDP only.
    pub const NONE: Self = Self {
        broadcast: false,
        values: false,
        reconcile: false,
        membership: false,
        connectivity: false,
    };

    /// What the PINC node carries: broadcast, values, reconcile, membership and the connectivity client with its
    /// relays.
    pub const NODE: Self = Self {
        broadcast: true,
        values: true,
        reconcile: true,
        membership: true,
        connectivity: true,
    };
}

/// How much of a scenario ran.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Status {
    /// Every intent ran with every layer present.
    Running,
    /// Part of the workload ran; the reasons say what did not. Never a pass by itself.
    Partial(Vec<String>),
    /// Nothing that defines the scenario can run yet; it was not run.
    Waiting(Vec<String>),
}

/// The plan of a run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan {
    /// Indices into `world.intents` of the intents the run schedules.
    pub scheduled: Vec<usize>,
    /// Intents listed as waiting, by reason.
    pub excluded: BTreeMap<&'static str, u64>,
    /// Scheduled intents by kind name.
    pub scheduled_kinds: BTreeMap<&'static str, u64>,
    /// How the scenario stands.
    pub status: Status,
}

fn udp_capable(world: &World, n: &NodeSpec) -> bool {
    n.ifaces.iter().any(|f| f.kind.starts_with("udp"))
        && !world
            .sites
            .get(n.site)
            .and_then(|s| s.middlebox.as_ref())
            .is_some_and(|m| m.udp_block)
}

fn public_udp(n: &NodeSpec) -> bool {
    n.ifaces.iter().any(|f| f.kind.starts_with("udp") && f.public)
}

/// Why `it` cannot run with `layers`, or `None` when it can.
fn blocked(world: &World, layers: LayerSet, it: &Intent) -> Option<&'static str> {
    match it.kind {
        IntentKind::Publish => return (!layers.broadcast).then_some(WAIT_BROADCAST),
        IntentKind::Fetch => return (!layers.values).then_some(WAIT_VALUES),
        IntentKind::Reconcile => return (!layers.reconcile).then_some(WAIT_RECONCILE),
        IntentKind::Push | IntentKind::Docsync | IntentKind::Manage | IntentKind::Echo => {}
    }
    if layers.connectivity {
        return None;
    }
    let (Some(a), Some(z)) = (world.nodes.get(it.node), it.to.and_then(|t| world.nodes.get(t))) else {
        return None;
    };
    if !udp_capable(world, a) || !udp_capable(world, z) {
        return Some(WAIT_CARRIER);
    }
    (!public_udp(z)).then_some(WAIT_RELAY)
}

fn kind_name(k: IntentKind) -> &'static str {
    match k {
        IntentKind::Publish => "publish",
        IntentKind::Push => "push",
        IntentKind::Docsync => "docsync",
        IntentKind::Manage => "manage",
        IntentKind::Echo => "echo",
        IntentKind::Fetch => "fetch",
        IntentKind::Reconcile => "reconcile",
    }
}

/// Plans the run of `world` with `layers`.
pub fn plan(world: &World, layers: LayerSet) -> Plan {
    let mut scheduled = Vec::new();
    let mut excluded: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut kinds: BTreeMap<&'static str, u64> = BTreeMap::new();
    for (i, it) in world.intents.iter().enumerate() {
        match blocked(world, layers, it) {
            None => {
                scheduled.push(i);
                *kinds.entry(kind_name(it.kind)).or_insert(0) += 1;
            }
            Some(why) => *excluded.entry(why).or_insert(0) += 1,
        }
    }
    let defining = match world.id.as_str() {
        "S11" if !layers.values => Some(WAIT_VALUES),
        "S14" if !layers.reconcile => Some(WAIT_RECONCILE),
        _ => None,
    };
    let status = if scheduled.is_empty() || defining.is_some() {
        let mut why: Vec<String> = excluded.keys().map(|r| (*r).to_owned()).collect();
        if let Some(d) = defining
            && !why.iter().any(|w| w == d)
        {
            why.push(d.to_owned());
        }
        if why.is_empty() {
            why.push("the scenario has no intents".to_owned());
        }
        Status::Waiting(why)
    } else {
        let mut why: Vec<String> = excluded.iter().map(|(r, n)| format!("{r}: {n} intents")).collect();
        if !layers.membership {
            why.push("waiting for the membership layer: G-AWARE is not evaluated".to_owned());
        }
        if why.is_empty() {
            Status::Running
        } else {
            Status::Partial(why)
        }
    };
    Plan {
        scheduled,
        excluded,
        scheduled_kinds: kinds,
        status,
    }
}
