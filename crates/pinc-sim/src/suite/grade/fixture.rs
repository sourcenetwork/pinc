//! A minimal [`World`] for tests and tools that grade a recording without generating a scenario.
//!
//! Invariant: the world is internally consistent (sites, nodes and regions line up) and carries the reference
//! defaults for every cap, so a test overrides only the fields it is about.

use std::collections::BTreeMap;

use crate::suite::rec::NS;
use crate::suite::world::model::{NodeSpec, Site, World};

/// A world of `nodes` desktop nodes, one site each in region 0 (10 ms one way up and 10 ms down), running
/// `duration_ns`, with an idle window over the last tenth, no environment, no intents and the reference caps.
pub fn blank_world(id: &str, nodes: usize, duration_ns: u64) -> World {
    let sites = (0..nodes)
        .map(|i| Site {
            sid: i,
            region: 0,
            up_bps: 10_000_000,
            down_bps: 50_000_000,
            up_delay_ns: 10_000_000,
            down_delay_ns: 10_000_000,
            loss: 0.0,
            burst_ns: 0,
            queue_bytes: 65_536,
            nats: Vec::new(),
            v6_open: false,
            mtu: 1500,
            middlebox: None,
        })
        .collect();
    let node_specs = (0..nodes)
        .map(|i| NodeSpec {
            device: "desktop".to_owned(),
            site: i,
            kind: "home".to_owned(),
            region: 0,
            ifaces: Vec::new(),
            topics: Vec::new(),
            sites: vec![i],
            clock: None,
            cpu_factor: None,
        })
        .collect();
    World {
        id: id.to_owned(),
        seed: 0,
        params: BTreeMap::new(),
        sites,
        nodes: node_specs,
        region_delay_ns: vec![vec![40_000_000]],
        bootstrap: Vec::new(),
        duration_ns,
        idle_window: (duration_ns / 10 * 9, duration_ns),
        env: Vec::new(),
        intents: Vec::new(),
        values: BTreeMap::new(),
        provides: BTreeMap::new(),
        changes: Vec::new(),
        denied: Vec::new(),
        revoked: Vec::new(),
        connect_deadline_ns: 30 * NS,
        acp_latency_ns: 100_000,
        acp_validity_ns: 60 * NS,
        revocation_bound_cap_ns: 5 * NS,
        awareness_bound_cap_ns: 150 * NS,
        false_suspicion_cap: 1.0,
        score_c3: false,
        clouds: Vec::new(),
        homes: Vec::new(),
        mobiles: Vec::new(),
        hostile: Vec::new(),
        browsers: Vec::new(),
        liars: Vec::new(),
        soak: false,
        partitions: Vec::new(),
        adversary: None,
        adversary_env: Vec::new(),
        compromise: Vec::new(),
        compromise_node: None,
        eclipse_victim: None,
        sets: BTreeMap::new(),
        set_profiles: BTreeMap::new(),
        load_used: BTreeMap::new(),
    }
}
