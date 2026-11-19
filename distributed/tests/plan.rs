//! The orchestration logic that needs no root: scenario parsing and validation, the network plan (addresses, names,
//! routes, translation, CPU sets), the shaping commands, the helper's checks, the kernel-metric parsers and the result
//! aggregation.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

use std::collections::BTreeSet;

use pinc_distributed::helper::{gateway_conf, host_ns_allowed, readable};
use pinc_distributed::metrics::{Iface, NodeUse, Reading, parse_cpu_usec, parse_net_dev, parse_tc};
use pinc_distributed::plan::{Ns, Plan, Tool, cpu_sets, netem_args, queue_limit};
use pinc_distributed::quiet::{Monitor, Snapshot, Thresholds, parse_stat_line};
use pinc_distributed::results::{Cell, Row, Table, civil_date, fmt_cell, fmt_num, markdown, spread, summarize};
use pinc_distributed::scenario::{
    Nat, PincEndpoints, Reading as ReadingMode, Scenario, Shape, Stack, TransportTest, Workload,
};

fn scenario(name: &str) -> Scenario {
    let path = format!("{}/scenarios/{name}.toml", env!("CARGO_MANIFEST_DIR"));
    Scenario::parse(&std::fs::read_to_string(path).unwrap()).unwrap()
}

const EXAMPLES: [&str; 39] = [
    "port-mapping",
    "port-mapping-upnp",
    "port-mapping-none",
    "dtn-store-forward",
    "dtn-custody",
    "dtn-copies",
    "dtn-resume",
    "dtn-ledger",
    "dtn-tamper",
    "dtn-wake",
    "dtn-fragment",
    "dtn-parity",
    "lan",
    "lan-per-core",
    "wan",
    "lossy",
    "geo",
    "leo",
    "lte-rural",
    "low-bandwidth",
    "ble",
    "serial",
    "home-routers",
    "three-site",
    "pubsub-lan",
    "pubsub-wan",
    "sync-wan",
    "sync-trace",
    "sync-multi",
    "reconcile-wan",
    "partition-heal",
    "churn",
    "suspend-resume",
    "nat-reach",
    "punch-port-restricted",
    "punch-symmetric",
    "relay-server-hub",
    "relay-server-no-punch",
    "relay-server-punch",
];

#[test]
fn every_example_scenario_validates_and_round_trips() {
    for name in EXAMPLES {
        let sc = scenario(name);
        assert_eq!(sc.validate(), vec![], "{name}");
        let again = Scenario::parse(&sc.to_toml().unwrap()).unwrap();
        assert_eq!(again, sc, "{name} does not survive a save and a load");
    }
}

#[test]
fn pinc_endpoints_default_to_one_and_per_core_is_read_validated_and_refused_when_bad() {
    assert_eq!(scenario("lan").pinc_endpoints, PincEndpoints::One);
    let sc = scenario("lan-per-core");
    assert_eq!(sc.pinc_endpoints, PincEndpoints::PerCore);
    assert!(sc.to_toml().unwrap().contains("pinc_endpoints = \"per-core\""));
    // Every row of the scenario is a row per-core applies to: a test that runs on one endpoint would read as per-core.
    let Workload::Transport(t) = &sc.workload else {
        panic!("lan-per-core is a transport scenario")
    };
    assert!(
        t.tests.iter().all(|t| matches!(t, TransportTest::Many { .. })),
        "only the many test"
    );
    // The default is not written back, so a file made before the field existed stays as it was.
    assert!(!scenario("lan").to_toml().unwrap().contains("pinc_endpoints"));
    let text = std::fs::read_to_string(format!("{}/scenarios/lan-per-core.toml", env!("CARGO_MANIFEST_DIR"))).unwrap();
    let bad = Scenario::parse(&text.replace("\"per-core\"", "\"two\""));
    assert!(bad.is_err(), "a value that is neither one nor per-core is refused");
    // Per-core with nothing it applies to is a problem, not a silent no-op.
    let mut sc = scenario("lan-per-core");
    sc.stacks = vec![Stack::Iroh];
    let paths: BTreeSet<String> = sc.validate().into_iter().map(|p| p.path).collect();
    assert!(paths.contains("pinc_endpoints"), "{paths:?}");
    let mut sc = scenario("lan-per-core");
    if let Workload::Transport(t) = &mut sc.workload {
        t.tests.retain(|t| !matches!(t, TransportTest::Many { .. }));
    }
    let paths: BTreeSet<String> = sc.validate().into_iter().map(|p| p.path).collect();
    assert!(paths.contains("pinc_endpoints"), "{paths:?}");
    // A test that runs on one endpoint cannot stand in a per-core scenario, even beside a many test.
    let mut sc = scenario("lan-per-core");
    if let Workload::Transport(t) = &mut sc.workload {
        t.tests.push(TransportTest::Throughput {
            bytes: 1 << 20,
            streams: 1,
        });
    }
    let problems: Vec<_> = sc
        .validate()
        .into_iter()
        .filter(|p| p.path == "pinc_endpoints")
        .collect();
    assert_eq!(problems.len(), 1, "{problems:?}");
    assert!(problems[0].message.contains("throughput_1s"), "{problems:?}");
    let mut sc = scenario("pubsub-lan");
    sc.pinc_endpoints = PincEndpoints::PerCore;
    let paths: BTreeSet<String> = sc.validate().into_iter().map(|p| p.path).collect();
    assert!(paths.contains("pinc_endpoints"), "{paths:?}");
}

#[test]
fn the_many_test_reads_undriven_by_default_driven_on_request_and_names_each_reading() {
    for name in ["lan", "lan-per-core"] {
        let sc = scenario(name);
        let Workload::Transport(t) = &sc.workload else {
            panic!("{name} is a transport scenario")
        };
        let many: Vec<_> = t
            .tests
            .iter()
            .filter(|t| matches!(t, TransportTest::Many { .. }))
            .collect();
        assert_eq!(many.len(), 2, "{name} has the many test in both readings");
        assert_eq!(many[0].id(), "many", "{name}");
        assert_eq!(many[1].id(), "many_driven", "{name}");
        assert_eq!(
            many[0].scenario(),
            many[1].scenario(),
            "both print the result line `many`"
        );
        assert!(matches!(
            many[0],
            TransportTest::Many {
                reading: ReadingMode::Undriven,
                ..
            }
        ));
    }
    let text = std::fs::read_to_string(format!("{}/scenarios/lan.toml", env!("CARGO_MANIFEST_DIR"))).unwrap();
    let bad = text.replace("reading = \"driven\"", "reading = \"idle\"");
    assert!(
        Scenario::parse(&bad).is_err(),
        "a reading that is neither undriven nor driven is refused"
    );
}

#[test]
fn workload_problems_name_their_fields() {
    let mut sc = scenario("pubsub-lan");
    if let Workload::Pubsub(w) = &mut sc.workload {
        w.publishers = vec!["nobody".into()];
        w.messages = 0;
        w.size = 4;
        w.rate_hz = 0.0;
    }
    let paths: BTreeSet<String> = sc.validate().into_iter().map(|p| p.path).collect();
    for want in [
        "workload.publishers[0]",
        "workload.messages",
        "workload.size",
        "workload.rate_hz",
    ] {
        assert!(paths.contains(want), "no problem reported at {want}: {paths:?}");
    }

    // Every stack joins through a hub or relay node: without one the scenario cannot run.
    let mut sc = scenario("sync-wan");
    sc.nodes.retain(|g| g.name != "hub");
    let paths: BTreeSet<String> = sc.validate().into_iter().map(|p| p.path).collect();
    assert!(paths.contains("nodes"), "{paths:?}");

    // A value larger than the node can hold, and a node that both provides and fetches.
    let mut sc = scenario("sync-wan");
    if let Workload::Sync(w) = &mut sc.workload {
        w.sizes = vec![4 << 30];
        w.consumers.push("provider".into());
    }
    let paths: BTreeSet<String> = sc.validate().into_iter().map(|p| p.path).collect();
    assert!(paths.contains("workload.sizes[0]"), "{paths:?}");
    assert!(paths.contains("workload.consumers"), "{paths:?}");

    // More differences than items.
    let mut sc = scenario("reconcile-wan");
    if let Workload::Reconcile(w) = &mut sc.workload {
        w.differences = vec![5000];
    }
    let paths: BTreeSet<String> = sc.validate().into_iter().map(|p| p.path).collect();
    assert!(paths.contains("workload.differences"), "{paths:?}");
}

#[test]
fn a_node_behind_translation_is_known_by_its_routers_address() {
    let sc = scenario("nat-reach");
    let p = Plan::new(&sc, "RUN", 16);
    let n1 = p.node("n1").unwrap();
    let rv = p.node("rv").unwrap();
    assert_eq!(
        p.public_ip(rv),
        p.nodes[rv].ip,
        "a routed node is reached at its own address"
    );
    assert_ne!(
        p.public_ip(n1),
        p.nodes[n1].ip,
        "a translated node is seen at its router's"
    );
    assert!(
        p.links
            .iter()
            .any(|l| l.ip_a == p.public_ip(n1) || l.ip_b == p.public_ip(n1))
    );
}

#[test]
fn groups_expand_to_numbered_nodes() {
    let sc = scenario("three-site");
    let names: Vec<String> = sc.expand().into_iter().map(|n| n.name).collect();
    assert_eq!(names.len(), 33);
    assert!(names.contains(&"a-hub".to_owned()));
    assert!(names.contains(&"c-10".to_owned()));
    assert!(!names.contains(&"c-11".to_owned()));
}

#[test]
fn validation_reports_every_problem_with_its_path() {
    let mut sc = scenario("wan");
    sc.name = "Bad Name".into();
    sc.links[0].shape.loss_pct = 120.0;
    sc.nodes[1].site = "nowhere".into();
    sc.stacks.push(Stack::Pinc);
    let paths: BTreeSet<String> = sc.validate().into_iter().map(|p| p.path).collect();
    for want in ["name", "links[0].shape.loss_pct", "nodes[1].site", "stacks"] {
        assert!(paths.contains(want), "no problem reported at {want}: {paths:?}");
    }
}

#[test]
fn a_transport_server_behind_translation_is_refused_with_the_reason() {
    let mut sc = scenario("home-routers");
    let Workload::Transport(t) = &mut sc.workload else {
        panic!("the wan scenario is a transport scenario");
    };
    t.pairs[0].server = "n2".into();
    let p = sc.validate();
    assert!(
        p.iter()
            .any(|p| p.path == "workload.pairs[0].server" && p.message.contains("address translation")),
        "{p:?}"
    );
}

#[test]
fn unknown_fields_are_errors_not_silently_ignored() {
    let text = std::fs::read_to_string(format!("{}/scenarios/wan.toml", env!("CARGO_MANIFEST_DIR"))).unwrap();
    let bad = text.replace("repetitions = 3", "repetitions = 3\nrepetitons = 4");
    assert!(Scenario::parse(&bad).is_err());
}

#[test]
fn the_debug_table_asks_for_traces_and_defaults_to_off() {
    assert!(scenario("sync-trace").debug.trace);
    let sc = scenario("sync-wan");
    assert!(!sc.debug.trace);
    assert!(
        !sc.to_toml().unwrap().contains("[debug]"),
        "an untraced scenario saves without the table"
    );
    let on = scenario("sync-trace").to_toml().unwrap();
    assert!(Scenario::parse(&on).unwrap().debug.trace);
    let bad = on.replace("trace = true", "trace = true\ntraces = true");
    assert!(Scenario::parse(&bad).is_err());
}

#[test]
fn addresses_are_unique_and_names_fit_the_kernel() {
    for name in EXAMPLES {
        let sc = scenario(name);
        let p = Plan::new(&sc, "abc123", 16);
        let ips: BTreeSet<_> = p.nodes.iter().map(|n| n.ip).collect();
        assert_eq!(ips.len(), p.nodes.len(), "{name}");
        for v in &p.veths {
            assert!(v.a.1.len() <= 15 && v.b.1.len() <= 15);
        }
        for n in &p.nodes {
            assert!(n.port.len() <= 15 && n.ifb.len() <= 15);
            assert!(n.container.name.starts_with("vd-abc123-"));
        }
    }
}

#[test]
fn every_node_has_its_site_gateway_as_default_route() {
    let sc = scenario("three-site");
    let p = Plan::new(&sc, "r", 16);
    for (i, n) in p.nodes.iter().enumerate() {
        let gw = p.sites[n.site].gateway.to_string();
        let cmds = &p.setup.iter().find(|(ns, _)| *ns == Ns::Node(i)).unwrap().1;
        assert!(
            cmds.iter()
                .any(|c| c.tool == Tool::Ip && c.args == ["route", "add", "default", "via", gw.as_str()])
        );
        assert!(
            cmds.iter().any(|c| c.args.contains(&"gso_max_segs".to_owned())),
            "offloaded batches must be segmented in the node"
        );
    }
}

#[test]
fn routers_use_the_direct_link_and_route_every_routed_lan() {
    let sc = scenario("three-site");
    let p = Plan::new(&sc, "r", 16);
    let a = p.site("site-a").unwrap();
    let cmds = &p.setup.iter().find(|(ns, _)| *ns == Ns::Router(a)).unwrap().1;
    let routes: Vec<&Vec<String>> = cmds
        .iter()
        .filter(|c| c.args.first().map(String::as_str) == Some("route"))
        .map(|c| &c.args)
        .collect();
    // c's LAN is 10.3.0.0/24, and the a-c link is w2: a detour through b has less delay, but the direct link is taken.
    assert!(
        routes.iter().any(|r| r[2] == "10.3.0.0/24" && r[6] == "w2"),
        "{routes:?}"
    );
    assert!(
        routes.iter().any(|r| r[2] == "10.2.0.0/24" && r[6] == "w0"),
        "{routes:?}"
    );
}

#[test]
fn a_router_that_maps_ports_gets_unreserved_links_and_the_chains_miniupnpd_uses() {
    let mapped = Plan::new(&scenario("port-mapping"), "r", 16);
    let none = Plan::new(&scenario("port-mapping-none"), "r", 16);
    let (h1, h2) = (mapped.site("home1").unwrap(), mapped.site("home2").unwrap());
    // home1's link is numbered from 11.0.0.0, home2's stays in 100.64.0.0/10, as every link of the control does
    assert_eq!(mapped.links[0].net.octets()[0], 11);
    assert_eq!(mapped.links[1].net, none.links[1].net);
    assert!(none.links.iter().all(|l| l.net.octets()[..2] == [100, 64]));
    let n1 = mapped.node("n1").unwrap();
    assert_eq!(
        mapped.public_ip(n1).octets()[0],
        11,
        "the node is seen at its router's unreserved address"
    );
    let nft = |p: &Plan, s: usize| {
        p.setup
            .iter()
            .find(|(ns, _)| *ns == Ns::Router(s))
            .unwrap()
            .1
            .iter()
            .filter(|c| c.tool == Tool::Nft)
            .count()
    };
    assert_eq!(nft(&mapped, h1), 1);
    assert_eq!(nft(&mapped, h2), 0);
    assert_eq!(nft(&none, h1), 0);
    // every router routes the link /30 it is not on, by the link's own numbering
    let public = mapped.site("public").unwrap();
    let cmds = &mapped.setup.iter().find(|(ns, _)| *ns == Ns::Router(h2)).unwrap().1;
    let net0 = format!("{}/30", mapped.links[0].net);
    assert!(cmds.iter().any(|c| c.args.contains(&net0)));
    assert!(mapped.sites[public].portmap.is_none());
}

#[test]
fn a_port_mapping_needs_a_translating_router() {
    let mut sc = scenario("port-mapping");
    let public = sc.sites.iter().position(|s| s.name == "public").unwrap();
    sc.sites[public].portmap = sc.sites[0].portmap;
    let problems = sc.validate();
    assert!(
        problems.iter().any(|p| p.path == format!("sites[{public}].portmap")),
        "{problems:?}"
    );
}

#[test]
fn the_helper_writes_a_gateway_config_only_from_valid_fields() {
    let conf = gateway_conf(42, "w0", "lan", "10.1.0.0", "pcp").unwrap();
    for line in [
        "ext_ifname=w0",
        "listening_ip=lan",
        "enable_pcp_pmp=yes",
        "enable_upnp=no",
        "allow 1024-65535 10.1.0.0/24 1024-65535",
    ] {
        assert!(conf.lines().any(|l| l == line), "{line} missing from\n{conf}");
    }
    assert!(
        gateway_conf(42, "w0", "lan", "10.1.0.0", "upnp")
            .unwrap()
            .contains("enable_upnp=yes")
    );
    for (ext, lan, prefix, proto) in [
        ("w0;rm", "lan", "10.1.0.0", "pcp"),
        ("w0", "lan\nallow 0-65535 0.0.0.0/0 0-65535", "10.1.0.0", "pcp"),
        ("w0", "lan", "10.1.0.7", "pcp"),
        ("w0", "lan", "not an address", "pcp"),
        ("w0", "lan", "10.1.0.0", "natpmp"),
        ("a-name-longer-than-fifteen", "lan", "10.1.0.0", "pcp"),
    ] {
        assert_eq!(
            gateway_conf(1, ext, lan, prefix, proto),
            None,
            "{ext} {lan} {prefix} {proto}"
        );
    }
}

#[test]
fn translated_sites_masquerade_and_are_not_routed() {
    let sc = scenario("home-routers");
    let p = Plan::new(&sc, "r", 16);
    let (h1, h2, public) = (
        p.site("home1").unwrap(),
        p.site("home2").unwrap(),
        p.site("public").unwrap(),
    );
    assert_eq!(p.sites[h1].nat, Nat::PortRestricted);
    let rules = |s: usize| -> Vec<Vec<String>> {
        p.setup
            .iter()
            .find(|(ns, _)| *ns == Ns::Router(s))
            .unwrap()
            .1
            .iter()
            .filter(|c| c.tool == Tool::Iptables)
            .map(|c| c.args.clone())
            .collect()
    };
    assert_eq!(rules(h1).len(), 2);
    assert!(!rules(h1)[0].contains(&"--random-fully".to_owned()));
    for s in [h1, h2] {
        let drop = [
            "-A",
            "INPUT",
            "-i",
            "w",
            "-m",
            "conntrack",
            "--ctstate",
            "NEW,INVALID",
            "-j",
            "DROP",
        ];
        assert!(
            rules(s).iter().any(|r| r.len() == drop.len()
                && r.iter()
                    .zip(drop)
                    .all(|(a, b)| if b == "w" { a.starts_with(b) } else { a == b })),
            "a home router drops unsolicited packets before conntrack keeps them, or a peer's punch remaps the port"
        );
    }
    assert!(
        rules(h2)[0].contains(&"--random-fully".to_owned()),
        "the symmetric translation picks a random port per destination"
    );
    assert_eq!(rules(public), Vec::<Vec<String>>::new());
    let public_cmds = &p.setup.iter().find(|(ns, _)| *ns == Ns::Router(public)).unwrap().1;
    let lan1 = format!("{}/24", p.sites[h1].lan);
    assert!(
        !public_cmds.iter().any(|c| c.args.contains(&lan1)),
        "a translated LAN must not be routed"
    );
}

#[test]
fn both_directions_of_every_link_are_shaped_in_a_router() {
    let sc = scenario("wan");
    let p = Plan::new(&sc, "r", 16);
    let [(fwd, fs), (rev, rs)] = p.link_points("east", "west").unwrap();
    assert_eq!((fwd.ns, rev.ns), (Ns::Router(0), Ns::Router(1)));
    assert!((fs.delay_ms - 25.0).abs() < 1e-9 && (rs.loss_pct - 1.0).abs() < 1e-9);
    let [(down, _), (up, _)] = p.link_points("n1", "east").unwrap();
    assert_eq!((down.dev.as_str(), up.dev.as_str()), ("p0", "u0"));
    assert!(
        p.link_points("n1", "west").is_none(),
        "n1 has no link to the other site's router"
    );
}

#[test]
fn netem_arguments_are_exact_integers() {
    let s = Shape {
        delay_ms: 25.0,
        jitter_ms: 0.0,
        loss_pct: 1.0,
        rate_mbit: Some(100.0),
        queue_ms: None,
    };
    let a = netem_args(&s, 1500);
    assert_eq!(a[..3], ["netem", "delay", "25000us"]);
    assert!(a.windows(2).any(|w| w == ["loss", "1%"]));
    assert!(a.windows(2).any(|w| w == ["rate", "100000kbit"]));
    let j = netem_args(
        &Shape {
            delay_ms: 100.0,
            jitter_ms: 30.0,
            loss_pct: 5.0,
            rate_mbit: Some(10.0),
            queue_ms: None,
        },
        1500,
    );
    assert_eq!(
        j[..6],
        ["netem", "delay", "100000us", "30000us", "distribution", "normal"]
    );
    let lan = netem_args(&Shape::lan(), 1500);
    assert_eq!(lan[2], "50us");
    assert!(!lan.contains(&"loss".to_owned()));
}

#[test]
fn queue_limit_holds_the_path_and_the_buffer() {
    // 100 Mbit/s over 25 ms plus 50 ms of buffer: 625 kB, about 417 packets of 1500 bytes, plus the margin.
    let s = Shape {
        delay_ms: 25.0,
        rate_mbit: Some(100.0),
        ..Shape::default()
    };
    assert_eq!(queue_limit(&s, 1500), 625 + 16);
    let tiny = Shape {
        delay_ms: 0.05,
        rate_mbit: Some(1.0),
        ..Shape::default()
    };
    assert_eq!(queue_limit(&tiny, 1500), 64 + 16);
}

#[test]
fn the_queue_counts_packets_of_the_interface_size() {
    // 100 Mbit/s over 25 ms plus 50 ms of buffer is 937500 bytes: 733 packets of 1280 bytes, plus the margin.
    let s = Shape {
        delay_ms: 25.0,
        rate_mbit: Some(100.0),
        ..Shape::default()
    };
    assert_eq!(queue_limit(&s, 1280), 733 + 16);
}

#[test]
fn a_scenario_without_mtu_gives_every_interface_1500() {
    let sc = scenario("wan");
    assert_eq!(sc.mtu, 1500);
    assert!(!sc.to_toml().unwrap().contains("mtu"), "the default is not written");
    let p = Plan::new(&sc, "r", 16);
    assert_eq!(p.mtu, 1500);
    let sizes = mtu_args(&p);
    assert_eq!(sizes.len(), 10, "{sizes:?}");
    assert!(sizes.iter().all(|m| m == "1500"), "{sizes:?}");
}

fn mtu_args(p: &Plan) -> Vec<String> {
    p.setup
        .iter()
        .flat_map(|(_, cmds)| cmds)
        .filter_map(|c| {
            let i = c.args.iter().position(|a| a == "mtu")?;
            c.args.get(i + 1).cloned()
        })
        .collect()
}

#[test]
fn a_scenario_with_mtu_gives_every_interface_and_the_nodes_that_size() {
    let mut sc = scenario("wan");
    sc.mtu = 1280;
    assert_eq!(sc.validate(), vec![]);
    let again = Scenario::parse(&sc.to_toml().unwrap()).unwrap();
    assert_eq!(again.mtu, 1280, "the value survives a save and a load");
    let p = Plan::new(&sc, "r", 16);
    let sizes = mtu_args(&p);
    // two nodes (eth0), two bridges, two ports and two ifb devices, and both ends of the link
    assert_eq!(sizes.len(), 2 + 2 + 2 + 2 + 2, "{sizes:?}");
    assert!(sizes.iter().all(|m| m == "1280"), "{sizes:?}");
}

#[test]
fn an_mtu_outside_1280_to_1500_is_refused_with_the_range() {
    for bad in [1200, 9000] {
        let mut sc = scenario("wan");
        sc.mtu = bad;
        let p = sc.validate();
        assert!(
            p.iter().any(|p| p.path == "mtu" && p.message.contains("1280 to 1500")),
            "{bad}: {p:?}"
        );
    }
}

#[test]
fn cpu_sets_are_disjoint_when_the_host_has_room_and_shared_when_not() {
    let (sets, shared) = cpu_sets(2, 2, 16);
    assert_eq!(sets, ["1,2", "3,4"]);
    assert!(!shared);
    let (sets, shared) = cpu_sets(33, 1, 16);
    assert!(shared);
    assert_eq!(sets[0], "1");
    assert_eq!(sets[15], "1", "the sixteenth node wraps to the first CPU");
    assert!(sets.iter().all(|s| s != "0"), "CPU 0 is left to the routers");
}

#[test]
fn the_helper_runs_nothing_else_in_the_host_namespace() {
    let s = |v: &[&str]| v.iter().map(|x| (*x).to_owned()).collect::<Vec<_>>();
    assert!(host_ns_allowed(
        "ip",
        &s(&[
            "link", "add", "eth0", "netns", "12", "type", "veth", "peer", "name", "p0", "netns", "34"
        ])
    ));
    assert!(!host_ns_allowed(
        "ip",
        &s(&["link", "add", "eth0", "type", "veth", "peer", "name", "p0"])
    ));
    assert!(!host_ns_allowed(
        "tc",
        &s(&["qdisc", "add", "dev", "lo", "root", "netem", "delay", "1ms"])
    ));
    assert!(!host_ns_allowed("iptables", &s(&["-F"])));
    assert!(readable("/proc/123/net/dev"));
    assert!(!readable("/proc/self/net/dev"));
    assert!(!readable("/etc/shadow"));
    assert!(!readable("/sys/fs/cgroup/../../etc/shadow"));
}

#[test]
fn kernel_counters_parse() {
    let dev = "Inter-|   Receive\n face |bytes packets errs drop fifo frame compressed multicast|bytes packets errs drop fifo colls carrier compressed\n    lo: 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0\n  eth0: 1000 10 0 2 0 0 0 0 5000 20 0 1 0 0 0 0\n";
    let m = parse_net_dev(dev);
    assert_eq!(
        m["eth0"],
        Iface {
            rx_bytes: 1000,
            rx_packets: 10,
            rx_drops: 2,
            tx_bytes: 5000,
            tx_packets: 20,
            tx_drops: 1
        }
    );
    assert_eq!(parse_cpu_usec("usage_usec 123456\nuser_usec 1\n"), Some(123_456));
    assert_eq!(parse_cpu_usec("nothing"), None);
    let tc = r#"[{"kind":"netem","handle":"8001:","dev":"w0","root":true,"bytes":10,"packets":2,"drops":3,"overlimits":0,"requeues":0,"backlog":0,"qlen":0}]"#;
    let q = parse_tc(tc);
    assert_eq!((q[0].dev.as_str(), q[0].drops), ("w0", 3));
    let u = NodeUse::between(
        &Reading {
            cpu_usec: Some(1_000_000),
            eth0: Some(Iface {
                tx_bytes: 100,
                ..Iface::default()
            }),
        },
        &Reading {
            cpu_usec: Some(3_500_000),
            eth0: Some(Iface {
                tx_bytes: 600,
                ..Iface::default()
            }),
        },
        Some(2 * 1_048_576),
    );
    assert_eq!(u.cpu_s, Some(2.5));
    assert_eq!(u.peak_mib, Some(2.0));
    assert_eq!(u.eth0.unwrap().tx_bytes, 500);
    assert_eq!(
        NodeUse::between(&Reading::default(), &Reading::default(), None).cpu_s,
        None,
        "unmeasured is absent, not zero"
    );
}

fn row(stack: &str, rep: u32, p50: f64) -> Row {
    let mut node = serde_json::Map::new();
    node.insert("p50_us".into(), p50.into());
    Row {
        run: "r".into(),
        stack: stack.into(),
        test: "setup".into(),
        pair: "a>b".into(),
        rep,
        status: "ok".into(),
        node,
        kernel: std::collections::BTreeMap::default(),
        shaper_drops: Some(0),
        host: None,
    }
}

#[test]
fn spread_is_median_min_max() {
    let s = spread(vec![3.0, 1.0, 2.0]).unwrap();
    assert_eq!((s.median, s.min, s.max, s.n), (2.0, 1.0, 3.0, 3));
    assert_eq!(spread(vec![4.0, 1.0, 2.0, 3.0]).unwrap().median, 2.5);
    assert!(spread(vec![]).is_none());
    assert!(spread(vec![f64::NAN]).is_none());
}

#[test]
fn summary_marks_the_best_and_keeps_what_was_not_measured() {
    let mut rows = vec![
        row("pinc", 0, 900.0),
        row("pinc", 1, 1100.0),
        row("pinc", 2, 1000.0),
        row("iroh", 0, 1200.0),
    ];
    let mut missing = row("libp2p", 0, 0.0);
    missing.status = "not measured: the library has no resumption with early data".into();
    missing.node.clear();
    rows.push(missing);
    let stacks: Vec<String> = ["pinc", "iroh", "libp2p"].iter().map(|s| (*s).to_owned()).collect();
    let t = summarize(&rows, &stacks);
    assert_eq!(t.len(), 1);
    let p50 = &t[0].lines[0];
    assert_eq!(p50.best, Some(0));
    assert_eq!(fmt_cell(&p50.cells[0]), "1,000 [900..1,100]");
    assert!(matches!(&p50.cells[2], Cell::Missing(m) if m.contains("no resumption")));
}

#[test]
fn discarded_measurements_count_for_nothing_and_are_noted() {
    let mut busy = row("pinc", 0, 5.0);
    busy.status =
        "discarded: the host was busy (other processes 40.0% of a core, steal 0.00%, most: rsync 40.0%)".into();
    let rows = vec![busy, row("pinc", 0, 900.0), row("iroh", 0, 1000.0)];
    let stacks = vec!["pinc".to_owned(), "iroh".to_owned()];
    let t = &summarize(&rows, &stacks)[0];
    assert_eq!(
        fmt_cell(&t.lines[0].cells[0]),
        "900",
        "the discarded value must not count"
    );
    assert!(
        t.notes.iter().any(|n| n.contains("1 measurement(s) discarded")),
        "{:?}",
        t.notes
    );
    let mut gone = row("libp2p", 0, 1.0);
    gone.status =
        "not measured: the host was busy (other processes 9.0% of a core, steal 0.00%, most: cc1 9.0%)".into();
    let t = &summarize(&[gone], &["libp2p".to_owned()])[0];
    assert!(matches!(&t.lines[0].cells[0], Cell::Missing(m) if m.contains("host was busy")));
}

#[test]
fn the_quiet_check_counts_only_what_is_not_the_run() {
    let me = std::process::id();
    let t0 = std::time::Instant::now();
    let t1 = t0 + std::time::Duration::from_secs(1);
    let a = Snapshot::from_parts(
        t0,
        &[
            (9001, 1, "rsync", 0),
            (9002, 2, "kworker/3:1", 0),
            (9003, me, "docker", 0),
            (me, 1, "pinc-distributed", 0),
        ],
        0,
        0,
    );
    let b = Snapshot::from_parts(
        t1,
        &[
            (9001, 1, "rsync", 50),
            (9002, 2, "kworker/3:1", 80),
            (9003, me, "docker", 70),
            (me, 1, "pinc-distributed", 90),
        ],
        1600,
        8,
    );
    let m = Monitor {
        containers: Vec::new(),
        limits: Thresholds::default(),
    };
    let u = m.usage(&a, &b);
    assert!((u.other_pct - 50.0).abs() < 1e-6, "only rsync counts: {u:?}");
    assert!((u.steal_pct - 0.5).abs() < 1e-6);
    assert!(u.top.starts_with("rsync"));
    assert!(!u.clean);
    let quiet = Snapshot::from_parts(t1, &[(9001, 1, "rsync", 2), (me, 1, "pinc-distributed", 500)], 1600, 0);
    assert!(m.usage(&a, &quiet).clean, "2% of a core is under the 3% threshold");
}

#[test]
fn proc_stat_lines_parse_with_odd_names() {
    assert_eq!(
        parse_stat_line("42 (tokio (rt) w) S 7 1 1 0 -1 4194560 100 0 0 0 250 50 0 0 20 0 1 0 1 1 1"),
        Some(("tokio (rt) w".to_owned(), 7, 300))
    );
    assert_eq!(parse_stat_line("garbage"), None);
}

#[test]
fn a_tie_is_not_a_win() {
    let rows = vec![row("pinc", 0, 5.0), row("iroh", 0, 5.0)];
    let stacks = vec!["pinc".to_owned(), "iroh".to_owned()];
    assert_eq!(summarize(&rows, &stacks)[0].lines[0].best, None);
}

const MARK_NOTE: &str = "† did not complete the test (see the delivery row above): its cost is not compared.";

/// A table of `test` with one row per stack: `(stack, node fields, cost)`, the cost being its CPU seconds and bytes sent.
type Fields<'a> = &'a [(&'a str, f64)];

fn table_of(test: &str, stacks: &[(&str, Fields, u32)]) -> Table {
    let rows: Vec<Row> = stacks
        .iter()
        .map(|(s, fields, cost)| {
            let mut r = row(s, 0, 0.0);
            r.test = test.into();
            r.node = fields
                .iter()
                .map(|(k, v)| ((*k).to_owned(), serde_json::json!(v)))
                .collect();
            r.kernel.insert(
                "client".into(),
                NodeUse {
                    cpu_s: Some(f64::from(*cost)),
                    eth0: Some(Iface {
                        tx_bytes: u64::from(*cost),
                        ..Iface::default()
                    }),
                    ..NodeUse::default()
                },
            );
            r
        })
        .collect();
    let names: Vec<String> = stacks.iter().map(|(s, ..)| (*s).to_owned()).collect();
    summarize(&rows, &names).remove(0)
}

fn line<'a>(t: &'a Table, label: &str) -> &'a pinc_distributed::results::Line {
    t.lines.iter().find(|l| l.label == label).unwrap()
}

fn has_mark_note(t: &Table) -> bool {
    t.notes.iter().any(|n| n == MARK_NOTE)
}

#[test]
fn dtn_cost_is_compared_only_among_the_stacks_that_delivered() {
    let t = table_of(
        "dtn_store_forward",
        &[
            ("pinc", &[("delivered", 1.0)], 200),
            ("iroh", &[("delivered", 1.0)], 100),
            ("libp2p", &[("delivered", 0.0)], 10),
        ],
    );
    let wire = line(&t, "bytes on the wire");
    assert_eq!(wire.best, Some(1));
    assert_eq!(wire.out, [false, false, true]);
    assert!(has_mark_note(&t));
    let md = markdown("t", &[], std::slice::from_ref(&t));
    assert!(md.contains("| bytes on the wire (B) | 200 | **100** | 10 † |"), "{md}");
    let delivered = line(&t, "bundles delivered intact");
    assert_eq!((delivered.best, delivered.out.contains(&true)), (None, false));
}

#[test]
fn dtn_without_a_delivery_share_compares_the_stacks_with_checks() {
    let t = table_of(
        "dtn_ledger",
        &[
            ("pinc", &[("checks_passed", 3.0)], 200),
            ("iroh", &[("checks_passed", 3.0)], 100),
            ("libp2p", &[], 10),
        ],
    );
    let wire = line(&t, "bytes on the wire");
    assert_eq!(wire.best, Some(1));
    assert_eq!(wire.out, [false, false, true]);
}

#[test]
fn pubsub_cost_of_a_stack_that_lost_everything_is_not_compared() {
    let t = table_of(
        "pubsub",
        &[("pinc", &[("loss_pct", 0.0)], 5), ("iroh", &[("loss_pct", 100.0)], 1)],
    );
    let cpu = line(&t, "CPU, all nodes (kernel)");
    assert_eq!(cpu.best, None);
    assert_eq!(cpu.out, [false, true]);
    assert!(has_mark_note(&t));
}

#[test]
fn pubsub_latency_of_a_stack_that_lost_messages_is_not_a_win() {
    let t = table_of(
        "pubsub",
        &[
            ("pinc", &[("loss_pct", 0.0), ("p99_us", 13.8e6)], 1),
            ("iroh", &[("loss_pct", 0.0), ("p99_us", 13.8e6)], 1),
            ("libp2p", &[("loss_pct", 12.5), ("p99_us", 1300.0)], 1),
        ],
    );
    let p99 = line(&t, "delivery latency p99");
    assert_eq!((p99.best, p99.out.clone()), (None, vec![false, false, true]));
    let loss = line(&t, "messages lost");
    assert_eq!((loss.best, loss.out.contains(&true)), (None, false));
}

#[test]
fn pubsub_loss_within_a_point_of_the_least_completes() {
    let t = table_of(
        "pubsub",
        &[
            ("pinc", &[("loss_pct", 12.0), ("p99_us", 900.0)], 1),
            ("iroh", &[("loss_pct", 12.2), ("p99_us", 800.0)], 1),
            ("libp2p", &[("loss_pct", 23.9), ("p99_us", 10.0)], 1),
        ],
    );
    let p99 = line(&t, "delivery latency p99");
    assert_eq!((p99.best, p99.out.clone()), (Some(1), vec![false, false, true]));
}

#[test]
fn sync_and_latency_tables_compare_every_stack() {
    for test in ["sync_1mib", "latency_64b"] {
        let t = table_of(
            test,
            &[
                ("pinc", &[("p50_us", 9.0), ("fetch_ms", 9.0)], 3),
                ("iroh", &[("p50_us", 5.0), ("fetch_ms", 5.0)], 2),
            ],
        );
        assert!(t.lines.iter().all(|l| !l.out.contains(&true)), "{test}");
        assert!(!has_mark_note(&t));
        assert_eq!(t.lines[0].best, Some(1));
    }
}

#[test]
fn numbers_and_dates_print_plainly() {
    assert_eq!(fmt_num(1_234_567.0), "1,234,567");
    assert_eq!(fmt_num(12.345), "12.3");
    assert_eq!(fmt_num(0.5), "0.50");
    assert_eq!(civil_date(0), "1970-01-01");
    assert_eq!(civil_date(20_403), "2025-11-11");
    assert_eq!(civil_date(11_016), "2000-02-29");
}
