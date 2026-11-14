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

use vinc_distributed::helper::{host_ns_allowed, readable};
use vinc_distributed::metrics::{Iface, NodeUse, Reading, parse_cpu_usec, parse_net_dev, parse_tc};
use vinc_distributed::plan::{Ns, Plan, Tool, cpu_sets, netem_args, queue_limit};
use vinc_distributed::quiet::{Monitor, Snapshot, Thresholds, parse_stat_line};
use vinc_distributed::results::{Cell, Row, civil_date, fmt_cell, fmt_num, spread, summarize};
use vinc_distributed::scenario::{Nat, Scenario, Shape, Stack, Workload};

fn scenario(name: &str) -> Scenario {
    let path = format!("{}/scenarios/{name}.toml", env!("CARGO_MANIFEST_DIR"));
    Scenario::parse(&std::fs::read_to_string(path).unwrap()).unwrap()
}

const EXAMPLES: [&str; 26] = [
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
    "wan",
    "lossy",
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
    sc.stacks.push(Stack::Vinc);
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
    let a = netem_args(&s);
    assert_eq!(a[..3], ["netem", "delay", "25000us"]);
    assert!(a.windows(2).any(|w| w == ["loss", "1%"]));
    assert!(a.windows(2).any(|w| w == ["rate", "100000kbit"]));
    let j = netem_args(&Shape {
        delay_ms: 100.0,
        jitter_ms: 30.0,
        loss_pct: 5.0,
        rate_mbit: Some(10.0),
        queue_ms: None,
    });
    assert_eq!(
        j[..6],
        ["netem", "delay", "100000us", "30000us", "distribution", "normal"]
    );
    let lan = netem_args(&Shape::lan());
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
    assert_eq!(queue_limit(&s), 625 + 16);
    let tiny = Shape {
        delay_ms: 0.05,
        rate_mbit: Some(1.0),
        ..Shape::default()
    };
    assert_eq!(queue_limit(&tiny), 64 + 16);
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
        row("vinc", 0, 900.0),
        row("vinc", 1, 1100.0),
        row("vinc", 2, 1000.0),
        row("iroh", 0, 1200.0),
    ];
    let mut missing = row("libp2p", 0, 0.0);
    missing.status = "not measured: the library has no resumption with early data".into();
    missing.node.clear();
    rows.push(missing);
    let stacks: Vec<String> = ["vinc", "iroh", "libp2p"].iter().map(|s| (*s).to_owned()).collect();
    let t = summarize(&rows, &stacks);
    assert_eq!(t.len(), 1);
    let p50 = &t[0].lines[0];
    assert_eq!(p50.best, Some(0));
    assert_eq!(fmt_cell(&p50.cells[0]), "1,000 [900..1,100]");
    assert!(matches!(&p50.cells[2], Cell::Missing(m) if m.contains("no resumption")));
}

#[test]
fn discarded_measurements_count_for_nothing_and_are_noted() {
    let mut busy = row("vinc", 0, 5.0);
    busy.status =
        "discarded: the host was busy (other processes 40.0% of a core, steal 0.00%, most: rsync 40.0%)".into();
    let rows = vec![busy, row("vinc", 0, 900.0), row("iroh", 0, 1000.0)];
    let stacks = vec!["vinc".to_owned(), "iroh".to_owned()];
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
            (me, 1, "vinc-distributed", 0),
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
            (me, 1, "vinc-distributed", 90),
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
    let quiet = Snapshot::from_parts(t1, &[(9001, 1, "rsync", 2), (me, 1, "vinc-distributed", 500)], 1600, 0);
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
    let rows = vec![row("vinc", 0, 5.0), row("iroh", 0, 5.0)];
    let stacks = vec!["vinc".to_owned(), "iroh".to_owned()];
    assert_eq!(summarize(&rows, &stacks)[0].lines[0].best, None);
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
