//! Stream carriers against the reference: each scenario in `data/reference_carrier.txt` was run through the
//! reference harness's own link, NAT, middlebox and TCP code (`scripts/gen_reference_carrier.py`), recording what
//! each end saw. The simulator, driven by the reference random source, must reproduce every event time, every
//! record, every wire byte count and the count of opened carriers exactly.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::type_complexity
)]

use std::collections::BTreeMap;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use vinc_sim::reference::RefRng;
use vinc_sim::toy_stream::{StreamCmd, StreamProbe};
use vinc_sim::{
    FlatCost, LanConfig, LinkConfig, NatConfig, NatKind, NodeId, PortPolicy, Sim, SimConfig, StreamEvent, StreamId,
    StreamKind, StreamPolicy, Time,
};

const DATA: &str = include_str!("data/reference_carrier.txt");

type Fields = BTreeMap<String, String>;

fn kv(tokens: &[&str]) -> Fields {
    tokens
        .iter()
        .filter_map(|t| t.split_once('='))
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect()
}

fn num<T: std::str::FromStr>(f: &Fields, k: &str) -> T
where
    T::Err: std::fmt::Debug,
{
    f[k].parse().unwrap()
}

fn host(h: u32) -> IpAddr {
    IpAddr::V4(Ipv4Addr::from(h))
}

#[derive(Default)]
struct Scenario {
    name: String,
    head: Fields,
    sites: Vec<Fields>,
    nats: Vec<Vec<String>>,
    boxes: Vec<Vec<String>>,
    cuts: Vec<Vec<String>>,
    ops: Vec<Vec<String>>,
    /// Expected `ev` lines `(node, time, kind, handle, host, port)`.
    ev: Vec<Vec<String>>,
    rec: Vec<Vec<String>>,
    werr: usize,
    wire: Vec<u64>,
    carriers: u64,
}

fn parse() -> Vec<Scenario> {
    let mut out = Vec::new();
    let mut cur = Scenario::default();
    for line in DATA.lines() {
        let f: Vec<&str> = line.split(' ').collect();
        let rest = || f[1..].iter().map(|s| (*s).to_string()).collect::<Vec<_>>();
        match f[0] {
            "scn" => {
                cur = Scenario {
                    name: f[1].to_string(),
                    head: kv(&f[2..]),
                    ..Scenario::default()
                };
            }
            "site" => cur.sites.push(kv(&f[1..])),
            "nat" => cur.nats.push(rest()),
            "box" => cur.boxes.push(rest()),
            "cut" => cur.cuts.push(rest()),
            "op" => cur.ops.push(rest()),
            "ev" => cur.ev.push(rest()),
            "rec" => cur.rec.push(rest()),
            "werr" => cur.werr += 1,
            "wire" => cur.wire.push(f[2].parse().unwrap()),
            "carriers" => cur.carriers = f[1].parse().unwrap(),
            "end" => out.push(std::mem::take(&mut cur)),
            other => panic!("unknown line {other}"),
        }
    }
    out
}

fn nat_kind(mapping: &str, filtering: &str) -> NatKind {
    match (mapping, filtering) {
        ("eim", "eif") => NatKind::FullCone,
        ("eim", "adf") => NatKind::AddressRestricted,
        ("eim", "apdf") => NatKind::PortRestricted,
        ("edm", "apdf") => NatKind::Symmetric,
        ("edm", "eif") => NatKind::DependentOpen,
        ("edm", "adf") => NatKind::DependentAddress,
        _ => panic!("{mapping}/{filtering}"),
    }
}

fn payload(i: usize, n: usize) -> Vec<u8> {
    (0..n).map(|j| ((i + j) % 256) as u8).collect()
}

struct Run {
    sim: Sim<StreamProbe, RefRng>,
    nodes: Vec<NodeId>,
}

fn build(sc: &Scenario) -> Run {
    let seed: u64 = sc.head["seed"].parse().unwrap();
    let mut sim = Sim::<StreamProbe, RefRng>::with_parts(seed, SimConfig::default(), FlatCost);
    let mut lans = Vec::new();
    for s in &sc.sites {
        let sid: usize = num(s, "sid");
        let (bps, q, burst): (u64, usize, Time) = (num(s, "up_bps"), num(s, "queue"), num(s, "burst"));
        let loss: f64 = num(s, "loss");
        let boxed = sc.boxes.iter().find(|b| b[0] == sid.to_string());
        let lan = sim.add_lan(LanConfig {
            up: LinkConfig::reference(bps, num(s, "up_delay"), q, loss, burst),
            down: LinkConfig::reference(num(s, "down_bps"), num(s, "down_delay"), q, loss, burst),
            region: num(s, "region"),
            udp_block: boxed.is_some_and(|b| b[1] == "1"),
            stream: boxed.map(|b| StreamPolicy {
                ports: (b[2] != "-").then(|| b[2].split(',').map(|p| p.parse().unwrap()).collect()),
                tls_only: b[3] == "1",
                reject: b[4] == "1",
            }),
            ..LanConfig::default()
        });
        lans.push(lan);
    }
    let rd: Time = sc.head["region_delay"].parse().unwrap();
    sim.set_region_delay(0, 1, rd);
    sim.set_region_delay(1, 0, rd);
    let mut nodes = Vec::new();
    for (i, s) in sc.sites.iter().enumerate() {
        let node = sim.add_node(StreamProbe::new());
        let ip = host(num(s, "host"));
        if let Some(n) = sc.nats.iter().find(|n| n[0] == i.to_string()) {
            let nat = sim.add_nat_in(
                NatConfig {
                    kind: nat_kind(&n[2], &n[3]),
                    ext_ip: host(n[1].parse().unwrap()),
                    mapping_timeout: n[4].parse().unwrap(),
                    tcp_timeout: n[5].parse().unwrap(),
                    refresh_on_inbound: false,
                    port_base: 1024,
                    ports: PortPolicy::Randomized,
                    no_punch: false,
                },
                lans[i],
            );
            sim.add_iface_behind(node, ip, nat);
        } else {
            sim.add_iface_in(node, ip, lans[i]);
            sim.listen(node, SocketAddr::new(ip, 443), StreamKind::Tcp);
            sim.listen(node, SocketAddr::new(ip, 8443), StreamKind::Ws);
        }
        if let Some(b) = sc.boxes.iter().find(|b| b[0] == i.to_string()) {
            let portal: Time = b[5].parse().unwrap();
            if portal > 0 {
                sim.set_portal(node, portal);
            }
        }
        nodes.push(node);
    }
    for c in &sc.cuts {
        let ids =
            |s: &str| -> Vec<vinc_sim::LanId> { s.split(',').map(|x| lans[x.parse::<usize>().unwrap()]).collect() };
        sim.partition_lans(
            c[0].parse().unwrap(),
            c[1].parse().unwrap(),
            &ids(&c[2]),
            &ids(&c[3]),
            c[4] == "both",
        );
    }
    for (i, op) in sc.ops.iter().enumerate() {
        let (t, node): (Time, usize) = (op[0].parse().unwrap(), op[1].parse().unwrap());
        let site = &sc.sites[node];
        let nated = sc.nats.iter().any(|n| n[0] == node.to_string());
        let cmd = match op[2].as_str() {
            "connect" => {
                let simul = op[8] == "1";
                let (kind, port) = match (op[3].as_str(), nated) {
                    ("tcp", true) => (StreamKind::Tcp, 50_000),
                    ("ws", true) => (StreamKind::Ws, 50_001),
                    ("tcp", false) => (StreamKind::Tcp, 443),
                    _ => (StreamKind::Ws, 8443),
                };
                let port = if simul { num(site, "client_port") } else { port };
                StreamCmd::Connect {
                    local: SocketAddr::new(host(num(site, "host")), port),
                    remote: SocketAddr::new(host(op[4].parse().unwrap()), op[5].parse().unwrap()),
                    kind,
                    simultaneous: simul,
                }
            }
            "write" => StreamCmd::Send {
                stream: StreamId(op[6].parse().unwrap()),
                data: payload(i, op[7].parse().unwrap()),
            },
            "close" => StreamCmd::Close(StreamId(op[6].parse().unwrap())),
            other => panic!("op {other}"),
        };
        sim.command(t, nodes[node], cmd);
    }
    Run { sim, nodes }
}

fn ev_line(node: usize, t: Time, e: &StreamEvent) -> Vec<String> {
    let s = |x: &dyn ToString| x.to_string();
    let (kind, h, remote) = match e {
        StreamEvent::Pending { stream, remote } => ("pending", stream.0, Some(*remote)),
        StreamEvent::Opened { stream, remote } => ("opened", stream.0, Some(*remote)),
        StreamEvent::Failed { stream } => ("failed", stream.0, None),
        StreamEvent::Closed { stream } => ("closed", stream.0, None),
    };
    let (host, port) = remote.map_or((0, 0), |r| {
        let IpAddr::V4(v4) = r.ip() else { panic!() };
        (u32::from(v4), r.port())
    });
    vec![s(&node), s(&t), s(&kind), s(&h), s(&host), s(&port)]
}

#[test]
fn every_scenario_matches_the_reference_event_for_event() {
    let all = parse();
    assert!(all.len() >= 30, "{} scenarios", all.len());
    for sc in &all {
        let mut run = build(sc);
        let until: Time = sc.head["until"].parse().unwrap();
        run.sim.run_until(until);
        for (i, node) in run.nodes.iter().enumerate() {
            let probe = run.sim.node(*node);
            let got: Vec<Vec<String>> = probe.stream_events.iter().map(|(t, e)| ev_line(i, *t, e)).collect();
            let want: Vec<Vec<String>> = sc
                .ev
                .iter()
                .filter(|e| e[0] == i.to_string())
                .map(|e| e[..6].to_vec())
                .collect();
            assert_eq!(got, want, "{}: stream events of node {i}", sc.name);
            let got: Vec<Vec<String>> = probe
                .records
                .iter()
                .map(|(t, s, d)| {
                    let sum: u64 = d.iter().map(|b| u64::from(*b)).sum();
                    vec![
                        i.to_string(),
                        t.to_string(),
                        s.0.to_string(),
                        d.len().to_string(),
                        (sum % 1_000_003).to_string(),
                    ]
                })
                .collect();
            let want: Vec<Vec<String>> = sc.rec.iter().filter(|r| r[0] == i.to_string()).cloned().collect();
            assert_eq!(got, want, "{}: records of node {i}", sc.name);
        }
        let m = run.sim.metrics();
        for (i, w) in sc.wire.iter().enumerate() {
            assert_eq!(m.nodes[i].wire_bytes, *w, "{}: wire bytes of node {i}", sc.name);
        }
        assert_eq!(m.carriers_opened, sc.carriers, "{}: carriers opened", sc.name);
        assert_eq!(m.stream_write_errors as usize, sc.werr, "{}: writes refused", sc.name);
    }
}
