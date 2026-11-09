//! The NAT of `vinc-sim` against the reference NAT: operation sequences recorded from the reference harness's NAT
//! class (`data/reference_nat.txt`, made by `scripts/gen_reference_nat.py`) are replayed as datagrams, and every
//! translated port, every admitted or refused reply, every rebind and the final mapping count must be the same.
//! Covers port allocation (advance then return, wrap above 65000), expiry, filtering and the rebind order.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use std::fmt::Write;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use vinc_sim::reference::{RefRng, blake2b_128};
use vinc_sim::toy::{Probe, ProbeCmd, ProbeEvent};
use vinc_sim::{FlatCost, LinkConfig, NatConfig, NatKind, PortPolicy, Sim, SimConfig, Time};

const DATA: &str = include_str!("data/reference_nat.txt");
const EXT: u32 = 2_000_000;
const PRIV: u32 = 3_000_001;
const SERVERS: [u32; 3] = [1_000_001, 1_000_002, 1_000_003];

fn addr(h: u32, port: u16) -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::from(h)), port)
}

fn kind(mapping: &str, filtering: &str) -> NatKind {
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

fn world(
    seed: u64,
    kind: NatKind,
    timeout: Time,
) -> (
    Sim<Probe, RefRng>,
    vinc_sim::NatId,
    vinc_sim::NodeId,
    Vec<vinc_sim::NodeId>,
) {
    let cfg = SimConfig {
        default_link: Some(LinkConfig::default()),
        ..SimConfig::default()
    };
    let mut sim = Sim::<Probe, RefRng>::with_parts(seed, cfg, FlatCost);
    let nat = sim.add_nat(NatConfig {
        kind,
        ext_ip: addr(EXT, 0).ip(),
        mapping_timeout: timeout,
        tcp_timeout: 50 * 1_000_000_000,
        refresh_on_inbound: false,
        port_base: 1024,
        ports: PortPolicy::Randomized,
        no_punch: false,
    });
    let client = sim.add_node(Probe::new());
    sim.add_iface_behind(client, addr(PRIV, 0).ip(), nat);
    let servers = SERVERS
        .iter()
        .map(|h| sim.add_node_at(Probe::new(), addr(*h, 0).ip()))
        .collect();
    (sim, nat, client, servers)
}

#[test]
fn operation_sequences_match_the_reference_nat() {
    let mut cases = 0;
    let lines: Vec<Vec<&str>> = DATA.lines().map(|l| l.split(' ').collect()).collect();
    for head in lines.iter().filter(|f| f[0] == "natcase") {
        let name = head[1];
        let (mut sim, nat, client, servers) = world(head[2].parse().unwrap(), kind(head[3], head[4]), 20_000_000_000);
        let ops: Vec<&Vec<&str>> = lines.iter().filter(|f| f[0] == "natop" && f[1] == name).collect();
        for (i, op) in ops.iter().enumerate() {
            let t: Time = op[3].parse().unwrap();
            let id = vec![(i % 256) as u8, (i / 256) as u8];
            match op[2] {
                "out" => {
                    let (sport, srv, dport): (u16, usize, u16) =
                        (op[4].parse().unwrap(), op[5].parse().unwrap(), op[6].parse().unwrap());
                    sim.command(
                        t,
                        client,
                        ProbeCmd::Send {
                            local: addr(PRIV, sport),
                            remote: addr(SERVERS[srv], dport),
                            data: id,
                        },
                    );
                }
                "in" => {
                    let (ext, srv, sport): (u16, usize, u16) =
                        (op[4].parse().unwrap(), op[5].parse().unwrap(), op[6].parse().unwrap());
                    sim.command(
                        t,
                        servers[srv],
                        ProbeCmd::Send {
                            local: addr(SERVERS[srv], sport),
                            remote: addr(EXT, ext),
                            data: id,
                        },
                    );
                }
                _ => sim.nat_rebind(t, nat, None),
            }
        }
        sim.run_until(10_000 * 1_000_000_000);
        let tag = |d: &[u8]| usize::from(d[0]) + 256 * usize::from(d[1]);
        let mut seen_at_server = std::collections::BTreeMap::new();
        for s in &servers {
            for (_, e) in sim.events(*s) {
                if let ProbeEvent::Recv { remote, data, .. } = e {
                    seen_at_server.insert(tag(data), remote.port());
                }
            }
        }
        let mut seen_at_client = std::collections::BTreeMap::new();
        for (_, e) in sim.events(client) {
            if let ProbeEvent::Recv { local, data, .. } = e {
                seen_at_client.insert(tag(data), local.port());
            }
        }
        for (i, op) in ops.iter().enumerate() {
            match op[2] {
                "out" => assert_eq!(
                    seen_at_server.get(&i).copied(),
                    Some(op[7].parse().unwrap()),
                    "{name} op {i} {op:?}"
                ),
                "in" => {
                    let want = (op[7] == "1").then(|| op[8].parse::<u16>().unwrap());
                    assert_eq!(seen_at_client.get(&i).copied(), want, "{name} op {i} {op:?}");
                }
                _ => {}
            }
        }
        let end = lines.iter().find(|f| f[0] == "natend" && f[1] == name).unwrap();
        assert_eq!(
            sim.nat_mappings(nat),
            end[2].parse::<usize>().unwrap(),
            "{name}: mappings"
        );
        assert_eq!(sim.nat_punched(nat), end[3].parse::<u64>().unwrap(), "{name}: punched");
        cases += 1;
    }
    assert_eq!(cases, 18);
}

#[test]
fn the_port_counter_wraps_above_65000_into_the_low_range() {
    for f in DATA
        .lines()
        .map(|l| l.split(' ').collect::<Vec<_>>())
        .filter(|f| f[0] == "natwrap")
    {
        let seed: u64 = f[1].parse().unwrap();
        let count: usize = f[2].parse().unwrap();
        let (mut sim, _nat, client, servers) = world(seed, NatKind::DependentOpen, 1_000_000 * 1_000_000_000);
        for k in 0..count {
            let t = k as u64 * 1_000_000;
            let id = vec![(k % 256) as u8, (k / 256) as u8];
            sim.command(
                t,
                client,
                ProbeCmd::Send {
                    local: addr(PRIV, 4000),
                    remote: addr(SERVERS[0], 1000 + k as u16),
                    data: id,
                },
            );
        }
        sim.run_until(count as u64 * 1_000_000 + 1_000_000);
        let mut ports = vec![0u16; count];
        for (_, e) in sim.events(servers[0]) {
            if let ProbeEvent::Recv { remote, data, .. } = e {
                ports[usize::from(data[0]) + 256 * usize::from(data[1])] = remote.port();
            }
        }
        let wraps = ports.windows(2).filter(|w| w[1] < w[0]).count();
        assert_eq!(wraps.to_string(), f[3], "seed {seed}: the counter wrapped once");
        let bytes: Vec<u8> = ports.iter().flat_map(|p| u32::from(*p).to_le_bytes()).collect();
        let digest = blake2b_128(&bytes).iter().fold(String::new(), |mut s, b| {
            let _ = write!(s, "{b:02x}");
            s
        });
        assert_eq!(digest, f[4], "seed {seed}");
        let first: Vec<String> = ports.iter().take(5).map(ToString::to_string).collect();
        assert_eq!(first.join(","), f[5]);
        assert!(
            ports.iter().skip(1).any(|p| *p < 21_000),
            "seed {seed}: ports restart in 20000..21000"
        );
    }
}
