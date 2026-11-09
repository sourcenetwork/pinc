//! Stream carriers in `vinc-sim`: the TCP and WebSocket model between a node and a relay. Setup round trips, bulk
//! transfer over a lossy link, retransmission timeouts and failure, middleboxes (UDP block, stream policy, captive
//! portal), NAT mappings for streams, partitions, FIN notification, lifecycle faults and determinism.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::assert_is_empty
)]

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use vinc_sim::toy_stream::{StreamCmd, StreamProbe, StreamProbeEvent};
use vinc_sim::{
    DropReason, LanConfig, LanId, LinkChange, LinkConfig, MS, NatConfig, NatKind, NodeId, PortPolicy, SEC, Sim,
    SimConfig, StreamEvent, StreamId, StreamKind, StreamPolicy, Time,
};

const fn ip(a: u8, b: u8) -> IpAddr {
    IpAddr::V4(Ipv4Addr::new(10, 0, a, b))
}

const fn sa(a: u8, b: u8, port: u16) -> SocketAddr {
    SocketAddr::new(ip(a, b), port)
}

const CLIENT: SocketAddr = sa(1, 1, 50_000);
const SERVER: SocketAddr = sa(2, 1, 443);
const SERVER_WS: SocketAddr = sa(2, 1, 8443);
/// One-way time between the two LANs with the default delays: 5 ms up plus 5 ms down.
const OWD: Time = 10 * MS;

fn lan_cfg(delay: Time) -> LanConfig {
    LanConfig {
        up: LinkConfig {
            delay: delay / 2,
            ..LinkConfig::default()
        },
        down: LinkConfig {
            delay: delay / 2,
            ..LinkConfig::default()
        },
        ..LanConfig::default()
    }
}

struct World {
    sim: Sim<StreamProbe>,
    client: NodeId,
    server: NodeId,
    client_lan: LanId,
    server_lan: LanId,
}

fn world_with(seed: u64, client_lan: LanConfig, server_lan: LanConfig) -> World {
    let mut sim = Sim::with_config(
        seed,
        SimConfig {
            trace: true,
            trace_packets: true,
            ..SimConfig::default()
        },
    );
    let (cl, sl) = (sim.add_lan(client_lan), sim.add_lan(server_lan));
    let client = sim.add_node(StreamProbe::new());
    sim.add_iface_in(client, CLIENT.ip(), cl);
    let server = sim.add_node(StreamProbe::new());
    sim.add_iface_in(server, SERVER.ip(), sl);
    sim.listen(server, SERVER, StreamKind::Tcp);
    sim.listen(server, SERVER_WS, StreamKind::Ws);
    World {
        sim,
        client,
        server,
        client_lan: cl,
        server_lan: sl,
    }
}

fn world(seed: u64) -> World {
    world_with(seed, lan_cfg(OWD), lan_cfg(OWD))
}

impl World {
    fn connect(&mut self, at: Time, to: SocketAddr, kind: StreamKind) {
        self.sim.command(
            at,
            self.client,
            StreamCmd::Connect {
                local: CLIENT,
                remote: to,
                kind,
                simultaneous: false,
            },
        );
    }

    fn client_when(&self, f: impl Fn(&StreamEvent) -> bool) -> Option<Time> {
        self.sim.node(self.client).when(f)
    }

    fn server_when(&self, f: impl Fn(&StreamEvent) -> bool) -> Option<Time> {
        self.sim.node(self.server).when(f)
    }
}

fn opened(e: &StreamEvent) -> bool {
    matches!(e, StreamEvent::Opened { .. })
}
fn failed(e: &StreamEvent) -> bool {
    matches!(e, StreamEvent::Failed { .. })
}
fn closed(e: &StreamEvent) -> bool {
    matches!(e, StreamEvent::Closed { .. })
}

const H1: StreamId = StreamId(1);

#[test]
fn a_tcp_connect_opens_after_one_round_trip_and_the_server_after_one_and_a_half() {
    let mut w = world(1);
    w.connect(0, SERVER, StreamKind::Tcp);
    w.sim.run_until(SEC);
    assert_eq!(w.client_when(opened), Some(2 * OWD));
    assert_eq!(w.server_when(opened), Some(3 * OWD));
    let ev = &w.sim.node(w.client).stream_events;
    assert_eq!(
        ev[0],
        (
            0,
            StreamEvent::Pending {
                stream: H1,
                remote: SERVER
            }
        )
    );
    assert_eq!(w.sim.node(w.client).handles(), vec![H1]);
    assert_eq!(w.sim.node(w.server).handles(), vec![H1]);
    assert_eq!(w.sim.metrics().carriers_opened, 2);
    assert_eq!(w.sim.stream_count(w.client), 1);
}

#[test]
fn a_websocket_connect_takes_three_round_trips_and_the_server_opens_after_two_and_a_half() {
    let mut w = world(1);
    w.connect(0, SERVER_WS, StreamKind::Ws);
    w.sim.run_until(SEC);
    assert_eq!(w.client_when(opened), Some(6 * OWD));
    assert_eq!(w.server_when(opened), Some(5 * OWD));
    // The client sent a SYN (60 bytes), the third ACK (52) and the TLS and upgrade requests (520 and 260 bytes of
    // payload, one segment each); the server a SYN-ACK (60) and its two responses (2900 over three segments, 160).
    let c = &w.sim.metrics().nodes[w.client.index()];
    let s = &w.sim.metrics().nodes[w.server.index()];
    assert!(
        c.stream_wire_bytes >= 60 + 52 + (52 + 520) + (52 + 260),
        "{}",
        c.stream_wire_bytes
    );
    assert!(
        s.stream_wire_bytes >= 60 + (3 * 52 + 2900) + (52 + 160),
        "{}",
        s.stream_wire_bytes
    );
}

#[test]
fn records_arrive_whole_in_order_and_ws_framing_is_counted() {
    let mut w = world(1);
    w.connect(0, SERVER, StreamKind::Tcp);
    w.connect(0, SERVER_WS, StreamKind::Ws);
    w.sim.run_until(SEC);
    let (tcp, ws) = (StreamId(1), StreamId(2));
    for (i, len) in [1usize, 100, 1448, 1449, 5000].into_iter().enumerate() {
        let data: Vec<u8> = (0..len).map(|j| (i * 7 + j) as u8).collect();
        w.sim.command(
            SEC,
            w.client,
            StreamCmd::Send {
                stream: tcp,
                data: data.clone(),
            },
        );
        w.sim.command(SEC, w.client, StreamCmd::Send { stream: ws, data });
    }
    w.sim.run_until(2 * SEC);
    let got = &w.sim.node(w.server).records;
    assert_eq!(got.len(), 10);
    for stream in [tcp, ws] {
        let lens: Vec<usize> = got.iter().filter(|r| r.1 == stream).map(|r| r.2.len()).collect();
        assert_eq!(lens, vec![1, 100, 1448, 1449, 5000]);
    }
    // The server's stream numbering follows its accept order: handle 1 is the tcp end, 2 the ws end.
    let sent_tcp: u64 = [1u64, 100, 1448, 1449, 5000].iter().sum();
    let wire = w.sim.metrics().nodes[w.client.index()].stream_wire_bytes;
    let segs_tcp = [1u64, 100, 1448, 1449, 5000]
        .iter()
        .map(|n| n.div_ceil(1448))
        .sum::<u64>();
    assert!(wire > sent_tcp + 52 * segs_tcp, "{wire}");
}

fn lossy(delay: Time, bps: u64, loss: f64) -> LanConfig {
    LanConfig {
        up: LinkConfig::reference(bps, delay / 2, 64 << 10, loss, 20 * MS),
        down: LinkConfig::reference(bps, delay / 2, 64 << 10, loss, 20 * MS),
        ..LanConfig::default()
    }
}

#[test]
fn bulk_transfer_over_a_lossy_link_delivers_every_byte_in_order() {
    for seed in 1..=4 {
        let mut w = world_with(seed, lossy(40 * MS, 20_000_000, 0.05), lossy(0, 1_000_000_000, 0.0));
        w.connect(0, SERVER, StreamKind::Tcp);
        w.sim.run_until(5 * SEC);
        assert!(w.client_when(opened).is_some(), "seed {seed}");
        let (count, len) = (2000, 1000);
        w.sim
            .command(5 * SEC, w.client, StreamCmd::SendMany { stream: H1, count, len });
        w.sim.run_until(3000 * SEC);
        let node = w.sim.node(w.server);
        assert_eq!(node.records.len(), count, "seed {seed}");
        for (i, (_, _, d)) in node.records.iter().enumerate() {
            let want: Vec<u8> = (0..len).map(|j| (i + j) as u8).collect();
            assert_eq!(d, &want, "seed {seed} record {i}");
        }
        let m = w.sim.metrics();
        assert!(
            m.dropped(DropReason::Loss) > 0,
            "seed {seed}: the link must have lost segments"
        );
        let c = &m.nodes[w.client.index()];
        let ideal = (count * len) as u64 + 52 * (count * len).div_ceil(1448) as u64;
        assert!(
            c.stream_wire_bytes > ideal,
            "seed {seed}: retransmissions are counted on the wire"
        );
        assert!(w.client_when(failed).is_none() && w.server_when(failed).is_none());
    }
}

#[test]
fn a_lost_segment_is_retransmitted_after_the_initial_timeout_of_one_second() {
    let mut w = world(1);
    w.connect(0, SERVER, StreamKind::Tcp);
    w.sim.run_until(25 * MS);
    w.sim
        .lan_link_change(25 * MS, w.client_lan, vinc_sim::LanDir::Up, LinkChange::Blocked(true));
    w.sim
        .lan_link_change(35 * MS, w.client_lan, vinc_sim::LanDir::Up, LinkChange::Blocked(false));
    w.sim.command(
        30 * MS,
        w.client,
        StreamCmd::Send {
            stream: H1,
            data: vec![7; 100],
        },
    );
    w.sim.run_until(5 * SEC);
    let got = &w.sim.node(w.server).records;
    assert_eq!(got.len(), 1);
    // Sent at 30 ms, lost, timer at 1.030 s, the retransmission reaches the server one way later.
    assert_eq!(got[0].0, 30 * MS + SEC + OWD);
    assert!(w.sim.metrics().dropped(DropReason::Blocked) >= 1);
}

#[test]
fn a_dead_path_fails_a_connect_after_five_retries_and_an_open_stream_after_eight_timeouts() {
    let mut w = world(1);
    w.sim.lan_outage(w.server_lan, 0, 10_000 * SEC);
    w.connect(0, SERVER, StreamKind::Tcp);
    w.sim.run_until(1000 * SEC);
    // SYN timeouts at 1, 3, 7, 15, 31 s retry; the sixth at 61 s fails.
    assert_eq!(w.client_when(failed), Some(61 * SEC));
    assert_eq!(w.sim.stream_count(w.client), 0);

    let mut w = world(1);
    w.connect(0, SERVER, StreamKind::Tcp);
    w.sim.run_until(25 * MS);
    w.sim.lan_outage(w.server_lan, 25 * MS, 10_000 * SEC);
    w.sim.command(
        30 * MS,
        w.client,
        StreamCmd::Send {
            stream: H1,
            data: vec![1; 10],
        },
    );
    w.sim.run_until(1000 * SEC);
    // Timeouts at 1, 3, 7, 15, 31, 63, 123, 183 s retry (the delay doubles to a 60 s cap); the ninth fails.
    assert_eq!(w.client_when(failed), Some(30 * MS + 243 * SEC));
}

#[test]
fn a_udp_block_leaves_only_carriers_and_a_stream_policy_filters_them() {
    let hostile = |reject, tls_only| LanConfig {
        udp_block: true,
        stream: Some(StreamPolicy {
            ports: Some(vec![443, 8443]),
            tls_only,
            reject,
        }),
        ..lan_cfg(OWD)
    };
    // UDP never gets out, the carrier on an allowed port does.
    let mut w = world_with(1, hostile(false, false), lan_cfg(OWD));
    w.sim.command(
        0,
        w.client,
        StreamCmd::Datagram {
            local: CLIENT,
            remote: SERVER,
            data: vec![1; 50],
        },
    );
    w.connect(0, SERVER, StreamKind::Tcp);
    w.sim.run_until(SEC);
    assert_eq!(w.sim.metrics().dropped(DropReason::Middlebox), 1);
    assert!(w.sim.node(w.server).records.is_empty());
    assert!(
        !w.sim
            .events(w.server)
            .iter()
            .any(|(_, e)| matches!(e, StreamProbeEvent::Datagram { .. }))
    );
    assert_eq!(w.client_when(opened), Some(2 * OWD));

    // A port outside the list: dropped silently, the connect times out; with a reset it fails at once.
    let mut w = world_with(1, hostile(false, false), lan_cfg(OWD));
    w.connect(0, sa(2, 1, 80), StreamKind::Tcp);
    w.sim.run_until(100 * SEC);
    assert_eq!(w.client_when(failed), Some(61 * SEC));
    let mut w = world_with(1, hostile(true, false), lan_cfg(OWD));
    w.connect(0, sa(2, 1, 80), StreamKind::Tcp);
    w.sim.run_until(100 * SEC);
    assert_eq!(w.client_when(failed), Some(OWD + 1));

    // Only TLS and WebSocket: raw TCP on 443 is refused, the WebSocket carrier is not.
    let mut w = world_with(1, hostile(true, true), lan_cfg(OWD));
    w.connect(0, SERVER, StreamKind::Tcp);
    w.connect(0, SERVER_WS, StreamKind::Ws);
    w.sim.run_until(SEC);
    let failed_streams: Vec<_> = w
        .sim
        .node(w.client)
        .stream_events
        .iter()
        .filter(|(_, e)| failed(e))
        .map(|(_, e)| *e)
        .collect();
    assert_eq!(failed_streams, vec![StreamEvent::Failed { stream: H1 }]);
    assert_eq!(w.client_when(opened), Some(6 * OWD));
}

#[test]
fn a_hostile_lan_refuses_inbound_connections() {
    let mut w = world_with(
        1,
        LanConfig {
            udp_block: true,
            ..lan_cfg(OWD)
        },
        lan_cfg(OWD),
    );
    w.sim.listen(w.client, CLIENT, StreamKind::Tcp);
    w.sim.command(
        0,
        w.server,
        StreamCmd::Connect {
            local: SERVER,
            remote: CLIENT,
            kind: StreamKind::Tcp,
            simultaneous: false,
        },
    );
    w.sim.run_until(100 * SEC);
    assert_eq!(w.server_when(failed), Some(61 * SEC));
    assert!(w.client_when(opened).is_none());
    assert!(w.sim.metrics().dropped(DropReason::Middlebox) >= 6);
}

#[test]
fn a_captive_portal_resets_connections_until_it_opens() {
    let mut w = world(1);
    w.sim.set_portal(w.client, 10 * SEC);
    w.connect(SEC, SERVER, StreamKind::Tcp);
    w.connect(12 * SEC, SERVER, StreamKind::Tcp);
    w.sim.run_until(30 * SEC);
    // The first connect (handle 1) is reset after two up-link delays; the second opens.
    assert_eq!(w.client_when(failed), Some(SEC + OWD + 1));
    let opened_at: Vec<Time> = w
        .sim
        .node(w.client)
        .stream_events
        .iter()
        .filter(|(_, e)| opened(e))
        .map(|(t, _)| *t)
        .collect();
    assert_eq!(opened_at, vec![12 * SEC + 2 * OWD]);
}

#[test]
fn a_nat_forgets_an_idle_stream_and_the_servers_packets_are_black_holed() {
    let mut sim = Sim::<StreamProbe>::with_config(1, SimConfig::default());
    let (cl, sl) = (sim.add_lan(lan_cfg(OWD)), sim.add_lan(lan_cfg(0)));
    let ext = ip(9, 1);
    let nat = sim.add_nat_in(
        NatConfig {
            kind: NatKind::PortRestricted,
            ext_ip: ext,
            mapping_timeout: 30 * SEC,
            tcp_timeout: 30 * SEC,
            refresh_on_inbound: false,
            port_base: 20_000,
            ports: PortPolicy::Sequential,
            no_punch: false,
        },
        cl,
    );
    let client = sim.add_node(StreamProbe::new());
    sim.add_iface_behind(client, CLIENT.ip(), nat);
    let server = sim.add_node(StreamProbe::new());
    sim.add_iface_in(server, SERVER.ip(), sl);
    sim.listen(server, SERVER, StreamKind::Tcp);
    sim.command(
        0,
        client,
        StreamCmd::Connect {
            local: CLIENT,
            remote: SERVER,
            kind: StreamKind::Tcp,
            simultaneous: false,
        },
    );
    sim.command(
        SEC,
        client,
        StreamCmd::Send {
            stream: H1,
            data: vec![1; 10],
        },
    );
    sim.run_until(5 * SEC);
    assert_eq!(
        sim.node(server).records.len(),
        1,
        "a live mapping carries the stream both ways"
    );
    assert_eq!(
        sim.node(server).stream_events[0].1,
        StreamEvent::Opened {
            stream: H1,
            remote: SocketAddr::new(ext, 20_000)
        }
    );
    // Idle past the 30 s timeout, the server writes: the NAT no longer knows the mapping.
    sim.command(
        60 * SEC,
        server,
        StreamCmd::Send {
            stream: H1,
            data: vec![2; 10],
        },
    );
    sim.run_until(1000 * SEC);
    assert!(sim.node(client).records.is_empty());
    assert!(sim.metrics().dropped(DropReason::NatFilter) >= 8);
    let failed_at = sim
        .node(server)
        .when(failed)
        .expect("the server's end fails after its timeouts");
    assert_eq!(failed_at, 60 * SEC + 243 * SEC);
}

#[test]
fn a_partition_stalls_a_carrier_and_a_heal_resumes_it() {
    let mut w = world(1);
    w.connect(0, SERVER, StreamKind::Tcp);
    w.sim.run_until(SEC);
    w.sim
        .partition_lans(2 * SEC, 6 * SEC, &[w.client_lan], &[w.server_lan], true);
    w.sim.command(
        3 * SEC,
        w.client,
        StreamCmd::SendMany {
            stream: H1,
            count: 20,
            len: 1000,
        },
    );
    w.sim.run_until(60 * SEC);
    let node = w.sim.node(w.server);
    assert_eq!(node.records.len(), 20);
    assert!(
        node.records.iter().all(|r| r.0 > 6 * SEC),
        "nothing crossed while partitioned"
    );
    assert!(w.sim.metrics().dropped(DropReason::Partition) > 0);
    assert!(w.client_when(failed).is_none());
}

#[test]
fn a_close_reaches_the_peer_even_through_a_partition() {
    let mut w = world(1);
    w.connect(0, SERVER, StreamKind::Tcp);
    w.sim
        .partition_lans(SEC, 100 * SEC, &[w.client_lan], &[w.server_lan], true);
    w.sim.command(2 * SEC, w.client, StreamCmd::Close(H1));
    w.sim.run_until(10 * SEC);
    assert_eq!(w.server_when(closed), Some(2 * SEC + OWD));
    assert!(
        w.client_when(closed).is_none(),
        "the closing node asked for it and gets no event"
    );
    assert_eq!(w.sim.stream_count(w.client), 0);
    assert_eq!(w.sim.stream_count(w.server), 0);
}

#[test]
fn crash_suspend_and_address_change_end_streams_as_the_reference_does() {
    // A crash closes the node's streams and tells the peer.
    let mut w = world(1);
    w.connect(0, SERVER, StreamKind::Tcp);
    w.sim.crash(SEC, w.client);
    w.sim.run_until(2 * SEC);
    assert_eq!(w.server_when(closed), Some(SEC + OWD));

    // A suspension does too; on resume the node learns its sockets are gone, before anything else.
    let mut w = world(1);
    w.connect(0, SERVER, StreamKind::Tcp);
    w.sim.suspend(SEC, w.client);
    w.sim.resume(5 * SEC, w.client);
    w.sim.run_until(10 * SEC);
    assert_eq!(w.server_when(closed), Some(SEC + OWD));
    assert_eq!(w.client_when(closed), Some(5 * SEC));

    // An address change closes locally and the peer is not told.
    let mut w = world(1);
    w.connect(0, SERVER, StreamKind::Tcp);
    w.sim.set_iface_addr(SEC, w.client, 0, ip(1, 9));
    w.sim.run_until(10 * SEC);
    assert_eq!(w.client_when(closed), Some(SEC));
    assert!(w.server_when(closed).is_none());
    assert_eq!(w.sim.stream_count(w.server), 1);
}

#[test]
fn writes_to_a_stream_that_is_not_open_are_dropped_and_counted() {
    let mut w = world(1);
    w.connect(0, SERVER, StreamKind::Tcp);
    w.sim.command(
        MS,
        w.client,
        StreamCmd::Send {
            stream: H1,
            data: vec![1; 10],
        },
    );
    w.sim.command(
        MS,
        w.client,
        StreamCmd::Send {
            stream: StreamId(99),
            data: vec![1; 10],
        },
    );
    w.sim.run_until(SEC);
    assert_eq!(w.sim.metrics().stream_write_errors, 2);
    assert!(w.sim.node(w.server).records.is_empty());
}

#[test]
fn a_lost_third_ack_leaves_a_raw_tcp_server_unopened_but_a_websocket_server_recovers() {
    for (kind, to) in [(StreamKind::Tcp, SERVER), (StreamKind::Ws, SERVER_WS)] {
        let mut w = world(1);
        // The client's ACK leaves at 2 * OWD; the uplink is down from 1 ms to 2 * OWD + 1 ms, after the SYN.
        w.sim
            .lan_link_change(MS, w.client_lan, vinc_sim::LanDir::Up, LinkChange::Blocked(true));
        w.sim.lan_link_change(
            2 * OWD + MS,
            w.client_lan,
            vinc_sim::LanDir::Up,
            LinkChange::Blocked(false),
        );
        w.connect(0, to, kind);
        w.sim.command(
            SEC,
            w.client,
            StreamCmd::Send {
                stream: H1,
                data: vec![5; 100],
            },
        );
        w.sim.run_until(20 * SEC);
        match kind {
            StreamKind::Tcp => {
                assert!(w.client_when(opened).is_some());
                assert!(w.server_when(opened).is_none(), "the server never saw the third ACK");
                assert!(
                    w.sim.node(w.server).records.is_empty(),
                    "records are discarded at a server that is not open"
                );
                assert!(w.client_when(failed).is_none(), "TCP itself acknowledged the data");
            }
            StreamKind::Ws => {
                // The ACK is lost with the TLS hello behind it, which then times out and is resent; setup completes.
                assert!(w.server_when(opened).is_some());
            }
        }
    }
}

#[test]
fn a_simultaneous_open_between_two_public_hosts_opens_both_ends() {
    let mut w = world(1);
    let arg = |local, remote| StreamCmd::Connect {
        local,
        remote,
        kind: StreamKind::Tcp,
        simultaneous: true,
    };
    let other = sa(2, 1, 50_000);
    w.sim.command(0, w.client, arg(CLIENT, other));
    w.sim.command(0, w.server, arg(other, CLIENT));
    w.sim.run_until(SEC);
    assert!(w.client_when(opened).is_some() && w.server_when(opened).is_some());
}

#[test]
fn the_same_seed_gives_the_same_trace_and_another_seed_a_different_one() {
    let run = |seed| {
        let mut w = world_with(seed, lossy(40 * MS, 20_000_000, 0.05), lossy(0, 1_000_000_000, 0.0));
        w.connect(0, SERVER, StreamKind::Tcp);
        w.connect(0, SERVER_WS, StreamKind::Ws);
        w.sim.command(
            5 * SEC,
            w.client,
            StreamCmd::SendMany {
                stream: H1,
                count: 1000,
                len: 1500,
            },
        );
        w.sim.command(
            5 * SEC,
            w.client,
            StreamCmd::SendMany {
                stream: StreamId(2),
                count: 1000,
                len: 700,
            },
        );
        w.sim.run_until(200 * SEC);
        w.sim.take_trace()
    };
    let a = run(7);
    assert!(a.contains("srec"));
    assert_eq!(a, run(7));
    assert_ne!(a, run(8));
}
