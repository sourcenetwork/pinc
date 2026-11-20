//! Zero allocation in steady state: once a session carries traffic, no endpoint call (datagram in, datagram out, timer,
//! command, event, query) touches the heap.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation
)]

use pinc_core::{Command, Event, Role, Value};
use pinc_tests::*;

pinc_tests::install_counting_allocator!();

fn transfer(net: &mut CoreNet, a: usize, sa: pinc_core::SessionId, size: usize, seed: u64) {
    let data = pattern(size, seed);
    let t = net.now;
    let Value::Stream(id) = net.nodes[a]
        .cmd(
            t,
            Command::OpenStream {
                session: sa,
                bidi: false,
            },
        )
        .unwrap()
        .value
    else {
        panic!()
    };
    let mut off = 0;
    let want = net.nodes[1].fin.len() + 1;
    assert!(net.run(t + 30 * SEC_NS, |n| {
        let t = n.now;
        while off < data.len() {
            let Ok(rep) = n.nodes[a].cmd(
                t,
                Command::Write {
                    session: sa,
                    stream: id,
                    data: &data[off..],
                },
            ) else {
                break;
            };
            let Value::Written(w) = rep.value else { break };
            if w == 0 {
                break;
            }
            off += w;
        }
        if off == data.len() {
            let _ = n.nodes[a].cmd(
                t,
                Command::Finish {
                    session: sa,
                    stream: id,
                },
            );
        }
        n.nodes[1].fin.len() >= want
    }));
}

#[test]
fn a_session_in_steady_state_never_allocates() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        // Warm up: the first transfers fill the path table and the congestion window.
        transfer(&mut net, a, sa, 300_000, 1);
        transfer(&mut net, a, sa, 300_000, 2);
        net.run_for(2 * SEC_NS);

        // The meter sees an allocation when there is one.
        meter_endpoint_calls(true);
        metered(|| std::hint::black_box(vec![0u8; 64]));
        assert!(take_metered_allocs() >= 1, "the meter is blind");
        transfer(&mut net, a, sa, 400_000, 3);
        net.run_for(30 * SEC_NS); // keepalives and timers too
        meter_endpoint_calls(false);
        let allocs = take_metered_allocs();
        assert_eq!(
            allocs, 0,
            "the endpoint allocated {allocs} times while carrying traffic"
        );
        assert!(net.nodes[b].fin.len() >= 3);
    });
}

#[test]
fn a_sub_session_and_a_dial_after_warm_up_allocate_nothing_either() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        meter_endpoint_calls(true);
        let _ = take_metered_allocs();
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_B, to, Role::Other).unwrap();
        let child = net.nodes[a].session(&rep);
        transfer(&mut net, a, child, 50_000, 9);
        meter_endpoint_calls(false);
        let allocs = take_metered_allocs();
        assert_eq!(allocs, 0, "opening a sub-session allocated {allocs} times");
    });
}

/// A dial to a quiet parent probes it (`QUIET_PROBE`): the probe, its ride, its end by a close and its lapse into a
/// handshake allocate nothing.
#[test]
fn a_quiet_parent_probe_rides_lapses_and_ends_without_allocating() {
    big_stack(|| {
        // A pair whose session has not heard its peer for 21 s, the peer alive.
        let quiet = || {
            let mut net = CoreNet::new(5 * MS_NS);
            let (a, b) = (net.add(1), net.add(2));
            net.connect_pair(a, b, ALPN_A, Role::Other);
            net.run_for(SEC_NS);
            let to = net.nodes[b].addr;
            net.loss = Some(Box::new(move |f, _, _| f == to));
            net.run_for(21 * SEC_NS);
            net.loss = None;
            net
        };
        let connected =
            |net: &CoreNet, s| net.nodes[0].saw(|e| matches!(e, Event::Connected { session, .. } if *session == s));
        // A dial that probes: its own command reports no connection.
        let probe = |net: &mut CoreNet| {
            let (peer, to) = (net.nodes[1].node, net.nodes[1].addr);
            let rep = net.nodes[0].connect(net.now, peer, ALPN_B, to, Role::Other).unwrap();
            assert!(
                !rep.events.any(|e| matches!(e, Event::Connected { .. })),
                "the dial did not probe"
            );
            net.nodes[0].session(&rep)
        };
        let _ = take_metered_allocs();
        // The ride: the peer answers the probe's ping.
        let mut net = quiet();
        meter_endpoint_calls(true);
        let rode = probe(&mut net);
        assert!(net.run(net.now + 2 * SEC_NS, |n| connected(n, rode)));
        meter_endpoint_calls(false);
        // The end: the application closes the dial while it probes.
        let mut net = quiet();
        meter_endpoint_calls(true);
        let closed = probe(&mut net);
        let now = net.now;
        net.nodes[0]
            .cmd(
                now,
                Command::Close {
                    session: closed,
                    error: 0,
                },
            )
            .unwrap();
        net.run_for(SEC_NS);
        meter_endpoint_calls(false);
        assert!(net.nodes[0].saw(|e| matches!(e, Event::ConnectFailed { session: Some(s), .. } if *s == closed)));
        // The lapse: the peer stays silent past the window, and the dial makes its own handshake.
        let mut net = quiet();
        let to = net.nodes[1].addr;
        net.loss = Some(Box::new(move |f, _, _| f == to));
        meter_endpoint_calls(true);
        let lapsed = probe(&mut net);
        // The connectivity client's flight commands on the probing id are kept for the lapse.
        let now = net.now;
        let x: std::net::SocketAddr = ([192, 0, 2, 77], 4433).into();
        net.nodes[0]
            .cmd(
                now,
                Command::FlightPaths {
                    session: lapsed,
                    addrs: &[x],
                    skip_primary: false,
                },
            )
            .unwrap();
        net.nodes[0]
            .cmd(
                now,
                Command::FirstResend {
                    session: lapsed,
                    delay: 0,
                },
            )
            .unwrap();
        net.nodes[0]
            .cmd(
                now,
                Command::HoldFlight {
                    session: lapsed,
                    hold: false,
                },
            )
            .unwrap();
        net.run_for(3 * SEC_NS);
        meter_endpoint_calls(false);
        net.loss = None;
        meter_endpoint_calls(true);
        assert!(net.run(net.now + 5 * SEC_NS, |n| connected(n, lapsed)));
        meter_endpoint_calls(false);
        let allocs = take_metered_allocs();
        assert_eq!(allocs, 0, "the probe allocated {allocs} times");
    });
}

#[test]
fn a_resumption_dial_and_a_forged_hello_allocate_nothing() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        let now = net.now;
        net.nodes[a].cmd(now, Command::Close { session: sa, error: 0 }).unwrap();
        net.run_for(2 * SEC_NS);
        net.capture = true;
        meter_endpoint_calls(true);
        let _ = take_metered_allocs();
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
        net.run_for(SEC_NS);
        // Once the resumed session is gone the Hello's id routes nowhere, so the copies reach admission.
        let session = net.nodes[a].session(&rep);
        let now = net.now;
        net.nodes[a].cmd(now, Command::Close { session, error: 0 }).unwrap();
        net.run_for(2 * SEC_NS);
        let mut hello = net.captured.iter().find(|c| c.1 == to).unwrap().2.clone();
        *hello.last_mut().unwrap() ^= 1;
        for i in 0..20u8 {
            net.inject(([10, 9, 9, i], 1000).into(), to, hello.clone(), 0);
        }
        net.run_for(SEC_NS);
        meter_endpoint_calls(false);
        let allocs = take_metered_allocs();
        assert_eq!(allocs, 0, "a resumption allocated {allocs} times");
        assert!(net.nodes[a].count(|e| matches!(e, pinc_core::Event::Connected { .. })) >= 2);
    });
}
