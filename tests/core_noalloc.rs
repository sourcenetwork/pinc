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

use vinc_core::{Command, Role, Value};
use vinc_tests::*;

vinc_tests::install_counting_allocator!();

fn transfer(net: &mut CoreNet, a: usize, sa: vinc_core::SessionId, size: usize, seed: u64) {
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
