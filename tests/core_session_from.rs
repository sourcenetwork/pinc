//! The endpoint's table of sessions by address (`Endpoint::session_from`) gives, after every step of a hub's life,
//! exactly what a walk of every live session gives: the lowest session whose active path is validated, direct and
//! from the address. The hub is dialed, a member dials it twice from one address, a member changes its address, a NAT
//! in front of a member rebinds to a new outside port, and a session closes and its slot is taken again; the check
//! runs after every datagram and timer the pump hands any node, so a stale entry (an address a session left, a
//! session that ended) or a missing one fails it at the step it appears.
#![allow(clippy::unwrap_used, clippy::panic, clippy::indexing_slicing)]

use std::net::SocketAddr;

use vinc_core::{Answer, Command, IfaceEvent, IfaceId, Query, Role, SessionId, Value, is_relay_addr};
use vinc_tests::*;

/// The sessions of node `n` whose active path is validated, direct and from `addr`, by a walk of every live session.
fn walk(net: &CoreNet, n: usize, addr: SocketAddr) -> Vec<SessionId> {
    let mut out = Vec::new();
    for k in 0.. {
        let Answer::Stats(st) = net.nodes[n].ep.query(Query::SessionAt(k)) else {
            break;
        };
        if st.path_validated && st.route.map(|(_, r)| r) == Some(addr) && !is_relay_addr(&addr) {
            out.push(st.session);
        }
    }
    out.sort();
    out
}

/// The table answers as the walk does for every address in `addrs`, with every session of the walk excluded in turn.
fn agree(net: &CoreNet, n: usize, addrs: &[SocketAddr]) {
    for a in addrs {
        let all = walk(net, n, *a);
        let ep = &net.nodes[n].ep;
        assert_eq!(ep.session_from(a, |_| true), all.first().copied(), "{a} at {}", net.now);
        for skip in &all {
            let rest = all.iter().copied().find(|s| s != skip);
            assert_eq!(
                ep.session_from(a, |s| s != *skip),
                rest,
                "{a} without {skip:?} at {}",
                net.now
            );
        }
    }
}

/// Run for `span`, checking the table after every step.
fn run_checked(net: &mut CoreNet, n: usize, addrs: &[SocketAddr], span: u64) {
    let end = net.now + span;
    net.run(end, |net| {
        agree(net, n, addrs);
        false
    });
}

fn send(net: &mut CoreNet, n: usize, s: SessionId) {
    let now = net.now;
    let Value::Stream(id) = net.nodes[n]
        .cmd(now, Command::OpenStream { session: s, bidi: true })
        .unwrap()
        .value
    else {
        panic!("no stream")
    };
    net.nodes[n]
        .cmd(
            now,
            Command::Write {
                session: s,
                stream: id,
                data: b"here",
            },
        )
        .unwrap();
    net.nodes[n]
        .cmd(now, Command::Finish { session: s, stream: id })
        .unwrap();
}

#[test]
fn the_table_of_sessions_by_address_answers_as_a_walk_of_the_sessions_through_dials_moves_rebinds_and_closes() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let hub = net.add(1);
        let (twice, mover, natted, closer) = (net.add(2), net.add(3), net.add(4), net.add(5));
        let elsewhere: SocketAddr = ([10, 0, 9, 3], 4433).into();
        let (out1, out2): (SocketAddr, SocketAddr) =
            (([198, 51, 100, 4], 40000).into(), ([198, 51, 100, 4], 40001).into());
        let mut addrs: Vec<SocketAddr> = net.nodes.iter().map(|n| n.addr).collect();
        addrs.extend([elsewhere, out1, out2]);

        // Dials: one member twice from the same address (two protocols), the others once; the NAT is in front of one.
        let (_, two_a) = net.connect_pair(twice, hub, ALPN_A, Role::Other);
        run_checked(&mut net, hub, &addrs, SEC_NS);
        let (_, two_b) = net.connect_pair(twice, hub, ALPN_B, Role::Other);
        run_checked(&mut net, hub, &addrs, SEC_NS);
        assert_eq!(walk(&net, hub, net.nodes[twice].addr), {
            let mut v = vec![two_a, two_b];
            v.sort();
            v
        });
        let (m_side, m_hub) = net.connect_pair(mover, hub, ALPN_A, Role::Other);
        let (_, c_hub) = net.connect_pair(closer, hub, ALPN_A, Role::Other);
        net.nat = Some((net.nodes[natted].addr, out1));
        let (n_side, n_hub) = net.connect_pair(natted, hub, ALPN_A, Role::Other);
        run_checked(&mut net, hub, &addrs, 2 * SEC_NS);
        assert_eq!(net.nodes[hub].ep.session_from(&out1, |_| true), Some(n_hub));

        // A member changes its address: the hub's session moves to the new address once the path is validated.
        let old = net.nodes[mover].addr;
        net.nodes[mover].addr = elsewhere;
        net.loss = Some(Box::new(move |from, _, _| from == old));
        let now = net.now;
        net.nodes[mover].ep.iface_event(now, IfaceId(0), IfaceEvent::Down);
        net.nodes[mover]
            .ep
            .iface_event(now, IfaceId(0), IfaceEvent::AddrChange(elsewhere));
        net.nodes[mover].ep.iface_event(now, IfaceId(0), IfaceEvent::Up);
        send(&mut net, mover, m_side);
        run_checked(&mut net, hub, &addrs, 6 * SEC_NS);
        assert_eq!(
            net.nodes[hub].ep.session_from(&elsewhere, |_| true),
            Some(m_hub),
            "the member that moved is found"
        );
        assert_eq!(
            net.nodes[hub].ep.session_from(&old, |_| true),
            None,
            "nobody is left at the old address"
        );

        // The NAT rebinds to a new outside port.
        net.nat = Some((net.nodes[natted].addr, out2));
        send(&mut net, natted, n_side);
        run_checked(&mut net, hub, &addrs, 6 * SEC_NS);
        assert_eq!(
            net.nodes[hub].ep.session_from(&out2, |_| true),
            Some(n_hub),
            "the rebound member is found"
        );
        assert_eq!(
            net.nodes[hub].ep.session_from(&out1, |_| true),
            None,
            "nobody is left at the old port"
        );

        // The hub closes a session; its slot is taken by the member's next dial.
        let now = net.now;
        net.nodes[hub]
            .cmd(
                now,
                Command::Close {
                    session: c_hub,
                    error: 0,
                },
            )
            .unwrap();
        run_checked(&mut net, hub, &addrs, 3 * SEC_NS);
        assert_eq!(net.nodes[hub].ep.session_from(&net.nodes[closer].addr, |_| true), None);
        let (_, again) = net.connect_pair(closer, hub, ALPN_A, Role::Other);
        run_checked(&mut net, hub, &addrs, 2 * SEC_NS);
        assert_eq!(
            net.nodes[hub].ep.session_from(&net.nodes[closer].addr, |_| true),
            Some(again)
        );
    });
}
