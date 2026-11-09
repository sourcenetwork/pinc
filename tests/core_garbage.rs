//! Garbage never panics: random datagrams, corrupted and truncated real ones, and commands with stale or absurd
//! arguments, and the endpoint keeps serving afterwards.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation
)]

use std::net::SocketAddr;

use vinc_core::{Answer, Command, Event, Query, Role, SessionId, Value};
use vinc_crypto::NodeId;
use vinc_tests::*;

#[test]
fn random_and_corrupted_datagrams_leave_the_endpoint_serving() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        net.capture = true;
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        // Real traffic to corrupt, in both directions.
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
        net.nodes[a]
            .cmd(
                t,
                Command::Write {
                    session: sa,
                    stream: id,
                    data: &pattern(20_000, 5),
                },
            )
            .unwrap();
        net.run_for(2 * SEC_NS);
        let real: Vec<(SocketAddr, SocketAddr, Vec<u8>)> = net.captured.clone();
        assert!(real.len() > 10);
        let mut rng = SplitMix64::new(0xBAD);
        let (addr_a, addr_b) = (net.nodes[a].addr, net.nodes[b].addr);
        let mut fed = 0u32;
        for round in 0..6000u32 {
            let now = net.now + u64::from(round);
            let kind = rng.next_u64() % 5;
            let (from, to, mut d) = {
                let (f, t, d) = &real[(rng.next_u64() as usize) % real.len()];
                (*f, *t, d.clone())
            };
            match kind {
                0 => {
                    // Pure noise of a random length, sometimes shaped like a header.
                    let n = (rng.next_u64() % 1500) as usize;
                    d = vec![0u8; n];
                    rng.fill(&mut d);
                    if let Some(f) = d.first_mut() {
                        *f = [0x40, 0xC0, 0xE0, 0x00, 0xFF][(rng.next_u64() % 5) as usize];
                    }
                }
                1 => {
                    // Flip a few bits of a real datagram.
                    for _ in 0..=(rng.next_u64() % 4) {
                        let i = (rng.next_u64() as usize) % d.len();
                        d[i] ^= 1 << (rng.next_u64() % 8);
                    }
                }
                2 => d.truncate((rng.next_u64() as usize) % d.len()),
                3 => {
                    let extra = (rng.next_u64() % 64) as usize;
                    let mut tail = vec![0u8; extra];
                    rng.fill(&mut tail);
                    d.extend_from_slice(&tail);
                }
                _ => {
                    // Overwrite a window with noise.
                    let at = (rng.next_u64() as usize) % d.len();
                    let n = ((rng.next_u64() % 40) as usize).min(d.len() - at);
                    rng.fill(&mut d[at..at + n]);
                }
            }
            let target = if to == addr_b { b } else { a };
            net.nodes[target].ep.handle_datagram(now, to, from, &mut d);
            fed += 1;
            if round % 500 == 0 {
                net.nodes[target].service(now);
            }
        }
        assert!(fed > 5000);
        let _ = (addr_a, addr_b);
        // Both endpoints still carry a clean transfer.
        net.pump_all();
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
        net.nodes[a]
            .cmd(
                t,
                Command::Write {
                    session: sa,
                    stream: id,
                    data: b"still-alive",
                },
            )
            .unwrap();
        net.nodes[a]
            .cmd(
                t,
                Command::Finish {
                    session: sa,
                    stream: id,
                },
            )
            .unwrap();
        let want = net.nodes[b].read.len() + 1;
        assert!(net.run(
            t + 30 * SEC_NS,
            |n| n.nodes[b].read.values().any(|v| v == b"still-alive") || n.nodes[b].read.len() > want + 5
        ));
        assert!(net.nodes[b].read.values().any(|v| v == b"still-alive"));
    });
}

#[test]
fn a_stranger_cannot_fill_the_table_with_noise_shaped_like_handshakes() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let b = net.add(2);
        let to = net.nodes[b].addr;
        let mut rng = SplitMix64::new(77);
        for i in 0..3000u32 {
            let mut d = vec![0u8; 1200 + (rng.next_u64() % 200) as usize];
            rng.fill(&mut d);
            // A long header of the handshake type with a plausible length and message type.
            d[0] = 0xC0;
            d[1] = 1;
            d[2] = 8;
            d[11] = 4;
            let from: SocketAddr = ([10, 7, (i >> 8) as u8, i as u8], 9).into();
            net.nodes[b]
                .ep
                .handle_datagram(net.now + u64::from(i), to, from, &mut d);
        }
        net.pump_all();
        let ns = net.nodes[b].ep.node_stats();
        assert!(ns.sessions <= 8 && ns.half_open <= 8, "{ns:?}");
        assert!(ns.ledger <= 1024);
        assert!(!net.nodes[b].saw(|e| matches!(e, Event::Incoming { .. })));
    });
}

#[test]
fn commands_with_stale_or_absurd_arguments_fail_cleanly() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let t = net.now;
        let ghost = SessionId(0xFFFF_FFFF_FFFF_FFFF);
        let stale = SessionId(sa.0 + (1 << 32));
        for s in [ghost, stale] {
            for c in [
                Command::OpenStream { session: s, bidi: true },
                Command::Write {
                    session: s,
                    stream: 0,
                    data: b"x",
                },
                Command::Finish { session: s, stream: 0 },
                Command::Reset {
                    session: s,
                    stream: 0,
                    error: 1,
                },
                Command::Consume {
                    session: s,
                    stream: 0,
                    n: 9,
                },
                Command::SendDatagram { session: s, data: b"x" },
                Command::Close { session: s, error: 1 },
                Command::SetRole {
                    session: s,
                    role: Role::Hub,
                },
                Command::SetGossip {
                    session: s,
                    gossip: true,
                },
            ] {
                assert!(net.nodes[a].cmd(t, c).is_err());
            }
        }
        // Real session, absurd stream ids and sizes.
        assert!(
            net.nodes[a]
                .cmd(
                    t,
                    Command::Write {
                        session: sa,
                        stream: 9999,
                        data: b"x"
                    }
                )
                .is_err()
        );
        assert!(
            net.nodes[a]
                .cmd(
                    t,
                    Command::Consume {
                        session: sa,
                        stream: 9999,
                        n: usize::MAX
                    }
                )
                .is_err()
        );
        assert!(
            net.nodes[a]
                .cmd(
                    t,
                    Command::SendDatagram {
                        session: sa,
                        data: &vec![0u8; 70_000]
                    }
                )
                .is_err()
        );
        assert!(
            net.nodes[a]
                .cmd(
                    t,
                    Command::AcpAnswer {
                        check: u64::MAX,
                        allow: true
                    }
                )
                .is_err()
        );
        assert!(
            net.nodes[a]
                .cmd(
                    t,
                    Command::KeyResponse {
                        session: sa,
                        response: vinc_security::KeyResponse::Failed
                    }
                )
                .is_err()
        );
        let other = NodeId {
            alg: vinc_crypto::IdentityAlg::Ed25519,
            bytes: [3; 32],
        };
        let nowhere: SocketAddr = "192.0.2.1:9".parse().unwrap();
        assert!(
            net.nodes[a]
                .connect(t, other, &[0u8; 64], nowhere, Role::Other)
                .is_err()
        );
        for q in [
            Query::Stats(ghost),
            Query::SessionAt(99),
            Query::PeerAt(9999),
            Query::KeyRequest(ghost),
            Query::Read {
                session: ghost,
                stream: 3,
            },
        ] {
            assert!(matches!(net.nodes[a].ep.query(q), Answer::None));
        }
        // The session is untouched by all of that.
        net.run_for(SEC_NS);
        assert!(matches!(net.nodes[a].ep.query(Query::Stats(sa)), Answer::Stats(_)));
    });
}

/// A first flight with a bit flipped on the way (still a valid Initial of another dialer) makes the server start a
/// session for it; the dialer's own repeat then replaces that session, and the dial completes.
#[test]
fn a_damaged_first_flight_does_not_stop_the_dial() {
    use std::cell::Cell;
    use std::rc::Rc;

    big_stack(|| {
        for at in [80usize, 120, 200, 300, 400, 500] {
            let mut net = CoreNet::new(5 * MS_NS);
            net.capture = true;
            let (a, b) = (net.add(1), net.add(2));
            let (addr_a, addr_b) = (net.nodes[a].addr, net.nodes[b].addr);
            // The first long datagram of the dialer never arrives; a copy with one bit flipped does.
            let taken = Rc::new(Cell::new(false));
            let seen = Rc::clone(&taken);
            net.loss = Some(Box::new(move |from, _, d| {
                let first = from == addr_a && !seen.get() && d.first().is_some_and(|b| b & 0x80 != 0);
                seen.set(seen.get() || first);
                first
            }));
            let (peer, now) = (net.nodes[b].node, net.now);
            net.nodes[a].connect(now, peer, ALPN_A, addr_b, Role::Other).unwrap();
            net.pump_all();
            assert!(taken.get());
            let mut damaged = net.captured.iter().find(|(f, ..)| *f == addr_a).unwrap().2.clone();
            damaged[at] ^= 1;
            net.inject(addr_a, addr_b, damaged, 0);
            let ok = net.run(now + 10 * SEC_NS, |n| {
                n.nodes[a].saw(|e| matches!(e, Event::Connected { .. }))
                    && n.nodes[b].saw(|e| matches!(e, Event::Incoming { .. }))
            });
            assert!(ok, "byte {at}: {:?} / {:?}", net.nodes[a].events, net.nodes[b].events);
        }
    });
}

/// A peer that still holds a session with a restarted node keeps writing to the address the node came back on. Those
/// datagrams must not hold back the node's own dial to that peer.
#[test]
fn a_dial_to_an_address_that_wrote_first_still_goes_out() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (addr_a, addr_b) = (net.nodes[a].addr, net.nodes[b].addr);
        // Two small datagrams from b reach a before a has sent anything: the ledger holds b to three times them.
        net.inject(addr_b, addr_a, vec![0x40; 25], 0);
        net.inject(addr_b, addr_a, vec![0x41; 25], 0);
        net.run_for(MS_NS * 20);
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(sa)) else {
            panic!()
        };
        assert!(st.established && st.dialer);
    });
}
