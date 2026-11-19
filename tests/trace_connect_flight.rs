//! Trace generation for the candidate list of a flight (`pinc_connect::client::Connectivity::candidates_for`, read
//! through the `trace_candidates` probe of the `trace` feature): seeded and fixed calls of the real layer, recorded as
//! ndjson (`connect_flight.ndjson`) for the TLA+ trace check (`TraceConnectFlight.tla`).
//!
//! A layer with three relays and five peers: one heard only on the local link (a beacon), one with a record only, one
//! with both, one with neither, and a node that carries the relay role, named as a peer. Phase 1 has no home relay yet;
//! in phase 2 the address discovery of relay 1 made it the home and records came in by lookup answers. Every call
//! shows what the layer read (the hints, the beacon addresses, the record, whether it is fresh, the relays of the peer
//! and of its record, the home, `fwd`) and the candidates it built, in order.
//!
//! The test checks by itself: no repeat and at most 16 candidates, every direct address before every relay, the hints
//! first, a stale record's addresses left out, the home relay listed with `fwd` when there is room and not listed
//! without it for a peer homed elsewhere, and at most two relays with the peer's before ours.
#![allow(
    dead_code,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::cognitive_complexity,
    clippy::too_many_arguments,
    unreachable_pub,
    clippy::cast_possible_wrap,
    clippy::manual_is_multiple_of
)]

mod connect_common;

use core::net::SocketAddr;
use std::fmt::Write as _;

use connect_common::{SEC, big_stack, ed, id, nid};
use pinc_connect::carrier::DnsAnswer;
use pinc_connect::client::conn::FOUND_TTL;
use pinc_connect::client::dial::Cand;
use pinc_connect::client::{Config, Connectivity, Port, RelayCfg};
use pinc_connect::local;
use pinc_connect::record::{self, MAX_RECORD_LEN, Reach, RecordFields};
use pinc_connect::relay::datagram::Datagram;
use pinc_core::{CommandError, Events, NodeStats, PeerInfo, Reply, Role, SessionId, SessionStats, Value};
use pinc_crypto::{Drbg, Keypair, NodeId, Software};
use pinc_security::{ConnId, Env};
use pinc_tests::{Host, SplitMix64, soaking};

const MS: u64 = 1_000_000;

/// The endpoint the layer drives, as a stub: it has no sessions and answers every command with nothing (as the stub
/// of `connect_flight_fwd.rs`).
struct Stub {
    route: (SocketAddr, SocketAddr),
    now: u64,
    retx: u64,
    next: u64,
}

impl Port for Stub {
    type Src = pinc_transport::stream::NoSource;

    fn command(&mut self, _: u64, cmd: pinc_core::Command<'_, Self::Src>) -> Result<Reply, CommandError> {
        let value = match cmd {
            pinc_core::Command::Connect { .. } => {
                self.next += 1;
                Value::Session(SessionId(self.next))
            }
            _ => Value::None,
        };
        Ok(Reply {
            value,
            events: Events::default(),
        })
    }

    fn stats(&self, session: SessionId) -> Option<SessionStats> {
        let hub = session == SessionId(1);
        let transport = pinc_transport::conn::Stats {
            handshake_retransmits: self.retx,
            ..Default::default()
        };
        (session.0 == 1 || session.0 == 2).then(|| SessionStats {
            session,
            node: None,
            alpn: None,
            role: Role::Hub,
            gossip: false,
            dialer: true,
            established: hub,
            allowed: true,
            path: None,
            route: hub.then_some(self.route),
            thin: false,
            held: 0,
            held_dropped: 0,
            pto: 0,
            pto_count: 0,
            path_validated: hub,
            heard: self.now,
            heard_any: self.now,
            pulse_due: false,
            last_app: 0,
            sub: false,
            answered: true,
            transport,
        })
    }

    fn node(&self) -> Option<NodeStats> {
        Some(NodeStats {
            sessions: 2,
            half_open: 1,
            lrtt: 300 * MS,
            tgr: 0,
            hs_floor: 0,
            thin: true,
            ledger: 0,
            datagrams_in: 0,
            datagrams_out: 0,
            dropped_in: 0,
            dropped_out: 0,
            reach_dropped: 0,
            ext_dropped: 0,
            held_by_ledger: 0,
            stalled_in: 0,
            events_dropped: 0,
            events_lost: 0,
            fragments_held: 0,
            fragments_replayed: 0,
            fragments_expired: 0,
            fragments_evicted: 0,
            fragments_waiting: 0,
            holders_refused: 0,
            first_too_short: 0,
            stateless_rejects: 0,
            stateless_refused: 0,
            events_queued: 0,
            backlog_refused: 0,
            owed: 0,
        })
    }

    fn peer(&self, _: &NodeId) -> Option<PeerInfo> {
        None
    }

    fn reach_body(&self, _: SessionId, _: &mut [u8; pinc_core::REACH_BODY_MAX]) -> usize {
        0
    }

    fn by_conn_id(&self, _: &ConnId) -> Option<SessionStats> {
        None
    }
}

type Conn = Connectivity<Software, 3, 4>;

fn a(s: &str) -> SocketAddr {
    s.parse().unwrap()
}

/// What the calls exercised.
#[derive(Default)]
struct Seen {
    cut16: u32,
    two_relays: u32,
    no_relay: u32,
}

struct T {
    out: String,
    seen: Seen,
}

/// A peer, and what the layer was told of it.
struct Peer {
    id: NodeId,
    beacon: Vec<SocketAddr>,
    rec: Vec<SocketAddr>,
    /// When its record was stored (the time of the lookup answer), or the time of the first record for a peer with
    /// none.
    at: u64,
}

fn quoted(v: &[SocketAddr]) -> String {
    let items: Vec<String> = v.iter().map(|x| format!("\"{x}\"")).collect();
    format!("[{}]", items.join(","))
}

fn num(v: Option<usize>) -> i64 {
    v.map_or(-1, |x| x as i64)
}

/// One call of the probe, checked and recorded.
fn call(t: &mut T, conn: &mut Conn, node: &NodeId, hints: &[SocketAddr], fresh_at: Option<u64>, fwd: bool) {
    let p = conn.trace_candidates(node, hints, fresh_at, fwd);
    let out = &p.out[..p.n];
    let beacon: Vec<SocketAddr> = p
        .beacon
        .map_or_else(Vec::new, |b| b.iter().flatten().copied().collect());
    let rec: Vec<SocketAddr> = p
        .record
        .map_or_else(Vec::new, |b| b.iter().flatten().copied().collect());
    // no repeat, at most 16, every direct address before every relay
    assert!(p.n <= 16);
    assert!(
        out.iter().enumerate().all(|(i, c)| !out[..i].contains(c)),
        "a repeat in {out:?}"
    );
    let n_udp = out.iter().take_while(|c| matches!(c, Cand::Udp(_))).count();
    assert!(
        out[n_udp..].iter().all(|c| matches!(c, Cand::Relay(_))),
        "a direct address after a relay in {out:?}"
    );
    // the hints first, deduplicated, in order, cut at 16
    let mut distinct: Vec<SocketAddr> = Vec::new();
    for h in hints {
        if !distinct.contains(h) {
            distinct.push(*h);
        }
    }
    let k = distinct.len().min(16);
    assert!(out.len() >= k, "the hints were cut: {out:?}");
    for (c, h) in out.iter().zip(&distinct[..k]) {
        assert_eq!(*c, Cand::Udp(*h), "the hints do not lead");
    }
    // a stale record's addresses are left out unless they are a hint or a beacon address
    if p.record.is_some() && !p.fresh {
        for c in out {
            if let Cand::Udp(x) = c
                && rec.contains(x)
            {
                assert!(
                    hints.contains(x) || beacon.contains(x),
                    "a stale record's address {x} was listed"
                );
            }
        }
    }
    // the relays: at most two, the peer's before ours, ours when there is room
    let relays: Vec<u8> = out
        .iter()
        .filter_map(|c| if let Cand::Relay(r) = c { Some(*r) } else { None })
        .collect();
    assert!(relays.len() <= 2);
    let peer_r = p.peer_relay.or(p.home_relay);
    if relays.len() == 2 {
        assert_eq!(
            peer_r.map(|r| r as u8),
            Some(relays[0]),
            "the peer's relay does not come first"
        );
    }
    if p.home == Some(1) {
        if fwd {
            let need = 1 + usize::from(peer_r.is_some_and(|r| r != 1));
            if n_udp + need <= 16 {
                assert!(relays.contains(&1), "the home relay is not listed with room for it");
            }
        } else if p.record.is_some() && peer_r != Some(1) {
            assert!(
                !relays.contains(&1),
                "the home relay is listed for a peer homed elsewhere"
            );
        }
    }
    t.seen.cut16 += u32::from(n_udp == 16 && (peer_r.is_some() || fwd && p.home.is_some()));
    t.seen.two_relays += u32::from(relays.len() == 2);
    t.seen.no_relay += u32::from(relays.is_empty());
    let cands: Vec<String> = out
        .iter()
        .map(|c| match c {
            Cand::Udp(x) => format!(r#"{{"k":"u","a":"{x}","r":-1}}"#),
            Cand::Relay(r) => format!(r#"{{"k":"r","a":"","r":{r}}}"#),
        })
        .collect();
    let _ = writeln!(
        t.out,
        r#"{{"t":"fl","v":{{"hints":{},"beacon":{},"hasRec":{},"rec":{},"fresh":{},"peer":{},"recHome":{},"home":{},"fwd":{fwd}}},"out":[{}]}}"#,
        quoted(hints),
        quoted(&beacon),
        p.record.is_some(),
        quoted(&rec),
        p.fresh || p.record.is_none(),
        num(p.peer_relay),
        num(p.home_relay),
        num(p.home),
        cands.join(",")
    );
}

fn beacon(conn: &mut Conn, kp: &Keypair, now: u64, addrs: &[SocketAddr]) {
    let mut buf = vec![0u8; local::MAX_LEN];
    let n = local::sign(kp, 1, addrs, &[], &mut buf).unwrap();
    assert_eq!(conn.handle_beacon(now, &buf[..n]), Some(id(kp)));
}

/// Answer a lookup for `kp` with a record homed on `home` that lists `addrs`, at `*t` (moved on first).
fn record_of(
    conn: &mut Conn,
    hub_udp: SocketAddr,
    t: &mut u64,
    kp: &Keypair,
    home: NodeId,
    addrs: &[SocketAddr],
) -> u64 {
    let fields = RecordFields {
        home,
        seq: 1,
        reach: Reach::Nat,
        addrs,
        hints: b"",
    };
    let mut rec = vec![0u8; MAX_RECORD_LEN];
    let n = record::sign(kp, &fields, &mut rec).unwrap();
    let mut out = [0u8; 1500];
    let m = Datagram::DnsReply {
        peer: id(kp),
        answer: DnsAnswer::Record(&rec[..n]),
    }
    .encode(&mut out)
    .unwrap();
    *t += 40 * MS;
    assert!(conn.handle_udp(*t, hub_udp, &out[..m]));
    *t
}

fn hint_lists(p: &Peer) -> Vec<Vec<SocketAddr>> {
    let h1 = a("203.0.113.7:7000");
    let pool = |n: usize| -> Vec<SocketAddr> { (0..n).map(|i| a(&format!("192.0.2.{}:9000", i + 1))).collect() };
    let mut v = vec![vec![], vec![h1], vec![h1, h1]];
    if let Some(b) = p.beacon.first() {
        v.push(vec![*b]);
    }
    if let Some(r) = p.rec.first() {
        v.push(vec![*r]);
    }
    v.push(pool(12));
    v.push(pool(16));
    v.push(pool(20));
    v.push(vec![a("[2001:db8::7]:7000"), h1]);
    v
}

#[test]
fn flight_candidates_match_the_model() {
    big_stack(|| {
        let mut rng = SplitMix64::traced(0xF1_1647);
        let mut t = T {
            out: String::new(),
            seen: Seen::default(),
        };
        let host = Box::new(Host::new(0x41, a("192.168.1.2:4433"), 1000 * SEC));
        let relay_ids = [id(&ed(0x10)), id(&ed(0x11)), id(&ed(0x12))];
        let hub_udp = a("203.0.113.10:4433");
        let local_addr = a("192.168.1.2:4433");
        let mut relays = [None; 3];
        relays[0] = Some(RelayCfg {
            id: relay_ids[0],
            udp: Some(a("203.0.113.11:4433")),
            tcp: None,
            ws: None,
        });
        relays[1] = Some(RelayCfg {
            id: relay_ids[1],
            udp: Some(hub_udp),
            tcp: Some(a("203.0.113.10:443")),
            ws: None,
        });
        relays[2] = Some(RelayCfg {
            id: relay_ids[2],
            udp: Some(a("203.0.113.12:4433")),
            tcp: None,
            ws: None,
        });
        let cfg = Config {
            me: host.identity.node_id(),
            identity: host.identity,
            relays,
            phone: false,
            restarted: false,
            start: 1000 * SEC,
            v6: false,
            keep_learn: false,
        };
        let mut conn: Box<Conn> = Box::new(Connectivity::new(cfg, host.prekey_info.clone(), Software, 7));
        conn.set_local(&[local_addr]);
        let (k40, k41, k42, k43) = (ed(0x40), ed(0x41), ed(0x42), ed(0x43));
        let mut peers = [id(&k40), id(&k41), id(&k42), id(&k43), relay_ids[2]].map(|id| Peer {
            id,
            beacon: Vec::new(),
            rec: Vec::new(),
            at: 0,
        });
        // phase 1: no home relay yet
        let b40: Vec<SocketAddr> = (0..4).map(|i| a(&format!("10.0.0.40:{}", 4000 + i))).collect();
        let b42 = vec![a("10.0.0.42:4000"), a("192.168.1.9:4433")];
        beacon(&mut conn, &k40, 1000 * SEC, &b40);
        beacon(&mut conn, &k42, 1000 * SEC + MS, &b42);
        peers[0].beacon = b40;
        peers[2].beacon = b42;
        for p in &peers {
            for hints in hint_lists(p) {
                for fwd in [false, true] {
                    call(&mut t, &mut conn, &p.id, &hints, None, fwd);
                }
            }
        }
        // phase 2: the home through address discovery, as connect_flight_fwd.rs does it
        let mut ep = Stub {
            route: (local_addr, hub_udp),
            now: 1000 * SEC,
            retx: 0,
            next: 0,
        };
        let mut drbg = Drbg::new(&[0x62; 32]);
        let mut buf = vec![0u8; 2048];
        let mut now = 1000 * SEC + SEC;
        while conn.home() != Some(1) && now < 1000 * SEC + 3 * SEC {
            now += 50 * MS;
            let mut env = Env {
                provider: &Software,
                now,
                drbg: &mut drbg,
            };
            conn.drive(now, &mut ep, &mut env, None);
            while let Some((_, to, n)) = conn.poll_udp_from(&mut buf) {
                if to == hub_udp
                    && let Ok(Datagram::Qad { nonce }) = Datagram::decode(&buf[..n])
                {
                    let mut out = [0u8; 64];
                    let m = Datagram::Qadr {
                        nonce,
                        addr: a("198.51.100.7:4433"),
                    }
                    .encode(&mut out)
                    .unwrap();
                    conn.handle_udp(now + 20 * MS, hub_udp, &out[..m]);
                }
            }
        }
        assert_eq!(conn.home(), Some(1), "relay 1 became the home relay");
        // the lookup answers, after every time the clock has seen
        let mut at = now + SEC;
        let r41: Vec<SocketAddr> = (0..3).map(|i| a(&format!("198.51.100.41:{}", 5000 + i))).collect();
        let mut r42 = vec![a("10.0.0.42:4000")];
        r42.extend((0..7).map(|i| a(&format!("198.51.100.42:{}", 5000 + i))));
        let r43 = vec![a("198.51.100.43:5000")];
        peers[1].at = record_of(&mut conn, hub_udp, &mut at, &k41, relay_ids[0], &r41);
        peers[2].at = record_of(&mut conn, hub_udp, &mut at, &k42, relay_ids[1], &r42);
        peers[3].at = record_of(&mut conn, hub_udp, &mut at, &k43, nid(0x99), &r43);
        peers[0].at = record_of(&mut conn, hub_udp, &mut at, &k40, relay_ids[2], &[]);
        peers[4].at = peers[1].at;
        peers[1].rec = r41;
        peers[2].rec = r42;
        peers[3].rec = r43;
        let fresh = |p: &Peer| [None, Some(p.at + FOUND_TTL - 1), Some(p.at + FOUND_TTL)];
        for p in &peers {
            for hints in hint_lists(p) {
                for fresh_at in fresh(p) {
                    for fwd in [false, true] {
                        call(&mut t, &mut conn, &p.id, &hints, fresh_at, fwd);
                    }
                }
            }
        }
        // random calls over a pool of 24 addresses, the beacon and record addresses among them
        let mut pool: Vec<SocketAddr> = Vec::new();
        for x in peers.iter().flat_map(|p| p.beacon.iter().chain(&p.rec)) {
            if !pool.contains(x) {
                pool.push(*x);
            }
        }
        let mut i = 1;
        while pool.len() < 24 {
            pool.push(a(&format!("192.0.2.{i}:9000")));
            i += 1;
        }
        for _ in 0..200 {
            let p = &peers[(rng.next_u64() % 5) as usize];
            let n = (rng.next_u64() % 21) as usize;
            let hints: Vec<SocketAddr> = (0..n).map(|_| pool[(rng.next_u64() % 24) as usize]).collect();
            let fresh_at = fresh(p)[(rng.next_u64() % 3) as usize];
            call(&mut t, &mut conn, &p.id, &hints, fresh_at, rng.next_u64() % 2 == 0);
        }
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("connect_flight.ndjson"), &t.out).unwrap();
        }
        if !soaking() {
            let s = &t.seen;
            assert!(s.cut16 > 0, "no call had 16 entries with a relay cut off");
            assert!(s.two_relays > 0, "no call listed two relays");
            assert!(s.no_relay > 0, "no call listed no relay");
        }
    });
}
