//! `RELAY_FWD` lasts until the handshake is done: a dial that started without a usable record keeps our home relay in
//! its flight until its handshake completes, even when it reported `Connected` at once on a cached allow.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod connect_common;

use core::net::SocketAddr;

use connect_common::{SEC, big_stack, ed, id, record_bytes};
use pinc_connect::carrier::DnsAnswer;
use pinc_connect::client::{Config, Connectivity, Port, RelayCfg};
use pinc_connect::relay::datagram::Datagram;
use pinc_core::{
    Command, CommandError, Event, Events, NodeStats, PeerInfo, Reply, Role, SessionId, SessionStats, Value,
};
use pinc_crypto::{Drbg, NodeId, Software};
use pinc_security::{Alpn, ConnId, Env};
use pinc_tests::Host;

const MS: u64 = 1_000_000;

/// Session 1 is an established, validated hub session; session 2 is a dial in handshake with `retx` resends. The
/// node's handshake round trip is 300 ms (slow). Every `FlightPaths` the layer sends is kept.
struct Stub {
    route: (SocketAddr, SocketAddr),
    now: u64,
    retx: u64,
    next: u64,
    /// The highest session number of a dial in handshake (the hub is session 1).
    dials: u64,
    /// Whether the dials have ended: the endpoint knows none of them.
    gone: bool,
    /// The addresses of every `FlightPaths`, by session.
    lists: Vec<(SessionId, Vec<SocketAddr>)>,
}

impl Port for Stub {
    type Src = pinc_transport::stream::NoSource;

    fn command(&mut self, _: u64, cmd: Command<'_, Self::Src>) -> Result<Reply, CommandError> {
        let value = match cmd {
            Command::Connect { .. } => {
                self.next += 1;
                Value::Session(SessionId(self.next))
            }
            Command::FlightPaths { session, addrs, .. } => {
                self.lists.push((session, addrs.to_vec()));
                Value::None
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
        (session.0 == 1 || ((2..=self.dials).contains(&session.0) && !self.gone)).then(|| SessionStats {
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

    fn peer(&self, _: &pinc_crypto::NodeId) -> Option<PeerInfo> {
        None
    }

    fn reach_body(&self, _: SessionId, _: &mut [u8; pinc_core::REACH_BODY_MAX]) -> usize {
        0
    }

    fn by_conn_id(&self, _: &ConnId) -> Option<SessionStats> {
        None
    }
}

/// A node whose home relay is the hub, up after its address discovery: the layer, the stub endpoint, the random
/// source, the time, the hub's id and the other relay's id.
fn home_up() -> (Box<Connectivity<Software, 2, 4>>, Stub, Drbg, u64, NodeId, NodeId) {
    let host = Box::new(Host::new(0x41, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
    let (hub, other) = (id(&ed(0x77)), id(&ed(0x78)));
    let hub_udp: SocketAddr = "203.0.113.10:4433".parse().unwrap();
    let local: SocketAddr = "192.168.1.2:4433".parse().unwrap();
    let mut relays = [None; 2];
    relays[0] = Some(RelayCfg {
        id: other,
        udp: Some("203.0.113.11:4433".parse().unwrap()),
        tcp: None,
        ws: None,
    });
    relays[1] = Some(RelayCfg {
        id: hub,
        udp: Some(hub_udp),
        tcp: Some("203.0.113.10:443".parse().unwrap()),
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
    let mut conn: Box<Connectivity<Software, 2, 4>> =
        Box::new(Connectivity::new(cfg, host.prekey_info.clone(), Software, 7));
    conn.set_local(&[local]);
    let mut ep = Stub {
        route: (local, hub_udp),
        now: 1000 * SEC,
        retx: 0,
        next: 0,
        dials: 2,
        gone: false,
        lists: Vec::new(),
    };
    let mut drbg = Drbg::new(&[0x62; 32]);
    let mut buf = vec![0u8; 2048];
    let mut t = 1000 * SEC + SEC;
    // The hub answers the address discovery and becomes the home relay.
    while conn.home() != Some(1) && t < 1000 * SEC + 3 * SEC {
        t += 50 * MS;
        let mut env = Env {
            provider: &Software,
            now: t,
            drbg: &mut drbg,
        };
        conn.drive(t, &mut ep, &mut env, None);
        while let Some((_, to, n)) = conn.poll_udp_from(&mut buf) {
            if to == hub_udp
                && let Ok(Datagram::Qad { nonce }) = Datagram::decode(&buf[..n])
            {
                let mut out = [0u8; 64];
                let m = Datagram::Qadr {
                    nonce,
                    addr: "198.51.100.7:4433".parse().unwrap(),
                }
                .encode(&mut out)
                .unwrap();
                conn.handle_udp(t + 20 * MS, hub_udp, &out[..m]);
            }
        }
    }
    assert_eq!(conn.home(), Some(1), "the hub became the home relay");
    ep.now = t;
    (conn, ep, drbg, t, hub, other)
}

/// `RELAY_FWD` lasts until the handshake is done. A dial with a cached allow reports `Connected` at once, before its
/// handshake; the answer to its lookup then names the peer's relay, and our home relay stays in the flight, because the
/// peer may answer on the copy that came through it.
#[test]
fn an_early_connected_keeps_the_home_relay_in_the_flight_of_a_dial_without_a_record() {
    big_stack(|| {
        let (mut conn, mut ep, mut drbg, mut t, hub, other) = home_up();
        let hub_udp: SocketAddr = "203.0.113.10:4433".parse().unwrap();
        // Session 1 (the hub, established in the stub) comes first, so the dial below is session 2, in its handshake.
        conn.dial(t, &mut ep, hub, b"pinc/hub", Role::Hub, &[hub_udp]).unwrap();
        let peer_kp = ed(0x79);
        let peer = id(&peer_kp);
        let dial = conn.dial(t, &mut ep, peer, b"app/1", Role::Other, &[]).unwrap();
        assert_eq!(dial, SessionId(2));
        conn.observe(
            t,
            &mut ep,
            &Event::Connected {
                session: dial,
                node: peer,
                alpn: Alpn::new(b"app/1").unwrap(),
                resumed: false,
            },
        );
        // The answer: the peer is homed on the other relay.
        let rec = record_bytes(&peer_kp, other, 1);
        let mut out = [0u8; 1500];
        let n = Datagram::DnsReply {
            peer,
            answer: DnsAnswer::Record(&rec),
        }
        .encode(&mut out)
        .unwrap();
        t += 40 * MS;
        assert!(conn.handle_udp(t, hub_udp, &out[..n]));
        let mut env = Env {
            provider: &Software,
            now: t,
            drbg: &mut drbg,
        };
        conn.drive(t, &mut ep, &mut env, None);
        let list = ep
            .lists
            .iter()
            .rev()
            .find(|(s, _)| *s == dial)
            .map(|(_, l)| l.clone())
            .expect("the answer set the paths of the dial");
        assert!(list.contains(&conn.path_addr(0, &peer)), "the peer's relay: {list:?}");
        assert!(
            list.contains(&conn.path_addr(1, &peer)),
            "our home relay stays in the flight until the handshake is done: {list:?}"
        );
    });
}

/// A pending dial that ended drops its lookup, however many end in one drive (the table holds as many as there are
/// lookups, not eight).
#[test]
fn twelve_dials_that_end_in_one_drive_all_drop_their_lookups() {
    big_stack(|| {
        let (mut conn, mut ep, mut drbg, mut t, hub, _) = home_up();
        let hub_udp: SocketAddr = "203.0.113.10:4433".parse().unwrap();
        conn.dial(t, &mut ep, hub, b"pinc/hub", Role::Hub, &[hub_udp]).unwrap();
        for tag in 0..12u8 {
            conn.dial(t, &mut ep, id(&ed(0xa0 + tag)), b"app/1", Role::Other, &[])
                .unwrap();
        }
        ep.dials = 13;
        assert_eq!(conn.lookups_outstanding(), 12, "a lookup for each pending dial");
        ep.gone = true;
        t += 10 * MS;
        let mut env = Env {
            provider: &Software,
            now: t,
            drbg: &mut drbg,
        };
        conn.drive(t, &mut ep, &mut env, None);
        assert_eq!(conn.lookups_outstanding(), 0, "a dial that ended kept its lookup");
    });
}
