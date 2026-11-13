//! A tunnel packet leaves from the local address of the hub session that carries it: the hub knows the member by the
//! address that session uses, so a packet from the member's other address is refused as unauthenticated.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod connect_common;

use core::net::SocketAddr;

use connect_common::{SEC, big_stack, ed, id, nid};
use vinc_connect::client::{Config, Connectivity, Port, RelayCfg};
use vinc_core::{
    Command, CommandError, Event, Events, NodeStats, PeerInfo, Reply, Role, SessionId, SessionStats, Value,
};
use vinc_crypto::Software;
use vinc_security::{Alpn, ConnId};
use vinc_tests::Host;

/// An endpoint that holds one established, validated hub session on the route `route`.
struct Stub {
    route: (SocketAddr, SocketAddr),
    now: u64,
}

impl Port for Stub {
    type Src = vinc_transport::stream::NoSource;

    fn command(&mut self, _: u64, cmd: Command<'_, Self::Src>) -> Result<Reply, CommandError> {
        let value = match cmd {
            Command::Connect { .. } => Value::Session(SessionId(1)),
            _ => Value::None,
        };
        Ok(Reply {
            value,
            events: Events::default(),
        })
    }

    fn stats(&self, session: SessionId) -> Option<SessionStats> {
        (session == SessionId(1)).then(|| SessionStats {
            session,
            node: None,
            alpn: None,
            role: Role::Hub,
            gossip: false,
            dialer: true,
            established: true,
            allowed: true,
            path: None,
            route: Some(self.route),
            thin: false,
            held: 0,
            held_dropped: 0,
            pto: 0,
            pto_count: 0,
            path_validated: true,
            heard: self.now,
            pulse_due: false,
            last_app: 0,
            sub: false,
            transport: vinc_transport::conn::Stats::default(),
        })
    }

    fn node(&self) -> Option<NodeStats> {
        None
    }

    fn peer(&self, _: &vinc_crypto::NodeId) -> Option<PeerInfo> {
        None
    }

    fn reach_body(&self, _: SessionId, _: &mut [u8; vinc_core::REACH_BODY_MAX]) -> usize {
        0
    }

    fn by_conn_id(&self, _: &ConnId) -> Option<SessionStats> {
        None
    }
}

#[test]
fn a_tunnel_packet_leaves_from_the_local_address_of_the_hub_session() {
    big_stack(|| {
        let host = Box::new(Host::new(0x41, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let hub_kp = ed(0x77);
        let hub = id(&hub_kp);
        let hub_udp: SocketAddr = "203.0.113.10:4433".parse().unwrap();
        // The hub session runs from the second address of a host that has two.
        let (first, second): (SocketAddr, SocketAddr) =
            ("192.168.1.2:4433".parse().unwrap(), "[fd00::2]:4433".parse().unwrap());
        let mut relays = [None; 1];
        relays[0] = Some(RelayCfg {
            id: hub,
            udp: Some(hub_udp),
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
        let mut conn: Box<Connectivity<Software, 1, 4>> =
            Box::new(Connectivity::new(cfg, host.prekey_info.clone(), Software, 7));
        conn.set_local(&[first, second]);
        let now = 1000 * SEC + SEC;
        let mut ep = Stub {
            route: (second, hub_udp),
            now,
        };
        let session = conn
            .dial(now, &mut ep, hub, b"vinc/hub", Role::Hub, &[hub_udp])
            .unwrap();
        let connected = Event::Connected {
            session,
            node: hub,
            alpn: Alpn::new(b"vinc/hub").unwrap(),
            resumed: false,
        };
        conn.observe(now, &mut ep, &connected);
        let mut buf = vec![0u8; 2048];
        while conn.poll_udp_from(&mut buf).is_some() {}
        // A packet for a peer behind the hub, with no carrier open: it goes down the hub session as a tunnel packet.
        let peer = nid(0xb7);
        let to_peer = conn.path_addr(0, &peer);
        assert!(conn.route(now, &ep, to_peer, &[0x41; 100]));
        let (from, to, _) = conn.poll_udp_from(&mut buf).expect("a tunnel packet");
        assert_eq!(to, hub_udp);
        assert_eq!(from, Some(second), "it leaves from the address of the hub session");
    });
}
