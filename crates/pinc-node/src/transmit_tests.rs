//! Which datagrams the node returns to its host and which it routes through the connectivity client.

#![allow(clippy::unwrap_used, reason = "test assertions")]

use pinc_core::{LOCAL_RELAY, relay_addr, relay_parts};
use pinc_crypto::{IdentityAlg, Keypair};

use crate::layer_tests::{TNode, big, node_with};

/// A peer the client names a relay path for.
fn peer() -> pinc_crypto::NodeId {
    Keypair::from_seed(IdentityAlg::Ed25519, &[0x52; 32]).unwrap().node_id()
}

/// The member address the host's relay role gives the slot the client gave `peer`, as the facade's tunnel makes it.
fn member_on_clients_slot(n: &mut TNode) -> core::net::SocketAddr {
    let client = n.conn.path_addr(0, &peer());
    let (_, slot) = relay_parts(&client).unwrap();
    relay_addr(false, LOCAL_RELAY, slot)
}

/// Send one packet to `to` and say whether the node returned it to the host.
fn returned(n: &mut TNode, to: core::net::SocketAddr) -> bool {
    n.io.ep.transmits.push_back(to);
    let mut out = [0u8; 64];
    n.poll_transmit(1, &mut out).is_some_and(|t| t.remote == to)
}

/// A hub returns a packet for a member of its own relay role even when the member's slot is the slot of a client path.
#[test]
fn a_hub_returns_the_packets_for_its_own_relay_roles_members() {
    big(|| {
        let mut n = node_with(true);
        let member = member_on_clients_slot(&mut n);
        assert!(
            returned(&mut n, member),
            "the member's packet was routed through the client"
        );
    });
}

/// A node that carries the relay role without the hub role returns them too.
#[test]
fn a_node_with_the_relay_role_and_no_hub_role_returns_the_packets_for_its_members() {
    big(|| {
        let mut n = node_with(false);
        let member = member_on_clients_slot(&mut n);
        assert!(
            returned(&mut n, member),
            "the member's packet was routed through the client"
        );
    });
}

/// A packet on a path of the client is never returned to the host.
#[test]
fn a_packet_on_a_client_path_is_routed_not_returned() {
    big(|| {
        for hub in [false, true] {
            let mut n = node_with(hub);
            let client = n.conn.path_addr(0, &peer());
            assert!(
                !returned(&mut n, client),
                "hub {hub}: a client path packet came back to the host"
            );
        }
    });
}

/// A hub returns a packet on a relay path its client has no slot for and that is not the role's index, as before the
/// reserved index existed.
#[test]
fn a_hub_returns_a_packet_on_a_relay_path_its_client_does_not_know() {
    big(|| {
        let mut n = node_with(true);
        let unknown = relay_addr(false, 1, 200);
        assert!(
            returned(&mut n, unknown),
            "a packet on a path the client does not know was routed through the client"
        );
    });
}
