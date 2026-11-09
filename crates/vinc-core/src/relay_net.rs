//! Relay paths: the addresses the endpoint uses for a path that runs through a relay carrier.
//!
//! A packet to or from a peer through a relay has no UDP address. The connectivity layer names such a path with a
//! synthetic address, one per (relay, peer) pair, and moves the datagrams between the endpoint and the carrier. The
//! endpoint treats any address in this range as a relay path (it costs a second more when the active path is chosen,
//! and its congestion state survives a move from one relay to another). IPv4 addresses are `240.relay.peer`
//! (the reserved class E block, never routed) and IPv6 addresses are `fd56:494e:43::relay:peer`; the port is
//! unused. `relay` is a table position below 256 and `peer` a table position the connectivity layer assigns.
//!
//! Invariants: [`relay_addr`] and [`relay_parts`] are inverses; an address outside the block is never a relay path.

use core::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

/// The first octet of an IPv4 relay path address.
pub const RELAY_V4: u8 = 240;
/// The first 32 bits of an IPv6 relay path address: `fd56:494e`.
const RELAY_V6: [u16; 2] = [0xfd56, 0x494e];

/// The synthetic address of the path through relay slot `relay` to peer slot `peer`.
pub const fn relay_addr(v6: bool, relay: u8, peer: u16) -> SocketAddr {
    let [p0, p1] = peer.to_be_bytes();
    if v6 {
        SocketAddr::new(
            IpAddr::V6(Ipv6Addr::new(
                RELAY_V6[0],
                RELAY_V6[1],
                0x43,
                0,
                0,
                relay as u16,
                0,
                peer,
            )),
            0,
        )
    } else {
        SocketAddr::new(IpAddr::V4(Ipv4Addr::new(RELAY_V4, relay, p0, p1)), 0)
    }
}

/// The relay slot and peer slot of a relay path address, or `None` for any other address.
pub const fn relay_parts(a: &SocketAddr) -> Option<(u8, u16)> {
    match a.ip() {
        IpAddr::V4(ip) => {
            let [o, relay, p0, p1] = ip.octets();
            if o == RELAY_V4 {
                Some((relay, u16::from_be_bytes([p0, p1])))
            } else {
                None
            }
        }
        IpAddr::V6(ip) => {
            let s = ip.segments();
            if s[0] == RELAY_V6[0]
                && s[1] == RELAY_V6[1]
                && s[2] == 0x43
                && s[3] == 0
                && s[4] == 0
                && s[5] <= 0xff
                && s[6] == 0
            {
                Some((s[5] as u8, s[7]))
            } else {
                None
            }
        }
    }
}

/// Whether `a` names a path through a relay.
pub const fn is_relay_addr(a: &SocketAddr) -> bool {
    relay_parts(a).is_some()
}
