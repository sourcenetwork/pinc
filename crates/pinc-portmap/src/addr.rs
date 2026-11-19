//! Which addresses the client trusts: the hosts it may send HTTP to when an answer names one, the local addresses it
//! searches from, and the external addresses it holds.
//!
//! Invariants: pure functions of the address, no allocation, no panic.

use core::net::{IpAddr, Ipv4Addr};

/// Whether `ip` is in the shared address space of carrier-grade NAT (100.64.0.0/10).
pub const fn is_shared(ip: Ipv4Addr) -> bool {
    let o = ip.octets();
    o[0] == 100 && o[1] & 0xc0 == 64
}

/// Whether `ip` is a private address a home network uses: RFC 1918 or carrier-grade NAT (100.64.0.0/10).
pub const fn is_private(ip: Ipv4Addr) -> bool {
    ip.is_private() || is_shared(ip)
}

/// Whether `ip` may be the host of an HTTP request taken from an answer: not unspecified, loopback, multicast,
/// broadcast or link-local.
pub const fn usable_host(ip: Ipv4Addr) -> bool {
    !(ip.is_unspecified() || ip.is_loopback() || ip.is_multicast() || ip.is_broadcast() || ip.is_link_local())
}

/// Whether `ip` may be the external address of a mapping: one a peer on the internet could send to. Unspecified,
/// loopback, multicast, link-local and private addresses (RFC 1918, 100.64.0.0/10, IPv6 unique local) are not.
pub const fn external_ok(ip: IpAddr) -> bool {
    match ip.to_canonical() {
        IpAddr::V4(v4) => usable_host(v4) && !is_private(v4),
        IpAddr::V6(v6) => {
            let s = v6.segments()[0];
            !(v6.is_unspecified()
                || v6.is_loopback()
                || v6.is_multicast()
                || s & 0xffc0 == 0xfe80
                || s & 0xfe00 == 0xfc00)
        }
    }
}
