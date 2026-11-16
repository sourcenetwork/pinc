//! Where a datagram that came through a relay is taken to have arrived.

use super::*;

fn addr(s: &str) -> SocketAddr {
    s.parse()
        .unwrap_or_else(|_| SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0))
}

#[test]
fn a_relayed_datagram_arrives_at_the_current_address_of_its_family() {
    let (old, new, v6) = (addr("10.0.0.1:4433"), addr("10.0.1.1:4433"), addr("[fd00::1]:4433"));
    let mut addrs = [None; MAX_ADDRS];
    for (d, a) in addrs.iter_mut().zip([v6, new]) {
        *d = Some(a);
    }
    assert_eq!(inbound_local(&addrs, &addr("240.0.0.3:0"), old), new);
    assert_eq!(inbound_local(&addrs, &addr("[fd00::9]:0"), old), v6);
    assert_eq!(inbound_local(&[None; MAX_ADDRS], &addr("240.0.0.3:0"), old), old);
}
