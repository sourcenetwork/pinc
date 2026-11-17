//! The largest UDP payload an interface carries on a path of each address family, and the datagram size probes that
//! follow from it: a probe of 1452 bytes is sent only when the interface carries that much on the path's family.

#![allow(clippy::unwrap_used)]

use vinc_transport::conn::{HEADERS_V4, HEADERS_V6, MtuProbe, PROBE_MTU, interface_payload};

#[test]
fn the_interface_payload_is_the_mtu_less_the_headers_of_the_family() {
    // (interface MTU, IPv4 payload, IPv6 payload)
    let table = [
        (1500u16, 1472u16, 1452u16),
        (1280, 1252, 1232),
        (1420, 1392, 1372),
        (HEADERS_V4, 0, 0),
        (HEADERS_V6, 20, 0),
        (10, 0, 0),
        (0, 0, 0),
    ];
    for (mtu, v4, v6) in table {
        assert_eq!(interface_payload(mtu, false), v4, "IPv4, interface {mtu}");
        assert_eq!(interface_payload(mtu, true), v6, "IPv6, interface {mtu}");
    }
}

/// The size due on a started, unprobed path on an interface of `mtu` bytes.
fn probe_due(mtu: u16, v6: bool) -> Option<u16> {
    let mut p = MtuProbe::new();
    p.start();
    p.target(true, mtu, v6, false, 0)
}

#[test]
fn a_probe_of_1452_bytes_is_sent_only_when_the_interface_carries_it_on_the_path() {
    assert_eq!(probe_due(1500, true), Some(PROBE_MTU), "1500 carries 1452 over IPv6");
    assert_eq!(probe_due(1500, false), Some(PROBE_MTU));
    assert_eq!(probe_due(1460, true), None, "1460 carries 1412 over IPv6");
    assert_eq!(probe_due(1460, false), None, "1460 carries 1432 over IPv4");
    assert_eq!(probe_due(1280, false), None);
    assert_eq!(
        probe_due(1480, false),
        Some(PROBE_MTU),
        "1480 carries exactly 1452 over IPv4"
    );
    assert_eq!(probe_due(1500, true), Some(PROBE_MTU));
}

#[test]
fn an_interface_of_1472_bytes_never_sends_a_probe_of_1452_bytes() {
    // 1472 carries 1444 bytes over IPv4 and 1424 over IPv6: a 1452-byte probe is a datagram the interface drops.
    assert_eq!(probe_due(1472, false), None);
    assert_eq!(probe_due(1472, true), None);
}
