//! The largest UDP payload an interface carries on a path of each address family, and the datagram size probes that
//! follow from it: a probe of 1452 bytes is sent only when the interface carries that much on the path's family.

#![allow(clippy::unwrap_used)]

use vinc_transport::conn::{HEADERS_V4, HEADERS_V6, JUMBO_MTU, MIN_MTU, MtuProbe, PROBE_MTU, interface_payload};

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

#[test]
fn an_echo_with_no_probe_in_flight_changes_nothing() {
    let mut p = MtuProbe::new();
    p.start();
    for size in [u16::MAX, PROBE_MTU, JUMBO_MTU] {
        assert_eq!(
            p.echo(size, 9000, false),
            None,
            "an echo of {size} with nothing in flight"
        );
        assert_eq!(p.view().current, MIN_MTU, "an echo of {size} with nothing in flight");
    }
}

#[test]
fn an_echo_of_another_size_than_the_probe_in_flight_changes_nothing() {
    let mut p = MtuProbe::new();
    p.start();
    p.probe_sent(PROBE_MTU, 7);
    assert_eq!(p.echo(JUMBO_MTU, 9000, false), None);
    assert_eq!(p.echo(u16::MAX, 9000, false), None);
    let v = p.view();
    assert_eq!((v.current, v.inflight), (MIN_MTU, Some(PROBE_MTU)));
    assert_eq!(
        p.echo(PROBE_MTU, 1500, false),
        Some(PROBE_MTU),
        "the echo of the probe in flight is taken"
    );
    let v = p.view();
    assert_eq!((v.current, v.inflight), (PROBE_MTU, None));
}

#[test]
fn an_echo_equal_to_the_probe_in_flight_is_refused_above_what_the_interface_carries_and_the_jumbo_size() {
    // A probe of 8952 on an interface of 1500 (1472 bytes of payload) is above what the interface carries.
    let mut p = MtuProbe::new();
    p.start();
    p.probe_sent(JUMBO_MTU, 7);
    assert_eq!(p.echo(JUMBO_MTU, 1500, false), None);
    let v = p.view();
    assert_eq!(
        (v.current, v.inflight),
        (MIN_MTU, Some(JUMBO_MTU)),
        "the refused echo left the path alone"
    );
    // The same echo within the interface's room is taken.
    assert_eq!(p.echo(JUMBO_MTU, 9000, false), Some(JUMBO_MTU));
    // Above the jumbo size nothing is taken, whatever the interface carries.
    let mut q = MtuProbe::new();
    q.start();
    q.probe_sent(u16::MAX, 7);
    assert_eq!(q.echo(u16::MAX, u16::MAX, false), None);
    assert_eq!(q.view().current, MIN_MTU);
}
