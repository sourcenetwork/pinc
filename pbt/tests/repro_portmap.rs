//! Reproductions of `pinc-portmap` bugs found by the properties in `portmap.rs`. Each test fails on the code as it is.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, missing_docs)]

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use pinc_portmap::client::PORT;
use pinc_portmap::lease::SEC;
use pinc_portmap::{Config, PortMap, pcp};

const GW: Ipv4Addr = Ipv4Addr::new(192, 168, 1, 1);
const T0: u64 = 1_000 * SEC;
const NONCE: [u8; 12] = [0x5a; 12];

fn gw() -> SocketAddr {
    SocketAddr::new(IpAddr::V4(GW), PORT)
}

fn drain(pm: &mut PortMap) -> usize {
    let mut b = [0u8; pinc_portmap::MAX_DATAGRAM];
    let mut n = 0;
    while pm.poll_datagram(&mut b).is_some() && n < 8 {
        n += 1;
    }
    n
}

fn grant(epoch: u32, lifetime: u32) -> Vec<u8> {
    let r = pcp::Response::Map {
        result: pcp::SUCCESS,
        lifetime,
        epoch,
        nonce: NONCE,
        protocol: pcp::UDP,
        internal_port: 4433,
        external_port: 4433,
        external_ip: IpAddr::V4(Ipv4Addr::new(203, 0, 113, 9)),
    };
    let mut b = [0u8; 60];
    let n = pcp::encode_response(&r, &mut b).unwrap();
    b[..n].to_vec()
}

/// A header-form PCP MAP error (24 bytes, no nonce) that anyone who can send from the gateway's address can forge.
fn header_error(result: u8, epoch: u32) -> Vec<u8> {
    let r = pcp::Response::Header {
        opcode: pcp::OP_MAP,
        result,
        lifetime: 0,
        epoch,
    };
    let mut b = [0u8; 24];
    let n = pcp::encode_response(&r, &mut b).unwrap();
    b[..n].to_vec()
}

/// `mapped()` reports a mapping whose lease ended on the client's clock when the clock reached the end through a
/// call other than `handle_timeout`.
///
/// Expected: `None`. `pinc_portmap::client` module doc: "[`PortMap::mapped`] is a mapping the gateway granted and
/// whose lease has not ended on the client's clock". Every entry point (`handle_datagram`, `handle_http`, `stop`,
/// `restart`) moves the client's clock to `now`, and `handle_timeout` itself ends a lease at `now >= expiry`.
///
/// Actual: `handle_datagram` sets `self.now` but only `handle_timeout` compares it with `held.expiry`, so after a
/// datagram that arrives at or past the end (a host that was suspended, or that runs its socket before its timer)
/// `mapped()` still returns the dead lease. Found by `client_keeps_its_lease_and_nonce_invariants`, replay
/// `EPHYRA_REPLAY=4497193941245644059:409` (the same through NAT-PMP) and `EPHYRA_REPLAY=9341186842301696821:473`
/// (the same through `handle_http`, an HTTP answer the client was not waiting for).
///
/// Suspected fault: `crates/pinc-portmap/src/client.rs:226` (`mapped` reads `held` without the clock) and
/// `client.rs:433-435` (`handle_datagram` advances the clock without ending the lease).
///
/// Who: the local application through the public API, in the order a host may call it; a datagram from anyone on the
/// link (even one the client drops as not its own) is enough to move the clock.
#[test]
fn mapped_reports_a_lease_that_ended_on_the_clients_clock() {
    let mut pm = PortMap::new(Config::new(Some(IpAddr::V4(GW)), "192.168.1.10:4433".parse().unwrap(), NONCE), T0);
    drain(&mut pm);
    pm.handle_datagram(T0, gw(), &grant(5000, 2));
    assert!(pm.mapped().is_some());
    // Two seconds later, before the host ran the timer, a stray datagram arrives: the client's clock is at the end.
    pm.handle_datagram(T0 + 2 * SEC, gw(), &[0u8; 3]);
    assert_eq!(pm.mapped(), None, "the lease ended at {} and the client's clock is there", T0 + 2 * SEC);
}

/// A forged, nonce-less PCP error received while a renewal is in flight drops the held mapping.
///
/// Expected: the mapping held stays. `pinc_portmap::client` module doc: "an answer is taken only from the gateway
/// ... and only for the request in flight (PCP by its nonce, protocol and port ...)"; `docs/proofs/properties.md`
/// (port mapping): "a client that believes an announce's epoch lets a host on the link take a held mapping out of the
/// record", the reason an announce's epoch is never believed. The existing test
/// `a_pcp_error_header_while_a_mapping_is_held_changes_nothing` (tests/portmap_security.rs) pins the same outcome for
/// the step `Held`.
///
/// Actual: the header form carries no nonce, yet in step `Pcp` (which a renewal enters) `pcp_answer` takes it as the
/// answer to the request in flight and passes its epoch to `note_epoch`. An epoch that went back reads as a gateway
/// restart and `held` is set to `None`; `fail` then delays the next request by the retry gap. Found by
/// `client_keeps_its_lease_and_nonce_invariants`, replay `EPHYRA_REPLAY=4496481917054289948:251`.
///
/// Suspected fault: `crates/pinc-portmap/src/client.rs:513-515` (`note_epoch` on a header-form answer, no nonce).
///
/// Who: any host on the link that can send a UDP datagram from the gateway's address to the client's port, without
/// seeing the request. Renewals come at half the lease, so the window is predictable.
#[test]
fn a_forged_pcp_error_header_during_a_renewal_drops_the_held_mapping() {
    let mut pm = PortMap::new(Config::new(Some(IpAddr::V4(GW)), "192.168.1.10:4433".parse().unwrap(), NONCE), T0);
    drain(&mut pm);
    pm.handle_datagram(T0, gw(), &grant(5000, 7200));
    let held = pm.mapped();
    assert!(held.is_some());
    // The renewal at half the lease: the client is now in step Pcp with a request in flight.
    let renew = pm.poll_timeout().unwrap();
    assert_eq!(renew, T0 + 3600 * SEC);
    pm.handle_timeout(renew);
    assert_eq!(drain(&mut pm), 1, "the renewal left");
    // A forged header-form error whose epoch went back.
    pm.handle_datagram(renew + SEC / 100, gw(), &header_error(2, 0));
    assert_eq!(pm.mapped(), held, "a nonce-less datagram took the held mapping out of the record");
}
