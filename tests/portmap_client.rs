//! The port-mapping client against scripted gateways: PCP, the fall back to NAT-PMP and to UPnP, renewal, the end of
//! a lease, a gateway that restarted, and the release on stop.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::doc_markdown, clippy::panic)]

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use vinc_portmap::client::{FIRST_GAP, HTTP_WAIT, PORT, RETRY};
use vinc_portmap::lease::SEC;
use vinc_portmap::upnp::{self, SSDP};
use vinc_portmap::{Config, PortMap, Proto, natpmp, pcp};

const GW: Ipv4Addr = Ipv4Addr::new(192, 168, 1, 1);
const EXT: Ipv4Addr = Ipv4Addr::new(203, 0, 113, 9);
const T0: u64 = 1_000 * SEC;
const NONCE: [u8; 12] = [5; 12];

fn gw() -> SocketAddr {
    SocketAddr::new(GW.into(), PORT)
}

fn local() -> SocketAddr {
    "192.168.1.5:4433".parse().unwrap()
}

fn client(gateway: Option<Ipv4Addr>, local: SocketAddr, lifetime: u32) -> PortMap {
    let mut cfg = Config::new(gateway.map(IpAddr::V4), local, NONCE);
    cfg.lifetime = lifetime;
    PortMap::new(cfg, T0)
}

/// Every datagram the client wants sent now.
fn sent(pm: &mut PortMap) -> Vec<(SocketAddr, Vec<u8>)> {
    let mut out = Vec::new();
    let mut b = [0u8; vinc_portmap::MAX_DATAGRAM];
    while let Some((to, n)) = pm.poll_datagram(&mut b) {
        out.push((to, b[..n].to_vec()));
    }
    out
}

fn pcp_grant(epoch: u32, port: u16, lifetime: u32) -> Vec<u8> {
    let r = pcp::Response::Map {
        result: pcp::SUCCESS,
        lifetime,
        epoch,
        nonce: NONCE,
        protocol: pcp::UDP,
        internal_port: 4433,
        external_port: port,
        external_ip: EXT.into(),
    };
    let mut b = [0u8; 60];
    pcp::encode_response(&r, &mut b).unwrap();
    b.to_vec()
}

fn announce(epoch: u32) -> Vec<u8> {
    let mut b = [0u8; 24];
    let n = pcp::encode_response(
        &pcp::Response::Header {
            opcode: 0,
            result: 0,
            lifetime: 0,
            epoch,
        },
        &mut b,
    )
    .unwrap();
    b[..n].to_vec()
}

fn nat(r: natpmp::Response) -> Vec<u8> {
    let mut b = [0u8; 16];
    let n = natpmp::encode_response(&r, &mut b).unwrap();
    b[..n].to_vec()
}

/// Run the client's timers until `until`.
fn run_to(pm: &mut PortMap, until: u64) {
    while let Some(t) = pm.poll_timeout().filter(|t| *t <= until) {
        pm.handle_timeout(t);
    }
}

#[test]
fn pcp_grants_a_mapping_that_is_renewed_half_way() {
    let mut pm = client(Some(GW), local(), 120);
    let out = sent(&mut pm);
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].0, gw());
    let r = pcp::decode_request(&out[0].1).unwrap();
    assert_eq!(
        (r.lifetime, r.internal_port, r.external_port, r.nonce),
        (120, 4433, 4433, NONCE)
    );
    assert!(pm.owns(gw(), &pcp_grant(1, 4433, 120)));
    pm.handle_datagram(T0 + SEC / 100, gw(), &pcp_grant(1, 4433, 120));
    assert_eq!(pm.mapped(), Some(SocketAddr::new(EXT.into(), 4433)));
    assert_eq!(pm.protocol(), Some(Proto::Pcp));
    // the lease started when the request left: renewal half way from then, the end a lifetime from then
    assert_eq!(pm.poll_timeout(), Some(T0 + 60 * SEC));
    pm.handle_timeout(T0 + 60 * SEC);
    let renew = sent(&mut pm);
    assert_eq!(renew.len(), 1);
    let r = pcp::decode_request(&renew[0].1).unwrap();
    assert_eq!(
        (r.nonce, r.external_port, r.external_ip),
        (NONCE, 4433, IpAddr::V4(EXT)),
        "the renewal asks for the same mapping"
    );
    // still mapped while the renewal is in flight
    assert!(pm.mapped().is_some());
    // the gateway moved the port: the client follows
    pm.handle_datagram(T0 + 60 * SEC, gw(), &pcp_grant(61, 5000, 120));
    assert_eq!(pm.mapped(), Some(SocketAddr::new(EXT.into(), 5000)));
}

#[test]
fn a_lease_whose_renewals_go_unanswered_ends_on_the_client_clock() {
    let mut pm = client(Some(GW), local(), 120);
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_grant(1, 4433, 120));
    // the gateway goes silent: renewals are tried, then the lease ends at T0 + 120 s, not later
    let mut t = T0;
    while pm.mapped().is_some() {
        t = pm.poll_timeout().unwrap();
        assert!(t <= T0 + 120 * SEC);
        pm.handle_timeout(t);
        sent(&mut pm);
    }
    assert_eq!(t, T0 + 120 * SEC);
    // and the client asks from the beginning
    let again = sent(&mut pm);
    assert!(again.is_empty() || again[0].0 == gw());
}

#[test]
fn a_nat_pmp_gateway_answers_the_fallback() {
    let mut pm = client(Some(GW), local(), 7200);
    sent(&mut pm);
    // a NAT-PMP-only server answers the PCP request with its unsupported-version error
    pm.handle_datagram(
        T0,
        gw(),
        &nat(natpmp::Response::Error {
            opcode: 1,
            result: 1,
            epoch: 50,
        }),
    );
    let out = sent(&mut pm);
    assert_eq!(natpmp::decode_request(&out[0].1), Ok(natpmp::Request::Address));
    pm.handle_datagram(
        T0,
        gw(),
        &nat(natpmp::Response::Address {
            result: 0,
            epoch: 50,
            ip: EXT,
        }),
    );
    let out = sent(&mut pm);
    assert_eq!(
        natpmp::decode_request(&out[0].1),
        Ok(natpmp::Request::Map {
            internal_port: 4433,
            external_port: 4433,
            lifetime: 7200
        })
    );
    pm.handle_datagram(
        T0,
        gw(),
        &nat(natpmp::Response::Map {
            result: 0,
            epoch: 50,
            internal_port: 4433,
            external_port: 4433,
            lifetime: 7200,
        }),
    );
    assert_eq!(pm.mapped(), Some(SocketAddr::new(EXT.into(), 4433)));
    assert_eq!(pm.protocol(), Some(Proto::NatPmp));
    // the renewal shows the gateway restarted (its epoch went back): the mapping is dropped at once and asked again
    pm.handle_timeout(T0 + 3600 * SEC);
    assert_eq!(
        natpmp::decode_request(&sent(&mut pm)[0].1),
        Ok(natpmp::Request::Address)
    );
    pm.handle_datagram(
        T0 + 3600 * SEC,
        gw(),
        &nat(natpmp::Response::Address {
            result: 0,
            epoch: 3,
            ip: EXT,
        }),
    );
    assert_eq!(pm.mapped(), None);
    assert!(matches!(
        natpmp::decode_request(&sent(&mut pm)[0].1),
        Ok(natpmp::Request::Map { .. })
    ));
}

#[test]
fn an_announce_brings_the_renewal_forward_and_the_renewal_finds_a_restart() {
    let mut pm = client(Some(GW), local(), 7200);
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_grant(1000, 4433, 7200));
    assert!(pm.mapped().is_some());
    // ten seconds later an announce arrives: nothing in it is checked, so the mapping stays
    pm.handle_datagram(T0 + 10 * SEC, gw(), &announce(2));
    assert!(pm.mapped().is_some(), "an unchecked announce dropped the mapping");
    let renewal = pm.poll_timeout().unwrap();
    assert!(
        (T0 + 10 * SEC..=T0 + 15 * SEC).contains(&renewal),
        "the renewal is brought forward by 0 to 5 s"
    );
    pm.handle_timeout(renewal);
    let out = sent(&mut pm);
    assert_eq!(out.len(), 1);
    assert!(pcp::decode_request(&out[0].1).is_ok(), "the renewal is asked for");
    // the gateway restarted: the renewal is refused and its epoch went back
    let refused = pcp::Response::Map {
        result: 2,
        lifetime: 0,
        epoch: 2,
        nonce: NONCE,
        protocol: pcp::UDP,
        internal_port: 4433,
        external_port: 4433,
        external_ip: EXT.into(),
    };
    let mut b = [0u8; 60];
    pcp::encode_response(&refused, &mut b).unwrap();
    pm.handle_datagram(renewal, gw(), &b);
    assert_eq!(pm.mapped(), None, "the restart the renewal's epoch shows was not found");
    assert!(!sent(&mut pm).is_empty(), "the mapping is asked for again");
}

/// Run the UPnP leg: answer the SSDP search, then each HTTP request with `answers`, in order.
fn upnp_leg(pm: &mut PortMap, t: u64, answers: &[&[u8]]) -> Vec<String> {
    let ssdp = b"HTTP/1.1 200 OK\r\nST: urn:schemas-upnp-org:device:InternetGatewayDevice:1\r\nLOCATION: http://192.168.1.1:5000/rootDesc.xml\r\n\r\n";
    let from = SocketAddr::new(GW.into(), 1900);
    assert!(pm.owns(from, ssdp));
    pm.handle_datagram(t, from, ssdp);
    let mut reqs = Vec::new();
    for a in answers {
        let mut b = [0u8; upnp::MAX_REQUEST];
        let (to, n) = pm.poll_http(&mut b).unwrap();
        assert_eq!(to, "192.168.1.1:5000".parse().unwrap());
        reqs.push(String::from_utf8(b[..n].to_vec()).unwrap());
        pm.handle_http(t, Some(a));
    }
    reqs
}

const DESC: &[u8] = b"HTTP/1.1 200 OK\r\n\r\n<root><device><serviceList><service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>/ctl/IPConn</controlURL></service></serviceList></device></root>";
const EXTIP: &[u8] = b"HTTP/1.1 200 OK\r\n\r\n<u:GetExternalIPAddressResponse><NewExternalIPAddress>203.0.113.9</NewExternalIPAddress></u:GetExternalIPAddressResponse>";
const OK: &[u8] = b"HTTP/1.1 200 OK\r\n\r\n<u:AddPortMappingResponse/>";

#[test]
fn a_silent_gateway_falls_back_to_upnp() {
    let mut pm = client(Some(GW), local(), 7200);
    // three PCP tries, three NAT-PMP tries, then the SSDP search
    let mut t = T0;
    let mut pcp_n = 0;
    let mut nat_n = 0;
    loop {
        let out = sent(&mut pm);
        if out.iter().any(|(to, _)| *to == SSDP) {
            break;
        }
        for (_, b) in out {
            if b[0] == 2 { pcp_n += 1 } else { nat_n += 1 }
        }
        t = pm.poll_timeout().unwrap();
        pm.handle_timeout(t);
    }
    assert_eq!((pcp_n, nat_n), (3, 3));
    assert_eq!(t, T0 + 2 * 7 * FIRST_GAP, "250, 500 and 1000 ms for each protocol");
    // a 718 conflict moves to the next port; 725 asks for a permanent lease
    let conflict = b"HTTP/1.1 500 Error\r\n\r\n<errorCode>718</errorCode>";
    let perm = b"HTTP/1.1 500 Error\r\n\r\n<errorCode>725</errorCode>";
    let reqs = upnp_leg(&mut pm, t, &[DESC, EXTIP, conflict, perm, OK]);
    assert!(reqs[0].starts_with("GET /rootDesc.xml HTTP/1.0"));
    assert!(reqs[1].contains("#GetExternalIPAddress"));
    assert!(reqs[2].contains("<NewExternalPort>4433<") && reqs[2].contains("<NewLeaseDuration>7200<"));
    assert!(reqs[3].contains("<NewExternalPort>4434<"));
    assert!(reqs[4].contains("<NewExternalPort>4434<") && reqs[4].contains("<NewLeaseDuration>0<"));
    assert_eq!(pm.mapped(), Some(SocketAddr::new(EXT.into(), 4434)));
    assert_eq!(pm.protocol(), Some(Proto::Upnp));
    // stop: DeletePortMapping of that port, then nothing
    pm.stop(t + SEC);
    assert_eq!(pm.mapped(), None);
    let mut b = [0u8; upnp::MAX_REQUEST];
    let (_, n) = pm.poll_http(&mut b).unwrap();
    let del = std::str::from_utf8(&b[..n]).unwrap();
    assert!(del.contains("#DeletePortMapping") && del.contains("<NewExternalPort>4434<"));
    assert!(!pm.stopped());
    pm.handle_http(t + SEC, Some(OK));
    assert!(pm.stopped());
    assert_eq!(pm.poll_timeout(), None);
}

#[test]
fn an_http_exchange_the_host_never_finishes_ends_by_the_deadline() {
    let mut pm = client(None, local(), 7200);
    assert_eq!(sent(&mut pm)[0].0, SSDP, "with no gateway known only UPnP is tried");
    let ssdp = b"HTTP/1.1 200 OK\r\nLOCATION: http://192.168.1.1:5000/d.xml\r\n\r\n";
    pm.handle_datagram(T0, SocketAddr::new(GW.into(), 1900), ssdp);
    let mut b = [0u8; upnp::MAX_REQUEST];
    assert!(pm.poll_http(&mut b).is_some());
    assert_eq!(pm.poll_timeout(), Some(T0 + HTTP_WAIT));
    pm.handle_timeout(T0 + HTTP_WAIT);
    assert_eq!(
        pm.poll_timeout(),
        Some(T0 + HTTP_WAIT + RETRY),
        "every protocol failed: try again later"
    );
    assert_eq!(pm.mapped(), None);
}

#[test]
fn answers_from_elsewhere_are_not_taken() {
    let mut pm = client(Some(GW), local(), 7200);
    sent(&mut pm);
    let other = SocketAddr::new(Ipv4Addr::new(192, 168, 1, 77).into(), PORT);
    assert!(!pm.owns(other, &pcp_grant(1, 4433, 7200)));
    pm.handle_datagram(T0, other, &pcp_grant(1, 4433, 7200));
    assert_eq!(pm.mapped(), None);
    // a grant for another nonce is not ours
    let mut g = pcp_grant(1, 4433, 7200);
    g[24] ^= 1;
    pm.handle_datagram(T0, gw(), &g);
    assert_eq!(pm.mapped(), None);
    // with a gateway known, an SSDP answer from another device is not taken either
    run_to(&mut pm, T0 + 2 * 7 * FIRST_GAP);
    assert!(sent(&mut pm).iter().any(|(to, _)| *to == SSDP));
    let ssdp = b"HTTP/1.1 200 OK\r\nLOCATION: http://192.168.1.77:5000/d.xml\r\n\r\n";
    assert!(!pm.owns(SocketAddr::new(Ipv4Addr::new(192, 168, 1, 77).into(), 1900), ssdp));
}

#[test]
fn stop_releases_a_pcp_mapping_with_lifetime_zero() {
    let mut pm = client(Some(GW), local(), 7200);
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_grant(1, 4433, 7200));
    pm.stop(T0 + SEC);
    assert_eq!(pm.mapped(), None);
    assert!(!pm.stopped(), "the release is not sent yet");
    let out = sent(&mut pm);
    assert_eq!(out.len(), 1);
    let r = pcp::decode_request(&out[0].1).unwrap();
    assert_eq!((r.lifetime, r.nonce, r.external_port), (0, NONCE, 4433));
    assert!(pm.stopped());
    assert_eq!(pm.poll_timeout(), None);
    // nothing afterwards, whatever arrives
    pm.handle_datagram(T0 + 2 * SEC, gw(), &pcp_grant(1, 4433, 7200));
    assert_eq!(pm.mapped(), None);
    assert_eq!(sent(&mut pm), Vec::new());
}

#[test]
fn a_socket_on_the_unspecified_address_tries_nat_pmp_only() {
    let any: SocketAddr = "0.0.0.0:4433".parse().unwrap();
    let mut pm = client(Some(GW), any, 7200);
    assert_eq!(
        natpmp::decode_request(&sent(&mut pm)[0].1),
        Ok(natpmp::Request::Address)
    );
    run_to(&mut pm, T0 + 7 * FIRST_GAP);
    assert!(
        sent(&mut pm).is_empty(),
        "no SSDP search: UPnP needs the client's address"
    );
    assert_eq!(pm.poll_timeout(), Some(T0 + 7 * FIRST_GAP + RETRY));
    // and with no gateway either, nothing at all
    let mut idle = client(None, any, 7200);
    assert_eq!(sent(&mut idle), Vec::new());
    assert_eq!(idle.poll_timeout(), None);
}

#[test]
fn a_renewal_refused_by_a_restarted_gateway_drops_the_mapping() {
    let mut pm = client(Some(GW), local(), 7200);
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_grant(1000, 4433, 7200));
    pm.handle_timeout(T0 + 3600 * SEC);
    assert!(pcp::decode_request(&sent(&mut pm)[0].1).is_ok(), "the renewal goes out");
    // the gateway restarted (epoch 3, not 4600) and refuses the renewal: the mapping it lost is not kept
    let mut b = [0u8; 24];
    let refusal = pcp::Response::Header {
        opcode: pcp::OP_MAP,
        result: 8,
        lifetime: 30,
        epoch: 3,
    };
    let n = pcp::encode_response(&refusal, &mut b).unwrap();
    pm.handle_datagram(T0 + 3600 * SEC, gw(), &b[..n]);
    assert_eq!(pm.mapped(), None);
    // the same through NAT-PMP: a refused mapping request with an epoch that went back
    let mut pm = client(Some(GW), local(), 7200);
    sent(&mut pm);
    pm.handle_datagram(
        T0,
        gw(),
        &nat(natpmp::Response::Error {
            opcode: 1,
            result: 1,
            epoch: 50,
        }),
    );
    pm.handle_datagram(
        T0,
        gw(),
        &nat(natpmp::Response::Address {
            result: 0,
            epoch: 50,
            ip: EXT,
        }),
    );
    pm.handle_datagram(
        T0,
        gw(),
        &nat(natpmp::Response::Map {
            result: 0,
            epoch: 50,
            internal_port: 4433,
            external_port: 4433,
            lifetime: 7200,
        }),
    );
    pm.handle_timeout(T0 + 3600 * SEC);
    pm.handle_datagram(
        T0 + 3600 * SEC,
        gw(),
        &nat(natpmp::Response::Address {
            result: 0,
            epoch: 3650,
            ip: EXT,
        }),
    );
    assert!(pm.mapped().is_some(), "an epoch at the clocks' pace is no restart");
    pm.handle_datagram(
        T0 + 3600 * SEC,
        gw(),
        &nat(natpmp::Response::Error {
            opcode: 1,
            result: 3,
            epoch: 1,
        }),
    );
    assert_eq!(pm.mapped(), None);
}
