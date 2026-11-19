//! The port-mapping codecs: PCP and NAT-PMP decode what they encode and nothing else, the UPnP parsers take their one
//! form, and no input makes any of them panic.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::doc_markdown,
    clippy::panic,
    clippy::many_single_char_names
)]

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use pinc_portmap::natpmp::{self, NatPmpError};
use pinc_portmap::pcp::{self, MapRequest, PcpError};
use pinc_portmap::upnp::{self, Call, SoapResult, Url};
use proptest::prelude::*;

fn req() -> MapRequest {
    MapRequest {
        lifetime: 7200,
        client: IpAddr::V4(Ipv4Addr::new(192, 168, 1, 5)),
        nonce: [7; 12],
        protocol: pcp::UDP,
        internal_port: 4433,
        external_port: 4433,
        external_ip: IpAddr::V4(Ipv4Addr::UNSPECIFIED),
    }
}

#[test]
fn a_pcp_map_request_has_the_rfc_layout() {
    let mut b = [0u8; 64];
    assert_eq!(pcp::encode_request(&req(), &mut b), Ok(60));
    assert_eq!(&b[..4], &[2, 1, 0, 0]);
    assert_eq!(&b[4..8], &7200u32.to_be_bytes());
    assert_eq!(&b[8..24], &Ipv4Addr::new(192, 168, 1, 5).to_ipv6_mapped().octets());
    assert_eq!(&b[24..36], &[7; 12]);
    assert_eq!(&b[36..40], &[17, 0, 0, 0]);
    assert_eq!(&b[40..44], &[0x11, 0x51, 0x11, 0x51]);
    assert_eq!(&b[44..60], &Ipv4Addr::UNSPECIFIED.to_ipv6_mapped().octets());
    assert_eq!(pcp::decode_request(&b[..60]), Ok(req()));
}

#[test]
fn pcp_refuses_every_other_form() {
    let mut b = [0u8; 60];
    pcp::encode_request(&req(), &mut b).unwrap();
    assert_eq!(pcp::decode_request(&b[..59]), Err(PcpError::Length));
    let mut v = b;
    v[0] = 1;
    assert_eq!(pcp::decode_request(&v), Err(PcpError::Version(1)));
    let mut r = b;
    r[2] = 1;
    assert_eq!(pcp::decode_request(&r), Err(PcpError::Reserved));
    let mut m = b;
    m[38] = 1;
    assert_eq!(pcp::decode_request(&m), Err(PcpError::Reserved));
    // a short output writes nothing
    let mut short = [9u8; 59];
    assert_eq!(pcp::encode_request(&req(), &mut short), Err(PcpError::Short));
    assert!(short.iter().all(|c| *c == 9));
    // a NAT-PMP server's answer of any length says: fall back
    assert_eq!(pcp::decode_response(&[0, 129, 0, 1, 0, 0, 0, 5]), Err(PcpError::NatPmp));
    // a successful header that is not an ANNOUNCE is not a form
    let mut h = [0u8; 24];
    h[0] = 2;
    h[1] = 0x81;
    assert_eq!(pcp::decode_response(&h), Err(PcpError::Form));
    h[1] = 0x80;
    assert!(matches!(
        pcp::decode_response(&h),
        Ok(pcp::Response::Header {
            opcode: 0,
            result: 0,
            ..
        })
    ));
}

#[test]
fn natpmp_messages_have_the_rfc_layout() {
    let mut b = [0u8; 16];
    assert_eq!(natpmp::encode_request(&natpmp::Request::Address, &mut b), Ok(2));
    assert_eq!(&b[..2], &[0, 0]);
    let m = natpmp::Request::Map {
        internal_port: 4433,
        external_port: 4433,
        lifetime: 7200,
    };
    assert_eq!(natpmp::encode_request(&m, &mut b), Ok(12));
    assert_eq!(&b[..12], &[0, 1, 0, 0, 0x11, 0x51, 0x11, 0x51, 0, 0, 0x1c, 0x20]);
    let addr = [0, 128, 0, 0, 0, 0, 0, 9, 203, 0, 113, 9];
    assert_eq!(
        natpmp::decode_response(&addr),
        Ok(natpmp::Response::Address {
            result: 0,
            epoch: 9,
            ip: Ipv4Addr::new(203, 0, 113, 9)
        })
    );
    assert_eq!(natpmp::decode_response(&addr[..11]), Err(NatPmpError::Length));
    assert_eq!(
        natpmp::decode_response(&[0, 129, 0, 0, 0, 0, 0, 9]),
        Err(NatPmpError::Form)
    );
    assert_eq!(natpmp::decode_response(&[1, 128]), Err(NatPmpError::Version(1)));
}

fn ip_strategy() -> impl Strategy<Value = IpAddr> {
    prop_oneof![
        any::<[u8; 4]>().prop_map(|o| IpAddr::V4(Ipv4Addr::from(o))),
        any::<[u8; 16]>().prop_map(|o| IpAddr::V6(o.into()).to_canonical()),
    ]
}

proptest! {
    #[test]
    fn pcp_request_round_trips(lifetime: u32, client in ip_strategy(), nonce: [u8; 12], protocol: u8,
                               internal_port: u16, external_port: u16, external_ip in ip_strategy()) {
        let r = MapRequest { lifetime, client, nonce, protocol, internal_port, external_port, external_ip };
        let mut b = [0u8; 60];
        prop_assert_eq!(pcp::encode_request(&r, &mut b), Ok(60));
        prop_assert_eq!(pcp::decode_request(&b), Ok(r));
    }

    #[test]
    fn pcp_response_round_trips(result: u8, lifetime: u32, epoch: u32, nonce: [u8; 12], protocol: u8,
                                internal_port: u16, external_port: u16, external_ip in ip_strategy(), opcode in 0u8..2) {
        let m = pcp::Response::Map { result, lifetime, epoch, nonce, protocol, internal_port, external_port, external_ip };
        let mut b = [0u8; 60];
        prop_assert_eq!(pcp::encode_response(&m, &mut b), Ok(60));
        prop_assert_eq!(pcp::decode_response(&b), Ok(m));
        let h = pcp::Response::Header { opcode, result, lifetime, epoch };
        match pcp::encode_response(&h, &mut b) {
            Ok(n) => prop_assert_eq!(pcp::decode_response(&b[..n]), Ok(h)),
            Err(e) => prop_assert_eq!(e, PcpError::Form),
        }
    }

    #[test]
    fn natpmp_round_trips(internal_port: u16, external_port: u16, lifetime: u32, result: u16, epoch: u32, ip: [u8; 4], opcode in 0u8..128) {
        let mut b = [0u8; 16];
        for r in [natpmp::Request::Address, natpmp::Request::Map { internal_port, external_port, lifetime }] {
            let n = natpmp::encode_request(&r, &mut b).unwrap();
            prop_assert_eq!(natpmp::decode_request(&b[..n]), Ok(r));
        }
        for r in [
            natpmp::Response::Address { result, epoch, ip: Ipv4Addr::from(ip) },
            natpmp::Response::Map { result, epoch, internal_port, external_port, lifetime },
            natpmp::Response::Error { opcode, result, epoch },
        ] {
            match natpmp::encode_response(&r, &mut b) {
                Ok(n) => prop_assert_eq!(natpmp::decode_response(&b[..n]), Ok(r)),
                Err(e) => prop_assert!(e == NatPmpError::Form && result == 0),
            }
        }
    }

    /// Every decoder takes any bytes without panicking, and what it accepts encodes back to the same bytes.
    #[test]
    fn decoders_never_panic_and_accept_only_canonical_bytes(b in proptest::collection::vec(any::<u8>(), 0..80)) {
        let mut out = [0u8; 80];
        if let Ok(r) = pcp::decode_request(&b) {
            let n = pcp::encode_request(&r, &mut out).unwrap();
            prop_assert_eq!(&out[..n], &b[..]);
        }
        if let Ok(r) = pcp::decode_response(&b) {
            // an IPv4-mapped address decodes to IPv4 and encodes back to the same bytes
            let n = pcp::encode_response(&r, &mut out).unwrap();
            prop_assert_eq!(&out[..n], &b[..]);
        }
        if let Ok(r) = natpmp::decode_request(&b) {
            let n = natpmp::encode_request(&r, &mut out).unwrap();
            prop_assert_eq!(&out[..n], &b[..]);
        }
        if let Ok(r) = natpmp::decode_response(&b) {
            let n = natpmp::encode_response(&r, &mut out).unwrap();
            prop_assert_eq!(&out[..n], &b[..]);
        }
    }

    /// The text parsers take any bytes without panicking.
    #[test]
    fn upnp_parsers_never_panic(b in proptest::collection::vec(any::<u8>(), 0..600), from_port: u16) {
        let base = Url::new("192.168.1.1:5000".parse().unwrap(), b"/rootDesc.xml").unwrap();
        let _ = upnp::ssdp_location(&b);
        let _ = upnp::parse_location(&b);
        let _ = upnp::http_response(&b);
        let _ = upnp::control_of(&b, &base);
        let _ = upnp::soap_result(&b);
        let _ = upnp::external_ip(&b);
        let _ = upnp::is_ssdp_answer(SocketAddr::new(Ipv4Addr::LOCALHOST.into(), from_port), &b);
    }

    /// The text parsers take any mix of the pieces they look for without panicking.
    #[test]
    fn upnp_parsers_never_panic_on_near_misses(parts in proptest::collection::vec(prop_oneof![
        Just(&b"HTTP/1.1 200 OK\r\n"[..]), Just(&b"\r\n"[..]), Just(&b"\r\n\r\n"[..]), Just(&b"LOCATION: http://"[..]),
        Just(&b"10.0.0.1:"[..]), Just(&b"<serviceType>"[..]), Just(&b"</serviceType>"[..]), Just(&b"<controlURL>"[..]),
        Just(&b"</controlURL>"[..]), Just(&b"</service>"[..]), Just(&b"urn:schemas-upnp-org:service:WANIPConnection:1"[..]),
        Just(&b"<errorCode>718</errorCode>"[..]), Just(&b"Content-Length: 3"[..]), Just(&b"<"[..]), Just(&b">"[..]),
        Just(&b"/"[..]), Just(&b":"[..]), Just(&b"9"[..]),
    ], 0..40)) {
        let b: Vec<u8> = parts.concat();
        let base = Url::new("192.168.1.1:5000".parse().unwrap(), b"/d").unwrap();
        let _ = upnp::ssdp_location(&b);
        let _ = upnp::http_response(&b);
        let _ = upnp::control_of(&b, &base);
        let _ = upnp::soap_result(&b);
    }
}

#[test]
fn an_ssdp_answer_names_its_description() {
    let a = b"HTTP/1.1 200 OK\r\nCACHE-CONTROL: max-age=120\r\nST: urn:schemas-upnp-org:device:InternetGatewayDevice:1\r\nLocation: http://192.168.1.1:5000/rootDesc.xml\r\n\r\n";
    let u = upnp::ssdp_location(a).unwrap();
    assert_eq!(u.addr, "192.168.1.1:5000".parse().unwrap());
    assert_eq!(u.path(), b"/rootDesc.xml");
    assert_eq!(
        upnp::parse_location(b"http://10.0.0.1").unwrap().addr,
        "10.0.0.1:80".parse().unwrap()
    );
    // one form only: no host name, no other scheme, no port 0, no IPv6
    for bad in [
        &b"http://router.lan/x"[..],
        b"https://10.0.0.1/x",
        b"http://10.0.0.1:0/x",
        b"http://[::1]/x",
        b"http://10.0.0.256/",
    ] {
        assert_eq!(upnp::parse_location(bad), None);
    }
    assert_eq!(
        upnp::ssdp_location(b"HTTP/1.1 404 Not Found\r\nLOCATION: http://10.0.0.1/\r\n\r\n"),
        None
    );
}

const DESC: &[u8] = br#"<?xml version="1.0"?><root xmlns="urn:schemas-upnp-org:device-1-0"><device><serviceList><service><serviceType>urn:schemas-upnp-org:service:Layer3Forwarding:1</serviceType><controlURL>/ctl/L3F</controlURL></service></serviceList><deviceList><device><deviceList><device><serviceList><service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><serviceId>urn:upnp-org:serviceId:WANIPConn1</serviceId><controlURL>/ctl/IPConn</controlURL></service></serviceList></device></deviceList></device></deviceList></device></root>"#;

#[test]
fn the_description_gives_the_control_url_of_the_mapping_service() {
    let base = Url::new("192.168.1.1:5000".parse().unwrap(), b"/rootDesc.xml").unwrap();
    let (ctl, svc) = upnp::control_of(DESC, &base).unwrap();
    assert_eq!(ctl.addr, base.addr);
    assert_eq!(ctl.path(), b"/ctl/IPConn");
    assert_eq!(upnp::SERVICES[svc], b"urn:schemas-upnp-org:service:WANIPConnection:1");
    // an absolute control URL names its own address
    let abs = br"<service><serviceType>urn:schemas-upnp-org:service:WANPPPConnection:1</serviceType><controlURL>http://192.168.1.1:49000/upnp/control/WANPPPConn1</controlURL></service>";
    let (ctl, svc) = upnp::control_of(abs, &base).unwrap();
    assert_eq!(
        (ctl.addr, ctl.path(), svc),
        (
            "192.168.1.1:49000".parse().unwrap(),
            &b"/upnp/control/WANPPPConn1"[..],
            2
        )
    );
    // no mapping service: nothing
    assert_eq!(upnp::control_of(&DESC[..200], &base), None);
}

#[test]
fn soap_calls_and_answers() {
    let ctl = Url::new("192.168.1.1:5000".parse().unwrap(), b"/ctl/IPConn").unwrap();
    let mut b = [0u8; upnp::MAX_REQUEST];
    let call = Call::Add {
        external: 4433,
        client: Ipv4Addr::new(192, 168, 1, 5),
        internal: 4433,
        lease: 7200,
    };
    let n = upnp::soap(&ctl, 1, &call, &mut b).unwrap();
    let r = std::str::from_utf8(&b[..n]).unwrap();
    assert!(r.starts_with("POST /ctl/IPConn HTTP/1.0\r\nHost: 192.168.1.1:5000\r\n"));
    assert!(r.contains("SOAPAction: \"urn:schemas-upnp-org:service:WANIPConnection:1#AddPortMapping\""));
    assert!(r.contains("<NewExternalPort>4433</NewExternalPort><NewProtocol>UDP</NewProtocol><NewInternalPort>4433</NewInternalPort><NewInternalClient>192.168.1.5</NewInternalClient>"));
    assert!(r.contains("<NewLeaseDuration>7200</NewLeaseDuration>"));
    let body_len = r.split("\r\n\r\n").nth(1).unwrap().len();
    assert!(r.contains(&format!("Content-Length: {body_len}\r\n")));
    let ok = b"HTTP/1.1 200 OK\r\nContent-Type: text/xml\r\n\r\n<s:Envelope><s:Body><u:GetExternalIPAddressResponse xmlns:u=\"x\"><NewExternalIPAddress>203.0.113.9</NewExternalIPAddress></u:GetExternalIPAddressResponse></s:Body></s:Envelope>";
    let Some(SoapResult::Ok(body)) = upnp::soap_result(ok) else {
        panic!("a 200 is success")
    };
    assert_eq!(upnp::external_ip(body), Some(Ipv4Addr::new(203, 0, 113, 9)));
    let fault = b"HTTP/1.1 500 Internal Server Error\r\n\r\n<s:Fault><detail><UPnPError><errorCode>718</errorCode></UPnPError></detail></s:Fault>";
    assert_eq!(upnp::soap_result(fault), Some(SoapResult::Fault(upnp::CONFLICT)));
    // a request that does not fit is not built
    assert_eq!(upnp::soap(&ctl, 1, &call, &mut b[..100]), None);
}
