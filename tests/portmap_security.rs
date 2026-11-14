//! What the port-mapping client takes from whom: HTTP goes only to the host that answered, an external address that
//! no peer could reach is not held, and an answer that is not the gateway's changes nothing.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::doc_markdown,
    clippy::panic,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::many_single_char_names
)]

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use vinc_portmap::client::PORT;
use vinc_portmap::lease::SEC;
use vinc_portmap::upnp;
use vinc_portmap::{Config, PortMap, natpmp, pcp};

const GW: Ipv4Addr = Ipv4Addr::new(192, 168, 1, 1);
const T0: u64 = 1_000 * SEC;
const NONCE: [u8; 12] = [5; 12];

fn local() -> SocketAddr {
    "192.168.1.5:4433".parse().unwrap()
}

fn client(gateway: Option<IpAddr>, local: SocketAddr) -> PortMap {
    PortMap::new(Config::new(gateway, local, NONCE), T0)
}

fn sent(pm: &mut PortMap) -> Vec<(SocketAddr, Vec<u8>)> {
    let mut out = Vec::new();
    let mut b = [0u8; vinc_portmap::MAX_DATAGRAM];
    while let Some((to, n)) = pm.poll_datagram(&mut b) {
        out.push((to, b[..n].to_vec()));
    }
    out
}

/// The next HTTP request: where it goes and its first line.
fn http(pm: &mut PortMap) -> Option<(SocketAddr, String)> {
    let mut b = [0u8; upnp::MAX_REQUEST];
    pm.poll_http(&mut b).map(|(to, n)| {
        (
            to,
            String::from_utf8_lossy(&b[..n])
                .lines()
                .next()
                .unwrap_or_default()
                .to_owned(),
        )
    })
}

fn answer(location: &str) -> Vec<u8> {
    format!("HTTP/1.1 200 OK\r\nLOCATION: {location}\r\n\r\n").into_bytes()
}

fn from(ip: [u8; 4]) -> SocketAddr {
    SocketAddr::new(Ipv4Addr::from(ip).into(), 1900)
}

#[test]
fn a_description_is_taken_only_from_the_host_that_answered() {
    let mut pm = client(None, local());
    assert_eq!(sent(&mut pm)[0].0, upnp::SSDP);
    // a LAN host answers and names another host: nothing is sent there
    let ans = answer("http://10.9.9.9:6379/x");
    assert!(pm.owns(from([192, 168, 1, 77]), &ans));
    pm.handle_datagram(T0, from([192, 168, 1, 77]), &ans);
    assert_eq!(
        http(&mut pm),
        None,
        "no HTTP request leaves for the host the answer named"
    );
    // the same host naming itself is followed
    let ans = answer("http://192.168.1.77:5000/d.xml");
    pm.handle_datagram(T0, from([192, 168, 1, 77]), &ans);
    assert_eq!(
        http(&mut pm),
        Some(("192.168.1.77:5000".parse().unwrap(), "GET /d.xml HTTP/1.0".to_owned()))
    );
}

#[test]
fn a_socket_on_a_public_address_does_not_search() {
    let public: SocketAddr = "203.0.113.50:4433".parse().unwrap();
    let mut pm = client(None, public);
    assert_eq!(sent(&mut pm), vec![], "no search leaves a public address");
    let far = from([198, 51, 100, 7]);
    let ans = answer("http://169.254.169.254:80/latest/meta-data/");
    assert!(!pm.owns(far, &ans), "an answer from the internet is not for the client");
    pm.handle_datagram(T0, far, &ans);
    assert_eq!(http(&mut pm), None);
    // a carrier-grade address is a network of its own and searches
    let shared: SocketAddr = "100.64.0.9:4433".parse().unwrap();
    assert_eq!(sent(&mut client(None, shared))[0].0, upnp::SSDP);
}

#[test]
fn with_a_gateway_a_description_on_another_host_is_not_followed() {
    let mut pm = client(Some(GW.into()), local());
    // silence through the PCP and NAT-PMP rounds brings the search
    let mut now = T0;
    while !sent(&mut pm).iter().any(|(to, _)| *to == upnp::SSDP) {
        now = pm.poll_timeout().unwrap();
        pm.handle_timeout(now);
    }
    let gw = SocketAddr::new(GW.into(), 1900);
    let ans = answer("http://10.0.0.99:22/");
    assert!(pm.owns(gw, &ans));
    pm.handle_datagram(now, gw, &ans);
    assert_eq!(
        http(&mut pm),
        None,
        "no HTTP request leaves for a host that is not the gateway"
    );
}

#[test]
fn a_control_url_on_another_host_is_not_used() {
    let mut pm = client(None, local());
    sent(&mut pm);
    pm.handle_datagram(T0, from([192, 168, 1, 1]), &answer("http://192.168.1.1:5000/d.xml"));
    assert!(http(&mut pm).is_some());
    let desc = b"HTTP/1.1 200 OK\r\n\r\n<service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>http://8.8.8.8:53/anything</controlURL></service>";
    pm.handle_http(T0, Some(desc));
    assert_eq!(
        http(&mut pm),
        None,
        "no SOAP request leaves for the host the description named"
    );
    // the description's own host, on another port, is fine
    let mut pm = client(None, local());
    sent(&mut pm);
    pm.handle_datagram(T0, from([192, 168, 1, 1]), &answer("http://192.168.1.1:5000/d.xml"));
    http(&mut pm).unwrap();
    let desc = b"HTTP/1.1 200 OK\r\n\r\n<service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>http://192.168.1.1:5555/ctl</controlURL></service>";
    pm.handle_http(T0, Some(desc));
    assert_eq!(
        http(&mut pm).map(|(to, _)| to),
        Some("192.168.1.1:5555".parse().unwrap())
    );
}

#[test]
fn no_http_goes_to_a_loopback_unspecified_multicast_or_link_local_host() {
    // an answer from such a host naming itself, and a description naming such a control host
    for ip in [[127, 0, 0, 1], [0, 0, 0, 0], [224, 0, 0, 251], [169, 254, 169, 254]] {
        let mut pm = client(None, local());
        sent(&mut pm);
        let who = from(ip);
        pm.handle_datagram(
            T0,
            who,
            &answer(&format!("http://{}.{}.{}.{}:80/d.xml", ip[0], ip[1], ip[2], ip[3])),
        );
        assert_eq!(http(&mut pm), None, "{who}: no HTTP request");
        let mut pm = client(None, local());
        sent(&mut pm);
        pm.handle_datagram(T0, from([192, 168, 1, 1]), &answer("http://192.168.1.1:5000/d.xml"));
        http(&mut pm).unwrap();
        let desc = format!(
            "HTTP/1.1 200 OK\r\n\r\n<service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>http://{}.{}.{}.{}/c</controlURL></service>",
            ip[0], ip[1], ip[2], ip[3]
        );
        pm.handle_http(T0, Some(desc.as_bytes()));
        assert_eq!(http(&mut pm), None, "{ip:?}: no SOAP request");
    }
}

fn gw() -> SocketAddr {
    SocketAddr::new(GW.into(), PORT)
}

fn pcp_grant(ip: IpAddr) -> Vec<u8> {
    let r = pcp::Response::Map {
        result: pcp::SUCCESS,
        lifetime: 7200,
        epoch: 1000,
        nonce: NONCE,
        protocol: pcp::UDP,
        internal_port: 4433,
        external_port: 4433,
        external_ip: ip,
    };
    let mut b = [0u8; 60];
    pcp::encode_response(&r, &mut b).unwrap();
    b.to_vec()
}

fn nat(r: natpmp::Response) -> Vec<u8> {
    let mut b = [0u8; 16];
    let n = natpmp::encode_response(&r, &mut b).unwrap();
    b[..n].to_vec()
}

/// External addresses no peer on the internet could send to.
const UNREACHABLE: [&str; 12] = [
    "100.64.0.7",
    "100.127.255.1",
    "10.1.1.1",
    "172.16.0.3",
    "192.168.9.9",
    "127.0.0.1",
    "169.254.1.1",
    "224.0.0.1",
    "0.0.0.0",
    "::",
    "fe80::1",
    "fd00::1",
];

#[test]
fn a_pcp_grant_of_an_address_no_peer_could_reach_is_not_held() {
    for ip in UNREACHABLE {
        let mut pm = client(Some(GW.into()), local());
        sent(&mut pm);
        pm.handle_datagram(T0, gw(), &pcp_grant(ip.parse().unwrap()));
        assert_eq!(pm.mapped(), None, "a grant of {ip} is held");
    }
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_grant("203.0.113.9".parse().unwrap()));
    assert_eq!(pm.mapped(), Some("203.0.113.9:4433".parse().unwrap()));
}

#[test]
fn a_nat_pmp_address_no_peer_could_reach_is_not_mapped() {
    for ip in [
        "100.64.0.7",
        "10.1.1.1",
        "127.0.0.1",
        "169.254.1.1",
        "224.0.0.1",
        "0.0.0.0",
    ] {
        let mut pm = client(Some(GW.into()), local());
        sent(&mut pm);
        pm.handle_datagram(
            T0,
            gw(),
            &nat(natpmp::Response::Error {
                opcode: 1,
                result: 1,
                epoch: 1,
            }),
        );
        sent(&mut pm);
        let ip: Ipv4Addr = ip.parse().unwrap();
        pm.handle_datagram(
            T0,
            gw(),
            &nat(natpmp::Response::Address {
                result: 0,
                epoch: 1,
                ip,
            }),
        );
        let asks_for_a_mapping = sent(&mut pm)
            .iter()
            .any(|(to, b)| *to == gw() && matches!(natpmp::decode_request(b), Ok(natpmp::Request::Map { .. })));
        assert!(!asks_for_a_mapping, "{ip}: a mapping was asked for");
        assert_eq!(pm.mapped(), None);
    }
}

#[test]
fn a_upnp_external_address_no_peer_could_reach_is_not_mapped() {
    for ip in [
        "100.64.0.7",
        "10.1.1.1",
        "127.0.0.1",
        "169.254.1.1",
        "224.0.0.1",
        "0.0.0.0",
    ] {
        let mut pm = client(None, local());
        sent(&mut pm);
        pm.handle_datagram(T0, from([192, 168, 1, 1]), &answer("http://192.168.1.1:5000/d.xml"));
        http(&mut pm).unwrap();
        let desc = b"HTTP/1.1 200 OK\r\n\r\n<service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>/ctl</controlURL></service>";
        pm.handle_http(T0, Some(desc));
        http(&mut pm).unwrap();
        let ext = format!("HTTP/1.1 200 OK\r\n\r\n<NewExternalIPAddress>{ip}</NewExternalIPAddress>");
        pm.handle_http(T0, Some(ext.as_bytes()));
        assert_eq!(http(&mut pm), None, "{ip}: AddPortMapping was asked");
        assert_eq!(pm.mapped(), None);
    }
}
