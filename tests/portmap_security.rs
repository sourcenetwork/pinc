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

use pinc_portmap::client::PORT;
use pinc_portmap::lease::SEC;
use pinc_portmap::upnp;
use pinc_portmap::{Config, PortMap, natpmp, pcp};

#[path = "portmap_security/counted.rs"]
mod counted;

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
    let mut b = [0u8; pinc_portmap::MAX_DATAGRAM];
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

const OK: &[u8] = b"HTTP/1.1 200 OK\r\n\r\n<u:AddPortMappingResponse/>";

fn pcp_map(nonce: [u8; 12], result: u8, epoch: u32, lifetime: u32) -> Vec<u8> {
    let r = pcp::Response::Map {
        result,
        lifetime,
        epoch,
        nonce,
        protocol: pcp::UDP,
        internal_port: 4433,
        external_port: 4433,
        external_ip: "203.0.113.9".parse().unwrap(),
    };
    let mut b = [0u8; 60];
    pcp::encode_response(&r, &mut b).unwrap();
    b.to_vec()
}

fn pcp_header(opcode: u8, result: u8, epoch: u32) -> Vec<u8> {
    let mut b = [0u8; 24];
    let n = pcp::encode_response(
        &pcp::Response::Header {
            opcode,
            result,
            lifetime: 30,
            epoch,
        },
        &mut b,
    )
    .unwrap();
    b[..n].to_vec()
}

#[test]
fn a_pcp_error_header_while_a_mapping_is_held_changes_nothing() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_map(NONCE, pcp::SUCCESS, 1000, 7200));
    let held = pm.mapped();
    assert!(held.is_some());
    // a header-form MAP error (no nonce in this form) whose epoch went back: it answers no request
    pm.handle_datagram(T0 + 10 * SEC, gw(), &pcp_header(pcp::OP_MAP, 8, 3));
    assert_eq!(pm.mapped(), held, "an answer to no request dropped the mapping");
    assert_eq!(pm.poll_timeout(), Some(T0 + 3600 * SEC), "the renewal is still armed");
    assert_eq!(sent(&mut pm), vec![]);
}

/// The wait between an announce and the renewal it brings forward: 0 to 5 seconds drawn from the first byte of the
/// nonce (5): 5 * 5 s / 256.
const ANNOUNCE_DELAY: u64 = 5 * 5 * SEC / 256;

#[test]
fn an_announce_keeps_the_mapping_and_the_renewal_answer_decides() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_map(NONCE, pcp::SUCCESS, 1000, 7200));
    let held = pm.mapped();
    let at = T0 + 10 * SEC;
    pm.handle_datagram(at, gw(), &pcp_header(pcp::OP_ANNOUNCE, 0, 3));
    assert_eq!(pm.mapped(), held, "an announce dropped the mapping");
    assert_eq!(
        pm.poll_timeout(),
        Some(at + ANNOUNCE_DELAY),
        "the renewal is brought forward by the announce wait"
    );
    pm.handle_timeout(at + ANNOUNCE_DELAY);
    assert_eq!(sent(&mut pm).len(), 1, "the renewal is asked for");
    // the renewal is refused with an epoch that went back: the gateway lost its mappings
    pm.handle_datagram(at + ANNOUNCE_DELAY, gw(), &pcp_map(NONCE, 2, 3, 7200));
    assert_eq!(pm.mapped(), None, "the mapping the gateway lost is still held");
    assert!(
        pm.poll_timeout().is_some(),
        "a client that holds nothing still has a timer"
    );
    assert!(!sent(&mut pm).is_empty(), "the mapping is asked for again");
}

/// A flood of spoofed announces, one per millisecond for `secs` seconds, against a gateway that answers every request
/// `rtt_ms` later with an epoch that matches the clocks: how many renewal requests were asked, and whether the mapping
/// ever changed. The run goes half a second past the flood.
fn flood(rtt_ms: u64, secs: u64) -> (usize, bool) {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_map(NONCE, pcp::SUCCESS, 1000, 7200));
    let held = pm.mapped();
    let mut due: Vec<u64> = Vec::new();
    let (mut asked, mut changed) = (0, false);
    for ms in 0..=secs * 1000 + 500 {
        let now = T0 + 10 * SEC + ms * SEC / 1000;
        if ms < secs * 1000 {
            pm.handle_datagram(now, gw(), &pcp_header(pcp::OP_ANNOUNCE, 0, 0));
        }
        if pm.poll_timeout().is_some_and(|t| t <= now) {
            pm.handle_timeout(now);
        }
        for (_, b) in sent(&mut pm) {
            if pcp::decode_request(&b).is_ok_and(|r| r.lifetime > 0) {
                asked += 1;
                due.push(now + rtt_ms * SEC / 1000);
            }
        }
        while due.first().is_some_and(|t| *t <= now) {
            due.remove(0);
            pm.handle_datagram(
                now,
                gw(),
                &pcp_map(
                    NONCE,
                    pcp::SUCCESS,
                    1000 + u32::try_from((now - T0) / SEC).unwrap(),
                    7200,
                ),
            );
        }
        changed |= pm.mapped() != held;
    }
    (asked, changed)
}

#[test]
fn a_flood_of_spoofed_announces_costs_at_most_one_renewal_per_floor() {
    // the announce-brought renewals of one mapping are at least ANNOUNCE_FLOOR (10 s) apart, so in a flood of 10 s and
    // the half second after it there are at most 10 / 10 + 1 = 2
    for rtt in [1, 20] {
        let (asked, changed) = flood(rtt, 10);
        assert!(!changed, "a flood changed the mapping (round trip {rtt} ms)");
        assert!(
            (1..=2).contains(&asked),
            "{asked} renewals for a 10 s flood with a {rtt} ms round trip, at most 2 are allowed"
        );
    }
}

#[test]
fn a_flood_of_spoofed_announces_costs_a_upnp_mapping_at_most_four_exchanges() {
    let mut pm = client(Some(GW.into()), local());
    let mut now = T0;
    while !sent(&mut pm).iter().any(|(to, _)| *to == upnp::SSDP) {
        now = pm.poll_timeout().unwrap();
        pm.handle_timeout(now);
    }
    pm.handle_datagram(now, from([192, 168, 1, 1]), &answer("http://192.168.1.1:5000/d.xml"));
    let desc = b"HTTP/1.1 200 OK\r\n\r\n<service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>/ctl</controlURL></service>";
    let ip = b"HTTP/1.1 200 OK\r\n\r\n<NewExternalIPAddress>203.0.113.9</NewExternalIPAddress>";
    for a in [desc.as_slice(), ip, OK] {
        http(&mut pm).unwrap();
        pm.handle_http(now, Some(a));
    }
    let held = pm.mapped();
    assert!(held.is_some());
    // 100 spoofed announces, one every 100 ms for 10 s; every HTTP exchange the client asks for is answered at once
    let mut exchanges = 0;
    let start = now;
    for i in 0..=105u64 {
        let t = start + i * SEC / 10;
        if i < 100 {
            pm.handle_datagram(t, gw(), &pcp_header(pcp::OP_ANNOUNCE, 0, 0));
        }
        if pm.poll_timeout().is_some_and(|d| d <= t) {
            pm.handle_timeout(t);
        }
        while let Some(req) = http_text(&mut pm) {
            exchanges += 1;
            let a: &[u8] = if req.contains("GetExternalIPAddress") { ip } else { OK };
            pm.handle_http(t, Some(a));
        }
        assert_eq!(pm.mapped(), held, "announce {i} changed the mapping");
    }
    // at most 2 brought-forward renewals in 10 s, each an address read and an AddPortMapping
    assert!(exchanges <= 4, "{exchanges} HTTP exchanges for 100 spoofed announces");
}

#[test]
fn two_restarts_closer_than_the_floor_are_found_a_floor_after_the_first_renewal() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_map(NONCE, pcp::SUCCESS, 1000, 7200));
    let t1 = T0 + 10 * SEC;
    // restart one is announced: the renewal is asked for after the announce wait, and its answer shows the restart
    pm.handle_datagram(t1, gw(), &pcp_header(pcp::OP_ANNOUNCE, 0, 2));
    let first = t1 + ANNOUNCE_DELAY;
    pm.handle_timeout(first);
    assert_eq!(sent(&mut pm).len(), 1, "the first renewal");
    pm.handle_datagram(first, gw(), &pcp_map(NONCE, pcp::SUCCESS, 2, 7200));
    // restart two is announced 5 ms later, inside the floor: its renewal waits for the floor and then goes
    pm.handle_datagram(first + SEC / 200, gw(), &pcp_header(pcp::OP_ANNOUNCE, 0, 1));
    let second = first + 10 * SEC;
    assert_eq!(
        pm.poll_timeout(),
        Some(second),
        "the second renewal is a floor after the first"
    );
    pm.handle_timeout(second - 1);
    assert!(sent(&mut pm).is_empty(), "the floor was not kept");
    pm.handle_timeout(second);
    assert_eq!(sent(&mut pm).len(), 1, "the second renewal");
    // its answer shows the second restart (the epoch went back again) and the gateway refuses
    pm.handle_datagram(second, gw(), &pcp_map(NONCE, 2, 1, 7200));
    assert_eq!(pm.mapped(), None, "the second restart was not found");
    assert!(!sent(&mut pm).is_empty(), "the mapping is asked for again");
}

#[test]
fn an_announce_kept_across_a_failed_renewal_brings_no_renewal_inside_the_floor() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_map(NONCE, pcp::SUCCESS, 1000, 7200));
    // the scheduled renewal goes out half way; an announce arrives while it is in flight and is kept for its answer
    let half = T0 + 3600 * SEC;
    pm.handle_timeout(half);
    assert_eq!(sent(&mut pm).len(), 1, "the scheduled renewal");
    pm.handle_datagram(half + SEC / 1000, gw(), &pcp_header(pcp::OP_ANNOUNCE, 0, 4600));
    // no answer comes: the renewal's tries run out and the mapping stays held
    while let Some(t) = pm.poll_timeout().filter(|t| *t < half + 4 * SEC) {
        pm.handle_timeout(t);
        sent(&mut pm);
    }
    assert!(pm.mapped().is_some(), "a renewal that failed dropped the mapping");
    // a second announce, now with the mapping held and no request in flight, brings a renewal forward
    let t2 = half + 5 * SEC;
    pm.handle_datagram(t2, gw(), &pcp_header(pcp::OP_ANNOUNCE, 0, 4605));
    pm.handle_timeout(t2 + ANNOUNCE_DELAY);
    assert_eq!(
        sent(&mut pm).len(),
        1,
        "the renewal the second announce brought forward"
    );
    // its grant arrives; the announce kept from before must not start another renewal inside the floor
    pm.handle_datagram(
        t2 + ANNOUNCE_DELAY + SEC / 1000,
        gw(),
        &pcp_map(NONCE, pcp::SUCCESS, 4605, 7200),
    );
    let floor = t2 + 10 * SEC;
    assert!(
        pm.poll_timeout().is_none_or(|t| t >= floor),
        "the announce kept from before brings a renewal {:?} inside the floor that ends at {floor}",
        pm.poll_timeout()
    );
    pm.handle_timeout(floor - 1);
    assert!(sent(&mut pm).is_empty(), "a renewal went out inside the floor");
    // it is not lost either: its renewal goes once the floor has passed
    pm.handle_timeout(floor + ANNOUNCE_DELAY);
    assert_eq!(sent(&mut pm).len(), 1, "the kept announce's renewal, a floor later");
}

#[test]
fn an_announce_outside_a_held_mapping_is_dropped_and_counted() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_header(pcp::OP_ANNOUNCE, 0, 5));
    assert_eq!(pm.stats().unexpected, 1);
    assert_eq!(pm.mapped(), None);
    assert!(sent(&mut pm).is_empty(), "an announce changed what the client asks");
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}

/// Random events against the client, PCP header answers among them. After every event and a drain of what it sends,
/// a client that is not stopped has a timer or an HTTP request to make (or it never acts again), and one that
/// stopped holds nothing.
fn never_wedged(seed: u64) {
    let mut r = Rng(seed.wrapping_mul(0x2545_f491_4f6c_dd1d) | 1);
    let gateway = if r.below(5) == 0 { None } else { Some(IpAddr::V4(GW)) };
    let mut cfg = Config::new(gateway, local(), NONCE);
    cfg.lifetime = [120, 7200][r.below(2) as usize];
    let mut pm = PortMap::new(cfg, T0);
    let mut now = T0;
    let mut epoch: u32 = 100;
    let mut trace = Vec::new();
    for _ in 0..150 {
        match r.below(12) {
            0..=2 => {
                now = pm.poll_timeout().map_or(now + SEC, |t| t.max(now));
                pm.handle_timeout(now);
                trace.push(format!("timeout@{}", (now - T0) / SEC));
            }
            3 => {
                now += r.below(4000) * SEC;
                pm.handle_timeout(now);
                trace.push(format!("jump@{}", (now - T0) / SEC));
            }
            4 | 5 => {
                epoch = epoch.wrapping_add(r.below(50) as u32);
                let e = if r.below(8) == 0 { r.below(5) as u32 } else { epoch };
                let nonce = if r.below(5) == 0 { [9; 12] } else { NONCE };
                let res = [0, 0, 1, 2, 8][r.below(5) as usize];
                pm.handle_datagram(
                    now,
                    gw(),
                    &pcp_map(nonce, res, e, [0, 1, 120, 7200][r.below(4) as usize]),
                );
                trace.push(format!("pcp-map res={res} e={e}"));
            }
            6 => {
                let e = if r.below(3) == 0 { r.below(5) as u32 } else { epoch };
                let op = r.below(2) as u8;
                let res = if op == 0 { 0 } else { [1, 2, 8][r.below(3) as usize] };
                pm.handle_datagram(now, gw(), &pcp_header(op, res, e));
                trace.push(format!("pcp-header op={op} res={res} e={e}"));
            }
            7 => {
                let e = if r.below(4) == 0 { r.below(5) as u32 } else { epoch };
                let m = match r.below(3) {
                    0 => natpmp::Response::Address {
                        result: 0,
                        epoch: e,
                        ip: "203.0.113.9".parse().unwrap(),
                    },
                    1 => natpmp::Response::Map {
                        result: 0,
                        epoch: e,
                        internal_port: 4433,
                        external_port: 4433,
                        lifetime: 120,
                    },
                    _ => natpmp::Response::Error {
                        opcode: r.below(2) as u8,
                        result: 1 + r.below(3) as u16,
                        epoch: e,
                    },
                };
                pm.handle_datagram(now, gw(), &nat(m));
                trace.push(format!("natpmp {m:?}"));
            }
            8 => {
                pm.handle_datagram(now, from([192, 168, 1, 1]), &answer("http://192.168.1.1:5000/d.xml"));
                trace.push("ssdp".into());
            }
            9 => {
                if http(&mut pm).is_some() {
                    let desc: &[u8] = b"HTTP/1.1 200 OK\r\n\r\n<service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>/c</controlURL></service>";
                    let answers: [Option<&[u8]>; 6] = [
                        Some(desc),
                        Some(b"HTTP/1.1 200 OK\r\n\r\n<NewExternalIPAddress>203.0.113.9</NewExternalIPAddress>"),
                        Some(OK),
                        Some(b"HTTP/1.1 500 E\r\n\r\n<errorCode>718</errorCode>"),
                        Some(b"HTTP/1.1 500 E\r\n\r\n<errorCode>725</errorCode>"),
                        None,
                    ];
                    pm.handle_http(now, answers[r.below(6) as usize]);
                    trace.push("http".into());
                }
            }
            10 => {
                let junk: Vec<u8> = (0..r.below(60)).map(|_| r.next().to_le_bytes()[0]).collect();
                pm.handle_datagram(now, gw(), &junk);
                trace.push("junk".into());
            }
            _ => {
                if r.below(10) == 0 {
                    pm.stop(now);
                    trace.push("stop".into());
                }
            }
        }
        sent(&mut pm);
        if pm.stopped() {
            assert_eq!(pm.mapped(), None, "a stopped client holds a mapping: {trace:?}");
            return;
        }
        let mut b = [0u8; upnp::MAX_REQUEST];
        assert!(
            pm.poll_timeout().is_some() || pm.clone().poll_http(&mut b).is_some(),
            "wedged: no timer, not stopped, nothing to send after {trace:?}"
        );
    }
}

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(2000))]

    #[test]
    fn the_client_always_has_a_timer_or_an_exchange_in_flight(seed in proptest::prelude::any::<u64>()) {
        never_wedged(seed);
    }
}

/// The next HTTP request in full.
fn http_text(pm: &mut PortMap) -> Option<String> {
    let mut b = [0u8; upnp::MAX_REQUEST];
    pm.poll_http(&mut b)
        .map(|(_, n)| String::from_utf8_lossy(&b[..n]).into_owned())
}

/// A client that holds a UPnP mapping of external address `ext`, its grant at `T0`.
fn upnp_held(ext: &str) -> PortMap {
    let mut pm = client(None, local());
    sent(&mut pm);
    pm.handle_datagram(T0, from([192, 168, 1, 1]), &answer("http://192.168.1.1:5000/d.xml"));
    let desc = b"HTTP/1.1 200 OK\r\n\r\n<service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>/ctl</controlURL></service>";
    let ip = format!("HTTP/1.1 200 OK\r\n\r\n<NewExternalIPAddress>{ext}</NewExternalIPAddress>");
    for a in [desc.as_slice(), ip.as_bytes(), OK] {
        http(&mut pm).unwrap();
        pm.handle_http(T0, Some(a));
    }
    assert_eq!(pm.mapped(), Some(format!("{ext}:4433").parse().unwrap()));
    pm
}

#[test]
fn a_upnp_renewal_reads_the_external_address_again() {
    let mut pm = upnp_held("203.0.113.9");
    pm.handle_timeout(T0 + 3600 * SEC);
    let first = http_text(&mut pm).unwrap();
    assert!(
        first.contains("#GetExternalIPAddress"),
        "the renewal did not ask for the address first: {first}"
    );
    pm.handle_http(
        T0 + 3600 * SEC,
        Some(b"HTTP/1.1 200 OK\r\n\r\n<NewExternalIPAddress>198.51.100.77</NewExternalIPAddress>"),
    );
    assert!(http_text(&mut pm).unwrap().contains("#AddPortMapping"));
    pm.handle_http(T0 + 3600 * SEC, Some(OK));
    assert_eq!(
        pm.mapped(),
        Some("198.51.100.77:4433".parse().unwrap()),
        "the mapping still names the old address"
    );
}

#[test]
fn a_restart_drops_the_mapping_releases_it_and_asks_again() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_map(NONCE, pcp::SUCCESS, 1000, 7200));
    assert!(pm.mapped().is_some());
    pm.restart(T0 + 10 * SEC);
    assert_eq!(pm.mapped(), None, "the old mapping is still held");
    let out = sent(&mut pm);
    let lifetimes: Vec<u32> = out
        .iter()
        .map(|(_, b)| pcp::decode_request(b).unwrap().lifetime)
        .collect();
    assert_eq!(
        lifetimes,
        [0, 7200],
        "the old mapping is released, then a new one asked for"
    );
    assert!(out.iter().all(|(to, _)| *to == gw()));
    assert!(pm.poll_timeout().is_some());
}

#[test]
fn a_restart_of_a_upnp_mapping_searches_again_and_a_stopped_client_stays_stopped() {
    let mut pm = upnp_held("203.0.113.9");
    pm.restart(T0 + 10 * SEC);
    assert_eq!(pm.mapped(), None);
    assert_eq!(sent(&mut pm).first().map(|(to, _)| *to), Some(upnp::SSDP));
    assert_eq!(http(&mut pm), None);
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.stop(T0 + SEC);
    sent(&mut pm);
    pm.restart(T0 + 2 * SEC);
    assert!(pm.stopped());
    assert_eq!(sent(&mut pm), vec![]);
    assert_eq!(pm.poll_timeout(), None);
}

#[test]
fn a_grant_longer_than_asked_is_scheduled_as_asked() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_map(NONCE, pcp::SUCCESS, 1000, 86_400));
    assert_eq!(
        pm.poll_timeout(),
        Some(T0 + 3600 * SEC),
        "a day-long grant renews at half the lifetime asked (7200 s), not at 12 hours"
    );
    // a shorter grant is kept as granted
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_map(NONCE, pcp::SUCCESS, 1000, 120));
    assert_eq!(pm.poll_timeout(), Some(T0 + 60 * SEC));
}

#[test]
fn an_ipv4_mapped_gateway_is_the_ipv4_address_it_maps() {
    let mapped = IpAddr::V6(GW.to_ipv6_mapped());
    let mut pm = client(Some(mapped), local());
    let out = sent(&mut pm);
    assert_eq!(out[0].0, gw(), "requests go to the IPv4 address");
    assert!(pm.owns(gw(), &[2; 60]), "its answers are the gateway's");
    let v6_source = SocketAddr::new(mapped, PORT);
    assert!(pm.owns(v6_source, &[2; 60]), "a mapped source is the same address");
}

#[test]
fn stop_releases_a_pcp_request_in_flight() {
    let mut pm = client(Some(GW.into()), local());
    let asked = pcp::decode_request(&sent(&mut pm)[0].1).unwrap();
    pm.stop(T0 + SEC / 10);
    let out = sent(&mut pm);
    assert_eq!(out.len(), 1, "the request may have made a mapping: it is released");
    let release = pcp::decode_request(&out[0].1).unwrap();
    assert_eq!((out[0].0, release.lifetime, release.nonce), (gw(), 0, asked.nonce));
    assert!(pm.stopped());
}

#[test]
fn stop_releases_a_nat_pmp_request_in_flight() {
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
    pm.handle_datagram(
        T0,
        gw(),
        &nat(natpmp::Response::Address {
            result: 0,
            epoch: 1,
            ip: "203.0.113.9".parse().unwrap(),
        }),
    );
    assert!(!sent(&mut pm).is_empty(), "the mapping request is out");
    pm.stop(T0 + SEC / 10);
    let out = sent(&mut pm);
    assert_eq!(out.len(), 1);
    assert_eq!(
        natpmp::decode_request(&out[0].1),
        Ok(natpmp::Request::Map {
            internal_port: 4433,
            external_port: 0,
            lifetime: 0
        })
    );
}

#[test]
fn stop_deletes_a_upnp_mapping_whose_request_is_in_flight() {
    let mut pm = client(None, local());
    sent(&mut pm);
    pm.handle_datagram(T0, from([192, 168, 1, 1]), &answer("http://192.168.1.1:5000/d.xml"));
    let desc = b"HTTP/1.1 200 OK\r\n\r\n<service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>/ctl</controlURL></service>";
    let ip = b"HTTP/1.1 200 OK\r\n\r\n<NewExternalIPAddress>203.0.113.9</NewExternalIPAddress>";
    for a in [desc.as_slice(), ip] {
        http(&mut pm).unwrap();
        pm.handle_http(T0, Some(a));
    }
    assert!(
        http_text(&mut pm).unwrap().contains("#AddPortMapping"),
        "the AddPortMapping is out"
    );
    pm.stop(T0 + SEC / 10);
    let del = http_text(&mut pm).expect("the mapping the gateway may have made is deleted");
    assert!(del.contains("#DeletePortMapping") && del.contains("<NewExternalPort>4433<"));
}
