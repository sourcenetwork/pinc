//! The port-mapping client allocates nothing once it is made: asking for a PCP mapping and taking the grant, renewing
//! at half the lease, a gateway restart seen by its epoch, the fall back to NAT-PMP and to UPnP, and the release on
//! stop touch the heap zero times. The gateway's answers are encoded before the measured span.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::doc_markdown, clippy::panic)]

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use pinc_portmap::client::{FIRST_GAP, PORT};
use pinc_portmap::lease::SEC;
use pinc_portmap::upnp::{self, SSDP};
use pinc_portmap::{Config, PortMap, Proto, natpmp, pcp};
use pinc_tests::measure;

pinc_tests::install_counting_allocator!();

const GW: Ipv4Addr = Ipv4Addr::new(192, 168, 1, 1);
const EXT: Ipv4Addr = Ipv4Addr::new(203, 0, 113, 9);
const T0: u64 = 1_000 * SEC;
const NONCE: [u8; 12] = [5; 12];

fn gw() -> SocketAddr {
    SocketAddr::new(GW.into(), PORT)
}

fn client() -> PortMap {
    let local: SocketAddr = "192.168.1.5:4433".parse().unwrap();
    PortMap::new(Config::new(Some(IpAddr::V4(GW)), local, NONCE), T0)
}

/// Take every datagram the client wants sent, into a stack buffer; how many there were.
fn drain(pm: &mut PortMap) -> usize {
    let mut b = [0u8; pinc_portmap::MAX_DATAGRAM];
    let mut n = 0;
    while pm.poll_datagram(&mut b).is_some() {
        n += 1;
    }
    n
}

fn pcp_map(result: u8, epoch: u32, port: u16, lifetime: u32) -> [u8; 60] {
    let r = pcp::Response::Map {
        result,
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
    b
}

fn nat(r: &natpmp::Response) -> ([u8; 16], usize) {
    let mut b = [0u8; 16];
    let n = natpmp::encode_response(r, &mut b).unwrap();
    (b, n)
}

#[test]
fn the_pcp_path_allocates_nothing() {
    let (grant, again, restarted) = (
        pcp_map(0, 1, 4433, 7200),
        pcp_map(0, 1, 4433, 7200),
        pcp_map(2, 2, 4433, 0),
    );
    let mut pm = client();
    let st = measure(|| {
        assert_eq!(drain(&mut pm), 1);
        assert!(pm.owns(gw(), &grant));
        pm.handle_datagram(T0, gw(), &grant);
        assert_eq!(pm.protocol(), Some(Proto::Pcp));
        // renew at half the lease, several times, each grant starting the next lease
        for _ in 0..4 {
            let t = pm.poll_timeout().unwrap();
            pm.handle_timeout(t);
            assert_eq!(drain(&mut pm), 1);
            pm.handle_datagram(t, gw(), &again);
        }
        assert!(pm.mapped().is_some());
        // a gateway restart: the renewal is refused and its epoch went back
        let t = pm.poll_timeout().unwrap();
        pm.handle_timeout(t);
        assert_eq!(drain(&mut pm), 1);
        pm.handle_datagram(t, gw(), &restarted);
        assert_eq!(pm.mapped(), None);
        assert!(drain(&mut pm) > 0);
    });
    assert_eq!(st.count(), 0, "{st:?}");
}

#[test]
fn the_nat_pmp_fallback_and_the_stop_allocate_nothing() {
    let unsupported = nat(&natpmp::Response::Error {
        opcode: 1,
        result: 1,
        epoch: 50,
    });
    let address = nat(&natpmp::Response::Address {
        result: 0,
        epoch: 50,
        ip: EXT,
    });
    let map = nat(&natpmp::Response::Map {
        result: 0,
        epoch: 50,
        internal_port: 4433,
        external_port: 4433,
        lifetime: 7200,
    });
    let moved_back = nat(&natpmp::Response::Address {
        result: 0,
        epoch: 3,
        ip: EXT,
    });
    let mut pm = client();
    let st = measure(|| {
        drain(&mut pm);
        pm.handle_datagram(T0, gw(), &unsupported.0[..unsupported.1]);
        assert_eq!(drain(&mut pm), 1);
        pm.handle_datagram(T0, gw(), &address.0[..address.1]);
        assert_eq!(drain(&mut pm), 1);
        pm.handle_datagram(T0, gw(), &map.0[..map.1]);
        assert_eq!(pm.protocol(), Some(Proto::NatPmp));
        // the renewal shows a restart by the epoch going back
        pm.handle_timeout(T0 + 3600 * SEC);
        assert_eq!(drain(&mut pm), 1);
        pm.handle_datagram(T0 + 3600 * SEC, gw(), &moved_back.0[..moved_back.1]);
        assert_eq!(pm.mapped(), None);
        drain(&mut pm);
        // asked again and granted, then stopped: the delete goes out
        pm.handle_datagram(T0 + 3601 * SEC, gw(), &map.0[..map.1]);
        pm.stop(T0 + 3602 * SEC);
        drain(&mut pm);
        assert!(pm.stopped());
    });
    assert_eq!(st.count(), 0, "{st:?}");
}

const SSDP_ANSWER: &[u8] = b"HTTP/1.1 200 OK\r\nST: urn:schemas-upnp-org:device:InternetGatewayDevice:1\r\nLOCATION: http://192.168.1.1:5000/rootDesc.xml\r\n\r\n";
const DESC: &[u8] = b"HTTP/1.1 200 OK\r\n\r\n<root><device><serviceList><service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>/ctl/IPConn</controlURL></service></serviceList></device></root>";
const EXTIP: &[u8] = b"HTTP/1.1 200 OK\r\n\r\n<u:GetExternalIPAddressResponse><NewExternalIPAddress>203.0.113.9</NewExternalIPAddress></u:GetExternalIPAddressResponse>";
const OK: &[u8] = b"HTTP/1.1 200 OK\r\n\r\n<u:AddPortMappingResponse/>";

#[test]
fn the_upnp_path_allocates_nothing() {
    let mut pm = client();
    let st = measure(|| {
        // three PCP tries, three NAT-PMP tries, then the SSDP search
        let mut t = T0;
        let mut searched = false;
        let mut b = [0u8; pinc_portmap::MAX_DATAGRAM];
        while !searched {
            while let Some((to, _)) = pm.poll_datagram(&mut b) {
                searched |= to == SSDP;
            }
            if !searched {
                t = pm.poll_timeout().unwrap();
                pm.handle_timeout(t);
            }
        }
        assert_eq!(t, T0 + 2 * 7 * FIRST_GAP);
        pm.handle_datagram(t, SocketAddr::new(GW.into(), 1900), SSDP_ANSWER);
        let mut h = [0u8; upnp::MAX_REQUEST];
        for answer in [DESC, EXTIP, OK] {
            assert!(pm.poll_http(&mut h).is_some());
            pm.handle_http(t, Some(answer));
        }
        assert_eq!(pm.protocol(), Some(Proto::Upnp));
        // stop: the delete goes out, its answer ends the client
        pm.stop(t + SEC);
        assert!(pm.poll_http(&mut h).is_some());
        pm.handle_http(t + SEC, Some(OK));
        assert!(pm.stopped());
    });
    assert_eq!(st.count(), 0, "{st:?}");
}
