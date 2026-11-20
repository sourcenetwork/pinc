//! What the client counts: every datagram and answer it drops, every request that runs out, and the releases a
//! restart and a stop leave.

use super::*;

fn only(f: impl FnOnce(&mut pinc_portmap::Stats)) -> pinc_portmap::Stats {
    let mut s = pinc_portmap::Stats::default();
    f(&mut s);
    s
}

#[test]
fn a_datagram_from_another_source_is_counted() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(
        T0,
        "192.168.1.99:5351".parse().unwrap(),
        &pcp_map(NONCE, pcp::SUCCESS, 1, 7200),
    );
    assert_eq!(pm.stats(), only(|s| s.wrong_source = 1));
    assert_eq!(pm.mapped(), None);
    // a search answer that names another host
    let mut pm = client(None, local());
    sent(&mut pm);
    pm.handle_datagram(T0, from([192, 168, 1, 77]), &answer("http://10.9.9.9:6379/x"));
    assert_eq!(pm.stats(), only(|s| s.wrong_source = 1));
}

#[test]
fn a_pcp_answer_with_another_nonce_is_counted() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_map([9; 12], pcp::SUCCESS, 1, 7200));
    assert_eq!(pm.stats(), only(|s| s.wrong_nonce = 1));
    assert_eq!(pm.mapped(), None);
}

#[test]
fn an_answer_that_does_not_decode_or_does_not_match_the_request_is_counted() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &[2, 0, 0]);
    assert_eq!(pm.stats(), only(|s| s.unexpected = 1));
    pm.handle_datagram(
        T0,
        gw(),
        &nat(natpmp::Response::Address {
            result: 0,
            epoch: 1,
            ip: "203.0.113.9".parse().unwrap(),
        }),
    );
    assert_eq!(
        pm.stats(),
        only(|s| s.unexpected = 2),
        "a NAT-PMP address while PCP is asked"
    );
}

#[test]
fn a_refused_address_is_counted() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &pcp_grant("10.1.1.1".parse().unwrap()));
    assert_eq!(pm.stats().refused_address, 1);
    assert_eq!(pm.mapped(), None);
}

#[test]
fn a_request_that_runs_out_of_tries_is_counted_as_a_timeout() {
    let mut pm = client(Some(GW.into()), local());
    let mut n = 0;
    while pm.stats().timeouts == 0 && n < 20 {
        sent(&mut pm);
        let t = pm.poll_timeout().unwrap();
        pm.handle_timeout(t);
        n += 1;
    }
    assert_eq!(pm.stats(), only(|s| s.timeouts = 1), "the PCP tries ran out once");
}

#[test]
fn a_failed_http_exchange_is_counted() {
    let mut pm = client(None, local());
    sent(&mut pm);
    pm.handle_datagram(T0, from([192, 168, 1, 1]), &answer("http://192.168.1.1:5000/d.xml"));
    http(&mut pm).unwrap();
    pm.handle_http(T0, None);
    assert_eq!(pm.stats(), only(|s| s.http_failures = 1));
}

#[test]
fn with_no_gateway_a_search_answer_is_taken_only_from_a_private_address() {
    let mut pm = client(None, local());
    sent(&mut pm);
    let far = from([198, 51, 100, 7]);
    let ans = answer("http://198.51.100.7:5000/d.xml");
    assert!(!pm.owns(far, &ans), "an answer from a public host is for the client");
    pm.handle_datagram(T0, far, &ans);
    assert_eq!(http(&mut pm), None, "an HTTP request left for a public host");
    // a carrier-grade address is a private network
    let shared = from([100, 64, 0, 9]);
    assert!(pm.owns(shared, &answer("http://100.64.0.9:5000/d.xml")));
}

#[test]
fn with_a_gateway_a_search_answer_is_taken_only_from_it() {
    let mut pm = client(Some(GW.into()), local());
    while !sent(&mut pm).iter().any(|(to, _)| *to == upnp::SSDP) {
        let t = pm.poll_timeout().unwrap();
        pm.handle_timeout(t);
    }
    assert!(!pm.owns(from([192, 168, 1, 77]), &answer("http://192.168.1.77:5000/d.xml")));
    assert!(pm.owns(from([192, 168, 1, 1]), &answer("http://192.168.1.1:5000/d.xml")));
}

#[test]
fn a_restart_then_a_stop_keeps_both_releases() {
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
    let ext = "203.0.113.9".parse().unwrap();
    pm.handle_datagram(
        T0,
        gw(),
        &nat(natpmp::Response::Address {
            result: 0,
            epoch: 1,
            ip: ext,
        }),
    );
    sent(&mut pm);
    pm.handle_datagram(
        T0,
        gw(),
        &nat(natpmp::Response::Map {
            result: 0,
            epoch: 1,
            internal_port: 4433,
            external_port: 4433,
            lifetime: 7200,
        }),
    );
    assert!(pm.mapped().is_some());
    pm.restart(T0 + SEC);
    pm.stop(T0 + 2 * SEC);
    let out = sent(&mut pm);
    let nat_release = out.iter().any(|(_, b)| {
        natpmp::decode_request(b)
            == Ok(natpmp::Request::Map {
                internal_port: 4433,
                external_port: 0,
                lifetime: 0,
            })
    });
    let pcp_release = out
        .iter()
        .any(|(_, b)| pcp::decode_request(b).is_ok_and(|r| r.lifetime == 0));
    assert!(nat_release, "the NAT-PMP mapping's release was lost: {out:?}");
    assert!(pcp_release, "the request in flight was not released");
}

#[test]
fn a_search_answer_without_a_location_is_counted() {
    let mut pm = client(None, local());
    sent(&mut pm);
    pm.handle_datagram(T0, from([192, 168, 1, 77]), b"HTTP/1.1 200 OK\r\n\r\n");
    assert_eq!(pm.stats(), only(|s| s.unexpected = 1));
}

#[test]
fn a_datagram_after_stop_is_counted() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.stop(T0);
    pm.handle_datagram(T0, gw(), &[2, 0, 0]);
    assert_eq!(pm.stats(), only(|s| s.unexpected = 1));
}

#[test]
fn an_empty_datagram_from_the_gateway_is_counted() {
    let mut pm = client(Some(GW.into()), local());
    sent(&mut pm);
    pm.handle_datagram(T0, gw(), &[]);
    assert_eq!(pm.stats(), only(|s| s.unexpected = 1));
}
