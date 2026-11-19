//! Model-based tests of the port-mapping client's fallback order: a real `PortMap` (`pinc-portmap`, built with the
//! `trace` feature) driven along every edge of the state graph of `proofs/tla/MbtPortMapFallback.tla`.
//!
//! TLC enumerates every state the calls of `PortMapFallbackOps.tla` reach and writes the graph; `scripts/mbt.py` turns
//! it into paths from the initial state that take every edge, which `scripts/proofs.sh` writes to the directory
//! `PINC_MBT_DIR` as `portmap_fallback.ndjson`. This test runs each path on a fresh client: the first call builds it
//! for the case's gateway and socket, every other call is one of the client's (`poll_datagram`, `poll_http`,
//! `handle_timeout`, `handle_datagram` of a PCP, NAT-PMP or search answer, `handle_http`, `stop`, `restart`). After
//! every call the result must be the model's (the datagram or request given out, classified, or the one `Stats`
//! counter bumped) and the client's step, tries, due datagram, HTTP exchange, mapping held, renewal in flight,
//! release slots and halt, and when the model keeps a UPnP gateway its control URL, permanent-lease flag, conflict
//! count and external port, must be the model's state. It stops at the first difference and names the case, the step
//! and the calls that led there. Without `PINC_MBT_DIR` it checks nothing.
//!
//! The world is fixed (see `MbtPortMapFallback.tla`): the gateway is `192.168.1.1`, the local socket has port 65534
//! and, by the model's class, a private IPv4 address, a public one or an unspecified one (IPv4 for an even case
//! number, IPv6 for an odd one, except the private class), the nonce is `0..=11`, and the gateway's epoch in every
//! answer is the test's time in whole seconds, so no answer shows a restart.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    unreachable_pub,
    clippy::doc_markdown,
    clippy::many_single_char_names
)]

use std::fmt::Write as _;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use pinc_portmap::lease::SEC;
use pinc_portmap::upnp::MAX_REQUEST;
use pinc_portmap::{Config, MAX_DATAGRAM, PortMap, Probe, Proto, Stats, natpmp, pcp};
use pinc_tests::{Json, MbtCase, mbt_cases};

const GATEWAY_IP: Ipv4Addr = Ipv4Addr::new(192, 168, 1, 1);
const PORT: u16 = 65534;
const EXTERNAL: Ipv4Addr = Ipv4Addr::new(198, 51, 100, 7);
const PRIVATE: Ipv4Addr = Ipv4Addr::new(10, 0, 0, 9);
const NONCE: [u8; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

fn gateway(port: u16) -> SocketAddr {
    SocketAddr::from((GATEWAY_IP, port))
}

/// The local socket of the class `l` for case `id`.
fn local(l: &str, id: u64) -> SocketAddr {
    let ip: IpAddr = match (l, id % 2) {
        ("priv", _) => Ipv4Addr::new(192, 168, 1, 20).into(),
        ("pub", 0) => Ipv4Addr::new(203, 0, 113, 5).into(),
        ("pub", _) => Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 5).into(),
        ("unspec", 0) => Ipv4Addr::UNSPECIFIED.into(),
        ("unspec", _) => Ipv6Addr::UNSPECIFIED.into(),
        _ => panic!("a socket class the test does not know: {l}"),
    };
    SocketAddr::new(ip, PORT)
}

/// The external port `AddPortMapping` asks for after `cf` conflicts.
const fn ext_port(cf: u64) -> u16 {
    match cf {
        0 => 65534,
        1 => 65535,
        2 => 1024,
        _ => 1025,
    }
}

fn proto_name(p: Option<Proto>) -> &'static str {
    match p {
        None => "none",
        Some(Proto::Pcp) => "pcp",
        Some(Proto::NatPmp) => "natpmp",
        Some(Proto::Upnp) => "upnp",
    }
}

/// The PCP answer `k` at time `now`.
fn pcp_answer(k: &str, now: u64) -> Vec<u8> {
    let epoch = u32::try_from(now / SEC).unwrap();
    let map = |result: u8, nonce: [u8; 12], internal_port: u16, ip: Ipv4Addr| pcp::Response::Map {
        result,
        lifetime: 7200,
        epoch,
        nonce,
        protocol: pcp::UDP,
        internal_port,
        external_port: 40000,
        external_ip: ip.into(),
    };
    let header = |opcode: u8, result: u8| pcp::Response::Header {
        opcode,
        result,
        lifetime: 0,
        epoch,
    };
    let r = match k {
        "grant" => map(0, NONCE, PORT, EXTERNAL),
        "grantpriv" => map(0, NONCE, PORT, PRIVATE),
        "unsupp" => map(1, NONCE, PORT, EXTERNAL),
        "err" => map(8, NONCE, PORT, EXTERNAL),
        "nonce" => map(0, [9; 12], PORT, EXTERNAL),
        "port" => map(0, NONCE, PORT - 1, EXTERNAL),
        "hunsupp" => header(pcp::OP_MAP, 1),
        "herr" => header(pcp::OP_MAP, 8),
        "announce" => header(pcp::OP_ANNOUNCE, 0),
        _ => panic!("a PCP answer the test does not know: {k}"),
    };
    let mut buf = [0u8; MAX_DATAGRAM];
    let n = pcp::encode_response(&r, &mut buf).unwrap();
    buf[..n].to_vec()
}

/// The NAT-PMP answer `k` at time `now`.
fn nat_answer(k: &str, now: u64) -> Vec<u8> {
    let epoch = u32::try_from(now / SEC).unwrap();
    let addr = |result: u16, ip: Ipv4Addr| natpmp::Response::Address { result, epoch, ip };
    let map = |result: u16, internal_port: u16| natpmp::Response::Map {
        result,
        epoch,
        internal_port,
        external_port: 40000,
        lifetime: 7200,
    };
    let err = |opcode: u8| natpmp::Response::Error {
        opcode,
        result: 1,
        epoch,
    };
    let r = match k {
        "addr" => addr(0, EXTERNAL),
        "addrpriv" => addr(0, PRIVATE),
        "addrerr" => addr(3, EXTERNAL),
        "map" => map(0, PORT),
        "maperr" => map(3, PORT),
        "port" => map(0, PORT - 1),
        "err0" => err(natpmp::OP_ADDRESS),
        "err1" => err(natpmp::OP_MAP_UDP),
        "garbage" => return vec![0, 5],
        _ => panic!("a NAT-PMP answer the test does not know: {k}"),
    };
    let mut buf = [0u8; MAX_DATAGRAM];
    let n = natpmp::encode_response(&r, &mut buf).unwrap();
    buf[..n].to_vec()
}

fn ssdp_answer(k: &str) -> Vec<u8> {
    match k {
        "ok" => b"HTTP/1.1 200 OK\r\nLOCATION: http://192.168.1.1:5000/d\r\n\r\n".to_vec(),
        "foreign" => b"HTTP/1.1 200 OK\r\nLOCATION: http://192.168.1.77:5000/d\r\n\r\n".to_vec(),
        "other" => b"HTTP/1.1 404 Not Found\r\n\r\n".to_vec(),
        "bad" => b"NOTIFY * HTTP/1.1\r\n\r\n".to_vec(),
        _ => panic!("a search answer the test does not know: {k}"),
    }
}

fn http_answer(k: &str) -> Option<Vec<u8>> {
    let reply = |status: &str, body: &str| {
        Some(format!("HTTP/1.1 {status}\r\nContent-Length: {}\r\n\r\n{body}", body.len()).into_bytes())
    };
    let fault = |code: u32| {
        format!(
            "<s:Envelope><s:Body><s:Fault><detail><UPnPError><errorCode>{code}</errorCode></UPnPError></detail></s:Fault></s:Body></s:Envelope>"
        )
    };
    let ip = |a: &str| {
        format!(
            "<s:Envelope><s:Body><u:GetExternalIPAddressResponse><NewExternalIPAddress>{a}</NewExternalIPAddress></u:GetExternalIPAddressResponse></s:Body></s:Envelope>"
        )
    };
    match k {
        "fail" => None,
        "desc" => reply(
            "200 OK",
            "<root><device><serviceList><service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>/ctl</controlURL></service></serviceList></device></root>",
        ),
        "ip" => reply("200 OK", &ip("198.51.100.7")),
        "ippriv" => reply("200 OK", &ip("10.0.0.9")),
        "ok" => reply("200 OK", ""),
        "perm" => reply("500 Internal Server Error", &fault(725)),
        "conflict" => reply("500 Internal Server Error", &fault(718)),
        "fault" => reply("500 Internal Server Error", &fault(501)),
        _ => panic!("an HTTP answer the test does not know: {k}"),
    }
}

/// The datagram `bytes` to `to`, as the model names it.
fn classify_dgram(to: SocketAddr, bytes: &[u8]) -> &'static str {
    if to.port() == 1900 {
        assert!(
            bytes.starts_with(b"M-SEARCH"),
            "a datagram to port 1900 that is not a search"
        );
        return "search";
    }
    assert_eq!(to, gateway(5351), "a datagram to somewhere else than the gateway");
    match bytes[0] {
        2 => {
            let r = pcp::decode_request(bytes).unwrap();
            if r.lifetime > 0 { "pcp" } else { "pcprel" }
        }
        0 => match natpmp::decode_request(bytes).unwrap() {
            natpmp::Request::Address => "nataddr",
            natpmp::Request::Map { lifetime, .. } if lifetime > 0 => "natmap",
            natpmp::Request::Map { .. } => "natrel",
        },
        v => panic!("a datagram of version {v}"),
    }
}

/// The HTTP request `bytes`, as the model names it; the external port of an AddPortMapping.
fn classify_http(bytes: &[u8]) -> (&'static str, Option<u64>) {
    let text = std::str::from_utf8(bytes).unwrap();
    if text.starts_with("GET ") {
        return ("get", None);
    }
    assert!(
        text.starts_with("POST "),
        "an HTTP request that is neither a GET nor a POST"
    );
    let action = text
        .lines()
        .find(|l| l.starts_with("SOAPAction:"))
        .unwrap()
        .trim_end_matches('"');
    let port = |t: &str| {
        let at = t.find("<NewExternalPort>").unwrap() + "<NewExternalPort>".len();
        t[at..at + t[at..].find('<').unwrap()].parse::<u64>().unwrap()
    };
    if action.ends_with("#GetExternalIPAddress") {
        ("extip", None)
    } else if action.ends_with("#AddPortMapping") {
        let perm = text.contains("<NewLeaseDuration>0</NewLeaseDuration>");
        (if perm { "addperm" } else { "add" }, Some(port(text)))
    } else if action.ends_with("#DeletePortMapping") {
        ("delete", None)
    } else {
        panic!("a SOAP action the test does not know: {action}")
    }
}

/// The one `Stats` field that grew between `a` and `b` (by one), or "none"; the test asserts at most one did.
fn bumped(a: &Stats, b: &Stats) -> &'static str {
    let fields = [
        ("wrong_source", a.wrong_source, b.wrong_source),
        ("wrong_nonce", a.wrong_nonce, b.wrong_nonce),
        ("unexpected", a.unexpected, b.unexpected),
        ("refused_address", a.refused_address, b.refused_address),
        ("timeouts", a.timeouts, b.timeouts),
        ("http_failures", a.http_failures, b.http_failures),
    ];
    let grown: Vec<&str> = fields
        .iter()
        .filter(|(_, x, y)| {
            assert!(*y == *x || *y == *x + 1, "a counter moved by more than one");
            y != x
        })
        .map(|(n, _, _)| *n)
        .collect();
    assert!(grown.len() <= 1, "a call bumped more than one counter: {grown:?}");
    grown.first().copied().unwrap_or("none")
}

/// The counter the model's `r` names.
fn counter(r: &str) -> &'static str {
    match r {
        "none" => "none",
        "unexpected" => "unexpected",
        "wrong_nonce" => "wrong_nonce",
        "wrong_source" => "wrong_source",
        "refused" => "refused_address",
        "timeouts" => "timeouts",
        "http" => "http_failures",
        _ => panic!("a result the test does not know: {r}"),
    }
}

fn num(v: &Json) -> u64 {
    v.u64().unwrap()
}

fn text(v: &Json) -> &str {
    v.str().unwrap()
}

/// The calls of `case` up to step `upto`, for a failure message.
fn calls(case: &MbtCase, upto: usize) -> String {
    let mut s = String::new();
    for (i, st) in case.steps.iter().take(upto + 1).enumerate() {
        let _ = write!(s, "\n  {i}: {st}");
    }
    s
}

/// The client's state against the model's node `s`.
fn same_state(p: &Probe, s: &Json, at: &dyn Fn() -> String) {
    let f = |n: &str| s.get(n).unwrap();
    assert_eq!(
        p.step,
        text(f("st")),
        "{}: the step differs; the model's node is {s}; the probe {p:?}",
        at()
    );
    assert_eq!(
        u64::from(p.tries),
        num(f("tr")),
        "{}: the tries differ; the model's node is {s}; the probe {p:?}",
        at()
    );
    assert_eq!(
        p.send,
        f("sd").bool().unwrap(),
        "{}: the datagram due differs; the model's node is {s}; the probe {p:?}",
        at()
    );
    assert_eq!(
        p.http,
        text(f("ht")),
        "{}: the HTTP exchange differs; the model's node is {s}; the probe {p:?}",
        at()
    );
    assert_eq!(
        proto_name(p.held.map(|h| h.0)),
        text(f("hd")),
        "{}: the mapping held differs; the model's node is {s}; the probe {p:?}",
        at()
    );
    assert_eq!(
        p.renewing,
        f("rn").bool().unwrap(),
        "{}: the renewal differs; the model's node is {s}; the probe {p:?}",
        at()
    );
    let rl: Vec<&str> = f("rl").arr().unwrap().iter().map(text).collect();
    assert_eq!(
        [proto_name(p.releases[0]), proto_name(p.releases[1])],
        rl.as_slice(),
        "{}: the release slots differ; the model's node is {s}; the probe {p:?}",
        at()
    );
    assert_eq!(
        p.halted,
        f("hl").bool().unwrap(),
        "{}: the halt differs; the model's node is {s}; the probe {p:?}",
        at()
    );
    // the model clears the UPnP gateway where nothing reads it again; the code keeps it
    let ig = f("ig");
    if ig.get("on").unwrap().bool().unwrap() {
        let cf = num(ig.get("cf").unwrap());
        assert_eq!(
            p.igd,
            Some((
                ig.get("ctl").unwrap().bool().unwrap(),
                ig.get("pm").unwrap().bool().unwrap(),
                u8::try_from(cf).unwrap(),
                ext_port(cf)
            )),
            "{}: the UPnP gateway differs; the model's node is {s}; the probe {p:?}",
            at()
        );
    }
}

/// Runs one case of `file` on a fresh client; returns the number of calls.
fn run(file: &str, case: &MbtCase, init: &Json) -> usize {
    let who = format!("{file} case {}", case.id);
    let mut before = init.get("s").unwrap();
    let mut pm: Option<PortMap> = None;
    let mut now = 0u64;
    for (i, st) in case.steps.iter().enumerate() {
        let a = &st.args;
        let c = st.call.as_str();
        let at = || format!("{who} step {i} ({c}); calls:{}", calls(case, i));
        if c == "CallNew" {
            let [g, l] = a.as_slice() else {
                panic!("{who}: CallNew without two arguments")
            };
            let gw = g.bool().unwrap().then_some(IpAddr::V4(GATEWAY_IP));
            pm = Some(PortMap::new(Config::new(gw, local(text(l), case.id), NONCE), 0));
        } else {
            let p = pm.as_mut().unwrap_or_else(|| panic!("{who}: a call before CallNew"));
            let stats = p.stats();
            let mut result: Option<&str> = None;
            match (c, a.as_slice()) {
                ("CallDgram", [r]) => {
                    let mut buf = [0u8; MAX_DATAGRAM];
                    let got = p
                        .poll_datagram(&mut buf)
                        .map_or("none", |(to, n)| classify_dgram(to, &buf[..n]));
                    assert_eq!(got, text(r), "{}: the datagram given out differs", at());
                }
                ("CallHttpPoll", [r]) => {
                    let mut buf = [0u8; MAX_REQUEST];
                    let got = p.poll_http(&mut buf).map(|(_, n)| classify_http(&buf[..n]));
                    assert_eq!(
                        got.map_or("none", |g| g.0),
                        text(r),
                        "{}: the request given out differs",
                        at()
                    );
                    if let Some(("add" | "addperm", Some(port))) = got {
                        let cf = num(before.get("ig").unwrap().get("cf").unwrap());
                        assert_eq!(
                            port,
                            u64::from(ext_port(cf)),
                            "{}: AddPortMapping asks for another external port",
                            at()
                        );
                    }
                }
                ("CallTick", [r]) => {
                    let t = p.poll_timeout().unwrap_or(now);
                    p.handle_timeout(t);
                    now = t;
                    result = Some(text(r));
                }
                ("CallLate", []) => {
                    now += 2 * 86_400 * SEC;
                    p.handle_timeout(now);
                    result = Some("none");
                }
                ("CallPcp", [k, r]) => {
                    p.handle_datagram(now, gateway(5351), &pcp_answer(text(k), now));
                    result = Some(text(r));
                }
                ("CallNat", [k, r]) => {
                    p.handle_datagram(now, gateway(5351), &nat_answer(text(k), now));
                    result = Some(text(r));
                }
                ("CallSsdp", [k, r]) => {
                    p.handle_datagram(now, gateway(1900), &ssdp_answer(text(k)));
                    result = Some(text(r));
                }
                ("CallHttp", [k, r]) => {
                    p.handle_http(now, http_answer(text(k)).as_deref());
                    result = Some(text(r));
                }
                ("CallStop", []) => {
                    p.stop(now);
                    result = Some("none");
                }
                ("CallRestart", []) => {
                    p.restart(now);
                    result = Some("none");
                }
                _ => panic!("{who}: a call the test does not know: {st}"),
            }
            if let Some(r) = result {
                assert_eq!(
                    bumped(&stats, &p.stats()),
                    counter(r),
                    "{}: the counter bumped differs",
                    at()
                );
            }
        }
        let after = st.state.get("s").unwrap();
        same_state(&pm.as_ref().unwrap().probe(), after, &|| {
            format!("{who} after step {i}; calls:{}", calls(case, i))
        });
        before = after;
    }
    case.steps.len()
}

/// Walks every case of `file`; false when `PINC_MBT_DIR` is unset.
fn walk(file: &str) -> bool {
    let Some(cases) = mbt_cases(file) else {
        return false;
    };
    let mut cases = cases.unwrap();
    let head = cases.head.clone();
    let init = head.get("init").unwrap();
    let (mut n, mut steps) = (0u64, 0usize);
    for case in &mut cases {
        steps += run(file, &case.unwrap(), init);
        n += 1;
    }
    let count = |f: &str| num(head.get(f).unwrap());
    assert!(n > 0, "{file}: no cases");
    assert_eq!(
        (n, steps as u64),
        (count("cases"), count("steps")),
        "{file}: the file ends early"
    );
    eprintln!(
        "mbt_portmap_fallback: {file}: {n} cases, {steps} calls, every one of the {} edges between the {} states of the graph",
        count("edges"),
        count("states")
    );
    true
}

#[test]
fn the_fallback_order_follows_every_edge_of_the_model() {
    if !walk("portmap_fallback.ndjson") {
        eprintln!(
            "mbt_portmap_fallback: PINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)"
        );
    }
}
