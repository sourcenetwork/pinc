//! Trace generation for the parsers of the `UPnP` leg (`pinc_portmap::upnp`): the real `Url::new`, `parse_location`,
//! `http_response`, `ssdp_location`, `control_of`, `soap_result`, `external_ip` and `is_ssdp_answer`, recorded as
//! ndjson (`portmap/upnp.ndjson` under `PINC_TRACE_DIR`) for the TLA+ trace check (`TracePortMapUpnp.tla`).
//!
//! A URL is `{ip, port, path}`; a `u32` is `[hi, lo]`; byte strings are arrays of 0..=255. One event is written per
//! call, with its input and its result. The inputs are the case sets of `PortMapUpnp.tla` (built here from the same
//! pieces: locations, responses, descriptions and URLs) and seeded random ones: random byte strings and random edits
//! of the boundary cases. The parsers are also checked here against the properties the module documents, and the two
//! request builders `get` and `soap`, which the model leaves out, byte for byte against literals written below.
//! Nothing is written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::panic,
    unreachable_pub,
    clippy::assertions_on_constants,
    clippy::expect_used,
    clippy::needless_borrow
)]

use std::fmt::Write as _;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use pinc_portmap::addr::usable_host;
use pinc_portmap::upnp::{
    self, CONFLICT, Call, MAX_PATH, ONLY_PERMANENT_LEASES, SERVICES, SoapResult, Url, control_of, external_ip, get,
    http_response, is_ssdp_answer, parse_location, soap, soap_result, ssdp_location,
};
use pinc_tests::SplitMix64;

/// A JSON array of the bytes.
fn arr(b: &[u8]) -> String {
    let body: Vec<String> = b.iter().map(u8::to_string).collect();
    format!("[{}]", body.join(","))
}

/// A `u32` as `[hi, lo]`.
fn u(v: u32) -> String {
    format!("[{},{}]", v >> 16, v & 0xffff)
}

fn v4(ip: [u8; 4], port: u16) -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::from(ip)), port)
}

/// A URL as the model's record.
fn url_json(x: &Url) -> String {
    let SocketAddr::V4(a) = x.addr else {
        panic!("a URL of the trace is IPv4")
    };
    let o = a.ip().octets();
    format!(
        r#"{{"ip":[{},{},{},{}],"port":{},"path":{}}}"#,
        o[0],
        o[1],
        o[2],
        o[3],
        a.port(),
        arr(x.path())
    )
}

/// The `ok` and `u` fields of an event for a URL result.
fn url_res(x: Option<Url>) -> String {
    x.map_or_else(
        || r#""ok":false"#.to_owned(),
        |x| format!(r#""ok":true,"u":{}"#, url_json(&x)),
    )
}

/// The checks every location result passes: a usable host, a port of 1 to 65535, a path of 1 to 128 printable bytes
/// that starts with a slash.
fn location_form(x: &Url) {
    let SocketAddr::V4(a) = x.addr else {
        panic!("a location names an IPv4 host")
    };
    assert!(usable_host(*a.ip()), "a location names an unusable host {a}");
    assert!(a.port() >= 1);
    let p = x.path();
    assert!((1..=MAX_PATH).contains(&p.len()) && p[0] == b'/' && p.iter().all(u8::is_ascii_graphic));
}

#[derive(Default)]
struct Rec {
    out: String,
    parsed_loc: u32,
    parsed_resp: u32,
    parsed_ctl: u32,
    parsed_ext: u32,
    faults: u32,
}

impl Rec {
    fn url(&mut self, ip: [u8; 4], port: u16, path: &[u8]) {
        let got = Url::new(v4(ip, port), path);
        let _ = writeln!(
            self.out,
            r#"{{"op":"url","ip":[{},{},{},{}],"port":{port},"path":{},{}}}"#,
            ip[0],
            ip[1],
            ip[2],
            ip[3],
            arr(path),
            url_res(got)
        );
        let want = !path.is_empty() && path.len() <= MAX_PATH && path.iter().all(u8::is_ascii_graphic);
        assert_eq!(got.is_some(), want, "Url::new of {path:?}");
    }

    fn loc(&mut self, b: &[u8]) {
        let got = parse_location(b);
        if let Some(x) = &got {
            location_form(x);
            self.parsed_loc += 1;
        }
        let _ = writeln!(self.out, r#"{{"op":"loc","b":{},{}}}"#, arr(b), url_res(got));
    }

    fn resp(&mut self, b: &[u8]) {
        match http_response(b) {
            Some((status, body)) => {
                // HTTP/1.<digit> <3 digits>, then a space or the end of the line
                assert!(b.starts_with(b"HTTP/1.") && b[7].is_ascii_digit() && b[8] == b' ');
                assert!(b[9..12].iter().all(u8::is_ascii_digit) && (b[12] == b' ' || b[12] == b'\r'));
                assert_eq!(
                    u16::try_from(std::str::from_utf8(&b[9..12]).unwrap().parse::<u32>().unwrap()),
                    Ok(status)
                );
                // the body is a piece of the input that starts right after the first blank line
                let head_end = b.windows(4).position(|w| w == b"\r\n\r\n").unwrap();
                let at = body.as_ptr() as usize - b.as_ptr() as usize;
                assert_eq!(at, head_end + 4, "the body of {b:?} starts elsewhere");
                assert!(at + body.len() <= b.len());
                self.parsed_resp += 1;
                let _ = writeln!(
                    self.out,
                    r#"{{"op":"resp","b":{},"ok":true,"status":{status},"body":{}}}"#,
                    arr(b),
                    arr(body)
                );
            }
            None => {
                let _ = writeln!(self.out, r#"{{"op":"resp","b":{},"ok":false}}"#, arr(b));
            }
        }
    }

    fn ssdp(&mut self, b: &[u8]) {
        let got = ssdp_location(b);
        if let Some(x) = &got {
            location_form(x);
            assert!(b[..9].eq_ignore_ascii_case(b"HTTP/1.1 ") && &b[9..12] == b"200");
        }
        let _ = writeln!(self.out, r#"{{"op":"ssdp","b":{},{}}}"#, arr(b), url_res(got));
    }

    fn ctl(&mut self, b: &[u8], base: &Url) {
        let got = control_of(b, base);
        let res = match got {
            Some((x, k)) => {
                assert_eq!(x.addr.ip(), base.addr.ip(), "a control URL on another host");
                assert!(k < SERVICES.len());
                let SocketAddr::V4(_) = x.addr else {
                    panic!("an IPv4 control URL")
                };
                let p = x.path();
                assert!((1..=MAX_PATH).contains(&p.len()) && p[0] == b'/' && p.iter().all(u8::is_ascii_graphic));
                self.parsed_ctl += 1;
                format!(r#""ok":true,"u":{},"k":{k}"#, url_json(&x))
            }
            None => r#""ok":false"#.to_owned(),
        };
        let _ = writeln!(
            self.out,
            r#"{{"op":"ctl","b":{},"base":{},{res}}}"#,
            arr(b),
            url_json(base)
        );
    }

    fn soap(&mut self, b: &[u8]) {
        let status = http_response(b).map(|(s, body)| (s, body.to_vec()));
        let res = match soap_result(b) {
            None => r#""k":"none""#.to_owned(),
            Some(SoapResult::Ok(body)) => {
                assert_eq!(status.as_ref().map(|s| s.0), Some(200));
                format!(r#""k":"ok","body":{}"#, arr(body))
            }
            Some(SoapResult::Fault(c)) => {
                let (s, body) = status.expect("a fault of an answer that does not parse");
                assert_eq!(s, 500);
                let want = format!("<errorCode>{c}</errorCode>");
                assert!(
                    body.windows(want.len()).any(|w| w == want.as_bytes())
                        || std::str::from_utf8(&body).is_ok_and(|t| t.contains("errorCode")),
                    "a fault code that is not in the body"
                );
                self.faults += 1;
                format!(r#""k":"fault","code":{}"#, u(c))
            }
        };
        let _ = writeln!(self.out, r#"{{"op":"soap","b":{},{res}}}"#, arr(b));
    }

    fn extip(&mut self, b: &[u8]) {
        match external_ip(b) {
            Some(ip) => {
                let o = ip.octets();
                self.parsed_ext += 1;
                let _ = writeln!(
                    self.out,
                    r#"{{"op":"extip","b":{},"ok":true,"o":[{},{},{},{}]}}"#,
                    arr(b),
                    o[0],
                    o[1],
                    o[2],
                    o[3]
                );
            }
            None => {
                let _ = writeln!(self.out, r#"{{"op":"extip","b":{},"ok":false}}"#, arr(b));
            }
        }
    }

    fn ssdpans(&mut self, port: u16, b: &[u8]) {
        let r = is_ssdp_answer(v4([192, 168, 1, 1], port), b);
        assert_eq!(
            r,
            port == 1900 && b.len() >= 7 && b[..7].eq_ignore_ascii_case(b"HTTP/1.")
        );
        let _ = writeln!(self.out, r#"{{"op":"ssdpans","port":{port},"b":{},"r":{r}}}"#, arr(b));
    }

    /// A response through every op that reads one.
    fn resp_all(&mut self, b: &[u8]) {
        self.resp(b);
        self.ssdp(b);
        self.soap(b);
        self.ssdpans(1900, b);
        self.ssdpans(1901, b);
        if let Some((_, body)) = http_response(b) {
            self.extip(body);
        }
    }
}

/// `<name>text</name>`.
fn elem(name: &str, text: &[u8]) -> Vec<u8> {
    [format!("<{name}>").as_bytes(), text, format!("</{name}>").as_bytes()].concat()
}

/// The case sets of `PortMapUpnp.tla`.
struct Cases {
    locs: Vec<Vec<u8>>,
    resps: Vec<Vec<u8>>,
    bodies: Vec<Vec<u8>>,
    descs: Vec<Vec<u8>>,
    urls: Vec<([u8; 4], u16, Vec<u8>)>,
}

fn cases() -> Cases {
    let ip4 = |o: [u8; 4]| format!("{}.{}.{}.{}", o[0], o[1], o[2], o[3]).into_bytes();
    // locations
    let pre = ["http://", "HTTP://", "http:/", "https://"];
    let mut hosts: Vec<Vec<u8>> = [
        [192, 168, 1, 1],
        [10, 0, 0, 1],
        [127, 0, 0, 1],
        [0, 0, 0, 0],
        [169, 254, 1, 1],
        [224, 0, 0, 1],
        [255, 255, 255, 255],
        [8, 8, 8, 8],
    ]
    .map(ip4)
    .to_vec();
    hosts.extend(["1.2.3", "1.2.3.4.5", "256.1.1.1", "1.2.3.4a", ""].map(|s| s.as_bytes().to_vec()));
    let ports = ["", ":", ":0", ":80", ":65535", ":65536", ":x"];
    let paths = ["", "/", "/d", "/a b"];
    let mut locs = Vec::new();
    for w in ["", " "] {
        for p in pre {
            for h in &hosts {
                for pt in ports {
                    for pa in paths {
                        locs.push(
                            [
                                w.as_bytes(),
                                p.as_bytes(),
                                h,
                                pt.as_bytes(),
                                pa.as_bytes(),
                                w.as_bytes(),
                            ]
                            .concat(),
                        );
                    }
                }
            }
        }
    }
    for n in [127, 128] {
        locs.push([b"http://".as_slice(), &ip4([192, 168, 1, 1]), b"/", &vec![b'a'; n]].concat());
    }
    assert_eq!(locs.len(), 2914);
    // responses
    let status: Vec<Vec<u8>> = [
        "HTTP/1.1 200 OK",
        "HTTP/1.0 200",
        "HTTP/1.1 500 E",
        "HTTP/1.1 20",
        "HTTP/1.x 200",
        "HTTP/2 200",
        "http/1.1 200 OK",
        "HTTP/1.1 200OK",
        "HTTP/1.1 2x0",
    ]
    .map(|s| s.as_bytes().to_vec())
    .to_vec();
    let heads: Vec<Vec<u8>> = vec![
        Vec::new(),
        b"Content-Length: 2".to_vec(),
        b"content-length: 99".to_vec(),
        b"Content-Length: x".to_vec(),
        [b"LOCATION: http://".as_slice(), &ip4([192, 168, 1, 1]), b":5000/d"].concat(),
        [b"location:http://".as_slice(), &ip4([8, 8, 8, 8]), b"/x"].concat(),
    ];
    let bodies: Vec<Vec<u8>> = vec![
        Vec::new(),
        b"abcd".to_vec(),
        elem("errorCode", b"718"),
        [
            b"<u:NewExternalIPAddress>".as_slice(),
            &ip4([1, 2, 3, 4]),
            b"</u:NewExternalIPAddress>",
        ]
        .concat(),
        elem("NewExternalIPAddress", &ip4([10, 0, 0, 1])),
    ];
    let mut resps = Vec::new();
    for st in &status {
        for hd in &heads {
            for done in [true, false] {
                for body in &bodies {
                    let mut r = st.clone();
                    r.extend_from_slice(b"\r\n");
                    if !hd.is_empty() {
                        r.extend_from_slice(hd);
                        r.extend_from_slice(b"\r\n");
                    }
                    if done {
                        r.extend_from_slice(b"\r\n");
                    }
                    r.extend_from_slice(body);
                    resps.push(r);
                }
            }
        }
    }
    assert_eq!(resps.len(), 540);
    // descriptions
    let types: Vec<Vec<u8>> = SERVICES.iter().map(|s| s.to_vec()).chain([b"urn:x".to_vec()]).collect();
    let ctls: Vec<Vec<u8>> = vec![
        elem("controlURL", b"/ctl"),
        elem("controlURL", b"ctl"),
        elem(
            "controlURL",
            &[b"http://".as_slice(), &ip4([192, 168, 1, 1]), b":5000/c"].concat(),
        ),
        elem(
            "controlURL",
            &[b"http://".as_slice(), &ip4([192, 168, 1, 2]), b"/c"].concat(),
        ),
        Vec::new(),
        b"<u:controlURL >/n</u:controlURL>".to_vec(),
    ];
    let block =
        |ty: &[u8], ctl: &[u8]| [b"<service>".as_slice(), &elem("serviceType", ty), ctl, b"</service>"].concat();
    let mut firsts: Vec<Vec<u8>> = ctls.iter().map(|x| block(b"urn:x", x)).collect();
    firsts.push(block(&SERVICES[0], b""));
    let mut descs = Vec::new();
    for ty in &types {
        for x in &ctls {
            descs.push(block(ty, x));
        }
    }
    for f in &firsts {
        for ty in &types {
            for x in &ctls {
                descs.push([f.as_slice(), &block(ty, x)].concat());
            }
        }
    }
    assert_eq!(descs.len(), 192);
    // URLs
    let mut urls = Vec::new();
    for ip in [[192, 168, 1, 1], [8, 8, 8, 8], [1, 2, 3, 4]] {
        for p in [1u16, 80, 5000, 65535] {
            for pa in [b"/".to_vec(), b"/d".to_vec(), [b"/".as_slice(), &[b'a'; 127]].concat()] {
                urls.push((ip, p, pa));
            }
        }
    }
    assert_eq!(urls.len(), 36);
    Cases {
        locs,
        resps,
        bodies,
        descs,
        urls,
    }
}

/// A random edit of `b`: replace, insert or delete 1 to 3 bytes.
fn edit(rng: &mut SplitMix64, b: &[u8]) -> Vec<u8> {
    let mut v = b.to_vec();
    let n = 1 + (rng.next_u64() % 3) as usize;
    for _ in 0..n {
        let at = (rng.next_u64() % (v.len() as u64 + 1)) as usize;
        let byte = rng.next_u64() as u8;
        match rng.next_u64() % 3 {
            0 if at < v.len() => v[at] = byte,
            1 => v.insert(at, byte),
            _ if at < v.len() => {
                v.remove(at);
            }
            _ => v.push(byte),
        }
    }
    v
}

fn random_bytes(rng: &mut SplitMix64) -> Vec<u8> {
    let mut b = vec![0u8; (rng.next_u64() % 201) as usize];
    rng.fill(&mut b);
    b
}

fn pick<'a>(rng: &mut SplitMix64, from: &'a [Vec<u8>]) -> &'a [u8] {
    &from[(rng.next_u64() % from.len() as u64) as usize]
}

/// The SSDP answer that carries the location `b`.
fn ssdp_of(b: &[u8]) -> Vec<u8> {
    [b"HTTP/1.1 200\r\nlocation:".as_slice(), b, b"\r\n\r\n"].concat()
}

/// `http://a.b.c.d:port/path` of a boundary URL.
fn render(ip: [u8; 4], port: u16, path: &[u8]) -> Vec<u8> {
    [
        format!("http://{}.{}.{}.{}:{port}", ip[0], ip[1], ip[2], ip[3]).as_bytes(),
        path,
    ]
    .concat()
}

/// The request builders, byte for byte against literals.
fn builders() {
    let cases = cases();
    for (ip, port, path) in &cases.urls {
        let url = Url::new(v4(*ip, *port), path).unwrap();
        let want = [
            b"GET ".as_slice(),
            path,
            format!(
                " HTTP/1.0\r\nHost: {}.{}.{}.{}:{port}\r\nConnection: close\r\n\r\n",
                ip[0], ip[1], ip[2], ip[3]
            )
            .as_bytes(),
        ]
        .concat();
        for len in [want.len(), 1024] {
            let mut buf = vec![0xaa; len];
            assert_eq!(get(&url, &mut buf), Some(want.len()));
            assert_eq!(&buf[..want.len()], want.as_slice());
            assert!(buf[want.len()..].iter().all(|c| *c == 0xaa));
        }
        let mut short = vec![0xaa; want.len() + 4];
        assert_eq!(get(&url, &mut short[..want.len() - 1]), None);
        assert!(
            short[want.len() - 1..].iter().all(|c| *c == 0xaa),
            "a get wrote past its buffer"
        );

        let calls = [
            Call::ExternalIp,
            Call::Add {
                external: 65534,
                client: Ipv4Addr::new(10, 0, 0, 2),
                internal: 65534,
                lease: 7200,
            },
            Call::Add {
                external: 65534,
                client: Ipv4Addr::new(10, 0, 0, 2),
                internal: 65534,
                lease: 0,
            },
            Call::Delete { external: 1024 },
        ];
        for call in &calls {
            for service in 0..=3 {
                let mut buf = vec![0xaa; 2048];
                let Some(svc) = SERVICES.get(service) else {
                    assert_eq!(soap(&url, service, call, &mut buf), None);
                    continue;
                };
                let (action, args) = match call {
                    Call::ExternalIp => ("GetExternalIPAddress", String::new()),
                    Call::Add {
                        external,
                        internal,
                        lease,
                        ..
                    } => (
                        "AddPortMapping",
                        format!(
                            "<NewRemoteHost></NewRemoteHost><NewExternalPort>{external}</NewExternalPort><NewProtocol>UDP</NewProtocol><NewInternalPort>{internal}</NewInternalPort><NewInternalClient>10.0.0.2</NewInternalClient><NewEnabled>1</NewEnabled><NewPortMappingDescription>pinc</NewPortMappingDescription><NewLeaseDuration>{lease}</NewLeaseDuration>"
                        ),
                    ),
                    Call::Delete { external } => (
                        "DeletePortMapping",
                        format!(
                            "<NewRemoteHost></NewRemoteHost><NewExternalPort>{external}</NewExternalPort><NewProtocol>UDP</NewProtocol>"
                        ),
                    ),
                };
                let svc = std::str::from_utf8(svc).unwrap();
                let body = format!(
                    "<?xml version=\"1.0\"?><s:Envelope xmlns:s=\"http://schemas.xmlsoap.org/soap/envelope/\" s:encodingStyle=\"http://schemas.xmlsoap.org/soap/encoding/\"><s:Body><u:{action} xmlns:u=\"{svc}\">{args}</u:{action}></s:Body></s:Envelope>"
                );
                let want = [
                    b"POST ".as_slice(),
                    path,
                    format!(
                        " HTTP/1.0\r\nHost: {}.{}.{}.{}:{port}\r\nContent-Type: text/xml; charset=\"utf-8\"\r\nSOAPAction: \"{svc}#{action}\"\r\nConnection: close\r\nContent-Length: {}\r\n\r\n{body}",
                        ip[0],
                        ip[1],
                        ip[2],
                        ip[3],
                        body.len()
                    )
                    .as_bytes(),
                ]
                .concat();
                assert!(want.len() <= 2048);
                assert_eq!(soap(&url, service, call, &mut buf), Some(want.len()));
                assert_eq!(&buf[..want.len()], want.as_slice());
                let mut short = vec![0xaa; want.len() + 4];
                assert_eq!(soap(&url, service, call, &mut short[..want.len() - 1]), None);
                assert!(
                    short[want.len() - 1..].iter().all(|c| *c == 0xaa),
                    "a soap wrote past its buffer"
                );
            }
        }
    }
    assert!(ONLY_PERMANENT_LEASES == 725 && CONFLICT == 718);
    assert_eq!(upnp::SSDP.port(), 1900);
}

#[test]
fn the_upnp_parsers_match_the_models() {
    let c = cases();
    let mut r = Rec::default();
    let base = parse_location(b"http://192.168.1.1:5000/d").unwrap();

    // boundary
    for b in &c.locs {
        r.loc(b);
        r.ssdp(&ssdp_of(b));
    }
    for b in &c.resps {
        r.resp_all(b);
    }
    for b in &c.descs {
        r.ctl(b, &base);
    }
    for (ip, port, path) in &c.urls {
        r.url(*ip, *port, path);
        let rendered = render(*ip, *port, path);
        r.loc(&rendered);
        assert_eq!(
            parse_location(&rendered),
            Url::new(v4(*ip, *port), path),
            "a URL does not read back from its form"
        );
    }

    // seeded random
    let mut rng = SplitMix64::traced(0x7570_6e70);
    for _ in 0..2048 {
        let b = random_bytes(&mut rng);
        r.loc(&b);
        r.resp(&b);
        r.ssdp(&b);
        r.soap(&b);
        r.extip(&b);
        let port = [1900u16, 1901, rng.next_u64() as u16][(rng.next_u64() % 3) as usize];
        r.ssdpans(port, &b);
    }
    for _ in 0..2048 {
        let src = pick(&mut rng, &c.locs);
        let b = edit(&mut rng, src);
        r.loc(&b);
        let src = ssdp_of(pick(&mut rng, &c.locs));
        let b = edit(&mut rng, &src);
        r.ssdp(&b);
        let src = pick(&mut rng, &c.resps);
        let b = edit(&mut rng, src);
        r.resp(&b);
        r.soap(&b);
        let src = pick(&mut rng, &c.resps);
        let b = edit(&mut rng, src);
        r.ssdp(&b);
        r.ssdpans(1900, &b);
        let src = pick(&mut rng, &c.bodies);
        let b = edit(&mut rng, src);
        r.extip(&b);
    }
    for _ in 0..512 {
        let mut path = vec![0u8; (rng.next_u64() % 131) as usize];
        for p in &mut path {
            *p = match rng.next_u64() % 8 {
                0 => (rng.next_u64() % 32) as u8,
                1 => 127 + (rng.next_u64() % 129) as u8,
                _ => 33 + (rng.next_u64() % 94) as u8,
            };
        }
        r.url((rng.next_u64() as u32).to_be_bytes(), rng.next_u64() as u16, &path);
    }
    for _ in 0..512 {
        let src = pick(&mut rng, &c.descs);
        let b = edit(&mut rng, src);
        r.ctl(&b, &base);
    }

    builders();

    if !pinc_tests::soaking() {
        assert!(r.parsed_loc > 0 && r.parsed_resp > 0 && r.parsed_ctl > 0 && r.parsed_ext > 0 && r.faults > 0);
    }
    if let Some(dir) = std::env::var_os("PINC_TRACE_DIR") {
        let dir = std::path::PathBuf::from(dir).join("portmap");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("upnp.ndjson"), r.out).unwrap();
    }
}
