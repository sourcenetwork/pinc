//! Trace generation for the PCP and NAT-PMP codecs (`pinc_portmap::pcp`, `pinc_portmap::natpmp`): the real encoders and
//! decoders, recorded as ndjson (`portmap/codec.ndjson` under `PINC_TRACE_DIR`) for the TLA+ trace check
//! (`TracePortMapCodec.tla`).
//!
//! An encode event is `{op: "enc", layout, vs, out}` and a decode event `{op: "dec", fam, b, ok[, layout, vs]}`; every
//! number is its big-endian bytes at the field width, so no integer above a byte reaches TLC. The inputs are boundary
//! values of every field (0, 1, max, max - 1, the addresses and error codes of the specification), every one-byte
//! change, every prefix and the one-byte extension of each encoded output, and seeded random values and byte strings.
//! A refused encode is not recorded. Every call is also checked here: decode(encode(v)) is v, encode(decode(b)) is b,
//! a decoded input has exactly the length of its form, and no encoder writes past its buffer. Nothing is written when
//! `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    unreachable_pub,
    clippy::collapsible_if,
    clippy::ip_constant,
    clippy::items_after_statements,
    clippy::manual_is_multiple_of,
    clippy::many_single_char_names,
    clippy::match_wildcard_for_single_variants,
    clippy::panic,
    clippy::type_complexity
)]

use std::fmt::Write as _;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

use pinc_portmap::natpmp::{self, NatPmpError};
use pinc_portmap::pcp::{self, MapRequest, PcpError};
use pinc_tests::{SplitMix64, trace_cases};

/// A JSON array of the bytes.
fn arr(b: &[u8]) -> String {
    let body: Vec<String> = b.iter().map(u8::to_string).collect();
    format!("[{}]", body.join(","))
}

/// The fields of a layout, each as bytes.
type Vs = Vec<Vec<u8>>;

fn vs_json(vs: &Vs) -> String {
    let body: Vec<String> = vs.iter().map(|v| arr(v)).collect();
    format!("[{}]", body.join(","))
}

/// A PCP address as its 16 bytes.
fn a16(ip: IpAddr) -> Vec<u8> {
    match ip {
        IpAddr::V4(v) => v.to_ipv6_mapped().octets().to_vec(),
        IpAddr::V6(v) => v.octets().to_vec(),
    }
}

/// An address as the decoder returns it: an IPv4-mapped one is the IPv4 it maps.
fn canon(ip: IpAddr) -> IpAddr {
    ip.to_canonical()
}

fn req_vs(r: &MapRequest) -> (&'static str, Vs) {
    (
        "pcpMapRequest",
        vec![
            r.lifetime.to_be_bytes().to_vec(),
            a16(r.client),
            r.nonce.to_vec(),
            vec![r.protocol],
            r.internal_port.to_be_bytes().to_vec(),
            r.external_port.to_be_bytes().to_vec(),
            a16(r.external_ip),
        ],
    )
}

fn resp_vs(r: &pcp::Response) -> (&'static str, Vs) {
    match *r {
        pcp::Response::Map {
            result,
            lifetime,
            epoch,
            nonce,
            protocol,
            internal_port,
            external_port,
            external_ip,
        } => (
            "pcpMapResponse",
            vec![
                vec![result],
                lifetime.to_be_bytes().to_vec(),
                epoch.to_be_bytes().to_vec(),
                nonce.to_vec(),
                vec![protocol],
                internal_port.to_be_bytes().to_vec(),
                external_port.to_be_bytes().to_vec(),
                a16(external_ip),
            ],
        ),
        pcp::Response::Header {
            opcode,
            result,
            lifetime,
            epoch,
        } => (
            if opcode == pcp::OP_ANNOUNCE {
                "pcpAnnounce"
            } else {
                "pcpMapHeader"
            },
            vec![
                vec![result],
                lifetime.to_be_bytes().to_vec(),
                epoch.to_be_bytes().to_vec(),
            ],
        ),
    }
}

fn natreq_vs(r: &natpmp::Request) -> (&'static str, Vs) {
    match *r {
        natpmp::Request::Address => ("natAddressRequest", vec![]),
        natpmp::Request::Map {
            internal_port,
            external_port,
            lifetime,
        } => (
            "natMapRequest",
            vec![
                internal_port.to_be_bytes().to_vec(),
                external_port.to_be_bytes().to_vec(),
                lifetime.to_be_bytes().to_vec(),
            ],
        ),
    }
}

fn natresp_vs(r: &natpmp::Response) -> (&'static str, Vs) {
    match *r {
        natpmp::Response::Address { result, epoch, ip } => (
            "natAddressResponse",
            vec![
                result.to_be_bytes().to_vec(),
                epoch.to_be_bytes().to_vec(),
                ip.octets().to_vec(),
            ],
        ),
        natpmp::Response::Map {
            result,
            epoch,
            internal_port,
            external_port,
            lifetime,
        } => (
            "natMapResponse",
            vec![
                result.to_be_bytes().to_vec(),
                epoch.to_be_bytes().to_vec(),
                internal_port.to_be_bytes().to_vec(),
                external_port.to_be_bytes().to_vec(),
                lifetime.to_be_bytes().to_vec(),
            ],
        ),
        natpmp::Response::Error { opcode, result, epoch } => (
            "natError",
            vec![
                vec![opcode | natpmp::RESPONSE],
                result.to_be_bytes().to_vec(),
                epoch.to_be_bytes().to_vec(),
            ],
        ),
    }
}

/// One family: its value type and how it encodes, decodes and lays out.
trait Fam: Sized + Copy + PartialEq + std::fmt::Debug {
    const NAME: &'static str;
    /// The length of every valid encoding of `self`.
    fn form_len(&self) -> usize;
    fn enc(&self, out: &mut [u8]) -> Option<usize>;
    fn dec(b: &[u8]) -> Option<Self>;
    fn vs(&self) -> (&'static str, Vs);
    /// Equal after the canonicalisation of addresses.
    fn same(&self, o: &Self) -> bool;
}

impl Fam for MapRequest {
    const NAME: &'static str = "pcpreq";
    fn form_len(&self) -> usize {
        pcp::MAP_LEN
    }
    fn enc(&self, out: &mut [u8]) -> Option<usize> {
        pcp::encode_request(self, out).ok()
    }
    fn dec(b: &[u8]) -> Option<Self> {
        pcp::decode_request(b).ok()
    }
    fn vs(&self) -> (&'static str, Vs) {
        req_vs(self)
    }
    fn same(&self, o: &Self) -> bool {
        Self {
            client: canon(self.client),
            external_ip: canon(self.external_ip),
            ..*self
        } == Self {
            client: canon(o.client),
            external_ip: canon(o.external_ip),
            ..*o
        }
    }
}

impl Fam for pcp::Response {
    const NAME: &'static str = "pcpresp";
    fn form_len(&self) -> usize {
        match self {
            Self::Map { .. } => pcp::MAP_LEN,
            Self::Header { .. } => pcp::HEADER_LEN,
        }
    }
    fn enc(&self, out: &mut [u8]) -> Option<usize> {
        pcp::encode_response(self, out).ok()
    }
    fn dec(b: &[u8]) -> Option<Self> {
        pcp::decode_response(b).ok()
    }
    fn vs(&self) -> (&'static str, Vs) {
        resp_vs(self)
    }
    fn same(&self, o: &Self) -> bool {
        let c = |r: &Self| match *r {
            Self::Map { external_ip, .. } => match *r {
                Self::Map {
                    result,
                    lifetime,
                    epoch,
                    nonce,
                    protocol,
                    internal_port,
                    external_port,
                    ..
                } => Self::Map {
                    result,
                    lifetime,
                    epoch,
                    nonce,
                    protocol,
                    internal_port,
                    external_port,
                    external_ip: canon(external_ip),
                },
                h => h,
            },
            h => h,
        };
        c(self) == c(o)
    }
}

impl Fam for natpmp::Request {
    const NAME: &'static str = "natreq";
    fn form_len(&self) -> usize {
        match self {
            Self::Address => natpmp::ADDRESS_REQUEST_LEN,
            Self::Map { .. } => natpmp::MAP_REQUEST_LEN,
        }
    }
    fn enc(&self, out: &mut [u8]) -> Option<usize> {
        natpmp::encode_request(self, out).ok()
    }
    fn dec(b: &[u8]) -> Option<Self> {
        natpmp::decode_request(b).ok()
    }
    fn vs(&self) -> (&'static str, Vs) {
        natreq_vs(self)
    }
    fn same(&self, o: &Self) -> bool {
        self == o
    }
}

impl Fam for natpmp::Response {
    const NAME: &'static str = "natresp";
    fn form_len(&self) -> usize {
        match self {
            Self::Address { .. } => natpmp::ADDRESS_RESPONSE_LEN,
            Self::Map { .. } => natpmp::MAP_RESPONSE_LEN,
            Self::Error { .. } => natpmp::ERROR_LEN,
        }
    }
    fn enc(&self, out: &mut [u8]) -> Option<usize> {
        natpmp::encode_response(self, out).ok()
    }
    fn dec(b: &[u8]) -> Option<Self> {
        natpmp::decode_response(b).ok()
    }
    fn vs(&self) -> (&'static str, Vs) {
        natresp_vs(self)
    }
    fn same(&self, o: &Self) -> bool {
        self == o
    }
}

#[derive(Default)]
struct Rec {
    out: String,
    encoded: u32,
    decoded: u32,
}

impl Rec {
    /// A decode, recorded; checked against the encoder and the form length.
    fn dec<F: Fam>(&mut self, b: &[u8]) {
        match F::dec(b) {
            Some(v) => {
                assert_eq!(b.len(), v.form_len(), "{} decoded {b:?} of another length", F::NAME);
                let mut back = vec![0u8; 1100];
                let n = v
                    .enc(&mut back)
                    .unwrap_or_else(|| panic!("{} decoded {b:?} but will not encode it", F::NAME));
                assert_eq!(&back[..n], b, "{}: encode(decode(b)) is not b", F::NAME);
                let (layout, vs) = v.vs();
                self.decoded += 1;
                let _ = writeln!(
                    self.out,
                    r#"{{"op":"dec","fam":"{}","b":{},"ok":true,"layout":"{layout}","vs":{}}}"#,
                    F::NAME,
                    arr(b),
                    vs_json(&vs)
                );
            }
            None => {
                let _ = writeln!(
                    self.out,
                    r#"{{"op":"dec","fam":"{}","b":{},"ok":false}}"#,
                    F::NAME,
                    arr(b)
                );
            }
        }
    }

    /// An encode: into the exact length, one short (refused, nothing written) and 1100 bytes; the exact output is
    /// recorded and fed to the decoder with its variations.
    fn enc<F: Fam>(&mut self, v: &F) {
        let mut big = vec![0xaau8; 1100];
        let Some(n) = v.enc(&mut big) else {
            // a value the encoder refuses (a result code or opcode of no form) is not recorded
            return;
        };
        assert_eq!(n, v.form_len());
        assert!(big[n..].iter().all(|c| *c == 0xaa), "{} wrote past its output", F::NAME);
        let out = big[..n].to_vec();
        let mut exact = out.clone();
        assert_eq!(v.enc(&mut exact), Some(n));
        assert_eq!(exact, out);
        if n > 0 {
            let mut short = vec![0xaau8; n];
            assert_eq!(v.enc(&mut short[..n - 1]), None, "{} fit one byte short", F::NAME);
            assert!(short[n - 1..].iter().all(|c| *c == 0xaa));
        }
        let back = F::dec(&out).unwrap_or_else(|| panic!("{} does not decode its output {out:?}", F::NAME));
        assert!(v.same(&back), "{}: decode(encode(v)) is not v: {v:?} {back:?}", F::NAME);
        let (layout, vs) = v.vs();
        self.encoded += 1;
        let _ = writeln!(
            self.out,
            r#"{{"op":"enc","layout":"{layout}","vs":{},"out":{}}}"#,
            vs_json(&vs),
            arr(&out)
        );
        self.variations::<F>(&out);
    }

    fn variations<F: Fam>(&mut self, out: &[u8]) {
        self.dec::<F>(out);
        for i in 0..out.len() {
            for x in [0x01u8, 0x80, 0xff] {
                let mut b = out.to_vec();
                b[i] ^= x;
                self.dec::<F>(&b);
            }
        }
        for l in 0..out.len() {
            self.dec::<F>(&out[..l]);
        }
        let mut longer = out.to_vec();
        longer.push(0);
        self.dec::<F>(&longer);
    }
}

fn addrs() -> Vec<IpAddr> {
    vec![
        IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0)),
        IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1)),
        IpAddr::V4(Ipv4Addr::new(198, 51, 100, 7)),
        IpAddr::V4(Ipv4Addr::new(255, 255, 255, 255)),
        IpAddr::V6(Ipv6Addr::UNSPECIFIED),
        IpAddr::V6(Ipv6Addr::LOCALHOST),
        IpAddr::V6("2001:db8::5".parse().unwrap()),
        IpAddr::V6("::ffff:1.2.3.4".parse().unwrap()),
    ]
}

const NONCES: [[u8; 12]; 3] = [[0; 12], [255; 12], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]];

fn rand_ip(rng: &mut SplitMix64) -> IpAddr {
    if rng.next_u64() % 2 == 0 {
        IpAddr::V4(Ipv4Addr::from((rng.next_u64() as u32).to_be_bytes()))
    } else {
        let mut b = [0u8; 16];
        rng.fill(&mut b);
        IpAddr::V6(Ipv6Addr::from(b))
    }
}

fn rand_nonce(rng: &mut SplitMix64) -> [u8; 12] {
    let mut n = [0u8; 12];
    rng.fill(&mut n);
    n
}

#[test]
fn the_codecs_match_the_models() {
    let mut r = Rec::default();
    let u32s = [0u32, 1, u32::MAX - 1, u32::MAX];
    let u16s = [0u16, 1, u16::MAX - 1, u16::MAX];
    let u8s = [0u8, 1, 254, 255];
    let ips = addrs();

    // PCP requests: every field over its boundary values, the others at a base value
    let base_req = MapRequest {
        lifetime: 7200,
        client: ips[1],
        nonce: NONCES[2],
        protocol: pcp::UDP,
        internal_port: 65534,
        external_port: 65534,
        external_ip: ips[0],
    };
    r.enc(&base_req);
    for l in u32s {
        r.enc(&MapRequest {
            lifetime: l,
            ..base_req
        });
    }
    for ip in &ips {
        r.enc(&MapRequest {
            client: *ip,
            ..base_req
        });
        r.enc(&MapRequest {
            external_ip: *ip,
            ..base_req
        });
    }
    for n in NONCES {
        r.enc(&MapRequest { nonce: n, ..base_req });
    }
    for p in u8s {
        r.enc(&MapRequest {
            protocol: p,
            ..base_req
        });
    }
    for p in u16s {
        r.enc(&MapRequest {
            internal_port: p,
            ..base_req
        });
        r.enc(&MapRequest {
            external_port: p,
            ..base_req
        });
    }

    // PCP responses
    let base_map = pcp::Response::Map {
        result: 0,
        lifetime: 40,
        epoch: 5,
        nonce: NONCES[2],
        protocol: pcp::UDP,
        internal_port: 65534,
        external_port: 40000,
        external_ip: ips[2],
    };
    let map = |f: &dyn Fn(&mut [u32; 3], &mut [u8; 2], &mut [u16; 2], &mut IpAddr, &mut [u8; 12])| {
        let (mut w, mut b, mut p, mut ip, mut n) =
            ([40u32, 5, 0], [0u8, pcp::UDP], [65534u16, 40000], ips[2], NONCES[2]);
        f(&mut w, &mut b, &mut p, &mut ip, &mut n);
        pcp::Response::Map {
            result: b[0],
            lifetime: w[0],
            epoch: w[1],
            nonce: n,
            protocol: b[1],
            internal_port: p[0],
            external_port: p[1],
            external_ip: ip,
        }
    };
    r.enc(&base_map);
    for v in u32s {
        r.enc(&map(&|w, _, _, _, _| w[0] = v));
        r.enc(&map(&|w, _, _, _, _| w[1] = v));
    }
    for v in u8s {
        r.enc(&map(&|_, b, _, _, _| b[0] = v));
        r.enc(&map(&|_, b, _, _, _| b[1] = v));
    }
    for v in u16s {
        r.enc(&map(&|_, _, p, _, _| p[0] = v));
        r.enc(&map(&|_, _, p, _, _| p[1] = v));
    }
    for ip in &ips {
        r.enc(&map(&|_, _, _, i, _| *i = *ip));
    }
    for n in NONCES {
        r.enc(&map(&|_, _, _, _, m| *m = n));
    }
    for opcode in [pcp::OP_ANNOUNCE, pcp::OP_MAP, 2, 127] {
        for result in u8s {
            for lifetime in [0u32, u32::MAX] {
                for epoch in u32s {
                    r.enc(&pcp::Response::Header {
                        opcode,
                        result,
                        lifetime,
                        epoch,
                    });
                }
            }
        }
    }

    // NAT-PMP
    r.enc(&natpmp::Request::Address);
    for a in u16s {
        for b in u16s {
            for l in u32s {
                r.enc(&natpmp::Request::Map {
                    internal_port: a,
                    external_port: b,
                    lifetime: l,
                });
            }
        }
    }
    for result in u16s {
        for epoch in u32s {
            for ip in [[0, 0, 0, 0], [10, 0, 0, 1], [198, 51, 100, 7], [255, 255, 255, 255]] {
                r.enc(&natpmp::Response::Address {
                    result,
                    epoch,
                    ip: Ipv4Addr::from(ip),
                });
            }
            for p in u16s {
                for l in u32s {
                    r.enc(&natpmp::Response::Map {
                        result,
                        epoch,
                        internal_port: p,
                        external_port: u16::MAX - p,
                        lifetime: l,
                    });
                }
            }
        }
    }
    for opcode in [0u8, 1, 127] {
        for result in [0u16, 1, 65535] {
            for epoch in u32s {
                r.enc(&natpmp::Response::Error { opcode, result, epoch });
            }
        }
    }

    // seeded random values per encoder, and random bytes per decoder
    let mut rng = SplitMix64::traced(0x636f_6465);
    for _ in 0..trace_cases(110, 2048) {
        r.enc(&MapRequest {
            lifetime: rng.next_u64() as u32,
            client: rand_ip(&mut rng),
            nonce: rand_nonce(&mut rng),
            protocol: rng.next_u64() as u8,
            internal_port: rng.next_u64() as u16,
            external_port: rng.next_u64() as u16,
            external_ip: rand_ip(&mut rng),
        });
        r.enc(&pcp::Response::Map {
            result: rng.next_u64() as u8,
            lifetime: rng.next_u64() as u32,
            epoch: rng.next_u64() as u32,
            nonce: rand_nonce(&mut rng),
            protocol: rng.next_u64() as u8,
            internal_port: rng.next_u64() as u16,
            external_port: rng.next_u64() as u16,
            external_ip: rand_ip(&mut rng),
        });
        r.enc(&pcp::Response::Header {
            opcode: (rng.next_u64() % 3) as u8,
            result: rng.next_u64() as u8,
            lifetime: rng.next_u64() as u32,
            epoch: rng.next_u64() as u32,
        });
        r.enc(&natpmp::Request::Map {
            internal_port: rng.next_u64() as u16,
            external_port: rng.next_u64() as u16,
            lifetime: rng.next_u64() as u32,
        });
        r.enc(&natpmp::Response::Address {
            result: rng.next_u64() as u16,
            epoch: rng.next_u64() as u32,
            ip: Ipv4Addr::from((rng.next_u64() as u32).to_be_bytes()),
        });
        r.enc(&natpmp::Response::Map {
            result: rng.next_u64() as u16,
            epoch: rng.next_u64() as u32,
            internal_port: rng.next_u64() as u16,
            external_port: rng.next_u64() as u16,
            lifetime: rng.next_u64() as u32,
        });
        r.enc(&natpmp::Response::Error {
            opcode: (rng.next_u64() % 128) as u8,
            result: rng.next_u64() as u16,
            epoch: rng.next_u64() as u32,
        });
    }
    const LENS: [usize; 14] = [0, 1, 2, 8, 11, 12, 13, 16, 23, 24, 25, 59, 60, 61];
    for _ in 0..trace_cases(1024, 4096) {
        let n = if rng.next_u64() % 2 == 0 {
            LENS[(rng.next_u64() % LENS.len() as u64) as usize]
        } else {
            (rng.next_u64() % 81) as usize
        };
        let mut b = vec![0u8; n];
        rng.fill(&mut b);
        let valid = rng.next_u64() % 2 == 0;
        let (mut pcp_b, mut nat_b) = (b.clone(), b.clone());
        if valid {
            if n >= 2 {
                pcp_b[0] = pcp::VERSION;
                pcp_b[1] = (rng.next_u64() % 2) as u8;
                nat_b[0] = 0;
                nat_b[1] = (rng.next_u64() % 2) as u8;
            }
        }
        r.dec::<MapRequest>(&pcp_b);
        if valid && n >= 2 {
            pcp_b[1] |= pcp::RESPONSE;
        }
        r.dec::<pcp::Response>(&pcp_b);
        r.dec::<natpmp::Request>(&nat_b);
        if valid && n >= 2 {
            nat_b[1] |= natpmp::RESPONSE;
        }
        r.dec::<natpmp::Response>(&nat_b);
    }

    assert!(r.encoded > 1000 && r.decoded > 1000);
    // the error types are part of the public surface the decoders return through
    let _: Option<PcpError> = pcp::decode_request(&[]).err();
    let _: Option<NatPmpError> = natpmp::decode_request(&[]).err();
    if let Some(dir) = std::env::var_os("PINC_TRACE_DIR") {
        let dir = std::path::PathBuf::from(dir).join("portmap");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("codec.ndjson"), r.out).unwrap();
    }
}
