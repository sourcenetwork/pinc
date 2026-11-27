//! `pinc-portmap`: the client state machine driven by generated gateway replies, HTTP answers and clock steps, and the
//! codecs on gateway bytes that are valid, mangled or garbage.
//!
//! Where the expected behaviour comes from:
//! - the module documentation of `pinc_portmap::client`: "[`PortMap::mapped`] is a mapping the gateway granted and
//!   whose lease has not ended on the client's clock, and none after [`PortMap::stop`]; an answer is taken only from
//!   the gateway (or, for SSDP, from port 1900 of it) and only for the request in flight (PCP by its nonce, protocol
//!   and port; NAT-PMP by its opcode and port); every buffer is bounded and nothing allocates or panics", "A grant is a
//!   lease that started when its request first left ... it is as long as the shorter of what the gateway granted and
//!   what was asked", "[`PortMap::stop`] drops the mapping and asks the gateway to delete it ... The client does
//!   nothing more afterwards";
//! - `docs/proofs/properties.md`, the port-mapping row: "an announce, which answers no request and carries no nonce,
//!   never takes a mapping out of the record", "a client that believes an announce's epoch lets a host on the link take
//!   a held mapping out of the record";
//! - the crate documentation: "The codecs ([`pcp`], [`natpmp`], [`upnp`]) are length-checked, take one valid form,
//!   and never panic"; `upnp`: the control URL is "a path or an `http://` URL of the same form and of the
//!   description's own host", a description host is never "a loopback, unspecified, multicast, broadcast or
//!   link-local host"; `lease`: "nothing overflows (every sum saturates)".
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::cast_possible_truncation, missing_docs)]

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use ephyra::prelude::*;
use pinc_pbt::{bytes, mostly_valid};
use pinc_portmap::client::PORT;
use pinc_portmap::lease::{self, Epoch, MAX_LIFETIME, SEC};
use pinc_portmap::upnp::{self, SSDP, Url};
use pinc_portmap::{Config, PortMap, Proto, natpmp, pcp};

const GW: Ipv4Addr = Ipv4Addr::new(192, 168, 1, 1);
const OTHER: Ipv4Addr = Ipv4Addr::new(192, 168, 1, 77);
const FOREIGN_NONCE: [u8; 12] = [0xee; 12];

/// External addresses a gateway may name: the first two are reachable from the internet, the rest are refused.
const EXT_IPS: [IpAddr; 10] = [
    IpAddr::V4(Ipv4Addr::new(203, 0, 113, 9)),
    IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1)),
    IpAddr::V4(Ipv4Addr::new(192, 168, 1, 1)),
    IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1)),
    IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)),
    IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0)),
    IpAddr::V4(Ipv4Addr::new(100, 64, 1, 1)),
    IpAddr::V4(Ipv4Addr::new(169, 254, 1, 1)),
    IpAddr::V4(Ipv4Addr::new(224, 0, 0, 1)),
    IpAddr::V6(Ipv6Addr::new(0xfe80, 0, 0, 0, 0, 0, 0, 1)),
];

fn v4_ext(i: u8) -> Ipv4Addr {
    match EXT_IPS[usize::from(i) % EXT_IPS.len()] {
        IpAddr::V4(v4) => v4,
        IpAddr::V6(_) => Ipv4Addr::new(203, 0, 113, 10),
    }
}

/// How the gateway's epoch in an answer relates to its clock.
#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Ep {
    /// Seconds since the gateway booted, as a gateway that keeps its mappings says.
    Steady,
    /// A small epoch: the gateway restarted a moment ago (or a spoofer says so).
    Back(#[ephyra(gen = gens::int(0u32..=3))] u32),
    /// Any value.
    Any(#[ephyra(gen = gens::int(0u32..=u32::MAX))] u32),
}

/// How the host answers the HTTP request the client last gave out.
#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Answer {
    /// The answer a working gateway gives to that request.
    Right,
    /// The right answer with the external address replaced.
    ExtIp(#[ephyra(gen = gens::int(0u8..=9))] u8),
    /// A SOAP fault.
    Fault(#[ephyra(gen = gens::pick_from(vec![718u32, 725, 501, 402, 714]))] u32),
    /// Another status.
    Status404,
    /// The right answer cut short.
    Cut(#[ephyra(gen = gens::int(0usize..=400))] usize),
    /// The right answer with one byte changed.
    Flip(#[ephyra(gen = gens::int(0usize..=400))] usize, #[ephyra(gen = gens::int(1u8..=255))] u8),
    /// Bytes.
    Garbage(#[ephyra(gen = bytes(80))] Vec<u8>),
    /// The connection failed.
    Fail,
}

/// One thing that happens to the client.
#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Op {
    /// The host's timer: time jumps to the client's own deadline and the timer runs.
    Timer,
    /// Time passes and the host runs the timer.
    Wait(#[ephyra(gen = waits())] u64),
    /// Time passes, and the next thing the host hands the client is not the timer (a late host, a suspended machine).
    Late(#[ephyra(gen = waits())] u64),
    /// A PCP MAP success.
    PcpGrant {
        #[ephyra(gen = lifetimes())]
        lifetime: u32,
        epoch: Ep,
        #[ephyra(gen = gens::int(0u8..=9))]
        ext: u8,
        #[ephyra(gen = gens::bool_with(0.85))]
        our_nonce: bool,
        #[ephyra(gen = ports())]
        port: u16,
    },
    /// A PCP MAP answer with an error result.
    PcpMapError {
        #[ephyra(gen = gens::int(1u8..=13))]
        result: u8,
        epoch: Ep,
        #[ephyra(gen = gens::bool_with(0.7))]
        our_nonce: bool,
    },
    /// A PCP announce: no nonce, answers no request.
    Announce(Ep),
    /// A header-form PCP MAP error: no nonce in this form.
    PcpHeaderError(#[ephyra(gen = gens::int(1u8..=13))] u8, Ep),
    /// A NAT-PMP external address answer.
    NatAddr {
        #[ephyra(gen = gens::pick_from(vec![0u16, 0, 0, 1, 2, 3]))]
        result: u16,
        epoch: Ep,
        #[ephyra(gen = gens::int(0u8..=9))]
        ext: u8,
    },
    /// A NAT-PMP mapping answer.
    NatMap {
        #[ephyra(gen = gens::pick_from(vec![0u16, 0, 0, 1, 2, 3]))]
        result: u16,
        epoch: Ep,
        #[ephyra(gen = lifetimes())]
        lifetime: u32,
        #[ephyra(gen = ports())]
        port: u16,
        #[ephyra(gen = gens::bool_with(0.85))]
        our_port: bool,
    },
    /// A NAT-PMP error answer.
    NatError {
        #[ephyra(gen = gens::int(0u8..=1))]
        opcode: u8,
        #[ephyra(gen = gens::int(1u16..=5))]
        result: u16,
        epoch: Ep,
    },
    /// An SSDP answer: from the gateway naming itself, naming another host, or from another host naming itself.
    Ssdp(#[ephyra(gen = gens::int(0u8..=2))] u8),
    /// The answer to the last HTTP request.
    Http(Answer),
    /// Bytes from the gateway's port.
    Garbage(#[ephyra(gen = bytes(70))] Vec<u8>),
    /// The gateway reboots: its epoch starts again.
    Reboot,
    /// The host stops the client.
    Stop,
    /// The network changed.
    Restart,
}

fn waits() -> impl Gen<Value = u64> {
    gens::pick_from(vec![
        0,
        SEC / 1000,
        SEC / 4,
        SEC,
        5 * SEC,
        60 * SEC,
        300 * SEC,
        1800 * SEC,
        3600 * SEC,
        7200 * SEC,
        86_400 * SEC,
    ])
}

fn lifetimes() -> impl Gen<Value = u32> {
    gens::frequency(vec![
        (4, gens::pick_from(vec![0u32, 1, 2, 30, 120, 3600, 7200, 86_400, 86_401, u32::MAX]).boxed()),
        (1, gens::int(0u32..=u32::MAX).boxed()),
    ])
}

fn ports() -> impl Gen<Value = u16> {
    gens::frequency(vec![
        (4, gens::pick_from(vec![4433u16, 4434, 1, 65_535]).boxed()),
        (1, gens::int(0u16..=65_535).boxed()),
    ])
}

/// How the client is set up.
#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Setup {
    /// 0: a gateway and a private socket; 1: no gateway; 2: a socket on the unspecified address; 3: a public socket.
    #[ephyra(gen = gens::pick_from(vec![0u8, 0, 0, 1, 2, 3]))]
    shape: u8,
    #[ephyra(gen = gens::pick_from(vec![7200u32, 7200, 1, 2, 120, 86_400, 200_000, u32::MAX]))]
    lifetime: u32,
    #[ephyra(gen = gens::int(0u8..=255))]
    nonce0: u8,
    /// The client's clock at the start: a small one, or nanoseconds since 1970.
    #[ephyra(gen = gens::pick_from(vec![1_000 * SEC, 1_700_000_000 * SEC]))]
    t0: u64,
}

fn runs() -> impl Gen<Value = (Setup, Vec<Op>)> {
    (ephyra::any::<Setup>(), gens::vec(ephyra::any::<Op>()).len(0..=60))
}

/// The client, the host around it and what the host saw, with the oracles checked after every step.
struct Host {
    pm: PortMap,
    cfg: Config,
    now: u64,
    /// The latest instant any lease the client was handed could still run to on its clock: the latest grant time
    /// plus the shorter of what was granted and what was asked (and at most the longest lease taken).
    bound: u64,
    /// The times the first and the last map request of the current round left (seen by `drain`); a round ends when
    /// a grant is taken, so the next request starts another.
    round_first: Option<u64>,
    last_left: u64,
    /// When the first request left that led to the mapping held (the earliest the lease can have started).
    lease_first: u64,
    /// The shortest and the longest lifetime, in seconds, a grant handed to the client could carry.
    secs_lo: u64,
    secs_hi: u64,
    boot: u64,
    stopped: bool,
    released: bool,
    ssdp_from: Vec<IpAddr>,
    last_http: Vec<u8>,
}

impl Host {
    fn new(s: &Setup) -> Self {
        let local: SocketAddr = match s.shape {
            2 => "0.0.0.0:4433".parse().unwrap(),
            3 => "198.51.100.20:4433".parse().unwrap(),
            _ => "192.168.1.10:4433".parse().unwrap(),
        };
        let gateway = (s.shape != 1).then_some(IpAddr::V4(GW));
        let mut nonce = [0x5au8; 12];
        nonce[0] = s.nonce0;
        let mut cfg = Config::new(gateway, local, nonce);
        cfg.lifetime = s.lifetime;
        let pm = PortMap::new(cfg, s.t0);
        Self {
            pm,
            cfg,
            now: s.t0,
            bound: 0,
            round_first: None,
            last_left: 0,
            lease_first: 0,
            secs_lo: u64::MAX,
            secs_hi: 0,
            boot: s.t0.saturating_sub(5000 * SEC),
            stopped: false,
            released: false,
            ssdp_from: Vec::new(),
            last_http: Vec::new(),
        }
    }

    fn epoch(&self, e: &Ep) -> u32 {
        match e {
            Ep::Steady => u32::try_from(self.now.saturating_sub(self.boot) / SEC).unwrap_or(u32::MAX),
            Ep::Back(k) => *k,
            Ep::Any(v) => *v,
        }
    }

    /// A grant of `lifetime` seconds was handed over now: the lease it can make ends no later than this.
    fn granted(&mut self, lifetime: u32) {
        let secs = lifetime.min(self.cfg.lifetime.max(1)).min(MAX_LIFETIME);
        self.bound = self.bound.max(self.now.saturating_add(u64::from(secs) * SEC));
        self.secs_lo = self.secs_lo.min(u64::from(secs));
        self.secs_hi = self.secs_hi.max(u64::from(secs));
    }

    /// A map request left the client now.
    fn left(&mut self) {
        self.round_first.get_or_insert(self.now);
        self.last_left = self.now;
    }

    fn gw(&self) -> SocketAddr {
        SocketAddr::new(IpAddr::V4(GW), PORT)
    }

    fn datagram(&mut self, b: &[u8]) {
        let from = self.gw();
        self.pm.handle_datagram(self.now, from, b);
    }

    /// The right answer to the last HTTP request, as a working gateway gives it.
    fn right_answer(&self, ext: Ipv4Addr) -> Vec<u8> {
        let req = &self.last_http;
        let body: String = if req.starts_with(b"GET ") {
            "<root><device><serviceList><service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>/ctl/IPConn</controlURL></service></serviceList></device></root>".into()
        } else if contains(req, b"GetExternalIPAddress") {
            format!("<s:Envelope><s:Body><u:GetExternalIPAddressResponse><NewExternalIPAddress>{ext}</NewExternalIPAddress></u:GetExternalIPAddressResponse></s:Body></s:Envelope>")
        } else {
            "<s:Envelope><s:Body></s:Body></s:Envelope>".into()
        };
        format!("HTTP/1.1 200 OK\r\nContent-Type: text/xml\r\nContent-Length: {}\r\n\r\n{body}", body.len()).into_bytes()
    }

    /// Everything the client wants sent now, checked: datagrams go to the gateway's port or the SSDP group, HTTP only
    /// to a host that answered the search; after stop only the release, and nothing after it.
    fn drain(&mut self) {
        let mut buf = [0u8; pinc_portmap::MAX_DATAGRAM];
        let mut n = 0;
        while let Some((to, len)) = self.pm.poll_datagram(&mut buf) {
            n += 1;
            assert!(n <= 4, "poll_datagram keeps handing out datagrams");
            assert!(len <= pinc_portmap::MAX_DATAGRAM);
            let d = &buf[..len];
            assert!(to == self.gw() || to == SSDP, "a datagram to {to}");
            let map_request = pcp::decode_request(d).map(|r| r.lifetime > 0).unwrap_or(false)
                || natpmp::decode_request(d).is_ok_and(|r| matches!(r, natpmp::Request::Map { lifetime, .. } if lifetime > 0));
            if to == self.gw() && map_request {
                self.left();
            }
            if self.stopped {
                assert!(!self.released || !self.pm.stopped(), "a datagram after the release went out");
                let release = pcp::decode_request(d).map(|r| r.lifetime == 0).unwrap_or(false)
                    || natpmp::decode_request(d)
                        .map(|r| matches!(r, natpmp::Request::Map { lifetime: 0, .. }))
                        .unwrap_or(false);
                assert!(release, "after stop the client sent a datagram that is not a release: {d:?}");
            }
        }
        if self.stopped && self.pm.stopped() {
            self.released = true;
        }
        let mut req = [0u8; upnp::MAX_REQUEST];
        if let Some((to, len)) = self.pm.poll_http(&mut req) {
            assert!(len <= upnp::MAX_REQUEST);
            assert!(self.ssdp_from.contains(&to.ip()), "HTTP to {to}, a host that did not answer the search");
            let r = req[..len].to_vec();
            if contains(&r, b"AddPortMapping") {
                self.left();
            }
            if self.stopped {
                assert!(contains(&r, b"DeletePortMapping"), "after stop the client sent HTTP that is not the delete");
            }
            self.last_http = r;
        }
    }

    fn step(&mut self, op: &Op) {
        let before = (self.pm.mapped(), self.pm.protocol());
        let mut nonce_less = false;
        let mut timer = false;
        match op {
            Op::Timer => {
                if let Some(t) = self.pm.poll_timeout() {
                    self.now = self.now.max(t);
                }
                self.pm.handle_timeout(self.now);
                timer = true;
            }
            Op::Wait(dt) => {
                self.now = self.now.saturating_add(*dt);
                self.pm.handle_timeout(self.now);
                timer = true;
            }
            Op::Late(dt) => {
                self.now = self.now.saturating_add(*dt);
                return;
            }
            Op::PcpGrant {
                lifetime,
                epoch,
                ext,
                our_nonce,
                port,
            } => {
                let r = pcp::Response::Map {
                    result: pcp::SUCCESS,
                    lifetime: *lifetime,
                    epoch: self.epoch(epoch),
                    nonce: if *our_nonce { self.cfg.nonce } else { FOREIGN_NONCE },
                    protocol: pcp::UDP,
                    internal_port: self.cfg.local.port(),
                    external_port: *port,
                    external_ip: EXT_IPS[usize::from(*ext) % EXT_IPS.len()],
                };
                let mut b = [0u8; 60];
                let n = pcp::encode_response(&r, &mut b).unwrap();
                if *our_nonce {
                    self.granted(*lifetime);
                } else {
                    nonce_less = true;
                }
                self.datagram(&b[..n]);
            }
            Op::PcpMapError {
                result,
                epoch,
                our_nonce,
            } => {
                let r = pcp::Response::Map {
                    result: *result,
                    lifetime: 0,
                    epoch: self.epoch(epoch),
                    nonce: if *our_nonce { self.cfg.nonce } else { FOREIGN_NONCE },
                    protocol: pcp::UDP,
                    internal_port: self.cfg.local.port(),
                    external_port: 0,
                    external_ip: IpAddr::V4(Ipv4Addr::UNSPECIFIED),
                };
                let mut b = [0u8; 60];
                let n = pcp::encode_response(&r, &mut b).unwrap();
                nonce_less = !*our_nonce;
                self.datagram(&b[..n]);
            }
            Op::Announce(e) => {
                let r = pcp::Response::Header {
                    opcode: pcp::OP_ANNOUNCE,
                    result: 0,
                    lifetime: 0,
                    epoch: self.epoch(e),
                };
                let mut b = [0u8; 24];
                let n = pcp::encode_response(&r, &mut b).unwrap();
                nonce_less = true;
                self.datagram(&b[..n]);
            }
            Op::PcpHeaderError(result, e) => {
                let r = pcp::Response::Header {
                    opcode: pcp::OP_MAP,
                    result: *result,
                    lifetime: 0,
                    epoch: self.epoch(e),
                };
                let mut b = [0u8; 24];
                let n = pcp::encode_response(&r, &mut b).unwrap();
                nonce_less = true;
                self.datagram(&b[..n]);
            }
            Op::NatAddr { result, epoch, ext } => {
                let r = natpmp::Response::Address {
                    result: *result,
                    epoch: self.epoch(epoch),
                    ip: v4_ext(*ext),
                };
                self.nat(&r);
                nonce_less = true;
            }
            Op::NatMap {
                result,
                epoch,
                lifetime,
                port,
                our_port,
            } => {
                let r = natpmp::Response::Map {
                    result: *result,
                    epoch: self.epoch(epoch),
                    internal_port: if *our_port { self.cfg.local.port() } else { 9 },
                    external_port: *port,
                    lifetime: *lifetime,
                };
                self.granted(*lifetime);
                self.nat(&r);
                nonce_less = true;
            }
            Op::NatError { opcode, result, epoch } => {
                let r = natpmp::Response::Error {
                    opcode: *opcode,
                    result: *result,
                    epoch: self.epoch(epoch),
                };
                self.nat(&r);
                nonce_less = true;
            }
            Op::Ssdp(kind) => {
                let (from, named) = match kind {
                    0 => (GW, GW),
                    1 => (GW, OTHER),
                    _ => (OTHER, OTHER),
                };
                let answer = format!(
                    "HTTP/1.1 200 OK\r\nCACHE-CONTROL: max-age=120\r\nLOCATION: http://{named}:5000/rootDesc.xml\r\nST: urn:schemas-upnp-org:device:InternetGatewayDevice:1\r\n\r\n"
                );
                // Only an answer that names its own host may lead to HTTP.
                if from == named {
                    self.ssdp_from.push(IpAddr::V4(from));
                }
                self.pm
                    .handle_datagram(self.now, SocketAddr::new(IpAddr::V4(from), 1900), answer.as_bytes());
            }
            Op::Http(a) => {
                let right = self.right_answer(v4_ext(0));
                let resp: Option<Vec<u8>> = match a {
                    Answer::Right => Some(right),
                    Answer::ExtIp(i) => Some(self.right_answer(v4_ext(*i))),
                    Answer::Fault(code) => Some(
                        format!("HTTP/1.1 500 Internal Server Error\r\n\r\n<s:Envelope><s:Body><s:Fault><detail><UPnPError><errorCode>{code}</errorCode></UPnPError></detail></s:Fault></s:Body></s:Envelope>")
                            .into_bytes(),
                    ),
                    Answer::Status404 => Some(b"HTTP/1.1 404 Not Found\r\n\r\n".to_vec()),
                    Answer::Cut(n) => Some(right[..*n.min(&right.len())].to_vec()),
                    Answer::Flip(at, x) => {
                        let mut r = right;
                        let i = at % r.len();
                        r[i] ^= x;
                        Some(r)
                    }
                    Answer::Garbage(g) => Some(g.clone()),
                    Answer::Fail => None,
                };
                let ok = resp
                    .as_deref()
                    .and_then(upnp::soap_result)
                    .is_some_and(|r| matches!(r, upnp::SoapResult::Ok(_)));
                if self.pm.awaiting_http() && ok && contains(&self.last_http, b"AddPortMapping") {
                    self.granted(self.cfg.lifetime);
                }
                self.pm.handle_http(self.now, resp.as_deref());
            }
            Op::Garbage(b) => {
                nonce_less = true;
                self.datagram(b);
            }
            // like `Late`, no call reaches the client, so nothing is owed at `now` yet
            Op::Reboot => {
                self.boot = self.now;
                return;
            }
            Op::Stop => {
                self.stopped = true;
                self.pm.stop(self.now);
            }
            Op::Restart => self.pm.restart(self.now),
        }
        let now = self.now;
        if matches!(op, Op::Stop | Op::Restart) {
            self.round_first = None;
        }
        let took = matches!(op, Op::PcpGrant { our_nonce: true, .. } | Op::NatMap { .. } | Op::Http(_));
        if took && self.pm.mapped().is_some() {
            // the earliest request the lease can have come from: kept across a renewal, as the client keeps it
            let first = self.round_first.take();
            self.lease_first = match (before.0, first) {
                (Some(_), Some(f)) => self.lease_first.min(f),
                (None, Some(f)) => f,
                _ => self.lease_first,
            };
        }
        if let Some(ext) = self.pm.mapped() {
            assert!(!self.stopped, "a stopped client reports a mapping");
            // a lease is no longer than the longest grant, counted from the last request that left
            assert!(
                now < self.last_left.saturating_add(self.secs_hi.saturating_mul(SEC)),
                "at {now} the client reports {ext}, whose lease runs past the last request ({}) plus {} s",
                self.last_left,
                self.secs_hi
            );
            if timer {
                assert!(now < self.bound, "after the timer at {now} the client reports {ext}, whose lease ends by {}", self.bound);
            } else {
                assert!(now < self.bound, "at {now} the client reports {ext}, whose lease ended by {} on its clock", self.bound);
            }
        }
        if nonce_less && before.1 == Some(Proto::Pcp) {
            let ended = self.pm.mapped().is_none()
                && now >= self.lease_first.saturating_add(self.secs_lo.saturating_mul(SEC));
            assert!(
                ended || self.pm.mapped() == before.0,
                "a datagram without this client's nonce changed the PCP mapping held"
            );
        }
        self.drain();
    }

    fn nat(&mut self, r: &natpmp::Response) {
        let mut b = [0u8; 16];
        let n = natpmp::encode_response(r, &mut b).unwrap();
        self.datagram(&b[..n]);
    }
}

fn contains(hay: &[u8], needle: &[u8]) -> bool {
    hay.windows(needle.len()).any(|w| w == needle)
}

#[ephyra::test(gen = runs(), tests = 3000)]
fn client_keeps_its_lease_and_nonce_invariants(run: (Setup, Vec<Op>)) {
    let (setup, ops) = run;
    let mut h = Host::new(&setup);
    h.drain();
    for op in &ops {
        h.step(op);
    }
}

/// The same run with the two known causes taken out (see `repro_portmap.rs`), so other failures at the same checks
/// surface: the host runs its timer before anything else (a `Late` becomes a `Wait`), and the header-form PCP error
/// becomes a garbage datagram of the same length.
#[ephyra::test(gen = runs(), tests = 3000)]
fn client_invariants_with_a_timely_host_and_no_header_errors(run: (Setup, Vec<Op>)) {
    let (setup, ops) = run;
    let mut h = Host::new(&setup);
    h.drain();
    for op in &ops {
        let op = match op {
            Op::Late(dt) => Op::Wait(*dt),
            Op::PcpHeaderError(..) => Op::Garbage(vec![0xff; 24]),
            other => other.clone(),
        };
        h.step(&op);
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Codecs.

fn ip_any() -> impl Gen<Value = IpAddr> {
    gens::frequency(vec![
        (3, gens::int(0u32..=u32::MAX).map(|v| IpAddr::V4(Ipv4Addr::from(v))).boxed()),
        (
            1,
            (gens::int(0u64..=u64::MAX), gens::int(0u64..=u64::MAX))
                .map(|(a, b)| IpAddr::V6(Ipv6Addr::from((u128::from(a) << 64) | u128::from(b))).to_canonical())
                .boxed(),
        ),
    ])
}

fn pcp_responses() -> impl Gen<Value = pcp::Response> {
    (move |g: &mut Source| {
        if g.bool_with(0.7) {
            let mut nonce = [0u8; 12];
            nonce.iter_mut().for_each(|b| *b = g.int(0u8..=255));
            pcp::Response::Map {
                result: g.int(0u8..=255),
                lifetime: g.int(0u32..=u32::MAX),
                epoch: g.int(0u32..=u32::MAX),
                nonce,
                protocol: g.int(0u8..=255),
                internal_port: g.int(0u16..=65_535),
                external_port: g.int(0u16..=65_535),
                external_ip: g.draw(&ip_any()),
            }
        } else {
            let opcode = *g.pick(&[pcp::OP_ANNOUNCE, pcp::OP_MAP]);
            let result = if opcode == pcp::OP_MAP { g.int(1u8..=255) } else { g.int(0u8..=255) };
            pcp::Response::Header {
                opcode,
                result,
                lifetime: g.int(0u32..=u32::MAX),
                epoch: g.int(0u32..=u32::MAX),
            }
        }
    })
    .boxed()
}

#[ephyra::test(gen = pcp_responses(), tests = 5000)]
fn pcp_response_decode_inverts_encode(r: pcp::Response) {
    let mut b = [0u8; 64];
    let n = pcp::encode_response(&r, &mut b).unwrap();
    assert_eq!(pcp::decode_response(&b[..n]), Ok(r));
}

fn pcp_response_bytes() -> ephyra::BoxGen<Vec<u8>> {
    mostly_valid(|g: &mut Source| {
        let r = g.draw(&pcp_responses());
        let mut b = [0u8; 64];
        let n = pcp::encode_response(&r, &mut b).unwrap_or(0);
        b[..n].to_vec()
    })
}

#[ephyra::test(gen = pcp_response_bytes(), tests = 20_000)]
fn pcp_response_accepts_only_its_own_encodings(b: Vec<u8>) {
    let Ok(r) = pcp::decode_response(&b) else { return };
    let mut out = [0u8; 64];
    let n = pcp::encode_response(&r, &mut out).unwrap();
    // An IPv4-mapped address decodes as the IPv4 address and encodes back to the same 16 bytes.
    assert_eq!(&out[..n], &b[..], "decode accepted bytes that encode does not produce for {r:?}");
}

fn nat_responses() -> impl Gen<Value = natpmp::Response> {
    (move |g: &mut Source| match g.int(0u8..=2) {
        0 => natpmp::Response::Address {
            result: g.int(0u16..=65_535),
            epoch: g.int(0u32..=u32::MAX),
            ip: Ipv4Addr::from(g.int(0u32..=u32::MAX)),
        },
        1 => natpmp::Response::Map {
            result: g.int(0u16..=65_535),
            epoch: g.int(0u32..=u32::MAX),
            internal_port: g.int(0u16..=65_535),
            external_port: g.int(0u16..=65_535),
            lifetime: g.int(0u32..=u32::MAX),
        },
        _ => natpmp::Response::Error {
            opcode: g.int(0u8..=127),
            result: g.int(1u16..=65_535),
            epoch: g.int(0u32..=u32::MAX),
        },
    })
    .boxed()
}

fn nat_response_bytes() -> ephyra::BoxGen<Vec<u8>> {
    mostly_valid(|g: &mut Source| {
        let r = g.draw(&nat_responses());
        let mut b = [0u8; 16];
        let n = natpmp::encode_response(&r, &mut b).unwrap_or(0);
        b[..n].to_vec()
    })
}

#[ephyra::test(gen = nat_response_bytes(), tests = 20_000)]
fn natpmp_response_decode_and_encode_agree(b: Vec<u8>) {
    let Ok(r) = natpmp::decode_response(&b) else { return };
    let mut out = [0u8; 16];
    let n = natpmp::encode_response(&r, &mut out).unwrap();
    assert_eq!(&out[..n], &b[..], "decode accepted bytes that encode does not produce for {r:?}");
}

#[ephyra::test(gen = nat_responses(), tests = 5000)]
fn natpmp_response_decode_inverts_encode(r: natpmp::Response) {
    let mut b = [0u8; 16];
    let n = natpmp::encode_response(&r, &mut b).unwrap();
    assert_eq!(natpmp::decode_response(&b[..n]), Ok(r));
}

fn pcp_requests() -> impl Gen<Value = pcp::MapRequest> {
    (move |g: &mut Source| {
        let mut nonce = [0u8; 12];
        nonce.iter_mut().for_each(|b| *b = g.int(0u8..=255));
        pcp::MapRequest {
            lifetime: g.int(0u32..=u32::MAX),
            client: g.draw(&ip_any()),
            nonce,
            protocol: g.int(0u8..=255),
            internal_port: g.int(0u16..=65_535),
            external_port: g.int(0u16..=65_535),
            external_ip: g.draw(&ip_any()),
        }
    })
    .boxed()
}

fn pcp_request_bytes() -> ephyra::BoxGen<Vec<u8>> {
    mostly_valid(|g: &mut Source| {
        let r = g.draw(&pcp_requests());
        let mut b = [0u8; 64];
        let n = pcp::encode_request(&r, &mut b).unwrap_or(0);
        b[..n].to_vec()
    })
}

#[ephyra::test(gen = pcp_requests(), tests = 5000)]
fn pcp_request_decode_inverts_encode(r: pcp::MapRequest) {
    let mut b = [0u8; 64];
    let n = pcp::encode_request(&r, &mut b).unwrap();
    assert_eq!(pcp::decode_request(&b[..n]), Ok(r));
}

#[ephyra::test(gen = pcp_request_bytes(), tests = 20_000)]
fn pcp_request_accepts_only_its_own_encodings(b: Vec<u8>) {
    let Ok(r) = pcp::decode_request(&b) else { return };
    let mut out = [0u8; 64];
    let n = pcp::encode_request(&r, &mut out).unwrap();
    assert_eq!(&out[..n], &b[..], "decode accepted bytes that encode does not produce for {r:?}");
}

fn nat_requests() -> impl Gen<Value = natpmp::Request> {
    (move |g: &mut Source| {
        if g.bool() {
            natpmp::Request::Address
        } else {
            natpmp::Request::Map {
                internal_port: g.int(0u16..=65_535),
                external_port: g.int(0u16..=65_535),
                lifetime: g.int(0u32..=u32::MAX),
            }
        }
    })
    .boxed()
}

fn nat_request_bytes() -> ephyra::BoxGen<Vec<u8>> {
    mostly_valid(|g: &mut Source| {
        let r = g.draw(&nat_requests());
        let mut b = [0u8; 16];
        let n = natpmp::encode_request(&r, &mut b).unwrap_or(0);
        b[..n].to_vec()
    })
}

#[ephyra::test(gen = nat_request_bytes(), tests = 20_000)]
fn natpmp_request_decode_and_encode_agree(b: Vec<u8>) {
    let Ok(r) = natpmp::decode_request(&b) else { return };
    let mut out = [0u8; 16];
    let n = natpmp::encode_request(&r, &mut out).unwrap();
    assert_eq!(&out[..n], &b[..], "decode accepted bytes that encode does not produce for {r:?}");
    assert_eq!(natpmp::decode_request(&out[..n]), Ok(r));
}

// ---------------------------------------------------------------------------------------------------------------
// UPnP text.

/// A dotted IPv4 address, sometimes an unusable one.
fn host_ip(g: &mut Source) -> Ipv4Addr {
    if g.bool_with(0.7) {
        Ipv4Addr::new(192, 168, g.int(0u8..=255), g.int(1u8..=254))
    } else {
        *g.pick(&[
            Ipv4Addr::new(127, 0, 0, 1),
            Ipv4Addr::new(0, 0, 0, 0),
            Ipv4Addr::new(224, 0, 0, 251),
            Ipv4Addr::new(255, 255, 255, 255),
            Ipv4Addr::new(169, 254, 3, 4),
            Ipv4Addr::new(203, 0, 113, 1),
        ])
    }
}

fn path(g: &mut Source) -> String {
    let n = g.int(0usize..=140);
    let mut p = String::from("/");
    for _ in 0..n {
        p.push(*g.pick(&['a', 'Z', '0', '.', '/', '-', '_', '?', '=', '%', ' ', '\t', ':']));
    }
    p
}

fn location(g: &mut Source) -> String {
    let ip = host_ip(g);
    let port = match g.int(0u8..=3) {
        0 => String::new(),
        1 => format!(":{}", g.int(0u32..=70_000)),
        2 => ":5000".into(),
        _ => format!(":{}", g.int(0u16..=65_535)),
    };
    let scheme = *g.pick(&["http://", "HTTP://", "https://", "http:/", ""]);
    format!("{scheme}{ip}{port}{}", if g.bool() { path(g) } else { String::new() })
}

fn ssdp_answers() -> ephyra::BoxGen<Vec<u8>> {
    mostly_valid(|g: &mut Source| {
        let status = *g.pick(&["HTTP/1.1 200 OK", "HTTP/1.1 200", "HTTP/1.0 200 OK", "HTTP/1.1 404 Not Found"]);
        let loc = location(g);
        let name = *g.pick(&["LOCATION", "Location", "location", " LOCATION "]);
        format!("{status}\r\nCACHE-CONTROL: max-age=120\r\n{name}: {loc}\r\nST: upnp:rootdevice\r\n\r\n").into_bytes()
    })
}

#[ephyra::test(gen = ssdp_answers(), tests = 20_000)]
fn ssdp_location_names_only_usable_hosts(b: Vec<u8>) {
    let Some(url) = upnp::ssdp_location(&b) else { return };
    let IpAddr::V4(ip) = url.addr.ip() else { panic!("an IPv6 location") };
    assert!(pinc_portmap::addr::usable_host(ip), "a location on {ip}");
    assert_ne!(url.addr.port(), 0);
    assert!(!url.path().is_empty() && url.path().len() <= upnp::MAX_PATH);
    assert!(url.path().iter().all(u8::is_ascii_graphic));
    // What a description URL prints parses back to itself.
    let printed = format!("http://{}{}", url.addr, String::from_utf8_lossy(url.path()));
    assert_eq!(upnp::parse_location(printed.as_bytes()), Some(url));
}

fn descriptions() -> ephyra::BoxGen<Vec<u8>> {
    mostly_valid(|g: &mut Source| {
        let mut d = String::from("<?xml version=\"1.0\"?><root><device><serviceList>");
        for _ in 0..g.int(0u8..=3) {
            let ty = *g.pick(&[
                "urn:schemas-upnp-org:service:WANIPConnection:1",
                "urn:schemas-upnp-org:service:WANIPConnection:2",
                "urn:schemas-upnp-org:service:WANPPPConnection:1",
                "urn:schemas-upnp-org:service:Layer3Forwarding:1",
            ]);
            let ctl = match g.int(0u8..=3) {
                0 => path(g),
                1 => format!("http://{}:{}{}", host_ip(g), g.int(1u16..=65_535), path(g)),
                2 => "ctl/IPConn".into(),
                _ => location(g),
            };
            let prefix = *g.pick(&["", "u:", "ns0:"]);
            d.push_str(&format!(
                "<service><{prefix}serviceType>{ty}</{prefix}serviceType><controlURL>{ctl}</controlURL></service>"
            ));
        }
        d.push_str("</serviceList></device></root>");
        d.into_bytes()
    })
}

#[ephyra::test(gen = descriptions(), tests = 20_000)]
fn control_url_is_on_the_description_host(desc: Vec<u8>) {
    let base = Url::new(SocketAddr::new(IpAddr::V4(GW), 5000), b"/rootDesc.xml").unwrap();
    let Some((ctl, svc)) = upnp::control_of(&desc, &base) else { return };
    assert!(svc < upnp::SERVICES.len());
    assert_eq!(ctl.addr.ip(), base.addr.ip(), "a control URL on another host was taken");
    assert!(!ctl.path().is_empty() && ctl.path().len() <= upnp::MAX_PATH);
    // A request built for it stays within its bound and its path cannot end the request line.
    let mut out = [0u8; upnp::MAX_REQUEST];
    if let Some(n) = upnp::soap(&ctl, svc, &upnp::Call::ExternalIp, &mut out) {
        let line_end = out[..n].windows(2).position(|w| w == b"\r\n").unwrap();
        assert_eq!(out[..line_end].iter().filter(|c| **c == b' ').count(), 2, "the request line has extra spaces");
    }
}

fn http_answers() -> ephyra::BoxGen<Vec<u8>> {
    mostly_valid(|g: &mut Source| {
        let status = *g.pick(&["200 OK", "500 Internal Server Error", "404 Not Found", "200"]);
        let body = match g.int(0u8..=2) {
            0 => format!("<NewExternalIPAddress>{}</NewExternalIPAddress>", host_ip(g)),
            1 => format!("<s:Fault><errorCode>{}</errorCode></s:Fault>", g.int(0u32..=99_999)),
            _ => String::from_utf8_lossy(&g.draw(&bytes(40))).into_owned(),
        };
        let cl = match g.int(0u8..=3) {
            0 => format!("Content-Length: {}\r\n", body.len()),
            1 => format!("content-length: {}\r\n", g.int(0u32..=u32::MAX)),
            2 => format!("Content-Length: {}\r\n", g.int(0usize..=body.len() + 3)),
            _ => String::new(),
        };
        format!("HTTP/1.{} {status}\r\nServer: x\r\n{cl}\r\n{body}", g.int(0u8..=1)).into_bytes()
    })
}

#[ephyra::test(gen = http_answers(), tests = 20_000)]
fn http_answers_parse_within_their_bytes(b: Vec<u8>) {
    // Reference: "The status code and the body of an HTTP response (the body cut at `Content-Length` when that is
    // shorter)": the body starts after the first blank line and runs to the end or to Content-Length.
    if let Some((status, body)) = upnp::http_response(&b) {
        let head_end = b.windows(4).position(|w| w == b"\r\n\r\n").unwrap();
        let full = &b[head_end + 4..];
        assert_eq!(&full[..body.len()], body, "the body is not what follows the head");
        assert_eq!(std::str::from_utf8(&b[9..12]).ok().and_then(|s| s.parse().ok()), Some(status));
    }
    if let Some(upnp::SoapResult::Ok(body)) = upnp::soap_result(&b) {
        let _ = upnp::external_ip(body);
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Lease arithmetic.

fn epochs_and_times() -> impl Gen<Value = (u64, u32, u64, u32)> {
    (
        gens::frequency(vec![(1, gens::edges(0u64..=u64::MAX).boxed()), (3, gens::int(0u64..=u64::MAX).boxed())]),
        gens::frequency(vec![(1, gens::edges(0u32..=u32::MAX).boxed()), (3, gens::int(0u32..=u32::MAX).boxed())]),
        gens::frequency(vec![(1, gens::edges(0u64..=u64::MAX).boxed()), (3, gens::int(0u64..=u64::MAX).boxed())]),
        gens::frequency(vec![(1, gens::edges(0u32..=u32::MAX).boxed()), (3, gens::int(0u32..=u32::MAX).boxed())]),
    )
}

#[ephyra::test(gen = epochs_and_times(), tests = 20_000)]
fn lease_arithmetic_never_overflows(x: (u64, u32, u64, u32)) {
    let (at, server, now, lifetime) = x;
    let _ = lease::restarted(Epoch { at, server }, now, server.wrapping_add(lifetime));
    let _ = lease::restarted(Epoch { at, server }, now, lifetime);
    let (r, e) = (lease::renew_at(at, lifetime), lease::expiry(at, lifetime));
    assert!(r <= e);
    // Invariant of `lease`: "renew_at of a lease of at least one second is strictly before its expiry", for every
    // start a lease of the longest length still fits after.
    if lifetime >= 1 && at <= u64::MAX - u64::from(MAX_LIFETIME) * SEC {
        assert!(r < e, "renew_at({at}, {lifetime}) = {r} is not before expiry {e}");
    }
    // Hearing the same epoch at the same time is no restart.
    assert!(!lease::restarted(Epoch { at, server }, at, server));
}
