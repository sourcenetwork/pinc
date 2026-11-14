//! The port-mapping client: one UDP mapping of the node's socket, asked for with PCP, then NAT-PMP, then `UPnP`-IGD.
//!
//! **Asking.** With the gateway's address known, the client sends a PCP MAP request to it (three tries, 250 ms apart
//! and doubling). A NAT-PMP answer to it, an unsupported-version result, or silence moves on to NAT-PMP: the external
//! address request, then the UDP mapping request. Silence or a refusal there moves on to `UPnP`: an SSDP search, the
//! gateway's description, its external address and `AddPortMapping`, over HTTP the host carries ([`PortMap::poll_http`]).
//! PCP and `UPnP` need the client's own address (it is in their messages), so a socket on the unspecified address tries
//! NAT-PMP only; with no gateway known only `UPnP` is tried, and an answer from another address than the gateway's is
//! not taken (with none known, a search answer is taken only from a private address). `UPnP` searches only from a private IPv4 address, takes a description only from the host that answered
//! (and the gateway's, when it is known), and sends HTTP to no other host. When every protocol failed the client tries again after [`RETRY`].
//!
//! A grant whose external address no peer on the internet could send to (unspecified, loopback, multicast, link-local or
//! private, [`addr::external_ok`]) is refused: it is not held, and the client goes on to the next protocol.
//!
//! **Holding.** A grant is a lease that started when its request first left, so it ends on the client's clock no
//! later than on the gateway's ([`crate::lease`]); it is as long as the shorter of what the gateway granted and what
//! was asked. The client renews half way with the protocol that granted
//! it; a renewal that fails is tried again half way to the end, and a lease that reaches its end is gone: the client
//! drops the mapping and starts asking from the beginning.
//!
//! **A gateway that restarted.** Every PCP and NAT-PMP answer to a request carries the gateway's epoch. An answer that
//! shows the gateway lost its mappings ([`lease::restarted`]) drops a held mapping at once and asks again, unless the
//! answer is itself the grant that renews it. A PCP announce is no answer to a request and has no nonce: while a
//! mapping is held it brings the renewal forward once a round and changes nothing else, and in any other step it is
//! dropped and counted.
//!
//! **Releasing.** [`PortMap::stop`] drops the mapping and asks the gateway to delete it: PCP and NAT-PMP with a
//! lifetime of 0, `UPnP` with `DeletePortMapping`. The client does nothing more afterwards.
//!
//! Invariants: [`PortMap::mapped`] is a mapping the gateway granted and whose lease has not ended on the client's clock,
//! and none after [`PortMap::stop`]; an answer is taken only from the gateway (or, for SSDP, from port 1900 of it) and
//! only for the request in flight (PCP by its nonce, protocol and port; NAT-PMP by its opcode and port); every buffer is
//! bounded and nothing allocates or panics; everything the client drops is counted in [`Stats`].

use core::net::{IpAddr, Ipv4Addr, SocketAddr};

use crate::addr;
use crate::lease::{self, Epoch, SEC};
use crate::natpmp;
use crate::pcp;
use crate::upnp::{self, Call, SoapResult, Url};

/// The port PCP and NAT-PMP servers listen on.
pub const PORT: u16 = 5351;
/// The lease asked for, in seconds.
pub const LIFETIME: u32 = 7200;
/// The tries of one request.
pub const TRIES: u8 = 3;
/// The wait after the first try of a PCP or NAT-PMP request; it doubles after each.
pub const FIRST_GAP: u64 = 250_000_000;
/// The wait after each SSDP search.
pub const SSDP_GAP: u64 = SEC;
/// How long an HTTP exchange may take.
pub const HTTP_WAIT: u64 = 3 * SEC;
/// The wait before asking again when every protocol failed.
pub const RETRY: u64 = 300 * SEC;
/// The external ports `AddPortMapping` tries when the gateway says the port is taken.
pub const CONFLICT_TRIES: u8 = 3;

/// A protocol that maps ports.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Proto {
    /// PCP, RFC 6887.
    Pcp,
    /// NAT-PMP, RFC 6886.
    NatPmp,
    /// `UPnP`-IGD.
    Upnp,
}

/// What the client dropped, by reason.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Stats {
    /// Search answers that name another host than the one that answered.
    pub wrong_source: u64,
    /// PCP answers whose nonce is not this client's.
    pub wrong_nonce: u64,
    /// Answers that did not decode or did not answer the request in flight (step, protocol or port).
    pub unexpected: u64,
    /// Grants of an external address no peer could reach.
    pub refused_address: u64,
    /// Requests that ran out of tries and HTTP exchanges that passed their deadline.
    pub timeouts: u64,
    /// HTTP exchanges that failed or whose answer was refused.
    pub http_failures: u64,
}

/// Count one more in `c`.
fn bump(c: &mut u64) {
    *c = c.saturating_add(1);
}

/// How the client is set up.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Config {
    /// The default gateway, when the host knows it.
    pub gateway: Option<IpAddr>,
    /// The node's socket: the address in PCP and `UPnP` requests and the port mapped.
    pub local: SocketAddr,
    /// The lease asked for, in seconds.
    pub lifetime: u32,
    /// The PCP mapping nonce: random, the same for every request of this client.
    pub nonce: [u8; 12],
}

impl Config {
    /// A client for the socket `local` behind `gateway`, asking for [`LIFETIME`]. An IPv4-mapped IPv6 gateway is
    /// the IPv4 address it maps, so its answers are told from the requests it was sent.
    pub const fn new(gateway: Option<IpAddr>, local: SocketAddr, nonce: [u8; 12]) -> Self {
        Self {
            gateway: match gateway {
                Some(g) => Some(g.to_canonical()),
                None => None,
            },
            local,
            lifetime: LIFETIME,
            nonce,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Step {
    Pcp,
    NatAddr,
    NatMap,
    Ssdp,
    Desc,
    ExtIp,
    Add,
    Delete,
    Held,
    Idle,
    Stopped,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Http {
    None,
    Due,
    Sent,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Lease {
    proto: Proto,
    ext: SocketAddr,
    renew: u64,
    expiry: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Igd {
    desc: Url,
    ctl: Option<(Url, usize)>,
    ext_ip: Option<Ipv4Addr>,
    external: u16,
    permanent: bool,
    conflicts: u8,
}

/// The port-mapping client of one socket.
#[derive(Debug, Clone)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "the flags of one state machine, each set and read in few places"
)]
pub struct PortMap {
    cfg: Config,
    step: Step,
    renewing: bool,
    tries: u8,
    next: Option<u64>,
    send: bool,
    http: Http,
    started: u64,
    now: u64,
    held: Option<Lease>,
    epoch: Option<Epoch>,
    nat_ip: Option<Ipv4Addr>,
    igd: Option<Igd>,
    /// Releases not sent yet: a restart's and a stop's can wait together.
    releases: [Option<Lease>; 2],
    /// The held mapping's renewal was brought forward by an announce since it was granted.
    announced: bool,
    halted: bool,
    stats: Stats,
}

impl PortMap {
    /// A client that starts asking at `now`.
    pub fn new(cfg: Config, now: u64) -> Self {
        let mut pm = Self {
            cfg,
            step: Step::Idle,
            renewing: false,
            tries: 0,
            next: None,
            send: false,
            http: Http::None,
            started: now,
            now,
            held: None,
            epoch: None,
            nat_ip: None,
            igd: None,
            releases: [None; 2],
            announced: false,
            halted: false,
            stats: Stats::default(),
        };
        pm.enter(pm.first(), now);
        pm
    }

    /// The external address of the mapping held, if any.
    pub fn mapped(&self) -> Option<SocketAddr> {
        self.held.map(|l| l.ext)
    }

    /// The protocol of the mapping held.
    pub fn protocol(&self) -> Option<Proto> {
        self.held.map(|l| l.proto)
    }

    /// What the client dropped.
    pub fn stats(&self) -> Stats {
        self.stats
    }

    /// Whether the client waits for the answer to the HTTP request it last gave out: false once it gave the exchange
    /// up, so the host drops what it still runs for it.
    pub fn awaiting_http(&self) -> bool {
        self.http == Http::Sent
    }

    /// Whether the client stopped and sent its release.
    pub fn stopped(&self) -> bool {
        self.step == Step::Stopped && self.releases.iter().all(Option::is_none)
    }

    fn gateway(&self) -> Option<SocketAddr> {
        self.cfg.gateway.map(|g| SocketAddr::new(g, PORT))
    }

    fn client_v4(&self) -> Option<Ipv4Addr> {
        match self.cfg.local.ip().to_canonical() {
            IpAddr::V4(v4) if !v4.is_unspecified() => Some(v4),
            _ => None,
        }
    }

    /// Whether the client may search: only from a private IPv4 address, so an endpoint on the internet sends no
    /// multicast and takes no answer from a host that is not on its network.
    fn searchable(&self) -> bool {
        self.client_v4().is_some_and(addr::is_private)
    }

    fn first(&self) -> Step {
        let specified = !self.cfg.local.ip().is_unspecified();
        match (self.cfg.gateway.is_some(), specified) {
            (true, true) => Step::Pcp,
            (true, false) => Step::NatAddr,
            (false, _) if self.searchable() => Step::Ssdp,
            _ => Step::Stopped,
        }
    }

    fn enter(&mut self, step: Step, now: u64) {
        self.step = step;
        self.tries = 0;
        self.send = false;
        self.http = Http::None;
        self.next = None;
        match step {
            Step::Pcp | Step::NatAddr | Step::NatMap | Step::Ssdp => {
                if matches!(step, Step::Pcp | Step::NatMap) {
                    self.started = now;
                }
                self.tries = 1;
                self.send = true;
                self.next = Some(now.saturating_add(self.gap()));
            }
            Step::Desc | Step::ExtIp | Step::Add | Step::Delete => {
                if step == Step::Add {
                    self.started = now;
                }
                self.http = Http::Due;
                self.next = Some(now.saturating_add(HTTP_WAIT));
            }
            Step::Idle => self.next = Some(now.saturating_add(RETRY)),
            Step::Held | Step::Stopped => {}
        }
    }

    fn gap(&self) -> u64 {
        if self.step == Step::Ssdp {
            return SSDP_GAP;
        }
        FIRST_GAP << self.tries.saturating_sub(1).min(8)
    }

    /// When the client next needs [`handle_timeout`](Self::handle_timeout).
    pub fn poll_timeout(&self) -> Option<u64> {
        let renew = self.held.filter(|_| self.step == Step::Held).map(|l| l.renew);
        [self.next, renew, self.held.map(|l| l.expiry)]
            .into_iter()
            .flatten()
            .min()
    }

    /// Time passed.
    pub fn handle_timeout(&mut self, now: u64) {
        self.now = self.now.max(now);
        let now = self.now;
        if self.held.is_some_and(|l| now >= l.expiry) {
            self.held = None;
            self.renewing = false;
            let first = self.first();
            self.enter(first, now);
            return;
        }
        if self.step == Step::Held
            && let Some(l) = self.held
            && now >= l.renew
        {
            self.renew(l.proto, now);
            return;
        }
        if self.next.is_none_or(|n| now < n) {
            return;
        }
        match self.step {
            Step::Pcp | Step::NatAddr | Step::NatMap | Step::Ssdp if self.tries < TRIES => {
                self.tries += 1;
                self.send = true;
                self.next = Some(now.saturating_add(self.gap()));
            }
            Step::Idle => {
                let first = self.first();
                self.enter(first, now);
            }
            _ => {
                bump(&mut self.stats.timeouts);
                self.fail(now);
            }
        }
    }

    fn renew(&mut self, proto: Proto, now: u64) {
        self.renewing = true;
        let step = match proto {
            Proto::Pcp => Step::Pcp,
            Proto::NatPmp => Step::NatAddr,
            // the external address is read again: it moves when the gateway's WAN address does
            Proto::Upnp => Step::ExtIp,
        };
        self.enter(step, now);
    }

    fn fail(&mut self, now: u64) {
        if core::mem::take(&mut self.renewing) && self.held.is_some() {
            self.enter(Step::Held, now);
            if let Some(l) = &mut self.held {
                l.renew = now
                    .saturating_add(l.expiry.saturating_sub(now) / 2)
                    .max(now.saturating_add(FIRST_GAP));
            }
            return;
        }
        let next = match self.step {
            Step::Pcp => Step::NatAddr,
            Step::NatAddr | Step::NatMap if self.searchable() => Step::Ssdp,
            Step::Delete | Step::Stopped => Step::Stopped,
            _ => Step::Idle,
        };
        self.enter(next, now);
    }

    fn grant(&mut self, proto: Proto, ext: SocketAddr, lifetime: u32, now: u64) {
        // A gateway may grant more than was asked: the lease is the shorter, so a restart is noticed at the renewal.
        let lifetime = lifetime.min(self.cfg.lifetime.max(1));
        self.held = Some(Lease {
            proto,
            ext,
            renew: lease::renew_at(self.started, lifetime),
            expiry: lease::expiry(self.started, lifetime),
        });
        self.renewing = false;
        self.announced = false;
        self.enter(Step::Held, now);
    }

    /// Note the gateway's epoch. One that shows the gateway lost its mappings drops the mapping held at once, whatever
    /// the answer that carried it says next (a grant that follows holds a new lease). It is called only for the answer
    /// to a request in flight, so a client that drops a mapping here goes on with that request.
    fn note_epoch(&mut self, now: u64, server: u32) {
        let lost = self.epoch.is_some_and(|p| lease::restarted(p, now, server));
        self.epoch = Some(Epoch { at: now, server });
        if lost {
            self.renewing = false;
            self.held = None;
        }
    }

    /// Whether a datagram from `from` is for this client: from the gateway's PCP and NAT-PMP port, or an SSDP answer
    /// while the client searches.
    pub fn owns(&self, from: SocketAddr, b: &[u8]) -> bool {
        let from = SocketAddr::new(from.ip().to_canonical(), from.port());
        if self.gateway() == Some(from) {
            return true;
        }
        self.step == Step::Ssdp
            && upnp::is_ssdp_answer(from, b)
            && self.cfg.gateway.map_or_else(
                || matches!(from.ip(), IpAddr::V4(v4) if addr::is_private(v4)),
                |g| g == from.ip(),
            )
    }

    /// A datagram this client [`owns`](Self::owns) arrived at `now`.
    pub fn handle_datagram(&mut self, now: u64, from: SocketAddr, b: &[u8]) {
        self.now = self.now.max(now);
        let now = self.now;
        if !self.owns(from, b) {
            bump(&mut self.stats.wrong_source);
            return;
        }
        if self.step == Step::Stopped {
            return;
        }
        if self.step == Step::Ssdp {
            let desc = upnp::ssdp_location(b);
            if desc.is_some_and(|d| !self.location_ok(&d, from)) {
                bump(&mut self.stats.wrong_source);
            }
            if let Some(desc) = desc.filter(|d| self.location_ok(d, from)) {
                self.igd = Some(Igd {
                    desc,
                    ctl: None,
                    ext_ip: None,
                    external: self.cfg.local.port(),
                    permanent: false,
                    conflicts: 0,
                });
                self.enter(Step::Desc, now);
            }
            return;
        }
        match b.first() {
            Some(0) => self.natpmp_answer(now, b),
            Some(_) => self.pcp_answer(now, b),
            None => {}
        }
    }

    /// Whether the description `desc` an SSDP answer from `from` names is on the host that answered (and on the gateway,
    /// when one is known): HTTP goes only to the host that spoke.
    fn location_ok(&self, desc: &Url, from: SocketAddr) -> bool {
        let ip = from.ip().to_canonical();
        desc.addr.ip() == ip && self.cfg.gateway.is_none_or(|g| g == ip)
    }

    fn pcp_answer(&mut self, now: u64, b: &[u8]) {
        match pcp::decode_response(b) {
            Err(_) => bump(&mut self.stats.unexpected),
            Ok(pcp::Response::Map {
                result,
                lifetime,
                epoch,
                nonce,
                protocol,
                internal_port,
                external_port,
                external_ip,
            }) => {
                if nonce != self.cfg.nonce {
                    bump(&mut self.stats.wrong_nonce);
                    return;
                }
                if self.step != Step::Pcp || protocol != pcp::UDP || internal_port != self.cfg.local.port() {
                    bump(&mut self.stats.unexpected);
                    return;
                }
                self.note_epoch(now, epoch);
                match result {
                    pcp::SUCCESS if lifetime > 0 && external_port != 0 && self.acceptable(external_ip) => {
                        self.grant(Proto::Pcp, SocketAddr::new(external_ip, external_port), lifetime, now);
                    }
                    pcp::UNSUPP_VERSION if !self.renewing => self.enter(Step::NatAddr, now),
                    _ => self.fail(now),
                }
            }
            Ok(pcp::Response::Header {
                opcode, result, epoch, ..
            }) => {
                if opcode == pcp::OP_ANNOUNCE {
                    // Nothing asked for it and it carries no nonce, so it only brings the renewal forward, once a
                    // round, and the mapping stays: the renewal's answer has the nonce, and its epoch decides.
                    match &mut self.held {
                        Some(l) if self.step == Step::Held && !self.announced => {
                            self.announced = true;
                            l.renew = l.renew.min(now);
                        }
                        _ => bump(&mut self.stats.unexpected),
                    }
                } else if self.step == Step::Pcp {
                    // an answer to the request in flight (the form has no nonce); in any other step it answers nothing
                    self.note_epoch(now, epoch);
                    if result == pcp::UNSUPP_VERSION && !self.renewing {
                        self.enter(Step::NatAddr, now);
                    } else {
                        self.fail(now);
                    }
                } else {
                    bump(&mut self.stats.unexpected);
                }
            }
        }
    }

    /// Whether `ip` may be the external address of a mapping; one that may not is counted.
    fn acceptable(&mut self, ip: IpAddr) -> bool {
        let ok = addr::external_ok(ip);
        if !ok {
            bump(&mut self.stats.refused_address);
        }
        ok
    }

    fn natpmp_answer(&mut self, now: u64, b: &[u8]) {
        let Ok(r) = natpmp::decode_response(b) else {
            bump(&mut self.stats.unexpected);
            return;
        };
        match r {
            natpmp::Response::Error { .. } if self.step == Step::Pcp && !self.renewing => {
                self.enter(Step::NatAddr, now);
            }
            natpmp::Response::Error { opcode, epoch, .. } => {
                let ours = (opcode == natpmp::OP_ADDRESS && self.step == Step::NatAddr)
                    || (opcode == natpmp::OP_MAP_UDP && self.step == Step::NatMap);
                if ours {
                    self.note_epoch(now, epoch);
                    self.fail(now);
                } else {
                    bump(&mut self.stats.unexpected);
                }
            }
            natpmp::Response::Address { result, epoch, ip } if self.step == Step::NatAddr => {
                self.note_epoch(now, epoch);
                if result == 0 && self.acceptable(IpAddr::V4(ip)) {
                    self.nat_ip = Some(ip);
                    self.enter(Step::NatMap, now);
                } else {
                    self.fail(now);
                }
            }
            natpmp::Response::Map {
                result,
                epoch,
                internal_port,
                external_port,
                lifetime,
            } if self.step == Step::NatMap && internal_port == self.cfg.local.port() => {
                self.note_epoch(now, epoch);
                match self.nat_ip {
                    Some(ip) if result == 0 && lifetime > 0 && external_port != 0 => {
                        self.grant(
                            Proto::NatPmp,
                            SocketAddr::new(IpAddr::V4(ip), external_port),
                            lifetime,
                            now,
                        );
                    }
                    _ => self.fail(now),
                }
            }
            _ => bump(&mut self.stats.unexpected),
        }
    }

    /// The next datagram to send: its destination and length in `buf`. A buffer of
    /// [`MAX_DATAGRAM`](crate::MAX_DATAGRAM) bytes holds any.
    pub fn poll_datagram(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        if let Some(l) = self.releases.iter_mut().find_map(Option::take) {
            let gw = self.gateway()?;
            let n = match l.proto {
                Proto::Pcp => pcp::encode_request(&self.pcp_request(0, Some(l.ext)), buf).ok()?,
                Proto::NatPmp => natpmp::encode_request(
                    &natpmp::Request::Map {
                        internal_port: self.cfg.local.port(),
                        external_port: 0,
                        lifetime: 0,
                    },
                    buf,
                )
                .ok()?,
                Proto::Upnp => return None,
            };
            return Some((gw, n));
        }
        if !self.send {
            return None;
        }
        self.send = false;
        let ext = self.held.map(|l| l.ext);
        match self.step {
            Step::Pcp => {
                let r = self.pcp_request(self.cfg.lifetime, ext);
                Some((self.gateway()?, pcp::encode_request(&r, buf).ok()?))
            }
            Step::NatAddr => Some((
                self.gateway()?,
                natpmp::encode_request(&natpmp::Request::Address, buf).ok()?,
            )),
            Step::NatMap => {
                let r = natpmp::Request::Map {
                    internal_port: self.cfg.local.port(),
                    external_port: ext.map_or(self.cfg.local.port(), |e| e.port()),
                    lifetime: self.cfg.lifetime,
                };
                Some((self.gateway()?, natpmp::encode_request(&r, buf).ok()?))
            }
            Step::Ssdp => {
                let d = buf.get_mut(..upnp::M_SEARCH.len())?;
                d.copy_from_slice(upnp::M_SEARCH);
                Some((upnp::SSDP, upnp::M_SEARCH.len()))
            }
            _ => None,
        }
    }

    fn pcp_request(&self, lifetime: u32, ext: Option<SocketAddr>) -> pcp::MapRequest {
        let unspecified = if self.cfg.local.is_ipv4() {
            IpAddr::V4(Ipv4Addr::UNSPECIFIED)
        } else {
            IpAddr::V6(core::net::Ipv6Addr::UNSPECIFIED)
        };
        pcp::MapRequest {
            lifetime,
            client: self.cfg.local.ip(),
            nonce: self.cfg.nonce,
            protocol: pcp::UDP,
            internal_port: self.cfg.local.port(),
            external_port: ext.map_or(self.cfg.local.port(), |e| e.port()),
            external_ip: ext.map_or(unspecified, |e| e.ip()),
        }
    }

    /// The next HTTP request: where to open a TCP connection, and the request's length in `buf` (at most
    /// [`MAX_REQUEST`](crate::upnp::MAX_REQUEST) bytes). The host writes it, reads the answer until the server closes
    /// (at most [`MAX_RESPONSE`](crate::MAX_RESPONSE) bytes) and hands it to [`handle_http`](Self::handle_http).
    pub fn poll_http(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        if self.http != Http::Due {
            return None;
        }
        let igd = self.igd?;
        let built = match (self.step, igd.ctl) {
            (Step::Desc, _) => upnp::get(&igd.desc, buf).map(|n| (igd.desc.addr, n)),
            (Step::ExtIp, Some((ctl, svc))) => upnp::soap(&ctl, svc, &Call::ExternalIp, buf).map(|n| (ctl.addr, n)),
            (Step::Add, Some((ctl, svc))) => {
                let client = self.client_v4()?;
                let call = Call::Add {
                    external: igd.external,
                    client,
                    internal: self.cfg.local.port(),
                    lease: if igd.permanent { 0 } else { self.cfg.lifetime },
                };
                upnp::soap(&ctl, svc, &call, buf).map(|n| (ctl.addr, n))
            }
            (Step::Delete, Some((ctl, svc))) => {
                upnp::soap(&ctl, svc, &Call::Delete { external: igd.external }, buf).map(|n| (ctl.addr, n))
            }
            _ => None,
        };
        if built.is_some() {
            self.http = Http::Sent;
        } else {
            self.http_fail(self.now);
        }
        built
    }

    /// An HTTP exchange failed or its answer was refused: counted, and the step fails.
    fn http_fail(&mut self, now: u64) {
        bump(&mut self.stats.http_failures);
        self.fail(now);
    }

    /// The answer to the last HTTP request at `now`: the bytes the server sent, or `None` if the connection failed.
    pub fn handle_http(&mut self, now: u64, resp: Option<&[u8]>) {
        self.now = self.now.max(now);
        let now = self.now;
        if self.http != Http::Sent {
            return;
        }
        self.http = Http::None;
        let Some(igd) = &mut self.igd else { return };
        let Some(resp) = resp else {
            self.http_fail(now);
            return;
        };
        match self.step {
            Step::Desc => match upnp::http_response(resp).and_then(|(s, body)| (s == 200).then_some(body)) {
                Some(body) => match upnp::control_of(body, &igd.desc) {
                    Some(ctl) => {
                        igd.ctl = Some(ctl);
                        self.enter(Step::ExtIp, now);
                    }
                    None => self.http_fail(now),
                },
                None => self.http_fail(now),
            },
            Step::ExtIp => {
                let ext = match upnp::soap_result(resp) {
                    Some(SoapResult::Ok(body)) => upnp::external_ip(body),
                    _ => None,
                };
                match ext {
                    Some(ip) if addr::external_ok(IpAddr::V4(ip)) => {
                        igd.ext_ip = Some(ip);
                        self.enter(Step::Add, now);
                    }
                    Some(_) => {
                        bump(&mut self.stats.refused_address);
                        self.fail(now);
                    }
                    None => self.http_fail(now),
                }
            }
            Step::Add => match upnp::soap_result(resp) {
                Some(SoapResult::Ok(_)) => match igd.ext_ip {
                    Some(ip) => {
                        let ext = SocketAddr::new(IpAddr::V4(ip), igd.external);
                        self.grant(Proto::Upnp, ext, self.cfg.lifetime, now);
                    }
                    None => self.http_fail(now),
                },
                Some(SoapResult::Fault(upnp::ONLY_PERMANENT_LEASES)) if !igd.permanent => {
                    igd.permanent = true;
                    self.enter(Step::Add, now);
                }
                Some(SoapResult::Fault(upnp::CONFLICT)) if igd.conflicts < CONFLICT_TRIES && !self.renewing => {
                    igd.conflicts += 1;
                    igd.external = igd.external.checked_add(1).unwrap_or(1024);
                    self.enter(Step::Add, now);
                }
                _ => self.http_fail(now),
            },
            Step::Delete => self.enter(Step::Stopped, now),
            _ => {}
        }
    }

    /// The mapping a request in flight may have made at the gateway: a PCP or NAT-PMP request that left, or an
    /// `AddPortMapping` that was sent.
    fn in_flight(&self) -> Option<Lease> {
        let proto = match self.step {
            Step::Pcp => Proto::Pcp,
            Step::NatMap => Proto::NatPmp,
            Step::Add if self.igd.is_some_and(|i| i.ctl.is_some()) => Proto::Upnp,
            _ => return None,
        };
        let port = match proto {
            Proto::Upnp => self.igd.map_or(self.cfg.local.port(), |i| i.external),
            _ => self.cfg.local.port(),
        };
        Some(Lease {
            proto,
            ext: SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), port),
            renew: 0,
            expiry: 0,
        })
    }

    // vertexia: two releases wait at most; a third replaces the last, a restart of a restart is not a case that needs more
    fn queue_release(&mut self, l: Lease) {
        let slot = self.releases.iter().position(Option::is_none).unwrap_or(1);
        if let Some(r) = self.releases.get_mut(slot) {
            *r = Some(l);
        }
    }

    /// Stop at `now`: drop the mapping, or a request in flight that may have made one, and ask the gateway to delete
    /// it. Nothing is asked afterwards.
    pub fn stop(&mut self, now: u64) {
        self.now = self.now.max(now);
        let now = self.now;
        self.halted = true;
        let held = self.held.take().or_else(|| self.in_flight());
        self.renewing = false;
        match held {
            Some(l) if l.proto == Proto::Upnp && self.igd.is_some_and(|i| i.ctl.is_some()) => {
                if let Some(igd) = &mut self.igd {
                    igd.external = l.ext.port();
                }
                self.enter(Step::Delete, now);
            }
            Some(l) => {
                self.queue_release(l);
                self.enter(Step::Stopped, now);
            }
            None => self.enter(Step::Stopped, now),
        }
    }

    /// The network changed at `now`: drop the mapping held, release it at once (a `UPnP` one is left to its lease:
    /// its delete needs HTTP the new network may not carry), forget what was learned of the gateway and ask again
    /// from the beginning. A stopped client stays stopped.
    pub fn restart(&mut self, now: u64) {
        self.now = self.now.max(now);
        let now = self.now;
        if self.halted {
            return;
        }
        if let Some(l) = self.held.take().filter(|l| l.proto != Proto::Upnp) {
            self.queue_release(l);
        }
        self.renewing = false;
        self.epoch = None;
        self.nat_ip = None;
        self.igd = None;
        let first = self.first();
        self.enter(first, now);
    }
}
