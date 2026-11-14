//! UPnP-IGD, minimal and bounded: the SSDP search, the gateway's description, and the three WANIPConnection calls a
//! client needs (GetExternalIPAddress, AddPortMapping, DeletePortMapping), over HTTP/1.0 so no response is chunked.
//!
//! - **Search.** [`M_SEARCH`] goes to `239.255.255.250:1900`; an answer is `HTTP/1.1 200` with a `LOCATION` header
//!   naming the description: `http://<IPv4>[:port]/<path>`, the only form taken ([`parse_location`]), and never a
//!   loopback, unspecified, multicast, broadcast or link-local host ([`usable_host`]).
//! - **Description.** The first `<service>` whose `<serviceType>` is one of [`SERVICES`] gives the `<controlURL>`, a
//!   path or an `http://` URL of the same form and of the description's own host ([`control_of`]).
//! - **Calls.** A SOAP POST to the control URL ([`soap`]); a `200` answer is success and a `500` carries `<errorCode>`
//!   ([`soap_result`]).
//!
//! Bounds: a path is at most [`MAX_PATH`] bytes, a request at most [`MAX_REQUEST`]; the host hands at most
//! [`MAX_RESPONSE`](crate::MAX_RESPONSE) bytes of a response, and a longer one is read only that far.
//!
//! Invariants: nothing allocates, panics or reads past its input; every parse takes one form and refuses the rest.

use core::net::{Ipv4Addr, SocketAddr, SocketAddrV4};

use crate::addr::usable_host;
use crate::text::{Out, element, find, header, parse_ip4, parse_u32, trim};

/// The SSDP multicast address.
pub const SSDP: SocketAddr = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(239, 255, 255, 250), 1900));
/// The search for an Internet gateway device.
pub const M_SEARCH: &[u8] = b"M-SEARCH * HTTP/1.1\r\nHOST: 239.255.255.250:1900\r\nMAN: \"ssdp:discover\"\r\nMX: 1\r\nST: urn:schemas-upnp-org:device:InternetGatewayDevice:1\r\n\r\n";
/// The longest path kept.
pub const MAX_PATH: usize = 128;
/// The longest request built.
pub const MAX_REQUEST: usize = 2048;
/// The services that map ports.
pub const SERVICES: [&[u8]; 3] = [
    b"urn:schemas-upnp-org:service:WANIPConnection:2",
    b"urn:schemas-upnp-org:service:WANIPConnection:1",
    b"urn:schemas-upnp-org:service:WANPPPConnection:1",
];

/// An HTTP endpoint: where to connect and the path to ask for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Url {
    /// The server.
    pub addr: SocketAddr,
    path: [u8; MAX_PATH],
    len: u8,
}

impl Url {
    /// A URL of `addr` and `path`; `None` if the path is empty, longer than [`MAX_PATH`] or not printable ASCII.
    pub fn new(addr: SocketAddr, path: &[u8]) -> Option<Self> {
        if path.is_empty() || path.len() > MAX_PATH || !path.iter().all(u8::is_ascii_graphic) {
            return None;
        }
        let mut p = [0u8; MAX_PATH];
        p.get_mut(..path.len())?.copy_from_slice(path);
        Some(Self {
            addr,
            path: p,
            len: u8::try_from(path.len()).ok()?,
        })
    }

    /// The path.
    pub fn path(&self) -> &[u8] {
        self.path.get(..usize::from(self.len)).unwrap_or_default()
    }
}

/// `http://<IPv4>[:port][/path]`: the address and the path (`/` when none).
pub fn parse_location(b: &[u8]) -> Option<Url> {
    let rest = trim(b);
    let rest = rest
        .get(..7)
        .filter(|p| p.eq_ignore_ascii_case(b"http://"))
        .and(rest.get(7..))?;
    let slash = rest.iter().position(|c| *c == b'/').unwrap_or(rest.len());
    let (hostport, path) = rest.split_at(slash);
    let (host, port) = match hostport.iter().position(|c| *c == b':') {
        Some(c) => (
            hostport.get(..c)?,
            u16::try_from(parse_u32(hostport.get(c + 1..)?)?).ok()?,
        ),
        None => (hostport, 80),
    };
    if port == 0 {
        return None;
    }
    let ip = parse_ip4(host).filter(|ip| usable_host(*ip))?;
    let addr = SocketAddr::V4(SocketAddrV4::new(ip, port));
    Url::new(addr, if path.is_empty() { b"/" } else { path })
}

/// The status code and the body of an HTTP response (the body cut at `Content-Length` when that is shorter).
pub fn http_response(b: &[u8]) -> Option<(u16, &[u8])> {
    let line_end = find(b, b"\r\n")?;
    let line = b.get(..line_end)?;
    let rest = line.strip_prefix(b"HTTP/1.")?;
    let [minor, b' ', c0, c1, c2, tail @ ..] = rest else {
        return None;
    };
    if !minor.is_ascii_digit() || !(tail.is_empty() || tail.first() == Some(&b' ')) {
        return None;
    }
    let status = u16::try_from(parse_u32(&[*c0, *c1, *c2])?).ok()?;
    let head_end = find(b, b"\r\n\r\n")?;
    let head = b.get(..head_end)?;
    let body = b.get(head_end + 4..)?;
    let body = match header(head, b"content-length").and_then(parse_u32) {
        Some(n) => body.get(..usize::try_from(n).ok()?.min(body.len()))?,
        None => body,
    };
    Some((status, body))
}

/// The description URL of an SSDP answer: a `200` with a `LOCATION` header of the one form taken.
pub fn ssdp_location(b: &[u8]) -> Option<Url> {
    let line_end = find(b, b"\r\n")?;
    let line = b.get(..line_end)?;
    if line.get(..9).is_none_or(|p| !p.eq_ignore_ascii_case(b"HTTP/1.1 ")) || line.get(9..12) != Some(b"200") {
        return None;
    }
    let head_end = find(b, b"\r\n\r\n").unwrap_or(b.len());
    parse_location(header(b.get(..head_end)?, b"location")?)
}

/// The control URL and service of the first mapping service in a description that `base` served.
pub fn control_of(desc: &[u8], base: &Url) -> Option<(Url, usize)> {
    let mut at = 0;
    while let Some(off) = desc.get(at..).and_then(|d| find(d, b"<serviceType>")) {
        let (ty, next) = element(desc, at + off, b"serviceType")?;
        let end = desc
            .get(next..)
            .and_then(|d| find(d, b"</service>"))
            .map_or(desc.len(), |e| next + e);
        if let Some(k) = SERVICES.iter().position(|s| *s == ty) {
            let scope = desc.get(..end)?;
            if let Some((ctl, _)) = element(scope, next, b"controlURL") {
                return resolve(ctl, base).map(|u| (u, k));
            }
        }
        at = next;
    }
    None
}

fn resolve(ctl: &[u8], base: &Url) -> Option<Url> {
    if ctl.get(..7).is_some_and(|p| p.eq_ignore_ascii_case(b"http://")) {
        // The control address is the description's host: an answer names where to send HTTP only once.
        return parse_location(ctl).filter(|u| u.addr.ip() == base.addr.ip());
    }
    if ctl.first() == Some(&b'/') {
        return Url::new(base.addr, ctl);
    }
    let mut p = [0u8; MAX_PATH];
    let mut o = Out::new(&mut p);
    o.put(b"/").put(ctl);
    let n = o.done()?;
    Url::new(base.addr, p.get(..n)?)
}

/// An HTTP/1.0 GET of `url` into `out`; returns its length.
pub fn get(url: &Url, out: &mut [u8]) -> Option<usize> {
    let mut o = Out::new(out);
    o.put(b"GET ").put(url.path()).put(b" HTTP/1.0\r\nHost: ");
    host(&mut o, url.addr);
    o.put(b"\r\nConnection: close\r\n\r\n");
    o.done()
}

fn host(o: &mut Out<'_>, a: SocketAddr) {
    if let SocketAddr::V4(v4) = a {
        o.ip4(*v4.ip()).put(b":").dec(v4.port().into());
    }
}

/// A WANIPConnection call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Call {
    /// GetExternalIPAddress.
    ExternalIp,
    /// AddPortMapping of UDP `external` to `client:internal` for `lease` seconds (0: as long as the gateway keeps it).
    Add {
        /// The external port.
        external: u16,
        /// The client's address.
        client: Ipv4Addr,
        /// The client's port.
        internal: u16,
        /// Seconds.
        lease: u32,
    },
    /// DeletePortMapping of UDP `external`.
    Delete {
        /// The external port.
        external: u16,
    },
}

/// A SOAP POST of `call` to the service `service` (an index of [`SERVICES`]) at `url`, into `out`; returns its length.
pub fn soap(url: &Url, service: usize, call: &Call, out: &mut [u8]) -> Option<usize> {
    let svc = SERVICES.get(service)?;
    let action: &[u8] = match call {
        Call::ExternalIp => b"GetExternalIPAddress",
        Call::Add { .. } => b"AddPortMapping",
        Call::Delete { .. } => b"DeletePortMapping",
    };
    let mut body = [0u8; MAX_REQUEST / 2];
    let mut b = Out::new(&mut body);
    b.put(b"<?xml version=\"1.0\"?><s:Envelope xmlns:s=\"http://schemas.xmlsoap.org/soap/envelope/\" s:encodingStyle=\"http://schemas.xmlsoap.org/soap/encoding/\"><s:Body><u:")
        .put(action)
        .put(b" xmlns:u=\"")
        .put(svc)
        .put(b"\">");
    match *call {
        Call::ExternalIp => {}
        Call::Add {
            external,
            client,
            internal,
            lease,
        } => {
            b.put(b"<NewRemoteHost></NewRemoteHost><NewExternalPort>")
                .dec(external.into())
                .put(b"</NewExternalPort><NewProtocol>UDP</NewProtocol><NewInternalPort>")
                .dec(internal.into())
                .put(b"</NewInternalPort><NewInternalClient>")
                .ip4(client)
                .put(b"</NewInternalClient><NewEnabled>1</NewEnabled><NewPortMappingDescription>vinc</NewPortMappingDescription><NewLeaseDuration>")
                .dec(lease)
                .put(b"</NewLeaseDuration>");
        }
        Call::Delete { external } => {
            b.put(b"<NewRemoteHost></NewRemoteHost><NewExternalPort>")
                .dec(external.into())
                .put(b"</NewExternalPort><NewProtocol>UDP</NewProtocol>");
        }
    }
    b.put(b"</u:").put(action).put(b"></s:Body></s:Envelope>");
    let n = b.done()?;
    let body = body.get(..n)?;
    let mut o = Out::new(out);
    o.put(b"POST ").put(url.path()).put(b" HTTP/1.0\r\nHost: ");
    host(&mut o, url.addr);
    o.put(b"\r\nContent-Type: text/xml; charset=\"utf-8\"\r\nSOAPAction: \"")
        .put(svc)
        .put(b"#")
        .put(action)
        .put(b"\"\r\nConnection: close\r\nContent-Length: ")
        .dec(u32::try_from(n).ok()?)
        .put(b"\r\n\r\n")
        .put(body);
    o.done()
}

/// What a SOAP call's answer says.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SoapResult<'a> {
    /// `200`, with the body.
    Ok(&'a [u8]),
    /// A UPnP error code.
    Fault(u32),
}

/// The UPnP error: the gateway keeps only leases of duration 0.
pub const ONLY_PERMANENT_LEASES: u32 = 725;
/// The UPnP error: the external port is mapped to another client.
pub const CONFLICT: u32 = 718;

/// The result of a SOAP answer; `None` for anything but a `200` or a `500` with an `<errorCode>`.
pub fn soap_result(resp: &[u8]) -> Option<SoapResult<'_>> {
    match http_response(resp)? {
        (200, body) => Some(SoapResult::Ok(body)),
        (500, body) => Some(SoapResult::Fault(parse_u32(element(body, 0, b"errorCode")?.0)?)),
        _ => None,
    }
}

/// The address a GetExternalIPAddress answer names.
pub fn external_ip(body: &[u8]) -> Option<Ipv4Addr> {
    parse_ip4(element(body, 0, b"NewExternalIPAddress")?.0)
}

/// Whether `b` may be an answer to the search: it comes from port 1900 and starts as an HTTP response.
pub fn is_ssdp_answer(from: SocketAddr, b: &[u8]) -> bool {
    from.port() == 1900 && b.get(..7).is_some_and(|p| p.eq_ignore_ascii_case(b"HTTP/1."))
}
