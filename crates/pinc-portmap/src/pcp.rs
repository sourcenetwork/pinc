//! PCP (RFC 6887): the MAP request a client sends and the responses a server sends back.
//!
//! # Wire format
//!
//! Every message starts with a 24-byte header; a MAP message adds 36 bytes of opcode data. All integers are big-endian.
//!
//! - Request header: `version(1)=2 opcode(1) reserved(2)=0 lifetime(4) client_ip(16)`; the opcode's top bit (R) is 0.
//! - Response header: `version(1)=2 opcode(1) reserved(1)=0 result(1) lifetime(4) epoch(4) reserved(12)=0`; R is 1.
//! - MAP data: `nonce(12) protocol(1) reserved(3)=0 internal_port(2) external_port(2) external_ip(16)`.
//!
//! An IPv4 address travels as its IPv4-mapped IPv6 form (`::ffff:a.b.c.d`) and decodes back to IPv4.
//!
//! One valid form: a MAP request is exactly [`MAP_LEN`] bytes; a successful MAP response is exactly [`MAP_LEN`]
//! bytes; an ANNOUNCE response, or an error response without opcode data, is exactly [`HEADER_LEN`]; every reserved
//! byte is zero. No options are sent and none are taken. A response whose version byte is 0 is the answer of a NAT-PMP
//! server to a PCP request ([`PcpError::NatPmp`]), the signal to fall back.
//!
//! Invariants: [`decode_request`] accepts exactly what [`encode_request`] writes, and [`decode_response`] exactly what
//! [`encode_response`] writes (for IPv4 and non-mapped IPv6 addresses); an encode that fails writes nothing; nothing
//! panics or reads past its input.

use core::net::{IpAddr, Ipv6Addr};

/// The version this client speaks.
pub const VERSION: u8 = 2;
/// The header's length.
pub const HEADER_LEN: usize = 24;
/// A MAP message's length: the header and the MAP data.
pub const MAP_LEN: usize = 60;
/// The ANNOUNCE opcode.
pub const OP_ANNOUNCE: u8 = 0;
/// The MAP opcode.
pub const OP_MAP: u8 = 1;
/// The response bit of the opcode byte.
pub const RESPONSE: u8 = 0x80;
/// The protocol number of UDP.
pub const UDP: u8 = 17;
/// Result: success.
pub const SUCCESS: u8 = 0;
/// Result: the server does not speak this version.
pub const UNSUPP_VERSION: u8 = 1;

/// A MAP request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MapRequest {
    /// The lifetime asked for, in seconds; 0 deletes the mapping.
    pub lifetime: u32,
    /// The client's own address, as the server sees the request's source.
    pub client: IpAddr,
    /// The mapping nonce: the same for every request of one mapping.
    pub nonce: [u8; 12],
    /// The protocol to map.
    pub protocol: u8,
    /// The client's port.
    pub internal_port: u16,
    /// The external port asked for; 0 lets the server choose.
    pub external_port: u16,
    /// The external address asked for; unspecified lets the server choose.
    pub external_ip: IpAddr,
}

/// A response.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Response {
    /// A MAP response (successful or not) with its opcode data.
    Map {
        /// The result code.
        result: u8,
        /// The granted lifetime in seconds (or how long an error lasts).
        lifetime: u32,
        /// The server's epoch: seconds since it last lost its mappings.
        epoch: u32,
        /// The nonce of the request it answers.
        nonce: [u8; 12],
        /// The protocol mapped.
        protocol: u8,
        /// The client's port.
        internal_port: u16,
        /// The external port assigned.
        external_port: u16,
        /// The external address assigned.
        external_ip: IpAddr,
    },
    /// A header with no opcode data: an ANNOUNCE (opcode 0, success) or an error.
    Header {
        /// The opcode answered.
        opcode: u8,
        /// The result code.
        result: u8,
        /// The lifetime field.
        lifetime: u32,
        /// The server's epoch.
        epoch: u32,
    },
}

/// Why a message was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PcpError {
    /// The output is too small.
    Short,
    /// The length is not one of the valid forms.
    Length,
    /// The version byte is 0: a NAT-PMP server answered.
    NatPmp,
    /// Another version.
    Version(u8),
    /// The R bit is wrong for the direction, or the opcode is not one this client knows.
    Opcode(u8),
    /// A reserved byte is not zero.
    Reserved,
    /// A successful MAP response without its opcode data, or a successful header that is not an ANNOUNCE.
    Form,
}

fn put_ip(out: &mut [u8], ip: IpAddr) {
    let v6 = match ip {
        IpAddr::V4(v4) => v4.to_ipv6_mapped(),
        IpAddr::V6(v6) => v6,
    };
    out.copy_from_slice(&v6.octets());
}

fn get_ip(b: &[u8]) -> IpAddr {
    let mut o = [0u8; 16];
    o.copy_from_slice(b);
    IpAddr::V6(Ipv6Addr::from(o)).to_canonical()
}

fn be16(b: &[u8]) -> u16 {
    let mut o = [0u8; 2];
    o.copy_from_slice(b);
    u16::from_be_bytes(o)
}

fn zero(b: &[u8]) -> bool {
    b.iter().all(|c| *c == 0)
}

/// Write the MAP data of `nonce` ... into `m` (36 bytes).
fn put_map(data: &mut [u8; 36], nonce: &[u8; 12], protocol: u8, internal: u16, external: u16, ip: IpAddr) {
    let (nonce_out, rest) = data.split_at_mut(12);
    nonce_out.copy_from_slice(nonce);
    let (proto, rest) = rest.split_at_mut(4);
    proto.copy_from_slice(&[protocol, 0, 0, 0]);
    let (int_port, rest) = rest.split_at_mut(2);
    int_port.copy_from_slice(&internal.to_be_bytes());
    let (ext_port, rest) = rest.split_at_mut(2);
    ext_port.copy_from_slice(&external.to_be_bytes());
    put_ip(rest, ip);
}

/// The MAP data in `m` (36 bytes): nonce, protocol, internal port, external port, address; `None` if a reserved byte
/// is set.
fn get_map(data: &[u8; 36]) -> Option<([u8; 12], u8, u16, u16, IpAddr)> {
    let (nonce_in, rest) = data.split_at(12);
    let (proto, rest) = rest.split_at(4);
    let (int_port, rest) = rest.split_at(2);
    let (ext_port, ip) = rest.split_at(2);
    let mut nonce = [0u8; 12];
    nonce.copy_from_slice(nonce_in);
    let (protocol, reserved) = proto.split_first()?;
    zero(reserved).then(|| (nonce, *protocol, be16(int_port), be16(ext_port), get_ip(ip)))
}

/// Encode `r`; returns [`MAP_LEN`].
///
/// # Errors
/// [`PcpError::Short`] if `out` is shorter than [`MAP_LEN`]; nothing is written then.
pub fn encode_request(r: &MapRequest, out: &mut [u8]) -> Result<usize, PcpError> {
    let o: &mut [u8; MAP_LEN] = out
        .get_mut(..MAP_LEN)
        .and_then(|o| o.try_into().ok())
        .ok_or(PcpError::Short)?;
    let (h, m) = o.split_at_mut(HEADER_LEN);
    let (fixed, ip) = h.split_at_mut(8);
    let mut head = [VERSION, OP_MAP, 0, 0, 0, 0, 0, 0];
    if let Some(l) = head.get_mut(4..8) {
        l.copy_from_slice(&r.lifetime.to_be_bytes());
    }
    fixed.copy_from_slice(&head);
    put_ip(ip, r.client);
    let m: &mut [u8; 36] = m.try_into().map_err(|_| PcpError::Short)?;
    put_map(m, &r.nonce, r.protocol, r.internal_port, r.external_port, r.external_ip);
    Ok(MAP_LEN)
}

/// Decode a MAP request.
///
/// # Errors
/// The first rule `b` breaks, in the order: length, version, opcode, reserved bytes.
pub fn decode_request(b: &[u8]) -> Result<MapRequest, PcpError> {
    let o: &[u8; MAP_LEN] = b.try_into().map_err(|_| PcpError::Length)?;
    let (h, m) = o.split_at(HEADER_LEN);
    let [ver, op, r0, r1, l0, l1, l2, l3, ..] = *h else {
        return Err(PcpError::Length);
    };
    check_version(ver)?;
    if op != OP_MAP {
        return Err(PcpError::Opcode(op));
    }
    if r0 != 0 || r1 != 0 {
        return Err(PcpError::Reserved);
    }
    let m: &[u8; 36] = m.try_into().map_err(|_| PcpError::Length)?;
    let (nonce, protocol, internal_port, external_port, external_ip) = get_map(m).ok_or(PcpError::Reserved)?;
    Ok(MapRequest {
        lifetime: u32::from_be_bytes([l0, l1, l2, l3]),
        client: get_ip(h.get(8..).ok_or(PcpError::Length)?),
        nonce,
        protocol,
        internal_port,
        external_port,
        external_ip,
    })
}

const fn check_version(v: u8) -> Result<(), PcpError> {
    match v {
        VERSION => Ok(()),
        0 => Err(PcpError::NatPmp),
        v => Err(PcpError::Version(v)),
    }
}

/// Encode `r`; returns its length ([`MAP_LEN`] or [`HEADER_LEN`]).
///
/// # Errors
/// [`PcpError::Short`] if `out` is too small; [`PcpError::Form`] for a response [`decode_response`] would refuse (a
/// successful header that is not an ANNOUNCE, or an opcode other than MAP and ANNOUNCE). Nothing is written then.
pub fn encode_response(r: &Response, out: &mut [u8]) -> Result<usize, PcpError> {
    let (opcode, result, lifetime, epoch) = match *r {
        Response::Map {
            result,
            lifetime,
            epoch,
            ..
        } => (OP_MAP, result, lifetime, epoch),
        Response::Header {
            opcode,
            result,
            lifetime,
            epoch,
        } => {
            if opcode != OP_ANNOUNCE && (opcode != OP_MAP || result == SUCCESS) {
                return Err(PcpError::Form);
            }
            (opcode, result, lifetime, epoch)
        }
    };
    let len = if matches!(r, Response::Map { .. }) {
        MAP_LEN
    } else {
        HEADER_LEN
    };
    let o = out.get_mut(..len).ok_or(PcpError::Short)?;
    let (h, m) = o.split_at_mut(HEADER_LEN);
    h.fill(0);
    let mut head = [VERSION, opcode | RESPONSE, 0, result, 0, 0, 0, 0, 0, 0, 0, 0];
    if let Some(l) = head.get_mut(4..8) {
        l.copy_from_slice(&lifetime.to_be_bytes());
    }
    if let Some(e) = head.get_mut(8..12) {
        e.copy_from_slice(&epoch.to_be_bytes());
    }
    if let Some(d) = h.get_mut(..12) {
        d.copy_from_slice(&head);
    }
    if let Response::Map {
        nonce,
        protocol,
        internal_port,
        external_port,
        external_ip,
        ..
    } = *r
    {
        let m: &mut [u8; 36] = m.try_into().map_err(|_| PcpError::Short)?;
        put_map(m, &nonce, protocol, internal_port, external_port, external_ip);
    }
    Ok(len)
}

/// Decode a response.
///
/// # Errors
/// The first rule `b` breaks, in the order: version (from its first byte, so a NAT-PMP answer of any length is
/// [`PcpError::NatPmp`]), length, opcode and R bit, reserved bytes, form.
pub fn decode_response(b: &[u8]) -> Result<Response, PcpError> {
    check_version(*b.first().ok_or(PcpError::Length)?)?;
    if b.len() != HEADER_LEN && b.len() != MAP_LEN {
        return Err(PcpError::Length);
    }
    let h: &[u8; HEADER_LEN] = b
        .get(..HEADER_LEN)
        .and_then(|h| h.try_into().ok())
        .ok_or(PcpError::Length)?;
    let [_, op, r0, result, l0, l1, l2, l3, e0, e1, e2, e3, ..] = *h;
    if op & RESPONSE == 0 || (op & !RESPONSE != OP_MAP && op & !RESPONSE != OP_ANNOUNCE) {
        return Err(PcpError::Opcode(op));
    }
    if r0 != 0 || !zero(h.get(12..).unwrap_or_default()) {
        return Err(PcpError::Reserved);
    }
    let opcode = op & !RESPONSE;
    let lifetime = u32::from_be_bytes([l0, l1, l2, l3]);
    let epoch = u32::from_be_bytes([e0, e1, e2, e3]);
    match b.get(HEADER_LEN..).and_then(|m| <&[u8; 36]>::try_from(m).ok()) {
        Some(m) => {
            if opcode != OP_MAP {
                return Err(PcpError::Form);
            }
            let (nonce, protocol, internal_port, external_port, external_ip) = get_map(m).ok_or(PcpError::Reserved)?;
            Ok(Response::Map {
                result,
                lifetime,
                epoch,
                nonce,
                protocol,
                internal_port,
                external_port,
                external_ip,
            })
        }
        None if result == SUCCESS && opcode != OP_ANNOUNCE => Err(PcpError::Form),
        None => Ok(Response::Header {
            opcode,
            result,
            lifetime,
            epoch,
        }),
    }
}
