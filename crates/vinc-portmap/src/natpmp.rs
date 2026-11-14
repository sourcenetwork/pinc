//! NAT-PMP (RFC 6886): the external address request, the UDP mapping request, and their responses.
//!
//! # Wire format
//!
//! All integers are big-endian; the version byte is 0.
//!
//! - Address request: `version(1)=0 opcode(1)=0`, 2 bytes.
//! - Mapping request: `version(1)=0 opcode(1)=1 reserved(2)=0 internal_port(2) external_port(2) lifetime(4)`, 12 bytes.
//! - Address response: `version(1)=0 opcode(1)=128 result(2) epoch(4) external_ip(4)`, 12 bytes.
//! - Mapping response: `version(1)=0 opcode(1)=129 result(2) epoch(4) internal_port(2) external_port(2) lifetime(4)`,
//!   16 bytes.
//! - Error response without a body: `version(1)=0 opcode(1) result(2) epoch(4)` with a non-zero result, 8 bytes (what a
//!   server sends for a version or opcode it does not know).
//!
//! One valid form for each: the exact length, the version byte 0, the opcode, zero reserved bytes. Only UDP mappings
//! are asked for and taken.
//!
//! Invariants: each decode accepts exactly what its encode writes; an encode that fails writes nothing; nothing panics
//! or reads past its input.

use core::net::Ipv4Addr;

/// The address request's opcode.
pub const OP_ADDRESS: u8 = 0;
/// The UDP mapping opcode.
pub const OP_MAP_UDP: u8 = 1;
/// The response bit added to the opcode.
pub const RESPONSE: u8 = 128;
/// The address request's length.
pub const ADDRESS_REQUEST_LEN: usize = 2;
/// The mapping request's length.
pub const MAP_REQUEST_LEN: usize = 12;
/// The address response's length.
pub const ADDRESS_RESPONSE_LEN: usize = 12;
/// The mapping response's length.
pub const MAP_RESPONSE_LEN: usize = 16;
/// The error response's length.
pub const ERROR_LEN: usize = 8;

/// A request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Request {
    /// What is the external address?
    Address,
    /// Map UDP `internal_port`, preferably to `external_port`, for `lifetime` seconds (0 deletes).
    Map {
        /// The client's port.
        internal_port: u16,
        /// The external port asked for; 0 lets the server choose.
        external_port: u16,
        /// Seconds.
        lifetime: u32,
    },
}

/// A response.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Response {
    /// The external address.
    Address {
        /// The result code.
        result: u16,
        /// Seconds since the server last lost its mappings.
        epoch: u32,
        /// The external address.
        ip: Ipv4Addr,
    },
    /// A UDP mapping.
    Map {
        /// The result code.
        result: u16,
        /// Seconds since the server last lost its mappings.
        epoch: u32,
        /// The client's port.
        internal_port: u16,
        /// The external port granted.
        external_port: u16,
        /// The lifetime granted, in seconds.
        lifetime: u32,
    },
    /// An error with no body.
    Error {
        /// The opcode answered, without the response bit.
        opcode: u8,
        /// The result code, never 0.
        result: u16,
        /// Seconds since the server last lost its mappings.
        epoch: u32,
    },
}

/// Why a message was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatPmpError {
    /// The output is too small.
    Short,
    /// The length is not the form's.
    Length,
    /// The version byte is not 0.
    Version(u8),
    /// The opcode is not the form's.
    Opcode(u8),
    /// A reserved byte is set, or an error response says success.
    Form,
}

fn write<const N: usize>(out: &mut [u8], b: [u8; N]) -> Result<usize, NatPmpError> {
    out.get_mut(..N).ok_or(NatPmpError::Short)?.copy_from_slice(&b);
    Ok(N)
}

/// Encode `r`; returns its length.
///
/// # Errors
/// [`NatPmpError::Short`] if `out` is too small; nothing is written then.
pub fn encode_request(r: &Request, out: &mut [u8]) -> Result<usize, NatPmpError> {
    match *r {
        Request::Address => write(out, [0, OP_ADDRESS]),
        Request::Map {
            internal_port,
            external_port,
            lifetime,
        } => {
            let [i0, i1] = internal_port.to_be_bytes();
            let [x0, x1] = external_port.to_be_bytes();
            let [l0, l1, l2, l3] = lifetime.to_be_bytes();
            write(out, [0, OP_MAP_UDP, 0, 0, i0, i1, x0, x1, l0, l1, l2, l3])
        }
    }
}

/// Decode a request.
///
/// # Errors
/// The first rule `b` breaks, in the order: version, opcode, length, reserved bytes.
pub fn decode_request(b: &[u8]) -> Result<Request, NatPmpError> {
    match b {
        [0, OP_ADDRESS] => Ok(Request::Address),
        [0, OP_MAP_UDP, r0, r1, i0, i1, x0, x1, l0, l1, l2, l3] => {
            if *r0 != 0 || *r1 != 0 {
                return Err(NatPmpError::Form);
            }
            Ok(Request::Map {
                internal_port: u16::from_be_bytes([*i0, *i1]),
                external_port: u16::from_be_bytes([*x0, *x1]),
                lifetime: u32::from_be_bytes([*l0, *l1, *l2, *l3]),
            })
        }
        [v, ..] if *v != 0 => Err(NatPmpError::Version(*v)),
        [_, op, ..] if *op != OP_ADDRESS && *op != OP_MAP_UDP => Err(NatPmpError::Opcode(*op)),
        _ => Err(NatPmpError::Length),
    }
}

/// Encode `r`; returns its length.
///
/// # Errors
/// [`NatPmpError::Short`] if `out` is too small; [`NatPmpError::Form`] for an error response with result 0 or an
/// opcode that has the response bit, which [`decode_response`] would refuse. Nothing is written then.
pub fn encode_response(r: &Response, out: &mut [u8]) -> Result<usize, NatPmpError> {
    match *r {
        Response::Address { result, epoch, ip } => {
            let [r0, r1] = result.to_be_bytes();
            let [e0, e1, e2, e3] = epoch.to_be_bytes();
            let [o0, o1, o2, o3] = ip.octets();
            write(out, [0, OP_ADDRESS | RESPONSE, r0, r1, e0, e1, e2, e3, o0, o1, o2, o3])
        }
        Response::Map {
            result,
            epoch,
            internal_port,
            external_port,
            lifetime,
        } => {
            let [r0, r1] = result.to_be_bytes();
            let [e0, e1, e2, e3] = epoch.to_be_bytes();
            let [i0, i1] = internal_port.to_be_bytes();
            let [x0, x1] = external_port.to_be_bytes();
            let [l0, l1, l2, l3] = lifetime.to_be_bytes();
            write(
                out,
                [
                    0,
                    OP_MAP_UDP | RESPONSE,
                    r0,
                    r1,
                    e0,
                    e1,
                    e2,
                    e3,
                    i0,
                    i1,
                    x0,
                    x1,
                    l0,
                    l1,
                    l2,
                    l3,
                ],
            )
        }
        Response::Error { opcode, result, epoch } => {
            if result == 0 || opcode & RESPONSE != 0 {
                return Err(NatPmpError::Form);
            }
            let [r0, r1] = result.to_be_bytes();
            let [e0, e1, e2, e3] = epoch.to_be_bytes();
            write(out, [0, opcode | RESPONSE, r0, r1, e0, e1, e2, e3])
        }
    }
}

/// Decode a response.
///
/// # Errors
/// The first rule `b` breaks, in the order: version, opcode and length, form.
pub fn decode_response(b: &[u8]) -> Result<Response, NatPmpError> {
    match b {
        [v, ..] if *v != 0 => Err(NatPmpError::Version(*v)),
        [0, op, r0, r1, e0, e1, e2, e3] => {
            let result = u16::from_be_bytes([*r0, *r1]);
            if op & RESPONSE == 0 {
                return Err(NatPmpError::Opcode(*op));
            }
            if result == 0 {
                return Err(NatPmpError::Form);
            }
            Ok(Response::Error {
                opcode: op & !RESPONSE,
                result,
                epoch: u32::from_be_bytes([*e0, *e1, *e2, *e3]),
            })
        }
        [0, 128, r0, r1, e0, e1, e2, e3, a, b, c, d] => Ok(Response::Address {
            result: u16::from_be_bytes([*r0, *r1]),
            epoch: u32::from_be_bytes([*e0, *e1, *e2, *e3]),
            ip: Ipv4Addr::new(*a, *b, *c, *d),
        }),
        [0, 129, r0, r1, e0, e1, e2, e3, i0, i1, x0, x1, l0, l1, l2, l3] => Ok(Response::Map {
            result: u16::from_be_bytes([*r0, *r1]),
            epoch: u32::from_be_bytes([*e0, *e1, *e2, *e3]),
            internal_port: u16::from_be_bytes([*i0, *i1]),
            external_port: u16::from_be_bytes([*x0, *x1]),
            lifetime: u32::from_be_bytes([*l0, *l1, *l2, *l3]),
        }),
        [_, op, ..] if *op != 128 && *op != 129 => Err(NatPmpError::Opcode(*op)),
        _ => Err(NatPmpError::Length),
    }
}
