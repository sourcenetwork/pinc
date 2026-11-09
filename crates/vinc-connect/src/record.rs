//! A node's signed record: what rendezvous stores and replicates so a peer can be found from its node id.
//!
//! # Wire format
//!
//! `magic(8) node(33) home(33) seq(8) reach(1) n_addrs(1) addrs hint_len(1) hints public_key signature`
//!
//! - `magic` is `"VNCREC"` followed by two version bytes `0, 1`; it is part of the signed bytes, so a record of
//!   another kind never verifies as this one.
//! - `node` is the publisher, `home` is its home relay, `seq` orders the publisher's records (a higher one replaces
//!   a lower one; the publisher uses its clock in milliseconds), `reach` is the reachability class
//!   ([`Reach`]).
//! - Each address is `4 ip(4) port(2)` or `6 ip(16) port(2)`; there are at most [`MAX_ADDRS`] (reflexive and local
//!   addresses together); `hints` is at most [`MAX_HINT_LEN`] opaque bytes (ticket hints).
//! - `public_key` has the length of the node's algorithm, and the node id must be the id of that key;
//!   `signature` has the algorithm's length and covers every byte before it.
//!
//! Invariants: [`Record::parse`] accepts exactly what [`sign`] produces (no trailing bytes, no unknown tag, no
//! over-long list); [`Record::verify`] is the only way a record counts as authentic, and it checks both the key to
//! node id binding and the signature. Nothing here allocates or panics.

use core::fmt;
use core::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use vinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN, verify_node};
use vinc_crypto::{CryptoError, Keypair, NodeId};
use vinc_wire::{Reader, WireError, Writer};

use crate::carrier::node;

/// The most addresses in a record.
pub const MAX_ADDRS: usize = 8;
/// The most ticket-hint bytes in a record.
pub const MAX_HINT_LEN: usize = 64;
/// The longest encoded address.
pub const MAX_ADDR_LEN: usize = 19;
/// The longest encoded record, for the longest identity algorithm.
pub const MAX_RECORD_LEN: usize = MAGIC.len()
    + 2 * node::NODE_ID_LEN
    + 8
    + 2
    + MAX_ADDRS * MAX_ADDR_LEN
    + 1
    + MAX_HINT_LEN
    + MAX_PUBLIC_KEY_LEN
    + MAX_SIGNATURE_LEN;

const MAGIC: &[u8; 8] = b"VNCREC\x00\x01";

/// How a node is reachable (CMP-CON-02), as the node itself observed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reach {
    /// A public IPv4 or IPv6 address: the reflexive address equals the local one.
    Public = 1,
    /// A port mapping holds a public address.
    PortMapped = 2,
    /// Behind a NAT whose mapping is stable across relays.
    Nat = 3,
    /// Behind carrier-grade NAT or a symmetric mapping.
    Cgnat = 4,
    /// UDP is blocked: carriers only.
    UdpBlocked = 5,
}

impl Reach {
    const fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            1 => Some(Self::Public),
            2 => Some(Self::PortMapped),
            3 => Some(Self::Nat),
            4 => Some(Self::Cgnat),
            5 => Some(Self::UdpBlocked),
            _ => None,
        }
    }
}

/// Why a record was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecordError {
    /// A field is truncated or the output is too small.
    Wire(WireError),
    /// The magic bytes are wrong.
    Magic,
    /// An unknown reachability class.
    Reach(u8),
    /// An address tag that is neither 4 nor 6.
    AddrTag(u8),
    /// More than [`MAX_ADDRS`] addresses.
    TooManyAddrs,
    /// More than [`MAX_HINT_LEN`] hint bytes.
    HintsTooLong,
    /// Bytes follow the signature.
    Trailing,
    /// The key does not belong to the node id, or the signature does not verify.
    Signature(CryptoError),
}

impl From<WireError> for RecordError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

impl fmt::Display for RecordError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wire(e) => write!(f, "{e}"),
            Self::Magic => f.write_str("not a record"),
            Self::Reach(t) => write!(f, "unknown reachability class {t}"),
            Self::AddrTag(t) => write!(f, "unknown address tag {t}"),
            Self::TooManyAddrs => f.write_str("too many addresses"),
            Self::HintsTooLong => f.write_str("hints too long"),
            Self::Trailing => f.write_str("bytes after the signature"),
            Self::Signature(e) => write!(f, "record signature refused: {e}"),
        }
    }
}

impl core::error::Error for RecordError {}

/// Append an address: tag, octets, port.
///
/// # Errors
/// [`WireError::BufferTooSmall`] if it does not fit.
pub fn write_addr(w: &mut Writer<'_>, a: &SocketAddr) -> Result<(), WireError> {
    match a.ip() {
        IpAddr::V4(ip) => {
            w.ensure(7)?;
            w.put_u8(4)?;
            w.put_slice(&ip.octets())?;
        }
        IpAddr::V6(ip) => {
            w.ensure(19)?;
            w.put_u8(6)?;
            w.put_slice(&ip.octets())?;
        }
    }
    w.put_u16(a.port())
}

/// Read an address written by [`write_addr`].
///
/// # Errors
/// [`RecordError::AddrTag`] for an unknown tag, [`RecordError::Wire`] if truncated.
pub fn read_addr(r: &mut Reader<'_>) -> Result<SocketAddr, RecordError> {
    let ip = match r.read_u8()? {
        4 => IpAddr::V4(Ipv4Addr::from(r.read_array::<4>()?)),
        6 => IpAddr::V6(Ipv6Addr::from(r.read_array::<16>()?)),
        t => return Err(RecordError::AddrTag(t)),
    };
    Ok(SocketAddr::new(ip, r.read_u16()?))
}

/// The addresses of a parsed record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Addrs<'a> {
    left: u8,
    rest: &'a [u8],
}

#[allow(
    clippy::copy_iterator,
    reason = "the iterator is a slice and a count; copying it is how a record's addresses are walked twice"
)]
impl Iterator for Addrs<'_> {
    type Item = SocketAddr;

    fn next(&mut self) -> Option<SocketAddr> {
        if self.left == 0 {
            return None;
        }
        self.left -= 1;
        let mut r = Reader::new(self.rest);
        let a = read_addr(&mut r).ok()?;
        self.rest = self.rest.get(r.position()..)?;
        Some(a)
    }
}

/// What a publisher puts in its record.
#[derive(Debug, Clone, Copy)]
pub struct RecordFields<'a> {
    /// The home relay.
    pub home: NodeId,
    /// The publisher's sequence number.
    pub seq: u64,
    /// The reachability class.
    pub reach: Reach,
    /// Reflexive and local addresses, at most [`MAX_ADDRS`].
    pub addrs: &'a [SocketAddr],
    /// Ticket hints, at most [`MAX_HINT_LEN`] bytes.
    pub hints: &'a [u8],
}

/// Write everything of a record but its signature into `out`: the fields, then the public key of `node`. Returns
/// the length of those bytes, which are what the signature covers. A host whose key stays in a store signs
/// `out[..len]` there and completes the record with [`finish`].
///
/// # Errors
/// [`RecordError::TooManyAddrs`], [`RecordError::HintsTooLong`] and [`RecordError::Wire`] if `out` is short.
pub fn prepare(
    node: &NodeId,
    public_key: &[u8],
    fields: &RecordFields<'_>,
    out: &mut [u8],
) -> Result<usize, RecordError> {
    if fields.addrs.len() > MAX_ADDRS {
        return Err(RecordError::TooManyAddrs);
    }
    if fields.hints.len() > MAX_HINT_LEN {
        return Err(RecordError::HintsTooLong);
    }
    let mut w = Writer::new(out);
    w.put_slice(MAGIC)?;
    node::write(&mut w, node)?;
    node::write(&mut w, &fields.home)?;
    w.put_u64(fields.seq)?;
    w.put_u8(fields.reach as u8)?;
    w.put_u8(u8::try_from(fields.addrs.len()).map_err(|_| RecordError::TooManyAddrs)?)?;
    for a in fields.addrs {
        write_addr(&mut w, a)?;
    }
    w.put_u8(u8::try_from(fields.hints.len()).map_err(|_| RecordError::HintsTooLong)?)?;
    w.put_slice(fields.hints)?;
    w.put_slice(public_key)?;
    Ok(w.written().len())
}

/// Append `signature` to the `signed` bytes [`prepare`] wrote; returns the record's length.
///
/// # Errors
/// [`RecordError::Wire`] if `out` is short.
pub fn finish(out: &mut [u8], signed: usize, signature: &[u8]) -> Result<usize, RecordError> {
    let end = signed + signature.len();
    out.get_mut(signed..end)
        .ok_or(WireError::BufferTooSmall { needed: end })?
        .copy_from_slice(signature);
    Ok(end)
}

/// Sign `fields` with `keypair` and write the record into `out`; returns its length.
///
/// # Errors
/// [`RecordError::TooManyAddrs`], [`RecordError::HintsTooLong`], [`RecordError::Wire`] if `out` is short, and
/// [`RecordError::Signature`] if the key pair refuses to sign.
pub fn sign(keypair: &Keypair, fields: &RecordFields<'_>, out: &mut [u8]) -> Result<usize, RecordError> {
    let mut pk = [0u8; MAX_PUBLIC_KEY_LEN];
    let n = keypair.public_key(&mut pk).map_err(RecordError::Signature)?;
    let signed = prepare(&keypair.node_id(), pk.get(..n).unwrap_or_default(), fields, out)?;
    let (msg, sig_out) = out
        .split_at_mut_checked(signed)
        .ok_or(WireError::BufferTooSmall { needed: 0 })?;
    let sig_len = keypair.sign(msg, sig_out).map_err(RecordError::Signature)?;
    Ok(signed + sig_len)
}

/// A parsed record borrowing its bytes. Parsing checks the layout only; call [`Record::verify`] before trusting it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Record<'a> {
    /// The publisher.
    pub node: NodeId,
    /// The home relay.
    pub home: NodeId,
    /// The publisher's sequence number.
    pub seq: u64,
    /// The reachability class.
    pub reach: Reach,
    /// The ticket hints.
    pub hints: &'a [u8],
    addrs: Addrs<'a>,
    public_key: &'a [u8],
    signature: &'a [u8],
    signed: &'a [u8],
}

impl<'a> Record<'a> {
    /// Parse the layout of `bytes`.
    ///
    /// # Errors
    /// A [`RecordError`] for anything [`sign`] would not produce.
    pub fn parse(bytes: &'a [u8]) -> Result<Self, RecordError> {
        let mut r = Reader::new(bytes);
        if r.read_bytes(MAGIC.len())? != MAGIC {
            return Err(RecordError::Magic);
        }
        let node = node::read(&mut r)?;
        let home = node::read(&mut r)?;
        let seq = r.read_u64()?;
        let tag = r.read_u8()?;
        let reach = Reach::from_tag(tag).ok_or(RecordError::Reach(tag))?;
        let n = r.read_u8()?;
        if usize::from(n) > MAX_ADDRS {
            return Err(RecordError::TooManyAddrs);
        }
        let addr_start = r.position();
        for _ in 0..n {
            read_addr(&mut r)?;
        }
        let addr_bytes = bytes
            .get(addr_start..r.position())
            .ok_or(WireError::Truncated { needed: 0 })?;
        let hint_len = usize::from(r.read_u8()?);
        if hint_len > MAX_HINT_LEN {
            return Err(RecordError::HintsTooLong);
        }
        let hints = r.read_bytes(hint_len)?;
        let public_key = r.read_bytes(node.alg.public_key_len())?;
        let signed = bytes.get(..r.position()).ok_or(WireError::Truncated { needed: 0 })?;
        let signature = r.read_bytes(node.alg.signature_len())?;
        if !r.is_empty() {
            return Err(RecordError::Trailing);
        }
        Ok(Self {
            node,
            home,
            seq,
            reach,
            hints,
            addrs: Addrs {
                left: n,
                rest: addr_bytes,
            },
            public_key,
            signature,
            signed,
        })
    }

    /// The addresses.
    pub const fn addrs(&self) -> Addrs<'a> {
        self.addrs
    }

    /// Check that the key belongs to the node id and that the signature covers the record.
    ///
    /// # Errors
    /// [`RecordError::Signature`] with the cause.
    pub fn verify(&self) -> Result<(), RecordError> {
        verify_node(&self.node, self.public_key, self.signed, self.signature).map_err(RecordError::Signature)
    }

    /// Parse and verify in one call.
    ///
    /// # Errors
    /// As [`Record::parse`] and [`Record::verify`].
    pub fn parse_verified(bytes: &'a [u8]) -> Result<Self, RecordError> {
        let rec = Self::parse(bytes)?;
        rec.verify()?;
        Ok(rec)
    }
}
