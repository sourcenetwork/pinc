//! Local discovery: a signed beacon on the link's multicast group, and how often to send it.
//!
//! A node on a shared link (a LAN, a Wi-Fi network) announces itself so a peer next to it needs no relay. A
//! [`Beacon`] holds the sender's node id, its addresses (at most 4) and a short ticket hint (at most 8 bytes), signed
//! by the node; it is sent to [`GROUP_V4`] or [`GROUP_V6`] on [`PORT`]. A received beacon is only a candidate: its
//! addresses become candidate paths and the handshake proves the node, so a forged or replayed beacon costs one
//! failed handshake. The signature still must verify, which keeps a stranger from steering a dial by naming a node
//! it is not.
//!
//! Wire format: `magic(8) node(33) seq(8) n(1) addrs hint_len(1) hint public_key signature` with the signature over
//! every byte before it, as for a record ([`crate::record`]).
//!
//! [`Duty`] limits the air time. It beacons every [`BURST_GAP`] for [`BURST`] after a start or an interface change,
//! then every [`STEADY_GAP`], and not at all in the steady phase while a mailbox serves the node (a relay already
//! reaches it). [`Radio`] is the host adapter for a medium with its own duty cycle: it admits a beacon only if the
//! medium's frame fits and the share of air time allows it.
//!
//! Invariants: at most `BURST / BURST_GAP` beacons in a burst and one per [`STEADY_GAP`] after it; [`Beacon::parse`]
//! accepts exactly what [`sign`] writes; a beacon that does not verify is never returned as a candidate.

#![allow(clippy::doc_markdown, reason = "rule names are written as the rules call them")]

use core::net::{Ipv4Addr, Ipv6Addr, SocketAddr};

use vinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN, verify_node};
use vinc_crypto::{Keypair, NodeId};
use vinc_wire::{Reader, WireError, Writer};

use crate::carrier::node;
use crate::record::{MAX_ADDR_LEN, RecordError, read_addr, write_addr};

/// The IPv4 multicast group.
pub const GROUP_V4: Ipv4Addr = Ipv4Addr::new(239, 255, 86, 78);
/// The IPv6 multicast group (link-local scope).
pub const GROUP_V6: Ipv6Addr = Ipv6Addr::new(0xff02, 0, 0, 0, 0, 0, 0x5649, 0x4e43);
/// The beacon port.
pub const PORT: u16 = 4435;
/// The most addresses in a beacon.
pub const MAX_ADDRS: usize = 4;
/// The most hint bytes.
pub const MAX_HINT: usize = 8;
/// The longest beacon.
pub const MAX_LEN: usize =
    8 + node::NODE_ID_LEN + 8 + 2 + MAX_ADDRS * MAX_ADDR_LEN + MAX_HINT + MAX_PUBLIC_KEY_LEN + MAX_SIGNATURE_LEN;
/// The gap between beacons in the opening burst.
pub const BURST_GAP: u64 = 1_000_000_000;
/// How long the opening burst lasts.
pub const BURST: u64 = 5_000_000_000;
/// The gap between beacons after the burst.
pub const STEADY_GAP: u64 = 60_000_000_000;

const MAGIC: &[u8; 8] = b"VNCBCN\x00\x01";

/// A parsed beacon.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Beacon<'a> {
    /// The sender.
    pub node: NodeId,
    /// The sender's sequence number (its clock in milliseconds).
    pub seq: u64,
    /// The ticket hint.
    pub hint: &'a [u8],
    addrs: [Option<SocketAddr>; MAX_ADDRS],
    public_key: &'a [u8],
    signature: &'a [u8],
    signed: &'a [u8],
}

/// Why a beacon was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BeaconError {
    /// Truncated, or the output is too small.
    Wire(WireError),
    /// Not a beacon.
    Magic,
    /// A malformed address.
    Addr(RecordError),
    /// More addresses or hint bytes than allowed.
    TooLong,
    /// Bytes follow the signature.
    Trailing,
    /// The key does not belong to the node id, or the signature does not verify.
    Signature,
}

impl From<WireError> for BeaconError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

/// Write everything of a beacon but its signature into `out`; returns the length of those bytes, which the
/// signature covers. Sign `out[..len]` with the node's key and complete the beacon with [`finish`].
///
/// # Errors
/// [`BeaconError::TooLong`] for too many addresses or hint bytes, [`BeaconError::Wire`] if `out` is short.
pub fn prepare(
    node: &NodeId,
    public_key: &[u8],
    seq: u64,
    addrs: &[SocketAddr],
    hint: &[u8],
    out: &mut [u8],
) -> Result<usize, BeaconError> {
    if addrs.len() > MAX_ADDRS || hint.len() > MAX_HINT {
        return Err(BeaconError::TooLong);
    }
    let mut w = Writer::new(out);
    w.put_slice(MAGIC)?;
    node::write(&mut w, node)?;
    w.put_u64(seq)?;
    w.put_u8(u8::try_from(addrs.len()).map_err(|_| BeaconError::TooLong)?)?;
    for a in addrs {
        write_addr(&mut w, a)?;
    }
    w.put_u8(u8::try_from(hint.len()).map_err(|_| BeaconError::TooLong)?)?;
    w.put_slice(hint)?;
    w.put_slice(public_key)?;
    Ok(w.written().len())
}

/// Append `signature` to the `signed` bytes [`prepare`] wrote; returns the beacon's length.
///
/// # Errors
/// [`BeaconError::Wire`] if `out` is short.
pub fn finish(out: &mut [u8], signed: usize, signature: &[u8]) -> Result<usize, BeaconError> {
    let end = signed + signature.len();
    out.get_mut(signed..end)
        .ok_or(WireError::BufferTooSmall { needed: end })?
        .copy_from_slice(signature);
    Ok(end)
}

/// Sign a beacon for `keypair` and write it into `out`; returns its length.
///
/// # Errors
/// [`BeaconError::TooLong`] for too many addresses or hint bytes, [`BeaconError::Wire`] if `out` is short,
/// [`BeaconError::Signature`] if the key refuses to sign.
pub fn sign(
    keypair: &Keypair,
    seq: u64,
    addrs: &[SocketAddr],
    hint: &[u8],
    out: &mut [u8],
) -> Result<usize, BeaconError> {
    let mut pk = [0u8; MAX_PUBLIC_KEY_LEN];
    let n = keypair.public_key(&mut pk).map_err(|_| BeaconError::Signature)?;
    let signed = prepare(
        &keypair.node_id(),
        pk.get(..n).unwrap_or_default(),
        seq,
        addrs,
        hint,
        out,
    )?;
    let (msg, sig_out) = out
        .split_at_mut_checked(signed)
        .ok_or(WireError::BufferTooSmall { needed: 0 })?;
    let sig = keypair.sign(msg, sig_out).map_err(|_| BeaconError::Signature)?;
    Ok(signed + sig)
}

impl<'a> Beacon<'a> {
    /// Parse the layout of `bytes`; call [`Beacon::verify`] before using it.
    ///
    /// # Errors
    /// A [`BeaconError`] for anything [`sign`] would not write.
    pub fn parse(bytes: &'a [u8]) -> Result<Self, BeaconError> {
        let mut r = Reader::new(bytes);
        if r.read_bytes(MAGIC.len())? != MAGIC {
            return Err(BeaconError::Magic);
        }
        let node = node::read(&mut r)?;
        let seq = r.read_u64()?;
        let n = usize::from(r.read_u8()?);
        if n > MAX_ADDRS {
            return Err(BeaconError::TooLong);
        }
        let mut addrs = [None; MAX_ADDRS];
        for a in addrs.iter_mut().take(n) {
            *a = Some(read_addr(&mut r).map_err(BeaconError::Addr)?);
        }
        let hl = usize::from(r.read_u8()?);
        if hl > MAX_HINT {
            return Err(BeaconError::TooLong);
        }
        let hint = r.read_bytes(hl)?;
        let signed_len = r.position();
        let public_key = r.read_bytes(node.alg.public_key_len())?;
        let signed = bytes
            .get(..signed_len + public_key.len())
            .ok_or(WireError::Truncated { needed: 0 })?;
        let signature = r.read_bytes(node.alg.signature_len())?;
        if !r.is_empty() {
            return Err(BeaconError::Trailing);
        }
        Ok(Self {
            node,
            seq,
            hint,
            addrs,
            public_key,
            signature,
            signed,
        })
    }

    /// The addresses.
    pub fn addrs(&self) -> impl Iterator<Item = SocketAddr> + '_ {
        self.addrs.iter().flatten().copied()
    }

    /// Check the key to node id binding and the signature.
    ///
    /// # Errors
    /// [`BeaconError::Signature`].
    pub fn verify(&self) -> Result<(), BeaconError> {
        verify_node(&self.node, self.public_key, self.signed, self.signature).map_err(|_| BeaconError::Signature)
    }

    /// Parse and verify.
    ///
    /// # Errors
    /// As [`Beacon::parse`] and [`Beacon::verify`].
    pub fn parse_verified(bytes: &'a [u8]) -> Result<Self, BeaconError> {
        let b = Self::parse(bytes)?;
        b.verify()?;
        Ok(b)
    }
}

/// The beacon schedule.
#[derive(Debug, Clone, Copy)]
pub struct Duty {
    burst_from: u64,
    next: u64,
    sent: u64,
    mailbox: bool,
}

impl Duty {
    /// A schedule that starts its burst at `now`.
    pub const fn new(now: u64) -> Self {
        Self {
            burst_from: now,
            next: now,
            sent: 0,
            mailbox: false,
        }
    }

    /// A start or an interface change: burst again from `now`.
    pub const fn restart(&mut self, now: u64) {
        self.burst_from = now;
        self.next = now;
    }

    /// A mailbox serves the node (or stopped doing so): the steady phase is off while it does.
    pub const fn set_mailbox(&mut self, serves: bool) {
        self.mailbox = serves;
    }

    /// How many beacons the schedule released.
    pub const fn sent(&self) -> u64 {
        self.sent
    }

    /// Whether a beacon is due at `now`. Returns true once per release and schedules the next.
    pub fn poll(&mut self, now: u64) -> bool {
        if now < self.next {
            return false;
        }
        let in_burst = now.saturating_sub(self.burst_from) < BURST;
        if !in_burst && self.mailbox {
            self.next = now.saturating_add(STEADY_GAP);
            return false;
        }
        self.sent += 1;
        let after = now.saturating_add(BURST_GAP);
        self.next = if after.saturating_sub(self.burst_from) < BURST {
            after
        } else {
            now.saturating_add(STEADY_GAP)
        };
        true
    }

    /// When the schedule next wants a call.
    pub const fn deadline(&self) -> u64 {
        self.next
    }
}

/// A radio medium's limits: the largest frame and the share of time a node may transmit.
#[derive(Debug, Clone, Copy)]
pub struct Radio {
    /// The largest frame the medium carries.
    pub mtu: usize,
    /// Air time per byte in nanoseconds.
    pub ns_per_byte: u64,
    /// The permitted share of time on air, in parts per thousand.
    pub duty_permille: u64,
    ready_at: u64,
}

impl Radio {
    /// A medium with these limits, free to send now.
    pub const fn new(mtu: usize, ns_per_byte: u64, duty_permille: u64) -> Self {
        Self {
            mtu,
            ns_per_byte,
            duty_permille,
            ready_at: 0,
        }
    }

    /// Admit a frame of `len` bytes at `now`: it must fit the medium and its air time must be paid for by the duty
    /// share since the last frame. On success the next admission waits for the off time that keeps the share.
    pub fn admit(&mut self, now: u64, len: usize) -> bool {
        if len > self.mtu || now < self.ready_at || self.duty_permille == 0 {
            return false;
        }
        let air = (len as u64).saturating_mul(self.ns_per_byte);
        self.ready_at = now.saturating_add(air.saturating_mul(1000) / self.duty_permille);
        true
    }
}
