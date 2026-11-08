//! The handshake driver: carries `vinc-security` messages in long Handshake packets and runs its retransmit timer.
//!
//! A handshake message can be longer than a datagram, so a Handshake packet body is
//! `total(varint) offset(varint) fragment`: the message length, where the fragment starts and its bytes. The sender
//! cuts the message into datagram-sized fragments; the receiver keeps every fragment that arrives, in any order, in a
//! buffer of the largest message size with a bounded set of received runs, so a lost fragment costs only the
//! retransmission, which sends the flight again and completes the message. Both directions hold one message in a fixed buffer: nothing here allocates.
//!
//! Invariants: the reassembly buffer never holds more than [`MAX_MESSAGE_LEN`] bytes and a message is handed to the
//! state machine only when complete; the retransmit timer doubles from `max(500 ms, 2 x RTT)` up to
//! `max(16 s, 4 x RTT)` (8 s on a thin node) and stops once the handshake is confirmed.

use vinc_crypto::provider::KEM_CIPHERTEXT_LEN;
use vinc_crypto::{IdentityAlg, Provider};
use vinc_security::message::MAX_MESSAGE_LEN;
use vinc_security::{
    Env, Event as SecEvent, Failure, Initiator, KeyHandle, KeyRequest, Output, Responder, ResponderStores,
};
use vinc_wire::{Reader, varint};

use crate::recovery::{MS, SECOND};

/// The first retransmit delay when no round trip is remembered.
const RETX_BASE: u64 = 500 * MS;
/// The longest retransmit delay, unless 4 round trips are longer.
const RETX_CAP: u64 = 16 * SECOND;
/// The longest retransmit delay of a thin node.
const RETX_CAP_THIN: u64 = 8 * SECOND;

/// The most disjoint runs of one message the receiver tracks (a message is a handful of datagrams).
const RUNS: usize = 8;

/// The longest message a key request signs.
const SIGN_MAX: usize = 64;

/// One of the two state machines.
#[allow(
    clippy::large_enum_variant,
    reason = "one per connection, held inline so nothing allocates"
)]
pub(crate) enum Machine {
    Client(Initiator),
    Server(Responder),
}

/// An owned copy of a key request, so it can be shown as an event after the machine's borrow ended.
#[allow(clippy::large_enum_variant, reason = "held inline so nothing allocates")]
pub(crate) enum OwnedRequest {
    Sign {
        key: KeyHandle,
        alg: IdentityAlg,
        msg: [u8; SIGN_MAX],
        len: usize,
    },
    Decap {
        key: KeyHandle,
        ct: [u8; KEM_CIPHERTEXT_LEN],
    },
}

impl OwnedRequest {
    pub(crate) fn as_request(&self) -> KeyRequest<'_> {
        match self {
            Self::Sign { key, alg, msg, len } => KeyRequest::Sign {
                key: *key,
                alg: *alg,
                message: msg.get(..*len).unwrap_or_default(),
            },
            Self::Decap { key, ct } => KeyRequest::Decapsulate { key: *key, ct },
        }
    }
}

/// The handshake state of a connection.
pub(crate) struct Handshake {
    pub(crate) machine: Machine,
    tx: [u8; MAX_MESSAGE_LEN],
    tx_len: usize,
    tx_min: usize,
    tx_off: usize,
    tx_total_sent: usize,
    tx_active: bool,
    rx: [u8; MAX_MESSAGE_LEN],
    rx_runs: [(usize, usize); RUNS],
    rx_len: usize,
    rx_total: usize,
    pub(crate) request: Option<OwnedRequest>,
    pub(crate) request_announced: bool,
    retx_at: Option<u64>,
    retx_interval: u64,
    cap: u64,
}

impl Handshake {
    pub(crate) fn new(machine: Machine, now: u64, thin: bool, rtt: Option<u64>) -> Self {
        let base = rtt.map_or(RETX_BASE, |r| RETX_BASE.max(r.saturating_mul(2)));
        let cap = rtt.map_or(RETX_CAP, |r| RETX_CAP.max(r.saturating_mul(4)));
        let cap = if thin { cap.min(RETX_CAP_THIN) } else { cap };
        Self {
            machine,
            tx: [0; MAX_MESSAGE_LEN],
            tx_len: 0,
            tx_min: 0,
            tx_off: 0,
            tx_total_sent: 0,
            tx_active: false,
            rx: [0; MAX_MESSAGE_LEN],
            rx_runs: [(0, 0); RUNS],
            rx_len: 0,
            rx_total: 0,
            request: None,
            request_announced: false,
            retx_at: Some(now.saturating_add(base)),
            retx_interval: base.min(cap),
            cap,
        }
    }

    /// Drain the machine until it reports an event. Messages and key requests are copied out; the event is returned.
    pub(crate) fn step(&mut self) -> Option<SecEvent> {
        loop {
            let out = match &mut self.machine {
                Machine::Client(m) => m.poll_output(),
                Machine::Server(m) => m.poll_output(),
            };
            match out? {
                Output::Send { data, min_len } => {
                    if let Some(dst) = self.tx.get_mut(..data.len()) {
                        dst.copy_from_slice(data);
                        self.tx_len = data.len();
                        self.tx_min = min_len;
                        self.tx_off = 0;
                        self.tx_total_sent = 0;
                        self.tx_active = true;
                    }
                }
                Output::Key(req) => {
                    self.request = Some(match req {
                        KeyRequest::Sign { key, alg, message } => {
                            let mut msg = [0u8; SIGN_MAX];
                            let len = message.len().min(SIGN_MAX);
                            if let (Some(d), Some(s)) = (msg.get_mut(..len), message.get(..len)) {
                                d.copy_from_slice(s);
                            }
                            OwnedRequest::Sign { key, alg, msg, len }
                        }
                        KeyRequest::Decapsulate { key, ct } => OwnedRequest::Decap { key, ct: *ct },
                    });
                    self.request_announced = false;
                }
                Output::Event(e) => return Some(e),
            }
        }
    }

    /// Whether there are fragments or padding left to send.
    pub(crate) const fn has_tx(&self) -> bool {
        self.tx_active
    }

    /// The next fragment of at most `room` bytes after the two varints, as `(total, offset, bytes)`.
    pub(crate) fn next_fragment(&mut self, room: usize) -> Option<(usize, usize, &[u8])> {
        if !self.tx_active || self.tx_off >= self.tx_len {
            return None;
        }
        let end = self.tx_len.min(self.tx_off + room);
        let off = self.tx_off;
        self.tx_off = end;
        let bytes = self.tx.get(off..end)?;
        Some((self.tx_len, off, bytes))
    }

    /// The fixed bytes a fragment header spends: both varints at their current size.
    pub(crate) fn fragment_overhead(&self) -> usize {
        varint::encoded_len(self.tx_len as u64) + varint::encoded_len(self.tx_off as u64)
    }

    /// Record that a datagram of `len` bytes carried this flight; returns how many zero bytes it should be padded
    /// with so the flight totals at least the message's minimum, within `room`.
    pub(crate) fn account(&mut self, len: usize, room: usize) -> usize {
        let done = self.tx_off >= self.tx_len;
        let before = self.tx_total_sent;
        let pad = if done {
            self.tx_min.saturating_sub(before + len).min(room)
        } else {
            0
        };
        self.tx_total_sent = before + len + pad;
        if done && self.tx_total_sent >= self.tx_min {
            self.tx_active = false;
        }
        pad
    }

    /// Zero bytes still owed after the last fragment went out (a flight padded across datagrams).
    pub(crate) fn padding_owed(&self) -> usize {
        if self.tx_active && self.tx_off >= self.tx_len {
            self.tx_min.saturating_sub(self.tx_total_sent)
        } else {
            0
        }
    }

    /// A fragment arrived, in any order. Returns the length of the complete message once every byte is in;
    /// [`Self::feed`] hands it to the state machine.
    pub(crate) fn on_fragment(&mut self, body: &[u8]) -> Option<usize> {
        let mut r = Reader::new(body);
        let total = usize::try_from(r.read_varint().ok()?).ok()?;
        let off = usize::try_from(r.read_varint().ok()?).ok()?;
        let data = r.read_bytes(r.remaining()).ok()?;
        if total == 0 || total > MAX_MESSAGE_LEN {
            return None;
        }
        if total != self.rx_total {
            self.rx_total = total;
            self.rx_runs = [(0, 0); RUNS];
            self.rx_len = 0;
        }
        let end = off.checked_add(data.len())?.min(total);
        let data = data.get(..end.checked_sub(off)?)?;
        if data.is_empty() {
            return None;
        }
        // Merge the new run into the sorted, disjoint runs; with no free slot the fragment is dropped and the
        // retransmission brings it again.
        let (mut lo, mut hi) = (off, end);
        let mut keep = [(0usize, 0usize); RUNS];
        let mut n = 0;
        for &(s, e) in self.rx_runs.iter().take(self.rx_len) {
            if e < lo || s > hi {
                *keep.get_mut(n)? = (s, e);
                n += 1;
            } else {
                lo = lo.min(s);
                hi = hi.max(e);
            }
        }
        if n == RUNS {
            return None;
        }
        self.rx.get_mut(off..end)?.copy_from_slice(data);
        *keep.get_mut(n)? = (lo, hi);
        n += 1;
        keep.get_mut(..n)?.sort_unstable();
        self.rx_runs = keep;
        self.rx_len = n;
        if n == 1 && lo == 0 && hi == total {
            self.rx_total = 0;
            self.rx_len = 0;
            return Some(total);
        }
        None
    }

    /// Hand the complete message of `len` bytes to the state machine. A server needs the shared `stores`.
    pub(crate) fn feed<P: Provider, const PK: usize, const TK: usize>(
        &mut self,
        env: &mut Env<'_, P>,
        stores: Option<&mut ResponderStores<PK, TK>>,
        len: usize,
    ) -> Result<(), Failure> {
        let msg = self.rx.get(..len).ok_or(Failure::InvalidParameter)?;
        match (&mut self.machine, stores) {
            (Machine::Client(m), _) => m.handle(env, msg),
            (Machine::Server(m), Some(stores)) => m.handle(env, stores, msg),
            (Machine::Server(_), None) => Err(Failure::InvalidParameter),
        }
    }

    /// When the retransmit timer fires next, if it runs.
    pub(crate) const fn retransmit_at(&self) -> Option<u64> {
        self.retx_at
    }

    /// Run the timer if due: the machine queues its flight again and the delay doubles. Returns whether it fired.
    pub(crate) fn on_timer(&mut self, now: u64) -> bool {
        if self.retx_at.is_none_or(|t| t > now) {
            return false;
        }
        match &mut self.machine {
            Machine::Client(m) => {
                // The error type matches the encoder's and `retransmit` never fails in practice; a failure stops the machine
                // and surfaces as its event.
                let _ = m.retransmit();
            }
            Machine::Server(m) => m.retransmit(),
        }
        self.retx_interval = self.retx_interval.saturating_mul(2).min(self.cap);
        self.retx_at = Some(now.saturating_add(self.retx_interval));
        true
    }

    /// Stop the timer: the handshake is confirmed.
    pub(crate) fn confirm(&mut self) {
        self.retx_at = None;
    }
}
