//! Test-only observation of the key layer, for trace validation (cargo feature `trace`, off by default).
//!
//! A connection with the feature records one [`KeyEvent`] per step of the key layer it takes (a roll begun, a
//! 1-RTT packet sealed, a 1-RTT packet received, a lost REKEY message queued again) and can show its key state
//! as a [`KeysView`]. Keys are shown as fingerprints (equal fingerprints, equal secrets). The log is drained with
//! [`Connection::trace_take`]. Nothing here is compiled without the feature, and nothing here feeds back into the
//! connection.

use alloc::vec::Vec;

use vinc_crypto::Provider;
use vinc_security::Rekey;

use super::Sel;
use crate::conn::Connection;
use crate::stream::StreamSource;

/// The receive key a packet was opened with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Slot {
    /// The current generation.
    Current,
    /// The previous generation, held for one probe timeout.
    Previous,
    /// The staged next generation.
    Next,
}

impl From<Sel> for Slot {
    fn from(s: Sel) -> Self {
        match s {
            Sel::Current => Self::Current,
            Sel::Previous => Self::Previous,
            Sel::Next => Self::Next,
        }
    }
}

/// One step of the key layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KeyEvent {
    /// A roll started.
    Begun {
        /// The time of the call.
        now: u64,
    },
    /// A 1-RTT packet was sealed.
    Sent {
        /// The time of the call.
        now: u64,
        /// The probe timeout in force.
        pto: u64,
        /// The packet number.
        pn: u64,
        /// The phase bit of the header.
        phase: bool,
        /// The fingerprint of the sealing key.
        key: u64,
        /// The REKEY message the packet carries.
        rekey: Option<Rekey>,
    },
    /// A 1-RTT packet arrived.
    Received {
        /// The time of the call.
        now: u64,
        /// The probe timeout in force.
        pto: u64,
        /// The packet number (as received, estimated when the packet did not open).
        pn: u64,
        /// The phase bit of the header.
        phase: bool,
        /// The key chosen for the packet; `None` when no key applies.
        slot: Option<Slot>,
        /// Whether the packet opened.
        opened: bool,
        /// Whether the packet was a repeat of one already processed.
        dup: bool,
        /// Whether the packet promoted the staged key.
        promoted: bool,
        /// The REKEY message the packet carried and the connection acted on.
        rekey: Option<Rekey>,
    },
    /// A lost answer was queued again.
    AnswerRequeued,
    /// A lost request will be sent at the next opportunity.
    RequestLost,
}

/// The key state of a connection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeysView {
    /// The phase bit of the packets sent.
    pub send_phase: bool,
    /// The fingerprint of the sending key.
    pub send_key: u64,
    /// The fingerprint of the staged sending key.
    pub staged_send: Option<u64>,
    /// The phase bit of the current receive key.
    pub recv_phase: bool,
    /// The fingerprint of the current receive key.
    pub recv_key: u64,
    /// The lowest packet number seen in the phase.
    pub first_pn: u64,
    /// The previous receive key and its hold deadline.
    pub prev: Option<(u64, u64)>,
    /// The staged receive key and its floor.
    pub next: Option<(u64, u64)>,
    /// The next packet number to seal.
    pub next_pn: u64,
    /// Whether the roll machine is idle.
    pub idle: bool,
    /// The request waiting for its answer.
    pub pending: Option<Rekey>,
    /// The share of the last request answered and the answer given.
    pub last: Option<([u8; 32], Rekey)>,
    /// Completed rolls.
    pub rolls: u64,
    /// The REKEY message waiting for a packet.
    pub out: Option<Rekey>,
    /// The last answer sent.
    pub last_answer: Option<Rekey>,
    /// When the pending request last went out.
    pub request_at: Option<u64>,
}

/// What the connection records: the log and the REKEY message of the packet being sent or received.
#[derive(Debug)]
pub(crate) struct Recorder {
    pub(crate) log: Vec<(KeyEvent, Option<KeysView>)>,
    pub(crate) tx: Option<Rekey>,
    pub(crate) rx: Option<Rekey>,
}

impl Recorder {
    pub(crate) const fn new() -> Self {
        Self {
            log: Vec::new(),
            tx: None,
            rx: None,
        }
    }
}

conn_impl! {
    /// The key events since the last call, oldest first, each with the key state right after it (`None` for a
    /// loss event, which the connection notes from inside the key layer).
    pub fn trace_take(&mut self) -> Vec<(KeyEvent, Option<KeysView>)> {
        core::mem::take(&mut self.keys.rec.log)
    }

    /// The key state, once the 1-RTT keys are installed.
    pub fn trace_keys(&self) -> Option<KeysView> {
        let (s, r) = (self.keys.send.as_ref()?, self.keys.recv.as_ref()?);
        Some(KeysView {
            send_phase: s.phase,
            send_key: s.pk.fingerprint(),
            staged_send: self.keys.staged_send.as_ref().map(|k| k.fingerprint()),
            recv_phase: r.phase,
            recv_key: r.cur.fingerprint(),
            first_pn: r.first_pn,
            prev: r.prev.as_ref().map(|(k, until)| (k.fingerprint(), *until)),
            next: r.next.as_ref().map(|n| (n.pk.fingerprint(), n.floor)),
            next_pn: self.next_pn,
            idle: self.keys.roll.is_idle(),
            pending: self.keys.roll.pending(),
            last: self.keys.roll.last_answered(),
            rolls: self.keys.roll.rolls(),
            out: self.keys.out,
            last_answer: self.keys.last_answer,
            request_at: self.keys.request_at,
        })
    }

    /// Note the REKEY message put in the packet being built.
    pub(in crate::conn) fn trace_tx(&mut self, rekey: Rekey) {
        self.keys.rec.tx = Some(rekey);
    }

    /// Note a sealed 1-RTT packet `pn` with the message it carries.
    pub(in crate::conn) fn trace_sent(&mut self, now: u64, pn: u64) {
        let Some(s) = self.keys.send.as_ref() else { return };
        let ev = KeyEvent::Sent {
            now,
            pto: self.rec.pto_duration(),
            pn,
            phase: s.phase,
            key: s.pk.fingerprint(),
            rekey: self.keys.rec.tx.take(),
        };
        self.trace_note(ev);
    }

    /// Note a received 1-RTT packet: `seen` is its number, phase bit and key choice.
    pub(in crate::conn) fn trace_rx_event(
        &mut self,
        now: u64,
        seen: (u64, bool, Option<Sel>),
        opened: bool,
        dup: bool,
        promoted: bool,
    ) {
        let ev = KeyEvent::Received {
            now,
            pto: self.rec.pto_duration(),
            pn: seen.0,
            phase: seen.1,
            slot: seen.2.map(Slot::from),
            opened,
            dup,
            promoted,
            rekey: self.keys.rec.rx.take(),
        };
        self.trace_note(ev);
    }

    /// Note a step of the key layer.
    pub(super) fn trace_note(&mut self, ev: KeyEvent) {
        let view = self.trace_keys();
        self.keys.rec.log.push((ev, view));
    }
}
