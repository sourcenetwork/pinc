//! Test-only view of the path table for trace validation (cargo feature `trace`, off by default).

use alloc::vec::Vec;

use pinc_crypto::Provider;

use super::Connection;
use super::path::CHALLENGES;
use crate::recovery::PathKind;
use crate::stream::StreamSource;

/// One place of the path table as the connection holds it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(clippy::struct_excessive_bools, reason = "independent flags of the view")]
pub struct SlotView {
    /// The path's id.
    pub id: u64,
    /// Whether the path runs through a node that carries the relay role.
    pub relay: bool,
    /// Whether the path is IPv6.
    pub v6: bool,
    /// Whether the path is validated.
    pub validated: bool,
    /// The challenge outstanding on the path.
    pub challenge: Option<[u8; 8]>,
    /// The challenges kept, the oldest overwritten first.
    pub sent: [Option<[u8; 8]>; CHALLENGES],
    /// The place of `sent` the next challenge takes.
    pub sent_next: usize,
    /// The challenge waits for a packet.
    pub send_challenge: bool,
    /// Probes still to send on the path.
    pub probes_left: u32,
    /// The path is being re-joined after it was abandoned or idled out.
    pub rejoin: bool,
    /// The local address of the path is gone.
    pub gone: bool,
    /// When a datagram last arrived on the path, 0 for never.
    pub last_rx: u64,
    /// When a datagram last left on the path, 0 for never.
    pub last_tx: u64,
    /// The smoothed round trip of the path, 0 while unknown.
    pub rtt: u64,
    /// Bytes received on the path, counted against its amplification budget.
    pub amp_received: u64,
    /// Bytes charged on the path against its amplification budget.
    pub amp_sent: u64,
    /// The bytes the connection may still build a datagram of for the path (`usize::MAX` when unlimited).
    pub amp_room: usize,
}

/// The path table and what the path rules read beside it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathsView {
    /// The places of the table, in slot order.
    pub slots: Vec<Option<SlotView>>,
    /// The index of the active path.
    pub active: usize,
    /// The connection's smoothed round trip, `None` before the first sample.
    pub srtt: Option<u64>,
    /// Probe timeouts in a row.
    pub pto: u32,
    /// Whether the session counts as thin for its path rules.
    pub thin: bool,
    /// Whether the host declared the node thin.
    pub decl: bool,
    /// The connection's clock.
    pub clock: u64,
    /// The bytes of a packet number in a short header now.
    pub pn_len: usize,
    /// The bytes of a connection id this connection's packets carry.
    pub cid_len: usize,
}

conn_impl! {
    /// The path table as the path rules read it (trace validation).
    pub fn trace_paths(&self) -> PathsView {
        PathsView {
            slots: self
                .paths
                .slots
                .iter()
                .enumerate()
                .map(|(i, s)| {
                    s.as_ref().map(|p| SlotView {
                        id: p.id.0,
                        relay: p.info.kind == PathKind::Relay,
                        v6: p.info.v6,
                        validated: p.validated,
                        challenge: p.challenge,
                        sent: p.sent,
                        sent_next: p.sent_next,
                        send_challenge: p.send_challenge,
                        probes_left: p.probes_left,
                        rejoin: p.rejoin,
                        gone: p.gone,
                        last_rx: p.last_rx,
                        last_tx: p.last_tx,
                        rtt: p.rtt,
                        amp_received: p.amp.received(),
                        amp_sent: p.amp.sent(),
                        amp_room: self.amp_room(i),
                    })
                })
                .collect(),
            active: self.paths.active,
            srtt: self.rec.rtt().has_sample().then(|| self.rec.rtt().smoothed()),
            pto: self.rec.pto_count(),
            thin: self.thin_session(),
            decl: self.cfg.thin,
            clock: self.life.clock,
            pn_len: self.pn_len,
            cid_len: self.cfg.cid_len,
        }
    }
}
