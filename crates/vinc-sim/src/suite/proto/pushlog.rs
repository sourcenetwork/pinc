//! PUSHLOG: ordered pushes to replicators.
//!
//! One connection and one stream per (origin, replicator). Each push takes the next sequence number from the
//! durable log and stays there until a cumulative acknowledgement; on every (re)connect all unacknowledged pushes
//! are sent again. The replicator delivers sequence `exp` exactly once (a gap delivers anyway and records a G-ORDER
//! violation, an old sequence is only acknowledged again) and acknowledges its high-water mark after every push.
//!
//! Invariants: the log is written before the bytes; reconnecting backs off from 1 s doubling to 8 s and resets on a
//! connection; after a restart the unacknowledged pushes are retried 100 ms after start.

use vinc_core::SessionId;

use super::body;
use super::durable::Unacked;
use super::frame::{Frame, T_ACK, T_PUSH, hdr};
use super::host::Host;
use super::stack::{ALPN_PUSHLOG, Key, Proto, Role, Stack, Stream, Timers};
use crate::suite::crypto::MsgId;

const BACKOFF_FIRST: u64 = 1_000_000_000;
const BACKOFF_MAX: u64 = 8_000_000_000;
const BOOT_RETRY: u64 = 100_000_000;
/// The harness bound on a replicator's unacknowledged pushes (never reached in public scenarios).
const MAX_UNACKED: usize = 4096;

/// What the origin knows of the way to one replicator (volatile).
#[derive(Debug)]
pub(super) struct PushPeer {
    session: Option<SessionId>,
    stream: Option<Key>,
    connecting: bool,
    backoff: u64,
    retry_at: Option<u64>,
}

impl PushPeer {
    fn new() -> Self {
        Self {
            session: None,
            stream: None,
            connecting: false,
            backoff: BACKOFF_FIRST,
            retry_at: None,
        }
    }

    fn schedule_retry(&mut self, timers: &mut Timers, now: u64) {
        let at = now + self.backoff;
        self.retry_at = Some(at);
        self.backoff = (self.backoff * 2).min(BACKOFF_MAX);
        timers.0.insert(at);
    }
}

const NOT_PAYLOAD: &str = "body is not payload (stream corrupted or reordered)";

fn push_frame(host: &dyn Host, u: &Unacked) -> Vec<u8> {
    let mut f = hdr(T_PUSH, u.len as usize, u.seq).to_vec();
    f.extend_from_slice(&body::render(host.registry(), u.msg, u.len));
    f
}

impl Stack {
    pub(super) fn pl_boot(&mut self, now: u64) {
        let pending: Vec<(usize, bool)> = self
            .durable
            .borrow()
            .pl_out
            .iter()
            .map(|(p, o)| (*p, !o.unacked.is_empty()))
            .collect();
        for (peer, has) in pending {
            let mut pp = PushPeer::new();
            if has {
                pp.retry_at = Some(now + BOOT_RETRY);
                self.pl_timers.0.insert(now + BOOT_RETRY);
            }
            self.pl_peers.insert(peer, pp);
        }
    }

    /// Appends a push to the durable log towards `rep` and sends it if a stream is up.
    pub(super) fn pl_push(&mut self, now: u64, host: &mut dyn Host, rep: usize, iid: u32, msg: MsgId, len: u64) {
        let (u, overflow) = {
            let mut d = self.durable.borrow_mut();
            let out = d.pl_out.entry(rep).or_default();
            out.seq += 1;
            let u = Unacked {
                seq: out.seq,
                iid,
                msg,
                len,
            };
            out.unacked.push_back(u);
            let overflow = out.unacked.len() > MAX_UNACKED;
            if overflow {
                out.unacked.pop_front();
            }
            (u, overflow)
        };
        if overflow {
            self.violation(now, "G-SPEC", "the push log of a replicator overflowed its bound");
        }
        let st = self.pl_peers.entry(rep).or_insert_with(PushPeer::new);
        if let Some(key) = st.stream {
            let f = push_frame(host, &u);
            self.send(host, key, &f, false);
        } else if !st.connecting {
            self.pl_connect(now, host, rep);
        }
    }

    fn pl_connect(&mut self, now: u64, host: &mut dyn Host, peer: usize) {
        let Some(st) = self.pl_peers.get_mut(&peer) else { return };
        st.connecting = true;
        if !host.connect(peer, ALPN_PUSHLOG) {
            st.connecting = false;
            st.schedule_retry(&mut self.pl_timers, now);
        }
    }

    pub(super) fn pl_connected(&mut self, _now: u64, host: &mut dyn Host, session: SessionId, peer: usize) {
        let Some(st) = self.pl_peers.get_mut(&peer).filter(|s| s.connecting) else {
            host.close(session, 0);
            return;
        };
        st.connecting = false;
        st.session = Some(session);
        st.backoff = BACKOFF_FIRST;
        let Some(stream) = host.open_stream(session) else {
            host.close(session, 0);
            return;
        };
        let key = (session, stream);
        st.stream = Some(key);
        self.streams.insert(key, Stream::new(Role::None));
        let unacked: Vec<Unacked> = self
            .durable
            .borrow()
            .pl_out
            .get(&peer)
            .map(|o| o.unacked.iter().copied().collect())
            .unwrap_or_default();
        for u in unacked {
            let f = push_frame(host, &u);
            self.send(host, key, &f, false);
        }
    }

    pub(super) fn pl_connect_failed(&mut self, now: u64, peer: usize) {
        if let Some(st) = self.pl_peers.get_mut(&peer) {
            st.connecting = false;
            st.schedule_retry(&mut self.pl_timers, now);
        }
    }

    pub(super) fn pl_closed(&mut self, now: u64, session: SessionId, peer: usize) {
        let has = self
            .durable
            .borrow()
            .pl_out
            .get(&peer)
            .is_some_and(|o| !o.unacked.is_empty());
        if let Some(st) = self.pl_peers.get_mut(&peer)
            && st.session == Some(session)
        {
            st.session = None;
            st.stream = None;
            if has {
                st.schedule_retry(&mut self.pl_timers, now);
            }
        }
    }

    pub(super) fn pl_timeout(&mut self, now: u64, host: &mut dyn Host) {
        self.pl_timers.pop_due(now);
        let due: Vec<usize> = self
            .pl_peers
            .iter()
            .filter(|(_, s)| s.retry_at.is_some_and(|t| t <= now))
            .map(|(p, _)| *p)
            .collect();
        for peer in due {
            let has = self
                .durable
                .borrow()
                .pl_out
                .get(&peer)
                .is_some_and(|o| !o.unacked.is_empty());
            let go = self.pl_peers.get_mut(&peer).is_some_and(|st| {
                st.retry_at = None;
                st.session.is_none() && !st.connecting && has
            });
            if go {
                self.pl_connect(now, host, peer);
            }
        }
    }

    pub(super) fn pl_frame(&mut self, now: u64, host: &mut dyn Host, key: Key, f: &Frame) -> Result<(), String> {
        let Some(peer) = self.sessions.get(&key.0).map(|s| s.peer) else {
            return Ok(());
        };
        match (f.ty, f.body.as_deref()) {
            (T_PUSH, Some(b)) => {
                let msg = body::message_id(b).ok_or(NOT_PAYLOAD)?;
                if !self.check_origin(now, host.registry(), Proto::PushLog, peer, msg) {
                    return Ok(());
                }
                let exp = self.durable.borrow().pl_in.get(&peer).copied().unwrap_or(1);
                if f.id >= exp {
                    if f.id > exp {
                        self.violation(
                            now,
                            "G-ORDER",
                            &format!("PUSHLOG gap: expected seq {exp}, got {}", f.id),
                        );
                    }
                    self.durable.borrow_mut().pl_in.insert(peer, f.id + 1);
                    self.pushlog_delivered(now, host.registry(), peer, f.id, b);
                }
                let high = self.durable.borrow().pl_in.get(&peer).copied().unwrap_or(1) - 1;
                self.send(host, key, &hdr(T_ACK, 0, high), false);
            }
            (T_ACK, _) => {
                if let Some(o) = self.durable.borrow_mut().pl_out.get_mut(&peer) {
                    while o.unacked.front().is_some_and(|u| u.seq <= f.id) {
                        o.unacked.pop_front();
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}
