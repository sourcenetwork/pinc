//! DOCSYNC and MANAGE: request and response over one bidirectional stream per request.
//!
//! Connections are cached per peer. A request is the header with id `(intent id << 24) | response size`, its body
//! and the end of the stream; the server answers with a fresh message of the asked size and ends the stream. A
//! request whose connection closed or whose stream was reset before the answer is sent again while the intent's
//! deadline allows; an `open_stream` that gives nothing is retried after 100 ms; a failed dial drops the waiting
//! requests (they end undelivered).
//!
//! Invariants: a request is either waiting for a connection, in flight on exactly one stream, or finished; a
//! response is accepted only from the session peer and only as the whole message.

use std::collections::{BTreeMap, BTreeSet};

use pinc_core::SessionId;

use super::body::{self, Verdict};
use super::frame::{Frame, T_REQ, T_RESP, hdr};
use super::host::Host;
use super::stack::{Key, Proto, Role, Stack, Stream, Timers};
use crate::suite::crypto::payload::HEADER_LEN;
use crate::suite::crypto::{MsgId, PayloadKind};

const OPEN_RETRY: u64 = 100_000_000;
const RESET_RETRY: u64 = 200_000_000;
const NOT_PAYLOAD: &str = "body is not payload (stream corrupted or reordered)";

/// A request not yet sent.
#[derive(Debug, Clone, Copy)]
pub(super) struct Waiting {
    pub(super) iid: u32,
    pub(super) msg: MsgId,
    pub(super) len: u64,
    pub(super) resp: u64,
}

#[derive(Debug)]
struct Inflight {
    peer: usize,
    w: Waiting,
}

/// One request/response protocol of a node (volatile state).
#[derive(Debug, Default)]
pub(super) struct ReqResp {
    conns: BTreeMap<usize, SessionId>,
    waiting: BTreeMap<usize, Vec<Waiting>>,
    connecting: BTreeSet<usize>,
    inflight: BTreeMap<Key, Inflight>,
    pub(super) timers: Timers,
}

impl Stack {
    /// Sends a request to `peer` now, or when the connection is up.
    pub(super) fn rr_request(&mut self, now: u64, host: &mut dyn Host, p: Proto, peer: usize, w: Waiting) {
        let rr = &mut self.rr[p.rr()];
        rr.waiting.entry(peer).or_default().push(w);
        if let Some(&session) = rr.conns.get(&peer) {
            self.rr_send(now, host, p, peer, session);
        } else if !rr.connecting.contains(&peer) {
            self.rr_dial(host, p, peer);
        }
    }

    fn rr_dial(&mut self, host: &mut dyn Host, p: Proto, peer: usize) {
        let rr = &mut self.rr[p.rr()];
        rr.connecting.insert(peer);
        if !host.connect(peer, p.alpn()) {
            rr.connecting.remove(&peer);
            rr.waiting.remove(&peer);
        }
    }

    fn rr_send(&mut self, now: u64, host: &mut dyn Host, p: Proto, peer: usize, session: SessionId) {
        let queue = self.rr[p.rr()].waiting.remove(&peer).unwrap_or_default();
        for w in queue {
            let Some(stream) = host.open_stream(session) else {
                let rr = &mut self.rr[p.rr()];
                rr.waiting.entry(peer).or_default().push(w);
                rr.timers.0.insert(now + OPEN_RETRY);
                continue;
            };
            let key = (session, stream);
            self.streams.insert(key, Stream::new(Role::None));
            self.rr[p.rr()].inflight.insert(key, Inflight { peer, w });
            let id = (u64::from(w.iid) << 24) | (w.resp & 0xFF_FFFF);
            let mut f = hdr(T_REQ, w.len as usize, id).to_vec();
            f.extend_from_slice(&body::render(host.registry(), w.msg, w.len));
            self.send(host, key, &f, true);
        }
    }

    pub(super) fn rr_connected(&mut self, now: u64, host: &mut dyn Host, p: Proto, session: SessionId, peer: usize) {
        let rr = &mut self.rr[p.rr()];
        rr.connecting.remove(&peer);
        if rr.conns.get(&peer).is_some_and(|&old| old != session) {
            host.close(session, 0);
            return;
        }
        rr.conns.insert(peer, session);
        self.rr_send(now, host, p, peer, session);
    }

    pub(super) fn rr_connect_failed(&mut self, p: Proto, peer: usize) {
        let rr = &mut self.rr[p.rr()];
        rr.connecting.remove(&peer);
        rr.waiting.remove(&peer);
    }

    /// Requeues a request that lost its stream, if its intent is still within the deadline.
    fn rr_requeue(&mut self, now: u64, p: Proto, inf: &Inflight) -> bool {
        let live = self
            .rec
            .borrow()
            .intents
            .get(&inf.w.iid)
            .and_then(|it| it.deadline)
            .is_some_and(|d| now < d);
        if live {
            self.rr[p.rr()].waiting.entry(inf.peer).or_default().push(inf.w);
        }
        live
    }

    pub(super) fn rr_closed(&mut self, now: u64, host: &mut dyn Host, p: Proto, session: SessionId, peer: usize) {
        let lost: Vec<Key> = self.rr[p.rr()]
            .inflight
            .keys()
            .filter(|k| k.0 == session)
            .copied()
            .collect();
        for k in lost {
            if let Some(inf) = self.rr[p.rr()].inflight.remove(&k) {
                self.rr_requeue(now, p, &inf);
            }
        }
        let rr = &mut self.rr[p.rr()];
        if rr.conns.get(&peer) == Some(&session) {
            rr.conns.remove(&peer);
            if rr.waiting.get(&peer).is_some_and(|q| !q.is_empty()) && !rr.connecting.contains(&peer) {
                self.rr_dial(host, p, peer);
            }
        }
    }

    pub(super) fn rr_stream_end(&mut self, now: u64, key: Key, p: Proto, reset: bool) {
        let Some(inf) = self.rr[p.rr()].inflight.remove(&key) else {
            return;
        };
        if reset && self.rr_requeue(now, p, &inf) {
            self.rr[p.rr()].timers.0.insert(now + RESET_RETRY);
        }
    }

    pub(super) fn rr_timeout(&mut self, now: u64, host: &mut dyn Host) {
        for p in [Proto::DocSync, Proto::Manage] {
            if self.rr[p.rr()].timers.0.first().is_none_or(|&t| t > now) {
                continue;
            }
            self.rr[p.rr()].timers.pop_due(now);
            let ready: Vec<(usize, SessionId)> = {
                let rr = &self.rr[p.rr()];
                rr.waiting
                    .keys()
                    .filter_map(|peer| rr.conns.get(peer).map(|&s| (*peer, s)))
                    .collect()
            };
            for (peer, session) in ready {
                self.rr_send(now, host, p, peer, session);
            }
        }
    }

    pub(super) fn rr_frame(
        &mut self,
        now: u64,
        host: &mut dyn Host,
        key: Key,
        p: Proto,
        f: &Frame,
    ) -> Result<(), String> {
        let Some(peer) = self.sessions.get(&key.0).map(|s| s.peer) else {
            return Ok(());
        };
        let (Some(b), true) = (f.body.as_deref(), matches!(f.ty, T_REQ | T_RESP)) else {
            return Ok(());
        };
        let msg = body::message_id(b).ok_or(NOT_PAYLOAD)?;
        if !self.check_origin(now, host.registry(), p, peer, msg) {
            return Ok(());
        }
        if body::verify(host.registry(), msg, b) != Verdict::Whole {
            return Err(NOT_PAYLOAD.to_owned());
        }
        if f.ty == T_REQ {
            let size = f.id & 0xFF_FFFF;
            let len = size.max(HEADER_LEN as u64);
            let reg = host.registry();
            let resp = reg.new_msg(self.idx, PayloadKind::Msg, len);
            let mut out = hdr(T_RESP, len as usize, f.id >> 24).to_vec();
            out.extend_from_slice(&body::render(reg, resp, len));
            self.send(host, key, &out, true);
        } else if let Some(iid) = self.rr[p.rr()]
            .inflight
            .remove(&key)
            .map(|inf| inf.w.iid)
            .filter(|&iid| u64::from(iid) == f.id)
        {
            self.request_done(now, iid);
        }
        Ok(())
    }
}
