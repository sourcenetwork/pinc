//! Streams the peer opened and streams the application dropped: the accept queues, the stopped streams a session
//! remembers for their writers, and the list of streams whose bytes are thrown away until they end.

use pinc_core::{Answer, Command, Query, SessionId, Value};
use pinc_keystore::KeyStore;
use pinc_transport::stream::{RecvStatus, StreamId, is_uni};

use super::{Admit, BUSY, Core, DISCARDED, SKey, TRACKED};
use crate::error::Error;

impl<S: KeyStore, A: Admit> Core<S, A> {
    pub(super) fn stream_opened(&mut self, now: u64, session: SessionId, id: StreamId) {
        let uni = is_uni(id);
        let cap = self.limits.accept_streams;
        let Some(s) = self.sessions.get_mut(&session) else {
            return;
        };
        let q = if uni { &mut s.accept_uni } else { &mut s.accept_bi };
        if q.len() < cap {
            q.push_back(id);
            self.wake_s(session, if uni { SKey::AcceptUni } else { SKey::AcceptBi });
            return;
        }
        // Refuse: tell the peer to stop, and drop what it sends.
        debug_assert!(s.discard.len() < DISCARDED, "a dropped stream without a stream slot");
        if s.discard.len() < DISCARDED {
            s.discard.push(id);
        }
        if !uni {
            let _ = self.cmd(now, || Command::Reset {
                session,
                stream: id,
                error: BUSY,
            });
        }
        let _ = self.cmd(now, || Command::StopSending {
            session,
            stream: id,
            error: BUSY,
        });
        self.discard_if_dropped(now, session, id);
    }

    pub(super) fn send_failed(&mut self, session: SessionId, id: StreamId, err: Error) {
        if let Some(s) = self.sessions.get_mut(&session) {
            s.send_fail.retain(|(i, _)| *i != id);
            if s.send_fail.len() >= TRACKED {
                s.send_fail.remove(0);
            }
            s.send_fail.push((id, err));
        }
    }

    pub(super) fn send_failure(&self, session: SessionId, id: StreamId) -> Option<Error> {
        let s = self.sessions.get(&session)?;
        s.send_fail.iter().find(|(i, _)| *i == id).map(|(_, e)| *e)
    }

    /// Throw away what the endpoint holds on a stream the application dropped, until the stream ends.
    pub(super) fn discard_if_dropped(&mut self, now: u64, session: SessionId, id: StreamId) {
        if !self.sessions.get(&session).is_some_and(|s| s.discard.contains(&id)) {
            return;
        }
        loop {
            let n = match self.node.endpoint().query(Query::Read { session, stream: id }) {
                Answer::Chunk(c) => c.len(),
                _ => 0,
            };
            let status = match self.cmd(now, || Command::Consume { session, stream: id, n }) {
                Ok(Value::Recv(st)) => st,
                Ok(_) => RecvStatus::Open,
                Err(_) => RecvStatus::Finished,
            };
            if status != RecvStatus::Open {
                if let Some(s) = self.sessions.get_mut(&session) {
                    s.discard.retain(|i| *i != id);
                }
                return;
            }
            if n == 0 {
                return;
            }
        }
    }
}
