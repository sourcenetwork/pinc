//! ECHO: connect, open a stream, one round trip, close.
//!
//! One dial per intent. On the connection the client records `connected`, opens a stream, writes the header and a
//! 32 byte body with the end of the stream (recording `written`); the server records `served` and sends the same
//! body back with the end of the stream; the client records the delivery and closes the connection.
//!
//! Invariants: the dials of one peer are matched to the intents in the order they were made; a connection with no
//! intent waiting for it is closed.

use vinc_core::SessionId;

use super::body;
use super::frame::{Frame, T_ECHO, hdr};
use super::host::Host;
use super::stack::{ALPN_ECHO, Key, Role, Stack, Stream};
use crate::suite::crypto::PayloadKind;

/// The body of an echo.
const ECHO_LEN: u64 = 32;

impl Stack {
    /// Starts an echo of intent `iid` to `peer`.
    pub(super) fn echo_start(&mut self, host: &mut dyn Host, peer: usize, iid: u32) {
        self.echo_pending.entry(peer).or_default().push_back(iid);
        if !host.connect(peer, ALPN_ECHO) {
            self.echo_connect_failed(peer);
        }
    }

    pub(super) fn echo_connect_failed(&mut self, peer: usize) {
        if let Some(q) = self.echo_pending.get_mut(&peer) {
            q.pop_front();
            if q.is_empty() {
                self.echo_pending.remove(&peer);
            }
        }
    }

    pub(super) fn echo_connected(&mut self, now: u64, host: &mut dyn Host, session: SessionId, peer: usize) {
        let iid = self
            .echo_pending
            .get_mut(&peer)
            .and_then(std::collections::VecDeque::pop_front);
        let Some(iid) = iid else {
            host.close(session, 0);
            return;
        };
        self.rec.borrow_mut().echo_connected(iid, now);
        let Some(stream) = host.open_stream(session) else {
            host.close(session, 0);
            return;
        };
        let key = (session, stream);
        self.streams.insert(key, Stream::new(Role::EchoClient(iid)));
        let reg = host.registry();
        let msg = reg.new_msg(self.idx, PayloadKind::Msg, ECHO_LEN);
        let mut f = hdr(T_ECHO, ECHO_LEN as usize, u64::from(iid)).to_vec();
        f.extend_from_slice(&body::render(reg, msg, ECHO_LEN));
        self.rec.borrow_mut().echo_written(iid, now);
        self.send(host, key, &f, true);
    }

    pub(super) fn echo_frame(&mut self, now: u64, host: &mut dyn Host, key: Key, f: &Frame) {
        let role = self.streams.get(&key).map_or(Role::None, |s| s.role);
        if let Role::EchoClient(iid) = role {
            if let Some(st) = self.streams.get_mut(&key) {
                st.role = Role::None;
            }
            if f.ty == T_ECHO && u64::from(iid) == f.id {
                self.echo_done(now, iid);
            }
            host.close(key.0, 0);
        } else if let (T_ECHO, Some(b)) = (f.ty, f.body.as_deref()) {
            self.echo_served(now, f.id);
            let mut out = hdr(T_ECHO, b.len(), f.id).to_vec();
            out.extend_from_slice(b);
            self.send(host, key, &out, true);
        }
    }
}
