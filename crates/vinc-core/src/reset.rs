//! Stateless reset: a node that restarted tells a sender, in one datagram, that it holds no state for the connection
//! id the sender used.
//!
//! A node with a reset key ([`EndpointConfig::reset_key`](crate::EndpointConfig::reset_key)) gives its peer, on each
//! path of each session, the token of the connection id the peer sends to there: `token = keyed_hash(reset_key, id ||
//! remote address)[..16]`, in one `RESET_TOKEN` extension frame (`id token`, 20 bytes), sent once per path and id after
//! the first authenticated packet on it. The key survives a restart (the host derives it from the node identity), so a
//! node that restarted computes the same token for a packet on an id it no longer holds, and answers with a reset: 21
//! bytes, a first byte `0b011x_xxxx` that no packet has (bit 5 set where a short header has it clear), the id, then the
//! token. The sender closes the session that holds that id and token, and the sessions opened over it.
//!
//! Invariants:
//! - a reset answers only a short-header datagram longer than a reset, and never a reset: a reset is smaller than what
//!   caused it, so it never amplifies, and two restarted nodes cannot answer each other forever; at most one reset
//!   waits to be sent and it passes the amplification ledger like every datagram;
//! - a reset closes a session only if it carries the token that session was given for the id it names, and only if the
//!   session heard nothing from its peer for a smoothed round trip, so a stray packet on an id the peer forgot cannot
//!   end a session that is plainly alive;
//! - without a reset key no token is given and no reset is sent; resets are still accepted.

use core::net::{IpAddr, SocketAddr};

use vinc_crypto::{ct_eq, extract};
use vinc_security::ConnId;
use vinc_transport::conn::PathId;
use vinc_transport::frame::ext;
use vinc_transport::packet::short_dcid;

use crate::endpoint::{CID_LEN, ep_impl};

/// The bytes of a token.
pub(crate) const TOKEN_LEN: usize = 16;
/// The bytes of a reset: the first byte, the id, the token.
pub(crate) const RESET_LEN: usize = 1 + CID_LEN + TOKEN_LEN;
/// The bits of a reset's first byte that mark it; the low five are random.
const RESET_FORM: u8 = 0b0110_0000;
const FORM_MASK: u8 = 0b1110_0000;
/// Tokens a session keeps, one per path id it sends to; the oldest is replaced.
pub(crate) const TOKENS_HELD: usize = 4;

/// The token of connection id `cid` used by a peer at `remote`.
pub(crate) fn token(key: &[u8; 32], cid: &ConnId, remote: &SocketAddr) -> [u8; TOKEN_LEN] {
    let ip = match remote.ip() {
        IpAddr::V4(v) => v.to_ipv6_mapped().octets(),
        IpAddr::V6(v) => v.octets(),
    };
    let mut input = [0u8; CID_LEN + 16 + 2];
    let (c, rest) = input.split_at_mut(CID_LEN);
    let (a, p) = rest.split_at_mut(16);
    c.copy_from_slice(cid.as_bytes().get(..CID_LEN).unwrap_or(&[0; CID_LEN]));
    a.copy_from_slice(&ip);
    p.copy_from_slice(&remote.port().to_be_bytes());
    let h = extract(key, &input);
    let mut t = [0u8; TOKEN_LEN];
    t.copy_from_slice(h.get(..TOKEN_LEN).unwrap_or(&[0; TOKEN_LEN]));
    t
}

/// Whether `buf` has the form of a reset.
pub(crate) fn is_reset(buf: &[u8]) -> bool {
    buf.len() == RESET_LEN && buf.first().is_some_and(|b| b & FORM_MASK == RESET_FORM)
}

/// The id and token a reset carries.
fn parse(buf: &[u8]) -> Option<(ConnId, [u8; TOKEN_LEN])> {
    let cid = ConnId::new(buf.get(1..=CID_LEN)?)?;
    let mut t = [0u8; TOKEN_LEN];
    t.copy_from_slice(buf.get(1 + CID_LEN..RESET_LEN)?);
    Some((cid, t))
}

/// A reset waiting to be sent.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ResetOut {
    pub(crate) local: SocketAddr,
    pub(crate) remote: SocketAddr,
    pub(crate) bytes: [u8; RESET_LEN],
}

ep_impl! {
    /// A short-header datagram for an id no session holds: answer with a reset, if this node has a reset key, the
    /// datagram is longer than a reset and no reset is waiting already.
    pub(crate) fn answer_unknown(&mut self, local: SocketAddr, remote: SocketAddr, buf: &[u8]) {
        let Some(key) = self.cfg.reset_key else { return };
        if buf.len() <= RESET_LEN || self.reset_out.is_some() {
            return;
        }
        let Ok(cid) = short_dcid(buf, CID_LEN) else { return };
        let mut first = [0u8; 1];
        if self.drbg.fill(&mut first).is_err() {
            return;
        }
        let mut bytes = [0u8; RESET_LEN];
        let (head, rest) = bytes.split_at_mut(1);
        let (c, t) = rest.split_at_mut(CID_LEN);
        if let Some(b) = head.first_mut() {
            *b = RESET_FORM | (first.first().copied().unwrap_or(0) & !FORM_MASK);
        }
        c.copy_from_slice(cid.as_bytes().get(..CID_LEN).unwrap_or(&[0; CID_LEN]));
        t.copy_from_slice(&token(&key, &cid, &remote));
        self.reset_out = Some(ResetOut { local, remote, bytes });
    }

    /// Session `i` authenticated a short-header packet to `cid` from `remote` on `path`: give the peer the token of
    /// that id there, once per path and id.
    pub(crate) fn give_token(&mut self, i: usize, path: PathId, cid: ConnId, remote: SocketAddr) {
        let Some(key) = self.cfg.reset_key else { return };
        let Some(slot) = self.slots.get_mut(i) else { return };
        let Some(stamp) = slot.m.stamp(path) else { return };
        if stamp.token_for == Some(cid) {
            return;
        }
        stamp.token_for = Some(cid);
        let mut body = [0u8; CID_LEN + TOKEN_LEN];
        let (c, t) = body.split_at_mut(CID_LEN);
        c.copy_from_slice(cid.as_bytes().get(..CID_LEN).unwrap_or(&[0; CID_LEN]));
        t.copy_from_slice(&token(&key, &cid, &remote));
        if let Some(conn) = slot.conn.as_mut() {
            slot.m.ctrl_pending = true;
            // A full extension queue loses this token; the next new path or id gives another.
            let _ = conn.send_extension(ext::RESET_TOKEN, &body);
        }
    }

    /// A `RESET_TOKEN` frame arrived in session `i`: keep it, in place of the oldest.
    pub(crate) fn take_token(&mut self, i: usize, body: &[u8]) {
        let (Some(cid), Some(tok)) = (
            body.get(..CID_LEN).and_then(ConnId::new),
            body.get(CID_LEN..).filter(|t| t.len() == TOKEN_LEN),
        ) else {
            return;
        };
        let Some(slot) = self.slots.get_mut(i) else { return };
        let mut t = [0u8; TOKEN_LEN];
        t.copy_from_slice(tok);
        let m = &mut slot.m;
        let at = m.tokens.iter().position(|e| e.is_some_and(|(c, _)| c == cid)).unwrap_or(m.token_next);
        if let Some(e) = m.tokens.get_mut(at) {
            *e = Some((cid, t));
        }
        if at == m.token_next {
            m.token_next = (m.token_next + 1) % TOKENS_HELD;
        }
    }

    /// A datagram with the form of a reset arrived: close the session that holds its id and token, if it has been
    /// silent for a round trip, and every session opened over it.
    // ponytail: a scan of the slots, only for a datagram with the reset form; an index by token if resets get busy.
    pub(crate) fn on_reset(&mut self, now: u64, buf: &[u8]) {
        let Some((cid, tok)) = parse(buf) else { return };
        let hit = (0..self.slots.len()).find(|&i| {
            self.slots.get(i).is_some_and(|s| {
                s.m.in_use
                    && s.m.tokens.iter().flatten().any(|(c, t)| *c == cid && ct_eq(t, &tok))
                    && s.conn.as_ref().is_some_and(|c| now.saturating_sub(s.m.last_rx) >= c.rtt_estimate().smoothed())
            })
        });
        let Some(i) = hit else {
            self.counters.dropped_in += 1;
            return;
        };
        let parent = self.session_id(i);
        for c in 0..self.slots.len() {
            if self.slots.get(c).is_some_and(|s| s.m.in_use && s.m.parent == Some(parent)) {
                self.end_reset(c, now);
            }
        }
        self.end_reset(i, now);
    }

    fn end_reset(&mut self, i: usize, now: u64) {
        if let Some(conn) = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()) {
            conn.peer_reset();
        }
        self.settle(i, now);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> ConnId {
        ConnId::new(&[b; CID_LEN]).unwrap_or_else(|| unreachable!())
    }

    #[test]
    fn a_token_depends_on_the_key_the_id_and_the_address() {
        let a: SocketAddr = "10.0.0.1:4000".parse().unwrap_or_else(|_| unreachable!());
        let b: SocketAddr = "10.0.0.1:4001".parse().unwrap_or_else(|_| unreachable!());
        let t = token(&[1; 32], &cid(7), &a);
        assert_eq!(
            t,
            token(&[1; 32], &cid(7), &a),
            "the same inputs after a restart give the same token"
        );
        assert_ne!(t, token(&[2; 32], &cid(7), &a));
        assert_ne!(t, token(&[1; 32], &cid(8), &a));
        assert_ne!(t, token(&[1; 32], &cid(7), &b));
    }

    #[test]
    fn the_reset_form_is_no_packet_form() {
        let mut r = [RESET_FORM | 0b1_1111; RESET_LEN];
        assert!(is_reset(&r));
        assert!(short_dcid(&r, CID_LEN).is_err(), "a reset is not a short header");
        if let Some(b) = r.first_mut() {
            *b = 0b0100_0000;
        }
        assert!(!is_reset(&r), "a short header is not a reset");
        assert!(!is_reset(&[RESET_FORM; RESET_LEN + 1]), "a reset has one length");
    }
}
