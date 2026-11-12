//! The hub's relay duties that belong to the node, so a host that runs a relay for its members does not write them.
//!
//! The relay itself (`vinc-connect`) holds the carriers of the members; the host moves the bytes of the carrier
//! streams. What it must also do is tie the relay to the node's view of its members: a carrier that opens or closes
//! is evidence for membership ([`Node::relay_trace`]), a datagram that asks the relay for something is told from a
//! session packet ([`is_relay_request`]), a member's session packet heard from an address proves the member is there
//! ([`Node::member_at`]), and a member whose session ended or woke is announced ([`Node::poll_member`]).
//!
//! Invariants: nothing here reads a clock or moves bytes; a notice is queued once per event and the queue is bounded
//! (the oldest is dropped when it is full, and the relay forgets state it can relearn from the next packet).

use core::net::SocketAddr;

use vinc_connect::relay::Trace;
use vinc_connect::relay::datagram::Datagram;
use vinc_core::{Command, Event, SessionId, is_relay_addr};
use vinc_crypto::NodeId;

use crate::apps::{Apps, ServeSource};
use crate::config::{Nanos, Store};
use crate::ep::Ep;
use crate::node::Node;

/// What happened to a member of this hub that its relay should know.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemberNotice {
    /// A session of the member ended: the relay forgets the address it learned for the member.
    Gone(NodeId),
    /// The member woke from a sleep: the relay hands it what waited for it.
    Awake(NodeId),
}

/// Whether a datagram a hub received asks its relay for something (a request, a registration, a lookup) and not a
/// session packet or an answer to one of the node's own requests. A session packet starts at 0x40 or above.
pub fn is_relay_request(data: &[u8]) -> bool {
    data.first().is_some_and(|b| *b < 0x40)
        && !matches!(
            Datagram::decode(data),
            Ok(Datagram::Qadr { .. } | Datagram::DnsReply { .. } | Datagram::Spl { .. })
        )
}

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: vinc_crypto::Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: ServeSource<A::Values>,
{
    /// A decision of the hub's relay: the node acts on the ones that concern its members. A carrier that opened or
    /// closed is membership evidence (a sleep notice before a close means a suspension, not a failure), and a carrier
    /// keepalive counts as traffic of the member's hub session. Any other decision is none of the node's business.
    pub fn relay_trace(&mut self, now: Nanos, t: &Trace) {
        match t {
            Trace::CarrierOpened { node, .. } => self.member_carrier_opened(now, &node.bytes),
            Trace::CarrierClosed { node, asleep } => {
                self.member_carrier_closed(now, &node.bytes, asleep.then_some(now));
            }
            Trace::Pulse { node } => {
                self.begin(now);
                let session: Option<SessionId> = self.io.links.get(&node.bytes).and_then(|l| l.conn);
                if let Some(session) = session {
                    // A refused pulse means the session is gone, which the node learns from its own events.
                    let _ = self.io.cmd(Command::Pulse { session, sent: false });
                    let _ = self.io.cmd(Command::Pulse { session, sent: true });
                    self.settle(now);
                }
            }
            _ => {}
        }
    }

    /// The member whose hub session has a validated direct path from `src`, if any: who a session packet from `src`
    /// proves present.
    // vertexia: a linear walk of the hub's member sessions per call; an index by address when a hub carries many.
    pub fn member_at(&self, src: &SocketAddr) -> Option<NodeId> {
        if is_relay_addr(src) {
            return None;
        }
        self.io.sess.iter().filter(|(_, s)| s.incoming).find_map(|(sid, s)| {
            let st = self.io.ep.stats(*sid)?;
            (st.path_validated && st.route.map(|(_, r)| r) == Some(*src)).then(|| self.io.full_id(&s.peer))
        })
    }

    /// The direct address of `member`'s hub session, if it has a validated one: where the relay sends a datagram to
    /// the member.
    pub fn member_addr(&self, member: &NodeId) -> Option<SocketAddr> {
        self.member_route(member).map(|(_, remote)| remote)
    }

    /// The route of `member`'s hub session, `(local, remote)`, if it has a validated direct one: the address a datagram
    /// to the member leaves from and the address it goes to. A host with several addresses sends from the one the
    /// session uses, since a datagram from another family or interface does not reach the member. Any session of the
    /// member counts, as in [`Node::member_at`], the one heard last, so what the relay believes about the member's
    /// UDP session and where the datagram goes come from the same sessions.
    pub fn member_route(&self, member: &NodeId) -> Option<(SocketAddr, SocketAddr)> {
        self.io
            .sess
            .iter()
            .filter(|(_, s)| s.incoming && s.peer == member.bytes)
            .filter_map(|(sid, _)| {
                let st = self.io.ep.stats(*sid)?;
                let route = st.route.filter(|(_, r)| st.path_validated && !is_relay_addr(r))?;
                Some((st.heard, route))
            })
            .max_by_key(|(heard, _)| *heard)
            .map(|(_, route)| route)
    }

    /// Events that came out of commands the host's relay ran straight on the endpoint (it lends the endpoint to the
    /// relay, which answers for its members' sessions): they join the node's own loop, which then runs, so the node
    /// sees them as it sees the ones it polls itself.
    pub fn relay_events(&mut self, now: Nanos, events: &[Event]) {
        self.begin(now);
        self.io.evq.extend(events.iter().copied());
        self.settle(now);
    }

    /// The next thing the hub's relay should learn about a member, oldest first.
    pub fn poll_member(&mut self) -> Option<MemberNotice> {
        self.io.members.pop_front()
    }
}
