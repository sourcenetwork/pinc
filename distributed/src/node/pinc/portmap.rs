//! The node program's port mapping and its reach test.
//!
//! A node of a site whose router runs a port-mapping service asks it for a mapping of its socket, as the facade does
//! when `Builder::port_mapping` is on: the router is the `.1` of the node's LAN, and leases are [`LEASE_S`] seconds,
//! miniupnpd's shortest, so a run sees renewals. Every other node runs as the facade builds one by default, with no
//! port mapping. The client's HTTP requests (for the IGD) go over a TCP stream of the runtime layer, one at a time, with ids
//! from [`HTTP_BASE`], apart from the carriers' and the accepted streams'.
//!
//! The reach test dials a peer by its node id alone (the dialer finds its addresses in its record, through the hub)
//! on a protocol of its own, [`REACH_ALPN`], and reads the session's active path: a relay path has a synthetic address
//! (`relay_parts`), a direct one the peer's.
//!
//! Invariants: at most one HTTP exchange runs; an answer is kept up to `pinc_portmap::MAX_RESPONSE` bytes; a stream
//! that failed, or closed before it opened, is an exchange with no answer.

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use pinc_core::{Answer, Query, Role, SessionId, relay_parts};
use pinc_crypto::NodeId;
use serde_json::{Value, json};

use super::core::{Core, Op, StreamEv, StreamId};

/// The lease asked for, in seconds.
pub const LEASE_S: u32 = 120;
/// The first id of the HTTP leg's streams.
pub const HTTP_BASE: StreamId = 1 << 48;
/// The protocol the reach test dials and every node accepts.
pub const REACH_ALPN: &[u8] = b"vd/reach";

/// The HTTP exchange in flight.
#[derive(Debug)]
pub struct HttpLeg {
    stream: StreamId,
    req: Vec<u8>,
    answer: Vec<u8>,
    opened: bool,
}

/// What the reach test sees of a session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PathSeen {
    /// The session is established.
    pub established: bool,
    /// The remote address of its active path.
    pub remote: Option<SocketAddr>,
}

impl PathSeen {
    /// Whether the active path goes through a relay.
    pub fn relayed(&self) -> bool {
        self.remote.is_some_and(|r| relay_parts(&r).is_some())
    }

    /// The path as the results show it.
    pub fn json(&self) -> Value {
        json!({
            "remote": self.remote.map(|r| r.to_string()),
            "relayed": self.relayed(),
        })
    }
}

/// The router of the LAN `ip` is on: its `.1`.
pub fn gateway_of(ip: IpAddr) -> Option<IpAddr> {
    match ip {
        IpAddr::V4(v4) => {
            let [a, b, c, _] = v4.octets();
            Some(IpAddr::V4(Ipv4Addr::new(a, b, c, 1)))
        }
        IpAddr::V6(_) => None,
    }
}

impl<const K: usize, const D: usize> Core<K, D> {
    /// Ask the site's router for a mapping of the node's socket.
    pub(super) fn start_port_mapping(&mut self, now: u64) {
        let gateway = gateway_of(self.addr.ip());
        self.node.start_port_mapping(now, gateway, self.addr, LEASE_S);
    }

    /// Start the next HTTP exchange the port-mapping client asks for.
    pub(super) fn http_step(&mut self) -> bool {
        // The client gave the exchange up (its deadline passed): drop it, so the next request is polled.
        if self.http.is_some()
            && !self.node.http_awaited()
            && let Some(leg) = self.http.take()
        {
            self.ops.push_back(Op::Close { stream: leg.stream });
        }
        if self.http.is_some() {
            return false;
        }
        let mut buf = [0u8; pinc_portmap::upnp::MAX_REQUEST];
        let Some((to, n)) = self.node.poll_http(&mut buf) else {
            return false;
        };
        let stream = HTTP_BASE + self.http_count;
        self.http_count += 1;
        *self.counters.entry("portmap_http").or_insert(0) += 1;
        self.http = Some(HttpLeg {
            stream,
            req: buf.get(..n).unwrap_or_default().to_vec(),
            answer: Vec::new(),
            opened: false,
        });
        self.ops.push_back(Op::Connect { stream, to });
        true
    }

    /// A stream event of the HTTP leg: handled, and true; any other stream's: false.
    pub(super) fn http_event(&mut self, now: u64, ev: &StreamEv) -> bool {
        let Some(leg) = self.http.as_mut() else {
            return false;
        };
        match ev {
            StreamEv::Opened(s) if *s == leg.stream => {
                leg.opened = true;
                let data = std::mem::take(&mut leg.req);
                self.ops.push_back(Op::Write { stream: *s, data });
            }
            StreamEv::Data(s, d) if *s == leg.stream => {
                let room = pinc_portmap::MAX_RESPONSE.saturating_sub(leg.answer.len());
                leg.answer
                    .extend_from_slice(d.get(..d.len().min(room)).unwrap_or_default());
            }
            StreamEv::Closed(s) | StreamEv::Failed(s) if *s == leg.stream => {
                let stream = *s;
                let answer = self.http.take().and_then(|l| l.opened.then_some(l.answer));
                self.node.handle_http(now, answer.as_deref());
                self.ops.push_back(Op::Close { stream });
            }
            _ => return false,
        }
        true
    }

    /// The mapping held and the class the node publishes.
    pub fn portmap_report(&self) -> Value {
        json!({
            "mapped": self.node.port_mapping().map(|(a, p)| json!({ "addr": a.to_string(), "proto": format!("{p:?}") })),
            "class": self.node.connectivity().class().map(|c| format!("{c:?}")),
        })
    }

    /// Dial `peer` by its node id alone on the reach protocol.
    ///
    /// # Errors
    /// The node refused the dial.
    pub fn reach_dial(&mut self, now: u64, peer: NodeId) -> Result<SessionId, String> {
        let r = self
            .node
            .dial(now, peer, REACH_ALPN, Role::Other, &[])
            .map_err(|e| format!("the dial was refused: {e:?}"));
        self.pump(now);
        r
    }

    /// What the reach test sees of `session`, or none once it is gone.
    pub fn reach_path(&self, session: SessionId) -> Option<PathSeen> {
        match self.node.endpoint().query(Query::Stats(session)) {
            Answer::Stats(s) => Some(PathSeen {
                established: s.established,
                remote: s.route.map(|(_, r)| r),
            }),
            _ => None,
        }
    }
}
