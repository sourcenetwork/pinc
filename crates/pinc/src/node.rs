//! The endpoint of the right capacity, as one type the facade does not carry the capacity in.
//!
//! The endpoint's tables are const-generic, so the facade builds one of a ladder of shapes (see
//! [`CAPACITIES`]). [`AnyEp`] is the enum of those shapes: the core holds an `AnyEp` and is the same type whatever the
//! capacity, and each method is one `match` that forwards to the endpoint method of the same name. The ladder is
//! written once, in [`ladder!`], and everything that depends on it (the enum, the list of capacities and the function
//! that builds the endpoint of the smallest rung that holds `n` sessions) is generated from that one list.
//!
//! [`AnyEp`] implements the connectivity client's `Port` and the node's `Ep`, so the node runs over it unchanged.
//!
//! Invariants: every method forwards to the endpoint method of the same name and adds nothing.

use alloc::boxed::Box;
use core::net::SocketAddr;
use core::ops::Range;

use pinc_connect::client::Port;
use pinc_core::{
    Answer, Command, CommandError, EndpointConfig, Event, IfaceEvent, IfaceId, NodeStats, PeerInfo, Query,
    REACH_BODY_MAX, Reply, Restored, SendState, SessionId, SessionStats, StateError, Taken, TraceRecord, Transmit,
};
use pinc_crypto::{Drbg, NodeId, Software};
use pinc_node::Ep as NodeEp;
use pinc_security::{ConnId, LocalIdentity, PrekeyInfo};
use pinc_transport::stream::StreamId;

use crate::mem::Ep;

#[cfg(feature = "std")]
std::thread_local! {
    /// The boxes of handshake machines the endpoints of this thread share: an endpoint holds one only while a
    /// handshake of its runs.
    static MACHINES: pinc_transport::conn::Machines = pinc_transport::conn::Machines::new();
}

/// The handshake machines an endpoint draws its boxes from: the thread's shared pool under `std`, its own without it,
/// where there is no thread-local state to share through.
// vertexia: per-endpoint handshake machines without std; the thread's shared pool returns when core has a thread_local.
fn machines() -> pinc_transport::conn::Machines {
    #[cfg(feature = "std")]
    {
        MACHINES.with(core::clone::Clone::clone)
    }
    #[cfg(not(feature = "std"))]
    {
        pinc_transport::conn::Machines::new()
    }
}

/// The relays a node can name at once.
pub(crate) const RELAYS: usize = 4;
/// The peers the connectivity layer tracks.
pub(crate) const PEERS: usize = 32;

/// The node the facade runs: the endpoint of the right capacity under the connectivity client, membership and
/// broadcast.
pub(crate) type FacadeNode = pinc_node::Node<AnyEp, Software, (), RELAYS, PEERS>;

/// Call `$m!` with the ladder of `variant capacity` pairs.
macro_rules! ladder {
    ($m:ident) => {
        $m! {
            C1 1, C2 2, C4 4, C8 8, C16 16, C32 32, C64 64, C128 128, C256 256, C512 512, C1024 1024, C2048 2048,
            C4096 4096, C8192 8192, C16384 16_384, C32768 32_768, C65536 65_536
        }
    };
}

macro_rules! define {
    ($($v:ident $k:literal),+) => {
        /// The session capacities an endpoint is built for; `Limits::connections` picks the smallest that holds it.
        pub const CAPACITIES: [usize; [$($k),+].len()] = [$($k),+];

        /// The endpoint of one shape of the ladder.
        pub(crate) enum AnyEp {
            $(
                #[doc = concat!("An endpoint for ", stringify!($k), " sessions.")]
                $v(Box<Ep<'static, 'static, $k, { $k * 10 }>>),
            )+
        }

        impl AnyEp {
            /// The endpoint of the smallest rung that holds `connections` sessions, with ten connection id entries per
            /// session and `pool_chunks` chunks for each; `None` above the ladder. It is not generic, so it is compiled
            /// once, here, and optimised whatever the host's types: no host's build keeps a copy of a slot on the stack.
            #[inline(never)]
            pub(crate) fn new(
                connections: usize,
                now: u64,
                drbg: Drbg,
                identity: LocalIdentity,
                cfg: EndpointConfig,
                pool_chunks: usize,
            ) -> Option<Self> {
                match connections {
                    $(n if n <= $k => Some(Self::$v({
                        let mut ep = Ep::<$k, { $k * 10 }>::new_owned(now, Software, drbg, identity, cfg, pool_chunks);
                        ep.share_machines(&machines());
                        ep
                    })),)+
                    _ => None,
                }
            }
            pub(crate) fn add_iface(&mut self, local: SocketAddr) -> Option<IfaceId> {
                match self { $(Self::$v(e) => e.add_iface(local),)+ }
            }
            pub(crate) fn query(&self, q: Query) -> Answer<'_> {
                match self { $(Self::$v(e) => e.query(q),)+ }
            }
            pub(crate) fn read_datagram(&mut self, session: SessionId, out: &mut [u8]) -> Result<Option<usize>, CommandError> {
                match self { $(Self::$v(e) => e.read_datagram(session, out),)+ }
            }
            pub(crate) fn node_stats(&self) -> NodeStats {
                match self { $(Self::$v(e) => e.node_stats(),)+ }
            }
            pub(crate) fn set_backlog_room(&mut self, room: usize) {
                match self { $(Self::$v(e) => e.set_backlog_room(room),)+ }
            }
            pub(crate) fn session_taken(&mut self, session: SessionId) -> Taken {
                match self { $(Self::$v(e) => e.session_taken(session),)+ }
            }
            pub(crate) fn set_prekey(&mut self, prekey: PrekeyInfo) {
                match self { $(Self::$v(e) => e.set_prekey(prekey),)+ }
            }
            pub(crate) fn export_state(&self, now: u64, out: &mut [u8]) -> Result<usize, StateError> {
                match self { $(Self::$v(e) => e.export_state(now, out),)+ }
            }
            pub(crate) fn restore_state(&mut self, now: u64, bytes: &[u8]) -> Result<Restored, StateError> {
                match self { $(Self::$v(e) => e.restore_state(now, bytes),)+ }
            }
            pub(crate) fn iface_event(&mut self, now: u64, id: IfaceId, ev: IfaceEvent) {
                match self { $(Self::$v(e) => e.iface_event(now, id, ev),)+ }
            }
        }

        impl Port for AnyEp {
            type Src = crate::Body;
            fn command(&mut self, now: u64, cmd: Command<'_, crate::Body>) -> Result<Reply, CommandError> {
                match self { $(Self::$v(e) => Port::command(&mut **e, now, cmd),)+ }
            }
            fn stats(&self, session: SessionId) -> Option<SessionStats> {
                match self { $(Self::$v(e) => Port::stats(&**e, session),)+ }
            }
            fn node(&self) -> Option<NodeStats> {
                match self { $(Self::$v(e) => Port::node(&**e),)+ }
            }
            fn peer(&self, node: &NodeId) -> Option<PeerInfo> {
                match self { $(Self::$v(e) => Port::peer(&**e, node),)+ }
            }
            fn reach_body(&self, session: SessionId, out: &mut [u8; REACH_BODY_MAX]) -> usize {
                match self { $(Self::$v(e) => Port::reach_body(&**e, session, out),)+ }
            }
            fn by_conn_id(&self, cid: &ConnId) -> Option<SessionStats> {
                match self { $(Self::$v(e) => Port::by_conn_id(&**e, cid),)+ }
            }
        }

        impl NodeEp for AnyEp {
            fn handle_datagram(&mut self, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]) {
                match self { $(Self::$v(e) => NodeEp::handle_datagram(&mut **e, now, local, remote, buf),)+ }
            }
            fn poll_transmit(&mut self, now: u64, out: &mut [u8]) -> Option<Transmit> {
                match self { $(Self::$v(e) => NodeEp::poll_transmit(&mut **e, now, out),)+ }
            }
            fn transmit_waiting(&self) -> bool {
                match self { $(Self::$v(e) => NodeEp::transmit_waiting(&**e),)+ }
            }
            fn poll_event(&mut self) -> Option<Event> {
                match self { $(Self::$v(e) => NodeEp::poll_event(&mut **e),)+ }
            }
            fn events_waiting(&self) -> bool {
                match self { $(Self::$v(e) => NodeEp::events_waiting(&**e),)+ }
            }
            fn poll_timeout(&self) -> Option<u64> {
                match self { $(Self::$v(e) => NodeEp::poll_timeout(&**e),)+ }
            }
            fn handle_timeout(&mut self, now: u64) {
                match self { $(Self::$v(e) => NodeEp::handle_timeout(&mut **e, now),)+ }
            }
            fn register_alpn(&mut self, alpn: &[u8]) -> bool {
                match self { $(Self::$v(e) => NodeEp::register_alpn(&mut **e, alpn),)+ }
            }
            fn read_chunk(&self, session: SessionId, stream: StreamId) -> Option<&[u8]> {
                match self { $(Self::$v(e) => NodeEp::read_chunk(&**e, session, stream),)+ }
            }
            fn read_at(&self, session: SessionId, stream: StreamId, offset: u64) -> Option<&[u8]> {
                match self { $(Self::$v(e) => NodeEp::read_at(&**e, session, stream, offset),)+ }
            }
            fn stored_after(&self, session: SessionId, stream: StreamId, from: u64) -> Option<Range<u64>> {
                match self { $(Self::$v(e) => NodeEp::stored_after(&**e, session, stream, from),)+ }
            }
            fn send_state(&self, session: SessionId, stream: StreamId) -> Option<SendState> {
                match self { $(Self::$v(e) => NodeEp::send_state(&**e, session, stream),)+ }
            }
            fn in_flight(&self, session: SessionId) -> Option<u64> {
                match self { $(Self::$v(e) => NodeEp::in_flight(&**e, session),)+ }
            }
            fn read_extension(&mut self, out: &mut [u8]) -> Result<Option<(SessionId, u64, usize)>, CommandError> {
                match self { $(Self::$v(e) => NodeEp::read_extension(&mut **e, out),)+ }
            }
            fn session_at(&self, n: usize) -> Option<SessionStats> {
                match self { $(Self::$v(e) => NodeEp::session_at(&**e, n),)+ }
            }
            fn session_from(&self, remote: &SocketAddr, keep: &dyn Fn(SessionId) -> bool) -> Option<SessionId> {
                match self { $(Self::$v(e) => NodeEp::session_from(&**e, remote, keep),)+ }
            }
            fn poll_trace(&mut self) -> Option<TraceRecord> {
                match self { $(Self::$v(e) => NodeEp::poll_trace(&mut **e),)+ }
            }
            fn add_iface(&mut self, local: SocketAddr) -> Option<IfaceId> {
                match self { $(Self::$v(e) => NodeEp::add_iface(&mut **e, local),)+ }
            }
            fn iface_event(&mut self, now: u64, id: IfaceId, ev: IfaceEvent) {
                match self { $(Self::$v(e) => NodeEp::iface_event(&mut **e, now, id, ev),)+ }
            }
        }
    };
}
ladder!(define);
