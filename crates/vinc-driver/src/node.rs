//! The endpoint of the right capacity, as one type the engine does not carry the capacity in.
//!
//! The endpoint's tables are const-generic, so the driver builds one of a ladder of shapes (see
//! [`CAPACITIES`]). [`AnyEp`] is the enum of those shapes: [`Engine`](crate::Engine) holds an `AnyEp` and is the same
//! type whatever the capacity, and each method is one `match` that forwards to the endpoint method of the same name.
//! The ladder is written once, in [`ladder!`], and everything that depends on it (the enum, the list of capacities and
//! the function that builds an engine for the smallest one that holds `n` sessions) is generated from that one list.
//!
//! Invariants: every method forwards to the endpoint method of the same name and adds nothing.

use std::net::SocketAddr;

use vinc_core::{
    Answer, Command, CommandError, Event, IfaceEvent, IfaceId, NodeStats, Query, Reply, SessionId, Transmit,
};
use vinc_security::PrekeyInfo;
use vinc_transport::stream::NoSource;

use crate::mem::Ep;

/// Call `$m!` with the ladder of `variant capacity` pairs.
macro_rules! ladder {
    ($m:ident) => {
        $m! {
            C1 1, C2 2, C4 4, C8 8, C16 16, C32 32, C64 64, C128 128, C256 256, C512 512, C1024 1024, C2048 2048,
            C4096 4096, C8192 8192, C16384 16_384, C32768 32_768, C65536 65_536
        }
    };
}
pub(crate) use ladder;

macro_rules! define {
    ($($v:ident $k:literal),+) => {
        /// The session capacities an engine is built for; `Limits::connections` picks the smallest that holds it.
        pub const CAPACITIES: [usize; [$($k),+].len()] = [$($k),+];

        /// The endpoint of one shape of the ladder.
        pub(crate) enum AnyEp<'s, 'a> {
            $(
                #[doc = concat!("An endpoint for ", stringify!($k), " sessions.")]
                $v(Box<Ep<'s, 'a, $k, { $k * 10 }>>),
            )+
        }

        impl AnyEp<'_, '_> {
            pub(crate) fn handle_datagram(&mut self, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]) {
                match self { $(Self::$v(e) => e.handle_datagram(now, local, remote, buf)),+ }
            }
            pub(crate) fn handle_timeout(&mut self, now: u64) {
                match self { $(Self::$v(e) => e.handle_timeout(now)),+ }
            }
            pub(crate) fn poll_transmit(&mut self, now: u64, out: &mut [u8]) -> Option<Transmit> {
                match self { $(Self::$v(e) => e.poll_transmit(now, out)),+ }
            }
            pub(crate) fn poll_timeout(&self) -> Option<u64> {
                match self { $(Self::$v(e) => e.poll_timeout()),+ }
            }
            pub(crate) fn poll_event(&mut self) -> Option<Event> {
                match self { $(Self::$v(e) => e.poll_event()),+ }
            }
            pub(crate) fn command(&mut self, now: u64, c: Command<'_, NoSource>) -> Result<Reply, CommandError> {
                match self { $(Self::$v(e) => e.command(now, c)),+ }
            }
            pub(crate) fn query(&self, q: Query) -> Answer<'_> {
                match self { $(Self::$v(e) => e.query(q)),+ }
            }
            pub(crate) fn read_datagram(&mut self, session: SessionId, out: &mut [u8]) -> Result<Option<usize>, CommandError> {
                match self { $(Self::$v(e) => e.read_datagram(session, out)),+ }
            }
            pub(crate) fn node_stats(&self) -> NodeStats {
                match self { $(Self::$v(e) => e.node_stats()),+ }
            }
            pub(crate) fn set_prekey(&mut self, prekey: PrekeyInfo) {
                match self { $(Self::$v(e) => e.set_prekey(prekey)),+ }
            }
            pub(crate) fn register_alpn(&mut self, alpn: &[u8]) -> bool {
                match self { $(Self::$v(e) => e.register_alpn(alpn)),+ }
            }
            pub(crate) fn iface_event(&mut self, now: u64, id: IfaceId, ev: IfaceEvent) {
                match self { $(Self::$v(e) => e.iface_event(now, id, ev)),+ }
            }
        }
    };
}
ladder!(define);
