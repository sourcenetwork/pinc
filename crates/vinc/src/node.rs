//! The endpoint of the right capacity, as one type the facade does not carry the capacity in.
//!
//! The endpoint's tables are const-generic, so the facade builds one of a ladder of shapes (see
//! [`CAPACITIES`]). [`AnyEp`] is the enum of those shapes: the core holds an `AnyEp` and is the same type whatever the
//! capacity, and each method is one `match` that forwards to the endpoint method of the same name. The ladder is
//! written once, in [`ladder!`], and everything that depends on it (the enum, the list of capacities, the pool that
//! recycles slot tables and the function that builds a core for the smallest rung that holds `n` sessions) is generated
//! from that one list.
//!
//! Invariants: every method forwards to the endpoint method of the same name and adds nothing; the `Gone` rung, left
//! behind when the endpoint is recycled, answers nothing.

use std::net::SocketAddr;

use vinc_core::{
    Answer, Command, CommandError, Event, IfaceEvent, IfaceId, NodeStats, Query, Reply, SessionId, Transmit,
};
use vinc_security::PrekeyInfo;
use vinc_transport::stream::NoSource;

use std::sync::Mutex;

use crate::mem::{Ep, EpSlot};

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
        /// The session capacities an endpoint is built for; `Limits::connections` picks the smallest that holds it.
        pub const CAPACITIES: [usize; [$($k),+].len()] = [$($k),+];

        /// The endpoint of one shape of the ladder.
        pub(crate) enum AnyEp {
            $(
                #[doc = concat!("An endpoint for ", stringify!($k), " sessions.")]
                $v(Box<Ep<'static, 'static, $k, { $k * 10 }>>),
            )+
            /// The endpoint was handed back to the pool.
            Gone,
        }

        /// A slot table of one shape, waiting in the pool for the next endpoint.
        pub(crate) enum Idle {
            $($v(&'static mut [EpSlot<'static>; $k], usize),)+
        }

        /// The shapes the pool can hand a table of: one impl per rung.
        pub(crate) trait Rung<const K: usize> {
            fn take(pool: &mut Vec<Idle>, chunks: usize) -> Option<&'static mut [EpSlot<'static>; K]>;
        }

        /// The ladder as a type, to hang [`Rung`] on.
        pub(crate) struct Ladder;

        $(
            impl Rung<$k> for Ladder {
                fn take(pool: &mut Vec<Idle>, chunks: usize) -> Option<&'static mut [EpSlot<'static>; $k]> {
                    let at = pool.iter().position(|t| matches!(t, Idle::$v(_, c) if *c == chunks))?;
                    match pool.swap_remove(at) {
                        Idle::$v(t, _) => Some(t),
                        _ => None,
                    }
                }
            }
        )+

        impl AnyEp {
            /// End the endpoint and give its slot table back to the pool.
            pub(crate) fn recycle(&mut self, chunks: usize) {
                // vertexia: the pool never shrinks (see `crate::mem::Table`)
                let t = match std::mem::replace(self, Self::Gone) {
                    $(Self::$v(e) => e.into_slots_boxed().map(|t| Idle::$v(t, chunks)),)+
                    Self::Gone => None,
                };
                if let Some(t) = t {
                    POOL.lock().unwrap_or_else(std::sync::PoisonError::into_inner).push(t);
                }
            }

            pub(crate) fn handle_datagram(&mut self, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]) {
                match self { $(Self::$v(e) => e.handle_datagram(now, local, remote, buf),)+ Self::Gone => {} }
            }
            pub(crate) fn handle_timeout(&mut self, now: u64) {
                match self { $(Self::$v(e) => e.handle_timeout(now),)+ Self::Gone => {} }
            }
            pub(crate) fn poll_transmit(&mut self, now: u64, out: &mut [u8]) -> Option<Transmit> {
                match self { $(Self::$v(e) => e.poll_transmit(now, out),)+ Self::Gone => None }
            }
            pub(crate) fn poll_timeout(&self) -> Option<u64> {
                match self { $(Self::$v(e) => e.poll_timeout(),)+ Self::Gone => None }
            }
            pub(crate) fn poll_event(&mut self) -> Option<Event> {
                match self { $(Self::$v(e) => e.poll_event(),)+ Self::Gone => None }
            }
            pub(crate) fn command(&mut self, now: u64, c: Command<'_, NoSource>) -> Result<Reply, CommandError> {
                match self { $(Self::$v(e) => e.command(now, c),)+ Self::Gone => Err(CommandError::NoSession) }
            }
            pub(crate) fn query(&self, q: Query) -> Answer<'_> {
                match self { $(Self::$v(e) => e.query(q),)+ Self::Gone => Answer::None }
            }
            pub(crate) fn read_datagram(&mut self, session: SessionId, out: &mut [u8]) -> Result<Option<usize>, CommandError> {
                match self { $(Self::$v(e) => e.read_datagram(session, out),)+ Self::Gone => Err(CommandError::NoSession) }
            }
            pub(crate) fn node_stats(&self) -> Option<NodeStats> {
                match self { $(Self::$v(e) => Some(e.node_stats()),)+ Self::Gone => None }
            }
            pub(crate) fn set_prekey(&mut self, prekey: PrekeyInfo) {
                match self { $(Self::$v(e) => e.set_prekey(prekey),)+ Self::Gone => {} }
            }
            pub(crate) fn register_alpn(&mut self, alpn: &[u8]) -> bool {
                match self { $(Self::$v(e) => e.register_alpn(alpn),)+ Self::Gone => false }
            }
            pub(crate) fn iface_event(&mut self, now: u64, id: IfaceId, ev: IfaceEvent) {
                match self { $(Self::$v(e) => e.iface_event(now, id, ev),)+ Self::Gone => {} }
            }
        }
    };
}
ladder!(define);

/// The slot tables of ended endpoints, for the next endpoint of the same shape.
static POOL: Mutex<Vec<Idle>> = Mutex::new(Vec::new());

/// A table of `K` slots with `chunks` pool chunks each: one an ended endpoint left, else a new one.
///
/// # Errors
/// [`ErrorKind::Config`](crate::ErrorKind::Config) if the table cannot be made.
pub(crate) fn table<const K: usize>(chunks: usize) -> crate::Result<&'static mut [EpSlot<'static>; K]>
where
    Ladder: Rung<K>,
{
    let idle = <Ladder as Rung<K>>::take(
        &mut POOL.lock().unwrap_or_else(std::sync::PoisonError::into_inner),
        chunks,
    );
    match idle {
        Some(t) => Ok(t),
        None => crate::mem::new_table::<K>(chunks),
    }
}
