//! Building an engine: the endpoint of the right capacity, boxed, over the memory its sessions use.
//!
//! The ladder [`CAPACITIES`] lists the session capacities an engine can be built for; [`run`] picks the smallest one
//! that holds [`Limits::connections`](crate::Limits) and builds the endpoint for it with [`start`], which is repeated
//! once per rung. The large tables (the stream tables, the connection slots and the endpoint itself) live on the heap,
//! so building an engine needs a few kilobytes of the caller's stack only.
//!
//! Invariants: the endpoint is built once; its connection id table holds ten entries per session; the memory the slots
//! borrow outlives the engine.

use std::sync::Arc;

use kovan_channel::bounded::Sender;
use vinc_crypto::{Drbg, Software};

use crate::engine::{Engine, EngineConfig};
use crate::error::{Error, Result};
use crate::keys::Prekeys;
use crate::link::SessionShared;
use crate::mem::{Ep, Memory};
use crate::plane::Plane;

/// Define [`CAPACITIES`] and the function that builds an engine for the smallest of them that holds `n` sessions.
macro_rules! ladder {
    ($($k:literal),+ $(,)?) => {
        /// The session capacities an engine is built for; `Limits::connections` picks the smallest that holds it.
        pub const CAPACITIES: [usize; [$($k),+].len()] = [$($k),+];

        fn build(
            n: usize,
            cfg: EngineConfig,
            plane: Plane,
            queue: Sender<Arc<SessionShared>>,
            now: u64,
            f: &mut dyn FnMut(&mut Engine<'_, '_>),
        ) -> Result<()> {
            match n {
                $(n if n <= $k => start::<$k, { $k * 10 }>(cfg, plane, queue, now, f),)+
                _ => Err(Error::config("a limit is out of range")),
            }
        }
    };
}

ladder!(
    1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16_384, 32_768, 65_536
);

/// Build an engine at time `now` and run `f` with it. The endpoint borrows memory that lives for the call, so the
/// engine cannot outlive `f`; nothing is leaked. It works on a thread with the default stack size.
///
/// # Errors
/// [`ErrorKind::Config`](crate::ErrorKind::Config) if the limits or the keys are not usable.
pub fn run<R>(
    cfg: EngineConfig,
    plane: Plane,
    default_queue: Sender<Arc<SessionShared>>,
    now: u64,
    f: impl FnOnce(&mut Engine<'_, '_>) -> R,
) -> Result<R> {
    cfg.limits.check()?;
    let (mut f, mut out) = (Some(f), None);
    let n = cfg.limits.connections;
    build(n, cfg, plane, default_queue, now, &mut |e| out = f.take().map(|f| f(e)))?;
    out.ok_or_else(|| Error::config("the engine did not start"))
}

/// Run `build` on a short-lived thread with a stack of `stack` bytes and return what it built. The tables of an
/// engine (the endpoint, the connection slots, the stream tables) are built as values and moved to the heap, which
/// takes a stack as large as the value; building them here keeps the caller's thread, whatever its stack, from ever
/// holding one. The thread ends before this returns, so its stack is released at once.
fn on_big_stack<T: Send>(stack: usize, build: impl FnOnce() -> T + Send) -> Result<T> {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .name("vinc-build".into())
            .stack_size(stack)
            .spawn_scoped(s, build)
            .map_err(|_| Error::config("the endpoint cannot be built: the system refused a thread"))?
            .join()
            .map_err(|_| Error::config("the endpoint could not be built"))
    })
}

/// The stack the tables of one session are built with, besides the endpoint's own size.
const BUILD_STACK: usize = 8 << 20;

fn start<const K: usize, const D: usize>(
    cfg: EngineConfig,
    plane: Plane,
    default_queue: Sender<Arc<SessionShared>>,
    now: u64,
    f: &mut dyn FnMut(&mut Engine<'_, '_>),
) -> Result<()> {
    const { assert!(D >= 10 * K) };
    let mut mem = on_big_stack(BUILD_STACK, || Memory::new(K))?;
    let chunks = cfg.limits.pool_chunks;
    let mut slots = on_big_stack(BUILD_STACK, || mem.slots::<K>(chunks))??;
    let mut rnd = [0u8; 32];
    cfg.identity.random(&mut rnd)?;
    let mut seed = [0u8; 8];
    cfg.identity.random(&mut seed)?;
    let mut ecfg = vinc_core::EndpointConfig::new(u64::from_le_bytes(seed));
    ecfg.conn.max_gso = cfg.max_gso.max(1);
    ecfg.conn.credit = vinc_security::CreditRecord::new(cfg.limits.stream_window, cfg.limits.streams, u16::MAX);
    let (drbg, identity) = (Drbg::new(&rnd), cfg.identity.local()?);
    let stack = size_of::<Ep<'_, '_, K, D>>()
        .saturating_mul(4)
        .saturating_add(BUILD_STACK);
    let mut ep = on_big_stack(stack, || {
        Box::new(Ep::<K, D>::new(now, Software, drbg, identity, ecfg, &mut slots))
    })?;
    let mut prekeys = Prekeys::new()?;
    ep.set_prekey(prekeys.rotate(now)?);
    for a in &cfg.alpns {
        if !ep.register_alpn(a) {
            return Err(Error::config("a protocol name is empty, too long or one too many"));
        }
    }
    let ifaces = cfg.locals.iter().filter_map(|l| ep.add_iface(*l)).collect();
    let mut engine = Engine::new(ep, cfg, prekeys, plane, default_queue, ifaces, now);
    f(&mut engine);
    Ok(())
}
