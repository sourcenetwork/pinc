//! Building an engine: the endpoint of the right capacity, over the memory its sessions use.
//!
//! [`run`] picks the smallest rung of [`CAPACITIES`](crate::CAPACITIES) that holds
//! [`Limits::connections`](crate::Limits), builds the endpoint for it with [`start`] (repeated once per rung by the
//! ladder macro) and calls the closure it is given with the engine. The tables (the stream tables, the connection slots
//! and the endpoint itself) are built on the stack of the thread that first polls the future and moved to the heap, so
//! that thread needs a stack as large as the endpoint of the capacity asked for; the driver builds no thread of its own
//! for this. The default 1024 sessions build on nuclei's default 8 MiB worker stack (tested); a host that asks for more
//! sets a larger worker stack.
//!
//! Invariants: the endpoint is built once; its connection id table holds ten entries per session; the memory the slots
//! borrow outlives the engine.

use std::sync::Arc;

use kovan_channel::bounded::Sender;
use vinc_crypto::{Drbg, Software};
use vinc_keystore::KeyStore;

use crate::engine::{Admit, Engine, EngineConfig};
use crate::error::{Error, Result};
use crate::keys::Prekeys;
use crate::link::SessionShared;
use crate::mem::{Ep, Memory};
use crate::node::{AnyEp, ladder};
use crate::plane::Plane;

macro_rules! define_run {
    ($($v:ident $k:literal),+) => {
        /// Build an engine at time `now` and run `f` with it. The endpoint borrows memory that lives for the call, so
        /// the engine cannot outlive `f`; nothing is leaked.
        ///
        /// # Errors
        /// [`ErrorKind::Config`](crate::ErrorKind::Config) if the limits or the keys are not usable.
        pub async fn run<S: KeyStore, A: Admit, R>(
            cfg: EngineConfig<S, A>,
            plane: Plane,
            default_queue: Sender<Arc<SessionShared>>,
            now: u64,
            f: impl AsyncFnOnce(&mut Engine<'_, '_, S, A>) -> R,
        ) -> Result<R> {
            cfg.limits.check()?;
            match cfg.limits.connections {
                $(n if n <= $k => start::<S, A, R, $k, { $k * 10 }>(cfg, plane, default_queue, now, f, |e| AnyEp::$v(e)).await,)+
                _ => Err(Error::config("a limit is out of range")),
            }
        }
    };
}
ladder!(define_run);

async fn start<S: KeyStore, A: Admit, R, const K: usize, const D: usize>(
    mut cfg: EngineConfig<S, A>,
    plane: Plane,
    default_queue: Sender<Arc<SessionShared>>,
    now: u64,
    f: impl AsyncFnOnce(&mut Engine<'_, '_, S, A>) -> R,
    wrap: impl for<'s, 'a> FnOnce(Box<Ep<'s, 'a, K, D>>) -> AnyEp<'s, 'a>,
) -> Result<R> {
    const { assert!(D >= 10 * K) };
    let mut mem = Memory::new(K);
    let mut slots = mem.slots::<K>(cfg.limits.pool_chunks)?;
    let mut rnd = [0u8; 32];
    cfg.identity.random(&mut rnd)?;
    let mut seed = [0u8; 8];
    cfg.identity.random(&mut seed)?;
    let mut ecfg = vinc_core::EndpointConfig::new(u64::from_le_bytes(seed));
    ecfg.conn.max_gso = cfg.max_gso.max(1);
    ecfg.conn.credit = vinc_security::CreditRecord::new(cfg.limits.stream_window, cfg.limits.streams, u16::MAX);
    let (drbg, identity) = (Drbg::new(&rnd), cfg.identity.local()?);
    let mut ep = build::<K, D>(now, drbg, identity, ecfg, &mut slots);
    let mut prekeys = Prekeys::new()?;
    ep.set_prekey(prekeys.rotate(now)?);
    for a in &cfg.alpns {
        if !ep.register_alpn(a) {
            return Err(Error::config("a protocol name is empty, too long or one too many"));
        }
    }
    let ifaces = cfg.locals.iter().filter_map(|l| ep.add_iface(*l)).collect();
    let mut engine = Engine::new(wrap(ep), cfg, prekeys, plane, default_queue, ifaces, now);
    Ok(f(&mut engine).await)
}

/// Build the endpoint on the heap from a plain function. The endpoint's tables are large (megabytes at the default
/// capacity): built inside the async function they would sit in the frame of its poll function, and the stack probe
/// of that frame would touch every page on every poll of the driver.
// The endpoint takes these by value; they are moved once, at start.
#[allow(clippy::large_types_passed_by_value)]
#[inline(never)]
fn build<'s, 'a, const K: usize, const D: usize>(
    now: u64,
    drbg: Drbg,
    identity: vinc_security::LocalIdentity,
    ecfg: vinc_core::EndpointConfig,
    slots: &'s mut [crate::mem::EpSlot<'a>; K],
) -> Box<Ep<'s, 'a, K, D>> {
    Box::new(Ep::<K, D>::new(now, Software, drbg, identity, ecfg, slots))
}
