//! Building a core: the endpoint of the right capacity, over the memory its sessions use.
//!
//! [`build`] picks the smallest rung of [`CAPACITIES`](crate::CAPACITIES) that holds
//! [`Limits::connections`](crate::Limits) and builds the endpoint for it with `start` (repeated once per rung by the
//! ladder macro). The endpoint is a large value: it is built by this synchronous function, which no future ever
//! contains, and moved to the heap, so the frame of every poll function stays small. The thread that calls
//! [`build`] needs a stack as large as the endpoint of the capacity asked for, once; nothing else does.
//!
//! Invariants: the endpoint is built once; its connection id table holds ten entries per session; the slot table it
//! borrows comes from the pool of ended endpoints or is new.

use vinc_crypto::{Drbg, Software};
use vinc_keystore::KeyStore;

use crate::engine::{Admit, Core, CoreConfig};
use crate::error::{Error, Result};
use crate::keys::Prekeys;
use crate::mem::Ep;
use crate::node::{AnyEp, Ladder, Rung, ladder, table};

macro_rules! define_build {
    ($($v:ident $k:literal),+) => {
        /// Build a core at time `now`.
        ///
        /// # Errors
        /// [`ErrorKind::Config`](crate::ErrorKind::Config) if the limits or the keys are not usable.
        pub(crate) fn build<S: KeyStore, A: Admit>(cfg: CoreConfig<S, A>, now: u64) -> Result<Core<S, A>> {
            cfg.limits.check()?;
            match cfg.limits.connections {
                $(n if n <= $k => start::<S, A, $k, { $k * 10 }>(cfg, now, AnyEp::$v),)+
                _ => Err(Error::config("a limit is out of range")),
            }
        }
    };
}
ladder!(define_build);

#[inline(never)]
fn start<S: KeyStore, A: Admit, const K: usize, const D: usize>(
    mut cfg: CoreConfig<S, A>,
    now: u64,
    wrap: fn(Box<Ep<'static, 'static, K, D>>) -> AnyEp,
) -> Result<Core<S, A>>
where
    Ladder: Rung<K>,
{
    const { assert!(D >= 10 * K) };
    let slots = table::<K>(cfg.limits.pool_chunks)?;
    let mut rnd = [0u8; 32];
    cfg.identity.random(&mut rnd)?;
    let mut seed = [0u8; 8];
    cfg.identity.random(&mut seed)?;
    let mut ecfg = vinc_core::EndpointConfig::new(u64::from_le_bytes(seed));
    ecfg.conn.max_gso = cfg.max_gso.max(1);
    ecfg.conn.credit = vinc_security::CreditRecord::new(cfg.limits.stream_window, cfg.limits.streams, u16::MAX);
    let (drbg, identity) = (Drbg::new(&rnd), cfg.identity.local()?);
    let mut ep = Box::new(Ep::<K, D>::new(now, Software, drbg, identity, ecfg, slots));
    let mut prekeys = Prekeys::new()?;
    ep.set_prekey(prekeys.rotate(now)?);
    for a in &cfg.alpns {
        if !ep.register_alpn(a) {
            return Err(Error::config("a protocol name is empty, too long or one too many"));
        }
    }
    let ifaces = cfg.locals.iter().filter_map(|l| ep.add_iface(*l)).collect();
    Ok(Core::new(wrap(ep), cfg, prekeys, ifaces))
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use vinc_keystore::SoftwareStore;

    use super::*;
    use crate::engine::AllowAll;
    use crate::keys::Identity;
    use crate::mem::Limits;

    fn cfg(connections: usize) -> CoreConfig<SoftwareStore, AllowAll> {
        CoreConfig {
            identity: Identity::from_seed(&[3; 32]).unwrap(),
            alpns: vec![b"t".to_vec()],
            limits: Limits {
                connections,
                pool_chunks: 16,
                ..Limits::default()
            },
            admit: AllowAll,
            max_gso: 1,
            locals: vec!["127.0.0.1:1".parse().unwrap()],
        }
    }

    fn on_stack(kib: usize, f: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .stack_size(kib << 10)
            .spawn(f)
            .unwrap()
            .join()
            .unwrap();
    }

    /// The endpoint is built into the heap and ended there: a 1 MiB stack builds and drops one for a few sessions.
    #[test]
    fn a_small_endpoint_builds_and_drops_on_a_one_mebibyte_stack() {
        on_stack(1024, || drop(build(cfg(4), 1).unwrap()));
    }

    /// The default 1024 sessions need a stack of about twice the endpoint (2.2 MiB) to build, and nothing to drop.
    #[test]
    fn a_default_endpoint_builds_and_drops_on_six_mebibytes() {
        on_stack(6144, || drop(build(cfg(1024), 1).unwrap()));
    }
}
