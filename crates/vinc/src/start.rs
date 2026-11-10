//! Building a core: the endpoint of the right capacity, over the memory its sessions use.
//!
//! [`build`] draws the endpoint's randomness from the identity, then [`AnyEp::new`] builds the endpoint of the smallest
//! rung of [`CAPACITIES`](crate::CAPACITIES) that holds [`Limits::connections`](crate::Limits). The endpoint owns its
//! slot table and the memory of every slot (`Endpoint::new_owned` of `vinc-core`), built on the heap piece by piece,
//! so no table is ever formed on the stack, and the construction is not generic over the host's types, so it is
//! compiled once, optimised, in this crate: the default 1024 sessions build, run and drop on a 1 MiB stack.
//!
//! Invariants: the endpoint is built once; its connection id table holds ten entries per session; everything it uses is
//! freed when it is dropped.

use vinc_crypto::Drbg;
use vinc_keystore::KeyStore;

use crate::engine::{Admit, Core, CoreConfig};
use crate::error::{Error, Result};
use crate::keys::Prekeys;
use crate::node::AnyEp;

/// Build a core at time `now`.
///
/// # Errors
/// [`ErrorKind::Config`](crate::ErrorKind::Config) if the limits or the keys are not usable.
pub(crate) fn build<S: KeyStore, A: Admit>(mut cfg: CoreConfig<S, A>, now: u64) -> Result<Core<S, A>> {
    cfg.limits.check()?;
    let mut rnd = [0u8; 32];
    cfg.identity.random(&mut rnd)?;
    let mut seed = [0u8; 8];
    cfg.identity.random(&mut seed)?;
    let mut ecfg = vinc_core::EndpointConfig::new(u64::from_le_bytes(seed));
    ecfg.conn.max_gso = cfg.max_gso.max(1);
    ecfg.conn.interface_mtu = cfg.mtu;
    ecfg.conn.credit = vinc_security::CreditRecord::new(cfg.limits.stream_window, cfg.limits.streams, u16::MAX);
    let (drbg, identity) = (Drbg::new(&rnd), cfg.identity.local()?);
    let mut ep = AnyEp::new(
        cfg.limits.connections,
        now,
        drbg,
        identity,
        ecfg,
        cfg.limits.pool_chunks,
    )
    .ok_or_else(|| Error::config("a limit is out of range"))?;
    let mut prekeys = Prekeys::new()?;
    ep.set_prekey(prekeys.rotate(now)?);
    for a in &cfg.alpns {
        if !ep.register_alpn(a) {
            return Err(Error::config("a protocol name is empty, too long or one too many"));
        }
    }
    let ifaces = cfg.locals.iter().filter_map(|l| ep.add_iface(*l)).collect();
    Ok(Core::new(ep, cfg, prekeys, ifaces))
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
            mtu: 1500,
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

    /// The default 1024 sessions build and drop on a 1 MiB stack: the tables are built on the heap, piece by piece.
    #[test]
    fn a_default_endpoint_builds_and_drops_on_a_one_mebibyte_stack() {
        on_stack(1024, || drop(build(cfg(1024), 1).unwrap()));
    }
}
