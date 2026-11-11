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

use vinc_broadcast::Limits as BroadcastLimits;
use vinc_broadcast::consts::{DEFAULT_LOG_BYTES, DEFAULT_MAX_SUBSCRIBERS};
use vinc_connect::client::Config as ConnectConfig;
use vinc_crypto::{Drbg, Software};
use vinc_keystore::KeyStore;
use vinc_node::{Config as NodeConfig, Ep as _, HUB_ALPN, Node};

use crate::clock::wall_ms;
use crate::engine::{Admit, Core, CoreConfig};
use crate::error::{Error, Result};
use crate::keys::Prekeys;
use crate::node::{AnyEp, PEERS, RELAYS};

/// Build a core at time `now`.
///
/// # Errors
/// [`ErrorKind::Config`](crate::ErrorKind::Config) if the limits or the keys are not usable.
pub(crate) fn build<S: KeyStore, A: Admit>(mut cfg: CoreConfig<S, A>, now: u64) -> Result<Core<S, A>> {
    cfg.limits.check()?;
    if cfg.alpns.len() > crate::mem::MAX_PROTOCOLS {
        return Err(Error::config("an endpoint serves at most eight protocols"));
    }
    let mut rnd = [0u8; 32];
    cfg.identity.random(&mut rnd)?;
    let mut seed = [0u8; 8];
    cfg.identity.random(&mut seed)?;
    let mut node_rnd = [0u8; 32];
    cfg.identity.random(&mut node_rnd)?;
    let mut node_seed = [0u8; 8];
    cfg.identity.random(&mut node_seed)?;
    let mut ecfg = vinc_core::EndpointConfig::new(u64::from_le_bytes(seed));
    ecfg.conn.max_gso = cfg.max_gso.max(1);
    ecfg.conn.interface_mtu = cfg.mtu;
    ecfg.conn.send_window = cfg.limits.send_window;
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
    let prekey = prekeys.rotate(now)?;
    ep.set_prekey(prekey.clone());
    for a in &cfg.alpns {
        if !ep.register_alpn(a) {
            return Err(Error::config("a protocol name is empty, too long or one too many"));
        }
    }
    let ifaces = cfg.locals.iter().filter_map(|l| ep.add_iface(*l)).collect();
    let key = cfg.identity.take_signer().ok_or_else(|| {
        Error::config("the identity key is held where the broadcast layer cannot sign with it; use a seed or a generated identity")
    })?;
    let me = cfg.identity.node_id();
    let local = *cfg
        .locals
        .first()
        .ok_or_else(|| Error::config("the endpoint has no local address"))?;
    let mut relays = [None; RELAYS];
    for (slot, relay) in relays.iter_mut().zip(&cfg.relays) {
        *slot = Some(relay.cfg());
    }
    let node_cfg = NodeConfig {
        connect: ConnectConfig {
            me,
            identity: cfg.identity.local()?,
            relays,
            phone: false,
            restarted: false,
            start: now,
            v6: false,
            keep_learn: false,
        },
        is_hub: cfg.hub,
        version: 1,
        alpn: HUB_ALPN,
        limits: BroadcastLimits {
            max_body: cfg.limits.topic_message,
            log_bytes: DEFAULT_LOG_BYTES.max(cfg.limits.topic_message.saturating_mul(4)),
            max_topics: cfg.limits.topics,
            max_subscribers: DEFAULT_MAX_SUBSCRIBERS,
        },
        wall_ms: wall_ms(),
        local,
        trace: false,
    };
    let mut node = Node::<AnyEp, Software, (), RELAYS, PEERS>::new(
        &node_cfg,
        ep,
        prekey,
        Software,
        Drbg::new(&node_rnd),
        key,
        (),
        u64::from_le_bytes(node_seed),
    )
    .map_err(|e| match e {
        vinc_node::StartError::Alpn => Error::config("a protocol name is empty, too long or one too many"),
        vinc_node::StartError::Membership(_) => Error::config("the membership layer could not start"),
        vinc_node::StartError::Broadcast(_) => Error::config("the broadcast layer could not start"),
    })?;
    // The endpoint has no multicast group to announce itself on, and a listener for others' beacons is not wired.
    node.set_local_discovery(false);
    Ok(Core::new(Box::new(node), cfg, prekeys, ifaces))
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
            relays: Vec::new(),
            hub: false,
            connect_timeout: 1_000_000_000,
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
