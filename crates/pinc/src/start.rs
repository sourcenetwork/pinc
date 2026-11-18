//! Building a core: the endpoint of the right capacity, over the memory its sessions use.
//!
//! [`build`] draws the endpoint's randomness from the identity, then [`AnyEp::new`] builds the endpoint of the smallest
//! rung of [`CAPACITIES`](crate::CAPACITIES) that holds [`Limits::connections`](crate::Limits). The endpoint owns its
//! slot table and the memory of every slot (`Endpoint::new_owned` of `pinc-core`), built on the heap piece by piece,
//! so no table is ever formed on the stack, and the construction is not generic over the host's types, so it is
//! compiled once, optimised, in this crate: the default 1024 sessions build, run and drop on a 1 MiB stack.
//!
//! Invariants: the endpoint is built once; its connection id table holds ten entries per session; everything it uses is
//! freed when it is dropped.

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use pinc_broadcast::consts::DEFAULT_MAX_SUBSCRIBERS;
use pinc_broadcast::{IdKey, Limits as BroadcastLimits};
use pinc_connect::client::Config as ConnectConfig;
use pinc_crypto::{Drbg, Software};
use pinc_keystore::KeyStore;
use pinc_node::{Config as NodeConfig, Ep as _, HUB_ALPN, Node};

use crate::clock::wall_ms;
use crate::engine::{Admit, Core, CoreConfig};
use crate::error::{Error, Result};
use crate::keys::Prekeys;
use crate::node::{AnyEp, PEERS, RELAYS};

/// The endpoint configuration `cfg` asks for. An endpoint that serves other nodes, as a hub or in the relay role,
/// sends no tail repair on its sessions, as a relay host sends none.
fn endpoint_config<S, A>(cfg: &CoreConfig<S, A>, seed: u64) -> pinc_core::EndpointConfig {
    let mut ecfg = pinc_core::EndpointConfig::new(seed);
    ecfg.conn.max_gso = cfg.max_gso.max(1);
    ecfg.conn.interface_mtu = cfg.mtu;
    ecfg.conn.send_window = cfg.limits.send_window;
    ecfg.conn.credit = pinc_security::CreditRecord::new(cfg.limits.stream_window, cfg.limits.streams, u16::MAX);
    ecfg.conn.tail_repair = !(cfg.hub || cfg.relaying);
    ecfg
}

/// The node configuration `cfg` asks for, and the endpoint's local address. The broadcast layer's id tables are
/// placed by the endpoint's own map keys; the connectivity seed is not an input, because it is sent in the clear.
fn node_config<S: KeyStore, A: Admit>(
    cfg: &CoreConfig<S, A>,
    now: u64,
) -> Result<(NodeConfig<RELAYS>, core::net::SocketAddr)> {
    let local = *cfg
        .locals
        .first()
        .ok_or_else(|| Error::config("the endpoint has no local address"))?;
    let mut relays = [None; RELAYS];
    for (slot, relay) in relays.iter_mut().zip(&cfg.relays) {
        *slot = Some(relay.cfg());
    }
    let (seed, secrets) = cfg.map_keys.parts();
    let node_cfg = NodeConfig {
        connect: ConnectConfig {
            me: cfg.identity.node_id(),
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
            log_bytes: cfg.limits.topic_log.max(cfg.limits.topic_message.saturating_mul(4)),
            max_topics: cfg.limits.topics,
            max_subscribers: DEFAULT_MAX_SUBSCRIBERS,
            ..BroadcastLimits::default()
        },
        map_keys: IdKey::new(seed, secrets).map_err(|_| Error::config("the endpoint's map keys are not usable"))?,
        wall_ms: wall_ms(),
        local,
        trace: false,
    };
    Ok((node_cfg, local))
}

/// Build a core at time `now`.
///
/// # Errors
/// [`ErrorKind::Config`](crate::ErrorKind::Config) if the limits or the keys are not usable.
#[allow(
    clippy::too_many_lines,
    reason = "the endpoint, the node and the core, built in the order each needs the last"
)]
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
    let ecfg = endpoint_config(&cfg, u64::from_le_bytes(seed));
    let (drbg, identity) = (Drbg::new(&rnd), cfg.identity.local()?);
    let mut ep = AnyEp::new(
        cfg.limits.connections,
        now,
        drbg,
        identity,
        ecfg,
        cfg.limits.pool_chunks,
        cfg.limits.store_chunks(),
        cfg.limits.spill_slots,
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
    let (node_cfg, local) = node_config(&cfg, now)?;
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
        pinc_node::StartError::Alpn => Error::config("a protocol name is empty, too long or one too many"),
        pinc_node::StartError::AlpnOfLayer(_) => Error::config("the protocol name is also the name of a layer"),
        pinc_node::StartError::Membership(_) => Error::config("the membership layer could not start"),
        pinc_node::StartError::Broadcast(_) => Error::config("the broadcast layer could not start"),
    })?;
    if let Some(i) = cfg.relays.iter().take(RELAYS).position(|r| r.home) {
        node.pin_home(i);
    }
    // The endpoint has no multicast group to announce itself on, and a listener for others' beacons is not wired.
    node.set_local_discovery(false);
    // Scoped from the start, with no peers yet: no topic message from outside its component reaches it meanwhile.
    if cfg.connected_topics {
        node.set_adjacent(now, &[])
            .map_err(|_| Error::config("the adjacency record could not be signed"))?;
    }
    // The relay role is a server: it asks no gateway for a mapping, whatever the builder says.
    if cfg.port_mapping.on && !cfg.relaying && !local.ip().to_canonical().is_loopback() {
        node.start_port_mapping(now, cfg.port_mapping.gateway, local, pinc_portmap::client::LIFETIME);
    }
    let mut core = Core::new(Box::new(node), cfg, prekeys, ifaces);
    core.sync_backlog();
    Ok(core)
}

/// The local addresses the endpoint knows: one per family the socket can carry.
pub(crate) fn interfaces(local: core::net::SocketAddr) -> Vec<core::net::SocketAddr> {
    match local {
        core::net::SocketAddr::V6(a) if a.ip().is_unspecified() => {
            vec![
                local,
                core::net::SocketAddr::new(core::net::Ipv4Addr::UNSPECIFIED.into(), a.port()),
            ]
        }
        a => vec![a],
    }
}

/// Whether an endpoint asks its gateway for a port mapping, and the gateway's address.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct PortMapping {
    pub on: bool,
    pub gateway: Option<core::net::IpAddr>,
}

impl PortMapping {
    /// Port mapping off: the default.
    pub(crate) const OFF: Self = Self {
        on: false,
        gateway: None,
    };
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use alloc::format;
    use alloc::vec;
    use alloc::vec::Vec;
    use core::net::SocketAddr;

    use pinc_keystore::SoftwareStore;

    use super::*;
    use crate::engine::AllowAll;
    use crate::keys::Identity;
    use crate::mem::Limits;

    fn cfg(connections: usize) -> CoreConfig<SoftwareStore, AllowAll> {
        CoreConfig {
            identity: Identity::from_seed(&[3; 32]).unwrap(),
            map_keys: crate::maps::Keys::for_tests(3),
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
            connected_topics: false,
            relaying: false,
            connect_timeout: 1_000_000_000,
            port_mapping: PortMapping {
                on: true,
                gateway: None,
            },
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

    /// The broadcast layer's id tables are keyed by the endpoint's map keys; the connectivity seed is no input of the
    /// node configuration.
    #[test]
    fn the_broadcast_key_is_the_endpoints_map_keys() {
        let c = cfg(1);
        let (node_cfg, _) = node_config(&c, 0).unwrap();
        let (seed, secrets) = c.map_keys.parts();
        assert_eq!(node_cfg.map_keys, IdKey::new(seed, secrets).unwrap());
        let other = CoreConfig {
            map_keys: crate::maps::Keys::for_tests(4),
            ..cfg(1)
        };
        assert_ne!(node_config(&other, 0).unwrap().0.map_keys, node_cfg.map_keys);
    }

    /// A node repairs the tail of its bursts; an endpoint that is a hub or runs the relay role does not, on any
    /// session, as a relay host does not.
    #[test]
    fn an_endpoint_that_serves_others_sends_no_tail_repair() {
        assert!(endpoint_config(&cfg(4), 1).conn.tail_repair);
        for (hub, relaying) in [(true, false), (false, true), (true, true)] {
            let c = CoreConfig {
                hub,
                relaying,
                ..cfg(4)
            };
            assert!(
                !endpoint_config(&c, 1).conn.tail_repair,
                "hub {hub}, relay role {relaying}"
            );
        }
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

    const MS: u64 = 1_000_000;
    type C = Core<SoftwareStore, AllowAll>;
    fn end(seed: u8, port: u16) -> (C, SocketAddr) {
        let local: SocketAddr = format!("127.0.0.1:{port}").parse().unwrap();
        let mut c = cfg(4);
        c.identity = Identity::from_seed(&[seed; 32]).unwrap();
        c.locals = vec![local];
        (build(c, MS).unwrap(), local)
    }
    /// Carry datagrams both ways until both ends are at rest, a millisecond a round; the sizes sent go to `log`.
    #[allow(
        clippy::indexing_slicing,
        clippy::panic,
        reason = "a test helper indexes its own two ends and fails loudly"
    )]
    fn settle(ends: &mut [(C, SocketAddr); 2], now: &mut u64, log: &mut Vec<(usize, usize)>) {
        let mut buf = vec![0u8; 65_536];
        let mut idle = 0;
        for _ in 0..400 {
            let mut moved = false;
            for from in 0..2 {
                let (a, b) = ends.split_at_mut(1);
                let (tx, rx) = if from == 0 {
                    (&mut a[0], &mut b[0])
                } else {
                    (&mut b[0], &mut a[0])
                };
                tx.0.service(*now);
                while let Some(t) = tx.0.node.poll_transmit(*now, &mut buf) {
                    log.push((from, t.len));
                    rx.0.node
                        .handle_batch(*now, rx.1, tx.1, &mut buf[..t.len], t.segment_size);
                    moved = true;
                }
            }
            *now += MS;
            // A round without a datagram may be one that answered a key operation: rest is a few of them.
            idle = if moved { 0 } else { idle + 1 };
            if idle == 4 {
                return;
            }
        }
        panic!("the exchange did not come to rest");
    }

    /// The data path's light command changes nothing a peer can see: one exchange run through [`Node::command`] and
    /// again through [`Node::data_command`] sends datagrams of the same sizes in the same order and delivers the same
    /// bytes, and the node's deadline stays what its layers say it is (checked on every call in a debug build).
    #[test]
    fn a_data_command_sends_what_a_command_does() {
        use pinc_core::{Command, Value};

        fn run(light: bool) -> (Vec<(usize, usize)>, Vec<u8>) {
            let mut ends = [end(3, 1), end(4, 2)];
            let (mut now, mut log) = (MS, Vec::new());
            let peer = Identity::<SoftwareStore>::from_seed(&[4; 32]).unwrap().node_id();
            let to = [ends[1].1];
            let session = ends[0].0.connect_start(now, peer, b"t", &to).unwrap();
            settle(&mut ends, &mut now, &mut log);
            let apply = |c: &mut C, now: u64, cmd: Command<'_, _>| {
                if light {
                    c.node.data_command(now, cmd)
                } else {
                    c.node.command(now, cmd)
                }
                .unwrap()
            };
            let stream = match apply(&mut ends[0].0, now, Command::OpenStream { session, bidi: true }) {
                Value::Stream(stream) => stream,
                v => unreachable!("an opened stream answers with its id, not {v:?}"),
            };
            for part in [&b"one "[..], &[7u8; 3000], b" three"] {
                let v = apply(
                    &mut ends[0].0,
                    now,
                    Command::Write {
                        session,
                        stream,
                        data: part,
                    },
                );
                assert!(matches!(v, Value::Written(n) if n == part.len()));
                settle(&mut ends, &mut now, &mut log);
            }
            apply(&mut ends[0].0, now, Command::Finish { session, stream });
            settle(&mut ends, &mut now, &mut log);
            // What the other end holds of the stream, read as the facade reads it.
            let there = ends[1].0.node.endpoint().session_at(0).unwrap().session;
            let mut got = Vec::new();
            while let Some(chunk) = ends[1].0.node.endpoint().read_chunk(there, stream).map(<[u8]>::to_vec) {
                if chunk.is_empty() {
                    break;
                }
                got.extend_from_slice(&chunk);
                apply(
                    &mut ends[1].0,
                    now,
                    Command::Consume {
                        session: there,
                        stream,
                        n: chunk.len(),
                    },
                );
            }
            (log, got)
        }
        let (plain, light) = (run(false), run(true));
        let mut sent = b"one ".to_vec();
        sent.extend_from_slice(&[7u8; 3000]);
        sent.extend_from_slice(b" three");
        assert_eq!(plain.1, sent);
        assert_eq!(light.1, sent);
        assert_eq!(plain.0, light.0, "the two runs sent different datagrams");
        assert!(
            plain.0.len() > 6,
            "a handshake and three writes are more than {} datagrams",
            plain.0.len()
        );
    }
}
