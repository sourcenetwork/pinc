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
use vinc_broadcast::consts::DEFAULT_MAX_SUBSCRIBERS;
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
    // `Endpoint::connect` hands back a connection only once the peer answered, never on a cached allow alone.
    ecfg.early_report = false;
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
            log_bytes: cfg.limits.topic_log.max(cfg.limits.topic_message.saturating_mul(4)),
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
    use std::net::SocketAddr;

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
            relaying: false,
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
        use vinc_core::{Command, Value};

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
