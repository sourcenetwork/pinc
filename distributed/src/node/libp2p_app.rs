//! The rust-libp2p node program: the swarm over QUIC with gossipsub for publish and subscribe and a request-response
//! protocol for fetching a value.
//!
//! Set-up, as the library's documentation describes it: a signed gossipsub behaviour with its default mesh parameters
//! and heartbeat, a request-response behaviour with a codec of its own (the library ships none for raw bytes), over the
//! QUIC transport, an identity per node, and the hub and relay nodes dialled as the bootstrap peers (there is no
//! discovery service on the emulated network, so the mesh forms around them). A value is fetched in blocks of 256 KiB, 16
//! requests in flight per provider, spread over the providers in turn; the library has no verified transfer, so the
//! fetcher checks the whole value against its BLAKE3 hash at the end, which is inside the time reported.
//!
//! Invariants: the swarm is polled by one task that owns it; every message the node publishes that the library refuses
//! (no peer to send to) is counted and reported, never hidden; a join that finds no mesh peer within its wait is an
//! error; a fetch ends with the hash checked or with the reason it failed.

use std::collections::HashMap;
use std::io;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use futures::{AsyncReadExt, AsyncWriteExt, StreamExt};
use libp2p::gossipsub::{self, IdentTopic, MessageAuthenticity};
use libp2p::identity::Keypair;
use libp2p::request_response::{self, OutboundRequestId, ProtocolSupport};
use libp2p::swarm::{NetworkBehaviour, SwarmEvent};
use libp2p::{Multiaddr, PeerId, StreamProtocol, SwarmBuilder};
use serde_json::{Value, json};
use tokio::sync::{mpsc, oneshot};

use crate::node::data::{Content, Header, seed32, wall_ns};
use crate::node::proto::{Cmd, Init, Ready};
use crate::node::shell::{Handler, serve};
use crate::node::stats::PubSubStats;
use crate::scenario::Role;

/// The UDP port of every libp2p node.
pub const PORT: u16 = 4436;
/// The largest gossipsub message the program sets up (the library's default is 64 KiB).
const MAX_MESSAGE: usize = 1 << 20;
/// Bytes of one block of a fetched value.
const BLOCK: u64 = 256 << 10;
/// Block requests in flight per provider.
const WINDOW: usize = 16;
const BLOCKS: StreamProtocol = StreamProtocol::new("/vinc-distributed/blocks/1");

fn keypair(name: &str) -> Result<Keypair, String> {
    Keypair::ed25519_from_bytes(seed32(name, "libp2p-identity"))
        .map_err(|e| format!("the identity could not be made: {e}"))
}

fn peer_of(name: &str) -> Result<PeerId, String> {
    keypair(name).map(|k| k.public().to_peer_id())
}

fn addr_of(ip: std::net::Ipv4Addr, port: u16, peer: &PeerId) -> Result<Multiaddr, String> {
    format!("/ip4/{ip}/udp/{port}/quic-v1/p2p/{peer}")
        .parse()
        .map_err(|e| format!("an address could not be made: {e}"))
}

/// A request for a block of the value.
#[derive(Debug, Clone, Copy)]
struct BlockRequest {
    offset: u64,
    len: u32,
}

/// The codec of the block protocol: a request is 12 bytes, a response is the block.
#[derive(Debug, Clone, Default)]
struct BlockCodec;

impl request_response::Codec for BlockCodec {
    type Protocol = StreamProtocol;
    type Request = BlockRequest;
    type Response = Vec<u8>;

    async fn read_request<T>(&mut self, _: &Self::Protocol, io: &mut T) -> io::Result<BlockRequest>
    where
        T: futures::AsyncRead + Unpin + Send,
    {
        let mut b = [0u8; 12];
        io.read_exact(&mut b).await?;
        let (off, len) = b.split_at(8);
        Ok(BlockRequest {
            offset: u64::from_be_bytes(off.try_into().map_err(|_| io::ErrorKind::InvalidData)?),
            len: u32::from_be_bytes(len.try_into().map_err(|_| io::ErrorKind::InvalidData)?),
        })
    }

    async fn read_response<T>(&mut self, _: &Self::Protocol, io: &mut T) -> io::Result<Vec<u8>>
    where
        T: futures::AsyncRead + Unpin + Send,
    {
        let mut out = Vec::new();
        io.take(BLOCK + 1).read_to_end(&mut out).await?;
        Ok(out)
    }

    async fn write_request<T>(&mut self, _: &Self::Protocol, io: &mut T, req: BlockRequest) -> io::Result<()>
    where
        T: futures::AsyncWrite + Unpin + Send,
    {
        let mut b = [0u8; 12];
        b[..8].copy_from_slice(&req.offset.to_be_bytes());
        b[8..].copy_from_slice(&req.len.to_be_bytes());
        io.write_all(&b).await?;
        io.close().await
    }

    async fn write_response<T>(&mut self, _: &Self::Protocol, io: &mut T, res: Vec<u8>) -> io::Result<()>
    where
        T: futures::AsyncWrite + Unpin + Send,
    {
        io.write_all(&res).await?;
        io.close().await
    }
}

#[derive(NetworkBehaviour)]
struct Behaviour {
    gossipsub: gossipsub::Behaviour,
    blocks: request_response::Behaviour<BlockCodec>,
}

enum SwarmCmd {
    Subscribe(String, oneshot::Sender<Result<(), String>>),
    MeshPeers(String, oneshot::Sender<usize>),
    Publish(String, Vec<u8>),
    Provide(Content, oneshot::Sender<[u8; 32]>),
    Fetch {
        size: u64,
        root: [u8; 32],
        providers: Vec<PeerId>,
        done: oneshot::Sender<Result<f64, String>>,
    },
    Stop(oneshot::Sender<()>),
}

/// A fetch in progress.
struct Job {
    size: u64,
    root: [u8; 32],
    buf: Vec<u8>,
    providers: Vec<PeerId>,
    next: u64,
    inflight: HashMap<OutboundRequestId, (u64, usize)>,
    per_provider: Vec<usize>,
    filled: u64,
    started: Instant,
    done: Option<oneshot::Sender<Result<f64, String>>>,
}

impl Job {
    /// Send requests while a provider has room in its window and a block is left to ask for.
    fn fill(&mut self, b: &mut request_response::Behaviour<BlockCodec>) {
        while self.next < self.size {
            // The provider with the fewest requests in flight takes the next block.
            let Some((slot, load)) = self.per_provider.iter().copied().enumerate().min_by_key(|(_, c)| *c) else {
                return;
            };
            if load >= WINDOW {
                return;
            }
            self.send(b, slot);
        }
    }

    fn send(&mut self, b: &mut request_response::Behaviour<BlockCodec>, slot: usize) {
        let Some(peer) = self.providers.get(slot) else { return };
        let len = BLOCK.min(self.size - self.next);
        let id = b.send_request(
            peer,
            BlockRequest {
                offset: self.next,
                len: u32::try_from(len).unwrap_or(u32::MAX),
            },
        );
        self.inflight.insert(id, (self.next, slot));
        if let Some(c) = self.per_provider.get_mut(slot) {
            *c += 1;
        }
        self.next += len;
    }

    fn finish(&mut self, r: Result<f64, String>) {
        if let Some(d) = self.done.take() {
            let _ = d.send(r);
        }
    }
}

/// One libp2p node.
struct App {
    init: Init,
    me: u16,
    cmds: mpsc::UnboundedSender<SwarmCmd>,
    stats: Arc<std::sync::Mutex<PubSubStats>>,
    refused: Arc<AtomicU64>,
}

struct Driver {
    swarm: libp2p::Swarm<Behaviour>,
    stats: Arc<std::sync::Mutex<PubSubStats>>,
    refused: Arc<AtomicU64>,
    served: Option<Content>,
    job: Option<Job>,
}

impl Driver {
    fn on_event(&mut self, ev: SwarmEvent<BehaviourEvent>) {
        match ev {
            SwarmEvent::Behaviour(BehaviourEvent::Gossipsub(gossipsub::Event::Message { message, .. })) => {
                if let Ok(mut s) = self.stats.lock() {
                    s.record(&message.data, wall_ns());
                }
            }
            SwarmEvent::Behaviour(BehaviourEvent::Blocks(request_response::Event::Message { message, .. })) => {
                match message {
                    request_response::Message::Request { request, channel, .. } => {
                        let mut out = vec![0u8; usize::try_from(u64::from(request.len).min(BLOCK)).unwrap_or(0)];
                        let n = self.served.as_ref().map_or(0, |c| c.fill(request.offset, &mut out));
                        out.truncate(n);
                        let _ = self.swarm.behaviour_mut().blocks.send_response(channel, out);
                    }
                    request_response::Message::Response { request_id, response } => {
                        self.on_block(request_id, &response);
                    }
                }
            }
            SwarmEvent::Behaviour(BehaviourEvent::Blocks(request_response::Event::OutboundFailure {
                request_id,
                error,
                ..
            })) => {
                if let Some(job) = self.job.as_mut()
                    && job.inflight.remove(&request_id).is_some()
                {
                    job.finish(Err(format!("a block could not be fetched ({error})")));
                    self.job = None;
                }
            }
            _ => {}
        }
    }

    fn on_block(&mut self, id: OutboundRequestId, data: &[u8]) {
        let Some(job) = self.job.as_mut() else { return };
        let Some((offset, slot)) = job.inflight.remove(&id) else {
            return;
        };
        if let Some(c) = job.per_provider.get_mut(slot) {
            *c = c.saturating_sub(1);
        }
        let start = usize::try_from(offset).unwrap_or(usize::MAX);
        let Some(dst) = job.buf.get_mut(start..start + data.len()) else {
            job.finish(Err("a block had the wrong size".into()));
            self.job = None;
            return;
        };
        dst.copy_from_slice(data);
        job.filled += data.len() as u64;
        if job.filled >= job.size {
            let ok = *blake3::hash(&job.buf).as_bytes() == job.root;
            let ms = job.started.elapsed().as_secs_f64() * 1000.0;
            job.finish(if ok {
                Ok(ms)
            } else {
                Err("the value did not match its hash".into())
            });
            self.job = None;
        } else {
            job.fill(&mut self.swarm.behaviour_mut().blocks);
        }
    }

    fn on_cmd(&mut self, cmd: SwarmCmd) -> bool {
        match cmd {
            SwarmCmd::Subscribe(t, done) => {
                let r = self.swarm.behaviour_mut().gossipsub.subscribe(&IdentTopic::new(t));
                let _ = done.send(r.map(|_| ()).map_err(|e| e.to_string()));
            }
            SwarmCmd::MeshPeers(t, done) => {
                let n = self
                    .swarm
                    .behaviour()
                    .gossipsub
                    .mesh_peers(&IdentTopic::new(t).hash())
                    .count();
                let _ = done.send(n);
            }
            SwarmCmd::Publish(t, data) => {
                if self
                    .swarm
                    .behaviour_mut()
                    .gossipsub
                    .publish(IdentTopic::new(t), data)
                    .is_err()
                {
                    self.refused.fetch_add(1, Ordering::Relaxed);
                }
            }
            SwarmCmd::Provide(content, done) => {
                let mut h = blake3::Hasher::new();
                let mut buf = vec![0u8; 1 << 20];
                let mut off = 0;
                while off < content.len() {
                    let n = content.fill(off, &mut buf);
                    if n == 0 {
                        break;
                    }
                    h.update(buf.get(..n).unwrap_or_default());
                    off += n as u64;
                }
                self.served = Some(content);
                let _ = done.send(*h.finalize().as_bytes());
            }
            SwarmCmd::Fetch {
                size,
                root,
                providers,
                done,
            } => match usize::try_from(size) {
                Ok(n) => {
                    let mut job = Job {
                        size,
                        root,
                        buf: vec![0u8; n],
                        per_provider: vec![0; providers.len()],
                        providers,
                        next: 0,
                        inflight: HashMap::new(),
                        filled: 0,
                        started: Instant::now(),
                        done: Some(done),
                    };
                    if size == 0 {
                        job.finish(Ok(0.0));
                    } else {
                        job.fill(&mut self.swarm.behaviour_mut().blocks);
                        self.job = Some(job);
                    }
                }
                Err(_) => {
                    let _ = done.send(Err("the value is larger than this machine can hold".into()));
                }
            },
            SwarmCmd::Stop(done) => {
                let _ = done.send(());
                return false;
            }
        }
        true
    }
}

impl App {
    fn start(init: Init) -> Result<(Arc<Self>, Ready), String> {
        let me_spec = init
            .me()
            .ok_or_else(|| format!("{} is not a node of the scenario", init.name))?
            .clone();
        let key = keypair(&init.name)?;
        let peer_id = key.public().to_peer_id();
        let gcfg = gossipsub::ConfigBuilder::default()
            .max_transmit_size(MAX_MESSAGE)
            .build()
            .map_err(|e| format!("the gossipsub settings were refused: {e}"))?;
        let mut swarm = SwarmBuilder::with_existing_identity(key.clone())
            .with_tokio()
            .with_quic()
            .with_behaviour(|k| {
                Ok(Behaviour {
                    gossipsub: gossipsub::Behaviour::new(MessageAuthenticity::Signed(k.clone()), gcfg)
                        .map_err(ToString::to_string)?,
                    blocks: request_response::Behaviour::with_codec(
                        BlockCodec,
                        [(BLOCKS, ProtocolSupport::Full)],
                        request_response::Config::default().with_request_timeout(Duration::from_secs(60)),
                    ),
                })
            })
            .map_err(|e| format!("the swarm did not start: {e}"))?
            .with_swarm_config(|c| c.with_idle_connection_timeout(Duration::from_secs(300)))
            .build();
        let listen: Multiaddr = format!("/ip4/{}/udp/{}/quic-v1", me_spec.ip, me_spec.port(PORT))
            .parse()
            .map_err(|e| format!("the listen address is not valid: {e}"))?;
        swarm
            .listen_on(listen)
            .map_err(|e| format!("the swarm could not listen on {}: {e}", me_spec.ip))?;
        // Every node's address is known up front, as a static peer list gives it; only the hubs are dialled.
        let mut bootstrap = Vec::new();
        for p in init.peers.iter().filter(|p| p.name != init.name) {
            let id = peer_of(&p.name)?;
            let addr = addr_of(p.public_ip, p.port(PORT), &id)?;
            swarm.add_peer_address(id, addr.clone());
            if p.role != Role::Peer {
                bootstrap.push((id, addr));
            }
        }
        let stats = Arc::new(std::sync::Mutex::new(PubSubStats::new(me_spec.index)));
        let refused = Arc::new(AtomicU64::new(0));
        let (tx, mut rx) = mpsc::unbounded_channel::<SwarmCmd>();
        let mut driver = Driver {
            swarm,
            stats: Arc::clone(&stats),
            refused: Arc::clone(&refused),
            served: None,
            job: None,
        };
        tokio::spawn(async move {
            // The bootstrap peers are dialled again every second while they are not connected: they may start later.
            let mut redial = tokio::time::interval(Duration::from_secs(1));
            loop {
                tokio::select! {
                    _ = redial.tick() => {
                        for (id, addr) in &bootstrap {
                            if !driver.swarm.is_connected(id) {
                                let _ = driver.swarm.dial(addr.clone());
                            }
                        }
                    }
                    ev = driver.swarm.select_next_some() => driver.on_event(ev),
                    cmd = rx.recv() => match cmd {
                        Some(c) => if !driver.on_cmd(c) { return },
                        None => return,
                    },
                }
            }
        });
        let app = Arc::new(Self {
            init,
            me: me_spec.index,
            cmds: tx,
            stats,
            refused,
        });
        let ready = Ready {
            stack: "libp2p".into(),
            id: peer_id.to_string(),
            config:
                "rust-libp2p over QUIC with signed gossipsub (default mesh and heartbeat, messages up to 1 MiB) and a \
                     request-response protocol for values (256 KiB blocks, 16 requests in flight per provider, hash \
                     checked at the end); the hub and relay nodes are dialled as bootstrap peers"
                    .into(),
        };
        Ok((app, ready))
    }

    async fn ask<T>(&self, make: impl FnOnce(oneshot::Sender<T>) -> SwarmCmd) -> Result<T, String> {
        let (tx, rx) = oneshot::channel();
        self.cmds.send(make(tx)).map_err(|_| "the swarm stopped".to_owned())?;
        rx.await.map_err(|_| "the swarm stopped".to_owned())
    }

    async fn join(&self, topic: &str, wait_ms: u64) -> Result<Value, String> {
        self.ask(|tx| SwarmCmd::Subscribe(topic.to_owned(), tx)).await??;
        let is_hub = self.init.me().is_some_and(|m| m.role != Role::Peer);
        if is_hub {
            return Ok(Value::Null);
        }
        let deadline = tokio::time::Instant::now() + Duration::from_millis(wait_ms);
        loop {
            if self.ask(|tx| SwarmCmd::MeshPeers(topic.to_owned(), tx)).await? > 0 {
                return Ok(Value::Null);
            }
            if tokio::time::Instant::now() >= deadline {
                return Err(
                    "no node joined the topic's mesh in time; check that a hub or relay node is reachable".into(),
                );
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    }

    async fn publish(
        &self,
        topic: &str,
        count: u32,
        size: u32,
        interval_us: u64,
        start_ns: u64,
    ) -> Result<Value, String> {
        let lead = start_ns.saturating_sub(wall_ns());
        let start = tokio::time::Instant::now() + Duration::from_nanos(lead);
        let before = self.refused.load(Ordering::Relaxed);
        for seq in 0..count {
            tokio::time::sleep_until(start + Duration::from_micros(interval_us * u64::from(seq))).await;
            let body = Header {
                origin: self.me,
                seq,
                sent_ns: wall_ns(),
            }
            .body(size as usize);
            self.cmds
                .send(SwarmCmd::Publish(topic.to_owned(), body))
                .map_err(|_| "the swarm stopped")?;
            if let Ok(mut s) = self.stats.lock() {
                s.published();
            }
        }
        // Give the swarm task the chance to take the last message before the count is read.
        tokio::time::sleep(Duration::from_millis(50)).await;
        Ok(json!({ "published": count, "refused": self.refused.load(Ordering::Relaxed) - before }))
    }

    async fn provide(&self, size: u64, seed: u64) -> Result<Value, String> {
        let content = Content::new(seed, size);
        let root = self.ask(|tx| SwarmCmd::Provide(content, tx)).await?;
        let hex = root.iter().fold(String::new(), |mut s, b| {
            use std::fmt::Write as _;
            let _ = write!(s, "{b:02x}");
            s
        });
        Ok(json!({ "root": hex, "size": size }))
    }

    async fn fetch(&self, value: &Value, providers: &[String], timeout_ms: u64) -> Result<Value, String> {
        let size = value
            .get("size")
            .and_then(Value::as_u64)
            .ok_or("the value to fetch needs a size")?;
        let hex = value
            .get("root")
            .and_then(Value::as_str)
            .ok_or("the value to fetch needs a root")?;
        let mut root = [0u8; 32];
        for (i, o) in root.iter_mut().enumerate() {
            *o = hex
                .get(2 * i..2 * i + 2)
                .and_then(|h| u8::from_str_radix(h, 16).ok())
                .ok_or("the root is not valid")?;
        }
        let ids = providers.iter().map(|p| peer_of(p)).collect::<Result<Vec<_>, _>>()?;
        let (tx, rx) = oneshot::channel();
        self.cmds
            .send(SwarmCmd::Fetch {
                size,
                root,
                providers: ids,
                done: tx,
            })
            .map_err(|_| "the swarm stopped")?;
        let ms = tokio::time::timeout(Duration::from_millis(timeout_ms), rx)
            .await
            .map_err(|_| "the value did not arrive in time".to_owned())?
            .map_err(|_| "the swarm stopped".to_owned())??;
        Ok(json!({ "bytes": size, "ms": ms }))
    }
}

impl Handler for App {
    async fn handle(self: Arc<Self>, cmd: Cmd) -> Result<Value, String> {
        match cmd {
            Cmd::Join { topic, wait_ms } => self.join(&topic, wait_ms).await,
            Cmd::Publish {
                topic,
                count,
                size,
                interval_us,
                start_ns,
            } => self.publish(&topic, count, size, interval_us, start_ns).await,
            Cmd::Provide { size, seed } => self.provide(size, seed).await,
            Cmd::Fetch {
                value,
                providers,
                timeout_ms,
            } => self.fetch(&value, &providers, timeout_ms).await,
            Cmd::Report => {
                let rep = self.stats.lock().map_err(|_| "the counters are unavailable")?.report();
                Ok(json!({ "pubsub": rep, "refused": self.refused.load(Ordering::Relaxed) }))
            }
            Cmd::Stop => {
                let _ = self.ask(SwarmCmd::Stop).await;
                Ok(Value::Null)
            }
            Cmd::Suspend | Cmd::Resume => Err("libp2p has no notion of a node going to sleep: not available".into()),
            Cmd::HoldSet { .. } | Cmd::Reconcile { .. } => {
                Err("set reconciliation is not available for libp2p: it has no protocol for it".into())
            }
            Cmd::DtnContacts { .. } | Cmd::DtnSend { .. } => {
                Err("delay-tolerant delivery is not available for libp2p: it has no store and forward".into())
            }
        }
    }
}

/// Run the libp2p node program until it is told to stop.
///
/// # Errors
/// The swarm could not start.
pub fn run(init: Init) -> Result<(), String> {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .map_err(|e| format!("the runtime did not start: {e}"))?;
    rt.block_on(async {
        let (app, ready) = App::start(init)?;
        serve(app, ready).await
    })
}
