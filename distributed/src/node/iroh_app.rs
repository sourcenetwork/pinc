//! The iroh node program: the endpoint with iroh's gossip protocol for publish and subscribe.
//!
//! Set-up, as iroh's documentation describes it, except for what a network with no internet cannot have: the endpoint
//! is bound to the node's address, its relay and discovery services are off, and its address book is filled up front
//! with every node of the scenario (the documentation's own way to give an endpoint addresses it learned out of band).
//! Gossip joins a topic through the hub and relay nodes as its bootstrap peers. A value is a blob in iroh's blob protocol
//! (an in-memory store, as its documentation's first example uses). The downloader takes a blob from one provider at a
//! time, trying the next when one fails: its parallel strategy splits a collection of blobs, which one value is not, so
//! several providers do not add up their rates for iroh.
//!
//! Invariants: the topic and the identity derive from names, so every node agrees without being told; a join that
//! finds no neighbour within its wait is an error, never a silent success; set reconciliation is answered as not available:
//! iroh's protocols have no set reconciliation to configure.

use std::net::{IpAddr, SocketAddr};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use bytes::Bytes;
use futures::StreamExt;
use iroh::address_lookup::memory::MemoryLookup;
use iroh::endpoint::presets;
use iroh::protocol::Router;
use iroh::{Endpoint, EndpointAddr, EndpointId, RelayMode, SecretKey};
use iroh_blobs::api::downloader::{DownloadRequest, Downloader, SplitStrategy};
use iroh_blobs::store::mem::MemStore;
use iroh_blobs::{BlobsProtocol, Hash};
use iroh_gossip::api::{Event, GossipSender};
use iroh_gossip::{Gossip, TopicId};
use serde_json::{Value, json};
use tokio::sync::Mutex as AsyncMutex;

use crate::node::data::{Content, Header, seed32, wall_ns};
use crate::node::proto::{Cmd, Init, Ready};
use crate::node::shell::{Handler, serve};
use crate::node::stats::PubSubStats;
use crate::scenario::Role;

/// The UDP port of every iroh node.
pub const PORT: u16 = 4435;
/// The largest gossip message the program sets up, unless told to keep the library's default of 4 KiB.
const MAX_MESSAGE: usize = 1 << 20;

/// One iroh node.
struct App {
    init: Init,
    me: u16,
    router: Router,
    gossip: Gossip,
    store: MemStore,
    downloader: Downloader,
    stats: Arc<Mutex<PubSubStats>>,
    sender: AsyncMutex<Option<GossipSender>>,
}

fn topic_id(topic: &str) -> TopicId {
    TopicId::from_bytes(seed32(topic, "iroh-topic"))
}

fn secret(name: &str) -> SecretKey {
    SecretKey::from_bytes(&seed32(name, "iroh-identity"))
}

impl App {
    async fn start(init: Init) -> Result<(Arc<Self>, Ready), String> {
        let me_spec = init
            .me()
            .ok_or_else(|| format!("{} is not a node of the scenario", init.name))?
            .clone();
        let book = MemoryLookup::new();
        for p in init.peers.iter().filter(|p| p.name != init.name) {
            book.add_endpoint_info(
                EndpointAddr::new(secret(&p.name).public())
                    .with_ip_addr(SocketAddr::new(IpAddr::V4(p.public_ip), p.port(PORT))),
            );
        }
        let ep = Endpoint::builder(presets::Minimal)
            .relay_mode(RelayMode::Disabled)
            .secret_key(secret(&init.name))
            .address_lookup(book)
            .clear_ip_transports()
            .bind_addr(SocketAddr::new(IpAddr::V4(me_spec.ip), me_spec.port(PORT)))
            .map_err(|e| format!("the address {} is not usable: {e}", me_spec.ip))?
            .bind()
            .await
            .map_err(|e| format!("the iroh endpoint did not start: {e}"))?;
        let mut gossip = Gossip::builder();
        if !init.library_limits {
            gossip = gossip.max_message_size(MAX_MESSAGE);
        }
        let gossip = gossip.spawn(ep.clone());
        let limit = if init.library_limits { "the library's default of 4 KiB" } else { "1 MiB" };
        let store = MemStore::new();
        let downloader = store.downloader(&ep);
        let router = Router::builder(ep.clone())
            .accept(iroh_gossip::ALPN, gossip.clone())
            .accept(iroh_blobs::ALPN, BlobsProtocol::new(&store, None))
            .spawn();
        let ready = Ready {
            stack: "iroh".into(),
            id: ep.id().to_string(),
            config: format!(
                "the iroh endpoint with its gossip protocol (messages up to {limit}) and blob protocol (in-memory store, \
                 downloader, one provider at a time); relay and discovery services off, every node's address in the endpoint's address book; \
                 bootstrap through the hub and relay nodes"
            ),
        };
        let me = me_spec.index;
        Ok((
            Arc::new(Self {
                init,
                me,
                router,
                gossip,
                store,
                downloader,
                stats: Arc::new(Mutex::new(PubSubStats::new(me))),
                sender: AsyncMutex::new(None),
            }),
            ready,
        ))
    }

    async fn join(&self, topic: &str, wait_ms: u64) -> Result<Value, String> {
        let hubs: Vec<_> = self
            .init
            .peers
            .iter()
            .filter(|p| p.role != Role::Peer && p.name != self.init.name)
            .map(|p| secret(&p.name).public())
            .collect();
        let is_hub = self.init.me().is_some_and(|m| m.role != Role::Peer);
        let (sender, mut receiver) = self
            .gossip
            .subscribe(topic_id(topic), hubs)
            .await
            .map_err(|e| format!("the topic could not be joined: {e}"))?
            .split();
        if !is_hub {
            tokio::time::timeout(Duration::from_millis(wait_ms), receiver.joined())
                .await
                .map_err(|_| "no node answered in time; check that a hub or relay node is reachable".to_owned())?
                .map_err(|e| format!("the topic could not be joined: {e}"))?;
        }
        let stats = Arc::clone(&self.stats);
        tokio::spawn(async move {
            while let Some(ev) = receiver.next().await {
                if let Ok(Event::Received(m)) = ev
                    && let Ok(mut s) = stats.lock()
                {
                    s.record(&m.content, wall_ns());
                }
            }
        });
        *self.sender.lock().await = Some(sender);
        Ok(Value::Null)
    }

    async fn publish(&self, count: u32, size: u32, interval_us: u64, start_ns: u64) -> Result<Value, String> {
        let guard = self.sender.lock().await;
        let sender = guard.as_ref().ok_or("join the topic before publishing to it")?.clone();
        drop(guard);
        let lead = start_ns.saturating_sub(wall_ns());
        let start = tokio::time::Instant::now() + Duration::from_nanos(lead);
        for seq in 0..count {
            tokio::time::sleep_until(start + Duration::from_micros(interval_us * u64::from(seq))).await;
            let body = Header {
                origin: self.me,
                seq,
                sent_ns: wall_ns(),
            }
            .body(size as usize);
            sender
                .broadcast(Bytes::from(body))
                .await
                .map_err(|e| format!("a message could not be published: {e}"))?;
            if let Ok(mut s) = self.stats.lock() {
                s.published();
            }
        }
        Ok(json!({ "published": count }))
    }

    async fn provide(&self, size: u64, seed: u64) -> Result<Value, String> {
        let content = Content::new(seed, size);
        let mut data = vec![0u8; usize::try_from(size).map_err(|_| "the value is too large for this machine")?];
        content.fill(0, &mut data);
        let tag = self
            .store
            .blobs()
            .add_bytes(Bytes::from(data))
            .await
            .map_err(|e| format!("the value could not be stored: {e}"))?;
        Ok(json!({ "hash": tag.hash.to_string(), "size": size }))
    }

    async fn fetch(&self, value: &Value, providers: &[String], timeout_ms: u64) -> Result<Value, String> {
        let hash: Hash = value
            .get("hash")
            .and_then(Value::as_str)
            .ok_or("the value to fetch needs a hash")?
            .parse()
            .map_err(|e| format!("the hash is not valid: {e}"))?;
        let size = value.get("size").and_then(Value::as_u64).unwrap_or(0);
        let ids: Vec<EndpointId> = providers.iter().map(|p| secret(p).public()).collect();
        let started = std::time::Instant::now();
        let progress = self
            .downloader
            .download_with_opts(DownloadRequest::new(hash, ids, SplitStrategy::None));
        tokio::time::timeout(Duration::from_millis(timeout_ms), progress)
            .await
            .map_err(|_| "the value did not arrive in time".to_owned())?
            .map_err(|e| format!("the value could not be fetched: {e}"))?;
        Ok(json!({ "bytes": size, "ms": started.elapsed().as_secs_f64() * 1000.0 }))
    }
}

impl Handler for App {
    async fn handle(self: Arc<Self>, cmd: Cmd) -> Result<Value, String> {
        match cmd {
            Cmd::Join { topic, wait_ms } => self.join(&topic, wait_ms).await,
            Cmd::Publish {
                count,
                size,
                interval_us,
                start_ns,
                ..
            } => self.publish(count, size, interval_us, start_ns).await,
            Cmd::Report => {
                let rep = self.stats.lock().map_err(|_| "the counters are unavailable")?.report();
                Ok(json!({ "pubsub": rep }))
            }
            Cmd::Stop => {
                self.router
                    .shutdown()
                    .await
                    .map_err(|e| format!("the endpoint did not close cleanly: {e}"))?;
                Ok(Value::Null)
            }
            Cmd::Suspend | Cmd::Resume => Err("iroh has no notion of a node going to sleep: not available".into()),
            Cmd::Provide { size, seed } => self.provide(size, seed).await,
            Cmd::Fetch {
                value,
                providers,
                timeout_ms,
            } => self.fetch(&value, &providers, timeout_ms).await,
            Cmd::HoldSet { .. } | Cmd::Reconcile { .. } => {
                Err("set reconciliation is not available for iroh: it has no protocol for it".into())
            }
        }
    }
}

/// Run the iroh node program until it is told to stop.
///
/// # Errors
/// The endpoint could not start.
pub fn run(init: Init) -> Result<(), String> {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .map_err(|e| format!("the runtime did not start: {e}"))?;
    rt.block_on(async {
        let (app, ready) = App::start(init).await?;
        serve(app, ready).await
    })
}
