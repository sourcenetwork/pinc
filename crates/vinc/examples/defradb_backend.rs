//! The sketch of a VINC backend for a peer-to-peer transport trait shaped like DefraDB.rs's `P2PTransport`, with no
//! dependency on it: the contract a `DefraDB` backend implements against.
//!
//! The trait below keeps the shape that matters: a cloneable handle, a text peer id equal to the hex of the public key,
//! `sign`, `dial` with address hints or by peer id alone, `disconnect`, `connected_peers`, a request that returns its
//! reply, an inbound request that carries a response token (the send half of the request's own stream), and
//! `shutdown`. Protocols are per-stream tags on one connection per peer, so a failure on one stream never closes the
//! connection. Beside the trait sit the calls `DefraDB`'s peer assembly makes on its transport directly:
//!
//! - **Service classes.** Each tag has an urgency ([`urgency_of`]): control traffic (KMS, peer info) at 0, document
//!   pushes at the default 3, block transfers at 7, so a key request is not queued behind a 64 MiB CAR reply on the
//!   same connection. Both the request and the reply stream take the class of their tag.
//! - **Admission.** An allowlist (accept everyone, or only the listed peers) is the endpoint's access hook;
//!   `allow_peer` adds to it and lifts a revocation, `deny_peer` revokes the peer, which ends every session with it, and
//!   `is_peer_revoked` reads the bar. The hook is asked on accept, on dial and for any neighbour a layer takes.
//! - **Service records.** A node publishes a signed record of its addresses with up to 64 bytes of hints; `DefraDB`
//!   keeps a 38-byte pointer to its service records there (`set_service_pointer`, `service_pointer`). A dial with no
//!   hints finds the peer through that record. The rendezvous here is an in-process directory; with the relay client
//!   in the facade it is the node's home relay.
//!
//! - **Raw pubsub.** `subscribe_raw` joins a topic and `publish_raw` publishes opaque bytes to it, through a hub: any
//!   endpoint built with the hub role (here a third endpoint of the same process) that the others name as their relay.
//!   `register_pubsub_rpc_topic` answers every message on a topic on the requester's own response topic
//!   ([`response_topic`]: `<topic>/<peer>/_response`), the way `DefraDB`'s KMS answers key requests. Every message is
//!   signed by its publisher and the endpoint verifies it before it is delivered. An endpoint has one queue of topic
//!   events: read it in one place (`next_raw`, or the task an RPC topic starts).
//!
//! Run with `cargo run -p vinc --example defradb_backend`.

#![allow(
    missing_docs,
    unreachable_pub,
    async_fn_in_trait,
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::indexing_slicing,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::single_match_else,
    reason = "an example favours the short form"
)]

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::future::Future;
use std::net::{SocketAddr, UdpSocket};
use std::rc::Rc;
use std::sync::Arc;
use std::time::{Duration, Instant};

use nuclei::Handle;
use nuclei::sync::Mutex as AsyncMutex;
use nuclei::sync::mpsc::{UnboundedReceiver, UnboundedSender, unbounded_channel};
use nuclei::time::sleep_until_precise;
use vinc::{
    Admission, Builder, Connection, Direction, Discovery, Endpoint, Error, ErrorKind, Hosted, NodeAddr, NodeId,
    Records, Rendezvous, SendStream, Vinc, node_from_str, node_to_string,
};
use vinc::{RecvStream, read_tag};
use vinc_keystore::KeyStore;

const MUX: &[u8] = b"example/mux/1";
const MAX_MSG: usize = 16 << 20;
/// The length of `DefraDB`'s service-record pointer.
pub const POINTER_LEN: usize = 38;

/// Where `requester` hears the answers to what it published on the RPC topic `topic`.
pub fn response_topic(topic: &[u8], requester: &str) -> Vec<u8> {
    [topic, b"/", requester.as_bytes(), b"/_response"].concat()
}

/// The urgency of a stream by its tag: control first, block transfers last, everything else at the default.
pub fn urgency_of(tag: &[u8]) -> u8 {
    match tag {
        b"kms" | b"peerinfo" | b"replicator" => 0,
        b"car" | b"blocks" => 7,
        _ => vinc::DEFAULT_URGENCY,
    }
}

/// The seam: what the engine above needs from a backend.
pub trait Transport: Clone + 'static {
    /// The send half of a request's stream, used to reply on it.
    type ResponseToken: 'static;
    fn local_peer_id(&self) -> String;
    async fn sign(&self, data: &[u8]) -> Result<Vec<u8>, Error>;
    /// Dial `peer`; with no hints the peer is found through its published record.
    async fn dial(&self, peer: &str, hints: Vec<SocketAddr>) -> Result<(), Error>;
    async fn disconnect(&self, peer: &str) -> Result<(), Error>;
    async fn connected_peers(&self) -> Result<Vec<String>, Error>;
    async fn request(&self, peer: &str, tag: &[u8], body: Vec<u8>) -> Result<Vec<u8>, Error>;
    async fn next_request(&self) -> Option<Request<Self::ResponseToken>>;
    async fn respond(&self, token: Self::ResponseToken, body: Vec<u8>) -> Result<(), Error>;
    async fn shutdown(&self);
}

/// An inbound request.
pub struct Request<T> {
    pub peer: String,
    pub tag: Vec<u8>,
    pub body: Vec<u8>,
    pub token: T,
}

/// The access hook: everyone, or only the listed peers (`DefraDB`'s `AcceptAll` and `Explicit`).
#[derive(Clone, Default)]
pub struct Allowlist {
    only: Rc<RefCell<Option<HashSet<NodeId>>>>,
}

impl Allowlist {
    /// Admit only the peers `allow_peer` lists.
    pub fn explicit() -> Self {
        Self {
            only: Rc::new(RefCell::new(Some(HashSet::new()))),
        }
    }
}

impl Admission for Allowlist {
    fn admit(&self, peer: &NodeId, _alpn: &[u8], _dir: Direction) -> bool {
        self.only.borrow().as_ref().is_none_or(|l| l.contains(peer))
    }
}

/// The rendezvous: an in-process directory of signed records, which checks nothing (the endpoint verifies).
#[derive(Clone, Default)]
pub struct Directory(Rc<RefCell<HashMap<NodeId, Vec<u8>>>>);

impl Rendezvous for Directory {
    fn publish(&self, record: &[u8]) -> impl Future<Output = Result<(), Error>> {
        let stored = vinc_connect::record::Record::parse(record)
            .map(|r| {
                self.0.borrow_mut().insert(r.node, record.to_vec());
            })
            .map_err(|_| Error::new(ErrorKind::Config, "not a record"));
        std::future::ready(stored)
    }

    fn fetch(&self, node: &NodeId) -> impl Future<Output = Option<Vec<u8>>> {
        std::future::ready(self.0.borrow().get(node).cloned())
    }
}

/// The VINC backend.
pub struct VincTransport<H: Hosted> {
    ep: Endpoint<H, Records<Directory>>,
    allow: Allowlist,
    // One connection per peer for every protocol.
    conns: Rc<RefCell<HashMap<String, Connection<H>>>>,
    inbox: UnboundedSender<Request<SendStream<H>>>,
    requests: Rc<AsyncMutex<UnboundedReceiver<Request<SendStream<H>>>>>,
}

impl<H: Hosted> Clone for VincTransport<H> {
    fn clone(&self) -> Self {
        Self {
            ep: self.ep.clone(),
            allow: self.allow.clone(),
            conns: Rc::clone(&self.conns),
            inbox: self.inbox.clone(),
            requests: Rc::clone(&self.requests),
        }
    }
}

async fn write_msg<H: Hosted>(tx: &mut SendStream<H>, body: &[u8]) -> Result<(), Error> {
    tx.write_all(
        &u32::try_from(body.len())
            .map_err(|_| Error::new(ErrorKind::TooLarge, "message too large"))?
            .to_be_bytes(),
    )
    .await?;
    tx.write_all(body).await
}

async fn read_msg<H: Hosted>(rx: &mut RecvStream<H>) -> Result<Vec<u8>, Error> {
    let mut len = [0u8; 4];
    rx.read_exact(&mut len).await?;
    let len = u32::from_be_bytes(len) as usize;
    if len > MAX_MSG {
        return Err(Error::new(ErrorKind::TooLarge, "message too large"));
    }
    let mut body = vec![0u8; len];
    rx.read_exact(&mut body).await?;
    Ok(body)
}

impl<H: Hosted + 'static> VincTransport<H> {
    /// Start serving inbound streams of `ep`, and run it. `allow` must be the hook `ep` was built with.
    pub fn new(ep: Endpoint<H, Records<Directory>>, allow: Allowlist) -> Self {
        let runner = ep.clone();
        nuclei::spawn_local(async move {
            let _ = runner.run().await;
        })
        .detach();
        let (inbox, requests) = unbounded_channel();
        let t = Self {
            ep,
            allow,
            conns: Rc::default(),
            inbox,
            requests: Rc::new(AsyncMutex::new(requests)),
        };
        let me = t.clone();
        nuclei::spawn_local(async move {
            while let Some(inc) = me.ep.accept().await {
                let peer = node_to_string(&inc.remote());
                let conn = inc.into_connection();
                me.conns.borrow_mut().insert(peer.clone(), conn.clone());
                nuclei::spawn_local(serve(conn, peer, me.inbox.clone())).detach();
            }
        })
        .detach();
        t
    }

    /// The address to give peers.
    pub fn addr(&self) -> NodeAddr {
        self.ep.addr()
    }

    /// Join `topic`: its messages arrive through [`next_raw`](Self::next_raw).
    pub async fn subscribe_raw(&self, topic: &[u8]) -> Result<(), Error> {
        self.ep.join(topic, &[]).await.map(drop)
    }

    /// Publish `payload` to `topic`; with `wait`, only once a member of the topic this endpoint has a session with is
    /// known, or fail when the wait passes.
    pub async fn publish_raw(&self, topic: &[u8], payload: &[u8], wait: Option<Duration>) -> Result<(), Error> {
        self.ep.publish(topic, payload, wait).await.map(drop)
    }

    /// The next raw message: its topic, the peer that signed it and its bytes. `None` once the endpoint stopped.
    pub async fn next_raw(&self) -> Option<(Vec<u8>, String, Vec<u8>)> {
        loop {
            if let vinc::Event::Message {
                topic, origin, payload, ..
            } = self.ep.event().await?
            {
                return Some((topic, node_to_string(&origin), payload));
            }
        }
    }

    /// Join `topic` and answer every message on it with `handler`'s reply, published on the requester's response topic.
    /// The task this starts reads the endpoint's topic events from then on.
    pub async fn register_pubsub_rpc_topic(
        &self,
        topic: &[u8],
        handler: impl Fn(&[u8]) -> Vec<u8> + 'static,
    ) -> Result<(), Error> {
        self.subscribe_raw(topic).await?;
        let (me, topic) = (self.clone(), topic.to_vec());
        nuclei::spawn_local(async move {
            while let Some((on, from, body)) = me.next_raw().await {
                if on == topic {
                    let _ = me
                        .publish_raw(&response_topic(&topic, &from), &handler(&body), None)
                        .await;
                }
            }
        })
        .detach();
        Ok(())
    }

    fn conn(&self, peer: &str) -> Option<Connection<H>> {
        self.conns.borrow_mut().get(peer).cloned()
    }

    /// Let `peer` in: add it to an explicit allowlist and lift a revocation of it.
    pub fn allow_peer(&self, peer: &str) -> Result<(), Error> {
        let id = node_from_str(peer)?;
        if let Some(l) = self.allow.only.borrow_mut().as_mut() {
            l.insert(id);
        }
        self.ep.unrevoke(&id);
        Ok(())
    }

    /// Bar `peer` until `allow_peer` lets it in again: every session with it ends.
    pub async fn deny_peer(&self, peer: &str) -> Result<(), Error> {
        let id = node_from_str(peer)?;
        if let Some(l) = self.allow.only.borrow_mut().as_mut() {
            l.remove(&id);
        }
        self.ep.revoke(&id).await?;
        self.conns.borrow_mut().remove(peer);
        Ok(())
    }

    pub fn is_peer_revoked(&self, peer: &str) -> Result<bool, Error> {
        Ok(self.ep.is_revoked(&node_from_str(peer)?))
    }

    /// Put `DefraDB`'s service-record pointer in this node's record and publish it.
    pub async fn set_service_pointer(&self, pointer: &[u8; POINTER_LEN]) -> Result<(), Error> {
        self.ep.set_hints(pointer)?;
        self.ep.publish_record().await
    }

    /// The service-record pointer `peer` published, if it published one.
    pub async fn service_pointer(&self, peer: &str) -> Result<Option<Vec<u8>>, Error> {
        let rec = self.ep.lookup(&node_from_str(peer)?).await?;
        Ok(rec.map(|r| r.hints).filter(|h| h.len() == POINTER_LEN))
    }
}

async fn serve<H: Hosted>(conn: Connection<H>, peer: String, inbox: UnboundedSender<Request<SendStream<H>>>) {
    while let Ok((mut tx, mut rx)) = conn.accept_bi().await {
        let Ok(tag) = read_tag(&mut rx).await else { continue };
        let Ok(body) = read_msg(&mut rx).await else { continue };
        // The reply leaves at the class of its request.
        if tx.set_urgency(urgency_of(&tag)).await.is_err() {
            continue;
        }
        let _ = inbox.send(Request {
            peer: peer.clone(),
            tag,
            body,
            token: tx,
        });
    }
}

impl<H: Hosted + 'static> Transport for VincTransport<H> {
    type ResponseToken = SendStream<H>;

    fn local_peer_id(&self) -> String {
        node_to_string(&self.ep.id())
    }

    async fn sign(&self, data: &[u8]) -> Result<Vec<u8>, Error> {
        self.ep.sign(data).await
    }

    async fn dial(&self, peer: &str, hints: Vec<SocketAddr>) -> Result<(), Error> {
        if self.conn(peer).is_some_and(|c| c.close_reason().is_none()) {
            return Ok(());
        }
        let mut to = NodeAddr::new(node_from_str(peer)?);
        to.direct = hints;
        let conn = self.ep.connect(to, MUX).await?;
        self.conns.borrow_mut().insert(peer.to_owned(), conn);
        Ok(())
    }

    async fn disconnect(&self, peer: &str) -> Result<(), Error> {
        self.ep.close_peer(&node_from_str(peer)?).await;
        self.conns.borrow_mut().remove(peer);
        Ok(())
    }

    async fn connected_peers(&self) -> Result<Vec<String>, Error> {
        Ok(self.ep.peers().await?.iter().map(node_to_string).collect())
    }

    async fn request(&self, peer: &str, tag: &[u8], body: Vec<u8>) -> Result<Vec<u8>, Error> {
        let conn = self
            .conn(peer)
            .ok_or(Error::new(ErrorKind::Unreachable, "not connected"))?;
        let (mut tx, mut rx) = conn.open_bi_tagged(tag).await?;
        tx.set_urgency(urgency_of(tag)).await?;
        write_msg(&mut tx, &body).await?;
        tx.finish().await?;
        read_msg(&mut rx).await
    }

    async fn next_request(&self) -> Option<Request<SendStream<H>>> {
        self.requests.lock().await.recv().await
    }

    async fn respond(&self, mut token: SendStream<H>, body: Vec<u8>) -> Result<(), Error> {
        write_msg(&mut token, &body).await?;
        token.finish().await
    }

    async fn shutdown(&self) {
        self.ep.close().await;
    }
}

/// Two backends on loopback sharing a directory, and a third endpoint that is their hub. `b` publishes its service
/// pointer; `a` dials it by peer id alone, reads the pointer, sends a control request and a push, each answered on its
/// own stream, and asks for a key over raw pubsub, answered on its response topic; then `b` denies `a`, which loses its
/// connection at once and cannot come back. Returns the push's reply.
pub async fn run() -> Result<Vec<u8>, Error> {
    let lo: SocketAddr = ([127, 0, 0, 1], 0).into();
    let dir = Directory::default();
    // The hub: an endpoint like the others that also carries topics for those that name it as their relay.
    let hub = endpoint(Vinc::builder().seed(&[3; 32])?.alpn(MUX).hub(), lo).await?;
    let h = hub.clone();
    nuclei::spawn_local(async move {
        let _ = h.run().await;
    })
    .detach();
    let via = vinc::Relay::new(hub.id()).with_udp(hub.local_addr());
    let (aa, ba) = (Allowlist::default(), Allowlist::explicit());
    if let Some(l) = ba.only.borrow_mut().as_mut() {
        l.insert(hub.id());
    }
    let a = VincTransport::new(
        endpoint(
            Vinc::builder()
                .seed(&[1; 32])?
                .alpn(MUX)
                .relays([via])
                .discovery(Records::new(dir.clone()))
                .acp(aa.clone()),
            lo,
        )
        .await?,
        aa,
    );
    let b = VincTransport::new(
        endpoint(
            Vinc::builder()
                .seed(&[2; 32])?
                .alpn(MUX)
                .relays([via])
                .discovery(Records::new(dir.clone()))
                .acp(ba.clone()),
            lo,
        )
        .await?,
        ba,
    );
    let b2 = b.clone();
    nuclei::spawn_local(async move {
        while let Some(req) = b2.next_request().await {
            let mut reply = req.tag.clone();
            reply.extend_from_slice(b"/");
            reply.extend_from_slice(&req.body);
            let _ = b2.respond(req.token, reply).await;
        }
    })
    .detach();

    let pointer: [u8; POINTER_LEN] = *b"defra/service-records/1:0123456789abcd";
    b.set_service_pointer(&pointer).await?;
    b.allow_peer(&a.local_peer_id())?;
    a.dial(&b.local_peer_id(), Vec::new()).await?;
    assert!(a.connected_peers().await?.contains(&b.local_peer_id()));
    assert_eq!(
        a.service_pointer(&b.local_peer_id()).await?.as_deref(),
        Some(&pointer[..])
    );
    let sig = a.sign(b"message").await?;
    assert_eq!(sig.len(), 64);

    assert_eq!(
        a.request(&b.local_peer_id(), b"kms", b"key?".to_vec()).await?,
        b"kms/key?"
    );
    let reply = a.request(&b.local_peer_id(), b"pushlog", b"payload".to_vec()).await?;

    // Raw pubsub the way the KMS asks for keys: `b` answers every request on the requester's response topic.
    let kms = b"encryption".to_vec();
    let answers = response_topic(&kms, &a.local_peer_id());
    b.register_pubsub_rpc_topic(&kms, |doc| [b"key for ", doc].concat())
        .await?;
    a.subscribe_raw(&answers).await?;
    // A subscription takes a moment to reach the hub: ask until the answer comes.
    let mut answer = None;
    for _ in 0..100 {
        a.publish_raw(&kms, b"doc-1", None).await?;
        if let Ok(Some(m)) = nuclei::time::timeout(Duration::from_millis(300), a.next_raw()).await {
            answer = Some(m);
            break;
        }
    }
    assert_eq!(
        answer,
        Some((answers, b.local_peer_id(), b"key for doc-1".to_vec())),
        "no answer on the response topic"
    );

    b.deny_peer(&a.local_peer_id()).await?;
    assert!(b.is_peer_revoked(&a.local_peer_id())?);
    assert!(!b.connected_peers().await?.contains(&a.local_peer_id()));
    assert!(
        a.request(&b.local_peer_id(), b"pushlog", b"again".to_vec())
            .await
            .is_err()
    );

    a.shutdown().await;
    b.shutdown().await;
    hub.close().await;
    Ok(reply)
}

/// An endpoint over a UDP socket of the nuclei runtime bound to `bind`: the three closures are the whole of the host's I/O.
async fn endpoint<S: KeyStore + 'static, D: Discovery + 'static, A: Admission + 'static>(
    builder: Builder<S, D, A>,
    bind: SocketAddr,
) -> Result<Endpoint<impl Hosted<Access = A>, D>, Error> {
    let sock = Arc::new(
        Handle::<UdpSocket>::bind(bind)
            .await
            .map_err(|_| Error::new(ErrorKind::Unreachable, "the address cannot be bound"))?,
    );
    let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
    let local = sock
        .local_addr()
        .map_err(|_| Error::new(ErrorKind::Unreachable, "the socket has no address"))?;
    builder.local_addr(local).build(
        async move |buf: &mut [u8]| r.recv_from(buf).await,
        async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
        async |at: Instant| sleep_until_precise(at).await,
    )
}

#[allow(dead_code)]
#[nuclei::main]
async fn main() {
    match run().await {
        Ok(r) => println!("reply: {}", String::from_utf8_lossy(&r)),
        Err(e) => eprintln!("failed: {e}"),
    }
}
