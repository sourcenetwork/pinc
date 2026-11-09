//! The sketch of a VINC backend for a peer-to-peer transport trait shaped like DefraDB.rs's `P2PTransport`, with no
//! dependency on it.
//!
//! The trait below keeps the shape that matters: a cloneable handle, a text peer id equal to the hex of the public key,
//! `sign`, `dial` with address hints, `disconnect`, `connected_peers`, a request that returns its reply, an inbound
//! request that carries a response token (the send half of the request's own stream), and `shutdown`. Protocols are
//! per-stream tags on one connection per peer, so a failure on one stream never closes the connection.
//!
//! Run with `cargo run -p vinc --features nuclei --example defradb_backend`.

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

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::{Arc, Mutex};

use nuclei::sync::Mutex as AsyncMutex;
use nuclei::sync::mpsc::{UnboundedReceiver, UnboundedSender, unbounded_channel};
use vinc::{Connection, Endpoint, Error, ErrorKind, NodeAddr, SendStream, Vinc, node_from_str, node_to_string};
use vinc::{RecvStream, read_tag};

const MUX: &[u8] = b"example/mux/1";
const MAX_MSG: usize = 16 << 20;

/// The seam: what the engine above needs from a backend.
pub trait Transport: Clone + Send + Sync + 'static {
    /// The send half of a request's stream, used to reply on it.
    type ResponseToken: Send + 'static;
    fn local_peer_id(&self) -> String;
    async fn sign(&self, data: &[u8]) -> Result<Vec<u8>, Error>;
    async fn dial(&self, peer: &str, hints: Vec<SocketAddr>) -> Result<(), Error>;
    fn disconnect(&self, peer: &str) -> Result<(), Error>;
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

/// The VINC backend.
#[derive(Clone)]
pub struct VincTransport {
    ep: Endpoint,
    // One connection per peer for every protocol.
    conns: Arc<Mutex<HashMap<String, Connection>>>,
    inbox: UnboundedSender<Request<SendStream>>,
    requests: Arc<AsyncMutex<UnboundedReceiver<Request<SendStream>>>>,
}

async fn write_msg(tx: &mut SendStream, body: &[u8]) -> Result<(), Error> {
    tx.write_all(
        &u32::try_from(body.len())
            .map_err(|_| Error::new(ErrorKind::TooLarge, "message too large"))?
            .to_be_bytes(),
    )
    .await?;
    tx.write_all(body).await
}

async fn read_msg(rx: &mut RecvStream) -> Result<Vec<u8>, Error> {
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

impl VincTransport {
    /// Bind an endpoint with the given 32-byte seed, spawn its driver and start serving inbound streams.
    pub async fn start(seed: &[u8; 32], bind: SocketAddr) -> Result<Self, Error> {
        let (ep, driver) = Vinc::builder().seed(seed)?.alpn(MUX).bind_nuclei(bind).await?;
        nuclei::spawn(driver.run()).detach();
        let (inbox, requests) = unbounded_channel();
        let t = Self {
            ep: ep.clone(),
            conns: Arc::default(),
            inbox,
            requests: Arc::new(AsyncMutex::new(requests)),
        };
        let me = t.clone();
        nuclei::spawn(async move {
            while let Some(inc) = me.ep.accept().await {
                let peer = node_to_string(&inc.remote());
                let conn = inc.into_connection();
                me.conns
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .insert(peer.clone(), conn.clone());
                nuclei::spawn(serve(conn, peer, me.inbox.clone())).detach();
            }
        })
        .detach();
        Ok(t)
    }

    /// The address to give peers.
    pub fn addr(&self) -> NodeAddr {
        self.ep.addr()
    }

    fn conn(&self, peer: &str) -> Option<Connection> {
        self.conns
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get(peer)
            .cloned()
    }
}

async fn serve(conn: Connection, peer: String, inbox: UnboundedSender<Request<SendStream>>) {
    while let Ok((tx, mut rx)) = conn.accept_bi().await {
        let Ok(tag) = read_tag(&mut rx).await else { continue };
        let Ok(body) = read_msg(&mut rx).await else { continue };
        let _ = inbox.send(Request {
            peer: peer.clone(),
            tag,
            body,
            token: tx,
        });
    }
}

impl Transport for VincTransport {
    type ResponseToken = SendStream;

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
        self.conns
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(peer.to_owned(), conn);
        Ok(())
    }

    fn disconnect(&self, peer: &str) -> Result<(), Error> {
        self.ep.close_peer(&node_from_str(peer)?);
        self.conns
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(peer);
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
        write_msg(&mut tx, &body).await?;
        tx.finish().await?;
        read_msg(&mut rx).await
    }

    async fn next_request(&self) -> Option<Request<SendStream>> {
        self.requests.lock().await.recv().await
    }

    async fn respond(&self, mut token: SendStream, body: Vec<u8>) -> Result<(), Error> {
        write_msg(&mut token, &body).await?;
        token.finish().await
    }

    async fn shutdown(&self) {
        self.ep.close().await;
    }
}

/// Two backends on loopback: one asks, the other answers on the request's own stream. Returns the reply.
pub async fn run() -> Result<Vec<u8>, Error> {
    let lo: SocketAddr = ([127, 0, 0, 1], 0).into();
    let a = VincTransport::start(&[1; 32], lo).await?;
    let b = VincTransport::start(&[2; 32], lo).await?;
    let b2 = b.clone();
    nuclei::spawn(async move {
        while let Some(req) = b2.next_request().await {
            let mut reply = req.tag.clone();
            reply.extend_from_slice(b"/");
            reply.extend_from_slice(&req.body);
            let _ = b2.respond(req.token, reply).await;
        }
    })
    .detach();
    a.dial(&b.local_peer_id(), b.addr().direct).await?;
    assert!(a.connected_peers().await?.contains(&b.local_peer_id()));
    let sig = a.sign(b"message").await?;
    assert_eq!(sig.len(), 64);
    let reply = a.request(&b.local_peer_id(), b"pushlog", b"payload".to_vec()).await?;
    a.shutdown().await;
    Ok(reply)
}

#[allow(dead_code)]
#[nuclei::main]
async fn main() {
    match run().await {
        Ok(r) => println!("reply: {}", String::from_utf8_lossy(&r)),
        Err(e) => eprintln!("failed: {e}"),
    }
}
