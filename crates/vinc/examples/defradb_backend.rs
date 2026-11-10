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

use std::cell::RefCell;
use std::collections::HashMap;
use std::net::{SocketAddr, UdpSocket};
use std::rc::Rc;
use std::sync::Arc;
use std::time::Instant;

use nuclei::Handle;
use nuclei::sync::Mutex as AsyncMutex;
use nuclei::sync::mpsc::{UnboundedReceiver, UnboundedSender, unbounded_channel};
use nuclei::time::sleep_until_precise;
use vinc::{
    Builder, Connection, Endpoint, Error, ErrorKind, Hosted, NodeAddr, SendStream, Vinc, node_from_str, node_to_string,
};
use vinc::{RecvStream, read_tag};

const MUX: &[u8] = b"example/mux/1";
const MAX_MSG: usize = 16 << 20;

/// The seam: what the engine above needs from a backend.
pub trait Transport: Clone + 'static {
    /// The send half of a request's stream, used to reply on it.
    type ResponseToken: 'static;
    fn local_peer_id(&self) -> String;
    async fn sign(&self, data: &[u8]) -> Result<Vec<u8>, Error>;
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

/// The VINC backend.
pub struct VincTransport<H: Hosted> {
    ep: Endpoint<H>,
    // One connection per peer for every protocol.
    conns: Rc<RefCell<HashMap<String, Connection<H>>>>,
    inbox: UnboundedSender<Request<SendStream<H>>>,
    requests: Rc<AsyncMutex<UnboundedReceiver<Request<SendStream<H>>>>>,
}

impl<H: Hosted> Clone for VincTransport<H> {
    fn clone(&self) -> Self {
        Self {
            ep: self.ep.clone(),
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
    /// Start serving inbound streams of `ep`, and run it.
    pub fn new(ep: Endpoint<H>) -> Self {
        let runner = ep.clone();
        nuclei::spawn_local(async move {
            let _ = runner.run().await;
        })
        .detach();
        let (inbox, requests) = unbounded_channel();
        let t = Self {
            ep,
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

    fn conn(&self, peer: &str) -> Option<Connection<H>> {
        self.conns.borrow_mut().get(peer).cloned()
    }
}

async fn serve<H: Hosted>(conn: Connection<H>, peer: String, inbox: UnboundedSender<Request<SendStream<H>>>) {
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

/// Two backends on loopback: one asks, the other answers on the request's own stream. Returns the reply.
pub async fn run() -> Result<Vec<u8>, Error> {
    let lo: SocketAddr = ([127, 0, 0, 1], 0).into();
    let a = VincTransport::new(endpoint(Vinc::builder().seed(&[1; 32])?.alpn(MUX), lo).await?);
    let b = VincTransport::new(endpoint(Vinc::builder().seed(&[2; 32])?.alpn(MUX), lo).await?);
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
    a.dial(&b.local_peer_id(), b.addr().direct).await?;
    assert!(a.connected_peers().await?.contains(&b.local_peer_id()));
    let sig = a.sign(b"message").await?;
    assert_eq!(sig.len(), 64);
    let reply = a.request(&b.local_peer_id(), b"pushlog", b"payload".to_vec()).await?;
    a.shutdown().await;
    Ok(reply)
}

/// An endpoint over a UDP socket of the nuclei runtime bound to `bind`: the three closures are the whole of the host's I/O.
async fn endpoint(builder: Builder, bind: SocketAddr) -> Result<Endpoint<impl Hosted>, Error> {
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
