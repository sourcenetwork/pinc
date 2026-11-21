//! Discovery by signed records through the facade: a dial by node id alone succeeds once the peer published, fails
//! inside the deadline when it has not or the store is silent, refuses a forged record before any packet is sent,
//! and pays one failed handshake for a stale one; 38 bytes of hints round-trip through a lookup. The store is an
//! in-process table that verifies nothing, so every check is the endpoint's. On nuclei.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod pinc_common;

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::net::{SocketAddr, UdpSocket};
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use nuclei::Handle;
use pinc::{Builder, Discovery, Endpoint, ErrorKind, Hosted, LOOKUP_WAIT, MAX_HINTS, NodeId, Records, Rendezvous};
use pinc_common::{ECHO, bind, builder, lo, serve_conn, within};
use pinc_connect::record::{Reach, Record};
use pinc_keystore::KeyStore;

/// The pointer `DefraDB` keeps in its discovery record: 38 bytes.
const POINTER: [u8; 38] = *b"defra/service-records/1:0123456789abcd";

/// A rendezvous that keeps whatever it is given, by the node the bytes name, and checks nothing.
#[derive(Clone, Default)]
struct Table {
    held: Rc<RefCell<HashMap<NodeId, Vec<u8>>>>,
    silent: Rc<Cell<bool>>,
}

impl Rendezvous for Table {
    fn publish(&self, record: &[u8]) -> impl std::future::Future<Output = pinc::Result<()>> {
        let node = Record::parse(record).unwrap().node;
        self.held.borrow_mut().insert(node, record.to_vec());
        std::future::ready(Ok(()))
    }

    async fn fetch(&self, node: &NodeId) -> Option<Vec<u8>> {
        if self.silent.get() {
            std::future::pending::<()>().await;
        }
        self.held.borrow().get(node).cloned()
    }
}

/// A peer serving the echo protocol, discovering over `table`.
async fn peer(table: &Table) -> Endpoint<impl Hosted, Records<Table>> {
    let ep = bind(builder().alpn(ECHO).discovery(Records::new(table.clone()))).await;
    let s = ep.clone();
    nuclei::spawn_local(async move {
        while let Some(i) = s.accept().await {
            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();
    ep
}

#[nuclei::test]
async fn the_signed_record_still_verifies_beside_the_sign_guard() {
    let ep = bind(builder().discovery(Records::new(Table::default()))).await;
    let rec = within(30, ep.signed_record()).await.unwrap();
    assert_eq!(Record::parse_verified(&rec).unwrap().reach, Reach::Public);
    // A real record's bytes are the protocol's own statement: the public sign refuses them.
    let e = within(30, ep.sign(&rec)).await.unwrap_err();
    assert_eq!(e.kind(), pinc::ErrorKind::Config);
}

async fn echo<H: Hosted>(c: &pinc::Connection<H>) -> Vec<u8> {
    let (mut tx, mut rx) = c.open_bi().await.unwrap();
    tx.write_all(b"found").await.unwrap();
    tx.finish().await.unwrap();
    rx.read_to_end(16).await.unwrap()
}

#[nuclei::test]
async fn a_dial_by_node_id_succeeds_once_the_peer_published_and_its_hints_round_trip() {
    let table = Table::default();
    let server = peer(&table).await;
    let client = bind(builder().alpn(ECHO).discovery(Records::new(table.clone()))).await;
    within(60, async {
        // Not published: the dial fails at once, well inside the deadline, and the lookup finds nothing.
        let t = Instant::now();
        assert_eq!(
            client.connect(server.id(), ECHO).await.unwrap_err().kind(),
            ErrorKind::Unreachable
        );
        assert!(t.elapsed() < LOOKUP_WAIT, "{:?}", t.elapsed());
        assert_eq!(client.lookup(&server.id()).await.unwrap(), None);

        server.set_hints(&POINTER).unwrap();
        server.publish_record().await.unwrap();

        let c = client.connect(server.id(), ECHO).await.unwrap();
        assert_eq!(c.remote(), server.id());
        assert_eq!(echo(&c).await, b"found");
        let rec = client.lookup(&server.id()).await.unwrap().unwrap();
        assert_eq!(rec.node, server.id());
        assert_eq!(rec.hints, POINTER);
        assert_eq!(rec.addrs, server.addr().direct);
    })
    .await;
}

#[nuclei::test]
async fn hints_are_bounded_and_a_republish_replaces_them() {
    let table = Table::default();
    let server = peer(&table).await;
    let client = bind(builder().discovery(Records::new(table.clone()))).await;
    within(60, async {
        assert_eq!(
            server.set_hints(&[7; MAX_HINTS + 1]).unwrap_err().kind(),
            ErrorKind::TooLarge
        );
        server.set_hints(&[7; MAX_HINTS]).unwrap();
        server.publish_record().await.unwrap();
        let old = table.held.borrow()[&server.id()].clone();
        assert_eq!(
            client.lookup(&server.id()).await.unwrap().unwrap().hints,
            [7; MAX_HINTS]
        );

        server.set_hints(b"v2").unwrap();
        server.publish_record().await.unwrap();
        let new = client.lookup(&server.id()).await.unwrap().unwrap();
        assert_eq!(new.hints, b"v2");

        // A store that hands back the older record does not roll the client back.
        table.held.borrow_mut().insert(server.id(), old);
        let again = client.lookup(&server.id()).await.unwrap().unwrap();
        assert_eq!(again, new);
    })
    .await;
}

#[nuclei::test]
async fn a_silent_rendezvous_fails_the_dial_inside_the_deadline() {
    let table = Table::default();
    let server = peer(&table).await;
    server.publish_record().await.unwrap();
    table.silent.set(true);
    let client = bind(builder().alpn(ECHO).discovery(Records::new(table.clone()))).await;
    within(60, async {
        let t = Instant::now();
        assert_eq!(
            client.connect(server.id(), ECHO).await.unwrap_err().kind(),
            ErrorKind::TimedOut
        );
        let took = t.elapsed();
        assert!(
            took >= LOOKUP_WAIT && took < LOOKUP_WAIT + Duration::from_secs(2),
            "{took:?}"
        );
        assert_eq!(
            client.lookup(&server.id()).await.unwrap_err().kind(),
            ErrorKind::TimedOut
        );
    })
    .await;
}

/// An endpoint serving the echo protocol on a loopback socket bound to `at`, counting the datagrams that reach it and
/// raising `incoming` when a session is accepted. `None` if the address cannot be bound (yet).
async fn counted<S: KeyStore + 'static, D: Discovery + 'static>(
    b: Builder<S, D>,
    at: SocketAddr,
    incoming: Arc<AtomicBool>,
) -> Option<(Endpoint<impl Hosted, D>, Arc<AtomicUsize>)> {
    let sock = Arc::new(Handle::<UdpSocket>::bind(at).await.ok()?);
    let n = Arc::new(AtomicUsize::new(0));
    let (r, s, k) = (Arc::clone(&sock), Arc::clone(&sock), Arc::clone(&n));
    let ep = b
        .alpn(ECHO)
        .local_addr(sock.local_addr().unwrap())
        .build(
            async move |buf: &mut [u8]| {
                let got = r.recv_from(buf).await;
                k.fetch_add(1, Ordering::SeqCst);
                got
            },
            async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
            async |at: Instant| nuclei::time::sleep_until_precise(at).await,
        )
        .unwrap();
    let (e, a) = (ep.clone(), ep.clone());
    nuclei::spawn_local(async move {
        let _ = e.run().await;
    })
    .detach();
    nuclei::spawn_local(async move {
        while let Some(i) = a.accept().await {
            incoming.store(true, Ordering::SeqCst);
            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();
    Some((ep, n))
}

#[nuclei::test]
async fn a_forged_record_is_refused_before_any_packet_and_a_stale_one_costs_one_failed_handshake() {
    let table = Table::default();
    let client = bind(builder().alpn(ECHO).discovery(Records::new(table.clone()))).await;
    within(120, async {
        let seen = Arc::new(AtomicBool::new(false));
        let (real, hits) = counted(
            builder()
                .seed(&[41; 32])
                .unwrap()
                .discovery(Records::new(table.clone())),
            lo(),
            Arc::clone(&seen),
        )
        .await
        .unwrap();
        let (id, at) = (real.id(), real.addr().direct[0]);
        real.publish_record().await.unwrap();
        let genuine = table.held.borrow()[&id].clone();
        let other = bind(
            builder()
                .seed(&[42; 32])
                .unwrap()
                .discovery(Records::new(table.clone())),
        )
        .await;
        other.publish_record().await.unwrap();
        let foreign = table.held.borrow()[&other.id()].clone();

        // A record whose signature is broken: refused, and nothing reaches the address it names.
        let mut broken = genuine.clone();
        let last = broken.len() - 1;
        broken[last] ^= 1;
        table.held.borrow_mut().insert(id, broken);
        let before = hits.load(Ordering::SeqCst);
        assert_eq!(client.lookup(&id).await.unwrap(), None);
        assert_eq!(
            client.connect(id, ECHO).await.unwrap_err().kind(),
            ErrorKind::Unreachable
        );

        // Another node's valid record filed under this id: refused the same way.
        table.held.borrow_mut().insert(id, foreign);
        assert_eq!(client.lookup(&id).await.unwrap(), None);
        assert_eq!(
            client.connect(id, ECHO).await.unwrap_err().kind(),
            ErrorKind::Unreachable
        );
        assert_eq!(hits.load(Ordering::SeqCst), before, "a refused record led to a packet");

        // A stale record: the real node is gone and an impostor holds its address. The record verifies, so the
        // client dials; the handshake authenticates the node id, so the impostor's Reply is dropped, the one dial
        // fails at its connect timeout and nothing is accepted.
        table.held.borrow_mut().insert(id, genuine);
        real.close().await;
        drop(real);
        let fooled = Arc::new(AtomicBool::new(false));
        let mut impostor = None;
        for _ in 0..200 {
            impostor = counted(builder().seed(&[43; 32]).unwrap(), at, Arc::clone(&fooled)).await;
            if impostor.is_some() {
                break;
            }
            nuclei::time::sleep(Duration::from_millis(10)).await;
        }
        let (impostor, reached) = impostor.expect("the address was never free again");
        assert_ne!(impostor.id(), id);
        let t = Instant::now();
        let err = client.connect(id, ECHO).await.unwrap_err();
        assert!(
            matches!(err.kind(), ErrorKind::Unreachable | ErrorKind::TimedOut),
            "{err:?}"
        );
        assert!(
            reached.load(Ordering::SeqCst) > 0,
            "the dial never reached the stale address"
        );
        assert!(
            !fooled.load(Ordering::SeqCst),
            "the impostor accepted a session meant for another node"
        );
        assert!(!client.peers().await.unwrap().contains(&impostor.id()));
        assert!(t.elapsed() < Duration::from_secs(30), "{:?}", t.elapsed());
        assert!(!seen.load(Ordering::SeqCst));
    })
    .await;
}
