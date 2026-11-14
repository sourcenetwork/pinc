//! The port mapping on the facade: an endpoint sends nothing for it unless the builder turns it on, nothing on a
//! loopback address or in the relay role, only the search when it knows no gateway, asks the gateway it was given, reads
//! the grant back and releases the mapping when it closes.
//!
//! The host is a pair of in-memory queues: a send is logged, and the test hands the endpoint the gateway's answers.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::type_complexity,
    clippy::too_many_lines
)]

use std::cell::RefCell;
use std::net::{IpAddr, SocketAddr};
use std::rc::Rc;
use std::time::{Duration, Instant};

use smol::channel::{Sender, unbounded};
use vinc::relay::{CarrierFns, Peer, Relay as RelayHost};
use vinc::{CarrierKind, Endpoint, Error, ErrorKind, Hosted, Vinc};
use vinc_portmap::{pcp, upnp};

const ALPN: &[u8] = b"portmap/test";
const PRIVATE: &str = "192.168.1.5:4433";
const GATEWAY: &str = "192.168.1.1";

/// Everything the endpoint sent: where to, and the bytes.
type Log = Rc<RefCell<Vec<(SocketAddr, Vec<u8>)>>>;

fn addr(s: &str) -> SocketAddr {
    s.parse().unwrap()
}

fn gateway() -> SocketAddr {
    SocketAddr::new(GATEWAY.parse().unwrap(), 5351)
}

/// An endpoint on `local`, with port mapping `on` (the builder's default when `None`) and the gateway `gw`, on a host
/// that logs what is sent and hands over what `inbox` is given.
fn bind(
    local: &str,
    on: Option<bool>,
    gw: Option<&str>,
) -> (Endpoint<impl Hosted>, Log, Sender<(Vec<u8>, SocketAddr)>) {
    let (tx, rx) = unbounded::<(Vec<u8>, SocketAddr)>();
    let log: Log = Rc::default();
    let sent = Rc::clone(&log);
    let mut b = Vinc::builder().alpn(ALPN).local_addr(addr(local));
    if let Some(on) = on {
        b = b.port_mapping(on);
    }
    if let Some(gw) = gw {
        b = b.gateway(gw.parse::<IpAddr>().unwrap());
    }
    let ep = b
        .build(
            async move |buf: &mut [u8]| {
                let (d, from) = rx.recv().await.map_err(|_| std::io::ErrorKind::BrokenPipe)?;
                buf[..d.len()].copy_from_slice(&d);
                Ok((d.len(), from))
            },
            async move |pkt: &[u8], to: SocketAddr| {
                sent.borrow_mut().push((to, pkt.to_vec()));
                Ok(pkt.len())
            },
            async |at: Instant| tokio::time::sleep_until(tokio::time::Instant::from_std(at)).await,
        )
        .unwrap();
    (ep, log, tx)
}

/// Let the endpoint run for `d`.
async fn run_for<H: Hosted>(ep: &Endpoint<H>, d: Duration) {
    let _ = tokio::time::timeout(d, ep.accept()).await;
}

/// Run the endpoint until `cond` holds, backing off from 1 ms to 50 ms, for at most five seconds.
async fn until<H: Hosted>(ep: &Endpoint<H>, mut cond: impl FnMut() -> bool) -> bool {
    let end = Instant::now() + Duration::from_secs(5);
    let mut step = Duration::from_millis(1);
    while !cond() && Instant::now() < end {
        run_for(ep, step).await;
        step = (step * 2).min(Duration::from_millis(50));
    }
    cond()
}

/// The window an endpoint that must send nothing is watched for.
const QUIET: Duration = Duration::from_millis(300);

#[tokio::test(flavor = "current_thread")]
async fn by_default_an_endpoint_sends_nothing_for_port_mapping() {
    let (ep, log, _tx) = bind(PRIVATE, None, Some(GATEWAY));
    run_for(&ep, QUIET).await;
    assert_eq!(*log.borrow(), vec![], "the default sent something");
    assert_eq!(ep.port_mapping().await, None);
}

#[tokio::test(flavor = "current_thread")]
async fn with_it_off_an_endpoint_sends_nothing() {
    let (ep, log, _tx) = bind(PRIVATE, Some(false), Some(GATEWAY));
    run_for(&ep, QUIET).await;
    assert_eq!(*log.borrow(), vec![]);
}

#[tokio::test(flavor = "current_thread")]
async fn on_a_loopback_address_nothing_is_sent() {
    let (ep, log, _tx) = bind("127.0.0.1:4433", Some(true), Some(GATEWAY));
    run_for(&ep, QUIET).await;
    assert_eq!(*log.borrow(), vec![]);
}

#[tokio::test(flavor = "current_thread")]
async fn on_a_public_address_with_no_gateway_nothing_is_sent() {
    let (ep, log, _tx) = bind("203.0.113.50:4433", Some(true), None);
    run_for(&ep, QUIET).await;
    assert_eq!(*log.borrow(), vec![]);
}

#[tokio::test(flavor = "current_thread")]
async fn on_a_private_address_with_no_gateway_only_the_search_is_sent() {
    let (ep, log, _tx) = bind(PRIVATE, Some(true), None);
    assert!(until(&ep, || !log.borrow().is_empty()).await, "no search left");
    run_for(&ep, QUIET).await;
    let log = log.borrow();
    assert!(
        log.iter().all(|(to, b)| *to == upnp::SSDP && b == upnp::M_SEARCH),
        "something but the search left: {:?}",
        log.iter().map(|(to, b)| (*to, b.len())).collect::<Vec<_>>()
    );
}

#[tokio::test(flavor = "current_thread")]
async fn the_gateway_is_asked_for_a_mapping_of_the_socket_and_the_grant_is_read_back() {
    let (ep, log, tx) = bind(PRIVATE, Some(true), Some(GATEWAY));
    assert!(until(&ep, || !log.borrow().is_empty()).await, "nothing asked");
    let (to, bytes) = log.borrow()[0].clone();
    assert_eq!(to, gateway());
    let req = pcp::decode_request(&bytes).unwrap();
    assert_eq!((req.client, req.internal_port), (addr(PRIVATE).ip(), 4433));
    let grant = pcp::Response::Map {
        result: pcp::SUCCESS,
        lifetime: 7200,
        epoch: 1,
        nonce: req.nonce,
        protocol: pcp::UDP,
        internal_port: 4433,
        external_port: 4433,
        external_ip: "203.0.113.9".parse().unwrap(),
    };
    let mut b = [0u8; 60];
    let n = pcp::encode_response(&grant, &mut b).unwrap();
    tx.try_send((b[..n].to_vec(), gateway())).unwrap();
    let mut held = None;
    let end = Instant::now() + Duration::from_secs(5);
    while held.is_none() && Instant::now() < end {
        held = ep.port_mapping().await;
        run_for(&ep, Duration::from_millis(5)).await;
    }
    assert_eq!(held, Some(addr("203.0.113.9:4433")));
    // closing releases it: the gateway is asked for a mapping of lifetime zero
    let before = log.borrow().len();
    ep.close().await;
    let log = log.borrow();
    let release = log[before..]
        .iter()
        .find(|(to, _)| *to == gateway())
        .map(|(_, b)| pcp::decode_request(b).unwrap());
    assert_eq!(
        release.map(|r| (r.lifetime, r.nonce)),
        Some((0, req.nonce)),
        "no release left on close"
    );
}

/// The relay role is a server: it never asks a gateway for a mapping, even with the builder turned on.
#[tokio::test(flavor = "current_thread")]
async fn an_endpoint_with_the_relay_role_sends_nothing_for_port_mapping() {
    struct Pipe;
    let carriers = CarrierFns::new(
        async || -> vinc::Result<(Pipe, CarrierKind)> { std::future::pending().await },
        async |_peer: &Peer, _kind: CarrierKind| -> vinc::Result<Pipe> {
            Err(Error::new(ErrorKind::Unreachable, "the relay has no peers"))
        },
        async |_p: &Pipe, buf: Vec<u8>| (Ok(0), buf),
        async |_p: &Pipe, buf: Vec<u8>, _from: usize| (Ok(0), buf),
        async |_p: Pipe| {},
    );
    let (_tx, rx) = unbounded::<(Vec<u8>, SocketAddr)>();
    let log: Log = Rc::default();
    let sent = Rc::clone(&log);
    let ep = Vinc::builder()
        .local_addr(addr(PRIVATE))
        .port_mapping(true)
        .gateway(GATEWAY.parse().unwrap())
        .relay_role(RelayHost::builder(), carriers)
        .build(
            async move |buf: &mut [u8]| {
                let (d, from) = rx.recv().await.map_err(|_| std::io::ErrorKind::BrokenPipe)?;
                buf[..d.len()].copy_from_slice(&d);
                Ok((d.len(), from))
            },
            async move |pkt: &[u8], to: SocketAddr| {
                sent.borrow_mut().push((to, pkt.to_vec()));
                Ok(pkt.len())
            },
            async |at: Instant| tokio::time::sleep_until(tokio::time::Instant::from_std(at)).await,
        )
        .unwrap();
    let _ = tokio::time::timeout(QUIET, ep.run()).await;
    let asked: Vec<_> = log
        .borrow()
        .iter()
        .filter(|(to, _)| *to == gateway() || *to == upnp::SSDP)
        .map(|(to, _)| *to)
        .collect();
    assert_eq!(asked, vec![], "the relay role asked about a mapping");
}
