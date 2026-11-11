//! Endpoints that know only a relay reach each other through the real relay host on loopback sockets, then move to a
//! direct path and live on when the relay stops.
//!
//! The carriers are TCP streams the test hosts open and accept. A WebSocket carrier needs no HTTP upgrade here: the
//! facade frames the WebSocket itself and the relay host decodes it (`CarrierKind::Ws`), and for the carrier of a
//! browser (`CarrierKind::WsMessages`) the test hosts delimit the messages with a length, as a WebSocket library
//! would. A byte at the start of a stream tells the accepting host which kind it is, standing in for the path of the
//! upgrade request.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::large_futures,
    clippy::too_many_lines,
    missing_docs
)]

mod relay_members;
mod vinc_common;

use std::cell::RefCell;
use std::io;
use std::net::{SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::rc::Rc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use nuclei::Handle;
use relay_members::{Member, on_big_stack};
use vinc::relay::{Carriers, Clock, Limits, MemStore, Peer, Relay as RelayHost, Stats, Udp};
use vinc::{CarrierKind, Error, ErrorKind, Identity, Relay};
use vinc_common::{ECHO, SINK, eventually, lo, serve_conn, within};
use vinc_connect::carrier::session::ALPN;
use vinc_connect::relay::Quota;

fn failed(_: io::Error) -> Error {
    Error::new(ErrorKind::Unreachable, "the socket failed")
}

fn wall_ns() -> u64 {
    u64::try_from(SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()).unwrap()
}

/// The marker byte of a kind, and the kind of a marker byte.
const fn marker(kind: CarrierKind) -> u8 {
    match kind {
        CarrierKind::Tcp => 0,
        CarrierKind::Ws => 1,
        CarrierKind::WsMessages => 2,
    }
}

const fn kind_of(marker: u8) -> CarrierKind {
    match marker {
        1 => CarrierKind::Ws,
        2 => CarrierKind::WsMessages,
        _ => CarrierKind::Tcp,
    }
}

/// A stream of the test hosts: a TCP stream, with whole messages delimited by a length for `WsMessages`.
struct Wire {
    tcp: Handle<TcpStream>,
    messages: bool,
    rest: RefCell<Vec<u8>>,
}

impl Wire {
    fn new(tcp: Handle<TcpStream>, kind: CarrierKind) -> Self {
        Self {
            tcp,
            messages: kind == CarrierKind::WsMessages,
            rest: RefCell::new(Vec::new()),
        }
    }

    async fn read_exact(&self, buf: &mut [u8]) -> io::Result<bool> {
        let mut got = 0;
        while got < buf.len() {
            let n = self.tcp.recv(&mut buf[got..]).await?;
            if n == 0 {
                return Ok(false);
            }
            got += n;
        }
        Ok(true)
    }

    async fn write_all(&self, bytes: &[u8]) -> io::Result<()> {
        let mut sent = 0;
        while sent < bytes.len() {
            sent += self.tcp.send(&bytes[sent..]).await?;
        }
        Ok(())
    }

    async fn read(&self, mut buf: Vec<u8>) -> (io::Result<usize>, Vec<u8>) {
        if !self.messages {
            let r = self.tcp.recv(&mut buf).await;
            return (r, buf);
        }
        if self.rest.borrow().is_empty() {
            let mut len = [0u8; 4];
            match self.read_exact(&mut len).await {
                Ok(true) => {}
                Ok(false) => return (Ok(0), buf),
                Err(e) => return (Err(e), buf),
            }
            let mut body = vec![0u8; u32::from_be_bytes(len) as usize];
            match self.read_exact(&mut body).await {
                Ok(true) => *self.rest.borrow_mut() = body,
                Ok(false) => return (Ok(0), buf),
                Err(e) => return (Err(e), buf),
            }
        }
        let mut rest = self.rest.borrow_mut();
        let n = rest.len().min(buf.len());
        buf[..n].copy_from_slice(&rest[..n]);
        rest.drain(..n);
        (Ok(n), buf)
    }

    async fn write(&self, buf: Vec<u8>, from: usize) -> (io::Result<usize>, Vec<u8>) {
        let r = if self.messages {
            let mut framed = (u32::try_from(buf.len() - from).unwrap()).to_be_bytes().to_vec();
            framed.extend_from_slice(&buf[from..]);
            self.write_all(&framed).await.map(|()| buf.len() - from)
        } else {
            self.tcp.send(&buf[from..]).await
        };
        (r, buf)
    }
}

/// Connect to `to` and say which kind of carrier this is.
async fn open_wire(to: SocketAddr, kind: CarrierKind) -> io::Result<Wire> {
    let wire = Wire::new(Handle::<TcpStream>::connect(to).await?, kind);
    wire.write_all(&[marker(kind)]).await?;
    Ok(wire)
}

/// The sockets of a relay host on loopback: a TCP listener and a UDP socket on one port.
struct Ports {
    listener: Rc<Handle<TcpListener>>,
    sock: Rc<Handle<UdpSocket>>,
    addr: SocketAddr,
}

async fn bind_ports() -> Ports {
    // the UDP port of the same number may be taken by another test process: try another number
    for _ in 0..50 {
        let listener = Rc::new(Handle::<TcpListener>::bind(lo()).await.unwrap());
        let addr = listener.get_ref().local_addr().unwrap();
        if let Ok(sock) = Handle::<UdpSocket>::bind(addr).await {
            return Ports {
                listener,
                sock: Rc::new(sock),
                addr,
            };
        }
    }
    panic!("no port is free for both TCP and UDP");
}

/// A relay host run as a local task.
struct Host {
    id: vinc_crypto::NodeId,
    addr: SocketAddr,
    stats: Box<dyn Fn() -> Stats>,
    stop: Box<dyn Fn()>,
    task: Option<nuclei::Task<vinc::Result<()>>>,
}

impl Host {
    fn start(ports: &Ports, seed: u8, peers: &[Peer]) -> Self {
        Self::start_limits(ports, seed, peers, Limits::default())
    }

    fn start_limits(ports: &Ports, seed: u8, peers: &[Peer], limits: Limits) -> Self {
        let t0 = Instant::now();
        let base = wall_ns();
        let l = Rc::clone(&ports.listener);
        let (s1, s2) = (Rc::clone(&ports.sock), Rc::clone(&ports.sock));
        let mut builder = RelayHost::builder()
            .identity(Identity::from_seed(&[seed; 32]).unwrap())
            .limits(limits);
        for p in peers {
            builder = builder.peer(*p);
        }
        let relay = builder
            .store(MemStore::new())
            .hub(ports.addr, &[vinc_node::HUB_ALPN])
            .build(
                Udp::new(
                    async move |buf: &mut [u8]| s1.recv_from(buf).await.map_err(failed),
                    async move |pkt: &[u8], to| s2.send_to(pkt, to).await.map_err(failed),
                ),
                Carriers::new(
                    async move || {
                        let (tcp, _) = l.accept().await.map_err(failed)?;
                        let mut m = [0u8; 1];
                        let kind = if tcp.recv(&mut m).await.map_err(failed)? == 1 {
                            kind_of(m[0])
                        } else {
                            CarrierKind::Tcp
                        };
                        Ok((Wire::new(tcp, kind), kind))
                    },
                    async |p: &Peer, kind: CarrierKind| {
                        let to = p
                            .tcp
                            .ok_or_else(|| Error::new(ErrorKind::Unreachable, "the peer has no address"))?;
                        open_wire(to, kind).await.map_err(failed)
                    },
                    async |w: &Wire, buf: Vec<u8>| {
                        let (r, buf) = w.read(buf).await;
                        (r.map_err(failed), buf)
                    },
                    async |w: &Wire, buf: Vec<u8>, from: usize| {
                        let (r, buf) = w.write(buf, from).await;
                        (r.map_err(failed), buf)
                    },
                    async |_w: Wire| {},
                ),
                Clock::new(
                    move || base + u64::try_from(t0.elapsed().as_nanos()).unwrap(),
                    async move |at: u64| {
                        nuclei::time::sleep_until_precise(t0 + Duration::from_nanos(at.saturating_sub(base))).await;
                    },
                ),
            )
            .unwrap();
        let (r1, r2, r3) = (relay.clone(), relay.clone(), relay.clone());
        let task = nuclei::spawn_local(async move { r1.run().await });
        Self {
            id: r3.node_id(),
            addr: ports.addr,
            stats: Box::new(move || r2.stats()),
            stop: Box::new(move || relay.stop()),
            task: Some(task),
        }
    }

    /// The relay as an endpoint is told about it: the carriers of `kind` and the UDP address.
    fn relay(&self, kind: CarrierKind) -> Relay {
        let r = Relay::new(self.id).with_udp(self.addr);
        match kind {
            CarrierKind::Tcp => r.with_tcp(self.addr),
            CarrierKind::Ws => r.with_ws(self.addr),
            CarrierKind::WsMessages => r.with_ws(self.addr).with_messages(),
        }
    }

    /// Stop the relay and wait until it has closed its carriers and returned.
    async fn stop(&mut self) {
        (self.stop)();
        assert!(self.task.take().unwrap().await.is_ok());
    }
}

/// A facade endpoint with seed `seed` that knows only `relay`, over a new loopback UDP socket and the test carriers.
macro_rules! endpoint {
    ($seed:expr, $relay:expr) => {
        endpoint!($seed, $relay, false)
    };
    ($seed:expr, $relay:expr, $relayed_only:expr) => {{
        let relay: Relay = $relay;
        let only: bool = $relayed_only;
        let sock = Rc::new(Handle::<UdpSocket>::bind(lo()).await.unwrap());
        let (r, s) = (Rc::clone(&sock), Rc::clone(&sock));
        let ep = vinc_common::builder()
            .seed(&[$seed; 32])
            .unwrap()
            .alpn(ECHO)
            .alpn(SINK)
            .limits(vinc::Limits {
                connections: 8,
                ..vinc::Limits::default()
            })
            .relays([relay])
            .local_addr(sock.local_addr().unwrap())
            .carriers(
                async |relay: &Relay, kind: CarrierKind| {
                    let to = if kind == CarrierKind::Tcp { relay.tcp } else { relay.ws };
                    open_wire(to.unwrap(), kind).await
                },
                async |w: &Wire, buf: Vec<u8>| w.read(buf).await,
                async |w: &Wire, buf: Vec<u8>, from: usize| w.write(buf, from).await,
                async |_w: Wire| {},
            )
            .build(
                async move |buf: &mut [u8]| r.recv_from(buf).await,
                // with `only`, every datagram that is not for the relay is dropped: no direct path can form
                async move |pkt: &[u8], to: SocketAddr| {
                    if only && Some(to) != relay.udp {
                        Ok(pkt.len())
                    } else {
                        s.send_to(pkt, to).await
                    }
                },
                async |at: Instant| nuclei::time::sleep_until_precise(at).await,
            )
            .unwrap();
        let runner = ep.clone();
        nuclei::spawn_local(async move {
            let _ = runner.run().await;
        })
        .detach();
        let server = ep.clone();
        nuclei::spawn_local(async move {
            while let Some(i) = server.accept().await {
                nuclei::spawn_local(serve_conn(i.into_connection())).detach();
            }
        })
        .detach();
        ep
    }};
}

/// An echo over a connection that was opened by node id, then a wait until it uses a direct path, then the relays go.
macro_rules! reach_and_move {
    ($a:expr, $b:expr, $stops:expr) => {{
        let conn = $a.connect($b.id(), ECHO).await.unwrap();
        assert_eq!(conn.remote(), $b.id());
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        tx.write_all(b"through the relay").await.unwrap();
        let mut got = [0u8; 17];
        rx.read_exact(&mut got).await.unwrap();
        assert_eq!(&got, b"through the relay");
        eventually(60, "the connection moves to a direct path", || {
            let conn = conn.clone();
            async move {
                conn.stats()
                    .await
                    .is_ok_and(|s| s.route.is_some_and(|(_, r)| !vinc_core::is_relay_addr(&r)))
            }
        })
        .await;
        for host in $stops.iter_mut() {
            host.stop().await;
        }
        tx.write_all(b"the relay is gone").await.unwrap();
        let mut got = [0u8; 17];
        rx.read_exact(&mut got).await.unwrap();
        assert_eq!(&got, b"the relay is gone");
        assert!(conn.close_reason().is_none(), "the direct session lives on");
    }};
}

async fn through_one_relay(kind: CarrierKind) {
    let ports = bind_ports().await;
    let host = Host::start(&ports, 0x71, &[]);
    let relay = host.relay(kind);
    let a = endpoint!(1, relay);
    let b = endpoint!(2, relay);
    within(120, async {
        eventually(60, "both carriers are up at the relay", || {
            let up = (host.stats)().carriers;
            async move { up >= 2 }
        })
        .await;
        let mut stops = [host];
        reach_and_move!(a, b, stops);
    })
    .await;
}

#[nuclei::test]
async fn endpoints_that_know_only_a_relay_reach_each_other_through_the_relay_host_over_tcp() {
    through_one_relay(CarrierKind::Tcp).await;
}

#[nuclei::test]
async fn the_same_over_a_websocket_the_facade_frames_itself() {
    through_one_relay(CarrierKind::Ws).await;
}

#[nuclei::test]
async fn the_same_over_the_whole_message_websocket_of_a_browser() {
    through_one_relay(CarrierKind::WsMessages).await;
}

#[nuclei::test]
async fn endpoints_homed_at_two_relay_hosts_in_a_mesh_reach_each_other() {
    let (pa, pb) = (bind_ports().await, bind_ports().await);
    let ids = [
        Identity::from_seed(&[0x72; 32]).unwrap().node_id(),
        Identity::from_seed(&[0x73; 32]).unwrap().node_id(),
    ];
    let list = [Peer::new(ids[0]).with_tcp(pa.addr), Peer::new(ids[1]).with_tcp(pb.addr)];
    let host_a = Host::start(&pa, 0x72, &list);
    let host_b = Host::start(&pb, 0x73, &list);
    // `a` knows only the first relay and `b` only the second
    let a = endpoint!(1, host_a.relay(CarrierKind::Tcp));
    let b = endpoint!(2, host_b.relay(CarrierKind::Tcp));
    within(120, async {
        eventually(60, "the mesh is up and each endpoint has its carrier", || {
            let (sa, sb) = ((host_a.stats)(), (host_b.stats)());
            async move { sa.peers_up == 1 && sb.peers_up == 1 && sa.carriers == 1 && sb.carriers == 1 }
        })
        .await;
        let mut stops = [host_a, host_b];
        reach_and_move!(a, b, stops);
    })
    .await;
}

/// What one run of the indication measured.
struct Numbers {
    median_us: u128,
    p99_us: u128,
    mean_us: u128,
    mib_s: f64,
    stats: Stats,
}

/// A 64-byte round trip a thousand times and a 64 MiB transfer between two endpoints that know only a relay host
/// carrying `idle` other carriers; `relayed_only` drops every datagram that is not for the relay, so no direct path forms.
async fn measure(relayed_only: bool, idle: usize) -> Numbers {
    let ports = bind_ports().await;
    let limits = Limits {
        carriers: idle + 8,
        quota: Quota {
            bytes: u64::MAX / 2,
            ..Quota::DEFAULT
        },
        ..Limits::default()
    };
    let mut host = Host::start_limits(&ports, 0x7a, &[], limits);
    let mut idles = Vec::new();
    let relay = host.relay(CarrierKind::Tcp);
    let a = endpoint!(1, relay, relayed_only);
    let b = endpoint!(2, relay, relayed_only);
    let numbers = within(600, async {
        for n in 0..idle {
            let mut seed = [0u8; 32];
            seed[..4].copy_from_slice(&(u32::try_from(n).unwrap() + 1000).to_be_bytes());
            idles.push(
                Member::connect_prefixed(
                    host.addr,
                    host.id,
                    seed,
                    CarrierKind::Tcp,
                    ALPN,
                    &[marker(CarrierKind::Tcp)],
                )
                .await,
            );
        }
        eventually(60, "both endpoints are up at the relay", || {
            let up = (host.stats)().carriers;
            async move { up >= idle + 2 }
        })
        .await;
        let conn = a.connect(b.id(), ECHO).await.unwrap();
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        let direct = |conn: &vinc::Connection<_>| {
            let conn = conn.clone();
            async move {
                conn.stats()
                    .await
                    .is_ok_and(|s| s.route.is_some_and(|(_, r)| !vinc_core::is_relay_addr(&r)))
            }
        };
        if relayed_only {
            tx.write_all(b"x").await.unwrap();
            rx.read_exact(&mut [0u8; 1]).await.unwrap();
            nuclei::time::sleep(Duration::from_secs(2)).await;
            assert!(
                !direct(&conn).await,
                "a direct path formed although every datagram but the relay's is dropped"
            );
        } else {
            eventually(60, "the connection moves to a direct path", || direct(&conn)).await;
        }
        let mut rtts = Vec::new();
        let mut buf = [0u8; 64];
        for _ in 0..1000 {
            let t = Instant::now();
            tx.write_all(&[7u8; 64]).await.unwrap();
            rx.read_exact(&mut buf).await.unwrap();
            rtts.push(t.elapsed().as_micros());
        }
        rtts.sort_unstable();
        let sink = a.connect(b.id(), SINK).await.unwrap();
        let (mut stx, mut srx) = sink.open_bi().await.unwrap();
        let chunk = vec![9u8; 64 * 1024];
        let t = Instant::now();
        for _ in 0..1024 {
            stx.write_all(&chunk).await.unwrap();
        }
        stx.finish().await.unwrap();
        let mut reply = [0u8; 40];
        srx.read_exact(&mut reply).await.unwrap();
        assert_eq!(u64::from_le_bytes(reply[..8].try_into().unwrap()), 64 << 20);
        let secs = t.elapsed().as_secs_f64();
        Numbers {
            median_us: rtts[rtts.len() / 2],
            p99_us: rtts[rtts.len() * 99 / 100],
            mean_us: rtts.iter().sum::<u128>() / rtts.len() as u128,
            mib_s: 64.0 / secs,
            stats: (host.stats)(),
        }
    })
    .await;
    a.close().await;
    b.close().await;
    drop(idles);
    host.stop().await;
    numbers
}

/// An indication of what the relay costs, printed and not asserted: run with `--run-ignored all --no-capture` on a
/// machine that is not busy; the numbers of a loaded host are not to be quoted.
#[test]
#[ignore = "an indication on the machine it runs on, not a check"]
fn what_the_relay_costs() {
    on_big_stack(|| async {
        for (label, relayed_only, idle) in [
            ("direct", false, 0),
            ("relayed", true, 0),
            ("relayed, 250 idle carriers", true, 250),
            ("relayed, 1000 idle carriers", true, 1000),
        ] {
            let n = measure(relayed_only, idle).await;
            let polls = n.stats.stream_polls / n.stats.wakes.max(1);
            eprintln!(
                "BENCH {label}: 64 B round trip median {} us, p99 {} us, mean {} us; 64 MiB at {:.1} MiB/s; the relay woke {} times and looked at {polls} streams per wake",
                n.median_us, n.p99_us, n.mean_us, n.mib_s, n.stats.wakes
            );
        }
    });
}
