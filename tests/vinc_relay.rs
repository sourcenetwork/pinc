//! The relay client: endpoints that know only a relay reach each other through it, then move to a direct path.
//!
//! The relay is the relay state machine of `vinc-connect` with its own endpoint (`RelayNode`), driven here on a real
//! loopback UDP socket; the carriers are in-memory pipes between the endpoints' closures and that state machine, so the
//! host side of the carriers is exactly what a host writes: `open`, `read`, `write` and `close` over owned buffers.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::items_after_statements,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

#[macro_use]
mod vinc_common;

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::io;
use std::net::{SocketAddr, UdpSocket};
use std::rc::Rc;
use std::time::{Duration, Instant};

use nuclei::Handle;
use nuclei::sync::Mutex as AsyncMutex;
use nuclei::sync::mpsc::{UnboundedReceiver, UnboundedSender, unbounded_channel};
use vinc::{CarrierKind, Relay};
use vinc_common::{ECHO, eventually, lo, serve_conn, within};
use vinc_sim::{StreamEvent, StreamId, StreamOp};
use vinc_tests::RelayNode;

/// One end of an in-memory carrier: what the relay writes arrives on `rx`.
struct Pipe {
    stream: StreamId,
    rx: AsyncMutex<UnboundedReceiver<Vec<u8>>>,
    left: RefCell<Vec<u8>>,
}

/// The relay state machine on a UDP socket, and the carriers to it.
struct Rig {
    relay: RefCell<RelayNode>,
    sock: Handle<UdpSocket>,
    addr: SocketAddr,
    t0: Instant,
    next: Cell<u32>,
    to_client: RefCell<HashMap<StreamId, UnboundedSender<Vec<u8>>>>,
}

impl Rig {
    async fn start() -> Rc<Self> {
        let sock = Handle::<UdpSocket>::bind(lo()).await.unwrap();
        let addr = sock.local_addr().unwrap();
        let rig = Rc::new(Self {
            relay: RefCell::new(RelayNode::new(0x70, addr, 0)),
            sock,
            addr,
            t0: Instant::now(),
            next: Cell::new(1),
            to_client: RefCell::new(HashMap::new()),
        });
        let r = Rc::clone(&rig);
        nuclei::spawn_local(async move { r.serve().await }).detach();
        rig
    }

    fn now(&self) -> u64 {
        u64::try_from(self.t0.elapsed().as_nanos()).unwrap()
    }

    fn id(&self) -> vinc_crypto::NodeId {
        self.relay.borrow().id()
    }

    fn carriers_open(&self) -> usize {
        self.relay.borrow().carriers_opened.len()
    }

    /// Send what the relay produced: its datagrams on the socket, its carrier bytes into the pipes.
    async fn flush(&self) {
        let mut buf = vec![0u8; 65_536];
        loop {
            let op = self.relay.borrow_mut().poll_stream(&mut buf);
            match op {
                Some(StreamOp::Write { stream, len, .. }) => {
                    if let Some(tx) = self.to_client.borrow().get(&stream) {
                        let _ = tx.send(buf[..len].to_vec());
                    }
                }
                Some(StreamOp::Close { stream }) => {
                    self.to_client.borrow_mut().remove(&stream);
                }
                Some(StreamOp::Connect { .. }) => {}
                None => break,
            }
        }
        loop {
            let t = self.relay.borrow_mut().poll_transmit(&mut buf);
            let Some(t) = t else { break };
            let _ = self.sock.send_to(&buf[..t.len], t.remote).await;
        }
    }

    /// The relay's UDP side: datagrams in, timers.
    #[allow(clippy::needless_continue, reason = "the select macro's own expansion")]
    async fn serve(self: Rc<Self>) {
        let mut buf = vec![0u8; 65_536];
        loop {
            let wait = {
                let now = self.now();
                self.relay
                    .borrow()
                    .poll_timeout()
                    .map_or(Duration::from_millis(20), |t| {
                        Duration::from_nanos(t.saturating_sub(now)).min(Duration::from_millis(20))
                    })
            };
            nuclei::select! {
                r = self.sock.recv_from(&mut buf) => {
                    if let Ok((n, from)) = r {
                        let now = self.now();
                        self.relay.borrow_mut().handle_datagram(now, self.addr, from, &mut buf[..n]);
                        self.flush().await;
                    }
                },
                () = nuclei::time::sleep(wait) => {
                    let now = self.now();
                    self.relay.borrow_mut().handle_timeout(now);
                    self.flush().await;
                },
            }
        }
    }

    async fn open(&self) -> io::Result<Pipe> {
        let stream = StreamId(self.next.get());
        self.next.set(self.next.get() + 1);
        let (tx, rx) = unbounded_channel();
        self.to_client.borrow_mut().insert(stream, tx);
        let now = self.now();
        self.relay.borrow_mut().handle_stream_event(
            now,
            StreamEvent::Opened {
                stream,
                remote: self.addr,
            },
        );
        self.flush().await;
        Ok(Pipe {
            stream,
            rx: AsyncMutex::new(rx),
            left: RefCell::new(Vec::new()),
        })
    }

    async fn read(&self, p: &Pipe, mut buf: Vec<u8>) -> (io::Result<usize>, Vec<u8>) {
        if p.left.borrow().is_empty() {
            match p.rx.lock().await.recv().await {
                Some(d) => *p.left.borrow_mut() = d,
                None => return (Ok(0), buf),
            }
        }
        let mut left = p.left.borrow_mut();
        let n = left.len().min(buf.len());
        buf[..n].copy_from_slice(&left[..n]);
        left.drain(..n);
        (Ok(n), buf)
    }

    async fn write(&self, p: &Pipe, buf: Vec<u8>, from: usize) -> (io::Result<usize>, Vec<u8>) {
        let mut data = buf[from..].to_vec();
        let now = self.now();
        self.relay.borrow_mut().handle_stream_record(now, p.stream, &mut data);
        self.flush().await;
        (Ok(data.len()), buf)
    }

    async fn close(&self, p: Pipe) {
        let now = self.now();
        self.to_client.borrow_mut().remove(&p.stream);
        self.relay
            .borrow_mut()
            .handle_stream_event(now, StreamEvent::Closed { stream: p.stream });
        self.flush().await;
    }
}

/// An endpoint of `$builder` over a new loopback UDP socket whose carriers go to `$rig`.
macro_rules! relay_endpoint {
    ($builder:expr, $rig:expr) => {{
        let sock = Rc::new(Handle::<UdpSocket>::bind(lo()).await.unwrap());
        let (r, s) = (Rc::clone(&sock), Rc::clone(&sock));
        let (o, rd, w, c) = (Rc::clone(&$rig), Rc::clone(&$rig), Rc::clone(&$rig), Rc::clone(&$rig));
        $builder
            .local_addr(sock.local_addr().unwrap())
            .carriers(
                async move |_relay: &Relay, _kind: CarrierKind| o.open().await,
                async move |p: &Pipe, buf: Vec<u8>| rd.read(p, buf).await,
                async move |p: &Pipe, buf: Vec<u8>, from: usize| w.write(p, buf, from).await,
                async move |p: Pipe| c.close(p).await,
            )
            .build(
                async move |buf: &mut [u8]| r.recv_from(buf).await,
                async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
                async |at: Instant| nuclei::time::sleep_until_precise(at).await,
            )
            .unwrap()
    }};
}

/// Two endpoints that know only `relay_of(rig)` reach each other through the relay and move to a direct path.
async fn reach_through_the_relay(relay_of: fn(&Rig) -> Relay) {
    let rig = Rig::start().await;
    let relay = relay_of(&rig);
    let a = relay_endpoint!(
        vinc_common::builder()
            .seed(&[1; 32])
            .unwrap()
            .alpn(ECHO)
            .relays([relay]),
        rig
    );
    let b = relay_endpoint!(
        vinc_common::builder()
            .seed(&[2; 32])
            .unwrap()
            .alpn(ECHO)
            .relays([relay]),
        rig
    );
    let (ra, rb) = (a.clone(), b.clone());
    nuclei::spawn_local(async move {
        let _ = ra.run().await;
    })
    .detach();
    nuclei::spawn_local(async move {
        let _ = rb.run().await;
    })
    .detach();
    let server = b.clone();
    nuclei::spawn_local(async move {
        while let Some(i) = server.accept().await {
            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();
    within(120, async {
        let rig2 = Rc::clone(&rig);
        eventually(60, "both carriers open at the relay", || {
            let rig2 = Rc::clone(&rig2);
            async move { rig2.carriers_open() >= 2 }
        })
        .await;
        // B is known by its id alone: the relay finds it, the first packets go through the relay.
        let conn = a.connect(b.id(), ECHO).await.unwrap();
        assert_eq!(conn.remote(), b.id());
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        tx.write_all(b"through the relay").await.unwrap();
        let mut got = [0u8; 17];
        rx.read_exact(&mut got).await.unwrap();
        assert_eq!(&got, b"through the relay");
        // A direct path exists on loopback: the connection moves to it.
        eventually(60, "the connection moves to a direct path", || {
            let conn = conn.clone();
            async move {
                conn.stats()
                    .await
                    .is_ok_and(|s| s.route.is_some_and(|(_, r)| !vinc_core::is_relay_addr(&r)))
            }
        })
        .await;
        tx.write_all(b"direct").await.unwrap();
        let mut got = [0u8; 6];
        rx.read_exact(&mut got).await.unwrap();
        assert_eq!(&got, b"direct");
    })
    .await;
}

#[nuclei::test]
async fn endpoints_that_know_only_a_relay_reach_each_other_and_move_to_a_direct_path() {
    reach_through_the_relay(|rig| Relay::new(rig.id()).with_udp(rig.addr).with_tcp(rig.addr)).await;
}

#[nuclei::test]
async fn the_same_over_a_websocket_carrier_the_facade_frames_itself() {
    reach_through_the_relay(|rig| Relay::new(rig.id()).with_udp(rig.addr).with_ws(rig.addr)).await;
}
