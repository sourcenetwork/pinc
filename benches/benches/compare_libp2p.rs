//! The comparison harness for rust-libp2p (see `compare/mod.rs`).
//!
//! Two transports, chosen with `--variant=quic` (the default) or `--variant=tcp`: QUIC (`libp2p-quic`, its built-in
//! TLS and stream multiplexing) and TCP with Noise and Yamux, the stack most libp2p deployments run. Streams come from
//! `libp2p-stream`, so a stream opens with libp2p's protocol negotiation, as an application's would. Defaults: the
//! `SwarmBuilder` defaults with a new identity, plus a five minute idle connection timeout (the swarm's default of zero
//! closes a connection with no stream at once), and tokio's multi-thread runtime with one worker per core. libp2p has
//! no resumption with early data, so the resumed scenario is not measured.
#![allow(
    missing_docs,
    unsafe_code,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::unreadable_literal,
    clippy::missing_errors_doc,
    clippy::doc_markdown,
    clippy::needless_pass_by_value,
    clippy::items_after_statements,
    clippy::cast_lossless,
    clippy::format_push_string,
    clippy::unused_async_trait_impl,
    clippy::default_trait_access
)]

mod compare;

use std::io;
use std::sync::OnceLock;
use std::time::Duration;

use compare::{Counting, Lib, Rx, Tx};
use futures::channel::mpsc;
use futures::io::{ReadHalf, WriteHalf};
use futures::{AsyncReadExt, AsyncWriteExt, StreamExt};
use libp2p::multiaddr::Protocol;
use libp2p::swarm::{Stream, SwarmEvent};
use libp2p::{Multiaddr, PeerId, StreamProtocol, Swarm, SwarmBuilder, noise, tcp, yamux};
use libp2p_stream::{Behaviour, Control};

#[global_allocator]
static ALLOC: Counting = Counting;

const PROTO: StreamProtocol = StreamProtocol::new("/bench/1");

fn io_err(e: impl std::fmt::Display) -> io::Error {
    io::Error::other(e.to_string())
}

fn tcp_variant() -> bool {
    compare::variant() == "tcp"
}

impl Tx for WriteHalf<Stream> {
    async fn write_all(&mut self, b: &[u8]) -> io::Result<()> {
        AsyncWriteExt::write_all(self, b).await
    }
    async fn finish(&mut self) -> io::Result<()> {
        self.close().await
    }
}

impl Rx for ReadHalf<Stream> {
    async fn read(&mut self, b: &mut [u8]) -> io::Result<usize> {
        AsyncReadExt::read(self, b).await
    }
}

fn swarm() -> io::Result<Swarm<Behaviour>> {
    let base = SwarmBuilder::with_new_identity().with_tokio();
    let idle = |c: libp2p::swarm::Config| c.with_idle_connection_timeout(Duration::from_secs(300));
    if tcp_variant() {
        Ok(base
            .with_tcp(tcp::Config::default(), noise::Config::new, yamux::Config::default)
            .map_err(io_err)?
            .with_behaviour(|_| Behaviour::new())
            .map_err(io_err)?
            .with_swarm_config(idle)
            .build())
    } else {
        Ok(base
            .with_quic()
            .with_behaviour(|_| Behaviour::new())
            .map_err(io_err)?
            .with_swarm_config(idle)
            .build())
    }
}

enum Cmd {
    Dial(Multiaddr),
    Close(PeerId),
    Stop,
}

/// An endpoint: the control of its swarm and the channels to the task that polls the swarm.
struct Ep {
    control: Control,
    cmds: mpsc::UnboundedSender<Cmd>,
    up: tokio::sync::Mutex<mpsc::UnboundedReceiver<Result<PeerId, String>>>,
}

/// A connection is a peer: libp2p opens streams to a peer, over whatever connection it has.
#[derive(Clone)]
struct Conn {
    control: Control,
    peer: PeerId,
}

/// Poll the swarm until told to stop; report each outgoing connection as it opens or fails.
fn drive(mut swarm: Swarm<Behaviour>) -> Ep {
    let control = swarm.behaviour().new_control();
    let (cmds, rx) = mpsc::unbounded();
    let (up_tx, up) = mpsc::unbounded();
    tokio::spawn(async move {
        let mut rx = rx.fuse();
        loop {
            futures::select! {
                ev = swarm.select_next_some() => match ev {
                    SwarmEvent::ConnectionEstablished { peer_id, endpoint, .. } if endpoint.is_dialer() => {
                        let _ = up_tx.unbounded_send(Ok(peer_id));
                    }
                    SwarmEvent::OutgoingConnectionError { error, .. } => {
                        let _ = up_tx.unbounded_send(Err(error.to_string()));
                    }
                    _ => {}
                },
                cmd = rx.next() => match cmd {
                    Some(Cmd::Dial(a)) => {
                        if let Err(e) = swarm.dial(a) {
                            let _ = up_tx.unbounded_send(Err(e.to_string()));
                        }
                    }
                    Some(Cmd::Close(p)) => {
                        let _ = swarm.disconnect_peer_id(p);
                    }
                    Some(Cmd::Stop) | None => break,
                },
            }
        }
    });
    Ep {
        control,
        cmds,
        up: tokio::sync::Mutex::new(up),
    }
}

static RT: OnceLock<tokio::runtime::Runtime> = OnceLock::new();

struct Libp2p;

impl Lib for Libp2p {
    fn name() -> &'static str {
        if tcp_variant() { "libp2p-tcp" } else { "libp2p-quic" }
    }
    const RESUMES: bool = false;
    type Ep = Ep;
    type Conn = Conn;
    type Tx = WriteHalf<Stream>;
    type Rx = ReadHalf<Stream>;

    fn run<T>(f: impl Future<Output = T>) -> T {
        let rt = tokio::runtime::Builder::new_multi_thread().enable_all().build();
        RT.get_or_init(|| rt.unwrap_or_else(|e| panic!("the runtime did not start: {e}")))
            .block_on(f)
    }

    fn spawn(f: impl Future<Output = ()> + Send + 'static) {
        tokio::spawn(f);
    }

    async fn sleep(d: Duration) {
        tokio::time::sleep(d).await;
    }

    async fn serve() -> io::Result<String> {
        let mut sw = swarm()?;
        let me = *sw.local_peer_id();
        let on: Multiaddr = if tcp_variant() {
            "/ip4/127.0.0.1/tcp/0"
        } else {
            "/ip4/127.0.0.1/udp/0/quic-v1"
        }
        .parse()
        .map_err(io_err)?;
        sw.listen_on(on).map_err(io_err)?;
        let mut incoming = sw.behaviour().new_control().accept(PROTO).map_err(io_err)?;
        let listen = loop {
            if let SwarmEvent::NewListenAddr { address, .. } = sw.select_next_some().await {
                break address;
            }
        };
        tokio::spawn(async move {
            loop {
                sw.select_next_some().await;
            }
        });
        tokio::spawn(async move {
            while let Some((_peer, stream)) = incoming.next().await {
                tokio::spawn(async move {
                    let (rx, tx) = stream.split();
                    let _ = compare::handle(tx, rx).await;
                });
            }
        });
        Ok(format!("{listen}/p2p/{me}"))
    }

    async fn client() -> io::Result<Ep> {
        Ok(drive(swarm()?))
    }

    async fn connect(ep: &Ep, addr: &str) -> io::Result<Conn> {
        let addr: Multiaddr = addr.parse().map_err(io_err)?;
        let peer = addr
            .iter()
            .find_map(|p| if let Protocol::P2p(id) = p { Some(id) } else { None })
            .ok_or_else(|| io_err("the address has no peer id"))?;
        ep.cmds.unbounded_send(Cmd::Dial(addr)).map_err(io_err)?;
        match ep.up.lock().await.next().await {
            Some(Ok(_)) => Ok(Conn {
                control: ep.control.clone(),
                peer,
            }),
            Some(Err(e)) => Err(io_err(e)),
            None => Err(io_err("the swarm stopped")),
        }
    }

    async fn open(conn: &Conn) -> io::Result<(WriteHalf<Stream>, ReadHalf<Stream>)> {
        let stream = conn
            .control
            .clone()
            .open_stream(conn.peer, PROTO)
            .await
            .map_err(io_err)?;
        let (rx, tx) = stream.split();
        Ok((tx, rx))
    }

    async fn close(ep: &Ep, conn: &Conn) {
        let _ = ep.cmds.unbounded_send(Cmd::Close(conn.peer));
    }

    async fn shutdown(ep: Ep) {
        let _ = ep.cmds.unbounded_send(Cmd::Stop);
    }
}

fn main() {
    compare::main::<Libp2p>();
}
