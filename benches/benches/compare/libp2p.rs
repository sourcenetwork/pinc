//! The comparison harness for rust-libp2p (see `compare/mod.rs`).
//!
//! Two transports, chosen with `--variant=quic` (the default) or `--variant=tcp`: QUIC (`libp2p-quic`, its built-in
//! TLS and stream multiplexing) and TCP with Noise and Yamux, the stack most libp2p deployments run. A stream opens
//! with libp2p's protocol negotiation, as an application's would, through the behaviour in `libp2p_streams.rs`, which
//! negotiates every requested open at once (the `libp2p-stream` crate negotiates one at a time per connection, which
//! would cap the request test at one stream per round trip). Defaults: the
//! `SwarmBuilder` defaults with a new identity, plus a five minute idle connection timeout (the swarm's default of zero
//! closes a connection with no stream at once), and tokio's multi-thread runtime with one worker per core. libp2p has
//! no resumption with early data, so the resumed scenario is not measured.
//!
//! Opt-in knob, off by default and recorded in the row's `knobs` when set: `PINC_BENCH_LIBP2P_UPGRADE=v1-lazy` opens
//! streams with multistream-select V1Lazy instead of the swarm's default V1 (`v1` names the default).
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

use std::io;
use std::sync::OnceLock;
use std::time::Duration;

use super::libp2p_streams::{Behaviour, Control};
use super::{Lib, Rx, Tx};
use futures::channel::mpsc;
use futures::io::{ReadHalf, WriteHalf};
use futures::{AsyncReadExt, AsyncWriteExt, StreamExt};
use libp2p::multiaddr::Protocol;
use libp2p::swarm::{Stream, SwarmEvent};
use libp2p::{Multiaddr, PeerId, StreamProtocol, Swarm, SwarmBuilder, noise, tcp, yamux};

const PROTO: StreamProtocol = StreamProtocol::new("/bench/1");

fn io_err(e: impl std::fmt::Display) -> io::Error {
    io::Error::other(e.to_string())
}

fn tcp_variant() -> bool {
    super::variant() == "tcp"
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

/// Whether `PINC_BENCH_LIBP2P_UPGRADE=v1-lazy` asks for multistream-select's V1Lazy on new streams: the dialer sends
/// its data with the protocol proposal instead of waiting a round trip for the listener to confirm it. Unset (or
/// `v1`): the swarm's default, V1, under which libp2p-stream negotiates one outbound stream of a connection at a time
/// (`libp2p-stream` 0.5.0-alpha `handler.rs`, `pending_upgrade`), one round trip each.
fn v1_lazy() -> io::Result<bool> {
    match super::knob("PINC_BENCH_LIBP2P_UPGRADE").as_deref() {
        None | Some("v1") => Ok(false),
        Some("v1-lazy") => Ok(true),
        Some(other) => Err(io_err(format!(
            "PINC_BENCH_LIBP2P_UPGRADE is `v1` or `v1-lazy`, not `{other}`"
        ))),
    }
}

fn swarm() -> io::Result<Swarm<Behaviour>> {
    let base = SwarmBuilder::with_new_identity().with_tokio();
    let lazy = v1_lazy()?;
    let idle = move |c: libp2p::swarm::Config| {
        let c = c.with_idle_connection_timeout(Duration::from_secs(300));
        if lazy {
            c.with_substream_upgrade_protocol_override(libp2p::core::upgrade::Version::V1Lazy)
        } else {
            c
        }
    };
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
pub struct Ep {
    control: Control,
    cmds: mpsc::UnboundedSender<Cmd>,
    up: tokio::sync::Mutex<mpsc::UnboundedReceiver<Result<PeerId, String>>>,
}

/// A connection is a peer: libp2p opens streams to a peer, over whatever connection it has.
#[derive(Clone)]
pub struct Conn {
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

/// The library under test.
pub struct Libp2p;

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
            .block_on(tokio::task::LocalSet::new().run_until(f))
    }

    fn spawn(f: impl Future<Output = ()> + 'static) {
        // The scenarios run on the thread that drives them; the library's own tasks use the runtime's threads.
        tokio::task::spawn_local(f);
    }

    async fn sleep(d: Duration) {
        tokio::time::sleep(d).await;
    }

    async fn serve() -> io::Result<String> {
        let mut sw = swarm()?;
        let me = *sw.local_peer_id();
        let ip = super::bind_ip()?;
        let proto = if ip.is_ipv4() { "ip4" } else { "ip6" };
        let on: Multiaddr = if tcp_variant() {
            format!("/{proto}/{ip}/tcp/0")
        } else {
            format!("/{proto}/{ip}/udp/0/quic-v1")
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
                    let _ = super::handle(tx, rx).await;
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

    async fn wire(_conn: &Conn) -> super::Wire {
        let (udp_source, kx_group, kx_source) = if tcp_variant() {
            (
                "not UDP: TCP with Noise and Yamux".to_owned(),
                "X25519".to_owned(),
                "protocol: Noise_XX_25519_ChaChaPoly_SHA256 (libp2p-noise)".to_owned(),
            )
        } else {
            (
                "not exposed: libp2p-quic keeps its quinn connection, with its path MTU and UDP counters, private; \
                 its MTU discovery uses quinn's defaults (initial 1200 bytes, upper bound 1452); the node's kernel \
                 counters give the mean"
                    .to_owned(),
                tls_group(),
                "libp2p-tls's client and server configs (those libp2p-quic builds) in one TLS handshake in memory: \
                 libp2p-quic does not expose the live connection's handshake"
                    .to_owned(),
            )
        };
        let knobs = if v1_lazy().unwrap_or(false) {
            "upgrade=v1-lazy"
        } else {
            ""
        };
        super::Wire {
            max_udp_payload: None,
            mean_udp_payload: None,
            udp_source,
            kx_group,
            kx_source,
            cwnd: None,
            knobs: knobs.into(),
        }
    }
}

/// The key exchange group libp2p-tls's configs agree on, from one handshake between them in memory (once a process).
fn tls_group() -> String {
    static GROUP: OnceLock<String> = OnceLock::new();
    GROUP
        .get_or_init(|| tls_handshake().unwrap_or_else(|e| format!("unknown: {e}")))
        .clone()
}

fn tls_handshake() -> Result<String, String> {
    use std::sync::Arc;
    let (a, b) = (
        libp2p::identity::Keypair::generate_ed25519(),
        libp2p::identity::Keypair::generate_ed25519(),
    );
    let s_ = |x: &dyn std::fmt::Display| x.to_string();
    let client = libp2p_tls::make_client_config(&a, Some(b.public().to_peer_id())).map_err(|x| s_(&x))?;
    let server = libp2p_tls::make_server_config(&b).map_err(|x| s_(&x))?;
    // libp2p-quic dials with the server name "l".
    let name = rustls::pki_types::ServerName::try_from("l").map_err(|x| s_(&x))?;
    let mut c = rustls::ClientConnection::new(Arc::new(client), name).map_err(|x| s_(&x))?;
    let mut s = rustls::ServerConnection::new(Arc::new(server)).map_err(|x| s_(&x))?;
    for _ in 0..16 {
        let mut buf = Vec::new();
        while c.wants_write() {
            c.write_tls(&mut buf).map_err(|x| s_(&x))?;
        }
        let mut rd = &buf[..];
        while !rd.is_empty() {
            s.read_tls(&mut rd).map_err(|x| s_(&x))?;
            s.process_new_packets().map_err(|x| s_(&x))?;
        }
        buf.clear();
        while s.wants_write() {
            s.write_tls(&mut buf).map_err(|x| s_(&x))?;
        }
        let mut rd = &buf[..];
        while !rd.is_empty() {
            c.read_tls(&mut rd).map_err(|x| s_(&x))?;
            c.process_new_packets().map_err(|x| s_(&x))?;
        }
        if !c.is_handshaking() && !s.is_handshaking() {
            break;
        }
    }
    c.negotiated_key_exchange_group()
        .map(|g| format!("{:?}", g.name()))
        .ok_or_else(|| "the handshake did not finish".to_owned())
}
