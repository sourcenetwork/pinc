//! The PINC node program's sockets on the nuclei runtime: one UDP socket with segmented sends and coalesced receives (the
//! calls the compared libraries use), and TCP streams for relay carriers, each as a pair of tasks that talk to the
//! host loop through channels.
//!
//! Invariants: nothing here decides anything about the protocol; a socket error ends the stream or is returned, never
//! swallowed; a stream's tasks end when its socket does.

use std::io;
use std::net::{SocketAddr, TcpStream, UdpSocket};
use std::rc::Rc;
use std::time::Instant;

use nuclei::Handle;
use nuclei::io::Interest;
use nuclei::net::{TcpListener, UdpSocketBuilder};
use nuclei::sync::local::mpsc::{UnboundedReceiver, UnboundedSender, unbounded_channel};
use quinn_udp::{RecvMeta, Transmit, UdpSockRef, UdpSocketState};

use super::core::{StreamEv, StreamId};

/// Every UDP payload this node program sent: the largest, the mean (the node's `Report`, under `wire`).
pub static SENT: crate::node::transport::compare::Sent = crate::node::transport::compare::Sent::new();

/// What the socket's send and receive buffers are asked to hold.
const SOCKET_BUFFER: u32 = 8 << 20;

/// The node's UDP socket.
pub struct Net {
    sock: Rc<Handle<UdpSocket>>,
    udp: UdpSocketState,
}

impl Net {
    /// Bind a UDP socket on `addr`.
    ///
    /// # Errors
    /// The socket could not be made or bound.
    pub fn bind(addr: SocketAddr) -> io::Result<Self> {
        let builder = if addr.is_ipv4() {
            UdpSocketBuilder::new_v4()?
        } else {
            UdpSocketBuilder::new_v6()?
        };
        builder.set_recv_buffer_size(SOCKET_BUFFER)?;
        builder.set_send_buffer_size(SOCKET_BUFFER)?;
        let sock = Rc::new(builder.bind(addr)?);
        let udp = UdpSocketState::new(UdpSockRef::from(&*sock))?;
        Ok(Self { sock, udp })
    }

    /// Datagrams of one sender in a call: the most segments the system sends at once.
    pub fn batch(&self) -> usize {
        self.udp.max_gso_segments().clamp(1, 40)
    }

    /// The next datagrams: bytes, the sender and the size of each datagram.
    ///
    /// # Errors
    /// The socket failed.
    pub async fn recv(&self, buf: &mut [u8]) -> io::Result<(usize, SocketAddr, usize)> {
        loop {
            let mut meta = [RecvMeta::default()];
            // The runtime's own readiness, not `readable()`: that one asks the socket with a peek, a system call per
            // wake on top of the receive.
            self.sock
                .async_io(Interest::READABLE, || {
                    self.udp.recv(
                        UdpSockRef::from(&*self.sock),
                        &mut [io::IoSliceMut::new(buf)],
                        &mut meta,
                    )
                })
                .await?;
            let [m] = meta;
            if m.len > 0 {
                return Ok((m.len, m.addr, m.stride.max(1)));
            }
        }
    }

    /// Send a run of equal-size datagrams to one address.
    ///
    /// # Errors
    /// The socket failed in a way that is not a lost packet.
    pub async fn send(&self, buf: &[u8], to: SocketAddr, segment: usize) -> io::Result<()> {
        let count = buf.len().div_ceil(segment.max(1));
        let transmit = Transmit {
            destination: to,
            ecn: None,
            contents: buf,
            segment_size: (count > 1).then_some(segment),
            src_ip: None,
        };
        loop {
            match self.udp.try_send(UdpSockRef::from(&*self.sock), &transmit) {
                Ok(()) => {
                    SENT.add(buf.len(), if count > 1 { segment } else { buf.len() });
                    return Ok(());
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => self.sock.writable().await?,
                // A packet the network refused (no route yet, a full queue) is lost like any other.
                Err(e)
                    if matches!(
                        e.kind(),
                        io::ErrorKind::HostUnreachable | io::ErrorKind::NetworkUnreachable
                    ) =>
                {
                    return Ok(());
                }
                Err(e) => return Err(e),
            }
        }
    }

    /// Wait until `at`.
    pub async fn sleep_until(at: Instant) {
        nuclei::time::sleep_until_precise(at).await;
    }
}

/// What the tasks of the streams report to the host loop.
pub enum Wire {
    /// A stream event.
    Ev(StreamEv),
    /// A connection the host asked for: open, or not.
    Connected(StreamId, Option<Handle<TcpStream>>),
    /// A connection arrived at the listener.
    Accepted(StreamId, Handle<TcpStream>),
}

/// The streams of a node program: the channel their tasks report on, and the queue that feeds each writer.
pub struct Streams {
    events: UnboundedSender<Wire>,
    writers: std::collections::HashMap<StreamId, UnboundedSender<Vec<u8>>>,
}

impl Streams {
    /// A registry and the receiver the host loop reads stream events from.
    pub fn new() -> (Self, UnboundedReceiver<Wire>) {
        let (events, rx) = unbounded_channel();
        (
            Self {
                events,
                writers: std::collections::HashMap::new(),
            },
            rx,
        )
    }

    /// Start the tasks of an open stream.
    pub fn adopt(&mut self, id: StreamId, stream: Handle<TcpStream>) {
        let stream = Rc::new(stream);
        let (wtx, mut wrx) = unbounded_channel::<Vec<u8>>();
        self.writers.insert(id, wtx);
        let events = self.events.clone();
        let reader = Rc::clone(&stream);
        nuclei::spawn_local(async move {
            let mut buf = vec![0u8; 16 * 1024];
            loop {
                match reader.recv(&mut buf).await {
                    Ok(n) if n > 0 => {
                        let data = buf.get(..n).map(<[u8]>::to_vec).unwrap_or_default();
                        if events.send(Wire::Ev(StreamEv::Data(id, data))).is_err() {
                            break;
                        }
                    }
                    _ => {
                        let _ = events.send(Wire::Ev(StreamEv::Closed(id)));
                        break;
                    }
                }
            }
        })
        .detach();
        nuclei::spawn_local(async move {
            while let Some(data) = wrx.recv().await {
                let mut left: &[u8] = &data;
                while !left.is_empty() {
                    match stream.send(left).await {
                        Ok(n) if n > 0 => left = left.get(n..).unwrap_or_default(),
                        _ => break,
                    }
                }
            }
            // The queue is closed: the host closed the stream, so the reader must end too.
            let _ = stream.get_ref().shutdown(std::net::Shutdown::Both);
        })
        .detach();
    }

    /// Queue bytes on a stream; false if the stream is not open.
    pub fn write(&self, id: StreamId, data: Vec<u8>) -> bool {
        self.writers.get(&id).is_some_and(|w| w.send(data).is_ok())
    }

    /// Close a stream: its writer ends, which shuts the socket down.
    pub fn close(&mut self, id: StreamId) {
        self.writers.remove(&id);
    }

    /// Forget a stream that ended on its own.
    pub fn ended(&mut self, id: StreamId) {
        self.writers.remove(&id);
    }

    /// Open a connection in a task; the host loop hears `Opened` or `Failed`.
    pub fn connect(&self, id: StreamId, to: SocketAddr) {
        let events = self.events.clone();
        nuclei::spawn_local(async move {
            let r = nuclei::net::TcpStream::connect(to).await.and_then(at_once).ok();
            let _ = events.send(Wire::Connected(id, r));
        })
        .detach();
    }

    /// Accept connections for ever; each is handed to the host loop with an id counted up from `first`.
    pub fn listen(&self, listener: TcpListener, first: StreamId) {
        let events = self.events.clone();
        nuclei::spawn_local(async move {
            let mut id = first;
            while let Ok((stream, _)) = listener.accept().await {
                // A connection that cannot be set up is dropped: its dialer sees it close and dials again.
                let Ok(stream) = at_once(stream) else { continue };
                if events.send(Wire::Accepted(id, stream)).is_err() {
                    break;
                }
                id += 1;
            }
        })
        .detach();
    }
}

/// Make a carrier connection send every write at once. A relay forwards a handshake flight or a reply as two writes
/// one behind the other; with the kernel's default the second waits for the acknowledgement of the first, a round
/// trip of the link or the peer's delayed-acknowledgement timer, on every hop.
fn at_once(stream: Handle<TcpStream>) -> io::Result<Handle<TcpStream>> {
    stream.get_ref().set_nodelay(true)?;
    Ok(stream)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    #[nuclei::test]
    async fn a_carrier_connection_sends_at_once_at_both_ends() {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let to = listener.get_ref().local_addr().unwrap();
        let (streams, mut events) = Streams::new();
        streams.listen(listener, 7);
        streams.connect(1, to);
        let (mut dialed, mut accepted) = (None, None);
        while dialed.is_none() || accepted.is_none() {
            match events.recv().await {
                Some(Wire::Connected(1, Some(s))) => dialed = s.get_ref().nodelay().ok(),
                Some(Wire::Accepted(7, s)) => accepted = s.get_ref().nodelay().ok(),
                _ => break,
            }
        }
        assert_eq!((dialed, accepted), (Some(true), Some(true)));
    }
}
