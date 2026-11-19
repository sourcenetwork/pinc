//! A relay on real sockets, on nuclei: one UDP socket and one TCP listener on the same address.
//!
//! Run with `cargo run -p pinc --example relay -- 0.0.0.0:4433 <64 hex digits of the identity seed> [protocol...]`.
//! Each argument after the seed is either `<node id>@<tcp address>`, a peer relay this relay joins (the relay with the lower
//! node id dials the other and keeps the carrier up; a relay never peers with itself, so every relay can be given the same
//! list), or a protocol name accepted on the hub (UDP sessions that members tunnel through).
//!
//! The listener serves two kinds of members on one port, told apart by the first bytes: a raw PINC carrier over TCP,
//! and a WebSocket carrier. The WebSocket upgrade is done here in a few lines: it accepts a `GET` request with a
//! `Sec-WebSocket-Key` header and answers 101; it checks no other header, serves no other path and does not speak TLS.
//! A browser needs TLS in front of this port (a reverse proxy); that is out of scope. The upgrade runs inside the
//! accept, one stream at a time, with a five second bound.

#![allow(
    missing_docs,
    clippy::missing_errors_doc,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::too_many_lines,
    reason = "an example favours the short form"
)]

use std::cell::RefCell;
use std::collections::VecDeque;
use std::io;
use std::net::{Shutdown, SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::rc::Rc;
use std::task::{Context, Poll, Waker};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use nuclei::Handle;
use nuclei::time::{sleep_until_precise, timeout};

use pinc::relay::{Carriers, Clock, Completion, Done, Peer, Relay, Tag, Udp};
use pinc::{CarrierKind, Error, ErrorKind, Identity};

type Stream = Handle<TcpStream>;

fn io_err(_: io::Error) -> Error {
    Error::new(ErrorKind::Unreachable, "the socket failed")
}

fn sha1(data: &[u8]) -> [u8; 20] {
    let mut h: [u32; 5] = [0x6745_2301, 0xEFCD_AB89, 0x98BA_DCFE, 0x1032_5476, 0xC3D2_E1F0];
    let mut msg = data.to_vec();
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&((data.len() as u64) * 8).to_be_bytes());
    for block in msg.chunks(64) {
        let mut w = [0u32; 80];
        for (i, c) in block.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes([c[0], c[1], c[2], c[3]]);
        }
        for i in 16..80 {
            w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
        }
        let [mut a, mut b, mut c, mut d, mut e] = h;
        for (i, wi) in w.iter().enumerate() {
            let (f, k) = match i {
                0..=19 => ((b & c) | (!b & d), 0x5A82_7999),
                20..=39 => (b ^ c ^ d, 0x6ED9_EBA1),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8F1B_BCDC),
                _ => (b ^ c ^ d, 0xCA62_C1D6),
            };
            let t = a
                .rotate_left(5)
                .wrapping_add(f)
                .wrapping_add(e)
                .wrapping_add(k)
                .wrapping_add(*wi);
            (e, d, c, b, a) = (d, c, b.rotate_left(30), a, t);
        }
        for (x, y) in h.iter_mut().zip([a, b, c, d, e]) {
            *x = x.wrapping_add(y);
        }
    }
    let mut out = [0u8; 20];
    for (o, x) in out.chunks_mut(4).zip(h) {
        o.copy_from_slice(&x.to_be_bytes());
    }
    out
}

fn base64(bytes: &[u8]) -> String {
    const T: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut s = String::new();
    for c in bytes.chunks(3) {
        let n = u32::from(c[0]) << 16 | u32::from(*c.get(1).unwrap_or(&0)) << 8 | u32::from(*c.get(2).unwrap_or(&0));
        for i in 0..4 {
            if i <= c.len() {
                s.push(char::from(T[(n >> (18 - 6 * i) & 63) as usize]));
            } else {
                s.push('=');
            }
        }
    }
    s
}

/// Read the upgrade request byte by byte (so no frame bytes are consumed) and answer 101.
async fn upgrade(s: &Stream) -> io::Result<()> {
    let mut req = Vec::new();
    let mut b = [0u8; 1];
    while !req.ends_with(b"\r\n\r\n") {
        if req.len() > 8192 || s.recv(&mut b).await? == 0 {
            return Err(io::ErrorKind::InvalidData.into());
        }
        req.push(b[0]);
    }
    let text = String::from_utf8_lossy(&req);
    let key = text
        .lines()
        .find_map(|l| {
            let (n, v) = l.split_once(':')?;
            n.eq_ignore_ascii_case("sec-websocket-key").then(|| v.trim().to_owned())
        })
        .filter(|_| text.starts_with("GET "))
        .ok_or(io::ErrorKind::InvalidData)?;
    let accept = base64(&sha1(format!("{key}258EAFA5-E914-47DA-95CA-C5AB0DC85B11").as_bytes()));
    let resp = format!(
        "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: {accept}\r\n\r\n"
    );
    let mut sent = 0;
    while sent < resp.len() {
        sent += s.send(&resp.as_bytes()[sent..]).await?;
    }
    Ok(())
}

async fn accept_one(listener: &Handle<TcpListener>) -> Result<(Stream, CarrierKind), Error> {
    loop {
        let (s, _) = listener.accept().await.map_err(io_err)?;
        // Every write leaves at once: a frame behind another must not wait for the first one's acknowledgement.
        s.get_ref().set_nodelay(true).map_err(io_err)?;
        let mut first = [0u8; 4];
        let seen = timeout(Duration::from_secs(5), s.peek(&mut first)).await;
        match seen {
            Ok(Ok(4)) if &first == b"GET " => {
                if matches!(timeout(Duration::from_secs(5), upgrade(&s)).await, Ok(Ok(()))) {
                    return Ok((s, CarrierKind::Ws));
                }
            }
            Ok(Ok(n)) if n > 0 => return Ok((s, CarrierKind::Tcp)),
            _ => {}
        }
    }
}

/// The relay's carriers on nuclei, in the completion form: each operation the relay submits becomes a task of this
/// thread, and its result goes on a queue the relay reads. This is all a host writes; the relay does O(1) work for each
/// result however many streams are idle.
#[derive(Clone)]
struct Io {
    listener: Rc<Handle<TcpListener>>,
    done: Rc<RefCell<VecDeque<Completion<Stream>>>>,
    waker: Rc<RefCell<Option<Waker>>>,
}

impl Io {
    fn new(listener: Rc<Handle<TcpListener>>) -> Self {
        Self {
            listener,
            done: Rc::default(),
            waker: Rc::default(),
        }
    }

    /// Run `op` as a task; its result is the completion of `tag`.
    fn spawn(&self, tag: Tag, op: impl Future<Output = Done<Stream>> + 'static) {
        let io = self.clone();
        nuclei::spawn_local(async move {
            let done = op.await;
            io.done.borrow_mut().push_back(Completion { tag, done });
            if let Some(w) = io.waker.borrow_mut().take() {
                w.wake();
            }
        })
        .detach();
    }
}

impl Carriers for Io {
    type Stream = Stream;

    fn submit_accept(&self, tag: Tag) {
        let l = Rc::clone(&self.listener);
        self.spawn(tag, async move { Done::Accepted(accept_one(&l).await) });
    }

    fn submit_open(&self, tag: Tag, peer: &Peer, _kind: CarrierKind) {
        let to = peer.tcp;
        self.spawn(tag, async move {
            Done::Opened(match to {
                Some(to) => Handle::<TcpStream>::connect(to)
                    .await
                    .and_then(|s| s.get_ref().set_nodelay(true).map(|()| s))
                    .map_err(io_err),
                None => Err(Error::new(
                    ErrorKind::Unreachable,
                    "the example dials TCP carriers only",
                )),
            })
        });
    }

    fn submit_read(&self, stream: &Rc<Stream>, tag: Tag, mut buf: Vec<u8>) {
        let s = Rc::clone(stream);
        self.spawn(tag, async move {
            let r = s.recv(&mut buf).await.map_err(io_err);
            Done::Read(r, buf)
        });
    }

    fn submit_write(&self, stream: &Rc<Stream>, tag: Tag, buf: Vec<u8>, from: usize) {
        let s = Rc::clone(stream);
        self.spawn(tag, async move {
            let r = s.send(&buf[from..]).await.map_err(io_err);
            Done::Written(r, buf)
        });
    }

    fn close(&self, _tag: Tag, stream: Rc<Stream>) {
        // ends the operations still in flight on the stream: they fail, and the relay ignores their completions
        let _ = stream.get_ref().shutdown(Shutdown::Both);
    }

    fn poll_completed(&self, cx: &mut Context<'_>) -> Poll<Completion<Stream>> {
        if let Some(c) = self.done.borrow_mut().pop_front() {
            return Poll::Ready(c);
        }
        *self.waker.borrow_mut() = Some(cx.waker().clone());
        Poll::Pending
    }

    fn drive(&self) -> impl Future<Output = ()> {
        std::future::pending()
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let (Some(addr), Some(seed)) = (args.next(), args.next()) else {
        return Err("usage: relay <address> <64 hex digits of the identity seed>".into());
    };
    let (peers, protocols): (Vec<String>, Vec<String>) = args.partition(|a| a.contains('@'));
    let mut listed = Vec::new();
    for p in &peers {
        let (id, at) = p.split_once('@').ok_or("a peer is <node id>@<tcp address>")?;
        listed.push(Peer::new(pinc::node_from_str(id)?).with_tcp(at.parse()?));
    }
    let addr: SocketAddr = addr.parse()?;
    let mut bytes = [0u8; 32];
    if seed.len() != 64 {
        return Err("the identity seed is 64 hex digits".into());
    }
    for (b, h) in bytes.iter_mut().zip(seed.as_bytes().chunks(2)) {
        *b = u8::from_str_radix(std::str::from_utf8(h)?, 16)?;
    }
    nuclei::block_on(async move {
        let sock = Rc::new(Handle::<UdpSocket>::bind(addr).await?);
        let listener = Rc::new(Handle::<TcpListener>::bind(addr).await?);
        let (s1, s2) = (Rc::clone(&sock), Rc::clone(&sock));
        let t0 = Instant::now();
        let base = u64::try_from(SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos())?;
        let alpns: Vec<&[u8]> = protocols.iter().map(String::as_bytes).collect();
        let mut builder = Relay::builder().identity(Identity::from_seed(&bytes)?);
        for p in listed {
            builder = builder.peer(p);
        }
        if !alpns.is_empty() {
            builder = builder.hub(sock.get_ref().local_addr()?, &alpns);
        }
        let relay = builder.build(
            Udp::new(
                async move |buf: &mut [u8]| s1.recv_from(buf).await.map_err(io_err),
                async move |pkt: &[u8], to| s2.send_to(pkt, to).await.map_err(io_err),
            ),
            Io::new(Rc::clone(&listener)),
            Clock::new(
                move || base.saturating_add(u64::try_from(t0.elapsed().as_nanos()).unwrap_or(u64::MAX)),
                async move |at: u64| sleep_until_precise(t0 + Duration::from_nanos(at.saturating_sub(base))).await,
            ),
        )?;
        println!("relay {} on {addr}", pinc::node_to_string(&relay.node_id()));
        let watch = relay.clone();
        nuclei::spawn_local(async move {
            loop {
                nuclei::time::sleep(Duration::from_secs(1)).await;
                while let Some(e) = watch.next_event() {
                    println!("{e:?}");
                }
            }
        })
        .detach();
        relay.run().await?;
        Ok::<(), Box<dyn std::error::Error>>(())
    })
}
