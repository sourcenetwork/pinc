//! A member of a relay for the tests: the carrier handshake and frames over a real TCP stream, with optional WebSocket
//! framing, written with the carrier state machine of `vinc-connect` and nothing of the facade.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    dead_code,
    clippy::needless_continue,
    unreachable_pub,
    missing_docs
)]

use std::cell::RefCell;
use std::collections::VecDeque;
use std::net::{SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::rc::Rc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use nuclei::Handle;
use vinc::relay::{CarrierFns, Clock, Hosted, Peer, Relay, Udp};
use vinc::{CarrierKind, Error, ErrorKind};
use vinc_connect::carrier::session::Poll;
use vinc_connect::carrier::ws::{self, Decoder, Opcode, Role, WsFrame};
use vinc_connect::carrier::{Frame, MAX_FRAME_LEN, ProtectedCarrier};
use vinc_connect::record::{self, Reach, RecordFields};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use vinc_security::{
    ConnId, CreditRecord, Env, InitiatorParams, KeyHandle, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys,
};

pub fn wall_ns() -> u64 {
    u64::try_from(SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()).unwrap()
}

/// The dialing carrier and its key material; a function of its own so the large values live in its frame only.
#[inline(never)]
fn dial_carrier(
    kp: &Keypair,
    seed: &[u8; 32],
    relay: NodeId,
    alpn: &'static [u8],
) -> (Box<ProtectedCarrier<Software>>, Drbg, Box<SoftPrekeys<Software>>) {
    let identity = LocalIdentity::from_keypair(kp, KeyHandle(1)).unwrap();
    let mut drbg = Drbg::new(&seed.map(|b| b ^ 0x55));
    let prov = Software;
    let mut env = Env {
        provider: &prov,
        now: wall_ns(),
        drbg: &mut drbg,
    };
    let mut prekeys = Box::new(SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap());
    let prekey = prekeys.acquire(&mut env).unwrap();
    let carrier = Box::new(
        ProtectedCarrier::dial(
            &mut env,
            InitiatorParams {
                peer: relay,
                alpn,
                scid: ConnId::new(seed.first_chunk::<8>().unwrap()).unwrap(),
                identity: &identity,
                prekey: &prekey,
                peer_has_prekey: false,
                ticket: None,
                credit: CreditRecord::NONE,
            },
        )
        .unwrap(),
    );
    (carrier, drbg, prekeys)
}

/// A member: the carrier handshake and frames over a real TCP stream, with optional WebSocket framing.
pub struct Member {
    pub kp: Keypair,
    pub id: NodeId,
    relay: NodeId,
    stream: Handle<TcpStream>,
    carrier: Box<ProtectedCarrier<Software>>,
    drbg: Drbg,
    stores: Box<vinc_security::ResponderStores<4, 4>>,
    ws: Option<Decoder>,
    ws_in: Vec<u8>,
    eof: bool,
}

impl Member {
    /// Connect to the relay `relay` at `addr` with the carrier protocol name of a member (`ALPN`) or of a peer relay
    /// (`PEER_ALPN`); `kind` says how the member frames its bytes.
    pub async fn connect_to(
        addr: SocketAddr,
        relay: NodeId,
        seed: [u8; 32],
        kind: CarrierKind,
        alpn: &'static [u8],
    ) -> Self {
        Self::connect_prefixed(addr, relay, seed, kind, alpn, &[]).await
    }

    /// Like [`Member::connect_to`], with `prefix` sent first on the stream (a host may read a byte before the carrier).
    pub async fn connect_prefixed(
        addr: SocketAddr,
        relay: NodeId,
        seed: [u8; 32],
        kind: CarrierKind,
        alpn: &'static [u8],
        prefix: &[u8],
    ) -> Self {
        let stream = Handle::<TcpStream>::connect(addr).await.unwrap();
        let mut sent = 0;
        while sent < prefix.len() {
            sent += stream.send(&prefix[sent..]).await.unwrap();
        }
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &seed).unwrap();
        let (carrier, drbg, prekeys) = dial_carrier(&kp, &seed, relay, alpn);
        let mut m = Self {
            id: kp.node_id(),
            kp,
            relay,
            stream,
            carrier,
            drbg,
            stores: Box::default(),
            ws: (kind == CarrierKind::Ws).then(|| Decoder::new(Role::Server)),
            ws_in: Vec::new(),
            eof: false,
        };
        m.handshake(&prekeys).await;
        m
    }

    async fn write_all(&self, bytes: &[u8]) {
        let wrapped;
        let bytes = if self.ws.is_some() {
            let mut f = vec![0u8; bytes.len() + ws::MAX_HEADER];
            let n = ws::encode(Opcode::Binary, bytes, Some([1, 2, 3, 4]), &mut f).unwrap();
            f.truncate(n);
            wrapped = f;
            &wrapped[..]
        } else {
            bytes
        };
        let mut sent = 0;
        while sent < bytes.len() {
            sent += self.stream.send(&bytes[sent..]).await.unwrap();
        }
    }

    pub async fn flush(&mut self) {
        let mut buf = vec![0u8; 32 * 1024];
        while self.carrier.pending_transmit() > 0 {
            let n = self.carrier.transmit(&mut buf);
            self.write_all(&buf[..n]).await;
        }
    }

    /// Read from the stream into the carrier; false at end of stream.
    pub async fn fill(&mut self) -> bool {
        let mut buf = vec![0u8; 16 * 1024];
        let n = match self.stream.recv(&mut buf).await {
            Ok(n) if n > 0 => n,
            _ => {
                self.eof = true;
                return false;
            }
        };
        let mut payloads: Vec<Vec<u8>> = Vec::new();
        if let Some(dec) = self.ws.as_mut() {
            self.ws_in.extend_from_slice(&buf[..n]);
            let mut pos = 0;
            while let Ok(Some((frame, used))) = dec.decode(&mut self.ws_in[pos..]) {
                if let WsFrame::Data(p) = frame {
                    payloads.push(p.to_vec());
                }
                pos += used;
            }
            self.ws_in.drain(..pos);
        } else {
            payloads.push(buf[..n].to_vec());
        }
        for p in payloads {
            let mut rest = &p[..];
            while !rest.is_empty() {
                let used = self.carrier.receive(rest);
                rest = &rest[used..];
                if used == 0 {
                    break;
                }
                // make room: the caller polls between fills, and a unit is far below the buffer
            }
        }
        true
    }

    pub async fn handshake(&mut self, prekeys: &SoftPrekeys<Software>) {
        loop {
            self.flush().await;
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &self.kp)),
                prekeys: Some(prekeys),
            };
            let prov = Software;
            let mut env = Env {
                provider: &prov,
                now: wall_ns(),
                drbg: &mut self.drbg,
            };
            if self.carrier.key_request().is_some() {
                if let Poll::Open(_) = self.carrier.answer_soft(&mut env, &soft).unwrap() {
                    self.flush().await;
                    return;
                }
                continue;
            }
            let pr = self.carrier.poll(&mut env, &mut self.stores).unwrap();
            match pr {
                Poll::Open(peer) => {
                    assert_eq!(peer, self.relay, "the relay proved its identity");
                    return;
                }
                Poll::KeyRequest => {
                    if let Poll::Open(_) = self.carrier.answer_soft(&mut env, &soft).unwrap() {
                        self.flush().await;
                        return;
                    }
                }
                Poll::Handshake | Poll::Frame(_) => {}
                Poll::Idle => {
                    self.flush().await;
                    assert!(self.fill().await, "the relay closed during the handshake");
                }
            }
        }
    }

    pub async fn send(&mut self, f: &Frame<'_>) {
        let mut out = vec![0u8; MAX_FRAME_LEN + 64];
        let n = self.carrier.seal(&Software, f, &mut out).unwrap();
        self.write_all(&out[..n]).await;
    }

    /// The next frame, encoded; `None` once the relay closed the stream.
    pub async fn recv(&mut self) -> Option<Vec<u8>> {
        loop {
            let prov = Software;
            let mut env = Env {
                provider: &prov,
                now: wall_ns(),
                drbg: &mut self.drbg,
            };
            match self.carrier.poll(&mut env, &mut self.stores) {
                Ok(Poll::Frame(f)) => {
                    let mut b = vec![0u8; MAX_FRAME_LEN];
                    let n = f.encode(&mut b).unwrap();
                    b.truncate(n);
                    return Some(b);
                }
                Ok(Poll::Idle) | Err(_) if !self.eof => {
                    if !self.fill().await {
                        continue;
                    }
                }
                _ => return None,
            }
        }
    }

    pub fn record(&self, seq: u64) -> Vec<u8> {
        let mut out = vec![0u8; record::MAX_RECORD_LEN];
        let n = record::sign(
            &self.kp,
            &RecordFields {
                home: self.relay,
                seq,
                reach: Reach::UdpBlocked,
                addrs: &[],
                hints: &[],
            },
            &mut out,
        )
        .unwrap();
        out.truncate(n);
        out
    }

    pub async fn publish(&mut self, seq: u64) -> Vec<u8> {
        let rec = self.record(seq);
        self.send(&Frame::Publish { record: &rec }).await;
        rec
    }
}

pub fn decode(bytes: &[u8]) -> Frame<'_> {
    Frame::decode(bytes).unwrap()
}

/// Run `make`'s future on the nuclei runtime in a thread with a large stack: the handshake types of the dialing side
/// are generic over the provider and so are built unoptimised here, with frames far larger than a test thread's.
pub fn on_big_stack<F: Future<Output = ()> + 'static>(make: impl FnOnce() -> F + Send + 'static) {
    on_stack(256 << 20, make);
}

/// Run `make`'s future on the nuclei runtime in a thread of `bytes` of stack, and fail the test if it panics.
pub fn on_stack<F: Future<Output = ()> + 'static>(bytes: usize, make: impl FnOnce() -> F + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(bytes)
        .spawn(move || nuclei::block_on(make()))
        .unwrap()
        .join()
        .unwrap();
}

pub fn io_err(_: std::io::Error) -> Error {
    Error::new(ErrorKind::Unreachable, "the socket failed")
}

/// The sockets of a relay on loopback; a restarted relay is built on the same ones, so its address stays.
#[derive(Clone)]
pub struct Ports {
    pub listener: Rc<Handle<TcpListener>>,
    pub sock: Rc<Handle<UdpSocket>>,
    pub addr: SocketAddr,
}

pub async fn bind_ports() -> Ports {
    // the UDP port of the same number may be taken by another test process: try another number
    for _ in 0..50 {
        let listener = Rc::new(Handle::<TcpListener>::bind(crate::vinc_common::lo()).await.unwrap());
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

/// Build the relay `builder` describes over `ports`: its members' carriers arrive on the listener with the kind
/// taken from the front of `kinds` (TCP when it is empty), and its clock starts at the wall clock.
pub fn build_relay(
    ports: &Ports,
    kinds: &Rc<RefCell<VecDeque<CarrierKind>>>,
    builder: vinc::relay::Builder,
) -> Relay<impl Hosted + use<>> {
    let t0 = Instant::now();
    let base = wall_ns();
    let (k, l) = (Rc::clone(kinds), Rc::clone(&ports.listener));
    let (s1, s2) = (Rc::clone(&ports.sock), Rc::clone(&ports.sock));
    builder
        .build(
            Udp::new(
                async move |buf: &mut [u8]| s1.recv_from(buf).await.map_err(io_err),
                async move |pkt: &[u8], to| s2.send_to(pkt, to).await.map_err(io_err),
            ),
            CarrierFns::new(
                async move || {
                    let (s, _) = l.accept().await.map_err(io_err)?;
                    let kind = k.borrow_mut().pop_front().unwrap_or(CarrierKind::Tcp);
                    Ok((s, kind))
                },
                async |p: &Peer, _kind: CarrierKind| {
                    let to = p
                        .tcp
                        .ok_or_else(|| Error::new(ErrorKind::Unreachable, "the peer has no address"))?;
                    Handle::<TcpStream>::connect(to).await.map_err(io_err)
                },
                async |s: &Handle<TcpStream>, mut buf: Vec<u8>| {
                    let r = s.recv(&mut buf).await.map_err(io_err);
                    (r, buf)
                },
                async |s: &Handle<TcpStream>, buf: Vec<u8>, from: usize| {
                    let r = s.send(&buf[from..]).await.map_err(io_err);
                    (r, buf)
                },
                async |_s: Handle<TcpStream>| {},
            ),
            Clock::new(
                move || base + u64::try_from(t0.elapsed().as_nanos()).unwrap(),
                async move |at: u64| {
                    nuclei::time::sleep_until_precise(t0 + Duration::from_nanos(at.saturating_sub(base))).await;
                },
            ),
        )
        .unwrap()
}
