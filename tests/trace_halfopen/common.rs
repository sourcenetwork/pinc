//! The shared parts of the half-open trace: the table sizes, the endpoint builder, the crafted first flights and the
//! readers of a datagram.

use std::net::SocketAddr;

use pinc_core::{Endpoint, EndpointConfig, HALF_OPEN_HOLD, HALF_OPEN_LIFE, MAX_HALF_OPEN, Slot};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use pinc_security::message::{FULL_INITIAL_MIN, RESUME_HELLO_MIN, SHORT_INITIAL_MIN};
use pinc_security::{ConnId, KeyHandle, LocalIdentity};
use pinc_tests::*;
use pinc_transport::conn::{Resources, Tables};
use pinc_transport::packet::{LongHeader, LongType};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{self, NoSource, Streams};
use pinc_wire::{Reader, Writer};

pub const LIFE: u64 = HALF_OPEN_LIFE;
pub const HOLD: u64 = HALF_OPEN_HOLD;
pub const MAX: usize = MAX_HALF_OPEN;
/// The most sessions that may hold one id (`MAX_CANDIDATES` in `rx.rs`, private to the crate): a first flight for an id
/// that this many hold is dropped.
pub const HOLDERS: u64 = 4;
/// The table of the big endpoint: room past the cap, so the cap and not the table refuses.
pub const BK: usize = MAX_HALF_OPEN + 44;
/// The table of the small endpoint: full long before the cap.
pub const SK: usize = 8;

pub type Ep<const K: usize, const D: usize> = Endpoint<'static, 'static, Caps, NoSource, 1, 2, 16, 1, K, D, 4, 4, 2>;
pub type TSlot = Slot<'static, Caps, NoSource, 1, 2, 16, 1>;

pub fn small_memory() -> Resources<'static, NoSource, 1, 2, 16> {
    let pool = BufferPool::new_boxed(4);
    let streams: &'static mut Streams<NoSource, 1, 2> =
        Box::leak(Box::new(Streams::new(&stream::Config::new(false), &pool)));
    Resources {
        pool,
        streams: streams.into(),
        loss: (&*Box::leak(Box::new(LossEstimate::new()))).into(),
        tables: Tables::new(),
    }
}

pub fn server<const K: usize, const D: usize>(now: u64) -> (Box<Ep<K, D>>, SocketAddr) {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let v: Vec<TSlot> = (0..K).map(|_| Slot::new(small_memory())).collect();
    let slots: Box<[TSlot; K]> = v.into_boxed_slice().try_into().ok().unwrap();
    let mut ep = Box::new(Endpoint::new(
        now,
        Caps(Software, true),
        Drbg::new(&[3; 32]),
        id,
        EndpointConfig::new(5),
        Box::leak(slots),
    ));
    assert!(ep.register_alpn(ALPN_A));
    let addr: SocketAddr = "10.0.0.1:4433".parse().unwrap();
    ep.add_iface(addr).unwrap();
    (ep, addr)
}

/// A long handshake datagram of exactly `len` bytes for `odcid` whose message (of 4095 bytes) starts at `off` with
/// `kind`, then `salt`.
pub fn craft(odcid: u64, kind: u8, len: usize, off: u64, salt: u8) -> Vec<u8> {
    let mut d = vec![0u8; len];
    let mut h = LongHeader {
        ty: LongType::Handshake,
        dcid: ConnId::new(&odcid.to_be_bytes()).unwrap(),
        scid: ConnId::new(&[1, 2, 3, 4]).unwrap(),
        body_len: 0,
    };
    for _ in 0..3 {
        h.body_len = len - h.header_len();
    }
    let mut w = Writer::new(&mut d);
    h.write(&mut w, 0).unwrap();
    w.put_varint(4095).unwrap();
    w.put_varint(off).unwrap();
    w.put_u8(kind).unwrap();
    w.put_u8(salt).unwrap();
    d
}

/// The message type of a datagram whose first packet is a long Handshake packet that starts a message (offset 0, a
/// length above 0), 1 to 8; 0 for any other datagram (a later part, another packet, garbage, an unknown type byte).
pub fn kind_of(buf: &[u8]) -> u8 {
    let Ok((h, hlen)) = LongHeader::parse(buf) else {
        return 0;
    };
    if h.ty != LongType::Handshake {
        return 0;
    }
    let Some(body) = hlen.checked_add(h.body_len).and_then(|e| buf.get(hlen..e)) else {
        return 0;
    };
    let mut r = Reader::new(body);
    let (Ok(total), Ok(off)) = (r.read_varint(), r.read_varint()) else {
        return 0;
    };
    if off != 0 || total == 0 {
        return 0;
    }
    r.read_bytes(r.remaining())
        .ok()
        .and_then(|d| d.first().copied())
        .filter(|b| (1..=8).contains(b))
        .unwrap_or_default()
}

/// The size floor of a first message type, `None` for a type that starts no session.
pub const fn floor(kind: u8) -> Option<usize> {
    match kind {
        1 => Some(FULL_INITIAL_MIN),
        2 => Some(SHORT_INITIAL_MIN),
        6 => Some(RESUME_HELLO_MIN),
        _ => None,
    }
}

pub fn source(i: u64) -> SocketAddr {
    SocketAddr::from(([10, 1, (i >> 8) as u8, i as u8], 9))
}
