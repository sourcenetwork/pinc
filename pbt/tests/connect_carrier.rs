//! `pinc-connect` carriers: two real [`ProtectedCarrier`]s (a dialer and a listener) over a byte stream cut at
//! arbitrary points, plain (TCP) or inside WebSocket frames, with hostile bytes on the stream.
//!
//! Where the expected behaviour comes from:
//! - `carrier` (module doc, "Stream framing"): "Every unit on the stream starts with a 2-byte big-endian length ...
//!   The plaintext is one carrier frame (a batch counts as one) ... A unit longer than a record
//!   ([`session::MAX_UNIT_LEN`]) ends the carrier", and "Invariants: nothing is read or written outside the bounded
//!   buffers; a record that fails authentication ends the carrier".
//! - `carrier::session`: "[`Poll::Frame`] is never returned before [`Poll::Open`], and [`Poll::Open`] carries the
//!   node id the handshake proved"; "A record that fails authentication, a unit of the wrong size or a failed
//!   handshake ends the carrier for good: every later call that can fail returns [`CarrierError::Closed`] ...
//!   [`CarrierError::is_fatal`] is true exactly for an error the carrier ended with"; "A frame inside an
//!   authenticated record that does not decode is dropped and reported ([`CarrierError::Frame`]); the carrier stays
//!   usable"; "Packet numbers count records per direction from 0 and are never reused"; `receive`: "Buffer received
//!   stream bytes and return how many were taken ... this is the backpressure of the bounded buffer"; `free`: "How
//!   many bytes [`ProtectedCarrier::receive`] would take now".
//! - `carrier::ws`: "The carrier is a byte stream, so message boundaries carry no meaning and this codec delivers the
//!   payload of binary and continuation frames as one stream", "A client frame is masked and a server frame is not".
//!
//! Oracles: the frames that come out are the plaintexts that went in, in order, however the stream is cut and
//! whether or not it is framed (metamorphic); under a hostile edit of the stream what comes out is a prefix of what
//! went in, an error is fatal exactly when the carrier ended, and an ended carrier refuses everything after.

use std::collections::VecDeque;

use ephyra::prelude::*;
use pinc_connect::carrier::session::{self, ALPN, CarrierError, IN_LEN, MAX_UNIT_LEN, Poll, ProtectedCarrier};
use pinc_connect::carrier::ws::{self, Decoder, Opcode, Role as WsRole, WsFrame};
use pinc_connect::carrier::{BatchBuilder, Frame, MAX_FRAME_LEN, MAX_PACKET_LEN};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use pinc_pbt::mangle;
use pinc_security::{
    ConnId, CreditRecord, Env, InitiatorParams, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys,
    SoftPrekeys,
};

const NOW: u64 = 1_000_000_000_000;
/// Bounds every loop that moves bytes: far above what the largest generated exchange needs.
const TURNS: usize = 4_000;

fn big_stack(f: impl FnOnce() + Send + 'static) {
    let r = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .expect("a thread starts")
        .join();
    if let Err(e) = r {
        std::panic::resume_unwind(e);
    }
}

fn keypair(seed: u8) -> Keypair {
    Keypair::from_seed(IdentityAlg::Ed25519, &[seed; 32]).expect("a seed makes a key")
}

// ---------------------------------------------------------------------------------------------------------------
// Units

/// One sealed unit's plaintext, as the sender builds it.
#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Unit {
    Ping,
    /// A SEND frame with a packet of this length.
    Send(#[ephyra(gen = plen())] u16, u8),
    /// A batch of this many SEND frames of this length (one frame alone is sealed as itself).
    Batch(
        #[ephyra(gen = gens::int(1u8..=64))] u8,
        #[ephyra(gen = gens::pick_from(vec![1u16, 40, 200, 1452]))] u16,
    ),
    /// Bytes that are no frame: the receiver drops them and goes on.
    Garbage(#[ephyra(gen = gens::vec(gens::int(0u8..=255)).len(1..=40))] Vec<u8>),
}

fn plen() -> ephyra::BoxGen<u16> {
    let max = u16::try_from(MAX_PACKET_LEN).unwrap_or(1452);
    gens::frequency(vec![
        (3, gens::int(1u16..=max).boxed()),
        (1, gens::pick_from(vec![1u16, 2, max - 1, max]).boxed()),
    ])
    .boxed()
}

fn dst() -> NodeId {
    static ID: std::sync::OnceLock<NodeId> = std::sync::OnceLock::new();
    *ID.get_or_init(|| keypair(9).node_id())
}

fn packet(len: u16, fill: u8) -> Vec<u8> {
    // a short-header first byte, so a batch takes it
    let mut p = vec![fill; usize::from(len)];
    if let Some(b) = p.first_mut() {
        *b = 0x40 | (fill & 0x3f);
    }
    p
}

fn encode(f: &Frame<'_>) -> Vec<u8> {
    let mut b = vec![0u8; MAX_FRAME_LEN];
    let n = f.encode(&mut b).expect("a generated frame encodes");
    b.truncate(n);
    b
}

/// The plaintext of `u`.
fn plaintext(u: &Unit) -> Vec<u8> {
    match u {
        Unit::Ping => encode(&Frame::Ping),
        Unit::Send(len, fill) => encode(&Frame::Send {
            dst: dst(),
            flag: *fill,
            packet: &packet(*len, *fill),
        }),
        Unit::Batch(k, len) => {
            let mut out = vec![0u8; MAX_FRAME_LEN];
            let mut b = BatchBuilder::new(&mut out);
            for i in 0..*k {
                let p = packet(*len, i);
                // a frame that would overflow the batch is refused: the batch is sent with what it holds
                let _ = b.offer(&Frame::Send {
                    dst: dst(),
                    flag: i,
                    packet: &p,
                });
            }
            b.finish()
                .expect("a batch finishes")
                .expect("a batch holds a frame")
                .to_vec()
        }
        Unit::Garbage(g) => g.clone(),
    }
}

/// What the receiver should report for a unit with this plaintext.
fn expected(plain: &[u8]) -> Result<Vec<u8>, ()> {
    match Frame::decode(plain) {
        Ok(f) => Ok(encode(&f)),
        Err(_) => Err(()),
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The pair

struct End {
    c: Box<ProtectedCarrier<Software>>,
    kp: Keypair,
    drbg: Drbg,
    stores: ResponderStores<4, 4>,
    /// Stream bytes that arrived and the carrier has not taken yet (its backpressure).
    pending: VecDeque<u8>,
    /// WebSocket bytes that arrived and are not decoded yet.
    raw: Vec<u8>,
    dec: Decoder,
    opened: Vec<NodeId>,
    /// What came out, in order: a frame's encoding, or a dropped frame.
    frames: Vec<Result<Vec<u8>, ()>>,
    /// The first fatal error.
    ended: Option<CarrierError>,
    /// Errors reported that were not fatal and did not end the carrier.
    soft_errors: usize,
}

struct Pair {
    a: End,
    b: End,
    prekeys: SoftPrekeys<Software>,
}

fn pair() -> Pair {
    let ckp = keypair(0x31);
    let rkp = keypair(0x32);
    let mut cdrbg = Drbg::new(&[0x41; 32]);
    let cid = LocalIdentity::from_keypair(&ckp, KeyHandle(1)).expect("an identity");
    let rid = LocalIdentity::from_keypair(&rkp, KeyHandle(1)).expect("an identity");
    let mut env = Env {
        provider: &Software,
        now: NOW,
        drbg: &mut cdrbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).expect("prekeys");
    let prekey = prekeys.acquire(&mut env).expect("a prekey");
    let c = ProtectedCarrier::dial(
        &mut env,
        InitiatorParams {
            peer: rkp.node_id(),
            alpn: ALPN,
            scid: ConnId::new(b"client00").expect("a connection id"),
            identity: &cid,
            prekey: &prekey,
            peer_has_prekey: false,
            ticket: None,
            credit: CreditRecord::NONE,
        },
    )
    .expect("a dialer starts");
    let r = ProtectedCarrier::accept(
        session::responder_config(rid, ConnId::new(b"relay000").expect("a connection id")).expect("a config"),
    );
    let end = |c, kp, seed, peer| End {
        c: Box::new(c),
        kp,
        drbg: Drbg::new(&[seed; 32]),
        stores: ResponderStores::default(),
        pending: VecDeque::new(),
        raw: Vec::new(),
        dec: Decoder::new(peer),
        opened: Vec::new(),
        frames: Vec::new(),
        ended: None,
        soft_errors: 0,
    };
    // `a` dials (a WebSocket client: masks, decodes server frames); `b` accepts
    Pair {
        a: end(c, ckp, 0x51, WsRole::Server),
        b: end(r, rkp, 0x52, WsRole::Client),
        prekeys,
    }
}

impl End {
    /// Poll until the carrier has nothing more, answering key requests from software keys.
    fn poll(&mut self, prekeys: &SoftPrekeys<Software>) {
        for _ in 0..TURNS {
            if self.ended.is_some() {
                return;
            }
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &self.kp)),
                prekeys: Some(prekeys),
            };
            let mut env = Env {
                provider: &Software,
                now: NOW,
                drbg: &mut self.drbg,
            };
            let mut r = self.c.poll(&mut env, &mut self.stores).map(|p| owned(&p));
            while matches!(r, Ok(Owned::KeyRequest)) {
                r = self.c.answer_soft(&mut env, &soft).map(|p| owned(&p));
            }
            match r {
                Ok(Owned::Idle) => return,
                Ok(Owned::Handshake | Owned::KeyRequest) => {}
                Ok(Owned::Open(id)) => self.opened.push(id),
                Ok(Owned::Frame(f)) => {
                    assert!(!self.opened.is_empty(), "a frame came out before the carrier opened");
                    self.frames.push(Ok(f));
                }
                Err(e) => {
                    assert_eq!(
                        e.is_fatal(),
                        self.c.is_ended(),
                        "the error {e:?} is fatal exactly when the carrier ended"
                    );
                    if e.is_fatal() {
                        self.ended = Some(e);
                    } else {
                        assert!(
                            matches!(e, CarrierError::Frame(_)),
                            "a poll error that is not fatal is a dropped frame: {e:?}"
                        );
                        self.soft_errors += 1;
                        self.frames.push(Err(()));
                    }
                }
            }
        }
        panic!("the carrier never went idle");
    }

    /// Hand the carrier what waits, as much as it takes, polling between.
    fn drain(&mut self, prekeys: &SoftPrekeys<Software>) {
        for _ in 0..TURNS {
            self.poll(prekeys);
            if self.pending.is_empty() || self.ended.is_some() {
                return;
            }
            let free = self.c.free();
            assert!(free <= IN_LEN, "free {free} is beyond the buffer");
            let chunk: Vec<u8> = self.pending.iter().copied().take(4096).collect();
            let took = self.c.receive(&chunk);
            assert!(took <= free, "receive took {took} of {} with {free} free", chunk.len());
            self.pending.drain(..took);
            if took == 0 {
                self.poll(prekeys);
                if self.c.free() == 0 {
                    // a full buffer the carrier cannot make progress on: only a unit it waits the rest of
                    return;
                }
            }
        }
        panic!("the stream never drained");
    }

    /// Bytes of the stream arrived, framed or not.
    fn arrive(&mut self, bytes: &[u8], framed: bool) {
        if !framed {
            self.pending.extend(bytes);
            return;
        }
        self.raw.extend_from_slice(bytes);
        loop {
            let res = self.dec.decode(&mut self.raw);
            match res {
                Ok(Some((f, used))) => {
                    if let WsFrame::Data(d) = f {
                        self.pending.extend(d);
                    }
                    self.raw.drain(..used);
                }
                Ok(None) => return,
                Err(e) => panic!("a frame the other end encoded does not decode: {e:?}"),
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Owned {
    Idle,
    Handshake,
    KeyRequest,
    Open(NodeId),
    Frame(Vec<u8>),
}

fn owned(p: &Poll<'_>) -> Owned {
    match p {
        Poll::Idle => Owned::Idle,
        Poll::Handshake => Owned::Handshake,
        Poll::KeyRequest => Owned::KeyRequest,
        Poll::Open(n) => Owned::Open(*n),
        Poll::Frame(f) => Owned::Frame(encode(f)),
    }
}

/// How a byte stream is cut into reads, and how a WebSocket sender splits it into frames.
#[derive(Clone, Debug)]
struct Cuts {
    reads: Vec<usize>,
    frames: Vec<usize>,
    /// A ping between two data frames, every this many frames (0: never).
    pings: usize,
    framed: bool,
}

fn cuts() -> impl Gen<Value = Cuts> {
    let sizes = || {
        gens::vec(gens::frequency(vec![
            (3, gens::int(1usize..=8).boxed()),
            (2, gens::int(1usize..=600).boxed()),
            (
                1,
                gens::pick_from(vec![1usize, 2, 3, 17, 18, 1500, 16_400, 20_000]).boxed(),
            ),
        ]))
        .len(1..=6)
    };
    (sizes(), sizes(), gens::int(0usize..=3), gens::bool()).map(|(reads, frames, pings, framed)| Cuts {
        reads,
        frames,
        pings,
        framed,
    })
}

/// Wrap `bytes` in WebSocket frames from `from`'s side: fragments of the sizes in `frames` (a message of several
/// fragments, then the next), a ping between fragments now and then.
fn ws_wrap(bytes: &[u8], c: &Cuts, client: bool) -> Vec<u8> {
    let mask = client.then_some([0x5a, 0x17, 0xc3, 0x01]);
    let mut out = Vec::new();
    let mut at = 0;
    let mut i = 0;
    while at < bytes.len() {
        let n = c.frames[i % c.frames.len()].min(ws::MAX_PAYLOAD).min(bytes.len() - at);
        let last = at + n == bytes.len() || i % 3 == 2;
        let first = i % 3 == 0;
        let mut f = vec![0u8; n + ws::MAX_HEADER];
        let k = ws::encode(Opcode::Binary, &bytes[at..at + n], mask, &mut f).expect("a payload of a frame encodes");
        f.truncate(k);
        // fragment: the first frame of a message is binary, the rest continuation; FIN on the last
        f[0] = if first { 0x02 } else { 0x00 } | if last { 0x80 } else { 0 };
        out.extend_from_slice(&f);
        if c.pings != 0 && i % c.pings == 0 && !last {
            let mut p = vec![0u8; 2 + 4 + 4];
            let k = ws::encode(Opcode::Ping, b"ping", mask, &mut p).expect("a ping encodes");
            out.extend_from_slice(&p[..k]);
        }
        if last && !first {
            // the message ended on this fragment: the next starts a new one
            i += 3 - i % 3;
        } else if last {
            i += 3;
        } else {
            i += 1;
        }
        at += n;
    }
    out
}

/// Move what `from` has to transmit, and `extra` sealed bytes after it, to `to`, cut by `c`.
fn send(from: &mut End, to: &mut End, extra: &[u8], c: &Cuts, client: bool, prekeys: &SoftPrekeys<Software>) {
    let mut bytes = vec![0u8; session::OUT_LEN];
    let n = from.c.transmit(&mut bytes);
    bytes.truncate(n);
    bytes.extend_from_slice(extra);
    if bytes.is_empty() {
        return;
    }
    let wire = if c.framed { ws_wrap(&bytes, c, client) } else { bytes };
    let mut at = 0;
    let mut i = 0;
    while at < wire.len() {
        let n = c.reads[i % c.reads.len()].min(wire.len() - at);
        to.arrive(&wire[at..at + n], c.framed);
        to.drain(prekeys);
        at += n;
        i += 1;
    }
}

fn handshake(p: &mut Pair, c: &Cuts) {
    for _ in 0..16 {
        send(&mut p.a, &mut p.b, &[], c, true, &p.prekeys);
        send(&mut p.b, &mut p.a, &[], c, false, &p.prekeys);
        if !p.a.opened.is_empty() && !p.b.opened.is_empty() {
            break;
        }
    }
}

fn seal(e: &mut End, plain: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; MAX_UNIT_LEN + 2];
    let n =
        e.c.seal_bytes(&Software, plain, &mut out)
            .expect("an open carrier seals a unit");
    out.truncate(n);
    out
}

// ---------------------------------------------------------------------------------------------------------------
// Properties

/// The handshake opens both ends once with the right identities, and every unit either end seals comes out of the
/// other in order, the same however the stream is cut, plain or WebSocket-framed; a unit that is no frame is dropped
/// and reported and the carrier goes on.
fn stream(input: &(Cuts, Vec<(bool, Unit)>)) {
    let (c, units) = input;
    let mut p = pair();
    handshake(&mut p, c);
    let (ida, idb) = (p.a.kp.node_id(), p.b.kp.node_id());
    assert_eq!(p.a.opened, vec![idb], "the dialer opened once, to the relay it named");
    assert_eq!(
        p.b.opened,
        vec![ida],
        "the listener opened once, to the dialer's identity"
    );
    assert!(!p.b.c.is_peer_relay(), "a client asked for the client protocol");
    let (mut to_b, mut to_a) = (Vec::new(), Vec::new());
    let (mut want_b, mut want_a) = (Vec::new(), Vec::new());
    for (from_a, u) in units {
        let plain = plaintext(u);
        if *from_a {
            to_b.extend(seal(&mut p.a, &plain));
            want_b.push(expected(&plain));
        } else {
            to_a.extend(seal(&mut p.b, &plain));
            want_a.push(expected(&plain));
        }
    }
    send(&mut p.a, &mut p.b, &to_b, c, true, &p.prekeys);
    send(&mut p.b, &mut p.a, &to_a, c, false, &p.prekeys);
    assert_eq!(p.b.ended, None, "the listener's carrier ended");
    assert_eq!(p.a.ended, None, "the dialer's carrier ended");
    assert!(p.b.pending.is_empty() && p.a.pending.is_empty(), "every byte was taken");
    assert_eq!(p.b.frames, want_b, "what the listener got");
    assert_eq!(p.a.frames, want_a, "what the dialer got");
    ephyra::classify(c.framed, "websocket-framed");
    ephyra::classify(
        units.iter().any(|(_, u)| matches!(u, Unit::Garbage(_))),
        "a unit that is no frame",
    );
    ephyra::classify(units.iter().any(|(_, u)| matches!(u, Unit::Batch(..))), "a batch");
    ephyra::classify(units.len() >= 12, "12 units or more");
}

#[test]
fn the_same_frames_come_out_however_the_stream_is_cut() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(300)
            .name("the_same_frames_come_out_however_the_stream_is_cut");
        let g = (cuts(), gens::vec((gens::bool(), ephyra::any::<Unit>())).len(0..=24));
        ephyra::check(&config, g, |i: (Cuts, Vec<(bool, Unit)>)| stream(&i)).assert_passed();
    });
}

/// A hostile edit of the stream of sealed units.
#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Edit {
    /// One of the edits a broken or hostile peer makes (`pinc_pbt::mangle`), drawn from this seed.
    Mangle(u64),
    /// Unit `i` sent again after the others (a replay).
    Replay(#[ephyra(gen = gens::int(0usize..=7))] usize),
    /// Units `i` and `i + 1` swapped.
    Swap(#[ephyra(gen = gens::int(0usize..=7))] usize),
    /// A length field of 0, of one more than a unit may be, or the largest.
    Length(
        #[ephyra(gen = gens::int(0usize..=7))] usize,
        #[ephyra(gen = gens::int(0u8..=2))] u8,
    ),
}

/// The receiving end under a hostile edit: what comes out is the start of what was sent, in order, never a frame
/// that was not sent; an error is fatal exactly when the carrier ended, and an ended carrier refuses every later
/// call (`poll`, `seal`, `seal_bytes`, `key_response` return `Closed`).
fn hostile(input: &(Cuts, Vec<Unit>, Edit)) {
    let (c, units, edit) = input;
    let mut p = pair();
    handshake(&mut p, c);
    assert_eq!(p.b.opened.len(), 1, "the carrier opened");
    let sealed: Vec<Vec<u8>> = units.iter().map(|u| seal(&mut p.a, &plaintext(u))).collect();
    let want: Vec<Result<Vec<u8>, ()>> = units.iter().map(|u| expected(&plaintext(u))).collect();
    let mut stream: Vec<u8> = sealed.concat();
    match edit {
        Edit::Mangle(seed) => {
            let mut src = ephyra::Source::new(*seed, 8);
            stream = mangle(&mut src, &stream);
        }
        Edit::Replay(i) => {
            if let Some(u) = sealed.get(i % sealed.len().max(1)) {
                stream.extend_from_slice(u);
            }
        }
        Edit::Swap(i) => {
            let i = i % sealed.len().max(1);
            if i + 1 < sealed.len() {
                let mut s = sealed.clone();
                s.swap(i, i + 1);
                stream = s.concat();
            }
        }
        Edit::Length(i, which) => {
            let i = i % sealed.len().max(1);
            let at: usize = sealed.iter().take(i).map(Vec::len).sum();
            let v: u16 = match which {
                0 => 0,
                1 => u16::try_from(MAX_UNIT_LEN + 1).unwrap_or(u16::MAX),
                _ => u16::MAX,
            };
            if let Some(s) = stream.get_mut(at..at + 2) {
                s.copy_from_slice(&v.to_be_bytes());
            }
        }
    }
    let untouched = stream == sealed.concat();
    send(&mut p.a, &mut p.b, &stream, c, true, &p.prekeys);
    let got = &p.b.frames;
    assert!(
        got.len() <= want.len() || matches!(edit, Edit::Replay(_)) && p.b.ended.is_some(),
        "more came out than was sent"
    );
    assert_eq!(
        &got[..],
        &want[..got.len().min(want.len())],
        "what came out is the start of what was sent"
    );
    if untouched {
        assert_eq!(got, &want, "an untouched stream delivers everything");
    }
    ephyra::label(match &p.b.ended {
        Some(e) => format!("ended: {e:?}"),
        None => format!("open, {} of {} out", got.len(), want.len()),
    });
    if p.b.ended.is_some() {
        assert!(p.b.c.is_ended(), "a fatal error ended the carrier");
        let mut env = Env {
            provider: &Software,
            now: NOW,
            drbg: &mut p.b.drbg,
        };
        let polled = p.b.c.poll(&mut env, &mut p.b.stores).map(|x| owned(&x));
        assert_eq!(polled, Err(CarrierError::Closed), "poll after the end");
        let mut out = vec![0u8; MAX_UNIT_LEN + 2];
        assert_eq!(
            p.b.c.seal(&Software, &Frame::Ping, &mut out),
            Err(CarrierError::Closed),
            "seal after the end"
        );
        assert_eq!(
            p.b.c.seal_bytes(&Software, &[3], &mut out),
            Err(CarrierError::Closed),
            "seal_bytes after the end"
        );
        let kr =
            p.b.c
                .key_response(&mut env, pinc_security::KeyResponse::Failed)
                .map(|x| owned(&x));
        assert_eq!(kr, Err(CarrierError::Closed), "key_response after the end");
    }
}

#[test]
fn a_hostile_stream_delivers_only_what_was_sent_and_an_ended_carrier_stays_closed() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(300)
            .name("a_hostile_stream_delivers_only_what_was_sent_and_an_ended_carrier_stays_closed");
        let g = (
            cuts(),
            gens::vec(ephyra::any::<Unit>()).len(1..=8),
            ephyra::any::<Edit>(),
        );
        ephyra::check(&config, g, |i: (Cuts, Vec<Unit>, Edit)| hostile(&i)).assert_passed();
    });
}

/// `carrier` (module doc): "A unit longer than a record ([`session::MAX_UNIT_LEN`]) ends the carrier", and
/// `session`: a unit of the wrong size "ends the carrier for good". The length is refused on its own two bytes,
/// before any of the unit is buffered: the units before it come out, the carrier ends with `UnitSize`, and it takes
/// no byte after.
fn oversized(input: &(Vec<Unit>, u16, usize)) {
    let (units, len, tail) = input;
    let mut p = pair();
    let c = Cuts {
        reads: vec![1, 7, 300],
        frames: vec![1],
        pings: 0,
        framed: false,
    };
    handshake(&mut p, &c);
    let mut stream: Vec<u8> = units.iter().flat_map(|u| seal(&mut p.a, &plaintext(u))).collect();
    let want: Vec<Result<Vec<u8>, ()>> = units.iter().map(|u| expected(&plaintext(u))).collect();
    stream.extend_from_slice(&len.to_be_bytes());
    p.b.arrive(&stream, false);
    p.b.drain(&p.prekeys);
    assert_eq!(p.b.frames, want, "the units before the length came out");
    assert_eq!(
        p.b.ended,
        Some(CarrierError::UnitSize),
        "the length {len} ended the carrier on its two bytes"
    );
    assert!(p.b.pending.is_empty(), "the carrier took the two bytes");
    // `receive` cannot fail, so the doc lets it take bytes after the end: what it takes never comes out
    let late: Vec<u8> = (0..*tail)
        .flat_map(|_| seal(&mut p.a, &plaintext(&Unit::Ping)))
        .collect();
    p.b.c.receive(&late);
    let mut env = Env {
        provider: &Software,
        now: NOW,
        drbg: &mut p.b.drbg,
    };
    let polled = p.b.c.poll(&mut env, &mut p.b.stores).map(|x| owned(&x));
    assert_eq!(
        polled,
        Err(CarrierError::Closed),
        "a unit after the end never comes out"
    );
}

#[test]
fn a_unit_length_out_of_range_ends_the_carrier_on_its_two_bytes() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(300)
            .name("a_unit_length_out_of_range_ends_the_carrier_on_its_two_bytes");
        let over = u16::try_from(MAX_UNIT_LEN + 1).unwrap_or(u16::MAX);
        // an offset above the limit, so every shrink stays out of range (0 drawn apart)
        let len =
            (gens::bool_with(0.1), gens::int(0u16..=u16::MAX - over)).map(move |(z, k)| if z { 0 } else { over + k });
        let g = (gens::vec(ephyra::any::<Unit>()).len(0..=6), len, gens::int(1usize..=8));
        ephyra::check(&config, g, |i: (Vec<Unit>, u16, usize)| oversized(&i)).assert_passed();
    });
}
