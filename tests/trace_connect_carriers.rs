//! Trace generation for a relay slot's carrier (`client/carriers.rs`): the real `Connectivity` driven through its public
//! API with a one-relay configuration, a host that keeps the stream contract and a responder of the protected carrier
//! on the other end of every stream. Eight fixed runs and 40 seeded ones are recorded as ndjson
//! (`connect_carriers.ndjson`) for the TLA+ trace check (`TraceConnectCarriers.tla`).
//!
//! After every call the test reads the link state, the generation, the stream requests and the carrier notices of
//! relay 0, and the ids of the packets the responder decoded. On its own it asserts that the generation grows once
//! per stream request, that `CarrierUp` and `CarrierDown` alternate and match the link, and that every packet
//! reaches a responder at most once (and, in the fixed runs, in the order it was routed). Where the code differs
//! from its documentation (a very slow node sends a newly routed packet before the held ones) the trace records what
//! the code does and the order is not asserted.
//! The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::struct_excessive_bools,
    unreachable_pub,
    clippy::manual_is_multiple_of
)]

mod connect_common;

use core::net::SocketAddr;

use connect_common::{SEC, big_stack, ed, id, nid};
use pinc_connect::carrier::Frame;
use pinc_connect::carrier::session::{self, Poll, ProtectedCarrier};
use pinc_connect::client::link::State;
use pinc_connect::client::queue::QUEUED;
use pinc_connect::client::{Config, Connectivity, Io, Kind, Notice, RelayCfg};
use pinc_crypto::{Drbg, Keypair, Software};
use pinc_security::{
    ConnId, Env, KeyHandle as SecHandle, KeyRequest, KeyResponse, LocalIdentity, ResponderStores, SoftKeys,
};
use pinc_tests::{Answer, Host, SplitMix64};

const MS: u64 = 1_000_000;
const TCP: &str = "203.0.113.10:443";
const WS: &str = "203.0.113.10:8443";

type Conn = Connectivity<Software, 1, 4>;

/// An answer that owns its bytes.
enum Ans {
    Sig(Vec<u8>),
    Secret(pinc_crypto::Secret<32>),
}

impl Ans {
    fn response(&self) -> KeyResponse<'_> {
        match self {
            Self::Sig(s) => KeyResponse::Signature(s),
            Self::Secret(s) => KeyResponse::SharedSecret(pinc_crypto::Secret::new(*s.expose())),
        }
    }
}

/// The node's key custody, as `connect_held.rs` has it.
struct Soft(Box<Host>);

impl Soft {
    fn answer(&mut self, now: u64, req: &KeyRequest<'_>) -> Ans {
        match self.0.answer(now, req) {
            Answer::Sig(b, n) => Ans::Sig(b[..n].to_vec()),
            Answer::Secret(s) => Ans::Secret(s),
            Answer::Failed => panic!("the software keys failed"),
        }
    }
}

/// The packet `k`: 100 bytes, `[0x40, k, 0xA5 x 98]`.
fn packet(k: u8) -> Vec<u8> {
    let mut p = vec![0xA5u8; 100];
    p[0] = 0x40;
    p[1] = k;
    p
}

/// The id of a packet made by [`packet`].
fn pkt_id(p: &[u8]) -> Option<u8> {
    (p.len() == 100 && p[0] == 0x40 && p[2..].iter().all(|&b| b == 0xA5)).then(|| p[1])
}

/// The ids of the packets a frame carries, a batch walked frame by frame.
fn ids_of(f: &Frame<'_>, out: &mut Vec<u8>) {
    match f {
        Frame::Send { packet, .. } | Frame::SendNew { packet, .. } | Frame::SendAlias { packet, .. } => {
            out.extend(pkt_id(packet));
        }
        Frame::Batch(b) => b.frames().for_each(|f| ids_of(&f, out)),
        _ => {}
    }
}

/// The relay side of one stream.
struct Resp {
    c: Box<ProtectedCarrier<Software>>,
    stores: ResponderStores<2, 2>,
    kp: Keypair,
}

impl Resp {
    fn new(tag: u8) -> Self {
        let kp = ed(tag);
        let cfg = session::responder_config(
            LocalIdentity::from_keypair(&kp, SecHandle(1)).unwrap(),
            ConnId::new(b"relay000").unwrap(),
        )
        .unwrap();
        Self {
            c: Box::new(ProtectedCarrier::accept(cfg)),
            stores: ResponderStores::default(),
            kp,
        }
    }

    /// Poll the carrier until idle, answering its key requests; the packet ids decoded go to `ids`.
    fn pump(&mut self, now: u64, drbg: &mut Drbg, ids: &mut Vec<u8>) {
        for _ in 0..64 {
            let soft = SoftKeys::<Software> {
                signer: Some((SecHandle(1), &self.kp)),
                prekeys: None,
            };
            let mut env = Env {
                provider: &Software,
                now,
                drbg: &mut *drbg,
            };
            match self.c.poll(&mut env, &mut self.stores) {
                Ok(Poll::Idle) | Err(_) => return,
                Ok(Poll::KeyRequest) => {
                    let _ = self.c.answer_soft(&mut env, &soft);
                }
                Ok(Poll::Frame(f)) => ids_of(&f, ids),
                Ok(_) => {}
            }
        }
    }
}

/// What the host holds for relay 0.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Stream {
    /// No stream.
    None,
    /// A stream was asked for and the host has not reported it yet.
    Asked,
    /// The host reported the stream open.
    Live,
}

/// The node, the host's side of its stream and the record of a run.
struct Rig {
    conn: Box<Conn>,
    keys: Soft,
    drbg: Drbg,
    rdrbg: Drbg,
    remote: SocketAddr,
    now: u64,
    stream: Stream,
    resp: Option<Resp>,
    /// Responder keys for the next streams, then the default (or a seeded pick).
    tags: Vec<u8>,
    default_tag: u8,
    tag_rng: Option<SplitMix64>,
    /// Bytes the responder sent that the node has not taken yet.
    inbox: Vec<u8>,
    out: Vec<String>,
    routed: Vec<u8>,
    decoded: Vec<u8>,
    opens: Vec<Kind>,
    gen_exp: u64,
    up: bool,
    ups: u32,
}

impl Rig {
    fn new(addr: &str, slow: bool, default_tag: u8) -> Self {
        let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        let mut relays = [None; 1];
        relays[0] = Some(RelayCfg {
            id: id(&ed(0x77)),
            udp: None,
            tcp: matches!(addr, "both" | "tcp").then(|| TCP.parse().unwrap()),
            ws: matches!(addr, "both" | "ws").then(|| WS.parse().unwrap()),
        });
        let cfg = Config {
            me: identity.node_id(),
            identity,
            relays,
            phone: false,
            restarted: false,
            start: 1000 * SEC,
            v6: false,
            keep_learn: false,
        };
        let mut conn: Box<Conn> = Box::new(Connectivity::new(cfg, prekey, Software, 7));
        conn.set_local(&["192.168.1.2:4433".parse().unwrap()]);
        if slow {
            conn.set_node_rtt(4 * SEC, 4 * SEC);
        }
        let remote = conn.path_addr(0, &nid(0xb7));
        let gen_exp = conn.generation(0);
        Self {
            conn,
            keys: Soft(host),
            drbg: Drbg::new(&[0x62; 32]),
            rdrbg: Drbg::new(&[0x63; 32]),
            remote,
            now: 1020 * SEC,
            stream: Stream::None,
            resp: None,
            tags: Vec::new(),
            default_tag,
            tag_rng: None,
            inbox: Vec::new(),
            out: vec![format!(
                r#"{{"op":"init","addr":"{addr}","slow":{slow},"cap":{QUEUED}}}"#
            )],
            routed: Vec::new(),
            decoded: Vec::new(),
            opens: Vec::new(),
            gen_exp,
            up: false,
            ups: 0,
        }
    }

    /// The responder keys of the next streams, in order; later streams use the default.
    fn with_tags(mut self, tags: &[u8]) -> Self {
        self.tags = tags.iter().rev().copied().collect();
        self
    }

    fn next_tag(&mut self) -> u8 {
        if let Some(t) = self.tags.pop() {
            return t;
        }
        match self.tag_rng.as_mut() {
            Some(r) => {
                if r.next_u64() % 6 == 0 {
                    0x78
                } else {
                    self.default_tag
                }
            }
            None => self.default_tag,
        }
    }

    /// Read the state after a call, take the stream requests and notices as the host does, and record the event.
    fn rec(&mut self, head: &str) {
        let link = match self.conn.carrier_state(0) {
            State::Down => "down",
            State::Dialing => "dialing",
            State::Open => "open",
        };
        let mut io = Vec::new();
        while let Some(i) = self.conn.poll_io() {
            match i {
                Io::Open { relay: 0, kind, .. } => {
                    let k = if kind == Kind::Tcp { "tcp" } else { "ws" };
                    io.push(format!(r#"{{"op":"open","kind":"{k}"}}"#));
                    self.opens.push(kind);
                    self.gen_exp += 1;
                    let tag = self.next_tag();
                    self.resp = Some(Resp::new(tag));
                    self.inbox.clear();
                    self.stream = Stream::Asked;
                }
                Io::Close { relay: 0 } => {
                    io.push(r#"{"op":"close","kind":"none"}"#.to_owned());
                    self.resp = None;
                    self.inbox.clear();
                    self.stream = Stream::None;
                }
                _ => {}
            }
        }
        let mut nt = Vec::new();
        while let Some(n) = self.conn.poll_notice() {
            match n {
                Notice::CarrierUp(0) => {
                    assert!(!self.up, "two CarrierUp in a row");
                    self.up = true;
                    self.ups += 1;
                    nt.push(r#""up""#);
                }
                Notice::CarrierDown(0) => {
                    assert!(self.up, "a CarrierDown with no CarrierUp before it");
                    self.up = false;
                    nt.push(r#""down""#);
                }
                _ => {}
            }
        }
        let generation = self.conn.generation(0);
        assert_eq!(
            generation, self.gen_exp,
            "the generation moved other than once per stream request"
        );
        assert_eq!(
            self.conn.carrier_state(0) == State::Open,
            self.up,
            "the link is open exactly after a CarrierUp not yet followed by a CarrierDown"
        );
        self.out.push(format!(
            r#"{{{head},"link":"{link}","gen":{generation},"io":[{}],"nt":[{}]}}"#,
            io.join(","),
            nt.join(",")
        ));
    }

    fn adv(&mut self, ms: u64) {
        self.now += ms * MS;
    }

    fn route(&mut self, k: u8) {
        self.adv(10);
        self.routed.push(k);
        let _ = self.conn.route(self.now, &*self.keys.0.ep, self.remote, &packet(k));
        self.rec(&format!(r#""op":"route","pkt":{k}"#));
    }

    /// Route the next unused packet id.
    fn route_next(&mut self) -> u8 {
        let k = self.routed.iter().copied().max().unwrap_or(0) + 1;
        self.route(k);
        k
    }

    fn tick(&mut self, ms: u64) {
        self.adv(ms);
        let mut env = Env {
            provider: &Software,
            now: self.now,
            drbg: &mut self.drbg,
        };
        self.conn.tick(self.now, &mut env, None);
        self.rec(r#""op":"tick""#);
    }

    fn drive(&mut self, ms: u64) {
        self.adv(ms);
        let mut env = Env {
            provider: &Software,
            now: self.now,
            drbg: &mut self.drbg,
        };
        self.conn.drive(self.now, &mut *self.keys.0.ep, &mut env, None);
        self.rec(r#""op":"drive""#);
    }

    /// The host connected the stream asked for. Nothing happens when none is asked for.
    fn opened(&mut self) {
        if self.stream != Stream::Asked {
            return;
        }
        self.adv(10);
        self.stream = Stream::Live;
        let mut env = Env {
            provider: &Software,
            now: self.now,
            drbg: &mut self.drbg,
        };
        self.conn.stream_opened(self.now, &mut env, 0);
        self.rec(r#""op":"opened","ok":true"#);
    }

    /// The network ended the stream, or its connect failed. The host forgets it and the node asks for no close.
    fn closed(&mut self) {
        self.adv(10);
        self.stream = Stream::None;
        self.resp = None;
        self.inbox.clear();
        self.conn.stream_closed(self.now, 0);
        self.rec(r#""op":"closed""#);
    }

    /// Tick every `ms` until the host is asked for a stream, at most `max` times.
    fn tick_until_dial(&mut self, ms: u64, max: u32) {
        for _ in 0..max {
            if self.stream == Stream::Asked {
                return;
            }
            self.tick(ms);
        }
    }

    /// The stream the run waits for: ticks every second when it has not come, and a route when still none.
    fn ensure_dial(&mut self) {
        self.tick_until_dial(1000, 5);
        if self.stream != Stream::Asked {
            self.route_next();
        }
    }

    /// Answer the node's key and signing requests, move bytes both ways once; true when something moved.
    fn shuttle_once(&mut self) -> bool {
        let mut moved = false;
        while self.stream == Stream::Live {
            let Some(ans) = self.conn.key_request(0).map(|r| self.keys.answer(self.now, &r)) else {
                break;
            };
            moved = true;
            let mut env = Env {
                provider: &Software,
                now: self.now,
                drbg: &mut self.drbg,
            };
            self.conn.key_response(self.now, &mut env, 0, ans.response());
            self.rec(r#""op":"hs""#);
        }
        while let Some(ans) = self.conn.sign_request().map(|r| self.keys.answer(self.now, &r)) {
            moved = true;
            self.conn.sign_response(self.now, ans.response());
            self.rec(r#""op":"hs""#);
        }
        if self.stream != Stream::Live {
            return moved;
        }
        let mut buf = vec![0u8; 32 * 1024];
        let n = self.conn.poll_stream(0, &mut buf);
        let mut ids = Vec::new();
        if let Some(resp) = self.resp.as_mut() {
            let mut rest = &buf[..n];
            while !rest.is_empty() {
                let took = resp.c.receive(rest);
                rest = &rest[took..];
                resp.pump(self.now, &mut self.rdrbg, &mut ids);
                if took == 0 {
                    break;
                }
            }
            resp.pump(self.now, &mut self.rdrbg, &mut ids);
            let mut back = vec![0u8; 32 * 1024];
            loop {
                let m = resp.c.transmit(&mut back);
                if m == 0 {
                    break;
                }
                self.inbox.extend_from_slice(&back[..m]);
            }
        }
        for k in &ids {
            assert!(!self.decoded.contains(k), "packet {k} was decoded twice");
        }
        self.decoded.extend_from_slice(&ids);
        let list: Vec<String> = ids.iter().map(u8::to_string).collect();
        self.rec(&format!(r#""op":"poll","sent":[{}]"#, list.join(",")));
        moved |= n > 0 || !ids.is_empty();
        if self.stream == Stream::Live && !self.inbox.is_empty() {
            moved = true;
            let mut env = Env {
                provider: &Software,
                now: self.now,
                drbg: &mut self.drbg,
            };
            let took = self.conn.stream_data(self.now, &mut env, 0, &self.inbox);
            self.inbox.drain(..took);
            self.rec(r#""op":"hs""#);
        }
        moved
    }

    fn shuttle(&mut self) {
        for _ in 0..16 {
            if !self.shuttle_once() {
                break;
            }
        }
    }

    fn until_open(&mut self) {
        for _ in 0..16 {
            if self.conn.carrier_state(0) == State::Open || !self.shuttle_once() {
                break;
            }
        }
    }

    /// The responder's sealed record of 64 zero bytes (empty when it cannot seal yet).
    fn sealed(&mut self) -> Vec<u8> {
        let mut out = vec![0u8; 4096];
        let n = self
            .resp
            .as_mut()
            .and_then(|r| r.c.seal_bytes(&Software, &[0u8; 64], &mut out).ok())
            .unwrap_or(0);
        out.truncate(n);
        out
    }

    /// Hand bytes to the node's stream.
    fn data(&mut self, bytes: &[u8]) {
        if self.stream != Stream::Live || bytes.is_empty() {
            return;
        }
        self.adv(10);
        let mut env = Env {
            provider: &Software,
            now: self.now,
            drbg: &mut self.drbg,
        };
        self.conn.stream_data(self.now, &mut env, 0, bytes);
        self.rec(r#""op":"hs""#);
    }

    /// The run ends: every packet decoded at most once, and (when `ordered`) exactly the routed ones in order.
    fn finish(self, ordered: bool, out: &mut Vec<String>) {
        if ordered {
            assert_eq!(self.decoded, self.routed, "the packets did not arrive as routed");
        }
        out.extend(self.out);
    }
}

/// Bring the carrier open with packet `k` waiting, then shuttle.
fn open_with(r: &mut Rig, k: u8) {
    r.route(k);
    r.ensure_dial();
    r.opened();
    r.until_open();
    r.shuttle();
}

fn normal(out: &mut Vec<String>) {
    let mut r = Rig::new("both", false, 0x77);
    r.route(1);
    r.route(2);
    r.opened();
    r.until_open();
    r.route(3);
    r.shuttle();
    r.closed();
    r.route(4);
    r.ensure_dial();
    r.opened();
    r.until_open();
    r.shuttle();
    r.finish(true, out);
}

/// The first responder is another node: the handshake fails, the kind changes and the second dial succeeds.
fn wrong(out: &mut Vec<String>, addr: &str, kinds: &[Kind]) {
    let mut r = Rig::new(addr, false, 0x77).with_tags(&[0x78]);
    r.route(1);
    r.opened();
    r.shuttle();
    r.tick_until_dial(500, 10);
    if r.stream != Stream::Asked {
        r.route_next();
    }
    r.opened();
    r.until_open();
    r.shuttle();
    assert!(r.opens.starts_with(kinds), "the stream kinds were {:?}", r.opens);
    r.finish(true, out);
}

fn wsonly(out: &mut Vec<String>) {
    let mut r = Rig::new("ws", false, 0x77);
    open_with(&mut r, 1);
    assert!(r.opens.starts_with(&[Kind::Ws]), "the stream kinds were {:?}", r.opens);
    r.finish(true, out);
}

fn watchdog(out: &mut Vec<String>) {
    let mut r = Rig::new("both", false, 0x77);
    r.route(1);
    r.tick(31_000);
    r.tick_until_dial(1000, 5);
    if r.stream != Stream::Asked {
        r.route_next();
    }
    r.opened();
    r.until_open();
    r.shuttle();
    r.finish(true, out);
}

fn dialfail(out: &mut Vec<String>) {
    let mut r = Rig::new("both", false, 0x77);
    r.route(1);
    r.closed();
    r.tick_until_dial(1000, 5);
    if r.stream != Stream::Asked {
        r.route_next();
    }
    r.opened();
    r.until_open();
    r.shuttle();
    r.finish(true, out);
}

/// A record cut in half by the end of the stream, then a record altered in flight.
fn midmessage(out: &mut Vec<String>) {
    let mut r = Rig::new("both", false, 0x77);
    open_with(&mut r, 1);
    let sealed = r.sealed();
    r.data(&sealed[..sealed.len() / 2]);
    r.closed();
    r.route_next();
    r.ensure_dial();
    r.opened();
    r.until_open();
    r.shuttle();
    let mut sealed = r.sealed();
    if let Some(last) = sealed.last_mut() {
        *last ^= 1;
    }
    r.data(&sealed);
    r.route_next();
    r.ensure_dial();
    r.opened();
    r.until_open();
    r.shuttle();
    r.finish(true, out);
}

/// A very slow node: the held packets and a new one; the order they leave in is not asserted.
fn slow(out: &mut Vec<String>) {
    let mut r = Rig::new("both", true, 0x77);
    r.route(1);
    r.route(2);
    r.route(3);
    r.opened();
    r.until_open();
    r.route(4);
    r.shuttle();
    r.drive(10);
    r.shuttle();
    let mut got = r.decoded.clone();
    got.sort_unstable();
    assert_eq!(got, [1, 2, 3, 4], "a packet was lost or sent twice");
    r.finish(false, out);
}

/// One seeded run: 60 calls the host contract allows, chosen at random. Returns whether a carrier opened.
fn seeded(seed: u64, out: &mut Vec<String>) -> bool {
    let addr = ["both", "tcp", "ws"][(seed % 3) as usize];
    let mut r = Rig::new(addr, seed % 4 == 3, 0x77);
    r.tag_rng = Some(SplitMix64::traced(0x5CA7 + seed));
    let mut rng = SplitMix64::traced(0xCA11 + seed);
    for _ in 0..60 {
        // 0 route, 1 tick, 2 drive, 3 shuttle, 4 closed, 5 altered record, 6 opened
        let mut choices = vec![1u8, 2];
        if r.routed.len() < 40 {
            choices.push(0);
        }
        match r.stream {
            Stream::Live => {
                if r.conn.carrier_state(0) == State::Open {
                    choices.extend([3, 4, 5]);
                } else {
                    // a handshake needs two or three rounds before the end of the stream may cut it
                    choices.extend([3, 3, 3, 4]);
                }
            }
            Stream::Asked => choices.extend([6, 6, 6, 4]),
            Stream::None => {}
        }
        match choices[(rng.next_u64() % choices.len() as u64) as usize] {
            0 => {
                r.route_next();
            }
            // mostly 10 ms; 2 s (the longest retry wait) one time in five, and 31 s (past a dial's cap) one in twenty
            1 => r.tick(match rng.next_u64() % 20 {
                0 => 31_000,
                1..=4 => 2_000,
                _ => 10,
            }),
            2 => r.drive(10),
            3 => {
                r.shuttle_once();
            }
            4 => r.closed(),
            5 => {
                let mut sealed = r.sealed();
                if let Some(last) = sealed.last_mut() {
                    *last ^= 1;
                }
                r.data(&sealed);
            }
            _ => r.opened(),
        }
    }
    let opened = r.ups > 0;
    r.finish(false, out);
    opened
}

#[test]
fn connect_carriers_trace() {
    big_stack(|| {
        let mut out = Vec::new();
        normal(&mut out);
        wrong(&mut out, "both", &[Kind::Tcp, Kind::Ws]);
        wrong(&mut out, "tcp", &[Kind::Tcp, Kind::Tcp]);
        wsonly(&mut out);
        watchdog(&mut out);
        dialfail(&mut out);
        midmessage(&mut out);
        slow(&mut out);
        let opened = (0..40).filter(|&seed| seeded(seed, &mut out)).count();
        eprintln!("connect_carriers: a carrier opened in {opened} of 40 seeds");
        assert!(opened >= 30, "a carrier opened in only {opened} of 40 seeds");
        assert!(out.len() > 2000, "the trace holds {} events", out.len());
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::write(format!("{dir}/connect_carriers.ndjson"), out.join("\n") + "\n").unwrap();
        }
    });
}
