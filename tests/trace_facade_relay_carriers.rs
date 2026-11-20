//! Trace generation for the carriers of a node that carries the relay role (`relay/part.rs`, `state.rs`, `conn.rs`):
//! a `Part` (the relay without its I/O) driven by hand over the carriers contract, recorded as ndjson
//! (`relay-carriers.ndjson`) for the TLA+ trace check `TraceFacadeRelayCarriers.tla`.
//!
//! The host here is the test: it keeps the operations the part submits, hands back one completion per poll, and plays
//! the members with the dialing side of the carrier protocol over byte queues (WebSocket framing for a WebSocket
//! stream). A scripted run walks the cases one by one (handshakes, refusals, an accept error, deadlines, pings, a slow
//! member, a replaced member, junk, stop, end); then seeded runs hand back random completions. Times are whole
//! milliseconds since the base the part was built at. Nothing is written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::large_futures,
    clippy::many_single_char_names,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::type_complexity,
    dead_code,
    unused_macros,
    unused_imports,
    missing_docs
)]

mod pinc_common;
mod relay_members;

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::rc::Rc;
use std::task::{Context, Poll as TaskPoll, Waker};

use pinc::relay::{Carriers, Completion, Done, Limits, Part, Peer, Relay, Stats, Tag};
use pinc::{CarrierKind, Error, ErrorKind, Identity};
use pinc_connect::carrier::session::{ALPN, Poll};
use pinc_connect::carrier::ws::{self, Decoder, Opcode, Role, WsFrame};
use pinc_connect::carrier::{Frame, MAX_FRAME_LEN, ProtectedCarrier};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use pinc_security::{Env, KeyHandle, ResponderStores, SoftKeys, SoftPrekeys};
use pinc_tests::SplitMix64;
use relay_members::{dial_carrier, wall_ns};

/// The host's byte stream: its number, from 1 in the order the test hands streams back.
struct S(u32);

/// What the host keeps: the operations out and what the part did in the current poll.
#[derive(Default)]
struct Ops {
    acc_out: bool,
    acc_tag: Option<Tag>,
    rd_out: BTreeMap<u32, (Tag, Vec<u8>)>,
    wr_out: BTreeMap<u32, (Tag, Vec<u8>, usize)>,
    closed: BTreeSet<u32>,
    known: BTreeSet<u32>,
    dropped: BTreeSet<u32>,
    next: Option<Completion<S>>,
    acc: bool,
    rd: Vec<u64>,
    wr: Vec<(u64, bool)>,
    close: Vec<u32>,
}

#[derive(Clone)]
struct Host(Rc<RefCell<Ops>>);

impl Carriers for Host {
    type Stream = S;

    fn submit_accept(&self, tag: Tag) {
        let mut o = self.0.borrow_mut();
        assert!(!o.acc_out, "a second accept was submitted");
        o.acc_out = true;
        o.acc_tag = Some(tag);
        o.acc = true;
    }

    fn submit_open(&self, _tag: Tag, _peer: &Peer, _kind: CarrierKind) {
        panic!("the part dialed a peer relay it was never given");
    }

    fn submit_read(&self, stream: &Rc<S>, tag: Tag, buf: Vec<u8>) {
        let mut o = self.0.borrow_mut();
        assert!(
            !o.rd_out.contains_key(&stream.0),
            "a second read on stream {}",
            stream.0
        );
        o.rd.push(tag.conn());
        o.rd_out.insert(stream.0, (tag, buf));
    }

    fn submit_write(&self, stream: &Rc<S>, tag: Tag, buf: Vec<u8>, from: usize) {
        let mut o = self.0.borrow_mut();
        assert!(
            !o.wr_out.contains_key(&stream.0),
            "a second write on stream {}",
            stream.0
        );
        o.wr.push((tag.conn(), from > 0));
        o.wr_out.insert(stream.0, (tag, buf, from));
    }

    fn close(&self, _tag: Tag, stream: Rc<S>) {
        let mut o = self.0.borrow_mut();
        let h = stream.0;
        assert!(o.closed.insert(h), "stream {h} was closed twice");
        assert!(!o.dropped.contains(&h), "stream {h} was closed after end dropped it");
        o.close.push(h);
    }

    fn poll_completed(&self, _cx: &mut Context<'_>) -> TaskPoll<Completion<S>> {
        self.0
            .borrow_mut()
            .next
            .take()
            .map_or(TaskPoll::Pending, TaskPoll::Ready)
    }

    fn drive(&self) -> impl Future<Output = ()> {
        core::future::pending()
    }

    fn ended(&self) {
        let mut o = self.0.borrow_mut();
        o.acc_out = false;
        o.rd_out.clear();
        o.wr_out.clear();
        let known = o.known.clone();
        o.dropped.extend(known);
    }
}

/// The dialing side of a member's carrier, with the bytes it has for the relay.
struct Dialer {
    kp: Keypair,
    relay: NodeId,
    carrier: Box<ProtectedCarrier<Software>>,
    drbg: Drbg,
    stores: Box<ResponderStores<4, 4>>,
    prekeys: Box<SoftPrekeys<Software>>,
    ws: Option<Decoder>,
    ws_in: Vec<u8>,
    to_relay: Vec<u8>,
}

impl Dialer {
    fn new(j: u8, kind: CarrierKind, relay: NodeId) -> Self {
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[0x30 + j; 32]).unwrap();
        let (carrier, drbg, prekeys) = dial_carrier(&kp, &[0x40 + j; 32], relay, ALPN);
        let mut d = Self {
            kp,
            relay,
            carrier,
            drbg,
            stores: Box::default(),
            prekeys,
            ws: (kind == CarrierKind::Ws).then(|| Decoder::new(Role::Server)),
            ws_in: Vec::new(),
            to_relay: Vec::new(),
        };
        d.advance();
        d
    }

    fn wrap(&mut self, bytes: &[u8]) {
        if self.ws.is_some() {
            let mut f = vec![0u8; bytes.len() + ws::MAX_HEADER];
            let n = ws::encode(Opcode::Binary, bytes, Some([1, 2, 3, 4]), &mut f).unwrap();
            self.to_relay.extend_from_slice(&f[..n]);
        } else {
            self.to_relay.extend_from_slice(bytes);
        }
    }

    fn flush(&mut self) {
        let mut buf = vec![0u8; 32 * 1024];
        while self.carrier.pending_transmit() > 0 {
            let n = self.carrier.transmit(&mut buf);
            self.wrap(&buf[..n]);
        }
    }

    /// Take bytes the relay wrote.
    fn feed(&mut self, bytes: &[u8]) {
        let mut payloads: Vec<Vec<u8>> = Vec::new();
        if let Some(dec) = self.ws.as_mut() {
            self.ws_in.extend_from_slice(bytes);
            let mut pos = 0;
            while let Ok(Some((frame, used))) = dec.decode(&mut self.ws_in[pos..]) {
                if let WsFrame::Data(p) = frame {
                    payloads.push(p.to_vec());
                }
                pos += used;
            }
            self.ws_in.drain(..pos);
        } else {
            payloads.push(bytes.to_vec());
        }
        for p in payloads {
            let mut rest = &p[..];
            while !rest.is_empty() {
                let used = self.carrier.receive(rest);
                rest = &rest[used..];
                if used == 0 {
                    break;
                }
            }
        }
        self.advance();
    }

    /// Run the handshake and read the frames as far as the bytes taken allow.
    fn advance(&mut self) {
        for _ in 0..64 {
            self.flush();
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &self.kp)),
                prekeys: Some(&*self.prekeys),
            };
            let prov = Software;
            let mut env = Env {
                provider: &prov,
                now: wall_ns(),
                drbg: &mut self.drbg,
            };
            if self.carrier.key_request().is_some() {
                let _ = self.carrier.answer_soft(&mut env, &soft);
                continue;
            }
            match self.carrier.poll(&mut env, &mut self.stores) {
                Ok(Poll::KeyRequest) => {
                    let _ = self.carrier.answer_soft(&mut env, &soft);
                }
                Ok(Poll::Idle) | Err(_) => {
                    self.flush();
                    return;
                }
                Ok(_) => {}
            }
        }
    }

    fn send(&mut self, f: &Frame<'_>) {
        let mut out = vec![0u8; MAX_FRAME_LEN + 64];
        let n = self.carrier.seal(&Software, f, &mut out).unwrap();
        self.wrap(&out[..n]);
    }
}

struct Strm {
    d: Dialer,
    kind: CarrierKind,
    j: u8,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Bytes {
    Data,
    Zero,
    Junk,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Wr {
    All,
    Part,
    Zero,
}

/// What a poll hands back.
#[derive(Clone, Copy)]
enum Pick {
    Nothing,
    Accept(u32),
    AcceptErr,
    Read(u32, Bytes),
    Write(u32, Wr),
}

fn limits() -> Limits {
    Limits {
        handshaking: 2,
        carriers: 2,
        handshake_ns: 2_000_000_000,
        idle_ns: 4_000_000_000,
        write_backlog: 64 * 1024,
        ..Limits::default()
    }
}

struct Sim {
    part: Part<Host>,
    ops: Rc<RefCell<Ops>>,
    base: u64,
    ms: u64,
    last_ms: u64,
    out: String,
    streams: BTreeMap<u32, Strm>,
    up: BTreeSet<u32>,
    next_h: u32,
    /// The kind and member of the stream the next accept hands back.
    plan: Option<(u32, CarrierKind, u8)>,
}

fn cnt(s: &Stats) -> String {
    format!(
        "{{\"opened\":{},\"closed\":{},\"full\":{},\"hsfull\":{},\"proto\":{},\"slow\":{},\"tout\":{},\"accerr\":{}}}",
        s.carriers_opened,
        s.carriers_closed,
        s.refused_carriers_full,
        s.refused_handshakes_full,
        s.protocol_failures,
        s.slow_closed,
        s.timed_out,
        s.accept_errors
    )
}

fn kind_name(k: CarrierKind) -> &'static str {
    if k == CarrierKind::Ws { "ws" } else { "tcp" }
}

impl Sim {
    fn new() -> Self {
        let ops = Rc::new(RefCell::new(Ops::default()));
        let base = wall_ns();
        let part = Relay::builder()
            .identity(Identity::from_seed_with(&[0x70; 32], &[0; 32]).unwrap())
            .limits(limits())
            .build_part(Host(Rc::clone(&ops)), base)
            .unwrap();
        Self {
            part,
            ops,
            base,
            ms: 0,
            last_ms: 0,
            out: String::new(),
            streams: BTreeMap::new(),
            up: BTreeSet::new(),
            next_h: 1,
            plan: None,
        }
    }

    fn now(&self) -> u64 {
        self.base + self.ms * 1_000_000
    }

    /// The clock moves to `ms`, which is never earlier than now.
    fn at(&mut self, ms: u64) {
        assert!(ms >= self.ms, "the script is at {} ms and wants {ms} ms", self.ms);
        self.ms = ms;
    }

    fn view(&self) -> String {
        let s = self.part.stats();
        format!("\"cnt\":{},\"sess\":{}", cnt(&s), s.carriers)
    }

    /// Plan the next accept: the stream number it will have.
    fn accept(&mut self, kind: CarrierKind, j: u8) -> u32 {
        for _ in 0..20 {
            if self.ops.borrow().acc_out {
                break;
            }
            self.poll(Pick::Nothing);
        }
        let h = self.next_h;
        self.next_h += 1;
        self.plan = Some((h, kind, j));
        self.poll(Pick::Accept(h));
        h
    }

    fn poll(&mut self, pick: Pick) {
        let before = self.part.stats();
        let (completion, k, conn, x, n, kind) = self.hand_back(pick);
        {
            let mut o = self.ops.borrow_mut();
            o.next = completion;
            o.acc = false;
            o.rd.clear();
            o.wr.clear();
            o.close.clear();
        }
        let now = self.now();
        let mut cx = Context::from_waker(Waker::noop());
        self.part.poll(&mut cx, now);
        self.ops.borrow_mut().next = None;
        let after = self.part.stats();
        assert!(after.carriers <= 2, "more carriers than the limit");
        let x = match (k, pick) {
            ("rd", Pick::Read(h, b)) => {
                let opened = after.carriers_opened > before.carriers_opened;
                let full = after.refused_carriers_full > before.refused_carriers_full;
                if b == Bytes::Zero {
                    "zero"
                } else if after.protocol_failures > before.protocol_failures {
                    "junk"
                } else if opened || full {
                    if opened {
                        self.up.insert(h);
                    }
                    "open"
                } else if self.up.contains(&h) {
                    "frame"
                } else {
                    "hello"
                }
            }
            _ => x,
        };
        let n = if x == "open" {
            match pick {
                Pick::Read(h, _) => self.streams.get(&h).map_or(0, |s| u32::from(s.j)),
                _ => 0,
            }
        } else {
            n
        };
        let o = self.ops.borrow();
        let rd: Vec<String> = o.rd.iter().map(u64::to_string).collect();
        let wr: Vec<String> =
            o.wr.iter()
                .map(|(c, p)| format!("{{\"conn\":{c},\"part\":{p}}}"))
                .collect();
        let close: Vec<String> = o.close.iter().map(u32::to_string).collect();
        let _ = writeln!(
            self.out,
            "{{\"op\":\"poll\",\"now\":{},\"acc\":{},\"done\":{{\"k\":\"{k}\",\"conn\":{conn},\"x\":\"{x}\",\"n\":{n},\"kind\":\"{kind}\",\"to\":0}},\"rd\":[{}],\"wr\":[{}],\"close\":[{}],{}}}",
            self.ms,
            o.acc,
            rd.join(","),
            wr.join(","),
            close.join(","),
            {
                let s = &after;
                format!("\"cnt\":{},\"sess\":{}", cnt(s), s.carriers)
            }
        );
        drop(o);
        self.last_ms = self.ms;
        self.ms += 10;
    }

    /// The completion for `pick`, and what the record says of it before the counters classify it.
    fn hand_back(
        &mut self,
        pick: Pick,
    ) -> (
        Option<Completion<S>>,
        &'static str,
        u64,
        &'static str,
        u32,
        &'static str,
    ) {
        match pick {
            Pick::Nothing => (None, "none", 0, "none", 0, "tcp"),
            Pick::AcceptErr => {
                let mut o = self.ops.borrow_mut();
                o.acc_out = false;
                let tag = o.acc_tag.take().expect("an accept is out");
                drop(o);
                let e = Error::new(ErrorKind::Unreachable, "the accept failed");
                (
                    Some(Completion {
                        tag,
                        done: Done::Accepted(Err(e)),
                    }),
                    "acc",
                    0,
                    "err",
                    0,
                    "tcp",
                )
            }
            Pick::Accept(h) => {
                let (ph, kind, j) = self.plan.take().expect("an accept was planned");
                assert_eq!(ph, h);
                let relay = self.part.node_id();
                self.streams.insert(
                    h,
                    Strm {
                        d: Dialer::new(j, kind, relay),
                        kind,
                        j,
                    },
                );
                let mut o = self.ops.borrow_mut();
                o.known.insert(h);
                o.acc_out = false;
                let tag = o.acc_tag.take().expect("an accept is out");
                (
                    Some(Completion {
                        tag,
                        done: Done::Accepted(Ok((S(h), kind))),
                    }),
                    "acc",
                    0,
                    "ok",
                    0,
                    kind_name(kind),
                )
            }
            Pick::Read(h, b) => {
                let (tag, mut buf) = self.ops.borrow_mut().rd_out.remove(&h).expect("a read is out");
                let st = self.streams.get_mut(&h).unwrap();
                let n = match b {
                    Bytes::Zero => 0,
                    Bytes::Junk => {
                        let n = 64.min(buf.len());
                        buf[..n].fill(0xFF);
                        n
                    }
                    Bytes::Data => {
                        let n = st.d.to_relay.len().min(buf.len());
                        buf[..n].copy_from_slice(&st.d.to_relay[..n]);
                        st.d.to_relay.drain(..n);
                        n
                    }
                };
                (
                    Some(Completion {
                        tag,
                        done: Done::Read(Ok(n), buf),
                    }),
                    "rd",
                    tag.conn(),
                    "hello",
                    0,
                    "tcp",
                )
            }
            Pick::Write(h, w) => {
                let (tag, buf, from) = self.ops.borrow_mut().wr_out.remove(&h).expect("a write is out");
                let rest = buf.len() - from;
                let n = match w {
                    Wr::All => rest,
                    Wr::Part => (rest / 2).max(1).min(rest),
                    Wr::Zero => 0,
                };
                if n > 0 {
                    self.streams.get_mut(&h).unwrap().d.feed(&buf[from..from + n]);
                }
                let x = match w {
                    Wr::All => "all",
                    Wr::Part => "part",
                    Wr::Zero => "zero",
                };
                (
                    Some(Completion {
                        tag,
                        done: Done::Written(Ok(n), buf),
                    }),
                    "wr",
                    tag.conn(),
                    x,
                    0,
                    "tcp",
                )
            }
        }
    }

    fn timeout(&mut self) {
        let now = self.now();
        self.part.handle_timeout(now);
        let _ = writeln!(self.out, "{{\"op\":\"timeout\",\"now\":{},{}}}", self.ms, self.view());
    }

    fn rd_out(&self, h: u32) -> bool {
        self.ops.borrow().rd_out.contains_key(&h)
    }

    fn wr_out(&self, h: u32) -> bool {
        self.ops.borrow().wr_out.contains_key(&h)
    }

    fn has_bytes(&self, h: u32) -> bool {
        self.streams.get(&h).is_some_and(|s| !s.d.to_relay.is_empty())
    }

    /// Run the member's handshake on `h` until its carrier opens or is refused.
    fn handshake(&mut self, h: u32, first_part: bool) {
        let mut part_next = first_part;
        for _ in 0..200 {
            let s = self.part.stats();
            if self.has_bytes(h) && self.rd_out(h) {
                self.poll(Pick::Read(h, Bytes::Data));
            } else if self.wr_out(h) {
                let w = if part_next { Wr::Part } else { Wr::All };
                part_next = false;
                self.poll(Pick::Write(h, w));
            } else {
                self.poll(Pick::Nothing);
            }
            let t = self.part.stats();
            if t.carriers_opened > s.carriers_opened || t.refused_carriers_full > s.refused_carriers_full {
                return;
            }
        }
        panic!(
            "the handshake of stream {h} neither opened nor was refused: {:?}",
            self.part.stats()
        );
    }

    /// Complete every write out whole, one per poll, until none is left (at most 50 polls).
    fn flush_writes(&mut self) {
        for _ in 0..50 {
            let w = self.ops.borrow().wr_out.keys().next().copied();
            if let Some(h) = w {
                self.poll(Pick::Write(h, Wr::All));
            } else {
                self.poll(Pick::Nothing);
                if self.ops.borrow().wr_out.is_empty() {
                    return;
                }
            }
        }
    }
}

fn scripted(s: &mut Sim) {
    use CarrierKind::{Tcp, Ws};
    // 1, 2: two members
    s.poll(Pick::Nothing);
    let h1 = s.accept(Tcp, 1);
    s.handshake(h1, false);
    let h2 = s.accept(Ws, 2);
    s.handshake(h2, true);
    // 3: a third is refused for the limit of carriers
    let h3 = s.accept(Tcp, 3);
    s.handshake(h3, false);
    s.poll(Pick::Nothing);
    // 4: streams that never speak; the third is refused for the limit of handshakes
    s.accept(Tcp, 1);
    s.accept(Tcp, 1);
    s.accept(Tcp, 1);
    // 5: an accept error pauses accepting
    for _ in 0..20 {
        if s.ops.borrow().acc_out {
            break;
        }
        s.poll(Pick::Nothing);
    }
    s.poll(Pick::AcceptErr);
    let paused = s.last_ms;
    s.ms = paused;
    s.poll(Pick::Nothing);
    s.ms = paused + 100;
    s.poll(Pick::Nothing);
    // 6: the first check pings the members
    let silent = s.ms;
    s.at(s.ms.max(1000));
    s.timeout();
    s.flush_writes();
    // 7: the handshakes past their deadline
    s.at(s.ms.max(silent + 2001));
    s.timeout();
    s.poll(Pick::Nothing);
    s.poll(Pick::Nothing);
    // 8: member 1 pings
    if s.streams.contains_key(&h1) {
        s.streams.get_mut(&h1).unwrap().d.send(&Frame::Ping);
        if s.rd_out(h1) {
            s.poll(Pick::Read(h1, Bytes::Data));
        }
        s.flush_writes();
    }
    // 9: member 2 floods and never reads
    let slow0 = s.part.stats().slow_closed;
    let mut reads = 0;
    while s.part.stats().slow_closed == slow0 && reads < 20 {
        if !s.rd_out(h2) {
            s.poll(Pick::Nothing);
            if !s.rd_out(h2) {
                break;
            }
        }
        let st = s.streams.get_mut(&h2).unwrap();
        for _ in 0..200 {
            st.d.send(&Frame::Ping);
        }
        s.poll(Pick::Read(h2, Bytes::Data));
        reads += 1;
    }
    assert!(
        s.part.stats().slow_closed > slow0,
        "a slow member was not closed within 20 reads"
    );
    // 10: member 1 ends its stream; the write still out is handed back late
    if s.rd_out(h1) {
        s.poll(Pick::Read(h1, Bytes::Zero));
    }
    s.poll(Pick::Nothing);
    if s.wr_out(h1) {
        s.poll(Pick::Write(h1, Wr::All));
    }
    // 11, 12: member 1 again, then again while the first is open
    let h7 = s.accept(Tcp, 1);
    s.handshake(h7, false);
    let h8 = s.accept(Tcp, 1);
    s.handshake(h8, false);
    s.poll(Pick::Nothing);
    // 13: a stream whose first read is junk
    let h9 = s.accept(Tcp, 2);
    if s.rd_out(h9) {
        s.poll(Pick::Read(h9, Bytes::Junk));
    }
    s.poll(Pick::Nothing);
    // 14: members silent for the idle time are closed
    s.at(s.ms.max(6500));
    s.timeout();
    for _ in 0..3 {
        s.poll(Pick::Nothing);
    }
    // 15: stop; every stream is closed; an accept comes back after the stop
    s.part.stop();
    let _ = writeln!(s.out, "{{\"op\":\"stop\"}}");
    for _ in 0..50 {
        let all = {
            let o = s.ops.borrow();
            o.known.iter().all(|h| o.closed.contains(h))
        };
        if all {
            break;
        }
        s.poll(Pick::Nothing);
    }
    if s.ops.borrow().acc_out {
        s.accept_late(Tcp, 3);
    }
    s.poll(Pick::Nothing);
    // 16: end; a poll; end again with that accept out; three polls
    s.end();
    s.poll(Pick::Nothing);
    s.end();
    for _ in 0..3 {
        s.poll(Pick::Nothing);
    }
}

impl Sim {
    /// Hand back the accept already out (after a stop, where no new one is submitted).
    fn accept_late(&mut self, kind: CarrierKind, j: u8) {
        let h = self.next_h;
        self.next_h += 1;
        self.plan = Some((h, kind, j));
        self.poll(Pick::Accept(h));
    }

    fn end(&mut self) {
        let now = self.now();
        self.part.end(now);
        let _ = writeln!(self.out, "{{\"op\":\"end\",{}}}", self.view());
    }
}

fn seeded(seed: u64) -> String {
    let mut rng = SplitMix64::new(seed);
    let mut s = Sim::new();
    for _ in 0..300 {
        let r = rng.next_u64() % 100;
        let hs: Vec<u32> = s.streams.keys().copied().collect();
        let pick_h = |rng: &mut SplitMix64| hs.get((rng.next_u64() % hs.len().max(1) as u64) as usize).copied();
        match r {
            0..15 => {
                let err = rng.next_u64().is_multiple_of(10);
                let kind = if rng.next_u64().is_multiple_of(2) {
                    CarrierKind::Tcp
                } else {
                    CarrierKind::Ws
                };
                let j = (rng.next_u64() % 3) as u8 + 1;
                if !s.ops.borrow().acc_out {
                    s.poll(Pick::Nothing);
                } else if err {
                    s.poll(Pick::AcceptErr);
                } else {
                    s.accept_late(kind, j);
                }
            }
            15..55 => match pick_h(&mut rng) {
                Some(h) if s.rd_out(h) => {
                    if s.has_bytes(h) {
                        s.poll(Pick::Read(h, Bytes::Data));
                    } else if rng.next_u64().is_multiple_of(4) {
                        s.poll(Pick::Read(h, Bytes::Zero));
                    } else {
                        s.poll(Pick::Nothing);
                    }
                }
                _ => s.poll(Pick::Nothing),
            },
            55..85 => match pick_h(&mut rng) {
                Some(h) if s.wr_out(h) => {
                    let w = match rng.next_u64() % 10 {
                        0..7 => Wr::All,
                        7..9 => Wr::Part,
                        _ => Wr::Zero,
                    };
                    s.poll(Pick::Write(h, w));
                }
                _ => s.poll(Pick::Nothing),
            },
            85..90 => {
                if let Some(h) = pick_h(&mut rng).filter(|h| s.up.contains(h)) {
                    s.streams.get_mut(&h).unwrap().d.send(&Frame::Ping);
                }
                s.poll(Pick::Nothing);
            }
            90..97 => s.poll(Pick::Nothing),
            _ => {
                let by = rng.next_u64() % 3000;
                s.ms += 10 + by;
                s.timeout();
            }
        }
    }
    s.out
}

#[test]
fn facade_relay_carriers_trace() {
    relay_members::on_big_stack(|| async {
        let mut s = Sim::new();
        scripted(&mut s);
        let mut out = std::mem::take(&mut s.out);
        drop(s);
        for seed in 1..=10 {
            out.push_str(&seeded(seed));
        }
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("relay-carriers.ndjson"), out).unwrap();
        }
    });
}
