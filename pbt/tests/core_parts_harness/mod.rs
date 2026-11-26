//! The driver of `core_parts.rs` and `repro_core2.rs`: an honest client and server (`core_harness`) and a third party
//! that taps their datagrams and sends what its rules derive from them. See `core_parts.rs` for where each expected
//! behaviour comes from.
#![allow(dead_code, clippy::unwrap_used, clippy::panic, clippy::indexing_slicing)]

use std::net::SocketAddr;

use super::core_harness::{self, ALPN_A, Edit, HostCfg, MS, Net, SEC, Violation, apply_edit};
use ephyra::gens;
use pinc_core::{Command, Event, Role, Value};
use pinc_security::ConnId;
use pinc_transport::packet::{LongHeader, LongType, handshake_packet};

/// The connect limit of a node that is not thin.
const CONNECT_LIMIT: u64 = 30 * SEC;
/// The most datagrams the third party sends in one case.
const MAX_INJECT: usize = 48;

/// An address of the third party; nothing sent there is ever read.
fn spoof(i: u8) -> SocketAddr {
    ([192, 0, 2, 1 + (i % 4)], 7000).into()
}

/// Where a forged datagram claims to come from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, ephyra::Arbitrary)]
pub enum Src {
    /// The address of the honest sender of the datagram it was derived from.
    Victim,
    /// One of the third party's own addresses.
    Other(#[ephyra(gen = gens::int(0u8..=3))] u8),
}

/// What the third party makes of a datagram it saw.
#[derive(Clone, Debug, PartialEq, Eq, ephyra::Arbitrary)]
pub enum Forge {
    /// The datagram again, with edits.
    Copy(#[ephyra(gen = gens::vec(ephyra::any::<Edit>()).len(0..=2))] Vec<Edit>),
    /// The handshake message the datagram carries a part of, byte `at` (modulo its length) changed by `xor`, in one
    /// datagram when `cut` is 0 (modulo the length), else cut in two there; `parts` says which go: 1 the first, 2 the
    /// second, 3 both in order, 0 both, the second first. Each datagram is padded to 1200 bytes when the one seen was.
    Mutate {
        #[ephyra(gen = gens::frequency(vec![(2, gens::int(0u16..=60).boxed()), (1, gens::int(0u16..=1400).boxed())]))]
        at: u16,
        #[ephyra(gen = gens::int(1u8..=255))]
        xor: u8,
        #[ephyra(gen = gens::frequency(vec![(2, gens::constant(0u16).boxed()), (1, gens::int(1u16..=1400).boxed())]))]
        cut: u16,
        #[ephyra(gen = gens::int(0u8..=3))]
        parts: u8,
    },
    /// A fragment of a message `delta` bytes longer or shorter than the one seen, from offset `off` (modulo its
    /// length), `len` bytes of the real message (zeros past its end).
    Total {
        #[ephyra(gen = gens::frequency(vec![(3, gens::int(-2i16..=2).boxed()), (1, gens::int(-1200i16..=1200).boxed())]))]
        delta: i16,
        #[ephyra(gen = gens::int(0u16..=1400))]
        off: u16,
        #[ephyra(gen = gens::int(1u16..=1300))]
        len: u16,
    },
    /// A fragment of the message seen (same length) whose `len` bytes from `off` (modulo the length) are all `byte`.
    Overwrite {
        #[ephyra(gen = gens::int(0u16..=1400))]
        off: u16,
        #[ephyra(gen = gens::int(1u16..=1300))]
        len: u16,
        byte: u8,
    },
}

/// One rule of the third party: on the `trigger`-th datagram one honest side sends the other (and every later one
/// when `every`), send the forgery to the same destination, from `src`, arriving `offset` ms after the genuine one
/// would on a link with no jitter (negative: before it).
#[derive(Clone, Debug, PartialEq, Eq, ephyra::Arbitrary)]
pub struct Act {
    /// 0: from the client's datagrams to the server; 1: from the server's to the client.
    #[ephyra(gen = gens::frequency(vec![(3, gens::constant(0u8).boxed()), (1, gens::constant(1u8).boxed())]))]
    pub dir: u8,
    #[ephyra(gen = gens::frequency(vec![(3, gens::int(0u8..=3).boxed()), (1, gens::int(0u8..=16).boxed())]))]
    pub trigger: u8,
    #[ephyra(gen = gens::bool_with(0.3))]
    pub every: bool,
    pub forge: Forge,
    pub src: Src,
    #[ephyra(gen = gens::frequency(vec![
        (2, gens::int(-60i16..=0).boxed()),
        (3, gens::int(0i16..=60).boxed()),
        (2, gens::int(0i16..=3000).boxed()),
    ]))]
    pub offset: i16,
}

#[derive(Clone, Debug, PartialEq, Eq, ephyra::Arbitrary)]
pub struct Case {
    pub seed: u64,
    /// `HostCfg::split`, the transport's `flight_split`: the first flight leaves whole when it fits a datagram and only
    /// the resends are cut (the endpoint's default), else every flight is cut to the minimum datagram size.
    pub split: bool,
    pub room: bool,
    #[ephyra(gen = gens::int(1u64..=60))]
    pub delay_ms: u64,
    #[ephyra(gen = gens::frequency(vec![(2, gens::constant(0u64).boxed()), (1, gens::int(0u64..=10).boxed())]))]
    pub jitter_ms: u64,
    /// The client's first flight is lost (after the tap saw it).
    pub drop_first: bool,
    #[ephyra(gen = gens::frequency(vec![(2, gens::constant(0u16).boxed()), (1, gens::int(0u16..=400).boxed())]))]
    pub loss: u16,
    /// How long the link loses `loss` per mille after the dial; it is clean from then on.
    #[ephyra(gen = gens::int(0u64..=6000))]
    pub lossy_ms: u64,
    #[ephyra(gen = gens::vec(ephyra::any::<Act>()).len(0..=6))]
    pub acts: Vec<Act>,
}

/// The first packet of a datagram when it is a long Handshake packet: its ids, message length, offset and bytes.
fn frag(d: &[u8]) -> Option<(ConnId, ConnId, usize, usize, Vec<u8>)> {
    let (h, hlen) = LongHeader::parse(d).ok()?;
    if h.ty != LongType::Handshake {
        return None;
    }
    let mut r = pinc_wire::Reader::new(d.get(hlen..hlen.checked_add(h.body_len)?)?);
    let total = usize::try_from(r.read_varint().ok()?).ok()?;
    let off = usize::try_from(r.read_varint().ok()?).ok()?;
    let data = r.read_bytes(r.remaining()).ok()?.to_vec();
    (total > 0 && off < total).then_some((h.dcid, h.scid, total, off, data))
}

/// The message of `total` bytes under `dcid` that `from` sent, from every part of it the tap saw (zeros where none).
fn assemble(captured: &[(SocketAddr, SocketAddr, Vec<u8>)], from: SocketAddr, dcid: ConnId, total: usize) -> Vec<u8> {
    let mut m = vec![0u8; total];
    for (f, _, d) in captured {
        if *f != from {
            continue;
        }
        if let Some((id, _, t, off, data)) = frag(d)
            && id == dcid
            && t == total
        {
            let end = (off + data.len()).min(total);
            m[off..end].copy_from_slice(&data[..end - off]);
        }
    }
    m
}

/// One long Handshake packet with `bytes` at `off` of a message of `total`, padded with zeros to `pad` bytes.
fn packet(dcid: ConnId, scid: ConnId, total: usize, off: usize, bytes: &[u8], pad: usize) -> Option<Vec<u8>> {
    let mut w = vec![0u8; bytes.len() + 64 + pad];
    let n = handshake_packet(&mut w, dcid, scid, total, off, bytes)?;
    w.truncate(n.max(pad));
    Some(w)
}

/// What the third party makes of datagram `d`, which `from` sent.
fn forge(captured: &[(SocketAddr, SocketAddr, Vec<u8>)], from: SocketAddr, d: &[u8], f: &Forge) -> Vec<Vec<u8>> {
    if let Forge::Copy(edits) = f {
        let mut x = d.to_vec();
        for e in edits {
            apply_edit(&mut x, *e);
        }
        return vec![x];
    }
    let Some((dcid, scid, total, _, _)) = frag(d) else { return Vec::new() };
    let msg = assemble(captured, from, dcid, total);
    let pad = if d.len() >= 1200 { 1200 } else { 0 };
    let out: Vec<Option<Vec<u8>>> = match *f {
        Forge::Copy(_) => Vec::new(),
        Forge::Mutate { at, xor, cut, parts } => {
            let mut m = msg;
            m[usize::from(at) % total] ^= xor;
            let c = usize::from(cut) % total;
            if c == 0 {
                vec![packet(dcid, scid, total, 0, &m, pad)]
            } else {
                let a = packet(dcid, scid, total, 0, &m[..c], pad);
                let b = packet(dcid, scid, total, c, &m[c..], pad);
                match parts {
                    1 => vec![a],
                    2 => vec![b],
                    3 => vec![a, b],
                    _ => vec![b, a],
                }
            }
        },
        Forge::Total { delta, off, len } => {
            let t = (total as i64 + i64::from(delta)).clamp(1, 4096) as usize;
            let o = usize::from(off) % t;
            let n = usize::from(len).min(t - o);
            let bytes: Vec<u8> = (o..o + n).map(|i| msg.get(i).copied().unwrap_or(0)).collect();
            vec![packet(dcid, scid, t, o, &bytes, pad)]
        },
        Forge::Overwrite { off, len, byte } => {
            let o = usize::from(off) % total;
            let n = usize::from(len).min(total - o);
            vec![packet(dcid, scid, total, o, &vec![byte; n], pad)]
        },
    };
    out.into_iter().flatten().collect()
}

/// The third party: it reads every datagram the hosts sent (the tap sits before the link's loss) and sends what its
/// rules derive from them.
struct Tap {
    seen: usize,
    count: [usize; 2],
    injected: usize,
    /// (arrival time, destination is the server, length) of each forgery.
    log: Vec<(u64, bool, usize)>,
    last: Option<(u64, usize, usize, u64, u64, u64, u64, u64, u64, u64, u64, u64)>,
}

impl Tap {
    fn new() -> Self {
        Self {
            seen: 0,
            count: [0; 2],
            injected: 0,
            log: Vec::new(),
            last: None,
        }
    }

    fn step(&mut self, n: &mut Net, c: &Case, ca: SocketAddr, sa: SocketAddr, t0: u64) {
        n.faults.cut = false;
        if std::env::var_os("PBT_TRACE").is_some()
            && let Some(h) = n.hosts.get(1)
        {
            let s = h.ep.node_stats();
            let key = (s.datagrams_in, s.sessions, s.half_open, s.dropped_in, s.holders_refused, s.backlog_refused, s.fragments_held, s.fragments_replayed, s.fragments_expired, s.fragments_evicted, s.stalled_in, s.first_too_short);
            if self.last != Some(key) {
                self.last = Some(key);
                eprintln!("{} ms: server (in, sessions, half_open, dropped_in, holders_refused, backlog_refused, held, replayed, expired, evicted, stalled, too_short) {key:?}", (n.now - t0) / MS);
            }
        }
        n.faults.loss = if n.now < t0 + c.lossy_ms * MS { c.loss } else { 0 };
        while self.seen < n.captured.len() {
            let (from, to, d) = n.captured[self.seen].clone();
            self.seen += 1;
            let dir = match (from == ca && to == sa, from == sa && to == ca) {
                (true, _) => 0,
                (_, true) => 1,
                _ => continue,
            };
            let k = self.count[dir];
            self.count[dir] += 1;
            if std::env::var_os("PBT_TRACE").is_some() {
                let f = frag(&d).map(|(_, _, t, o, x)| (t, o, x.len()));
                let s = n.hosts.get(1).map(|h| h.ep.node_stats());
                eprintln!(
                    "{} ms: {} #{k} {} bytes {f:?}; server half_open {:?} sessions {:?} held {:?} replayed {:?}; client in {:?} dropped {:?}",
                    (n.now - t0) / MS,
                    if dir == 0 { "client->server" } else { "server->client" },
                    d.len(),
                    s.map(|s| s.half_open),
                    s.map(|s| s.sessions),
                    s.map(|s| s.fragments_held),
                    s.map(|s| s.fragments_replayed),
                    n.hosts.first().map(|h| h.ep.node_stats().datagrams_in),
                    n.hosts.first().map(|h| h.ep.node_stats().dropped_in),
                );
            }
            for act in &c.acts {
                if usize::from(act.dir) != dir || !(k == usize::from(act.trigger) || act.every && k > usize::from(act.trigger)) {
                    continue;
                }
                for f in forge(&n.captured, from, &d, &act.forge) {
                    if self.injected >= MAX_INJECT {
                        return;
                    }
                    self.injected += 1;
                    let src = match act.src {
                        Src::Victim => from,
                        Src::Other(i) => spoof(i),
                    };
                    let delay = (n.delay as i64 + i64::from(act.offset) * MS as i64).max(0) as u64;
                    self.log.push((n.now + delay, dir == 0, f.len()));
                    n.inject(src, to, f, delay);
                }
            }
        }
    }
}

pub fn fail(v: Option<Violation>) {
    if let Some(v) = v {
        ephyra::signature(v.sig);
        panic!("{}: {}", v.sig, v.detail);
    }
}

/// Where the third party must sit for this case: whether a forgery may arrive before the genuine datagram.
pub fn races(c: &Case) -> bool {
    c.acts.iter().any(|a| a.offset < 0)
}

pub fn run(c: &Case) {
    run_with(c, false);
}

/// The causes `repro_core2.rs` reproduces, told by what they leave or by the rule that makes them, so a search that
/// lets them pass finds the others:
/// - A: the server never sent the client anything while it answered another address (a copied first flight made the
///   session), or a rule sends an exact copy of a client datagram from another address that may arrive first;
/// - B: the server let two held fragments expire with a half-open session left (the repeat's later part waited for a
///   start that only the next resend brings), or a rule sends one damaged copy from the client's address that may
///   stand in for the genuine datagram;
/// - C: the client sent to an address other than the server's (it followed a copied Reply);
/// - D: a rule that sends a forged fragment to the server with more than one flight, from any address (the reassembly
///   takes fragments from anyone).
///
/// vertexia: the exclusions are coarse (B and D let through any case that shows the symptom or uses the rule); narrow
/// them once the causes are fixed.
fn known_cause(net: &Net, c: &Case, a: usize, b: usize, ca: SocketAddr, sa: SocketAddr) -> Option<&'static str> {
    let to_client = net.sent_to.get(&(b, ca)).copied().unwrap_or(0);
    let to_spoof = net.sent_to.iter().any(|((h, to), n)| *h == b && *to != ca && *n > 0);
    let s = net.hosts[b].ep.node_stats();
    if to_client == 0 && to_spoof {
        return Some("A: the server answers only the address of a copied first flight");
    }
    if s.fragments_expired >= 2 && s.half_open >= 1 {
        return Some("B: the repeat of a damaged first message never meets its held part");
    }
    if net.sent_to.iter().any(|((h, to), n)| *h == a && *to != sa && *n > 0) {
        return Some("C: the client follows a copied Reply to another address");
    }
    // A by its rule: an exact copy of a client datagram from another address that may arrive first.
    let stand_in = c.drop_first || (c.loss > 0 && c.lossy_ms > 0);
    let copied_first = |act: &Act| {
        act.dir == 0 && matches!(act.src, Src::Other(_)) && matches!(&act.forge, Forge::Copy(e) if e.is_empty()) && (act.offset <= 0 || stand_in)
    };
    if c.acts.iter().any(copied_first) {
        return Some("A: a copy of the first flight from another address may make the session");
    }
    // B by its rule: one damaged copy of the first message from the client's address that may stand in for the
    // genuine one.
    let damaged_first = |act: &Act| {
        act.dir == 0 && act.src == Src::Victim && !act.every && !matches!(&act.forge, Forge::Copy(e) if e.is_empty()) && (act.offset < 0 || stand_in)
    };
    if c.acts.iter().any(damaged_first) {
        return Some("B: a damaged first message may stand in for the genuine one");
    }
    let spoofed_parts = |act: &Act| {
        act.dir == 0 && act.every && !matches!(&act.forge, Forge::Copy(e) if e.is_empty())
    };
    c.acts.iter().any(spoofed_parts).then_some("D: spoofed fragments keep the first message from completing intact")
}

/// [`run`], letting the causes of `repro_core2.rs` pass when `exclude_known`.
pub fn run_with(c: &Case, exclude_known: bool) {
    let mut net = Net::new(c.seed);
    net.delay = c.delay_ms * MS;
    net.faults.jitter = c.jitter_ms * MS;
    net.capture_max = 4000;
    let cfg = HostCfg {
        split: c.split,
        room: c.room,
        ..HostCfg::default()
    };
    let (a, b) = (net.add(1, cfg), net.add(2, cfg));
    let (ca, sa_addr, peer) = (net.hosts[a].addr, net.hosts[b].addr, net.hosts[b].id);
    let t0 = net.now;
    let Ok(core_harness::Reply2 {
        value: Value::Session(sa),
    }) = net.hosts[a].cmd(
        t0,
        Command::Connect {
            node: peer,
            alpn: ALPN_A,
            addrs: &[sa_addr],
            role: Role::Other,
        },
    )
    else {
        panic!("the dial was refused");
    };
    net.faults.cut = c.drop_first;
    let mut tap = Tap::new();
    let incoming = |n: &Net| n.hosts[b].count(|e| matches!(e, Event::Incoming { .. }));
    net.run(t0 + CONNECT_LIMIT + 2 * SEC, |n| {
        tap.step(n, c, ca, sa_addr, t0);
        n.hosts[a].opened.contains(&sa) && incoming(n) > 0
    });
    fail(net.first_violation());
    let up = net.hosts[a].opened.contains(&sa);
    let at = net.hosts[a]
        .events
        .iter()
        .find(|(_, e)| matches!(e, Event::Connected { session, .. } if *session == sa))
        .map(|(t, _)| *t);
    if !(up && at.is_some_and(|t| t <= t0 + CONNECT_LIMIT) && incoming(&net) > 0) {
        if exclude_known && known_cause(&net, c, a, b, ca, sa_addr).is_some() {
            return;
        }
        let s = net.hosts[b].ep.node_stats();
        let ended: Vec<_> = net.hosts[a].events.iter().filter(|(_, e)| matches!(e, Event::Closed { .. } | Event::ConnectFailed { .. })).collect();
        let detail = format!(
            "client up {up} at {:?} ms, server incoming {}; client ended {ended:?}; server sent (bytes to): {:?}; client sent (bytes to): {:?}, dropped_in {}; server: half_open {} sessions {} holders_refused {} fragments held {} replayed {} expired {} evicted {} dropped_in {}; forged {:?}",
            at.map(|t| (t - t0) / MS),
            incoming(&net),
            net.sent_to.iter().filter(|((h, _), _)| *h == b).map(|((_, to), n)| (*to, *n)).collect::<Vec<_>>(),
            net.sent_to.iter().filter(|((h, _), _)| *h == a).map(|((_, to), n)| (*to, *n)).collect::<Vec<_>>(),
            net.hosts[a].ep.node_stats().dropped_in,
            s.half_open,
            s.sessions,
            s.holders_refused,
            s.fragments_held,
            s.fragments_replayed,
            s.fragments_expired,
            s.fragments_evicted,
            s.dropped_in,
            tap.log.iter().map(|(t, to_s, l)| ((t - t0) / MS, *to_s, *l)).collect::<Vec<_>>(),
        );
        if tap.injected == 0 {
            ephyra::signature("the honest handshake failed on a link that turned clean, with no third party");
        } else if races(c) {
            ephyra::signature("a third party that races the genuine datagrams blocked the honest handshake");
        } else if c.drop_first || (c.loss > 0 && c.lossy_ms > 0) {
            ephyra::signature("a third party whose datagrams stand in for lost ones blocked the honest handshake");
        } else {
            ephyra::signature("a third party off the path blocked the honest handshake");
        }
        panic!("the honest handshake did not complete within the connect limit: {detail}");
    }
    // The forgeries stop with the handshake's datagrams; every half-open session they made is gone one tick past its
    // life (at most 60 s).
    let last = tap.log.iter().map(|l| l.0).max().unwrap_or(t0).max(net.now);
    let end = last + 61 * SEC + 10 * MS;
    net.run(end, |n| {
        tap.step(n, c, ca, sa_addr, t0);
        false
    });
    fail(net.first_violation());
    let last = tap.log.iter().map(|l| l.0).max().unwrap_or(t0);
    if last + 61 * SEC + 10 * MS <= net.now {
        let s = net.hosts[b].ep.node_stats();
        assert!(s.half_open == 0, "{} half-open sessions are left 61 s after the last forgery", s.half_open);
    }
}

pub fn in_support(c: &Case) -> bool {
    c.acts.len() <= 6 && (1..=60).contains(&c.delay_ms) && c.lossy_ms <= 6000 && c.loss <= 400
}

/// A case with no third party, no loss: the control.
pub fn quiet(split: bool) -> Case {
    Case {
        seed: 1,
        split,
        room: true,
        delay_ms: 10,
        jitter_ms: 0,
        drop_first: false,
        loss: 0,
        lossy_ms: 0,
        acts: Vec::new(),
    }
}

