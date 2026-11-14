//! The scripted pair of the timers trace: two connected nodes with a pool of datagrams, the calls that drive one node
//! and write the log, and the hand-over from the in-memory link.

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{Drop, PathId, code};
use vinc_wire::Writer;

use crate::rec::{Log, carrier_decision, ous, probe_json};

/// How a pool datagram is handed over.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum How {
    Fresh,
    Again,
    Altered,
}

/// Two connected nodes, the datagrams they wrote, and the time.
pub struct Duo<'a, 'b> {
    pub nodes: [Node<'a>; 2],
    pub stores: &'b mut Stores,
    pub now: u64,
    /// `(from, bytes, delivered)`.
    pub pool: Vec<(usize, Vec<u8>, bool)>,
    pub buf: Vec<u8>,
}

/// One node's calls, written to the log.
pub fn init(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64) {
    log.line(n, node, now, "init", "");
}

pub fn poll(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64) -> Option<u64> {
    let t = node.conn.poll_timeout();
    let out = t.map_or(-1, |t| i64::try_from(t.div_ceil(1000)).unwrap());
    log.line(n, node, now, "poll", &format!(r#","out":{out}"#));
    if node.conn.is_closed() && !node.conn.is_connected() && t.is_some() {
        assert_eq!(t, Some(0), "a closing connection runs its timer at once");
    }
    t
}

pub fn timeout(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64) -> Vec<&'static str> {
    node.with_env(now, Conn::handle_timeout);
    let probe = node.conn.trace_carrier_take();
    let extra = probe_json(probe.as_ref());
    let ev = log.line(n, node, now, "timeout", &extra);
    if let Some(p) = probe.filter(|p| p.ping && !p.dead) {
        let (close, v) = (carrier_decision(&p, now), node.conn.trace_timers());
        let fresh = p.carrier.is_some_and(|h| now.saturating_sub(h) < 6 * SEC);
        let rtt = if p.sampled { p.srtt } else { (333 * MS).max(p.node * 2) };
        let silent = now.saturating_sub(p.heard) >= rtt * 4;
        let seen = &mut log.seen;
        let mut note = |k: &'static str| *seen.entry(k).or_default() += 1;
        if close {
            assert!(
                ev.contains(&"dead") && v.close == Some(0),
                "no close behind a live carrier: {p:?}"
            );
            note("carrier_close");
            note(if p.sampled {
                "carrier_close_sampled"
            } else {
                "carrier_close_unsampled"
            });
        } else if p.relay {
            assert!(
                !ev.contains(&"dead"),
                "a close behind a carrier outside the rule: {p:?}"
            );
            if fresh && silent && p.ptos < 4 {
                note("near_pto3");
            }
            if p.carrier.is_some() && !fresh && silent && p.ptos >= 4 {
                note("near_stale");
            }
            if p.carrier.is_none() && silent && p.ptos >= 4 {
                note("near_nocarrier");
            }
            if fresh && !silent && p.ptos >= 4 {
                note(if p.sampled {
                    "near_heard_sampled"
                } else {
                    "near_heard_unsampled"
                });
            }
        } else if fresh && silent && p.ptos >= 4 {
            note("near_direct");
        }
    }
    ev
}

pub fn close(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64, err: u64) {
    node.with_env(now, |c, env| c.close(env, err));
    log.line(n, node, now, "close", &format!(r#","err":{err}"#));
}

pub fn simple(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64, op: &str, arg: u64) {
    let extra = match op {
        "sleep" => {
            node.with_env(now, Conn::sleep);
            String::new()
        }
        "wake" => {
            node.with_env(now, Conn::wake);
            String::new()
        }
        "link" => {
            let down = arg != 0;
            node.with_env(now, |c, env| c.set_link_down(env, down));
            format!(r#","down":{down}"#)
        }
        "keepalive" => {
            let ka = (arg != 0).then_some(arg);
            node.conn.set_keepalive(ka);
            format!(r#","ka":{}"#, ous(ka))
        }
        "pulse" => {
            let sent = arg != 0;
            node.conn.pulse(now, sent);
            format!(r#","sent":{sent}"#)
        }
        _ => unreachable!(),
    };
    log.line(n, node, now, op, &extra);
}

/// The application opens a stream and writes `len` bytes on it.
pub fn app(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64, len: usize) {
    let r = node.conn.open_bi().and_then(|id| node.conn.write(id, &vec![0x5a; len]));
    let ok = r.is_ok();
    if node.conn.is_closed() {
        assert!(!ok, "a closed connection took application data");
    }
    log.line(n, node, now, "app", &format!(r#","ok":{ok}"#));
}

/// Frames injected as an authenticated packet: `bad` ones do not decode, the others acknowledge a packet that was
/// never sent.
pub fn inject(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64, path: PathId, bad: bool) {
    assert!(!node.conn.is_closed());
    let mut buf = [0u8; 64];
    let len = if bad {
        buf[0] = 0x06;
        1
    } else {
        let mut w = Writer::new(&mut buf);
        vinc_transport::frame::write_ack(&mut w, core::iter::once(1_000_000u64..=1_000_000)).unwrap();
        w.written().len()
    };
    let _ = node.with_env(now, |c, env| c.inject_payload(env, path, now, 1 << 40, &buf[..len]));
    let (kind, err) = if bad {
        ("bad", code::FRAME_ENCODING)
    } else {
        ("viol", code::PROTOCOL_VIOLATION)
    };
    log.line(n, node, now, "inject", &format!(r#","kind":"{kind}","err":{err}"#));
}

impl Duo<'_, '_> {
    pub fn init(&mut self, log: &mut Log) {
        for n in 0..2 {
            init(log, n, &mut self.nodes[n], self.now);
        }
    }

    pub fn poll(&mut self, log: &mut Log, n: usize) -> Option<u64> {
        poll(log, n, &mut self.nodes[n], self.now)
    }

    pub fn timeout(&mut self, log: &mut Log, n: usize) -> Vec<&'static str> {
        timeout(log, n, &mut self.nodes[n], self.now)
    }

    /// `poll_transmit` until it has nothing; every call is an event. Returns the datagrams written.
    pub fn tx(&mut self, log: &mut Log, n: usize) -> usize {
        let mut made = 0;
        for _ in 0..64 {
            let now = self.now;
            let phase = self.nodes[n].conn.trace_timers().phase;
            let (closing, was_closed) = (phase == 2, phase == 3);
            let buf = &mut self.buf;
            let r = self.nodes[n].with_env(now, |c, env| c.poll_transmit(env, buf));
            let len = r.map_or(0, |t| t.len);
            log.line(n, &mut self.nodes[n], now, "tx", &format!(r#","len":{len}"#));
            let Some(t) = r else { break };
            assert!(!was_closed, "a closed connection wrote a datagram");
            if closing {
                log.closes[n] += 1;
                assert!(log.closes[n] <= 1, "a second CLOSE left");
            }
            for seg in self.buf[..t.len].chunks(t.segment_size) {
                self.pool.push((n, seg.to_vec(), false));
                made += 1;
            }
        }
        made
    }

    /// Hand pool datagram `i` to the other node.
    pub fn deliver(&mut self, log: &mut Log, i: usize, how: How) {
        let (from, mut bytes, _) = self.pool[i].clone();
        self.pool[i].2 = true;
        if how == How::Altered {
            let last = bytes.len() - 1;
            bytes[last] ^= 0x40;
        }
        let to = 1 - from;
        let now = self.now;
        let was_closed = self.nodes[to].conn.is_closed();
        let r = if to == 0 {
            self.nodes[0].with_env(now, |c, env| c.handle_datagram(env, PathId(1), &mut bytes))
        } else {
            let stores = &mut *self.stores;
            self.nodes[1].with_env(now, |c, env| c.handle_datagram_with(env, stores, PathId(2), &mut bytes))
        };
        let res = match r {
            Ok(()) => "ok",
            Err(Drop::Duplicate) => "dup",
            Err(Drop::Undecryptable) => "undecryptable",
            Err(Drop::Closed) => "closed",
            Err(Drop::Unroutable) => "unroutable",
            Err(e) => panic!("an unexpected refusal {e:?}"),
        };
        if was_closed {
            assert_eq!(res, "closed", "a closed connection took a datagram");
        }
        if how == How::Altered {
            assert!(res != "ok", "an altered datagram was taken");
        }
        log.line(to, &mut self.nodes[to], now, "recv", &format!(r#","res":"{res}""#));
    }

    /// Hand every waiting datagram over, in order.
    pub fn deliver_all(&mut self, log: &mut Log) {
        for i in 0..self.pool.len() {
            if !self.pool[i].2 {
                self.deliver(log, i, How::Fresh);
            }
        }
    }

    /// Lose every waiting datagram.
    pub fn lose_all(&mut self) {
        for d in &mut self.pool {
            d.2 = true;
        }
    }

    /// Both sides write, every datagram arrives, until quiet (a few rounds).
    pub fn exchange(&mut self, log: &mut Log) {
        for _ in 0..6 {
            let m = self.tx(log, 0) + self.tx(log, 1);
            self.deliver_all(log);
            if m == 0 {
                break;
            }
        }
    }

    /// The earliest timer of the open nodes.
    pub fn next_deadline(&self) -> Option<u64> {
        self.nodes.iter().filter_map(|x| x.conn.poll_timeout()).min()
    }

    /// Move to the next deadline (rounded up to a microsecond, never back), and run the timers that are due.
    pub fn advance_to_next(&mut self, log: &mut Log) -> bool {
        let Some(t) = self.next_deadline() else { return false };
        self.now = self.now.max(t.div_ceil(1000) * 1000);
        self.fire(log);
        true
    }

    /// Poll both nodes and run the timers that are due.
    pub fn fire(&mut self, log: &mut Log) {
        for n in 0..2 {
            if self.poll(log, n).is_some_and(|t| t <= self.now) {
                self.timeout(log, n);
            }
        }
    }
}

/// Hand the nodes of `net` to `f` as a scripted pair, at its time rounded up to a millisecond, their events served.
pub fn take_over<'a, 'b>(net: Net<'a, 'b>, f: impl FnOnce(&mut Duo<'a, 'b>)) {
    let Net { a, b, stores, now, .. } = net;
    let mut d = Duo {
        nodes: [a, b],
        stores,
        now: now.div_ceil(MS) * MS,
        pool: Vec::new(),
        buf: vec![0u8; 65_536],
    };
    for x in &mut d.nodes {
        while x.conn.poll_event().is_some() {}
    }
    f(&mut d);
}

/// Connect two nodes over the in-memory link, then hand them to `f` as a scripted pair.
pub fn with_pair(seed: u64, thin: bool, f: impl FnOnce(&mut Duo<'_, '_>)) {
    with_pair_at(seed, thin, false, f);
}

/// As [`with_pair`]; with `resent` the first flight of the dial is lost and its resend answered, so the handshake
/// measures no round trip and the connection has no round-trip sample.
pub fn with_pair_at(seed: u64, thin: bool, resent: bool, f: impl FnOnce(&mut Duo<'_, '_>)) {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.thin = thin;
    w.seed = seed as u8;
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, Params::new(10 * MS)));
    if resent {
        net.link.route(PathId(1)).up = false;
        net.run(net.now + SEC, |_| false);
        net.link.route(PathId(1)).up = true;
    }
    assert!(net.connect(net.now + 30 * SEC));
    if !resent {
        net.run(net.now + 100 * MS, |_| false);
    }
    take_over(net, f);
}
