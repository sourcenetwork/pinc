//! Trace generation for the path a dialing side's handshake reply arrives on (vinc#399) and the path table of the
//! connection: real dialing sides (`Connection::client` against a real responder) driven through a reply that comes
//! back on the dialed path, on another path the dial holds, on a path it does not hold, on one its table gave up, at a
//! full table, cut over two paths, after forged Replies and after a prekey reject, a resume Reply, and a resume Reply
//! with a 1-RTT packet behind it in the same datagram. After every call the dialing side's path table (`path_list`, in
//! slot order with the kind of each path, direct or relay, and `active_path`), whether it is established, whether its
//! round trip has a sample and its dropped handshake count are recorded as ndjson (`reply_path.ndjson`) for the TLA+
//! trace check (`TraceReplyPath.tla`) and the Lean replay (`Vinc/TraceReplyPath.lean`). Four runs dial on a relay path.
//!
//! A datagram is recorded with the path it arrived on, with what its handshake packet completed as the connection
//! answered it (`bad` the dropped count rose, `auth` the session was established by it, `pend` it raised a key request:
//! a Reply that passed its first checks, `rej` a whole reject it took, `other` a refusal, `none` no message completed),
//! and with whether a 1-RTT packet is in it (`coal`). Key requests are answered one by one (`ok` the
//! session was established, `bad` the dropped count rose, `more` another request followed).
//!
//! The test asserts what it can itself: each reply that authenticates establishes the session on the path it came
//! on, a forged one adds no path and moves nothing, the table never holds more than its 4 places, and no path is held
//! twice. The last two runs are the case the model found (`ReplyPath_coalesced.cfg`, the rule before the correction):
//! a resume Reply with a 1-RTT packet behind it, on a path the dial does not hold, holds that path once, and at a full
//! table gives up one path, not the one the session left.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    unreachable_pub
)]

use std::cell::RefCell;
use std::fmt::Write as _;
use std::rc::Rc;

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{PathError, PathId, PathInfo};
use vinc_transport::packet::{Header, packets};
use vinc_transport::recovery::PathKind;

/// The length of the connection ids in a 1-RTT header: the transport's default.
const CID_LEN: usize = 4;

/// The recorded events, and what they covered.
#[derive(Default)]
struct Log {
    out: String,
    run: u32,
    kinds: Vec<&'static str>,
    keys: Vec<&'static str>,
    coal: bool,
}

fn kind(k: PathKind) -> &'static str {
    if k == PathKind::Relay { "relay" } else { "direct" }
}

fn view(c: &Conn<'_>) -> String {
    let paths: Vec<String> = c
        .path_list()
        .map(|(id, info, v)| format!(r#"{{"id":{},"v":{v},"kind":"{}"}}"#, id.0, kind(info.kind)))
        .collect();
    format!(
        r#"{{"paths":[{}],"act":{},"est":{},"smp":{},"hd":{}}}"#,
        paths.join(","),
        c.active_path().map_or(0, |p| p.0),
        c.is_connected(),
        c.rtt_estimate().has_sample(),
        c.stats().handshake_dropped
    )
}

fn log(l: &mut Log, net: &Net<'_, '_>, body: &str) {
    let _ = writeln!(
        l.out,
        r#"{{"t":"rp","run":{},{body},"v":{}}}"#,
        l.run,
        view(&net.a.conn)
    );
}

/// A new run: the dialing side holds its dialed path 1, a relay path when `relay`. Its key requests wait for the test.
fn start(l: &mut Log, net: &mut Net<'_, '_>, relay: bool) {
    l.run += 1;
    net.a.auto_keys = false;
    let k = if relay { "relay" } else { "direct" };
    log(l, net, &format!(r#""op":"init","np":4,"id":1,"kind":"{k}""#));
}

fn add(l: &mut Log, net: &mut Net<'_, '_>, p: u64) {
    let now = net.now;
    let r = net
        .a
        .with_env(now, |c, env| c.add_path(env, PathId(p), PathInfo::default()));
    let r = if r.is_ok() { "ok" } else { "toomany" };
    log(l, net, &format!(r#""op":"add","id":{p},"r":"{r}""#));
}

fn rm(l: &mut Log, net: &mut Net<'_, '_>, p: u64) {
    let r = match net.a.conn.remove_path(PathId(p)) {
        Ok(()) => "ok",
        Err(PathError::Active) => "active",
        Err(_) => "unknown",
    };
    log(l, net, &format!(r#""op":"rm","id":{p},"r":"{r}""#));
}

/// Whether the datagram holds a 1-RTT packet to the dialing side (behind its handshake packet, or alone).
fn has_short(c: &Conn<'_>, d: &[u8]) -> bool {
    let mut d = d.to_vec();
    packets(&mut d, CID_LEN)
        .any(|p| matches!(p, Ok(p) if matches!(p.header, Header::Short { dcid } if c.local_cids().any(|l| l == dcid))))
}

/// Whether the datagram carries a whole reject (a prekey or a resume reject).
fn is_reject(d: &[u8]) -> bool {
    first_message([d]).is_some_and(|m| matches!(m.first(), Some(3 | 8)))
}

/// Hand the datagram `d` to the dialing side as arriving on path `p`.
fn rx(l: &mut Log, net: &mut Net<'_, '_>, p: u64, d: &[u8]) {
    let now = net.now;
    let (est, hd, keyed) = (
        net.a.conn.is_connected(),
        net.a.conn.stats().handshake_dropped,
        net.a.deferred.is_some(),
    );
    let (coal, rej) = (has_short(&net.a.conn, d), is_reject(d));
    let mut d = d.to_vec();
    let r = net.a.with_env(now, |c, env| c.handle_datagram(env, PathId(p), &mut d));
    assert!(
        !matches!(r, Err(vinc_transport::conn::Drop::NoPath)),
        "a datagram on path {p} was dropped for its path"
    );
    net.a.service(now);
    let k = if net.a.conn.stats().handshake_dropped > hd {
        "bad"
    } else if !est && net.a.conn.is_connected() {
        "auth"
    } else if !keyed && net.a.deferred.is_some() {
        "pend"
    } else if rej && r.is_ok() {
        "rej"
    } else if r.is_err() {
        "other"
    } else {
        "none"
    };
    l.kinds.push(k);
    l.coal |= coal;
    log(l, net, &format!(r#""op":"rx","id":{p},"k":"{k}","coal":{coal}"#));
}

/// Answer the key requests one by one until none is left.
fn keys(l: &mut Log, net: &mut Net<'_, '_>) {
    while net.a.deferred.is_some() {
        let now = net.now;
        let (est, hd) = (net.a.conn.is_connected(), net.a.conn.stats().handshake_dropped);
        let _ = net.a.deliver_deferred(now);
        net.a.service(now);
        let r = if !est && net.a.conn.is_connected() {
            "ok"
        } else if net.a.conn.stats().handshake_dropped > hd {
            "bad"
        } else {
            "more"
        };
        l.keys.push(r);
        log(l, net, &format!(r#""op":"key","r":"{r}""#));
    }
}

/// Run the pair until the responder has answered, with nothing it sends reaching the dialing side, and return what it
/// sent. The dialing side's flights go out on its path 1.
fn answer(net: &mut Net<'_, '_>) -> Vec<Vec<u8>> {
    net.link.route(PathId(1)).ba.p.loss_ppm = 1_000_000;
    let sent: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
    let sink = Rc::clone(&sent);
    net.on_tx = Some(Box::new(move |is_a, d, _| {
        if !is_a {
            sink.borrow_mut().push(d.to_vec());
        }
    }));
    let until = net.now + 100 * MS;
    net.run(until, |_| false);
    net.on_tx = None;
    let got = sent.borrow().clone();
    assert!(!got.is_empty(), "the responder sent nothing");
    got
}

/// How many of `datagrams`, from the first, carry the first handshake message whole.
fn message_len(datagrams: &[Vec<u8>]) -> usize {
    (1..=datagrams.len())
        .find(|n| first_message(datagrams[..*n].iter().map(Vec::as_slice)).is_some())
        .expect("the datagrams carry a whole message")
}

fn held(net: &Net<'_, '_>, p: u64) -> bool {
    net.a.conn.has_path(PathId(p))
}

fn active(net: &Net<'_, '_>) -> u64 {
    net.a.conn.active_path().map_or(0, |p| p.0)
}

/// The table holds at most its 4 places and no path twice.
fn bounded(net: &Net<'_, '_>) {
    let ids: Vec<u64> = net.a.conn.path_list().map(|(id, _, _)| id.0).collect();
    assert!(ids.len() <= 4, "the table holds more than its places: {ids:?}");
    let mut once = ids.clone();
    once.sort_unstable();
    once.dedup();
    assert_eq!(once.len(), ids.len(), "a path is held twice: {ids:?}");
}

/// A full handshake whose Reply comes back on `p` after the host added `added` (and removed `removed`).
fn full(l: &mut Log, alg: IdentityAlg, seed: u64, added: &[u64], removed: &[u64], p: u64) {
    full_on(l, alg, seed, added, removed, p, false);
}

/// `full` with the dial sent on a relay path when `relay`: the path the session leaves then stays validated.
fn full_on(l: &mut Log, alg: IdentityAlg, seed: u64, added: &[u64], removed: &[u64], p: u64, relay: bool) {
    let mut w = World::new(alg);
    if relay {
        w.dial_info = PathInfo {
            kind: PathKind::Relay,
            ..PathInfo::default()
        };
    }
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, Params::new(10 * MS)));
    start(l, &mut net, relay);
    for &q in added {
        add(l, &mut net, q);
    }
    for &q in removed {
        rm(l, &mut net, q);
    }
    let reply = answer(&mut net);
    for d in &reply {
        rx(l, &mut net, p, d);
    }
    keys(l, &mut net);
    assert!(net.a.conn.is_connected(), "the Reply on path {p} was not taken");
    assert!(held(&net, p) && active(&net) == p && net.a.conn.path_validated(PathId(p)));
    if relay && p != 1 {
        assert!(
            held(&net, 1) && net.a.conn.path_validated(PathId(1)),
            "the relay path the session left is no longer validated"
        );
    }
    // Once established, a dialing side takes no handshake packet: the Reply again, on a path it does not hold.
    rx(l, &mut net, 7, &reply[0]);
    assert!(!held(&net, 7) && active(&net) == p);
    bounded(&net);
}

/// A Reply cut over two paths: the datagrams before the last one of the message on `p`, the rest on `q`; the session
/// goes where the message completed.
fn split(l: &mut Log, seed: u64, p: u64, q: u64) {
    let mut w = World::new(IdentityAlg::Hybrid);
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, Params::new(10 * MS)));
    start(l, &mut net, false);
    let reply = answer(&mut net);
    let n = message_len(&reply);
    assert!(n > 1, "the Reply fits one datagram");
    for (i, d) in reply.iter().enumerate() {
        rx(l, &mut net, if i + 1 < n { p } else { q }, d);
    }
    keys(l, &mut net);
    assert!(net.a.conn.is_connected());
    assert_eq!(active(&net), q, "the session is not on the path the Reply completed on");
    bounded(&net);
}

/// Forged Replies on paths the dial does not hold, then the real one on one of them.
fn forged(l: &mut Log, seed: u64) {
    let mut w = World::new(IdentityAlg::Ed25519);
    let id = w.rp.id;
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, Params::new(10 * MS)));
    start(l, &mut net, false);
    net.link.route(PathId(1)).ba.p.loss_ppm = 1_000_000;
    let initial = sent_initial(&mut net);
    let dcid = net.a.conn.local_cids().next().unwrap();
    let zero_key = forge_message(dcid, &forge_reply(&net.a.prov, &initial, &Forgery::ZeroKey));
    let zero_sig = forge_message(
        dcid,
        &forge_reply(
            &net.a.prov,
            &initial,
            &Forgery::ZeroSignature {
                alg: id.alg(),
                public_key: id.public_key().to_vec(),
            },
        ),
    );
    rx(l, &mut net, 9, &zero_key);
    rx(l, &mut net, 8, &zero_sig);
    // While that Reply waits for the key host another one is refused, uncounted, on a path the dial does not hold.
    rx(l, &mut net, 7, &zero_key);
    assert!(!held(&net, 7));
    keys(l, &mut net);
    assert_eq!(
        net.a.conn.stats().handshake_dropped,
        2,
        "the forged Replies were not both counted"
    );
    assert!(!held(&net, 9) && !held(&net, 8) && active(&net) == 1);
    assert!(!net.a.conn.rtt_estimate().has_sample() && !net.a.conn.is_connected());
    let reply = answer(&mut net);
    for d in &reply {
        rx(l, &mut net, 9, d);
    }
    keys(l, &mut net);
    assert!(net.a.conn.is_connected() && active(&net) == 9 && !held(&net, 8));
    bounded(&net);
}

/// A prekey reject on a path the dial does not hold is taken (the full Initial follows) and moves nothing; the Reply
/// then comes back on the dialed path, where the session stays.
fn reject(l: &mut Log, seed: u64) {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.short = true;
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, Params::new(10 * MS)));
    start(l, &mut net, false);
    let rejects = answer(&mut net);
    let first = rejects.first().unwrap().clone();
    rx(l, &mut net, 9, &first);
    assert!(!held(&net, 9) && active(&net) == 1);
    let reply = answer(&mut net);
    for d in &reply {
        rx(l, &mut net, 1, d);
    }
    keys(l, &mut net);
    assert!(net.a.conn.is_connected() && active(&net) == 1 && !held(&net, 9));
    bounded(&net);
}

/// A resume Reply on path `p` after the host added `added`; `coalesce`: the responder's next datagram (a 1-RTT packet)
/// rides in the same datagram.
fn resume(l: &mut Log, seed: u64, added: &[u64], p: u64, coalesce: bool) {
    let mut w = World::new(IdentityAlg::Ed25519);
    let mut tickets = first_session(&mut w);
    let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
    let b = w.server(&mut sb);
    let mut net = Net::new(a, b, Link::new(seed, Params::new(10 * MS)), &mut w.stores);
    start(l, &mut net, false);
    for &q in added {
        add(l, &mut net, q);
    }
    let mut reply = answer(&mut net);
    if coalesce {
        assert!(
            reply.len() >= 2 && has_short(&net.a.conn, &reply[1]),
            "no 1-RTT datagram follows the resume Reply"
        );
        let tail = reply.remove(1);
        reply[0].extend_from_slice(&tail);
    }
    for d in &reply {
        rx(l, &mut net, p, d);
    }
    keys(l, &mut net);
    assert!(net.a.conn.is_connected(), "the resume Reply on path {p} was not taken");
    assert!(held(&net, p) && active(&net) == p && net.a.conn.path_validated(PathId(p)));
    if p != 1 {
        assert!(held(&net, 1), "the path the session left was given up");
    }
    // At a full table the reply's path took the place of exactly one of the paths that did not validate.
    if added.len() >= 3 {
        let kept = added.iter().filter(|q| held(&net, **q)).count();
        assert_eq!(kept, added.len() - 1, "not exactly one path was given up");
    }
    bounded(&net);
}

#[test]
fn reply_path_traces() {
    big_stack(|| {
        let mut l = Log::default();
        // The Reply on the dialed path, on another path the dial holds, on a path it does not hold, on one its table
        // gave up, and at a full table of paths that did not validate.
        full(&mut l, IdentityAlg::Ed25519, 81, &[], &[], 1);
        full(&mut l, IdentityAlg::Ed25519, 82, &[2], &[], 2);
        full(&mut l, IdentityAlg::Ed25519, 83, &[], &[], 9);
        full(&mut l, IdentityAlg::Ed25519, 84, &[9], &[9], 9);
        full(&mut l, IdentityAlg::Ed25519, 85, &[3, 4, 5, 6], &[], 9);
        full(&mut l, IdentityAlg::Hybrid, 86, &[3], &[], 9);
        // The dial sent on a relay path: the relay path the session leaves stays validated, and a full table gives up
        // one of the paths that did not validate, not the relay path.
        full_on(&mut l, IdentityAlg::Ed25519, 95, &[], &[], 9, true);
        full_on(&mut l, IdentityAlg::Ed25519, 96, &[2], &[], 2, true);
        full_on(&mut l, IdentityAlg::Ed25519, 97, &[3, 4, 5], &[], 9, true);
        full_on(&mut l, IdentityAlg::Ed25519, 98, &[], &[], 1, true);
        split(&mut l, 87, 9, 1);
        split(&mut l, 88, 1, 9);
        forged(&mut l, 89);
        reject(&mut l, 90);
        resume(&mut l, 91, &[], 1, false);
        resume(&mut l, 92, &[], 9, false);
        // A resume Reply with a 1-RTT packet behind it in the same datagram, on a path the dial does not hold: the path
        // is held once, and at a full table one path is given up, not the one the session left.
        resume(&mut l, 93, &[], 9, true);
        resume(&mut l, 94, &[3, 4, 5], 9, true);
        if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
            std::fs::write(std::path::Path::new(&dir).join("reply_path.ndjson"), &l.out).unwrap();
        }
        for k in ["bad", "auth", "pend", "rej", "other"] {
            assert!(l.kinds.contains(&k), "no datagram was taken as {k}: {:?}", l.kinds);
        }
        for k in ["ok", "more", "bad"] {
            assert!(l.keys.contains(&k), "no key answer was {k}: {:?}", l.keys);
        }
        assert!(l.coal, "no datagram carried a 1-RTT packet");
    });
}
