//! Trace generation for the relay: seeded random runs of the real `Relay` through its public API, recorded as ndjson
//! (`connect.ndjson`) for the TLA+ trace check (`TraceConnect.tla`) and the Lean replay (`Pinc/TraceConnect.lean`).
//!
//! A run is one relay of three session slots, four record slots and a mailbox of two members, with six nodes that open
//! carriers (four of them hold keys, so they sign records and sleep notices), three peer relays and an unknown
//! node. Calls: carrier opened and closed (current and stale sessions), frames from a node (SEND in its three forms,
//! SELF, PING, PONG, an unexpected RECV, PUB of an own and of a foreign record, SLEEP of an own, a foreign and a
//! mis-signed notice), frames from peer relays and from a node that is no peer (FWD, SYNC, PING, PONG, an unexpected
//! frame), `add_peer` and `remove_peer`, `udp_heard` and `udp_gone`, SPU datagrams with and without a validated
//! member, `member_returned`, sleep notices over UDP, the host's `tunnel_ready` answer for a member (changed by a call
//! of its own, so a held message is refused and kept), and `handle_timeout`. Times step by amounts around every rule
//! constant (10, 15, 20, 30 s, the sweep, the quota window, the session limit, the mailbox age); every time is a whole
//! number of seconds, written in seconds (the Lean replay multiplies by 10^9 and TLC keeps 32-bit integers).
//!
//! What is recorded is what an observer sees: the call, its arguments as small ids, the answer, and every effect the
//! relay emitted in order (frames to carriers, peers and UDP, closes, wake-ups and every `Trace` transition). The
//! checkers replay the call on their model and require the same answer and the same effects in the same order.
//! The bucket of every node in the relay's tables is recorded first (`Table::bucket_of` of the same seed and capacity),
//! so the checkers use the hash of the real code and the order in which the session table is swept.
//! What is not covered: a record or notice that is malformed (the record and notice codecs have their own checks), the
//! lookup and address discovery answers, the relay's own record and its republish timer. Signatures are an oracle: the
//! trace says whether a record or notice was validly signed for this relay by its node.
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
    clippy::type_complexity,
    clippy::same_functions_in_if_condition,
    clippy::manual_is_multiple_of,
    clippy::cast_possible_wrap,
    unreachable_pub
)]

mod connect_common;

use std::fmt::Write as _;

use connect_common::{addr, ed, id, nid, notice, record_bytes};
use pinc_connect::carrier::Frame;
use pinc_connect::relay::datagram::Datagram;
use pinc_connect::relay::sleep::SleepError;
use pinc_connect::relay::table::Table;
use pinc_connect::relay::{
    CloseReason, Config, Effect, Quota, RecordOrigin, Reject, Relay, Route, SessionId, Sink, Trace, UdpTarget,
};
use pinc_crypto::{Keypair, NodeId};
use pinc_tests::SplitMix64;

const SEC: u64 = 1_000_000_000;

struct Names(Vec<NodeId>);

impl Names {
    fn n(&self, id: &NodeId) -> usize {
        self.0.iter().position(|x| x == id).map_or(99, |p| p + 1)
    }
    fn opt(&self, id: Option<NodeId>) -> usize {
        id.map_or(0, |i| self.n(&i))
    }
}

fn reject_name(r: Reject) -> String {
    match r {
        Reject::Unauthenticated => "unauth".into(),
        Reject::UnexpectedFrame => "unexpected".into(),
        Reject::UnknownAlias => "unkalias".into(),
        Reject::StaleSession => "stale".into(),
        Reject::Quota => "quota".into(),
        Reject::SessionsFull => "full".into(),
        Reject::NoRoute => "noroute".into(),
        Reject::NoPeerSession => "nopeer".into(),
        Reject::NoTunnel => "notunnel".into(),
        Reject::StoreFull => "storefull".into(),
        Reject::BadRecord(_) => "badrecord".into(),
        Reject::StaleRecord => "stalerec".into(),
        Reject::WrongOwner => "wrongowner".into(),
        Reject::BadSleep(SleepError::Skew) => "skew".into(),
        Reject::BadSleep(SleepError::UnknownNode) => "unknown".into(),
        Reject::BadSleep(SleepError::WrongSender) => "wrongsender".into(),
        Reject::BadSleep(SleepError::Signature(_)) => "sig".into(),
        Reject::BadSleep(SleepError::Wire(_)) => "wire".into(),
        Reject::BadDatagram(_) => "baddg".into(),
        Reject::BadFrame(_) => "badframe".into(),
        Reject::MailboxRefused => "mbrefused".into(),
    }
}

/// Collects effects as JSON arrays.
struct Rec<'a> {
    names: &'a Names,
    out: Vec<String>,
    /// Bit `n` is set when node `n` (as `Names::n` numbers it) has no validated direct route.
    off: u16,
}

impl Sink for Rec<'_> {
    fn tunnel_ready(&self, node: &NodeId) -> bool {
        let n = self.names.n(node);
        n >= 16 || self.off & (1 << n) == 0
    }

    fn emit(&mut self, e: Effect<'_>) {
        let n = |x: &NodeId| self.names.n(x);
        let s = match e {
            Effect::Carrier { to, frame } => match frame {
                Frame::RecvNew {
                    src,
                    alias,
                    flag,
                    packet,
                } => format!(r#"["car",{},"rn",{},{alias},{flag},{}]"#, n(&to), n(&src), packet.len()),
                Frame::RecvAlias { alias, flag, packet } => {
                    format!(r#"["car",{},"ra",{alias},{flag},{}]"#, n(&to), packet.len())
                }
                Frame::Pong => format!(r#"["car",{},"pong"]"#, n(&to)),
                Frame::Ping => format!(r#"["car",{},"ping"]"#, n(&to)),
                Frame::SelfRecv { packet } => format!(r#"["car",{},"sr",{}]"#, n(&to), packet.len()),
                other => panic!("unexpected carrier frame {other:?}"),
            },
            Effect::PeerRelay { to, frame } => match frame {
                Frame::Forward { src, dst, flag, packet } => {
                    format!(
                        r#"["peer",{},"fwd",{},{},{flag},{}]"#,
                        n(&to),
                        n(&src),
                        n(&dst),
                        packet.len()
                    )
                }
                Frame::Sync { record } => format!(r#"["peer",{},"sync",{}]"#, n(&to), record.len()),
                Frame::Pong => format!(r#"["peer",{},"pong"]"#, n(&to)),
                other => panic!("unexpected peer frame {other:?}"),
            },
            Effect::Udp {
                to: UdpTarget::Member(m),
                datagram: Datagram::Spl { src, flag, packet },
            } => format!(r#"["udp",{},"spl",{},{flag},{}]"#, n(&m), n(&src), packet.len()),
            Effect::Udp { .. } => panic!("unexpected datagram"),
            Effect::Local { from, packet } => format!(r#"["local",{},{}]"#, n(&from), packet.len()),
            Effect::Close { node, session, reason } => format!(
                r#"["close",{},{},"{}"]"#,
                n(&node),
                session.0,
                match reason {
                    CloseReason::SessionTime => "session",
                    CloseReason::Replaced => "replaced",
                }
            ),
            Effect::Wake { node } => format!(r#"["wake",{}]"#, n(&node)),
            Effect::Trace(t) => match t {
                Trace::CarrierOpened { node, session } => format!(r#"["t","opened",{},{}]"#, n(&node), session.0),
                Trace::CarrierClosed { node, asleep } => format!(r#"["t","closed",{},{}]"#, n(&node), u8::from(asleep)),
                Trace::SessionExpired { node } => format!(r#"["t","expired",{}]"#, n(&node)),
                Trace::QuotaExceeded { node } => format!(r#"["t","quota",{}]"#, n(&node)),
                Trace::Routed { src, dst, route, bytes } => format!(
                    r#"["t","routed",{},{},"{}",{bytes}]"#,
                    n(&src),
                    n(&dst),
                    match route {
                        Route::Local => "local",
                        Route::Carrier => "carrier",
                        Route::Tunnel => "tunnel",
                        Route::Peer => "peer",
                        Route::Mailbox => "mailbox",
                    }
                ),
                Trace::FwdBackLearned { node, via } => format!(r#"["t","fwdback",{},{}]"#, n(&node), n(&via)),
                Trace::Rejected { reason, node } => {
                    format!(r#"["t","rej","{}",{}]"#, reject_name(reason), self.names.opt(node))
                }
                Trace::RecordStored { node, seq, origin } => format!(
                    r#"["t","rstored",{},{seq},"{}"]"#,
                    n(&node),
                    match origin {
                        RecordOrigin::Publish => "publish",
                        RecordOrigin::Replica => "replica",
                        RecordOrigin::Own => "own",
                    }
                ),
                Trace::SleepAccepted { node } => format!(r#"["t","sleepok",{}]"#, n(&node)),
                Trace::Pulse { node } => format!(r#"["t","pulse",{}]"#, n(&node)),
                Trace::MailboxStored { node, seq, dropped } => {
                    format!(r#"["t","mstored",{},{seq},{dropped}]"#, n(&node))
                }
                Trace::MailboxDelivered { node, seq } => format!(r#"["t","mdeliv",{},{seq}]"#, n(&node)),
                Trace::WakeRequested { node } => format!(r#"["t","wakereq",{}]"#, n(&node)),
                other => panic!("unexpected trace {other:?}"),
            },
        };
        self.out.push(s);
    }
}

fn res_name(r: &Result<(), Reject>) -> String {
    r.as_ref().map_or_else(|e| reject_name(*e), |()| "ok".into())
}

struct Cov {
    forwarded: u32,
    mailboxed: u32,
    quota: u32,
    stale_copy: u32,
    expired: u32,
    fwdback: u32,
    wake: u32,
    held_out: u32,
    heard_deliv: u32,
    tunnel_held: u32,
    refused_held: u32,
    stepped_over: u32,
}

/// The numbers of a mailbox trace line `["t","<kind>",node,seq,...]`.
fn mailbox_line(e: &str, kind: &str) -> Option<(u64, u64, u64)> {
    let mut f = e.strip_prefix(r#"["t",""#)?.strip_suffix(']')?.split(',');
    let tail = f.next()?.strip_suffix('"')?;
    if tail != kind {
        return None;
    }
    let mut num = || f.next().and_then(|v| v.parse().ok());
    Some((num()?, num()?, num().unwrap_or(0)))
}

type Cache = std::collections::HashMap<(u8, u64, u64, u8), Vec<u8>>;

/// One scripted step: (op, node, kind, dst, seconds to advance or MAX for random, packet length or 0 for random).
type Step = (u64, usize, u64, usize, u64, usize);

/// One run of 260 steps against a relay whose mailbox holds `MB` bytes and whose carrier quota is `quota_bytes`,
/// after the scripted steps in `first`.
fn run<const MB: usize>(
    seed: u64,
    quota_bytes: u64,
    first: &[Step],
    out: &mut Vec<String>,
    cov: &mut Cov,
    cache: &mut Cache,
) {
    let mut rng = SplitMix64::traced(seed);
    let kps: Vec<Keypair> = (0..4u8).map(|i| ed(0x61 + i)).collect();
    let me_kp = ed(0x50);
    let other_relay = id(&ed(0x51));
    let mut ids: Vec<NodeId> = kps.iter().map(id).collect();
    ids.extend([nid(0xa5), nid(0xa6), nid(0xb7), nid(0xb8), nid(0xb9)]);
    ids.push(id(&me_kp));
    ids.push(nid(0xc0));
    let names = Names(ids.clone());
    let me = ids[9];
    let mut cfg = Config::new(me, seed);
    cfg.quota = Quota {
        bytes: quota_bytes,
        window_ns: 60 * SEC,
        session_ns: 300 * SEC,
    };
    cfg.mailbox_max_age_ns = 100 * SEC;
    let mut r: Box<Relay<3, 4, 2, MB>> = Box::new(Relay::new(cfg));
    let tb: Table<(), 3> = Table::new(seed);
    out.push(format!(
        r#"{{"t":"rnew","me":10,"c":3,"r":4,"mn":2,"mb":{MB},"bytes":{quota_bytes},"window":60,"sess":300,"age":100}}"#
    ));
    for (i, nd) in ids.iter().enumerate() {
        out.push(format!(r#"{{"t":"rbk","n":{},"b":{}}}"#, i + 1, tb.bucket_of(nd)));
    }
    let mut sess: [Option<SessionId>; 6] = [None; 6];
    let mut secs = 1000u64;
    let mut seqs = [0u64; 4];
    // (node, seq, second stored) of the held messages the trace shows as still held, for the step-over count
    let mut live: Vec<(u64, u64, u64)> = Vec::new();
    let mut off = 0u16;
    // (op, node, kind, dst, seconds to advance or MAX for random, packet length or 0 for random)
    let mut script: std::collections::VecDeque<(u64, usize, u64, usize, u64, usize)> =
        std::collections::VecDeque::new();
    const R: u64 = u64::MAX;
    script.extend([(15, 6, 1, 0, 0, 0), (15, 7, 1, 0, 0, 0), (15, 8, 1, 0, 0, 0)]);
    script.extend(first.iter().copied());
    for _ in 0..260 {
        // now and then a guided sequence: a key holder opens, sends a good sleep notice and closes; another node sends
        // it two packets; it opens again (the mailbox is delivered)
        if script.is_empty() && rng.next_u64() % 3 == 0 {
            let k = (rng.next_u64() % 4) as usize;
            let o = 4 + (rng.next_u64() % 2) as usize;
            let d = |rng: &mut SplitMix64, v: [u64; 3]| v[(rng.next_u64() % 3) as usize];
            match rng.next_u64() % 11 {
                // sleep notice, close, packets for the sleeper, return
                0 => script.extend([
                    (0, k, 0, 0, R, 0),
                    (3, k, 11, 0, R, 0),
                    (2, k, 0, 0, R, 0),
                    (0, o, 0, 0, R, 0),
                    (3, o, 0, k, R, 0),
                    (3, o, 0, k, R, 0),
                    (0, k, 0, 0, R, 0),
                ]),
                // the reply route is held for 30 s, not 29 or 31 (the forwarded node 11 is never a client)
                1 => {
                    let dt = d(&mut rng, [29, 30, 31]);
                    script.extend([(0, k, 0, 0, 1, 0), (9, 6, 0, k, 1, 0), (3, k, 0, 10, dt, 0)]);
                }
                // the tunnel is used within 20 s of the last datagram
                2 => {
                    let dt = d(&mut rng, [19, 20, 21]);
                    script.extend([
                        (0, o, 0, 0, 1, 0),
                        (2, k, 0, 0, 1, 0),
                        (11, k, 0, 0, 1, 0),
                        (3, o, 0, k, dt, 0),
                    ]);
                }
                // a carrier silent for more than 15 s also gets a tunnel copy
                3 => {
                    let dt = d(&mut rng, [14, 15, 16]);
                    script.extend([
                        (0, o, 0, 0, 1, 0),
                        (0, k, 0, 0, 1, 0),
                        (11, k, 0, 0, 0, 0),
                        (3, o, 0, k, dt, 0),
                    ]);
                }
                // a close within 10 s of the notice is a suspension
                4 => {
                    let dt = d(&mut rng, [9, 10, 11]);
                    script.extend([(0, k, 0, 0, 1, 0), (3, k, 11, 0, 1, 0), (2, k, 0, 0, dt, 0)]);
                }
                // the wake-up is repeated after 30 s
                5 => {
                    let dt = d(&mut rng, [29, 30, 31]);
                    script.extend([
                        (0, k, 0, 0, 1, 0),
                        (3, k, 11, 0, 1, 0),
                        (2, k, 0, 0, 1, 0),
                        (0, o, 0, 0, 1, 0),
                        (3, o, 0, k, 1, 0),
                        (3, o, 0, k, dt, 0),
                    ]);
                }
                // the byte limit: 500 + 500 fits, one more byte does not
                6 => script.extend([
                    (0, k, 0, 0, 61, 0),
                    (3, k, 0, 10, 0, 500),
                    (3, k, 0, 10, 0, 500),
                    (3, k, 0, 10, 0, 1),
                    (3, k, 0, 10, 60, 1),
                ]),
                // a session is closed by the sweep at its limit, not before
                7 => script.extend([(0, k, 0, 0, 1, 0), (14, 0, 0, 0, 299, 0), (14, 0, 0, 0, 1, 0)]),
                // a sleeper's UDP session wakes before its carrier: the mailbox goes down the tunnel
                9 => script.extend([
                    (0, k, 0, 0, 1, 0),
                    (3, k, 11, 0, 1, 0),
                    (2, k, 0, 0, 1, 0),
                    (0, o, 0, 0, 1, 0),
                    (3, o, 0, k, 1, 0),
                    (3, o, 0, k, 1, 0),
                    (11, k, 0, 0, 1, 0),
                    (13, k, 0, 0, 1, 0),
                ]),
                // the sleeper's UDP session wakes with no validated direct route: the mailbox stays held and the pass
                // is refused once; when the route is ready the next heard packet hands all three over in order
                10 => script.extend([
                    (0, k, 0, 0, 1, 0),
                    (3, k, 11, 0, 1, 0),
                    (2, k, 0, 0, 1, 0),
                    (0, o, 0, 0, 1, 0),
                    (3, o, 0, k, 1, 0),
                    (3, o, 0, k, 1, 0),
                    (17, k, 0, 0, 0, 0),
                    (11, k, 0, 0, 1, 0),
                    (13, k, 0, 0, 1, 0),
                    (17, k, 1, 0, 0, 0),
                    (11, k, 0, 0, 1, 0),
                ]),
                // a record is dropped after three republish periods, not before
                _ => script.extend([
                    (0, k, 0, 0, 1, 0),
                    (3, k, 9, 0, 0, 0),
                    (2, k, 0, 0, 0, 0),
                    (14, 0, 0, 0, 5399, 0),
                    (3, o, 0, k, 0, 0),
                    (14, 0, 0, 0, 1, 0),
                    (3, o, 0, k, 0, 0),
                ]),
            }
        }
        let forced = script.pop_front();
        secs += match forced {
            Some(f) if f.4 != R => f.4,
            _ => [
                0, 0, 1, 2, 9, 10, 11, 14, 15, 16, 19, 20, 21, 29, 30, 31, 59, 60, 61, 100, 299, 300,
            ][(rng.next_u64() % 22) as usize],
        };
        let now = secs * SEC;
        let node = forced.map_or_else(|| (rng.next_u64() % 6) as usize, |f| f.1);
        let mut sink = Rec {
            names: &names,
            out: Vec::new(),
            off,
        };
        let head;
        let res: String;
        let pick_dst = |rng: &mut SplitMix64| ids[(rng.next_u64() % 11) as usize];
        let flen = forced.map_or(0, |f| f.5);
        let plen = |rng: &mut SplitMix64| match rng.next_u64() % 10 {
            _ if flen > 0 => flen,
            0 => 1,
            1 => 1380 + (rng.next_u64() % 40) as usize,
            2 => 400,
            _ => (rng.next_u64() % 150) as usize + 1,
        };
        let op = forced.map_or_else(|| rng.next_u64() % 17, |f| f.0);
        match op {
            0 | 1 => {
                let x = r.carrier_opened(now, ids[node], &mut sink);
                if let Ok(s) = x {
                    sess[node] = Some(s);
                }
                res = x.as_ref().map_or_else(|e| reject_name(*e), |_| "ok".into());
                head = format!(
                    r#"{{"t":"ropen","now":{secs},"n":{},"sid":{}"#,
                    node + 1,
                    x.map_or(-1, |s| s.0 as i64)
                );
            }
            2 => {
                let s = if forced.is_none() && rng.next_u64() % 4 == 0 {
                    SessionId(rng.next_u64() % 8)
                } else {
                    sess[node].unwrap_or(SessionId(77))
                };
                r.carrier_closed(now, &ids[node], s, &mut sink);
                if sess[node] == Some(s) {
                    sess[node] = None;
                }
                res = "ok".into();
                head = format!(r#"{{"t":"rclose","now":{secs},"n":{},"sid":{}"#, node + 1, s.0);
            }
            3..=8 => {
                let s = if forced.is_none() && rng.next_u64() % 8 == 0 {
                    SessionId(99)
                } else {
                    sess[node].unwrap_or(SessionId(98))
                };
                let packet = vec![0x55u8; plen(&mut rng)];
                let dst = forced.map_or_else(|| pick_dst(&mut rng), |f| ids[f.3]);
                let flag = (rng.next_u64() % 256) as u8;
                let alias = (rng.next_u64() % 32) as u8;
                let kind = forced.map_or_else(|| rng.next_u64() % 12, |f| f.2);
                let owned: Vec<u8>;
                let spec: String;
                let f = match kind {
                    0..=2 => {
                        spec = format!(r#"["send",{},{flag},{}]"#, names.n(&dst), packet.len());
                        Frame::Send {
                            dst,
                            flag,
                            packet: &packet,
                        }
                    }
                    3 | 4 => {
                        spec = format!(r#"["sendnew",{},{alias},{flag},{}]"#, names.n(&dst), packet.len());
                        Frame::SendNew {
                            dst,
                            alias,
                            flag,
                            packet: &packet,
                        }
                    }
                    5 | 6 => {
                        spec = format!(r#"["sendalias",{alias},{flag},{}]"#, packet.len());
                        Frame::SendAlias {
                            alias,
                            flag,
                            packet: &packet,
                        }
                    }
                    7 => {
                        spec = format!(r#"["selfsend",{}]"#, packet.len());
                        Frame::SelfSend { packet: &packet }
                    }
                    8 => {
                        if rng.next_u64() % 2 == 0 {
                            spec = r#"["ping"]"#.into();
                            Frame::Ping
                        } else if rng.next_u64() % 2 == 0 {
                            spec = r#"["pong"]"#.into();
                            Frame::Pong
                        } else {
                            spec = format!(r#"["other",{}]"#, packet.len());
                            Frame::Recv {
                                src: dst,
                                flag,
                                packet: &packet,
                            }
                        }
                    }
                    9 => {
                        // PUB: the record of key k (signed by k), published by this node or by another one
                        let k = if forced.is_some() {
                            node
                        } else {
                            (rng.next_u64() % 4) as usize
                        };
                        let home = if forced.is_some() {
                            ids[6]
                        } else {
                            ids[(rng.next_u64() % 4) as usize + 6]
                        };
                        seqs[k] = if rng.next_u64() % 3 == 0 { seqs[k] } else { seqs[k] + 1 };
                        let seq = if forced.is_some() {
                            seqs[k] + 1
                        } else if rng.next_u64() % 6 == 0 {
                            1
                        } else {
                            seqs[k]
                        };
                        if forced.is_some() {
                            seqs[k] += 1;
                        }
                        owned = cache
                            .entry((0, k as u64, seq, names.n(&home) as u8))
                            .or_insert_with(|| record_bytes(&kps[k], home, seq))
                            .clone();
                        spec = format!(r#"["pub",{},{seq},{},{}]"#, k + 1, names.n(&home), owned.len());
                        Frame::Publish { record: &owned }
                    }
                    _ => {
                        // SLEEP: a notice of key k for this relay or another, at a clock near the relay's
                        let k = if node < 4 && (forced.is_some() || rng.next_u64() % 4 != 0) {
                            node
                        } else {
                            (rng.next_u64() % 4) as usize
                        };
                        let ts = (now / 1_000_000).saturating_add_signed(if forced.is_some() {
                            0
                        } else {
                            [0, 9_999, -9_999, 10_000, -10_000, 20_000][(rng.next_u64() % 6) as usize]
                        });
                        let good = forced.is_some() || rng.next_u64() % 5 != 0;
                        owned = cache
                            .entry((1, k as u64, ts, u8::from(good)))
                            .or_insert_with(|| notice(&kps[k], if good { &me } else { &other_relay }, ts))
                            .clone();
                        spec = format!(r#"["sleep",{},{ts},{},{}]"#, k + 1, u8::from(good), owned.len());
                        Frame::Sleep { notice: &owned }
                    }
                };
                let x = r.carrier_frame(now, &ids[node], s, &f, &mut sink);
                res = res_name(&x);
                head = format!(
                    r#"{{"t":"rframe","now":{secs},"n":{},"sid":{},"f":{spec}"#,
                    node + 1,
                    s.0
                );
            }
            9 | 10 => {
                let from = if let Some(f) = forced {
                    ids[f.1]
                } else if rng.next_u64() % 6 == 0 {
                    ids[4]
                } else {
                    ids[6 + (rng.next_u64() % 3) as usize]
                };
                let packet = vec![0x66u8; plen(&mut rng)];
                let dst = forced.map_or_else(|| pick_dst(&mut rng), |f| ids[f.3]);
                let src = forced.map_or_else(|| ids[(rng.next_u64() % 6) as usize], |_| ids[10]);
                let flag = (rng.next_u64() % 256) as u8;
                let owned: Vec<u8>;
                let spec: String;
                let f = match if forced.is_some() { 0 } else { rng.next_u64() % 8 } {
                    0..=3 => {
                        spec = format!(r#"["fwd",{},{},{flag},{}]"#, names.n(&src), names.n(&dst), packet.len());
                        Frame::Forward {
                            src,
                            dst,
                            flag,
                            packet: &packet,
                        }
                    }
                    4 | 5 => {
                        let k = (rng.next_u64() % 4) as usize;
                        let home = ids[(rng.next_u64() % 4) as usize + 6];
                        let seq = 1 + rng.next_u64() % 3;
                        owned = cache
                            .entry((0, k as u64, seq, names.n(&home) as u8))
                            .or_insert_with(|| record_bytes(&kps[k], home, seq))
                            .clone();
                        spec = format!(r#"["sync",{},{seq},{},{}]"#, k + 1, names.n(&home), owned.len());
                        Frame::Sync { record: &owned }
                    }
                    6 => {
                        if rng.next_u64() % 2 == 0 {
                            spec = r#"["ping"]"#.into();
                            Frame::Ping
                        } else {
                            spec = r#"["pong"]"#.into();
                            Frame::Pong
                        }
                    }
                    _ => {
                        spec = r#"["other"]"#.into();
                        Frame::SelfSend { packet: &packet }
                    }
                };
                let x = r.peer_frame(now, &from, &f, &mut sink);
                res = res_name(&x);
                head = format!(r#"{{"t":"rpeer","now":{secs},"from":{},"f":{spec}"#, names.n(&from));
            }
            11 => {
                if forced.is_none() && rng.next_u64() % 3 == 0 {
                    r.udp_gone(&ids[node]);
                    res = "ok".into();
                    head = format!(r#"{{"t":"rudpg","n":{}"#, node + 1);
                } else {
                    let x = r.udp_heard(now, &ids[node], &mut sink);
                    res = res_name(&x);
                    head = format!(r#"{{"t":"rudph","now":{secs},"n":{}"#, node + 1);
                }
            }
            12 => {
                let member = if rng.next_u64() % 5 == 0 { None } else { Some(ids[node]) };
                let dst = pick_dst(&mut rng);
                let packet = vec![0x77u8; plen(&mut rng)];
                let flag = (rng.next_u64() % 256) as u8;
                // The encoder refuses an empty or oversized packet, and the relay must refuse those too: the header is
                // encoded with one byte and the packet appended raw.
                let mut b = vec![0u8; 2048];
                let n = Datagram::Spu {
                    dst,
                    flag,
                    packet: &[0x77],
                }
                .encode(&mut b)
                .unwrap();
                b.truncate(n - 1);
                b.extend_from_slice(&packet);
                let x = r.datagram(now, addr(), member.as_ref(), &b, &mut sink);
                res = res_name(&x);
                head = format!(
                    r#"{{"t":"rspu","now":{secs},"m":{},"dst":{},"flag":{flag},"len":{}"#,
                    names.opt(member),
                    names.n(&dst),
                    packet.len()
                );
            }
            13 => {
                r.member_returned(now, &ids[node], &mut sink);
                res = "ok".into();
                head = format!(r#"{{"t":"rret","now":{secs},"n":{}"#, node + 1);
            }
            14 | 15 => {
                r.handle_timeout(now, &mut sink);
                res = "ok".into();
                head = format!(r#"{{"t":"rtime","now":{secs}"#);
            }
            17 => {
                let ready = forced.map_or_else(|| rng.next_u64() % 2 == 0, |f| f.2 == 1);
                let bit = 1u16 << (node + 1);
                off = if ready { off & !bit } else { off | bit };
                res = "ok".into();
                head = format!(r#"{{"t":"rready","n":{},"ok":{}"#, node + 1, u8::from(ready));
            }
            _ => {
                let p = forced.map_or_else(|| ids[6 + (rng.next_u64() % 4) as usize], |f| ids[f.1]);
                if forced.is_none() && rng.next_u64() % 3 == 0 {
                    r.remove_peer(&p);
                    res = "ok".into();
                    head = format!(r#"{{"t":"rrem","p":{}"#, names.n(&p));
                } else {
                    let ok = r.add_peer(p);
                    res = if ok { "ok".into() } else { "full".into() };
                    head = format!(r#"{{"t":"radd","p":{}"#, names.n(&p));
                }
            }
        }
        for e in &sink.out {
            cov.forwarded += u32::from(e.starts_with(r#"["peer"#) && e.contains("fwd"));
            cov.mailboxed += u32::from(e.contains("mstored"));
            cov.quota += u32::from(e.contains(r#""quota""#));
            cov.expired += u32::from(e.contains("expired"));
            cov.fwdback += u32::from(e.contains("fwdback"));
            cov.wake += u32::from(e.starts_with(r#"["wake"#));
            cov.held_out += u32::from(e.contains("mdeliv"));
            cov.refused_held += u32::from(e.contains(r#""notunnel""#));
        }

        // A release stepped over a message when it handed over one while an older one for the same member is surely
        // still held: it was stored less than the mailbox's age limit (100 s) ago and no later store for the member
        // pushed anything out. A store that pushed something out forgets the member's older ones, so the count is a
        // lower bound.
        for e in &sink.out {
            if let Some((node, seq, dropped)) = mailbox_line(e, "mstored") {
                if dropped > 0 {
                    live.retain(|l| l.0 != node);
                }
                live.push((node, seq, secs));
            } else if let Some((node, seq, _)) = mailbox_line(e, "mdeliv") {
                let at = live.iter().position(|l| l.0 == node && l.1 == seq);
                if let Some(at) = at {
                    let older = live.iter().take(at).filter(|l| l.0 == node && secs - l.2 < 100).count();
                    cov.stepped_over += u32::from(older > 0);
                    live.remove(at);
                }
            }
        }
        let delivered = sink.out.iter().any(|e| e.contains("mdeliv"));
        cov.heard_deliv += u32::from(op == 11 && delivered);
        cov.tunnel_held += u32::from(
            sink.out.iter().any(|e| e.starts_with(r#"["udp"#)) && sink.out.iter().any(|e| e.contains("mdeliv")),
        );
        cov.stale_copy += u32::from(sink.out.iter().filter(|e| e.starts_with(r#"["udp"#)).count() > 0);
        out.push(format!(r#"{head},"res":"{res}","out":[{}]}}"#, sink.out.join(",")));
        assert!(r.sessions() <= 3);
    }
}

#[test]
fn the_relay_records_its_trace() {
    let mut out = Vec::new();
    let mut cov = Cov {
        forwarded: 0,
        mailboxed: 0,
        quota: 0,
        stale_copy: 0,
        expired: 0,
        fwdback: 0,
        wake: 0,
        held_out: 0,
        heard_deliv: 0,
        tunnel_held: 0,
        refused_held: 0,
        stepped_over: 0,
    };
    let mut cache = Cache::new();
    for seed in 0..24u64 {
        run::<300>(seed, 1000, &[], &mut out, &mut cov, &mut cache);
    }
    // The mailbox above holds 300 bytes, so no message in those runs is too long for a route: a member (node 1) is
    // put to sleep, a message of 1400 bytes (too long for a datagram, short enough for a carrier) and a short one
    // are held for it, and its UDP session is heard: the pass steps over the long one.
    const STEP_OVER: [Step; 7] = [
        (0, 0, 0, 0, 1, 0),
        (3, 0, 11, 0, 1, 0),
        (2, 0, 0, 0, 30, 0),
        (0, 4, 0, 0, 1, 0),
        (3, 4, 0, 0, 1, 1400),
        (3, 4, 0, 0, 1, 60),
        (11, 0, 0, 0, 1, 0),
    ];
    run::<4096>(24, 100_000, &STEP_OVER, &mut out, &mut cov, &mut cache);
    assert!(pinc_tests::soaking() || cov.forwarded > 0, "no forward");
    assert!(pinc_tests::soaking() || cov.mailboxed > 0, "nothing mailboxed");
    assert!(pinc_tests::soaking() || cov.quota > 0, "no quota drop");
    assert!(pinc_tests::soaking() || cov.expired > 0, "no session expiry");
    assert!(pinc_tests::soaking() || cov.fwdback > 0, "no reply route learnt");
    assert!(pinc_tests::soaking() || cov.wake > 0, "no wake-up");
    assert!(pinc_tests::soaking() || cov.held_out > 0, "no held packet delivered");
    assert!(pinc_tests::soaking() || cov.stale_copy > 0, "no tunnel packet");
    assert!(
        pinc_tests::soaking() || cov.heard_deliv > 0,
        "no held packet delivered by a heard packet"
    );
    assert!(
        pinc_tests::soaking() || cov.tunnel_held > 0,
        "no held packet delivered down the tunnel"
    );
    assert!(
        pinc_tests::soaking() || cov.refused_held > 0,
        "no held packet kept for a tunnel that was not ready"
    );
    assert!(
        pinc_tests::soaking() || cov.stepped_over > 0,
        "no release stepped over a held message too long for the route"
    );
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    let mut text = String::new();
    for l in &out {
        writeln!(text, "{l}").unwrap();
    }
    std::fs::write(dir.join("connect.ndjson"), text).unwrap();
}
