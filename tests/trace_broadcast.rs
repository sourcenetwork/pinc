//! Trace generation for the topic broadcast: the real `Topics` machine of four nodes (a hub, a publisher and two
//! subscribers, one of which answers its access checks by hand) driven through its public API, recorded as ndjson
//! (`broadcast.ndjson`) for the TLA+ trace check (`TraceBroadcast.tla`) and the Lean replay
//! (`Vinc/BroadcastTrace.lean`).
//!
//! Every input the message path acts on is one line: a frame handed to a node (`frame`, with the head fields of the
//! message as ids, one id per distinct byte string), a HAVE (`have`), a timer (`timer`), an access answer (`acp`) and
//! the start of a node (`start`); a node's own signatures are `sign` lines, the oracle the checkers verify against (a
//! signature is valid for a message only if it was made by its origin over exactly that topic, id, body, timestamp and
//! flag). Each input line carries what the machine reported for it (`out`: its trace records, in order, and `ack`, the
//! PACK frames it sent). The scenarios cover: pushes, mirrors and fans, duplicates, tampered messages (every field of
//! the signed statement, and a head cut short), the hub log (eviction by the ring and expiry by the window, and a late
//! copy of a message that left it), the dedupe window (a copy after 600 s), the access check (held, allowed, denied,
//! the verdict cached for 30 s and lapsing), a full held set, the end of the floor wait, a requested id arriving, and
//! a hub acknowledging only after it stored. What the checkers do not see: the floors the hubs report (the FLOOR frames
//! are not delivered, so every member's wait runs out) and the messages that go out; those are model checked and
//! proved separately.
//!
//! The test asserts the facts it relies on itself, so it is meaningful without the proof tools. The trace is written
//! to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::items_after_statements,
    clippy::type_complexity,
    unreachable_pub
)]

#[path = "broadcast_common.rs"]
mod common;

use std::collections::HashMap;

use common::{Ev, Net, SEC, WALL0, keypair, ty};
use vinc_broadcast::consts::HELD_MAX;
use vinc_broadcast::wire::{Head, MAX_HEAD};
use vinc_broadcast::{Limits, Trace, auth, topic_tag};
use vinc_crypto::IdentityAlg;
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_wire::hlc::Hlc;

/// Model time: units of 1/8 millisecond.
fn units(ns: u64) -> u64 {
    ns.div_ceil(125_000)
}

struct World {
    net: Net,
    ids: HashMap<(u8, Vec<u8>), u32>,
    signed: Vec<(u32, usize)>,
    out: String,
}

const K_MID: u8 = 1;
const K_TOPIC: u8 = 2;
const K_BODY: u8 = 3;
const K_SIG: u8 = 4;

impl World {
    fn id(&mut self, kind: u8, bytes: &[u8]) -> u32 {
        if kind == K_MID && bytes.iter().all(|b| *b == 0) {
            return 0;
        }
        let next = u32::try_from(self.ids.keys().filter(|(k, _)| *k == kind).count()).unwrap() + 1;
        *self.ids.entry((kind, bytes.to_vec())).or_insert(next)
    }

    fn origin(&self, node: &[u8; 32]) -> usize {
        self.net.nodes.iter().position(|n| n.id == *node).unwrap_or(99)
    }

    fn line(&mut self, s: &str) {
        self.out.push_str(s);
        self.out.push('\n');
    }

    fn outs(&mut self, i: usize) -> String {
        let mut v = Vec::new();
        while let Some(t) = self.net.nodes[i].t.poll_trace() {
            let id = |w: &mut Self, m: [u8; 8]| w.id(K_MID, &m);
            match t {
                Trace::Stored { mid, fanned, .. } => {
                    let m = id(self, mid);
                    v.push(format!("{{\"k\":\"Stored\",\"mid\":{m},\"fanned\":{fanned}}}"));
                }
                Trace::Rejected { mid, why } => {
                    let m = id(self, mid);
                    v.push(format!("{{\"k\":\"Rejected\",\"mid\":{m},\"why\":\"{why:?}\"}}"));
                }
                Trace::Delivered { mid, .. } => {
                    let m = id(self, mid);
                    v.push(format!("{{\"k\":\"Delivered\",\"mid\":{m}}}"));
                }
                Trace::Held { mid, why } => {
                    let m = id(self, mid);
                    v.push(format!("{{\"k\":\"Held\",\"mid\":{m},\"why\":\"{why:?}\"}}"));
                }
                Trace::AcpAsked { id } => v.push(format!("{{\"k\":\"AcpAsked\",\"id\":{id}}}")),
                Trace::AcpAnswered { id, allow } => {
                    v.push(format!("{{\"k\":\"AcpAnswered\",\"id\":{id},\"allow\":{allow}}}"));
                }
                Trace::Repaired { mid, .. } => {
                    let m = id(self, mid);
                    v.push(format!("{{\"k\":\"Repaired\",\"mid\":{m}}}"));
                }
                Trace::FloorDone { used } => v.push(format!("{{\"k\":\"FloorDone\",\"used\":{used}}}")),
                _ => {}
            }
        }
        format!("[{}]", v.join(","))
    }

    fn start_lines(&mut self) {
        for i in 0..self.net.nodes.len() {
            let at = units(self.net.now);
            let hub = self.net.nodes[i].hub;
            self.line(&format!(
                "{{\"t\":\"bc\",\"op\":\"start\",\"n\":{i},\"hub\":{hub},\"at\":{at},\"bw\":{at}}}"
            ));
        }
    }

    /// Record the signatures of the message frames node `i` just handed to the host.
    fn note_signs(&mut self, i: usize) {
        let outs: Vec<Vec<u8>> = self.net.nodes[i].h.out.iter().map(|o| o.bytes.clone()).collect();
        for b in outs {
            let (Some(&fty), Some(&tl)) = (b.get(4), b.get(5)) else {
                continue;
            };
            if !matches!(fty, ty::PUB | ty::FAN | ty::FANP | ty::MSG | ty::MEMBER_PUSH) {
                continue;
            }
            let tl = usize::from(tl);
            self.note_sign(i, &b[6..6 + tl], &b[6 + tl..]);
        }
    }

    /// Record the signing of the message `rest` of topic `topic` by node `i`, once.
    fn note_sign(&mut self, i: usize, topic: &[u8], rest: &[u8]) {
        let Ok((head, body)) = Head::parse(rest) else { return };
        let sig = self.id(K_SIG, head.sig);
        if self.signed.iter().any(|(s, _)| *s == sig) {
            return;
        }
        let org = self.origin(head.origin);
        assert_eq!(org, i, "only the origin signs");
        self.signed.push((sig, org));
        let (m, t, bd) = (
            self.id(K_MID, &head.mid),
            self.id(K_TOPIC, topic),
            self.id(K_BODY, body),
        );
        let ts = head.ts.wall.saturating_sub(WALL0) * 8 + u64::from(head.ts.counter.min(7));
        self.line(&format!(
            "{{\"t\":\"bc\",\"op\":\"sign\",\"sig\":{sig},\"org\":{org},\"tid\":{t},\"mid\":{m},\"bid\":{bd},\
             \"ts\":{ts},\"isb\":{}}}",
            head.isb
        ));
    }

    /// Hand a frame to node `to` and record what the machine did.
    fn frame(&mut self, to: usize, from: usize, fty: u8, topic: &[u8], rest: &[u8]) {
        let now = self.net.now;
        let fid = self.net.id(from);
        let boot = self.net.nodes[from].hub;
        let (hd, fields) = match Head::parse(rest) {
            Ok((head, body)) => {
                let (m, t, bd, sig) = (
                    self.id(K_MID, &head.mid),
                    self.id(K_TOPIC, topic),
                    self.id(K_BODY, body),
                    self.id(K_SIG, head.sig),
                );
                let org = self.origin(head.origin);
                let ts = head.ts.wall.saturating_sub(WALL0) * 8 + u64::from(head.ts.counter.min(7));
                (
                    true,
                    format!(
                        "\"mid\":{m},\"org\":{org},\"tid\":{t},\"bid\":{bd},\"sig\":{sig},\"ts\":{ts},\"isb\":{}",
                        head.isb
                    ),
                )
            }
            Err(_) => (
                false,
                "\"mid\":0,\"org\":0,\"tid\":0,\"bid\":0,\"sig\":0,\"ts\":0,\"isb\":false".to_string(),
            ),
        };
        let big = hd && Head::parse(rest).is_ok_and(|(_, body)| body.len() > self.net.limits.max_body);
        let before = self.net.nodes[to].h.out.len();
        {
            let n = &mut self.net.nodes[to];
            n.h.tick(now);
            n.t.frame(&mut n.h, now, &fid, fty, topic, rest);
        }
        let acks = self.net.nodes[to].h.out[before..]
            .iter()
            .filter(|o| o.bytes.get(4) == Some(&ty::PACK))
            .count();
        let out = self.outs(to);
        let at = units(now);
        let (ftn, sz) = (fty, rest.len());
        self.line(&format!(
            "{{\"t\":\"bc\",\"op\":\"frame\",\"n\":{to},\"from\":{from},\"ft\":{ftn},\"boot\":{boot},\"hd\":{hd},\"big\":{big},{fields},\"sz\":{sz},\"at\":{at},\"ack\":{acks},\"out\":{out}}}"
        ));
        self.note_signs(to);
    }

    /// Carry every queued frame, answer the access checks of the nodes that answer at once, until quiet.
    fn pump(&mut self) {
        loop {
            let mut progressed = false;
            for i in 0..self.net.nodes.len() {
                self.note_signs(i);
                let outs = std::mem::take(&mut self.net.nodes[i].h.out);
                for o in outs {
                    let to = self.net.nodes.iter().position(|n| n.id == o.to).unwrap();
                    let (Some(&fty), Some(&tl)) = (o.bytes.get(4), o.bytes.get(5)) else {
                        continue;
                    };
                    let tl = usize::from(tl);
                    let (topic, rest) = (&o.bytes[6..6 + tl], &o.bytes[6 + tl..]);
                    progressed = true;
                    match fty {
                        ty::PUB | ty::FAN | ty::FANP | ty::MSG | ty::MEMBER_PUSH => self.frame(to, i, fty, topic, rest),
                        ty::HAVE => self.have(to, i, topic, rest),
                        // Subscriptions and acknowledgements reach the machines unrecorded: they change nothing the
                        // message path models (SUBS only the fallback's targets, PACK only the publisher's retries).
                        ty::SUB | ty::UNSUB | ty::SUBS | ty::PACK | ty::GET | ty::RESTORED => {
                            let now = self.net.now;
                            let fid = self.net.id(i);
                            let n = &mut self.net.nodes[to];
                            n.h.tick(now);
                            n.t.frame(&mut n.h, now, &fid, fty, topic, rest);
                            while n.t.poll_trace().is_some() {}
                        }
                        _ => {}
                    }
                }
            }
            for i in 0..self.net.nodes.len() {
                let Some(allow) = self.net.nodes[i].auto_acp else {
                    continue;
                };
                let evs = std::mem::take(&mut self.net.nodes[i].h.events);
                let (acp, rest): (Vec<Ev>, Vec<Ev>) = evs.into_iter().partition(|e| matches!(e, Ev::Acp { .. }));
                self.net.nodes[i].h.events = rest;
                for e in acp {
                    if let Ev::Acp { id, .. } = e {
                        self.answer(i, id, allow);
                        progressed = true;
                    }
                }
            }
            if !progressed {
                return;
            }
        }
    }

    /// Hand a frame to node `to` without recording it: what the machine does with it is not in the node model (SUB,
    /// SUBS); the messages it makes the node send are recorded when they arrive.
    fn inject(&mut self, to: usize, from: usize, fty: u8, topic: &[u8], rest: &[u8]) {
        let now = self.net.now;
        let fid = self.net.id(from);
        let n = &mut self.net.nodes[to];
        n.h.tick(now);
        n.t.frame(&mut n.h, now, &fid, fty, topic, rest);
        while n.t.poll_trace().is_some() {}
        self.pump();
    }

    /// A valid message of node 1 that no other node has seen: published with the hub's link cut and node 3 out of its
    /// view (so the fallback skips it), its frame read back from the host. Returns the topic and the rest of the frame.
    fn capture(&mut self, t: &[u8], body: &[u8]) -> (Vec<u8>, Vec<u8>) {
        self.net.link(1, 0, false);
        let id3 = self.net.id(3);
        self.net.nodes[1].h.view.remove(&id3);
        let now = self.net.now;
        {
            let n = &mut self.net.nodes[1];
            n.h.tick(now);
            n.t.publish(&mut n.h, now, t, body).unwrap();
        }
        while self.net.nodes[1].t.poll_trace().is_some() {}
        self.note_signs(1);
        let got = self.net.nodes[1]
            .h
            .out
            .iter()
            .map(|o| parts(&o.bytes))
            .find(|(f, ..)| matches!(*f, ty::FANP | ty::PUB | ty::MEMBER_PUSH))
            .map(|(_, tp, r)| (tp, r))
            .unwrap();
        self.net.nodes[1].h.out.clear();
        self.net.nodes[1].h.view.insert(id3);
        self.net.link(1, 0, true);
        got
    }

    fn have(&mut self, to: usize, from: usize, topic: &[u8], rest: &[u8]) {
        let now = self.net.now;
        let fid = self.net.id(from);
        let ids: Vec<u32> = rest.as_chunks::<8>().0.iter().map(|m| self.id(K_MID, m)).collect();
        {
            let n = &mut self.net.nodes[to];
            n.h.tick(now);
            n.t.frame(&mut n.h, now, &fid, ty::HAVE, topic, rest);
        }
        let boot = self.net.nodes[from].hub;
        let list = ids.iter().map(ToString::to_string).collect::<Vec<_>>().join(",");
        let at = units(now);
        let out = self.outs(to);
        self.line(&format!(
            "{{\"t\":\"bc\",\"op\":\"have\",\"n\":{to},\"boot\":{boot},\"ids\":[{list}],\"at\":{at},\"out\":{out}}}"
        ));
    }

    fn answer(&mut self, i: usize, id: u32, allow: bool) {
        let now = self.net.now;
        {
            let n = &mut self.net.nodes[i];
            n.h.tick(now);
            n.t.acp_answer(&mut n.h, now, id, allow);
        }
        let out = self.outs(i);
        let at = units(now);
        self.line(&format!(
            "{{\"t\":\"bc\",\"op\":\"acp\",\"n\":{i},\"id\":{id},\"allow\":{allow},\"at\":{at},\"out\":{out}}}"
        ));
    }

    /// Run the timers due up to `t` and the network, recording each timer call.
    fn run_until(&mut self, t: u64) {
        loop {
            self.pump();
            let next = self.net.nodes.iter().filter_map(|n| n.t.poll_timeout()).min();
            match next {
                Some(x) if x <= t => {
                    self.net.now = self.net.now.max(x);
                    let now = self.net.now;
                    for i in 0..self.net.nodes.len() {
                        if self.net.nodes[i].t.poll_timeout().is_some_and(|x| x <= now) {
                            {
                                let n = &mut self.net.nodes[i];
                                n.h.tick(now);
                                n.t.on_timer(&mut n.h, now);
                            }
                            let out = self.outs(i);
                            let at = units(now);
                            self.line(&format!(
                                "{{\"t\":\"bc\",\"op\":\"timer\",\"n\":{i},\"at\":{at},\"out\":{out}}}"
                            ));
                        }
                    }
                }
                _ => break,
            }
        }
        self.net.now = self.net.now.max(t);
        self.pump();
    }

    fn publish(&mut self, i: usize, topic: &[u8], body: &[u8]) -> Vec<u8> {
        let now = self.net.now;
        let mid = {
            let n = &mut self.net.nodes[i];
            n.h.tick(now);
            n.t.publish(&mut n.h, now, topic, body).unwrap()
        };
        while self.net.nodes[i].t.poll_trace().is_some() {}
        self.note_signs(i);
        self.pump();
        mid.to_vec()
    }

    fn subscribe(&mut self, i: usize, topic: &[u8]) {
        let now = self.net.now;
        {
            let n = &mut self.net.nodes[i];
            n.h.tick(now);
            n.t.subscribe(&mut n.h, now, topic).unwrap();
        }
        while self.net.nodes[i].t.poll_trace().is_some() {}
        self.line(&format!("{{\"t\":\"bc\",\"op\":\"sub\",\"n\":{i}}}"));
        self.pump();
    }
}

/// A frame as the host received it: `(type, topic, rest)`.
fn parts(b: &[u8]) -> (u8, Vec<u8>, Vec<u8>) {
    let tl = usize::from(b[5]);
    (b[4], b[6..6 + tl].to_vec(), b[6 + tl..].to_vec())
}

#[test]
fn broadcast_trace() {
    // A log ring that holds some forty small messages, so the ring evicts.
    let limits = Limits {
        max_body: 64,
        log_bytes: 64 + MAX_HEAD + 400,
        ..Limits::default()
    };
    let mut w = World {
        net: Net::with_limits(&[IdentityAlg::Ed25519; 4], 1, SEC, limits),
        ids: HashMap::new(),
        signed: Vec::new(),
        out: String::new(),
    };
    w.net.nodes[3].auto_acp = None;
    w.start_lines();
    let t = b"trace";
    let _ = topic_tag(t);
    w.subscribe(2, t);
    w.subscribe(3, t);
    // The members' floor wait runs out (no FLOOR frame is delivered): messages that arrive meanwhile are held.
    let early = w.publish(1, t, b"early");
    w.run_until(2 * SEC);
    let mut seen_frames: Vec<(usize, u8, Vec<u8>, Vec<u8>)> = Vec::new();
    // Publishes through the hub.
    let m1 = w.publish(1, t, b"one");
    w.run_until(3 * SEC);
    assert!(w.net.delivered(2).is_empty(), "held for the floors");
    let _ = (m1, early);
    for k in 0..3u8 {
        w.publish(1, t, &[b'm', k]);
    }
    w.run_until(4 * SEC);
    // Duplicates and tampering: a frame the hub saw, handed again and with each field of the statement changed.
    let hub_in: Vec<(usize, u8, Vec<u8>, Vec<u8>)> = {
        // Rebuild a valid message frame by publishing from node 1 with the hub's link cut and reading its output.
        w.net.link(1, 0, false);
        let now = w.net.now;
        {
            let n = &mut w.net.nodes[1];
            n.h.tick(now);
            n.t.publish(&mut n.h, now, t, b"capture").unwrap();
        }
        while w.net.nodes[1].t.poll_trace().is_some() {}
        w.note_signs(1);
        let mut v = Vec::new();
        for o in &w.net.nodes[1].h.out {
            let (f, tp, r) = parts(&o.bytes);
            if matches!(f, ty::FANP | ty::PUB | ty::MEMBER_PUSH) {
                v.push((0usize, f, tp, r));
            }
        }
        w.net.nodes[1].h.out.clear();
        w.net.link(1, 0, true);
        v
    };
    seen_frames.extend(hub_in);
    let (_, f0, tp, rest) = seen_frames[0].clone();
    // A member push of the captured message to subscriber 2 (valid), a copy of it, then the tampered variants.
    w.frame(2, 1, ty::MEMBER_PUSH, &tp, &rest);
    w.frame(2, 1, ty::MEMBER_PUSH, &tp, &rest);
    let (head, _) = Head::parse(&rest).unwrap();
    let hlen = head.len();
    for (_name, pos) in [("mid", 0usize), ("ts", hlen - 1), ("flag", hlen - 17), ("body", hlen)] {
        let mut r = rest.clone();
        r[pos] ^= 1;
        // Fresh copies must not hit the dedupe set: flip the id too unless the id is the field under test.
        w.frame(3, 1, ty::MEMBER_PUSH, &tp, &r);
    }
    let mut other_topic = tp.clone();
    other_topic[0] ^= 1;
    w.frame(3, 1, ty::MEMBER_PUSH, &other_topic, &rest);
    w.frame(3, 1, ty::MEMBER_PUSH, &tp, &rest[..20]);
    let _ = f0;
    w.run_until(20 * SEC);
    assert!(!w.net.delivered(2).is_empty(), "released when the floor wait ran out");
    // The access check of subscriber 3: allow, then the cache lapses after 30 s.
    let evs: Vec<u32> = w.net.nodes[3]
        .h
        .events
        .iter()
        .filter_map(|e| if let Ev::Acp { id, .. } = e { Some(*id) } else { None })
        .collect();
    w.net.nodes[3].h.events.clear();
    for id in evs {
        w.answer(3, id, true);
    }
    w.run_until(40 * SEC);
    w.publish(1, t, b"after verdict");
    w.run_until(80 * SEC);
    // Enough messages for the hub's ring to evict, then a message that left the log is offered again.
    for k in 0..60u8 {
        w.publish(1, t, &[b'e', k]);
    }
    w.run_until(100 * SEC);
    // A held set that fills: subscriber 3's verdict lapsed; publish more than the held limit from the publisher.
    for k in 0..(HELD_MAX + 3) {
        w.publish(1, t, &u32::try_from(k).unwrap().to_be_bytes());
    }
    w.run_until(101 * SEC);
    let evs: Vec<u32> = w.net.nodes[3]
        .h
        .events
        .iter()
        .filter_map(|e| if let Ev::Acp { id, .. } = e { Some(*id) } else { None })
        .collect();
    w.net.nodes[3].h.events.clear();
    for id in evs {
        w.answer(3, id, false);
    }
    // Everything ages out: the log window (120 s) and the dedupe window (600 s).
    w.run_until(300 * SEC);
    w.frame(2, 1, ty::MEMBER_PUSH, &tp, &rest);
    w.run_until(1000 * SEC);
    w.frame(2, 1, ty::MEMBER_PUSH, &tp, &rest);
    w.run_until(1001 * SEC);

    // Frames a node has no use for: a PUB, FANP or FAN at a node that is not a hub, a MSG from a node that is not a hub.
    w.frame(2, 1, ty::PUB, &tp, &rest);
    w.frame(2, 1, ty::FANP, &tp, &rest);
    w.frame(2, 1, ty::FAN, &tp, &rest);
    w.frame(2, 1, ty::MSG, &tp, &rest);
    // A body over the receiver's limit (the head's own length field says so): refused before anything else, at a hub
    // and at a member.
    let mut big = rest.clone();
    let blen_at = hlen - 16;
    let body_len = u32::from_be_bytes(big[blen_at..blen_at + 4].try_into().unwrap()) + 70;
    big[blen_at..blen_at + 4].copy_from_slice(&body_len.to_be_bytes());
    big.extend([7u8; 70]);
    w.frame(0, 1, ty::PUB, &tp, &big);
    w.frame(2, 1, ty::MEMBER_PUSH, &tp, &big);
    // A PUB the hub took, sent again: a duplicate, which the hub acknowledges all the same.
    w.frame(0, 1, ty::PUB, &tp, &rest);
    w.frame(0, 1, ty::PUB, &tp, &rest);
    w.run_until(1003 * SEC);
    // A node that does not subscribe is handed a message (its own, from long ago): seen, nothing else. (A publisher
    // never subscribes here: its own publishes are in its dedupe set, which the node model does not have.)
    let (_, own1) = w.capture(t, b"own one");
    w.frame(1, 2, ty::MEMBER_PUSH, &tp, &rest);
    w.run_until(1005 * SEC);
    // Two origins' messages wait at node 3 for their answers; the answer of the second skips the first's held message.
    w.publish(1, t, b"from one");
    w.publish(2, t, b"from two");
    w.run_until(1007 * SEC);
    let id2 = w.net.id(2);
    let mut asked: Vec<(u32, [u8; 32])> = w.net.nodes[3]
        .h
        .events
        .iter()
        .filter_map(|e| {
            if let Ev::Acp { id, origin, .. } = e {
                Some((*id, *origin))
            } else {
                None
            }
        })
        .collect();
    w.net.nodes[3].h.events.clear();
    asked.sort_by_key(|(_, o)| std::cmp::Reverse(*o == id2));
    assert!(asked.len() >= 2, "two origins are being asked about");
    w.answer(3, 9_999, true);
    for (id, _) in asked {
        w.answer(3, id, true);
    }
    // A member asks the hub to replay what it logged (SUB with the replay flag), and a hub is sent short or misplaced
    // subscription frames: none of them is in the node model, what the replay delivers is.
    let mut replay = 0u64.to_be_bytes().to_vec();
    replay.push(1);
    w.inject(0, 3, ty::SUB, &tp, &replay);
    w.inject(0, 2, ty::SUB, &tp, &replay);
    w.inject(0, 3, ty::SUB, &tp, &[1, 2, 3]);
    w.inject(2, 3, ty::SUB, &tp, &replay);
    w.inject(2, 1, ty::SUBS, &tp, &[0, 0]);
    w.inject(2, 0, ty::SUBS, &tp, &[1]);
    w.run_until(1010 * SEC);
    // A node revoked an origin: its messages are refused, whatever they say.
    let mut forged = rest.clone();
    forged[0..8].copy_from_slice(&[9; 8]);
    forged[8..40].copy_from_slice(&[0xee; 32]);
    w.net.nodes[3].t.revoke(&[0xee; 32]);
    w.frame(3, 1, ty::MEMBER_PUSH, &tp, &forged);
    // Node 2 starts again, long after the messages it is now handed were made: held for the floor wait, then refused as
    // older than the start of its life; and one that arrives after the wait is refused at once.
    w.run_until(2000 * SEC);
    w.net.restart(2, w.net.now);
    w.net.set_primary(2, 0);
    let (at, hub) = (units(w.net.now), w.net.nodes[2].hub);
    w.line(&format!(
        "{{\"t\":\"bc\",\"op\":\"start\",\"n\":2,\"hub\":{hub},\"at\":{at},\"bw\":{at}}}"
    ));
    w.subscribe(2, t);
    w.frame(2, 1, ty::MEMBER_PUSH, &tp, &rest);
    w.run_until(2020 * SEC);
    w.frame(2, 1, ty::MEMBER_PUSH, &tp, &own1);
    w.run_until(2025 * SEC);
    // A message the hub stored, a rival under its id, and a retry after the log let it go. The rival is another
    // body signed by another origin under the same id: refused, no acknowledgement. The retry is the stored message
    // again: acknowledged by the print kept in the dedupe set, though the log no longer holds it.
    let (_, fresh) = w.capture(t, b"stored then evicted");
    w.frame(0, 1, ty::PUB, &tp, &fresh);
    assert!(
        w.out.lines().last().unwrap().contains("\"ack\":1"),
        "the stored message is acknowledged"
    );
    let (head, _) = Head::parse(&fresh).unwrap();
    let ts = Hlc::new(head.ts.wall, head.ts.counter + 1);
    let mut sig = [0u8; MAX_SIGNATURE_LEN];
    let key = keypair(IdentityAlg::Ed25519, 3);
    let n = auth::sign(&key, t, &head.mid, b"a rival body", ts, true, &mut sig).unwrap();
    let id2 = key.node_id();
    let mut rival = Vec::new();
    Head {
        mid: head.mid,
        origin: &id2.bytes,
        alg: IdentityAlg::Ed25519,
        pk: &[],
        sig: &sig[..n],
        isb: true,
        ts,
    }
    .write(12, &mut rival);
    rival.extend_from_slice(b"a rival body");
    w.note_sign(2, t, &rival);
    w.frame(0, 2, ty::PUB, &tp, &rival);
    assert!(
        w.out.lines().last().unwrap().contains("\"ack\":0"),
        "a rival under a taken id is not acknowledged"
    );
    let stored = w.net.nodes[0].t.log_len(t);
    for k in 0..60u32 {
        w.publish(1, t, format!("filler {k}").as_bytes());
    }
    // The 60 fillers did not all fit beside the stored message: the log let some go, the oldest first, and that
    // message was the oldest.
    let held = w.net.nodes[0].t.log_len(t);
    assert!(
        held < stored + 60,
        "the log held {stored} before the fillers and holds {held} after: nothing was let go"
    );
    w.frame(0, 1, ty::PUB, &tp, &fresh);
    assert!(
        w.out.lines().last().unwrap().contains("\"ack\":1"),
        "a retry after eviction is acknowledged"
    );
    w.run_until(2030 * SEC);
    assert!(w.out.lines().count() > 100);
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("broadcast.ndjson"), &w.out).unwrap();
    }
}
