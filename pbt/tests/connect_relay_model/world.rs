//! The world: a relay driven beside the model, every step checked.
#![allow(unused_imports)]

use std::collections::{BTreeMap, BTreeSet};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use ephyra::prelude::*;
use pinc_connect::carrier::{BatchBuilder, DnsAnswer, Frame, MAX_FRAME_LEN, MAX_PACKET_LEN, Offer};
use pinc_connect::record::{self, Reach, Record, RecordFields};
use pinc_connect::relay::datagram::{Datagram, MAX_DNS_DATAGRAM, MAX_TUNNEL_DATAGRAM};
use pinc_connect::relay::sleep::{self, Notice, SKEW_MS};
use pinc_connect::relay::table::{Cache, Table};
use pinc_connect::relay::{
    CloseReason, Config, Effect, NodeState, Quota, RecordOrigin, Reject, Relay, Route, SessionId, Sink, Trace,
    UdpTarget, rule,
};
use pinc_crypto::{IdentityAlg, Keypair, NodeId};

use super::model::*;
use super::*;

// ---------------------------------------------------------------------------------------------------------------
// The harness: builds the bytes of each generated input, drives the relay and checks it against the model

pub struct World {
    pub relay: Box<R>,
    pub m: Model,
    pub sink: Collect,
    pub next_packet: u64,
    pub step: usize,
    /// The datagrams the last call sent back to an address: `(to, length)`.
    pub replies: Vec<(SocketAddr, usize)>,
    /// Skip the check of the answers to unvalidated addresses, a known finding (see `repro_connect.rs`), so a run
    /// goes on to check everything else.
    pub skip_known: bool,
}

impl World {
    pub fn new(setup: &Setup, gone_cap: Option<usize>) -> Self {
        let mut cfg = Config::new(id(ME), setup.seed);
        cfg.quota = Quota { bytes: setup.quota_bytes, window_ns: setup.window_ns, session_ns: setup.session_ns };
        cfg.mailbox_max_age_ns = setup.mailbox_age_ns;
        let mut w = Self { relay: Box::new(R::new(cfg)), m: Model::new(cfg, gone_cap), sink: Collect::default(), next_packet: 0, step: 0, replies: Vec::new(), skip_known: gone_cap.is_some() };
        // The host runs the timers once at start, as it does at every deadline.
        w.run(true, |r, now, s| {
            r.handle_timeout(now, s);
            Ok(())
        }, |m, e| {
            m.timeout(e);
            vec![P::Done(Ok(()))]
        });
        w
    }

    /// A fresh packet body: a marker byte that is not a long header, then a run-unique number, cut to `len`.
    pub fn body(&mut self, len: u16) -> Vec<u8> {
        self.next_packet += 1;
        let mut b = vec![0x40u8];
        b.extend_from_slice(&self.next_packet.to_le_bytes());
        b.resize(usize::from(len).max(1), 0x5a);
        b.truncate(usize::from(len).max(1));
        b
    }

    pub fn notice(&mut self, owner: u8, spec: &NoticeSpec) -> Vec<u8> {
        match spec {
            NoticeSpec::Mine => self.notice(owner, &NoticeSpec::Fresh { signer: owner, for_me: true, skew_ms: 0, tamper: false }),
            NoticeSpec::Fresh { signer, for_me, skew_ms, tamper } => {
                let relay = if *for_me { id(ME) } else { id(OTHER_RELAY) };
                let ts = (self.m.now / MS).saturating_add_signed(*skew_ms);
                let mut out = vec![0u8; sleep::MAX_LEN];
                let n = KEYS.with(|keys| sleep::sign(&keys[usize::from(*signer)], &relay, ts, &mut out)).expect("a notice signs");
                out.truncate(n);
                if *tamper && let Some(b) = out.last_mut() {
                    *b ^= 1;
                }
                self.m.notices.push(out.clone());
                out
            },
            NoticeSpec::Replay(i) => {
                if self.m.notices.is_empty() {
                    return self.notice(owner, &NoticeSpec::Fresh { signer: 0, for_me: true, skew_ms: 0, tamper: false });
                }
                self.m.notices[usize::from(*i) % self.m.notices.len()].clone()
            },
        }
    }

    pub fn cframe(&mut self, owner: u8, f: &CFrame) -> Vec<u8> {
        match f {
            CFrame::Ping => enc(&Frame::Ping),
            CFrame::Pong => enc(&Frame::Pong),
            CFrame::Send(d, flag, len) => {
                let p = self.body(*len);
                enc(&Frame::Send { dst: id(*d), flag: *flag, packet: &p })
            },
            CFrame::SendNew(d, alias, len) => {
                let p = self.body(*len);
                enc(&Frame::SendNew { dst: id(*d), alias: *alias, flag: 1, packet: &p })
            },
            CFrame::SendAlias(alias, len) => {
                let p = self.body(*len);
                enc(&Frame::SendAlias { alias: *alias, flag: 2, packet: &p })
            },
            CFrame::SelfSend(len) => {
                let p = self.body(*len);
                enc(&Frame::SelfSend { packet: &p })
            },
            CFrame::Publish(r) => enc(&Frame::Publish { record: &r.bytes() }),
            CFrame::Dns(t) => enc(&Frame::DnsQuery { peer: id(*t) }),
            CFrame::Sleep(n) => {
                let b = self.notice(owner, n);
                enc(&Frame::Sleep { notice: &b })
            },
            CFrame::Forbidden(which, t, len) => {
                let p = self.body(*len);
                let r = signed_record(0, ME, 1, 0, false);
                match which {
                    0 => enc(&Frame::Recv { src: id(*t), flag: 0, packet: &p }),
                    1 => enc(&Frame::RecvNew { src: id(*t), alias: 0, flag: 0, packet: &p }),
                    2 => enc(&Frame::RecvAlias { alias: 0, flag: 0, packet: &p }),
                    3 => enc(&Frame::SelfRecv { packet: &p }),
                    4 => enc(&Frame::DnsReply { peer: id(*t), answer: DnsAnswer::Record(&r) }),
                    5 => enc(&Frame::Forward { src: id(*t), dst: id(0), flag: 0, packet: &p }),
                    _ => enc(&Frame::Sync { record: &r }),
                }
            },
        }
    }

    pub fn pframe(&mut self, f: &PFrame) -> Vec<u8> {
        match f {
            PFrame::Ping => enc(&Frame::Ping),
            PFrame::Pong => enc(&Frame::Pong),
            PFrame::Forward(s, d, len) => {
                let p = self.body(*len);
                enc(&Frame::Forward { src: id(*s), dst: id(*d), flag: 3, packet: &p })
            },
            PFrame::Sync(r) => enc(&Frame::Sync { record: &r.bytes() }),
            PFrame::Forbidden(which, t, len) => {
                let p = self.body(*len);
                match which {
                    0 => enc(&Frame::Send { dst: id(*t), flag: 0, packet: &p }),
                    1 => enc(&Frame::Publish { record: &signed_record(7, 7, 1, 0, false) }),
                    2 => enc(&Frame::DnsQuery { peer: id(*t) }),
                    3 => enc(&Frame::SelfSend { packet: &p }),
                    _ => {
                        let n = self.notice(7, &NoticeSpec::Fresh { signer: 7, for_me: true, skew_ms: 0, tamper: false });
                        enc(&Frame::Sleep { notice: &n })
                    },
                }
            },
        }
    }

    pub fn dgram(&mut self, owner: u8, d: &DSpec) -> Vec<u8> {
        match d {
            DSpec::Qad(n) => denc(&Datagram::Qad { nonce: n.to_be_bytes() }),
            DSpec::Dns(t) => denc(&Datagram::DnsQuery { peer: id(*t) }),
            DSpec::Sleep(n) => {
                let b = self.notice(owner, n);
                denc(&Datagram::Sleep { notice: &b })
            },
            DSpec::Spu(t, flag, len) => {
                let p = self.body((*len).min(u16::try_from(MAX_TUNNEL_DATAGRAM - 35).unwrap_or(1389)));
                denc(&Datagram::Spu { dst: id(*t), flag: *flag, packet: &p })
            },
            DSpec::Unexpected(which, t) => match which {
                0 => denc(&Datagram::Qadr { nonce: [1; 8], addr: addr(0) }),
                1 => denc(&Datagram::DnsReply { peer: id(*t), answer: DnsAnswer::Absent }),
                _ => {
                    let p = self.body(40);
                    denc(&Datagram::Spl { src: id(*t), flag: 0, packet: &p })
                },
            },
        }
    }

    /// Batch the frames as a carrier does: one record when the builder takes them all, else one frame each.
    pub fn batched(frames: &[Vec<u8>]) -> Vec<Vec<u8>> {
        let mut buf = vec![0u8; MAX_FRAME_LEN];
        let mut b = BatchBuilder::new(&mut buf);
        for f in frames {
            let Ok(frame) = Frame::decode(f) else { return frames.to_vec() };
            if b.offer(&frame) != Ok(Offer::Added) {
                return frames.to_vec();
            }
        }
        match b.finish() {
            Ok(Some(rec)) => vec![rec.to_vec()],
            _ => frames.to_vec(),
        }
    }

    /// One call of the relay, checked against the model: `act` calls the relay, `model` predicts; `releases` says
    /// the call may hand over held mail.
    pub fn run(
        &mut self,
        releases: bool,
        act: impl FnOnce(&mut R, u64, &mut Collect) -> Result<(), Reject>,
        model: impl FnOnce(&mut Model, &mut Expect) -> Vec<P>,
    ) {
        let before: BTreeSet<K> = self.m.sessions.keys().copied().collect();
        self.sink.got.clear();
        self.sink.not_ready = self.m.not_ready.clone();
        let got = act(self.relay.as_mut(), self.m.now, &mut self.sink);
        let mut e = Expect { releases, ..Expect::default() };
        let preds = model(&mut self.m, &mut e);
        self.check(&before, got, &preds, &e);
    }

    pub fn check(&mut self, before: &BTreeSet<K>, got: Result<(), Reject>, preds: &[P], e: &Expect) {
        let step = self.step;
        let raws = std::mem::take(&mut self.sink.got);
        let mut fx = Vec::new();
        self.replies.clear();
        let mut rejected = Vec::new();
        let mut quota = Vec::new();
        let mut stored = Vec::new();
        let mut mail_outcome: Vec<bool> = Vec::new();
        let mut woken = Vec::new();
        for raw in raws {
            match raw {
                Raw::Unencodable(what) => panic!("step {step}: the relay emitted a frame or datagram that does not encode: {what}"),
                Raw::Carrier(to, bytes) => {
                    let t = k(&to);
                    assert!(
                        self.m.sessions.contains_key(&t) || before.contains(&t),
                        "step {step}: a frame on the carrier of {to:?}, which has none open"
                    );
                    fx.push(self.normalise_carrier(t, &bytes));
                },
                Raw::Peer(to, bytes) => {
                    assert!(self.m.peers.contains(&k(&to)), "step {step}: a frame to {to:?}, not an authenticated peer relay");
                    match Frame::decode(&bytes) {
                        Ok(Frame::Forward { src, dst, flag, packet }) => fx.push(Fx::Forward {
                            to: k(&to),
                            src: k(&src),
                            dst: k(&dst),
                            flag,
                            body: packet.to_vec(),
                        }),
                        _ => fx.push(Fx::PeerCtl { to: k(&to), frame: bytes }),
                    }
                },
                Raw::Udp(UdpTarget::Reply(a), bytes) => {
                    self.replies.push((a, bytes.len()));
                    fx.push(Fx::Reply { to: a, dgram: bytes });
                },
                Raw::Udp(UdpTarget::Member(n), bytes) => match Datagram::decode(&bytes) {
                    Ok(Datagram::Spl { src, flag, packet }) => {
                        assert!(
                            self.m.fresh_udp(&k(&n)),
                            "step {step}: a packet down the UDP session of {n:?}, not heard in the last 20 s"
                        );
                        assert!(bytes.len() <= MAX_TUNNEL_DATAGRAM, "step {step}: a tunnel datagram of {} bytes", bytes.len());
                        fx.push(Fx::Spl { to: k(&n), src: k(&src), flag, body: packet.to_vec() });
                    },
                    _ => fx.push(Fx::MemberDgram { to: k(&n), dgram: bytes }),
                },
                Raw::Local(from, body) => fx.push(Fx::Local { from: k(&from), body }),
                Raw::Close(node, session, reason) => {
                    fx.push(Fx::Close { node: k(&node), session: session.0, replaced: reason == CloseReason::Replaced });
                },
                Raw::Wake(node) => woken.push(k(&node)),
                Raw::Trace(t) => match t {
                    Trace::Rejected { reason, node } => {
                        self.m.rejected_seen += 1;
                        if reason == Reject::MailboxRefused {
                            mail_outcome.push(false);
                        }
                        rejected.push((reason, node.map(|n| k(&n))));
                    },
                    Trace::QuotaExceeded { node } => {
                        self.m.quota_seen += 1;
                        quota.push(k(&node));
                    },
                    Trace::RecordStored { node, seq, origin } => stored.push((k(&node), seq, origin)),
                    Trace::Routed { route: Route::Mailbox, .. } => mail_outcome.push(true),
                    _ => {},
                },
            }
        }

        // The mailbox's answers, in the order the model routed packets to it.
        assert_eq!(mail_outcome.len(), e.mail.len(), "step {step}: packets routed to the mailbox");
        let mut want_rej = e.rejected.clone();
        for (stored_ok, (dst, src, flag, body)) in mail_outcome.iter().zip(&e.mail) {
            if *stored_ok {
                self.m.held_seq += 1;
                let seq = self.m.held_seq;
                self.m.held.entry(*dst).or_default().push((seq, *src, *flag, body.clone()));
            } else {
                want_rej.push((Reject::MailboxRefused, Some(*src)));
            }
        }
        for n in &woken {
            assert!(self.m.sleeping.contains_key(n), "step {step}: a wake-up for {n:?}, which is not asleep here");
        }

        // Every predicted effect, and nothing else but the hand-over of held mail.
        let mut want: Vec<Fx> = e.fx.clone();
        let mut extra = Vec::new();
        for f in fx {
            match want.iter().position(|w| *w == f) {
                Some(i) => {
                    want.swap_remove(i);
                },
                None => extra.push(f),
            }
        }
        assert!(want.is_empty(), "step {step}: effects the rules call for did not come: {want:?}");
        // What is left must be held mail handed to its member, each message once and in arrival order within the call.
        let mut last: BTreeMap<K, u64> = BTreeMap::new();
        for f in extra {
            let (to, src, flag, body) = match &f {
                Fx::Recv { to, src, flag, body } | Fx::Spl { to, src, flag, body } => (*to, *src, *flag, body.clone()),
                other => panic!("step {step}: an effect no rule calls for: {other:?}"),
            };
            assert!(e.releases, "step {step}: held mail handed over by a call that does not release it: {f:?}");
            let held = self.m.held.entry(to).or_default();
            let at = held.iter().position(|(_, s, fl, b)| *s == src && *fl == flag && *b == body);
            assert!(at.is_some(), "step {step}: a packet to {to:?} that was neither routed now nor held for it: {f:?}");
            let (seq, ..) = held.remove(at.unwrap_or(0));
            if let Some(prev) = last.get(&to) {
                assert!(seq > *prev, "step {step}: held mail of {to:?} handed over out of order");
            }
            last.insert(to, seq);
        }

        // Refusals, quota drops and stored records: exactly the predicted ones (a release may add one NoTunnel per
        // member).
        let mut got_rej: Vec<String> = rejected
            .iter()
            .filter(|(r, _)| !(e.releases && *r == Reject::NoTunnel))
            .map(|r| format!("{r:?}"))
            .collect();
        let mut want_rej: Vec<String> = want_rej.iter().map(|r| format!("{r:?}")).collect();
        got_rej.sort();
        want_rej.sort();
        assert_eq!(got_rej, want_rej, "step {step}: refusals traced");
        assert_eq!(quota, e.quota, "step {step}: frames dropped for the byte limit");
        assert_eq!(stored, e.stored, "step {step}: records stored");

        // The result: the first error among the sub-frames, the mailbox's answer filled in.
        let want: Result<(), Reject> = preds
            .iter()
            .map(|p| match p {
                P::Done(r) => *r,
                P::Mail(i) => {
                    if mail_outcome.get(*i).copied().unwrap_or(true) {
                        Ok(())
                    } else {
                        Err(Reject::MailboxRefused)
                    }
                },
            })
            .fold(Ok(()), |acc: Result<(), Reject>, r| acc.and(r));
        assert_eq!(got, want, "step {step}: the result");
        if let Err(r) = got
            && r != Reject::Quota
        {
            assert!(
                rejected.iter().any(|(x, _)| *x == r),
                "step {step}: refused with {r:?} but nothing was traced"
            );
        }
        self.invariants();
    }

    pub fn normalise_carrier(&mut self, to: K, bytes: &[u8]) -> Fx {
        let step = self.step;
        let Some(s) = self.m.sessions.get_mut(&to) else {
            return Fx::CarrierCtl { to, frame: bytes.to_vec() };
        };
        match Frame::decode(bytes) {
            Ok(Frame::Recv { src, flag, packet }) => Fx::Recv { to, src: k(&src), flag, body: packet.to_vec() },
            Ok(Frame::RecvNew { src, alias, flag, packet }) => {
                if let Some(slot) = s.seen.get_mut(usize::from(alias)) {
                    *slot = Some(k(&src));
                }
                Fx::Recv { to, src: k(&src), flag, body: packet.to_vec() }
            },
            Ok(Frame::RecvAlias { alias, flag, packet }) => {
                let src = s.seen.get(usize::from(alias)).copied().flatten();
                assert!(src.is_some(), "step {step}: the relay used alias {alias} on a carrier that never learnt it");
                Fx::Recv { to, src: src.unwrap_or((0, [0; 32])), flag, body: packet.to_vec() }
            },
            Ok(Frame::SelfRecv { packet }) => Fx::SelfRecv { to, body: packet.to_vec() },
            _ => Fx::CarrierCtl { to, frame: bytes.to_vec() },
        }
    }

    pub fn invariants(&self) {
        let step = self.step;
        let r = &self.relay;
        assert!(r.sessions() <= C, "step {step}: {} sessions in a table of {C}", r.sessions());
        assert_eq!(r.sessions(), self.m.sessions.len(), "step {step}: open sessions");
        assert!(r.record_count() <= RS, "step {step}: {} records in a store of {RS}", r.record_count());
        assert_eq!(r.record_count(), self.m.records.len(), "step {step}: stored records");
        assert!(r.mailbox_members() <= MN, "step {step}: {} mailbox members of {MN}", r.mailbox_members());
        let now = self.m.now;
        for i in 0..u8::try_from(IDS).unwrap_or(11) {
            let n = id(i);
            let key = k(&n);
            let (_, bytes) = r.mailbox_pending(&n);
            assert!(bytes <= MB, "step {step}: {bytes} bytes held for one member, the quota is {MB}");
            let state = r.node_state(&n);
            let want = self.m.state(&key);
            assert_eq!(state == NodeState::Open, want == NodeState::Open, "step {step}: whether node {i} is open");
            assert_eq!(state, want, "step {step}: what the relay knows of node {i}'s carrier");
            assert_eq!(r.lookup(now, &n), self.m.lookup(&key), "step {step}: the lookup of node {i}");
            assert_eq!(
                r.record_received(&n),
                self.m.records.get(&key).map(|s| s.received),
                "step {step}: the receive time of node {i}'s record"
            );
        }
        let st = r.stats();
        assert_eq!(st.rejected, self.m.rejected_seen, "step {step}: the refusal counter against the traces");
        assert_eq!(st.quota_drops, self.m.quota_seen, "step {step}: the quota counter against the traces");
        assert_eq!(r.next_deadline(), Some(self.m.next_deadline()), "step {step}: the next deadline");
    }

    pub fn op(&mut self, op: &Op) {
        match op {
            Op::Tick(d, early) => {
                self.m.now = self.m.now.saturating_add(*d);
                let due = self.relay.next_deadline().is_some_and(|t| t <= self.m.now);
                if due || *early {
                    let now = self.m.now;
                    self.run(false, |r, now, s| {
                        r.handle_timeout(now, s);
                        Ok(())
                    }, |m, e| {
                        m.timeout(e);
                        vec![P::Done(Ok(()))]
                    });
                    let next = self.relay.next_deadline().unwrap_or(u64::MAX);
                    assert!(next > now, "step {}: after the timers ran at {now} the next deadline is {next}", self.step);
                }
            },
            Op::Open(n) => {
                let node = id(*n);
                let mut session = None;
                self.run(true, |r, now, s| r.carrier_opened(now, node, s).map(|sid| session = Some(sid)), |m, e| {
                    let key = k(&node);
                    let now = m.now;
                    if let Some(old) = m.sessions.get(&key) {
                        e.fx.push(Fx::Close { node: key, session: old.id, replaced: true });
                    } else if m.sessions.len() >= C {
                        return vec![m.reject(e, Reject::SessionsFull, Some(key))];
                    }
                    let fresh = Sess { id: m.next_session, opened: now, last_rx: now, window_start: now, window_bytes: 0, rx: [None; 32], seen: [None; 32] };
                    m.sessions.insert(key, fresh);
                    let _ = m.order.insert(node, ());
                    m.next_session += 1;
                    m.gone.remove(&key);
                    m.sleeping.remove(&key);
                    vec![P::Done(Ok(()))]
                });
                if let Some(s) = session {
                    let want = self.m.sessions.get(&k(&node)).map(|x| x.id);
                    assert_eq!(Some(s.0), want, "step {}: the session id handed out", self.step);
                }
            },
            Op::Close(n, stale) => {
                let node = id(*n);
                let key = k(&node);
                let cur = self.m.sessions.get(&key).map(|s| s.id);
                let session = match (cur, stale) {
                    (Some(c), false) => c,
                    (Some(c), true) => c.wrapping_sub(1),
                    (None, _) => self.m.next_session.wrapping_sub(1),
                };
                self.run(false, |r, now, s| {
                    r.carrier_closed(now, &node, SessionId(session), s);
                    Ok(())
                }, |m, _| {
                    if cur == Some(session) {
                        m.sessions.remove(&key);
                        m.order.remove(&node);
                        let now = m.now;
                        m.gone_insert(key, now);
                    }
                    vec![P::Done(Ok(()))]
                });
            },
            Op::Frame(n, stale, f) => {
                let bytes = self.cframe(*n, f);
                self.carrier_bytes(*n, *stale, &bytes);
            },
            Op::Batch(n, fs) => {
                let frames: Vec<Vec<u8>> = fs.iter().map(|f| self.cframe(*n, f)).collect();
                for b in Self::batched(&frames) {
                    self.carrier_bytes(*n, false, &b);
                }
            },
            Op::Mangled(n, f, edits) => {
                let bytes = apply(edits, self.cframe(*n, f));
                self.carrier_bytes(*n, false, &bytes);
            },
            Op::Peer(p, f) => {
                let bytes = self.pframe(f);
                self.peer_bytes(*p, &bytes);
            },
            Op::PeerBatch(p, fs) => {
                let frames: Vec<Vec<u8>> = fs.iter().map(|f| self.pframe(f)).collect();
                for b in Self::batched(&frames) {
                    self.peer_bytes(*p, &b);
                }
            },
            Op::Dgram(a, member, d) => {
                let bytes = self.dgram(member.unwrap_or(*a % CLIENTS), d);
                self.datagram(*a, *member, &bytes);
            },
            Op::MangledDgram(a, member, d, edits) => {
                let bytes = apply(edits, self.dgram(member.unwrap_or(*a % CLIENTS), d));
                self.datagram(*a, *member, &bytes);
            },
            Op::Heard(n) => {
                let node = id(*n);
                self.run(true, |r, now, s| r.udp_heard(now, &node, s), |m, e| {
                    if m.stamp(k(&node)) {
                        vec![P::Done(Ok(()))]
                    } else {
                        vec![m.reject(e, Reject::SessionsFull, Some(k(&node)))]
                    }
                });
            },
            Op::UdpGone(n) => {
                let node = id(*n);
                self.relay.udp_gone(&node);
                self.m.udp.remove(&k(&node));
                self.invariants();
            },
            Op::Returned(n) => {
                let node = id(*n);
                self.run(true, |r, now, s| {
                    r.member_returned(now, &node, s);
                    Ok(())
                }, |m, _| {
                    m.sleeping.remove(&k(&node));
                    vec![P::Done(Ok(()))]
                });
            },
            Op::Ready(n, ready) => {
                if *ready {
                    self.m.not_ready.remove(&k(&id(*n)));
                } else {
                    self.m.not_ready.insert(k(&id(*n)));
                }
            },
            Op::AddPeer(p) => {
                let node = id(*p);
                assert!(self.relay.add_peer(node), "step {}: a peer set of 32 refused its first peers", self.step);
                if !self.m.peers.contains(&k(&node)) {
                    self.m.peers.push(k(&node));
                }
                self.invariants();
            },
            Op::RemovePeer(p) => {
                let node = id(*p);
                self.relay.remove_peer(&node);
                self.m.peers.retain(|x| *x != k(&node));
                self.invariants();
            },
            Op::Local(d, len) => {
                let dst = id(*d);
                let p = self.body(*len);
                self.run(false, |r, now, s| r.send_local(now, &dst, 4, &p, s), |m, e| {
                    let key = k(&dst);
                    if m.sessions.contains_key(&key) {
                        e.fx.push(Fx::SelfRecv { to: key, body: p.clone() });
                        return vec![P::Done(Ok(()))];
                    }
                    let me = m.cfg.me;
                    vec![m.route(e, &me, &dst, 4, &p, false)]
                });
            },
            Op::SetOwn(seq) => {
                let rec = signed_record(ME, ME, u64::from(*seq), 1, false);
                self.run(false, |r, now, s| r.set_own_record(now, &rec, s), |m, e| {
                    let me = m.me();
                    let p = m.store(e, &rec, RecordOrigin::Own, Some(me));
                    if matches!(p, P::Done(Ok(()))) {
                        m.replicate(e, &rec);
                        m.next_publish = m.now.checked_add(rule::RECORD_REPUBLISH_NS);
                    }
                    vec![p]
                });
            },
            Op::Restart => self.restart(),
            Op::Suspend(n, via_udp) => {
                let notice = self.notice(*n, &NoticeSpec::Mine);
                if *via_udp {
                    self.datagram(0, None, &denc(&Datagram::Sleep { notice: &notice }));
                } else {
                    self.carrier_bytes(*n, false, &enc(&Frame::Sleep { notice: &notice }));
                }
                self.op(&Op::Close(*n, false));
            },
        }
    }

    pub fn carrier_bytes(&mut self, n: u8, stale: bool, bytes: &[u8]) {
        let Ok(frame) = Frame::decode(bytes) else { return };
        let node = id(n);
        let key = k(&node);
        let cur = self.m.sessions.get(&key).map(|s| s.id);
        let session = match cur {
            Some(c) if !stale => c,
            Some(c) => c.wrapping_add(1),
            None => self.m.next_session,
        };
        self.run(false, |r, now, s| r.carrier_frame(now, &node, SessionId(session), &frame, s), |m, e| {
            match m.sessions.get_mut(&key) {
                Some(s) if Some(session) == cur => s.last_rx = m.now,
                _ => return vec![m.reject(e, Reject::StaleSession, Some(key))],
            }
            match frame {
                Frame::Batch(b) => b.frames().map(|sub| m.client_frame(e, &node, &sub)).collect(),
                f => vec![m.client_frame(e, &node, &f)],
            }
        });
    }

    pub fn peer_bytes(&mut self, p: u8, bytes: &[u8]) {
        let Ok(frame) = Frame::decode(bytes) else { return };
        let from = id(p);
        self.run(false, |r, now, s| r.peer_frame(now, &from, &frame, s), |m, e| m.peer_frame(e, &from, &frame));
    }

    pub fn datagram(&mut self, a: u8, member: Option<u8>, bytes: &[u8]) {
        let src = addr(a);
        let member = member.map(id);
        let in_len = bytes.len();
        self.run(member.is_some(), |r, now, s| r.datagram(now, src, member.as_ref(), bytes, s), |m, e| {
            let d = match Datagram::decode(bytes) {
                Ok(d) => d,
                Err(err) => return vec![m.reject(e, Reject::BadDatagram(err), member.map(|x| k(&x)))],
            };
            if let Some(x) = member {
                m.stamp(k(&x));
            }
            match d {
                Datagram::Qad { nonce } => {
                    e.fx.push(Fx::Reply { to: src, dgram: denc(&Datagram::Qadr { nonce, addr: src }) });
                    vec![P::Done(Ok(()))]
                },
                Datagram::DnsQuery { peer } => {
                    let dgram = denc(&Datagram::DnsReply { peer, answer: m.answer(&k(&peer), MAX_DNS_DATAGRAM - 35) });
                    e.fx.push(Fx::Reply { to: src, dgram });
                    vec![P::Done(Ok(()))]
                },
                Datagram::Sleep { notice } => vec![m.sleep(e, notice, None)],
                Datagram::Spu { dst, flag, packet } => {
                    let Some(x) = member else { return vec![m.reject(e, Reject::Unauthenticated, None)] };
                    if k(&dst) == m.me() {
                        return vec![m.reject(e, Reject::NoRoute, Some(k(&x)))];
                    }
                    vec![m.route(e, &x, &dst, flag, packet, false)]
                },
                _ => vec![m.reject(e, Reject::UnexpectedFrame, member.map(|x| k(&x)))],
            }
        });
        if member.is_none() && !self.skip_known {
            // vertexia: the relay's answers to one datagram, measured per datagram; a ledger over a run would also
            // catch a slow drip, which a run of 70 steps cannot show
            self.amplification(src, in_len);
        }
    }

    /// The bytes sent back to an address that has proved nothing, against the bytes it sent (wire bytes, 28 header
    /// bytes each way).
    pub fn amplification(&self, src: SocketAddr, in_len: usize) {
        let step = self.step;
        for (to, _) in &self.replies {
            assert_eq!(*to, src, "step {step}: an answer to a datagram went to another address");
        }
        let sent: usize = self.replies.iter().map(|(_, n)| n + 28).sum();
        let bound = 3 * (in_len + 28);
        assert!(
            sent <= bound,
            "step {step}: {sent} bytes sent to {src}, an address that proved nothing, for one datagram of {} bytes (at most {bound})",
            in_len + 28
        );
    }

    /// The host restarts the relay with the same identity and gives back the records and held packets it kept.
    pub fn restart(&mut self) {
        let now = self.m.now;
        let cfg = self.m.cfg;
        let mut saved_recs = Vec::new();
        let mut saved_mail: Vec<(NodeId, Vec<(NodeId, u8, Vec<u8>, u64)>)> = Vec::new();
        let mut buf = [0u8; MAX_PACKET_LEN];
        for i in 0..u8::try_from(IDS).unwrap_or(11) {
            let n = id(i);
            if let (Some(bytes), Some(at)) = (self.relay.lookup(now, &n), self.relay.record_received(&n)) {
                saved_recs.push((at, bytes.to_vec()));
            }
            let mut held = Vec::new();
            let mut j = 0;
            while let Some((d, at)) = self.relay.held_packet(&n, j, &mut buf) {
                held.push((d.src, d.flag, buf[..d.len].to_vec(), at));
                j += 1;
                assert!(j <= MB, "step {}: held_packet went past every message the mailbox can hold", self.step);
            }
            if !held.is_empty() {
                saved_mail.push((n, held));
            }
        }
        self.relay = Box::new(R::new(cfg));
        let peers = self.m.peers.clone();
        let mut m = Model::new(cfg, self.m.gone_cap);
        m.now = now;
        m.notices = std::mem::take(&mut self.m.notices);
        m.not_ready = std::mem::take(&mut self.m.not_ready);
        self.m = m;
        for p in &peers {
            assert!(self.relay.add_peer(node_of(*p)), "a restarted relay refused a peer");
            self.m.peers.push(*p);
        }
        for (at, bytes) in &saved_recs {
            let mut sink = Collect::default();
            assert_eq!(self.relay.restore_record(*at, bytes, &mut sink), Ok(()), "step {}: a saved record restores", self.step);
            let rec = Record::parse_verified(bytes).expect("a saved record verifies");
            self.m.records.insert(
                k(&rec.node),
                StoredRec { seq: rec.seq, bytes: bytes.clone(), received: *at, home: k(&rec.home) },
            );
            self.m.rejected_seen += sink.got.iter().filter(|r| matches!(r, Raw::Trace(Trace::Rejected { .. }))).count() as u64;
        }
        for (n, held) in &saved_mail {
            let mut kept = Vec::new();
            for (src, flag, body, at) in held {
                let r = self.relay.restore_held(now, *at, n, src, *flag, body);
                if now.saturating_sub(*at) < cfg.mailbox_max_age_ns {
                    assert_eq!(r, Ok(()), "step {}: a held packet the relay saved, not expired, restores", self.step);
                    kept.push((*src, *flag, body.clone(), *at));
                }
            }
            let mut again = Vec::new();
            let mut j = 0;
            while let Some((d, at)) = self.relay.held_packet(n, j, &mut buf) {
                again.push((d.src, d.flag, buf[..d.len].to_vec(), at));
                j += 1;
                if j > MB {
                    break;
                }
            }
            assert_eq!(again, kept, "step {}: the mailbox of {n:?} restored from what was saved", self.step);
            let held: Vec<(u64, K, u8, Vec<u8>)> = kept
                .into_iter()
                .map(|(s, f, b, _)| {
                    self.m.held_seq += 1;
                    (self.m.held_seq, k(&s), f, b)
                })
                .collect();
            self.m.held.insert(k(n), held);
        }
        // The host runs the timers at start.
        self.run(false, |r, now, s| {
            r.handle_timeout(now, s);
            Ok(())
        }, |m, e| {
            m.timeout(e);
            vec![P::Done(Ok(()))]
        });
    }
}

