//! The application of a node: scenario intents become work on the protocols, and every delivery is recorded with
//! the checks that belong at the application boundary (integrity, provenance, duplicates, access control).
//!
//! Intents that need an on-top layer which is not registered are not dropped and not recorded: they are counted in
//! [`Stack::waiting`] by kind. With the layer present the accounting is complete: a broadcast message must be whole,
//! come from its creator and arrive once; a fetch is delivered when the local store holds every requested range; a
//! reconcile result must be the exact difference of the two sets.
//!
//! Invariants: an intent is recorded exactly once, when it is accepted for work; the delivery of a push is reported
//! for the replicator, of a request/response for the peer, of an echo for the origin.

use super::body::{self, Verdict};
use super::durable::MsgIntents;
use super::host::Host;
use super::ontop::{Command, OnTopEvent};
use super::reqresp::Waiting;
use super::stack::{Proto, SLOTS, Slot, Stack};
use crate::suite::crypto::payload::HEADER_LEN;
use crate::suite::crypto::{MsgId, PayloadKind, Registry};
use crate::suite::rec::{IntentMeta, MustArg, NS, kind_name};
use crate::suite::world::model::{Intent, IntentKind, Must};

/// The size of one reconcile item.
const ITEM: u64 = 40;
/// The echo body and the bytes counted for an echo.
const ECHO_BYTES: u64 = 32;
/// The default request size of a docsync.
const DOCSYNC_REQ: u64 = 120;
/// The default request size of a manage.
const MANAGE_REQ: u64 = 1024;
/// The default response size of a docsync or manage.
const RESP_DEFAULT: u64 = 2048;
/// The framing overhead counted on top of the response size of a request/response delivery.
const RESP_OVERHEAD: u64 = 120;

fn must_arg(m: &Must) -> MustArg {
    match m {
        Must::Flag(f) => MustArg::Flag(*f),
        Must::Set(s) => MustArg::Set(s.clone()),
    }
}

impl Stack {
    pub(super) fn app_boot(&mut self, now: u64, host: &mut dyn Host) {
        let topics = self.world.nodes.get(self.idx).map_or_default(|n| n.topics.clone());
        for topic in topics {
            self.ontop_cmd(now, host, Slot::Broadcast, Command::Subscribe { topic });
        }
        // Without a values layer nothing is provided; the fetches that would need it are listed as waiting.
        let names = self.world.provides.get(&self.idx).cloned().unwrap_or_default();
        let provides = self.values.is_some();
        for name in names.into_iter().filter(|_| provides) {
            match (
                self.value_ids.get(&name).copied(),
                self.world.values.get(&name).copied(),
            ) {
                (Some(value), Some(len)) => self.ontop_cmd(now, host, Slot::Values, Command::Provide { value, len }),
                _ => self.violation(now, "G-SPEC", "a provided value is not in the value table"),
            }
        }
        // the database's durable log: fetches that did not finish are asked for again
        let open = self.durable.borrow().open_fetches.clone();
        for iid in open {
            let pending = self
                .rec
                .borrow()
                .intents
                .get(&iid)
                .is_some_and(|it| !it.delivered.contains_key(&self.idx));
            if pending {
                self.issue_fetch(now, host, iid);
            }
        }
    }

    fn ontop_cmd(&mut self, now: u64, host: &mut dyn Host, slot: Slot, cmd: Command) {
        if let Some(l) = self.slot_mut(slot) {
            l.command(now, host, cmd);
        }
    }

    fn missing(&self, now: u64, what: &str) {
        self.violation(now, "G-SPEC", &format!("an intent is missing its {what}"));
    }

    fn msg_intents(&self) -> MsgIntents {
        self.durable.borrow().msg_intents.clone()
    }

    pub(super) fn app_intent(&mut self, now: u64, host: &mut dyn Host, d: &Intent) {
        let slot = match d.kind {
            IntentKind::Publish => Some(Slot::Broadcast),
            IntentKind::Fetch => Some(Slot::Values),
            IntentKind::Reconcile => Some(Slot::Reconcile),
            _ => None,
        };
        if slot.is_some_and(|s| self.slot_mut(s).is_none()) {
            *self.waiting.entry(kind_name(d.kind)).or_default() += 1;
            return;
        }
        let deadline = now + d.deadline_ns;
        let must = must_arg(&d.must);
        match d.kind {
            IntentKind::Publish => self.do_publish(now, host, d, deadline, must),
            IntentKind::Push => self.do_push(now, host, d, deadline, must),
            IntentKind::Docsync => self.do_request(now, host, d, Proto::DocSync, deadline, must),
            IntentKind::Manage => self.do_request(now, host, d, Proto::Manage, deadline, must),
            IntentKind::Echo => {
                let Some(to) = d.to else {
                    return self.missing(now, "peer");
                };
                let meta = IntentMeta {
                    to: Some(to),
                    probe: d.probe,
                    ..IntentMeta::default()
                };
                let iid = self.rec.borrow_mut().intent(
                    IntentKind::Echo,
                    self.idx,
                    now,
                    deadline,
                    &[],
                    ECHO_BYTES,
                    must,
                    meta,
                );
                self.echo_start(host, to, iid);
            }
            IntentKind::Fetch => self.do_fetch(now, host, d, deadline, must),
            IntentKind::Reconcile => self.do_reconcile(now, host, d, deadline, must),
        }
    }

    /// Makes a message of `body` bytes and records the intent it belongs to; returns both and the message length.
    /// `(now, deadline)` are the times, `(size, receivers, must)` what the recorder stores of the intent.
    fn new_message(
        &mut self,
        host: &dyn Host,
        kind: IntentKind,
        (now, deadline): (u64, u64),
        (size, receivers, must): (u64, &[usize], MustArg),
        body: u64,
        d: &Intent,
    ) -> (u32, MsgId, u64) {
        // a message must be long enough to name its creator
        let len = body.max(HEADER_LEN as u64);
        let msg = host.registry().new_msg(self.idx, PayloadKind::Msg, len);
        let meta = IntentMeta {
            vid: Some(msg.0),
            to: matches!(kind, IntentKind::Docsync | IntentKind::Manage)
                .then_some(d.to)
                .flatten(),
            ..IntentMeta::default()
        };
        let mut rec = self.rec.borrow_mut();
        let iid = rec.intent(kind, self.idx, now, deadline, receivers, size, must, meta);
        rec.set_under_bulk(iid, d.under_bulk);
        (iid, msg, len)
    }

    fn do_publish(&mut self, now: u64, host: &mut dyn Host, d: &Intent, deadline: u64, must: MustArg) {
        let (Some(size), Some(topic)) = (d.size, d.topic.clone()) else {
            return self.missing(now, "size or topic");
        };
        let times = (now, deadline);
        let (iid, msg, len) = self.new_message(host, IntentKind::Publish, times, (size, &d.receivers, must), size, d);
        self.msg_intents().borrow_mut().insert(msg.0, iid);
        let msg = body::render(host.registry(), msg, len);
        self.ontop_cmd(now, host, Slot::Broadcast, Command::Publish { topic, msg });
    }

    fn do_push(&mut self, now: u64, host: &mut dyn Host, d: &Intent, deadline: u64, must: MustArg) {
        let (Some(size), Some(rep)) = (d.size, d.to) else {
            return self.missing(now, "size or replicator");
        };
        let (iid, msg, len) = self.new_message(host, IntentKind::Push, (now, deadline), (size, &[rep], must), size, d);
        self.msg_intents().borrow_mut().insert(msg.0, iid);
        self.pl_push(now, host, rep, iid, msg, len);
    }

    fn do_request(&mut self, now: u64, host: &mut dyn Host, d: &Intent, p: Proto, deadline: u64, must: MustArg) {
        let Some(to) = d.to else {
            return self.missing(now, "peer");
        };
        let (kind, req) = if p == Proto::DocSync {
            (IntentKind::Docsync, DOCSYNC_REQ)
        } else {
            (IntentKind::Manage, MANAGE_REQ)
        };
        let resp = d.resp.unwrap_or(RESP_DEFAULT);
        let (iid, msg, len) = self.new_message(
            host,
            kind,
            (now, deadline),
            (resp, &[to], must),
            d.req.unwrap_or(req),
            d,
        );
        self.rr_request(now, host, p, to, Waiting { iid, msg, len, resp });
    }

    fn do_fetch(&mut self, now: u64, host: &mut dyn Host, d: &Intent, deadline: u64, must: MustArg) {
        let Some(name) = d.value.as_ref() else {
            return self.missing(now, "value");
        };
        let (Some(&value), Some(&len)) = (self.value_ids.get(name), self.world.values.get(name)) else {
            return self.violation(now, "G-SPEC", "a fetch names a value that is not in the value table");
        };
        let ranges = (!d.ranges.is_empty()).then(|| d.ranges.clone());
        let req = ranges.as_ref().map_or(len, |r| r.iter().map(|&(_, n)| n).sum());
        let meta = IntentMeta {
            vid: Some(value.0),
            providers: d.providers.clone(),
            ranges,
            req_bytes: Some(req),
            stream_rate: d.stream_rate,
            ..IntentMeta::default()
        };
        let iid =
            self.rec
                .borrow_mut()
                .intent(IntentKind::Fetch, self.idx, now, deadline, &[self.idx], len, must, meta);
        {
            let mut dur = self.durable.borrow_mut();
            dur.open_fetches.push(iid);
            dur.fetch_intents.entry(value.0).or_default().push(iid);
        }
        self.issue_fetch(now, host, iid);
    }

    fn issue_fetch(&mut self, now: u64, host: &mut dyn Host, iid: u32) {
        let Some((value, len, providers, ranges, deadline)) = self.rec.borrow().intents.get(&iid).and_then(|it| {
            Some((
                MsgId(it.meta.vid?),
                it.size,
                it.meta.providers.clone(),
                it.meta.ranges.clone(),
                it.deadline?,
            ))
        }) else {
            return;
        };
        let fetch_id = {
            let mut d = self.durable.borrow_mut();
            d.next_fetch_id += 1;
            d.next_fetch_id
        };
        self.fetch_ids.insert(fetch_id, iid);
        let cmd = Command::Fetch {
            fetch_id,
            value,
            len,
            providers,
            ranges,
            priority: 3,
            deadline,
        };
        self.ontop_cmd(now, host, Slot::Values, cmd);
    }

    fn do_reconcile(&mut self, now: u64, host: &mut dyn Host, d: &Intent, deadline: u64, must: MustArg) {
        let (Some(to), Some(set_ref)) = (d.to, d.set_ref.clone()) else {
            return self.missing(now, "peer or collection");
        };
        let iid = {
            let mut rec = self.rec.borrow_mut();
            let tx = |n: usize| rec.node_tx_bytes.get(&n).copied().unwrap_or(0);
            let tx0 = tx(self.idx) + tx(to);
            let meta = IntentMeta {
                to: Some(to),
                set_ref: Some(set_ref.clone()),
                tx0: Some(tx0),
                ..IntentMeta::default()
            };
            rec.intent(IntentKind::Reconcile, self.idx, now, deadline, &[to], 0, must, meta)
        };
        self.durable.borrow_mut().open_reconcile.insert(set_ref.clone(), iid);
        self.ontop_cmd(now, host, Slot::Reconcile, Command::Reconcile { set_ref, peer: to });
    }

    // ------------------------------------------------------------------ deliveries

    /// The mutual-authentication check of a harness message: its true writer must be the session peer.
    pub(super) fn check_origin(&self, now: u64, reg: &Registry, p: Proto, peer: usize, msg: MsgId) -> bool {
        if reg.creator_of(msg) == Some(peer) {
            return true;
        }
        let name = String::from_utf8_lossy(p.alpn());
        self.violation(
            now,
            "G-SEC",
            &format!("{name} message accepted from a principal other than the session peer"),
        );
        false
    }

    /// The checks at the application boundary: the bytes are exactly one whole message, written by `claimed` when
    /// the transport names one. Returns the message and its length.
    fn origin_ok(
        &self,
        now: u64,
        reg: &Registry,
        bytes: &[u8],
        claimed: Option<usize>,
        what: &str,
    ) -> Option<(MsgId, u64)> {
        let verdict = body::message_id(bytes).map(|m| (m, body::verify(reg, m, bytes)));
        match verdict {
            None | Some((_, Verdict::Corrupt)) => {
                self.violation(now, "G-INT", &format!("{what} delivered corrupted or foreign bytes"));
                None
            }
            Some((_, Verdict::Partial)) => {
                self.violation(now, "G-INT", &format!("{what} delivered a partial message"));
                None
            }
            Some((m, Verdict::Whole)) => {
                if claimed.is_some() && claimed != reg.creator_of(m) {
                    self.violation(
                        now,
                        "G-SEC",
                        &format!("{what} attributed to a principal that did not write it"),
                    );
                    return None;
                }
                Some((m, bytes.len() as u64))
            }
        }
    }

    pub(super) fn pushlog_delivered(&mut self, now: u64, reg: &Registry, origin: usize, seq: u64, b: &[u8]) {
        let Some((m, len)) = self.origin_ok(now, reg, b, Some(origin), "PUSHLOG push") else {
            return;
        };
        let iid = self.msg_intents().borrow().get(&m.0).copied();
        let mut rec = self.rec.borrow_mut();
        rec.check_acp_delivery(now, self.idx, origin);
        if let Some(iid) = iid {
            rec.delivered(iid, self.idx, now, len);
            rec.pushlog_delivered(origin, self.idx, seq);
        }
    }

    pub(super) fn request_done(&mut self, now: u64, iid: u32) {
        let mut rec = self.rec.borrow_mut();
        let Some((to, size)) = rec.intents.get(&iid).and_then(|it| Some((it.meta.to?, it.size))) else {
            return;
        };
        rec.check_acp_delivery(now, self.idx, to);
        rec.delivered(iid, to, now, size + RESP_OVERHEAD);
    }

    pub(super) fn echo_served(&mut self, now: u64, id: u64) {
        let mut rec = self.rec.borrow_mut();
        if let Ok(iid) = u32::try_from(id)
            && rec.intents.contains_key(&iid)
        {
            rec.echo_served(iid, now);
        }
    }

    pub(super) fn echo_done(&mut self, now: u64, iid: u32) {
        let mut rec = self.rec.borrow_mut();
        let Some((node, to)) = rec
            .intents
            .get(&iid)
            .filter(|it| !it.delivered.contains_key(&it.node))
            .map(|it| (it.node, it.meta.to))
        else {
            return;
        };
        rec.check_acp_delivery(now, self.idx, to);
        rec.delivered(iid, node, now, ECHO_BYTES);
    }

    // ------------------------------------------------------------------ on-top events

    pub(super) fn drain_ontop(&mut self, now: u64, reg: &Registry) {
        for slot in SLOTS {
            while let Some(ev) = self.slot_mut(slot).and_then(|l| l.poll_event()) {
                self.ontop_event(now, reg, ev);
            }
        }
    }

    fn holds(&self, value: MsgId, off: u64, len: u64) -> bool {
        self.values.as_ref().is_some_and(|l| l.holds(value, off, len))
    }

    fn ontop_event(&mut self, now: u64, reg: &Registry, ev: OnTopEvent) {
        match ev {
            OnTopEvent::Message { origin, msg } => {
                let Some((m, len)) = self.origin_ok(now, reg, &msg, origin, "BROADCAST message") else {
                    return;
                };
                let mut rec = self.rec.borrow_mut();
                if !rec.message_first_delivery(now, self.idx, m.0) {
                    return;
                }
                rec.check_acp_delivery(now, self.idx, origin);
                let iid = self.durable.borrow().msg_intents.borrow().get(&m.0).copied();
                if let Some(iid) = iid {
                    rec.delivered(iid, self.idx, now, len);
                }
            }
            OnTopEvent::FetchProgress { fetch_id } => self.fetch_event(now, fetch_id, "FetchProgress", None),
            OnTopEvent::FetchFailed { fetch_id } => self.fetch_event(now, fetch_id, "FetchFailed", None),
            OnTopEvent::FetchComplete { fetch_id } => self.fetch_event(now, fetch_id, "FetchComplete", None),
            OnTopEvent::ValueReadable {
                fetch_id,
                offset,
                length,
            } => self.fetch_event(now, fetch_id, "ValueReadable", Some((offset, length))),
            OnTopEvent::ReconcileResult {
                set_ref,
                missing_here,
                missing_there,
            } => self.reconcile_result(now, &set_ref, &missing_here, &missing_there),
            OnTopEvent::Member(m) => {
                let inc = self.durable.borrow().incarnations;
                self.rec.borrow_mut().core_event(now, self.idx, inc, &m);
            }
        }
    }

    fn fetch_event(&mut self, now: u64, fetch_id: u64, name: &str, readable: Option<(u64, u64)>) {
        let info = self.fetch_ids.get(&fetch_id).and_then(|iid| {
            let rec = self.rec.borrow();
            let it = rec.intents.get(iid)?;
            Some((MsgId(it.meta.vid?), it.size, it.meta.ranges.clone()))
        });
        let Some((value, len, ranges)) = info else {
            return self.violation(now, "G-SPEC", &format!("{name} for an unknown fetch id"));
        };
        match (name, readable) {
            ("FetchComplete", _) => {
                let all = ranges.unwrap_or_else(|| vec![(0, len)]);
                if !all.iter().all(|&(o, n)| self.holds(value, o, n)) {
                    self.violation(now, "G-INT", "FetchComplete before every byte was verified and stored");
                }
            }
            ("ValueReadable", Some((off, n))) if !self.holds(value, off, n) => {
                self.violation(now, "G-INT", "ValueReadable for bytes that are not verified");
            }
            _ => {}
        }
        // Delivery is store-based: every event that follows a write looks at what the store holds now.
        if name != "FetchFailed" {
            self.value_progress(now, value);
        }
    }

    fn reconcile_result(&mut self, now: u64, set_ref: &[u8], here: &[[u8; 40]], there: &[[u8; 40]]) {
        let iid = self.durable.borrow_mut().open_reconcile.remove(set_ref);
        let Some((iid, z, tx0)) = iid.and_then(|iid| {
            let rec = self.rec.borrow();
            let it = rec.intents.get(&iid)?;
            Some((iid, it.meta.to?, it.meta.tx0.unwrap_or(0)))
        }) else {
            return self.violation(now, "G-SPEC", "ReconcileResult without an open Reconcile for that set");
        };
        let set = |n: usize| -> std::collections::BTreeSet<[u8; 40]> {
            self.world
                .sets
                .get(&(n, set_ref.to_vec()))
                .map_or_default(|v| v.iter().copied().collect())
        };
        let (mine, theirs) = (set(self.idx), set(z));
        let here_set: std::collections::BTreeSet<[u8; 40]> = here.iter().copied().collect();
        let there_set: std::collections::BTreeSet<[u8; 40]> = there.iter().copied().collect();
        if here_set != theirs.difference(&mine).copied().collect()
            || there_set != mine.difference(&theirs).copied().collect()
        {
            return self.violation(now, "G-INT", "reconciliation reported a difference that is not exact");
        }
        let diff = (here_set.len() + there_set.len()) as u64;
        let mut rec = self.rec.borrow_mut();
        rec.check_acp_delivery(now, self.idx, z);
        let tx = |n: usize| rec.node_tx_bytes.get(&n).copied().unwrap_or(0);
        let tx1 = tx(self.idx) + tx(z);
        rec.reconcile_done(tx1.saturating_sub(tx0), diff);
        rec.delivered(iid, z, now, ITEM * diff);
    }

    /// The node's store gained bytes of `value`: advances the fetches for it and delivers the ones whose every
    /// requested range is now held. The caller records the store write itself ([`crate::suite::rec::Rec::value_bytes_written`]).
    pub fn value_progress(&mut self, now: u64, value: MsgId) {
        let iids = self
            .durable
            .borrow()
            .fetch_intents
            .get(&value.0)
            .cloned()
            .unwrap_or_default();
        let Some(store) = self.values.as_deref() else { return };
        for iid in iids {
            let mut rec = self.rec.borrow_mut();
            let Some(it) = rec.intents.get_mut(&iid) else { continue };
            if it.delivered.contains_key(&self.idx) {
                continue;
            }
            let ranges = it.meta.ranges.clone().unwrap_or_else(|| vec![(0, it.size)]);
            let contiguous = ranges.first().map_or(0, |&(o0, _)| store.contiguous_from(value, o0));
            if contiguous > 0 {
                // A sample with nothing available says nothing the stall fraction does not already assume.
                it.meta.first_byte.get_or_insert(now);
                it.meta.progress.push((now, contiguous));
            }
            if !ranges.iter().all(|&(o, n)| store.holds(value, o, n)) {
                continue;
            }
            if let Some(rate) = it.meta.stream_rate.filter(|&r| r != 0) {
                let total = it.meta.req_bytes.unwrap_or(it.size);
                it.meta.stall_frac = Some(stall_fraction(&it.meta.progress, it.meta.first_byte, rate, total));
            }
            rec.delivered(iid, self.idx, now, 0);
            drop(rec);
            let mut d = self.durable.borrow_mut();
            if let Some(i) = d.open_fetches.iter().position(|&x| x == iid) {
                d.open_fetches.remove(i);
            }
        }
    }
}

/// The fraction of a rate-paced consumer's playback time spent stalled: the consumer starts at `t_first`, plays
/// `rate_bps` bits per second out of what `progress` (`(time, contiguous bytes)`) says is available, and must play
/// `total` bytes. Not started or no progress is fully stalled (1.0).
pub fn stall_fraction(progress: &[(u64, u64)], t_first: Option<u64>, rate_bps: u64, total: u64) -> f64 {
    let Some(t_first) = t_first else { return 1.0 };
    if progress.is_empty() {
        return 1.0;
    }
    let rate = rate_bps as f64 / 8.0 / NS as f64;
    let total = total as f64;
    let (mut played, mut stalled, mut avail) = (0.0f64, 0.0f64, 0u64);
    let mut t = t_first as f64;
    for &(tn, an) in progress {
        if played >= total {
            break;
        }
        let tn = tn as f64;
        if tn > t {
            let can = (avail as f64).min(total) - played;
            let need_t = if rate > 0.0 { can / rate } else { 0.0 };
            if need_t >= tn - t {
                played += (tn - t) * rate;
            } else {
                played += can.max(0.0);
                stalled += (tn - t) - need_t.max(0.0);
            }
            t = tn;
        }
        avail = avail.max(an);
    }
    if played < total && rate > 0.0 {
        t += (total - played) / rate;
    }
    let span = t - t_first as f64;
    if span > 0.0 { stalled / span } else { 0.0 }
}
