//! The sessions of the harness and the discrete-event simulation that joins them.
#![allow(
    dead_code,
    unreachable_pub,
    unused_imports,
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::missing_panics_doc
)]

use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeMap, BinaryHeap, HashMap, VecDeque};
use std::ops::Range;
use std::rc::Rc;

use vinc_dag::ranges::VerifiedRanges;
use vinc_dag::tree::{Cv, OutboardBuilder, build_outboard_vec};
use vinc_tests::SplitMix64;
use vinc_transport::stream::{StreamId, StreamSource};
use vinc_values::fetch::{Fetch, FetchSpec, In, Io};
use vinc_values::server::{Server, ServerIn};
use vinc_values::session::{Inbound, OpenError, Outbound, PeerInfo, Provider, Session};
use vinc_values::source::ValueSource;
use vinc_values::store::{StoreError, ValueRead, ValueStore};
use vinc_values::trace::{Event, Out, Trace};

use super::stores::*;

// ---------------------------------------------------------------------------------------------------------------
// Sessions
// ---------------------------------------------------------------------------------------------------------------

#[derive(Default)]
struct CStream {
    prov: usize,
    pieces: BTreeMap<u64, Vec<u8>>,
    consumed: u64,
    front: u64,
    fin_total: Option<u64>,
    finished: bool,
    dead: bool,
}

pub enum ToProv {
    Open(StreamId),
    Write(StreamId, Vec<u8>, bool),
    Reset(StreamId, u64),
    Ext(StreamId, u64, Vec<u8>),
    Hangup,
}

/// The requester's session: streams to the providers, received bytes held until consumed.
pub struct ClientSession {
    pub now: u64,
    pub up: Vec<bool>,
    pub dialing: Vec<bool>,
    pub latency: Vec<u64>,
    pub last_rx: Vec<u64>,
    pub live: bool,
    pub pto: bool,
    pub max_open: usize,
    pub dials: Vec<usize>,
    streams: HashMap<StreamId, CStream>,
    next: StreamId,
    pub outbox: Vec<(usize, ToProv)>,
}

impl ClientSession {
    fn new(n: usize) -> Self {
        Self {
            now: 0,
            up: vec![false; n],
            dialing: vec![false; n],
            latency: vec![0; n],
            last_rx: vec![0; n],
            live: false,
            pto: false,
            max_open: usize::MAX,
            dials: Vec::new(),
            streams: HashMap::new(),
            next: 0,
            outbox: Vec::new(),
        }
    }

    pub fn open_streams(&self) -> usize {
        self.streams.values().filter(|s| !s.dead).count()
    }

    pub fn provider_of(&self, s: StreamId) -> Option<usize> {
        self.streams.get(&s).map(|s| s.prov)
    }

    /// Hold `data` at stream offset `off`; returns the event to tell the fetch.
    fn deliver(&mut self, stream: StreamId, off: u64, data: Vec<u8>) -> Option<In<'static>> {
        let s = self.streams.get_mut(&stream).filter(|s| !s.dead)?;
        let len = data.len() as u64;
        if off + len <= s.consumed || s.pieces.contains_key(&off) {
            return None;
        }
        s.pieces.insert(off, data);
        if off > s.front {
            return Some(In::Ahead {
                stream,
                offset: off,
                len,
            });
        }
        let before = s.front;
        while let Some((&k, v)) = s.pieces.range(..=s.front).next_back() {
            let end = k + v.len() as u64;
            if end <= s.front {
                break;
            }
            s.front = end;
        }
        let bytes = (s.front - before) as usize;
        (bytes > 0).then_some(In::Readable { stream, bytes })
    }

    /// Streams whose end was reached and fully consumed and not yet announced.
    fn finished(&mut self) -> Vec<StreamId> {
        let mut out = Vec::new();
        for (id, s) in &mut self.streams {
            if !s.finished && !s.dead && s.fin_total.is_some_and(|t| s.consumed >= t) {
                s.finished = true;
                out.push(*id);
            }
        }
        out.sort_unstable();
        out
    }
}

impl Session for ClientSession {
    fn visit<F: FnMut(&[u8]) -> usize>(&mut self, stream: StreamId, from: u64, mut f: F) {
        let Some(s) = self.streams.get(&stream) else { return };
        let mut at = from;
        while let Some((&k, v)) = s.pieces.range(..=at).next_back() {
            if k + v.len() as u64 <= at {
                break;
            }
            let slice = &v[(at - k) as usize..];
            let n = f(slice);
            at += n as u64;
            if n < slice.len() {
                break;
            }
        }
    }

    fn has(&self, stream: StreamId, from: u64, len: u64) -> bool {
        let Some(s) = self.streams.get(&stream) else {
            return false;
        };
        let (mut at, end) = (from, from + len);
        while at < end {
            match s.pieces.range(..=at).next_back() {
                Some((&k, v)) if k + v.len() as u64 > at => at = k + v.len() as u64,
                _ => return false,
            }
        }
        true
    }

    fn consume(&mut self, stream: StreamId, upto: u64) {
        if let Some(s) = self.streams.get_mut(&stream) {
            s.consumed = s.consumed.max(upto);
            s.pieces.retain(|k, v| *k + v.len() as u64 > upto);
        }
    }

    fn write(&mut self, stream: StreamId, data: &[u8], fin: bool) -> bool {
        let Some(s) = self.streams.get(&stream) else {
            return false;
        };
        self.outbox.push((s.prov, ToProv::Write(stream, data.to_vec(), fin)));
        true
    }

    fn reset(&mut self, stream: StreamId, code: u64) {
        if let Some(s) = self.streams.get_mut(&stream) {
            if !s.dead {
                self.outbox.push((s.prov, ToProv::Reset(stream, code)));
            }
            s.dead = true;
            s.pieces.clear();
        }
    }

    fn send_ext(&mut self, stream: StreamId, ty: u64, body: &[u8]) -> bool {
        let Some(s) = self.streams.get(&stream) else {
            return false;
        };
        self.outbox.push((s.prov, ToProv::Ext(stream, ty, body.to_vec())));
        true
    }
}

impl Outbound for ClientSession {
    fn is_connected(&self, p: Provider) -> bool {
        self.up.get(p.0 as usize).copied().unwrap_or(false)
    }
    fn dial(&mut self, p: Provider) {
        let i = p.0 as usize;
        if !self.dialing[i] && !self.up[i] {
            self.dialing[i] = true;
            self.dials.push(i);
        }
    }
    fn hangup(&mut self, p: Provider) {
        let i = p.0 as usize;
        self.up[i] = false;
        for s in self.streams.values_mut().filter(|s| s.prov == i) {
            s.dead = true;
            s.pieces.clear();
        }
        self.outbox.push((i, ToProv::Hangup));
    }
    fn open_stream(&mut self, p: Provider, _urgency: u8) -> Result<StreamId, OpenError> {
        let i = p.0 as usize;
        if !self.up[i] {
            return Err(OpenError::NotConnected);
        }
        if self.open_streams() >= self.max_open {
            return Err(OpenError::Busy);
        }
        self.next += 1;
        let id = self.next;
        self.streams.insert(
            id,
            CStream {
                prov: i,
                ..CStream::default()
            },
        );
        self.outbox.push((i, ToProv::Open(id)));
        Ok(id)
    }
    fn peer_info(&self, p: Provider) -> Option<PeerInfo> {
        let i = p.0 as usize;
        self.up[i].then(|| PeerInfo {
            rtt_ns: Some(2 * self.latency[i]),
            pto: self.pto,
            last_rx: if self.live { self.now } else { self.last_rx[i] },
        })
    }
}

pub enum ToClient {
    Data(StreamId, u64, Vec<u8>),
    Fin(StreamId, u64),
    Reset(StreamId, u64),
    Ext(StreamId, u64, Vec<u8>),
}

/// A provider's session: request bytes in, sources installed, resets and extension frames out.
#[derive(Default)]
pub struct ServerSession {
    pub reqs: HashMap<StreamId, Vec<u8>>,
    pub installs: Vec<(StreamId, ValueSource<PStore>, u64)>,
    pub out: Vec<ToClient>,
    pub consumed: HashMap<StreamId, u64>,
}

impl Session for ServerSession {
    fn visit<F: FnMut(&[u8]) -> usize>(&mut self, stream: StreamId, from: u64, mut f: F) {
        if let Some(r) = self.reqs.get(&stream)
            && let Some(rest) = r.get(from as usize..).filter(|r| !r.is_empty())
        {
            f(rest);
        }
    }
    fn has(&self, stream: StreamId, from: u64, len: u64) -> bool {
        self.reqs.get(&stream).is_some_and(|r| (from + len) as usize <= r.len())
    }
    fn consume(&mut self, stream: StreamId, upto: u64) {
        self.consumed.insert(stream, upto);
    }
    fn write(&mut self, _: StreamId, _: &[u8], _: bool) -> bool {
        false
    }
    fn reset(&mut self, stream: StreamId, code: u64) {
        self.out.push(ToClient::Reset(stream, code));
    }
    fn send_ext(&mut self, stream: StreamId, ty: u64, body: &[u8]) -> bool {
        self.out.push(ToClient::Ext(stream, ty, body.to_vec()));
        true
    }
}

impl Inbound<PStore> for ServerSession {
    fn serve(&mut self, stream: StreamId, source: ValueSource<PStore>, len: u64) -> bool {
        self.installs.push((stream, source, len));
        true
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The simulation
// ---------------------------------------------------------------------------------------------------------------

#[derive(Clone)]
pub struct ProvCfg {
    pub store: PStore,
    /// Bytes per millisecond.
    pub rate: u64,
    /// One-way latency in nanoseconds.
    pub latency: u64,
    pub loss_permille: u64,
    pub reorder_ms: u64,
    /// After this many bytes sent the link goes silent (the session stays up).
    pub stall_after: Option<u64>,
}

impl ProvCfg {
    pub fn new(store: PStore, rate: u64) -> Self {
        Self {
            store,
            rate,
            latency: 10 * MS,
            loss_permille: 0,
            reorder_ms: 0,
            stall_after: None,
        }
    }
    pub fn latency(mut self, ns: u64) -> Self {
        self.latency = ns;
        self
    }
    pub fn loss(mut self, permille: u64) -> Self {
        self.loss_permille = permille;
        self
    }
    pub fn reorder(mut self, ms: u64) -> Self {
        self.reorder_ms = ms;
        self
    }
    pub fn stall_after(mut self, bytes: u64) -> Self {
        self.stall_after = Some(bytes);
        self
    }
}

struct Tx {
    source: ValueSource<PStore>,
    total: u64,
    next: u64,
    retx: VecDeque<(u64, u64)>,
    pending: u32,
    fin_sent: bool,
}

pub struct PSim {
    pub cfg: ProvCfg,
    pub up: bool,
    pub silent: bool,
    pub sent_bytes: u64,
    epoch: u64,
    server: Server<PStore, 32>,
    sess: ServerSession,
    pub rec: Rec,
    txs: BTreeMap<StreamId, Tx>,
    ticking: bool,
}

enum Ev {
    ToProv(usize, u64, ToProv),
    ToClient(usize, u64, ToClient),
    Tick(usize),
    Dial(usize),
    Detect(usize, u64, StreamId, u64, u64),
}

struct Item {
    t: u64,
    seq: u64,
    ev: Ev,
}
impl PartialEq for Item {
    fn eq(&self, o: &Self) -> bool {
        (self.t, self.seq) == (o.t, o.seq)
    }
}
impl Eq for Item {}
impl PartialOrd for Item {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Item {
    fn cmp(&self, o: &Self) -> Ordering {
        (self.t, self.seq).cmp(&(o.t, o.seq))
    }
}

pub struct Sim {
    pub now: u64,
    pub sess: ClientSession,
    pub store: ClientStore,
    pub rec: Rec,
    pub fetch: Box<Fetch>,
    pub provs: Vec<PSim>,
    heap: BinaryHeap<Reverse<Item>>,
    seq: u64,
    rng: SplitMix64,
    pub root: Cv,
    pub length: u64,
}

impl Sim {
    pub fn new(cfgs: Vec<ProvCfg>, store: ClientStore) -> Self {
        let root = cfgs[0].store.root();
        let length = cfgs[0].store.len();
        let mut sess = ClientSession::new(cfgs.len());
        for (i, c) in cfgs.iter().enumerate() {
            sess.latency[i] = c.latency;
        }
        let provs = cfgs
            .into_iter()
            .map(|cfg| PSim {
                server: Server::new(cfg.store.clone()),
                cfg,
                up: true,
                silent: false,
                sent_bytes: 0,
                epoch: 0,
                sess: ServerSession::default(),
                rec: Rec::default(),
                txs: BTreeMap::new(),
                ticking: false,
            })
            .collect();
        Self {
            now: 0,
            sess,
            store,
            rec: Rec::default(),
            fetch: Box::new(Fetch::new()),
            provs,
            heap: BinaryHeap::new(),
            seq: 0,
            rng: SplitMix64::new(0x00C0_FFEE),
            root,
            length,
        }
    }

    /// A simulation of `n` identical providers of one random value.
    pub fn uniform(n: usize, len: usize, rate: u64) -> Self {
        let store = PStore::random(7, len);
        Self::new(
            (0..n).map(|_| ProvCfg::new(store.clone(), rate)).collect(),
            ClientStore::new(),
        )
    }

    fn push(&mut self, t: u64, ev: Ev) {
        self.seq += 1;
        self.heap.push(Reverse(Item { t, seq: self.seq, ev }));
    }

    pub fn spec<'a>(&self, ranges: &'a [vinc_values::span::Span], provs: &'a [Provider]) -> FetchSpec<'a> {
        FetchSpec {
            root: self.root,
            length: self.length,
            ranges,
            providers: provs,
            deadline: None,
        }
    }

    pub fn all_providers(&self) -> Vec<Provider> {
        (0..self.provs.len() as u32).map(Provider).collect()
    }

    /// Start a whole-value fetch from every provider.
    pub fn start(&mut self) {
        let provs = self.all_providers();
        self.start_with(&[], &provs, None);
    }

    pub fn start_with(&mut self, ranges: &[vinc_values::span::Span], provs: &[Provider], deadline: Option<u64>) {
        let mut spec = self.spec(ranges, provs);
        spec.deadline = deadline;
        for p in provs {
            self.sess.up[p.0 as usize] = false;
        }
        let mut io = Io {
            session: &mut self.sess,
            store: &mut self.store,
            out: &mut self.rec,
        };
        self.fetch.start(&mut io, self.now, &spec).unwrap();
        self.flush();
    }

    /// Cut provider `i`: its in-flight messages are lost and the requester sees the session close.
    pub fn cut(&mut self, i: usize) {
        let p = &mut self.provs[i];
        p.up = false;
        p.epoch += 1;
        p.txs.clear();
        self.sess.up[i] = false;
        for s in self.sess.streams.values_mut().filter(|s| s.prov == i) {
            s.dead = true;
            s.pieces.clear();
        }
        self.fetch_event(&In::Closed(Provider(i as u32)));
    }

    /// Bring provider `i` back up (a later dial succeeds).
    pub fn revive(&mut self, i: usize) {
        self.provs[i].up = true;
    }

    fn fetch_event(&mut self, ev: &In<'_>) {
        let mut io = Io {
            session: &mut self.sess,
            store: &mut self.store,
            out: &mut self.rec,
        };
        self.fetch.on_event(&mut io, self.now, ev);
        self.flush();
    }

    /// Route what the requester's session queued, announce finished streams.
    fn flush(&mut self) {
        loop {
            let out = std::mem::take(&mut self.sess.outbox);
            let dials = std::mem::take(&mut self.sess.dials);
            let done = self.sess.finished();
            if out.is_empty() && dials.is_empty() && done.is_empty() {
                break;
            }
            for (i, msg) in out {
                let (t, g) = (self.now + self.provs[i].cfg.latency, self.provs[i].epoch);
                self.push(t, Ev::ToProv(i, g, msg));
            }
            for i in dials {
                let t = self.now + 2 * self.provs[i].cfg.latency;
                self.push(t, Ev::Dial(i));
            }
            for s in done {
                self.fetch_event(&In::Finished(s));
            }
        }
    }

    fn server_event(&mut self, i: usize, ev: &ServerIn<'_>) {
        let p = &mut self.provs[i];
        p.server.on_event(&mut p.sess, &mut p.rec, self.now, ev);
        let lat = p.cfg.latency;
        for (stream, source, total) in std::mem::take(&mut p.sess.installs) {
            p.txs.insert(
                stream,
                Tx {
                    source,
                    total,
                    next: 0,
                    retx: VecDeque::new(),
                    pending: 0,
                    fin_sent: false,
                },
            );
        }
        let g = p.epoch;
        let msgs = std::mem::take(&mut p.sess.out);
        let need_tick = !p.txs.is_empty() && !p.ticking;
        if need_tick {
            p.ticking = true;
        }
        for m in msgs {
            self.push(self.now + lat, Ev::ToClient(i, g, m));
        }
        if need_tick {
            self.push(self.now + MS, Ev::Tick(i));
        }
    }

    fn tick(&mut self, i: usize) {
        let now = self.now;
        let (lat, rate, loss, reorder, stall) = {
            let c = &self.provs[i].cfg;
            (c.latency, c.rate, c.loss_permille, c.reorder_ms, c.stall_after)
        };
        let g = self.provs[i].epoch;
        let mut pending: Vec<(u64, Ev)> = Vec::new();
        let mut sent_events: Vec<ServerIn<'static>> = Vec::new();
        let mut budget = rate;
        let ids: Vec<StreamId> = self.provs[i].txs.keys().copied().collect();
        for id in ids {
            while budget > 0 {
                let p = &mut self.provs[i];
                let silent = p.silent || stall.is_some_and(|n| p.sent_bytes >= n);
                let room = stall.map_or(u64::MAX, |n| n.saturating_sub(p.sent_bytes));
                let Some(tx) = p.txs.get_mut(&id) else { break };
                if silent {
                    break;
                }
                let (off, avail, from_retx) = if let Some((o, l)) = tx.retx.pop_front() {
                    (o, l, true)
                } else if tx.next < tx.total {
                    (tx.next, tx.total - tx.next, false)
                } else {
                    break;
                };
                let want = avail.min(budget).min(PACKET as u64).min(room) as usize;
                let mut buf = vec![0u8; want];
                let got = tx.source.read_at(off, &mut buf);
                buf.truncate(got);
                if got == 0 {
                    break;
                }
                let got64 = got as u64;
                if from_retx && got64 < avail {
                    tx.retx.push_front((off + got64, avail - got64));
                }
                if !from_retx {
                    tx.next = off + got64;
                }
                p.sent_bytes += got64;
                budget = budget.saturating_sub(got64);
                let next = tx.next;
                if loss > 0 && self.rng.next_u64() % 1000 < loss {
                    tx.pending += 1;
                    pending.push((now + 2 * lat, Ev::Detect(i, g, id, off, got64)));
                } else {
                    let jitter = if reorder > 0 {
                        self.rng.next_u64() % (reorder * MS)
                    } else {
                        0
                    };
                    pending.push((now + lat + jitter, Ev::ToClient(i, g, ToClient::Data(id, off, buf))));
                }
                sent_events.push(ServerIn::Sent {
                    stream: id,
                    sent: next,
                    window: 65_536,
                });
            }
            if let Some(tx) = self.provs[i].txs.get_mut(&id)
                && tx.next >= tx.total
                && tx.retx.is_empty()
                && tx.pending == 0
                && !tx.fin_sent
            {
                tx.fin_sent = true;
                pending.push((
                    now + lat + (reorder + 3) * MS,
                    Ev::ToClient(i, g, ToClient::Fin(id, tx.total)),
                ));
            }
        }
        for (t, ev) in pending {
            self.push(t, ev);
        }
        for ev in sent_events {
            self.server_event(i, &ev);
        }
        let finished: Vec<StreamId> = self.provs[i]
            .txs
            .iter()
            .filter(|(_, t)| t.fin_sent)
            .map(|(id, _)| *id)
            .collect();
        for id in finished {
            self.provs[i].txs.remove(&id);
            self.server_event(i, &ServerIn::Done(id));
        }
        let p = &mut self.provs[i];
        if p.txs.is_empty() {
            p.ticking = false;
        } else {
            self.push(now + MS, Ev::Tick(i));
        }
    }

    fn handle(&mut self, ev: Ev) {
        match ev {
            Ev::ToProv(i, g, msg) => {
                if g != self.provs[i].epoch || !self.provs[i].up {
                    return;
                }
                let peer = Provider(1000);
                match msg {
                    ToProv::Open(s) => {
                        self.provs[i].sess.reqs.insert(s, Vec::new());
                        self.server_event(i, &ServerIn::Opened { stream: s, peer });
                    }
                    ToProv::Write(s, d, _fin) => {
                        self.provs[i].sess.reqs.entry(s).or_default().extend_from_slice(&d);
                        self.server_event(i, &ServerIn::Readable(s));
                    }
                    ToProv::Reset(s, _) => {
                        self.provs[i].txs.remove(&s);
                        self.server_event(i, &ServerIn::Reset(s));
                    }
                    ToProv::Ext(_, ty, body) => self.server_event(i, &ServerIn::Ext { ty, body: &body }),
                    ToProv::Hangup => {
                        self.provs[i].txs.clear();
                        self.server_event(i, &ServerIn::Closed(peer));
                    }
                }
            }
            Ev::ToClient(i, g, msg) => {
                if g != self.provs[i].epoch || !self.sess.up[i] {
                    return;
                }
                self.sess.last_rx[i] = self.now;
                match msg {
                    ToClient::Data(s, off, d) => {
                        if let Some(ev) = self.sess.deliver(s, off, d) {
                            self.fetch_event(&ev);
                        }
                    }
                    ToClient::Fin(s, total) => {
                        if let Some(st) = self.sess.streams.get_mut(&s) {
                            st.fin_total = Some(total);
                        }
                        self.flush();
                    }
                    ToClient::Reset(s, code) => {
                        if let Some(st) = self.sess.streams.get_mut(&s) {
                            st.dead = true;
                            st.pieces.clear();
                        }
                        self.fetch_event(&In::Reset { stream: s, code });
                    }
                    ToClient::Ext(_, ty, body) => self.fetch_event(&In::Ext { ty, body: &body }),
                }
            }
            Ev::Tick(i) => self.tick(i),
            Ev::Dial(i) => {
                self.sess.dialing[i] = false;
                if self.provs[i].up {
                    self.sess.up[i] = true;
                    self.sess.last_rx[i] = self.now;
                    self.fetch_event(&In::Connected(Provider(i as u32)));
                } else {
                    self.fetch_event(&In::ConnectFailed(Provider(i as u32)));
                }
            }
            Ev::Detect(i, g, s, off, len) => {
                if g != self.provs[i].epoch {
                    return;
                }
                let sent = {
                    let tx = self.provs[i].txs.get_mut(&s);
                    match tx {
                        Some(tx) => {
                            tx.pending -= 1;
                            tx.retx.push_back((off, len));
                            tx.next
                        }
                        None => return,
                    }
                };
                self.sess.now = self.now;
                self.server_event(
                    i,
                    &ServerIn::Loss {
                        stream: s,
                        offset: off,
                        sent,
                        window: 65_536,
                    },
                );
            }
        }
    }

    /// Run until `stop` or `limit` (a virtual time); returns whether `stop` held.
    pub fn run_until(&mut self, limit: u64, mut stop: impl FnMut(&Sim) -> bool) -> bool {
        let mut same = 0;
        let mut last = u64::MAX;
        loop {
            if stop(self) {
                return true;
            }
            let te = self.heap.peek().map(|r| r.0.t);
            let tt = self.fetch.poll_timeout();
            let next = match (te, tt) {
                (None, None) => return false,
                (Some(a), None) => a,
                (None, Some(b)) => b,
                (Some(a), Some(b)) => a.min(b),
            };
            if next > limit {
                self.now = limit;
                return false;
            }
            self.now = self.now.max(next);
            self.sess.now = self.now;
            if te.is_some_and(|a| a <= self.now) {
                let Reverse(item) = self.heap.pop().unwrap();
                self.handle(item.ev);
            } else {
                let mut io = Io {
                    session: &mut self.sess,
                    store: &mut self.store,
                    out: &mut self.rec,
                };
                self.fetch.on_timeout(&mut io, self.now);
                self.flush();
                if last == self.now {
                    same += 1;
                    assert!(same < 10_000, "timer fires without progress at {}", self.now);
                } else {
                    same = 0;
                    last = self.now;
                }
            }
        }
    }

    /// Run to the end of the fetch (success or failure) within `limit_s` virtual seconds.
    pub fn run(&mut self, limit_s: u64) {
        let done = self.run_until(limit_s * SEC, |s| s.fetch.is_done());
        assert!(
            done,
            "fetch did not finish within {limit_s} s (now {} s)",
            self.now / SEC
        );
        // Let the resets and the last messages land.
        let end = self.now + SEC;
        self.run_until(end, |_| false);
    }
}
