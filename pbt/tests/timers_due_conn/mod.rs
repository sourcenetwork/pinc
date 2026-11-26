//! The driver of the connection-level timer checks of `timers_due.rs` and `repro_transport2.rs`: two real
//! `pinc_transport` connections (the public API an application uses) on a scripted link in virtual time, the clock
//! starting where the case says (possibly a few seconds before the end of `u64`), and a generated script of what the
//! application does to either side: streams, datagrams, pings, a keepalive, the link down and back, sleep and wake, a
//! probe of a second path whose datagrams go nowhere, a close, a link that drops everything, a reader that stops.
//!
//! The rule, after every step: a side whose `poll_timeout()` was due at `t` gets `handle_timeout(t)` and then
//! `poll_transmit` until `None` with nothing else in between; then its `poll_timeout()` is `None` or later than `t`
//! ("The next time `handle_timeout` must run", crates/pinc-transport/src/conn/timer.rs:29; "a timer is reported only
//! while it can still act (a stale deadline would make a driver spin)", timer.rs:3).
#![allow(dead_code, clippy::unwrap_used, clippy::panic, clippy::indexing_slicing)]

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use ephyra::gens;
use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use pinc_security::{AlpnList, Env, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys, SoftPrekeys};
use pinc_transport::conn::{
    ClientParams, Config, Connection, Event, Lent, PathId, PathInfo, Resources, ServerParams, Tables, Transmit,
};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::spill::SpillArena;
use pinc_transport::stream::{self, NoSource, Streams};

pub const MS: u64 = 1_000_000;
const ALPN: &[u8] = b"pinc/1";
const CHUNKS: usize = 256;

type Table = Streams<NoSource, 64, 257>;
type Conn<'a> = Connection<'a, Software, NoSource, 64, 257, 512, 4>;
type Stores = ResponderStores<8, 512>;

/// What the application (or the link) does next; `from` is 0 for the dialer, 1 for the server.
#[derive(Clone, Debug, PartialEq, Eq, ephyra::Arbitrary)]
pub enum COp {
    Wait(#[ephyra(gen = gens::frequency(vec![(3, gens::int(1u64..=600).boxed()), (1, gens::int(1u64..=40_000).boxed())]))] u64),
    Write {
        #[ephyra(gen = gens::int(0u8..=1))]
        from: u8,
        #[ephyra(gen = gens::frequency(vec![(3, gens::int(0usize..=4_000).boxed()), (1, gens::int(0usize..=400_000).boxed())]))]
        len: usize,
    },
    Datagram {
        #[ephyra(gen = gens::int(0u8..=1))]
        from: u8,
        #[ephyra(gen = gens::int(1usize..=1_400))]
        len: usize,
    },
    Ping(#[ephyra(gen = gens::int(0u8..=1))] u8),
    /// `set_keepalive`: 0 turns it off, else an interval of this many ms.
    Keepalive {
        #[ephyra(gen = gens::int(0u8..=1))]
        from: u8,
        #[ephyra(gen = gens::frequency(vec![(1, gens::constant(0u64).boxed()), (2, gens::int(1u64..=20_000).boxed())]))]
        ms: u64,
    },
    LinkDown {
        #[ephyra(gen = gens::int(0u8..=1))]
        from: u8,
        down: bool,
    },
    Sleep(#[ephyra(gen = gens::int(0u8..=1))] u8),
    Wake(#[ephyra(gen = gens::int(0u8..=1))] u8),
    /// A second path (its datagrams go nowhere), challenged at once.
    Probe(#[ephyra(gen = gens::int(0u8..=1))] u8),
    Close(#[ephyra(gen = gens::int(0u8..=1))] u8),
    /// The link drops everything for this many ms.
    Cut(#[ephyra(gen = gens::frequency(vec![(3, gens::int(1u64..=3_000).boxed()), (1, gens::int(1u64..=60_000).boxed())]))] u64),
    Read {
        #[ephyra(gen = gens::int(0u8..=1))]
        from: u8,
        on: bool,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, ephyra::Arbitrary)]
pub struct CCase {
    /// 0: the clock starts at 1000 s; else it starts this many ms before `u64::MAX`.
    #[ephyra(gen = gens::frequency(vec![(3, gens::constant(0u64).boxed()), (1, gens::int(1u64..=120_000).boxed())]))]
    pub end: u64,
    #[ephyra(gen = gens::frequency(vec![(3, gens::int(1u64..=40).boxed()), (1, gens::int(1u64..=300).boxed())]))]
    pub delay_ms: u64,
    pub flight_split: bool,
    #[ephyra(gen = gens::vec(ephyra::any::<COp>()).len(0..=12))]
    pub ops: Vec<COp>,
}

pub fn in_support(c: &CCase) -> bool {
    c.end <= 120_000 && (1..=300).contains(&c.delay_ms) && c.ops.len() <= 12
}

/// How long the driver lets the case run after an op.
fn span(op: &COp) -> u64 {
    match *op {
        COp::Wait(ms) | COp::Cut(ms) => ms * MS,
        _ => 30 * MS,
    }
}

fn label(op: Option<&COp>, end: bool) -> &'static str {
    macro_rules! pick {
        ($($p:pat => $s:literal),* $(,)?) => {
            match (op, end) {
                $(($p, false) => concat!("a connection timer stays due after handle_timeout ran at its time (", $s, ")"),
                  ($p, true) => concat!("a connection timer stays due after handle_timeout ran at its time near the end of the clock (", $s, ")"),)*
            }
        };
    }
    pick! {
        None => "connecting",
        Some(COp::Wait(_)) => "after a wait",
        Some(COp::Write { .. }) => "after a write",
        Some(COp::Datagram { .. }) => "after a datagram",
        Some(COp::Ping(_)) => "after a ping",
        Some(COp::Keepalive { .. }) => "after a keepalive change",
        Some(COp::LinkDown { .. }) => "after a link change",
        Some(COp::Sleep(_)) => "asleep",
        Some(COp::Wake(_)) => "after a wake",
        Some(COp::Probe(_)) => "probing a dead path",
        Some(COp::Close(_)) => "closing",
        Some(COp::Cut(_)) => "while the link drops everything",
        Some(COp::Read { .. }) => "after a reader change",
    }
}

struct Side<'a> {
    conn: Conn<'a>,
    drbg: Drbg,
    kp: Keypair,
    prekeys: Option<SoftPrekeys<Software>>,
    spill: SpillArena<'a>,
    /// Streams still being written: (id, bytes left).
    outs: Vec<(u64, usize)>,
    reading: bool,
    connected: bool,
    path2: bool,
}

macro_rules! env {
    ($s:expr, $now:expr) => {
        Env {
            provider: &Software,
            now: $now,
            drbg: &mut $s.drbg,
        }
    };
}

impl Side<'_> {
    fn service(&mut self, now: u64) {
        for _ in 0..1_000 {
            let mut key = false;
            let mut readable = Vec::new();
            while let Some(ev) = self.conn.poll_event() {
                match ev {
                    Event::KeyRequest(_) => key = true,
                    Event::Connected { .. } => self.connected = true,
                    Event::StreamReadable(id) => readable.push(id),
                    _ => {},
                }
            }
            while self.conn.recv_datagram().is_some() {
                self.conn.pop_datagram();
            }
            if self.reading {
                for id in readable {
                    while let Some(n) = self.conn.read_chunk(id).map(<[u8]>::len) {
                        if n == 0 || self.conn.consume(&mut env!(self, now), &mut Lent { spill: &mut self.spill }, id, n).is_err() {
                            break;
                        }
                    }
                }
            }
            if !key {
                return;
            }
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &self.kp)),
                prekeys: self.prekeys.as_ref(),
            };
            let mut env = Env {
                provider: &Software,
                now,
                drbg: &mut self.drbg,
            };
            while self.conn.answer_soft(&mut env, &soft).unwrap_or(false) {}
        }
    }

    fn write_out(&mut self) {
        let chunk = [5u8; 16 * 1024];
        for (id, left) in &mut self.outs {
            while *left > 0 {
                match self.conn.write(*id, &chunk[..(*left).min(chunk.len())]) {
                    Ok(0) | Err(_) => break,
                    Ok(n) => *left -= n,
                }
            }
            if *left == 0 {
                let _ = self.conn.finish(*id);
            }
        }
        self.outs.retain(|o| o.1 > 0);
    }

    /// Everything the side has to send, onto the link (path 1) or nowhere (any other path).
    fn transmit(&mut self, now: u64, to_client: bool, link: &mut Link, buf: &mut [u8]) {
        for _ in 0..20_000 {
            let Some(Transmit { path, len, segment_size }) =
                self.conn.poll_transmit(&mut env!(self, now), &mut Lent { spill: &mut self.spill }, buf)
            else {
                return;
            };
            if path != PathId(1) || link.cut {
                continue;
            }
            for seg in buf[..len].chunks(segment_size.max(1)) {
                link.seq += 1;
                link.q.push(Reverse((now.saturating_add(link.delay), link.seq, to_client, seg.to_vec())));
            }
        }
        panic!("poll_transmit never returned None");
    }
}

struct Link {
    q: BinaryHeap<Reverse<(u64, u64, bool, Vec<u8>)>>,
    seq: u64,
    delay: u64,
    cut: bool,
}

/// What a run did, so a test can tell that it ran at all.
#[derive(Debug, Clone, Copy, Default)]
pub struct Summary {
    pub connected: bool,
    pub datagrams: u64,
    pub ops: usize,
    /// ms of the clock the run covered.
    pub ran_ms: u64,
}

/// Run the case; panics (with an ephyra signature) at the first step that breaks the rule.
pub fn run(c: &CCase) {
    let _ = run_summary(c);
}

pub fn run_summary(c: &CCase) -> Summary {
    run_with(c, false)
}

/// [`run_summary`], letting the known causes pass when `known_full_ring`.
pub fn run_with(c: &CCase, known_full_ring: bool) -> Summary {
    let alg = IdentityAlg::Ed25519;
    let ckp = Keypair::from_seed(alg, &vec![0x21; alg.seed_len()]).unwrap();
    let skp = Keypair::from_seed(alg, &vec![0x22; alg.seed_len()]).unwrap();
    let cid = LocalIdentity::from_keypair(&ckp, KeyHandle(1)).unwrap();
    let sid = LocalIdentity::from_keypair(&skp, KeyHandle(1)).unwrap();
    let mut stores: Box<Stores> = Box::default();
    let mut ctab = Box::new(Table::new(&stream::Config::new(true), &BufferPool::new_boxed(CHUNKS)));
    let mut stab = Box::new(Table::new(&stream::Config::new(false), &BufferPool::new_boxed(CHUNKS)));
    let (closs, sloss) = (LossEstimate::new(), LossEstimate::new());
    let start = if c.end == 0 { 1_000 * 1_000 * MS } else { u64::MAX - c.end * MS };
    let mut cfg = Config::new();
    cfg.flight_split = c.flight_split;

    let mut cdrbg = Drbg::new(&[0x11; 32]);
    let mut env = Env {
        provider: &Software,
        now: start,
        drbg: &mut cdrbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
    let client = Conn::client(
        cfg,
        ClientParams {
            peer: sid.node_id(),
            alpn: ALPN,
            identity: &cid,
            prekey: &prekey,
            peer_has_prekey: false,
            ticket: None,
            path: PathId(1),
            path_info: PathInfo::default(),
        },
        Resources {
            pool: BufferPool::new_boxed(CHUNKS),
            streams: (&mut *ctab).into(),
            loss: (&closs).into(),
            tables: Tables::new(),
        },
        &mut env,
    )
    .unwrap();
    let mut sdrbg = Drbg::new(&[0x33; 32]);
    let params = ServerParams {
        identity: sid,
        alpns: AlpnList::new(&[ALPN]).unwrap(),
        tickets_per_session: 1,
        ticket_lifetime_s: 86_400,
    };
    let server = Conn::server(
        cfg,
        &params,
        Resources {
            pool: BufferPool::new_boxed(CHUNKS),
            streams: (&mut *stab).into(),
            loss: (&sloss).into(),
            tables: Tables::new(),
        },
        &mut Env {
            provider: &Software,
            now: start,
            drbg: &mut sdrbg,
        },
    )
    .unwrap();
    let side = |conn, drbg, kp, prekeys| Side {
        conn,
        drbg,
        kp,
        prekeys,
        spill: SpillArena::default(),
        outs: Vec::new(),
        reading: true,
        connected: false,
        path2: false,
    };
    let mut s = [side(client, cdrbg, ckp, Some(prekeys)), side(server, sdrbg, skp, None)];
    let mut link = Link {
        q: BinaryHeap::new(),
        seq: 0,
        delay: c.delay_ms * MS,
        cut: false,
    };
    let mut buf = vec![0u8; 65_536];
    let mut now = start;
    let mut next_op = 0usize;
    // The first op waits for the handshake (or 31 s); the run ends 70 s after the last.
    let mut op_at = start.saturating_add(31_000 * MS);
    let mut end: Option<u64> = None;
    let mut cut_until: Option<u64> = None;
    let mut same = 0u32;
    for _ in 0..3_000_000u32 {
        // Deliver what is due.
        while link.q.peek().is_some_and(|Reverse(w)| w.0 <= now) {
            let Reverse((_, _, to_client, mut d)) = link.q.pop().unwrap();
            if to_client {
                let a = &mut s[0];
                let _ = a.conn.handle_datagram(&mut env!(a, now), &mut Lent { spill: &mut a.spill }, PathId(1), &mut d);
            } else {
                let b = &mut s[1];
                let _ = b.conn.handle_datagram_with(
                    &mut env!(b, now),
                    &mut Lent { spill: &mut b.spill },
                    &mut *stores,
                    PathId(1),
                    &mut d,
                );
            }
        }
        s.iter_mut().for_each(|x| x.service(now));
        if cut_until.is_some_and(|u| u <= now) {
            cut_until = None;
            link.cut = false;
        }
        if s[0].connected && s[1].connected && next_op == 0 && op_at > now {
            op_at = now;
        }
        if end.is_none() && op_at <= now {
            if let Some(op) = c.ops.get(next_op) {
                apply(&mut s, op, now, &mut link, &mut cut_until);
                next_op += 1;
                op_at = now.saturating_add(span(op));
            } else {
                end = Some(now.saturating_add(70_000 * MS));
            }
        }
        for (k, x) in s.iter_mut().enumerate() {
            x.write_out();
            x.transmit(now, k == 1, &mut link, &mut buf);
            x.service(now);
        }
        // Timers, then the rule.
        for (k, x) in s.iter_mut().enumerate() {
            if x.conn.poll_timeout().is_none_or(|t| t > now) {
                continue;
            }
            x.conn.handle_timeout(&mut env!(x, now), &mut Lent { spill: &mut x.spill });
            x.transmit(now, k == 1, &mut link, &mut buf);
            let after = x.conn.poll_timeout();
            // The known case (repro_transport.rs): the probe deadline saturates at the end of the clock. Nothing can
            // run past it, so the case ends here; another timer due at the same instant is not seen.
            if now == u64::MAX && after == Some(u64::MAX) && x.conn.recovery().next_timeout() == Some(u64::MAX) {
                return Summary::default();
            }
            // The class of the known key-roll case (repro_transport_link.rs) and of the keepalive (repro_transport2.rs):
            // a timer whose packet cannot be built while the in-flight ring is full. The case ends here; another
            // timer blocked the same way is not seen.
            if known_full_ring && after.is_some_and(|t| t <= now) && !x.conn.recovery().ring_has_room() {
                return Summary::default();
            }
            if after.is_some_and(|t| t <= now) {
                let sig = label(next_op.checked_sub(1).and_then(|i| c.ops.get(i)), c.end > 0);
                ephyra::signature(sig);
                panic!(
                    "{sig}: {} at end - {} ms: poll_timeout {after:?}, recovery {:?}, rekey {:?}, ring room {}, can send {}; stats {:?}; ops done {:?}",
                    if k == 0 { "the dialer" } else { "the server" },
                    (u64::MAX - now) / MS,
                    x.conn.recovery().next_timeout(),
                    x.conn.rekey_deadline(),
                    x.conn.recovery().ring_has_room(),
                    x.conn.recovery().can_send(),
                    x.conn.stats(),
                    &c.ops[..next_op],
                );
            }
            x.service(now);
        }
        let next = [
            link.q.peek().map(|Reverse(w)| w.0),
            s[0].conn.poll_timeout(),
            s[1].conn.poll_timeout(),
            end.is_none().then_some(op_at),
            cut_until,
        ]
        .into_iter()
        .flatten()
        .min();
        let summary = Summary {
            connected: s[0].connected && s[1].connected,
            datagrams: link.seq,
            ops: next_op,
            ran_ms: (now - start) / MS,
        };
        let Some(t) = next else { return summary };
        if end.is_some_and(|e| t > e || (t <= now && now == u64::MAX)) {
            return summary;
        }
        if t <= now {
            same += 1;
            assert!(same < 10_000, "the driver stayed at one instant 10,000 turns");
        } else {
            same = 0;
            now = t;
        }
    }
    panic!("the driver loop ran 3,000,000 turns");
}

fn apply(s: &mut [Side<'_>; 2], op: &COp, now: u64, link: &mut Link, cut_until: &mut Option<u64>) {
    match *op {
        COp::Wait(_) => {},
        COp::Write { from, len } => {
            let x = &mut s[usize::from(from)];
            if let Ok(id) = x.conn.open_bi() {
                x.outs.push((id, len.max(1)));
            }
        },
        COp::Datagram { from, len } => {
            let _ = s[usize::from(from)].conn.send_datagram(&vec![3; len]);
        },
        COp::Ping(from) => s[usize::from(from)].conn.ping(),
        COp::Keepalive { from, ms } => s[usize::from(from)].conn.set_keepalive((ms > 0).then_some(ms * MS)),
        COp::LinkDown { from, down } => {
            let x = &mut s[usize::from(from)];
            x.conn.set_link_down(&mut env!(x, now), down);
        },
        COp::Sleep(from) => {
            let x = &mut s[usize::from(from)];
            x.conn.sleep(&mut env!(x, now));
        },
        COp::Wake(from) => {
            let x = &mut s[usize::from(from)];
            x.conn.wake(&mut env!(x, now));
        },
        COp::Probe(from) => {
            let x = &mut s[usize::from(from)];
            if x.path2 || x.conn.add_path(&mut env!(x, now), PathId(2), PathInfo::default()).is_ok() {
                x.path2 = true;
                let _ = x.conn.probe(&mut env!(x, now), PathId(2));
            }
        },
        COp::Close(from) => {
            let x = &mut s[usize::from(from)];
            x.conn.close(&mut env!(x, now), &mut Lent { spill: &mut x.spill }, 0);
        },
        COp::Cut(ms) => {
            link.cut = true;
            *cut_until = Some(now.saturating_add(ms * MS));
        },
        COp::Read { from, on } => s[usize::from(from)].reading = on,
    }
}
