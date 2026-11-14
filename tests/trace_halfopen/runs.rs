//! The runs of the half-open trace: the big endpoint (floors, the cap, a resumption at the cap, replays, a close and the
//! lifetime) and the small one (a full slot table, no protocol, a stalled queue, a clock that steps back).

use vinc_core::{Command, CommandError, MAX_DATAGRAM, Role};
use vinc_security::message::{FULL_INITIAL_MIN, SHORT_INITIAL_MIN};
use vinc_tests::*;

use crate::common::{LIFE, MAX, SK, craft, floor, kind_of, source};
use crate::duo::{Duo, pick_time};
use crate::rec::{Rec, Seen};

/// The big endpoint: floors, the cap, a resumption at the cap, replays, a close and the lifetime.
pub fn big_run(run: u32, seed: u64) -> (String, String, Seen) {
    let mut rng = SplitMix64::new(seed);
    let mut d = Duo::new(run);
    let mut id = u64::from(run) << 32;
    let mut next = || {
        id += 1;
        id
    };
    // floors and types around their edges
    for (kind, len) in [
        (1, FULL_INITIAL_MIN - 1),
        (1, FULL_INITIAL_MIN),
        (1, FULL_INITIAL_MIN + 1),
        (2, SHORT_INITIAL_MIN - 1),
        (2, SHORT_INITIAL_MIN),
        (2, SHORT_INITIAL_MIN + 1),
        (6, 40),
        (6, 300),
        (3, 1300),
        (4, 1300),
        (5, 1300),
        (7, 1300),
        (8, 1300),
        (9, 1300),
    ] {
        d.forge(next(), kind, len);
        d.drive(MS_NS);
    }
    let now = d.net.now;
    let i = next();
    d.r.dgram(now, source(i), craft(i, 1, 1300, 600, 1), None);
    d.r.dgram(now, source(1), vec![0x40; 50], None);
    d.r.dgram(now, source(2), Vec::new(), None);
    d.r.dgram(now, source(3), vec![0xC0; MAX_DATAGRAM + 1], None);
    // no protocol registered: the cap admits, no session is made
    d.r.ep.unregister_alpn(ALPN_A);
    d.forge(next(), 1, FULL_INITIAL_MIN);
    assert!(d.r.ep.register_alpn(ALPN_A));
    d.drive(MS_NS);
    // a full handshake whose first message is damaged on the way: the dialer's repeat gets a session beside the one it made;
    // the dialer then holds a ticket
    d.damage = true;
    let s = d.dial(3 * SEC_NS);
    d.reverse = false;
    d.hang_up(s);
    // a close of a half-open session: it counts until it is freed
    let open = d.r.unauth();
    let (i, _) = open[0];
    let sid = d.r.session_at(i).unwrap();
    let now = d.net.now;
    d.r.command(now, Command::Close { session: sid, error: 0 }).unwrap();
    // the flood, at staggered times, past the cap
    let mut extra = 0;
    while extra < 40 {
        let kind = [1u8, 2, 6][(rng.next_u64() % 3) as usize];
        let f = floor(kind).unwrap();
        let len = match rng.next_u64() % 8 {
            0 => f.max(40),
            1 => f.saturating_sub(1).max(40),
            2 => 1200 + (rng.next_u64() % 100) as usize,
            _ => f.max(40) + (rng.next_u64() % 300) as usize,
        };
        d.forge(next(), kind, len);
        extra += u32::from(d.r.ep.node_stats().half_open == MAX);
        let gap = rng.next_u64() % 25;
        d.drive(gap * MS_NS);
    }
    // a genuine resumption while the table is full, then replays of its Hello and a forged binder
    let mark = d.net.captured.len();
    let s = d.dial(300 * MS_NS);
    let hello = d.net.captured[mark..]
        .iter()
        .find(|c| c.1 == d.r.addr)
        .unwrap()
        .2
        .clone();
    assert_eq!(kind_of(&hello), 6, "the second dial is a resumption");
    d.hang_up(s);
    for k in 0..5u64 {
        let now = d.net.now;
        d.r.dgram(now, source(5000 + k), hello.clone(), Some(false));
        d.drive(MS_NS);
    }
    let mut forged = hello;
    *forged.last_mut().unwrap() ^= 1;
    let now = d.net.now;
    d.r.dgram(now, source(6000), forged, Some(false));
    // the lifetime: timers at the host's deadline, just before, at and after the ends, new first flights between
    let mut now = d.net.now;
    let mut rounds = 0;
    while (!d.r.unauth().is_empty() || rounds < 40) && rounds < 4000 {
        rounds += 1;
        let t = pick_time(&d.r, &mut rng, now).max(now);
        d.step_to(t);
        now = d.net.now;
        if rng.next_u64().is_multiple_of(5) {
            let kind = [1u8, 2, 6][(rng.next_u64() % 3) as usize];
            d.forge(next(), kind, floor(kind).unwrap().max(40));
        }
    }
    assert!(d.r.unauth().is_empty(), "sessions outlived the run");
    let Rec { ms, ns, seen, .. } = d.r;
    (ms, ns, seen)
}

/// Fill the event queue without reading it: each dial to this node itself fails at once with an event.
pub fn stall<const K: usize, const D: usize>(r: &mut Rec<K, D>, now: u64) {
    let me = r.ep.identity().node_id();
    for _ in 0..100_000 {
        let c = Command::Connect {
            node: me,
            alpn: ALPN_A,
            addrs: &[],
            role: Role::Other,
        };
        match r.command(now, c) {
            Err(CommandError::Refused) => {}
            Err(CommandError::EventsPending) => return,
            other => panic!("unexpected {other:?}"),
        }
    }
    panic!("the queue never stalled");
}

/// The small endpoint: a full slot table, no protocol, a stalled queue, and a clock that steps back.
pub fn small_run(run: u32, seed: u64) -> (String, String, Seen) {
    let mut rng = SplitMix64::new(seed);
    let mut now = 50 * SEC_NS + (rng.next_u64() % 1000) * MS_NS;
    let mut r: Rec<SK, { SK * 10 }> = Rec::new(now, run);
    let mut id = u64::from(run) << 32;
    let mut forge = |r: &mut Rec<SK, { SK * 10 }>, now: u64, kind: u8, len: usize| {
        id += 1;
        r.dgram(
            now,
            source(id),
            craft(id, kind, len, 0, id as u8),
            (kind == 6).then_some(false),
        );
    };
    for _ in 0..(SK + 3) {
        let kind = [1u8, 2, 6][(rng.next_u64() % 3) as usize];
        let f = floor(kind).unwrap();
        let len = if rng.next_u64().is_multiple_of(4) {
            f.saturating_sub(1).max(40)
        } else {
            f.max(40)
        };
        forge(&mut r, now, kind, len);
        now += MS_NS * (rng.next_u64() % 400);
        r.tick(now);
    }
    r.ep.unregister_alpn(ALPN_A);
    forge(&mut r, now, 2, SHORT_INITIAL_MIN);
    assert!(r.ep.register_alpn(ALPN_A));
    // a stalled queue: no session starts, no timer runs, no deadline is given
    if run.is_multiple_of(2) {
        stall(&mut r, now);
        forge(&mut r, now, 1, FULL_INITIAL_MIN);
        r.timer(now + LIFE + SEC_NS);
        r.drain(now);
    }
    // the lifetime, with a clock that sometimes steps back
    let mut rounds = 0;
    while !r.unauth().is_empty() && rounds < 400 {
        rounds += 1;
        let mut t = pick_time(&r, &mut rng, now).max(now);
        if rng.next_u64().is_multiple_of(7) {
            t = now.saturating_sub(MS_NS * (rng.next_u64() % 3000));
        }
        now = t;
        r.timer(now);
        if rng.next_u64().is_multiple_of(4) {
            let kind = [1u8, 2, 6][(rng.next_u64() % 3) as usize];
            forge(&mut r, now, kind, floor(kind).unwrap().max(40));
        }
    }
    let t = r
        .unauth()
        .iter()
        .map(|(_, s)| s.created + LIFE)
        .max()
        .unwrap_or(now)
        .max(now);
    r.timer(t);
    assert!(r.unauth().is_empty(), "sessions outlived the run");
    let Rec { ms, ns, seen, .. } = r;
    (ms, ns, seen)
}
