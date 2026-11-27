//! The sleep mark of a member: its time, its life and what it holds, through the relay's public calls.

#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::expect_used,
    reason = "tests assert"
)]

use alloc::vec::Vec;
use core::mem::size_of;

use pinc_crypto::{IdentityAlg, Keypair, NodeId};

use super::sleep;
use super::table::Table;
use super::{Config, Effect, Reject, Relay, SessionId, Sink, Sleeper, Trace};
use crate::carrier::Frame;

const SEC: u64 = 1_000_000_000;
const T0: u64 = 1_000_000 * SEC;
const DAY: u64 = 86_400 * SEC;

type R = Relay<2, 2, 2, 256>;

#[derive(Default)]
struct Rec {
    traces: Vec<Trace>,
    wakes: Vec<NodeId>,
}

impl Sink for Rec {
    fn emit(&mut self, e: Effect<'_>) {
        match e {
            Effect::Trace(t) => self.traces.push(t),
            Effect::Wake { node } => self.wakes.push(node),
            _ => {}
        }
    }
}

impl Rec {
    fn count(&self, t: Trace) -> usize {
        self.traces.iter().filter(|x| **x == t).count()
    }
}

fn key(seed: u8) -> Keypair {
    Keypair::from_seed(IdentityAlg::Ed25519, &[seed; 32]).unwrap()
}

struct Fx {
    me: Keypair,
    r: R,
    rec: Rec,
}

impl Fx {
    fn new() -> Self {
        let me = key(10);
        Self {
            r: Relay::new(Config::new(me.node_id(), 7)),
            me,
            rec: Rec::default(),
        }
    }

    fn open(&mut self, now: u64, k: &Keypair) -> SessionId {
        self.r.carrier_opened(now, k.node_id(), &mut self.rec).unwrap()
    }

    fn close(&mut self, now: u64, k: &Keypair, sid: SessionId) {
        self.r.carrier_closed(now, &k.node_id(), sid, &mut self.rec);
    }

    /// `k`'s notice with the clock `ts_ms` reaches the relay at `now` over UDP.
    fn notice(&mut self, now: u64, k: &Keypair, ts_ms: u64) -> Result<(), Reject> {
        let mut b = [0u8; sleep::MAX_LEN];
        let n = sleep::sign(k, &self.me.node_id(), ts_ms, &mut b).unwrap();
        self.r.sleep_notice(now, &b[..n], None, &mut self.rec)
    }

    /// `from` sends a packet to `to` at `now`.
    fn send(&mut self, now: u64, from: &Keypair, sid: SessionId, to: &Keypair) -> Result<(), Reject> {
        let f = Frame::Send {
            dst: to.node_id(),
            flag: 0,
            packet: &[0x40, 1, 2, 3, 4, 5],
        };
        self.r.carrier_frame(now, &from.node_id(), sid, &f, &mut self.rec)
    }

    fn woke(&self, k: &Keypair) -> u64 {
        self.r.sleeping.get(&k.node_id()).unwrap().woke
    }
}

const fn ms(now: u64) -> u64 {
    now / 1_000_000
}

#[test]
fn a_copy_of_a_notice_changes_nothing_and_another_clock_moves_the_mark() {
    let (mut f, a, o) = (Fx::new(), key(1), key(2));
    let sa = f.open(T0, &a);
    let so = f.open(T0, &o);
    f.notice(T0, &a, ms(T0)).unwrap();
    f.close(T0 + SEC, &a, sa);
    f.send(T0 + 2 * SEC, &o, so, &a).unwrap();
    let woke = f.woke(&a);
    assert_ne!(woke, 0);
    let accepted = Trace::SleepAccepted { node: a.node_id() };
    assert_eq!(f.rec.count(accepted), 1);
    // the copy 9 s later keeps the time and the wake mark and is not traced
    f.notice(T0 + 9 * SEC, &a, ms(T0)).unwrap();
    assert_eq!(f.r.sleeper(&a.node_id()), Some((T0, ms(T0))));
    assert_eq!(f.woke(&a), woke);
    assert_eq!(f.rec.count(accepted), 1);
    // a notice with another clock moves the mark and keeps the wake mark
    f.notice(T0 + 9 * SEC, &a, ms(T0) + 1).unwrap();
    assert_eq!(f.r.sleeper(&a.node_id()), Some((T0 + 9 * SEC, ms(T0) + 1)));
    assert_eq!(f.woke(&a), woke);
    assert_eq!(f.rec.count(accepted), 2);
}

#[test]
fn a_copy_after_the_mark_ended_sets_a_new_mark() {
    let (mut f, a) = (Fx::new(), key(1));
    let _ = f.open(T0, &a);
    f.notice(T0, &a, ms(T0)).unwrap();
    // the member returns: the mark ends, once
    let sb = f.open(T0 + SEC, &a);
    assert_eq!(f.r.sleeper(&a.node_id()), None);
    f.close(T0 + 2 * SEC, &a, sb);
    f.notice(T0 + 3 * SEC, &a, ms(T0)).unwrap();
    assert_eq!(f.r.sleeper(&a.node_id()), Some((T0 + 3 * SEC, ms(T0))));
}

#[test]
fn a_mark_is_live_up_to_the_mailbox_age_and_not_at_it() {
    let (mut f, a, o) = (Fx::new(), key(1), key(2));
    let sa = f.open(T0, &a);
    let so = f.open(T0, &o);
    f.notice(T0, &a, ms(T0)).unwrap();
    f.close(T0 + SEC, &a, sa);
    // the exact instant is decided at routing, the sweep has not run
    f.send(T0 + DAY - 1, &o, so, &a).unwrap();
    assert_eq!(f.r.mailbox_pending(&a.node_id()).0, 1);
    assert_eq!(f.rec.wakes, [a.node_id()]);
    assert_eq!(f.send(T0 + DAY, &o, so, &a), Err(Reject::NoRoute));
    assert_eq!(f.r.mailbox_pending(&a.node_id()).0, 1);
}

#[test]
fn a_mark_and_the_mail_held_under_it_end_together_at_the_sweep() {
    let (mut f, a, o) = (Fx::new(), key(1), key(2));
    let sa = f.open(T0, &a);
    let so = f.open(T0, &o);
    f.notice(T0, &a, ms(T0)).unwrap();
    f.close(T0 + SEC, &a, sa);
    f.send(T0 + 2 * SEC, &o, so, &a).unwrap();
    f.send(T0 + 3 * SEC, &o, so, &a).unwrap();
    // the member's own gone entry ends at 600 s and leaves the mark and the mail
    f.r.handle_timeout(T0 + 601 * SEC, &mut f.rec);
    assert_eq!(f.r.node_state(&a.node_id()), super::NodeState::Unknown);
    assert_eq!(f.r.sleeper(&a.node_id()), Some((T0, ms(T0))));
    assert_eq!(f.r.mailbox_pending(&a.node_id()).0, 2);
    // the sweep at the end of the mark's life clears both, and counts the mail as expired
    f.r.handle_timeout(T0 + DAY, &mut f.rec);
    assert_eq!(f.r.sleeper(&a.node_id()), None);
    assert_eq!(f.r.mailbox_pending(&a.node_id()).0, 0);
    assert_eq!(f.r.mailbox.stats().expired, 2);
}

#[test]
fn a_mark_that_ends_by_the_return_is_traced_once_and_its_mail_stays() {
    let (mut f, a, o) = (Fx::new(), key(1), key(2));
    let sa = f.open(T0, &a);
    let so = f.open(T0, &o);
    f.notice(T0, &a, ms(T0)).unwrap();
    f.close(T0 + SEC, &a, sa);
    f.send(T0 + 2 * SEC, &o, so, &a).unwrap();
    let ended = Trace::SleepEnded { node: a.node_id() };
    f.r.member_returned(T0 + 3 * SEC, &a.node_id(), &mut f.rec);
    assert_eq!(f.r.sleeper(&a.node_id()), None);
    assert_eq!(f.rec.count(ended), 1);
    f.r.member_returned(T0 + 4 * SEC, &a.node_id(), &mut f.rec);
    assert_eq!(f.rec.count(ended), 1, "a node with no mark ends none");
    // a carrier that opens for a member with a mark ends it, after the Opened trace
    f.notice(T0 + 5 * SEC, &a, ms(T0 + 5 * SEC)).unwrap();
    f.rec.traces.clear();
    let sa2 = f.open(T0 + 6 * SEC, &a);
    let opened = f
        .rec
        .traces
        .iter()
        .position(|t| matches!(t, Trace::CarrierOpened { .. }))
        .unwrap();
    assert_eq!(f.rec.traces.get(opened + 1), Some(&ended));
    // and one with none ends nothing
    f.close(T0 + 7 * SEC, &a, sa2);
    f.rec.traces.clear();
    let _ = f.open(T0 + 8 * SEC, &key(3));
    assert_eq!(f.rec.count(ended), 0);
}

#[test]
fn a_restored_mark_keeps_its_time_and_ends_at_the_boundary() {
    let (mut f, a) = (Fx::new(), key(1));
    let now = T0 + DAY;
    assert_eq!(f.r.restore_sleep(now, &a.node_id(), T0, 5), Err(Reject::MailboxRefused));
    assert_eq!(f.r.sleeper(&a.node_id()), None);
    assert_eq!(f.r.restore_sleep(now - 1, &a.node_id(), T0, 5), Ok(()));
    assert_eq!(f.r.sleeper(&a.node_id()), Some((T0, 5)));
    // a mark restored first is kept by the packets restored after it
    let src = key(2).node_id();
    f.r.restore_held(now - 1, T0 + SEC, &a.node_id(), &src, 0, &[0x40; 8])
        .unwrap();
    f.r.restore_held(now - 1, T0 + 2 * SEC, &a.node_id(), &src, 0, &[0x40; 8])
        .unwrap();
    assert_eq!(f.r.sleeper(&a.node_id()), Some((T0, 5)));
}

#[test]
fn restored_mail_with_no_mark_marks_the_member_at_its_oldest_packet() {
    let (mut f, a, o) = (Fx::new(), key(1), key(2));
    let src = o.node_id();
    let now = T0 + 30 * SEC;
    f.r.restore_held(now, T0 + SEC, &a.node_id(), &src, 0, &[0x40; 8])
        .unwrap();
    f.r.restore_held(now, T0 + 2 * SEC, &a.node_id(), &src, 0, &[0x40; 8])
        .unwrap();
    assert_eq!(f.r.sleeper(&a.node_id()), Some((T0 + SEC, u64::MAX)));
    // the next packet for the member is held and asks for a wake-up
    let so = f.open(now, &o);
    f.send(now + SEC, &o, so, &a).unwrap();
    assert_eq!(f.r.mailbox_pending(&a.node_id()).0, 3);
    assert_eq!(f.rec.wakes, [a.node_id()]);
    // a packet that expired is refused and marks nothing
    assert_eq!(
        f.r.restore_held(T0 + DAY + 2 * SEC, T0, &key(3).node_id(), &src, 0, &[0x40; 8]),
        Err(Reject::MailboxRefused)
    );
    assert_eq!(f.r.sleeper(&key(3).node_id()), None);
}

#[test]
fn a_full_mark_table_drops_the_oldest_mark_with_no_mail_and_refuses_when_all_hold_mail() {
    let (mut f, o) = (Fx::new(), key(9));
    let ks = [key(1), key(2), key(3)];
    for (i, k) in ks.iter().take(2).enumerate() {
        let at = T0 + i as u64 * SEC;
        let s = f.open(at, k);
        f.notice(at, k, ms(at)).unwrap();
        f.close(at + 1, k, s);
    }
    // the table is full: a third mark takes the place of the oldest one
    let at = T0 + 5 * SEC;
    let s3 = f.open(at, &ks[2]);
    f.notice(at, &ks[2], ms(at)).unwrap();
    assert_eq!(f.r.sleeper(&ks[0].node_id()), None);
    assert!(f.r.sleeper(&ks[1].node_id()).is_some() && f.r.sleeper(&ks[2].node_id()).is_some());
    // the mark that went is traced as ended, once, before the new one is accepted, and counted
    let ended = Trace::SleepEnded { node: ks[0].node_id() };
    assert_eq!(f.rec.count(ended), 1);
    assert_eq!(f.r.stats().marks_evicted, 1);
    let at_ended = f.rec.traces.iter().position(|t| *t == ended).unwrap();
    let at_new = f
        .rec
        .traces
        .iter()
        .position(|t| *t == Trace::SleepAccepted { node: ks[2].node_id() })
        .unwrap();
    assert!(at_ended < at_new);
    // both marks now hold mail: a new member's notice is refused
    f.close(at + SEC, &ks[2], s3);
    let so = f.open(at + 2 * SEC, &o);
    f.send(at + 3 * SEC, &o, so, &ks[1]).unwrap();
    f.send(at + 3 * SEC, &o, so, &ks[2]).unwrap();
    let k4 = key(4);
    let at = at + 4 * SEC;
    let _ = f.open(at, &k4);
    assert_eq!(f.notice(at, &k4, ms(at)), Err(Reject::SessionsFull));
    assert_eq!(f.r.sleeper(&k4.node_id()), None);
}

#[test]
fn a_mark_beyond_the_clock_ends_one_mailbox_age_after_the_restore_with_its_mail() {
    let (mut f, a) = (Fx::new(), key(1));
    let (now, src) = (T0, key(2).node_id());
    assert_eq!(f.r.restore_sleep(now, &a.node_id(), u64::MAX, 5), Ok(()));
    assert_eq!(f.r.sleeper(&a.node_id()), Some((now, 5)));
    f.r.restore_held(now, now, &a.node_id(), &src, 0, &[0x40; 8]).unwrap();
    f.r.handle_timeout(now + DAY - SEC, &mut f.rec);
    assert!(f.r.sleeper(&a.node_id()).is_some());
    f.r.handle_timeout(now + DAY, &mut f.rec);
    assert_eq!(f.r.sleeper(&a.node_id()), None);
    assert_eq!(f.r.mailbox_pending(&a.node_id()).0, 0);
    // the mark a packet from the future derives is bounded the same way
    let b = key(3);
    f.r.restore_held(now + DAY, now + DAY + 1, &b.node_id(), &src, 0, &[0x40; 8])
        .unwrap();
    assert_eq!(f.r.sleeper(&b.node_id()), Some((now + DAY, u64::MAX)));
}

#[test]
fn a_notice_after_a_derived_mark_sets_a_new_mark_even_with_clock_zero() {
    let (mut f, a) = (Fx::new(), key(1));
    let src = key(2).node_id();
    let ms1 = 1_000_000;
    let s = f.open(ms1, &a);
    f.close(2 * ms1, &a, s);
    let now = 10 * ms1;
    f.r.restore_held(now, 5 * ms1, &a.node_id(), &src, 0, &[0x40; 8])
        .unwrap();
    assert_eq!(f.r.sleeper(&a.node_id()), Some((5 * ms1, u64::MAX)));
    f.notice(now, &a, 0).unwrap();
    assert_eq!(f.r.sleeper(&a.node_id()), Some((now, 0)));
}

#[test]
fn a_restore_with_no_room_for_a_mark_holds_no_mail_and_evicts_nothing() {
    let (mut f, src) = (Fx::new(), key(9).node_id());
    let ks = [key(1), key(2), key(3), key(4)];
    for k in &ks[..2] {
        assert_eq!(f.r.restore_sleep(T0, &k.node_id(), T0, 5), Ok(()));
    }
    let c = ks[2].node_id();
    assert_eq!(f.r.restore_sleep(T0, &c, T0, 5), Err(Reject::SessionsFull));
    assert_eq!(
        f.r.restore_held(T0, T0, &c, &src, 0, &[0x40; 8]),
        Err(Reject::SessionsFull)
    );
    assert_eq!((f.r.sleeper(&c), f.r.mailbox_pending(&c).0), (None, 0));
    assert!(ks[..2].iter().all(|k| f.r.sleeper(&k.node_id()).is_some()));
    assert_eq!(f.r.stats().marks_evicted, 0);
    // a packet the mailbox refuses leaves no mark behind
    let mut g = Fx::new();
    assert_eq!(
        g.r.restore_held(T0, T0, &ks[3].node_id(), &src, 0, &[]),
        Err(Reject::MailboxRefused)
    );
    assert_eq!(g.r.sleeper(&ks[3].node_id()), None);
}

#[test]
fn the_mark_table_holds_exactly_its_capacity_of_64_byte_slots() {
    assert_eq!(size_of::<Sleeper>(), 24);
    assert_eq!(size_of::<Option<(NodeId, Sleeper)>>(), 64);
    let mut t = Table::<Sleeper, 1024>::new(7);
    let s = Sleeper {
        at: 0,
        ts_ms: 0,
        woke: 0,
    };
    for i in 0u16..1024 {
        let mut bytes = [0u8; 32];
        bytes[..2].copy_from_slice(&i.to_be_bytes());
        let id = NodeId {
            alg: IdentityAlg::Ed25519,
            bytes,
        };
        assert!(t.insert(id, s).is_ok(), "slot {i}");
    }
    assert!(t.is_full());
    // 1024 slots of 64 bytes: the 64 KiB the sleep marks cost at the default capacity
    assert_eq!(t.len() * size_of::<Option<(NodeId, Sleeper)>>(), 65_536);
    // the table itself: the slots plus its header words (the slice's pointer and length with `alloc`, none inline;
    // the count and the seed in both), so a field added to the table shows here
    #[cfg(feature = "alloc")]
    assert_eq!(size_of::<Table<Sleeper, 1024>>(), 32);
    #[cfg(not(feature = "alloc"))]
    assert_eq!(size_of::<Table<Sleeper, 1024>>(), 65_536 + 16);
}
