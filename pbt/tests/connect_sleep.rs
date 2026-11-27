//! `pinc-connect` relay role: sleep notices, the suspension they mark and the mailbox they open, on the state machine
//! of a node that carries the relay role (the same on an ordinary node and on one deployed from the relay binary),
//! driven by carriers that open and close, notices (fresh or replayed, on the carrier or over UDP), packets from
//! another member and time passing with the host's timer.
//!
//! Where the expected behaviour comes from:
//! - `relay::sleep`: "a notice counts only if its clock is within [`SKEW_MS`] of the relay's, its sender holds a
//!   carrier here or just lost one, and its signature verifies; an accepted notice means that the carrier close which
//!   follows is a suspension, not a crash. A notice is sent twice (lossy mobile uplinks); the second changes nothing."
//! - `relay::clients`: "When a carrier closes the node becomes \"gone\" with the time; if its sleep notice came within
//!   [`rule::SLEEP_WIN_NS`] before, the close is a suspension, not a crash"; `rule::GONE_TTL_NS`: "A node that lost
//!   its carrier stays known as gone this long."
//! - `relay::route`, rule 4: "`dst` is asleep (its sleep notice is held and it has no carrier): the packet goes into
//!   the mailbox and the host is asked to wake the member"; rule 1 delivers on the member's carrier.
//! - `mailbox`: "A relay that holds a member's sleep notice keeps the packets addressed to that member here, up to a
//!   byte quota per member and a maximum age, and hands them over when the member returns"; "A message is delivered
//!   at most once"; "Messages leave in the order they arrived"; the maximum age is `mailbox_max_age_ns` (one day by
//!   default). No document gives the held notice a shorter life than the mailbox it opens, so the model keeps it
//!   until the member returns (every run here is shorter than a day); a failure that only that reading explains is
//!   reported under its own signature.

use ephyra::prelude::*;
use pinc_connect::carrier::Frame;
use pinc_connect::relay::{Config, Effect, NodeState, Relay, SessionId, Sink, Trace, rule, sleep};
use pinc_crypto::{IdentityAlg, Keypair, NodeId};

const MS: u64 = 1_000_000;
const SEC: u64 = 1_000_000_000;
const T0: u64 = 1_700_000_000 * SEC;
/// The members that may sleep.
const N: usize = 3;

type R = Relay<8, 8, 8, 16_384>;

fn keypair(seed: u8) -> Keypair {
    Keypair::from_seed(IdentityAlg::Ed25519, &[seed; 32]).expect("a seed makes a key")
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Op {
    /// Time passes, then the host runs the relay's timer.
    Time(#[ephyra(gen = dt())] u64),
    /// Member `i` opens a carrier (if it has none).
    Open(#[ephyra(gen = gens::int(0usize..N))] usize),
    /// Member `i`'s carrier closes (if it has one).
    Close(#[ephyra(gen = gens::int(0usize..N))] usize),
    /// Member `i` sends a fresh notice, on its carrier if it has one, else over UDP.
    Notice(#[ephyra(gen = gens::int(0usize..N))] usize),
    /// A copy of the `k`th notice member `i` sent arrives again over UDP (the second copy, or a replay).
    Replay(
        #[ephyra(gen = gens::int(0usize..N))] usize,
        #[ephyra(gen = gens::int(0usize..=7))] usize,
    ),
    /// The other member sends a packet of this length to member `i`.
    Send(
        #[ephyra(gen = gens::int(0usize..N))] usize,
        #[ephyra(gen = gens::int(1usize..=64))] usize,
    ),
}

fn dt() -> ephyra::BoxGen<u64> {
    gens::frequency(vec![
        (
            4,
            gens::pick_from(vec![
                0,
                MS,
                SEC,
                5 * SEC,
                9 * SEC,
                10 * SEC,
                11 * SEC,
                30 * SEC,
                300 * SEC,
                600 * SEC,
                700 * SEC,
            ])
            .boxed(),
        ),
        (2, gens::int(0u64..=700 * SEC).boxed()),
    ])
    .boxed()
}

#[derive(Default)]
struct Seen {
    /// Packets handed to a member's carrier, in order.
    delivered: Vec<(NodeId, Vec<u8>)>,
    woken: Vec<NodeId>,
    closes: Vec<(NodeId, bool)>,
}

impl Sink for Seen {
    fn emit(&mut self, e: Effect<'_>) {
        match e {
            Effect::Carrier { to, frame } => {
                if let Some(p) = frame.packet() {
                    self.delivered.push((to, p.to_vec()));
                }
            }
            Effect::Wake { node } => self.woken.push(node),
            Effect::Trace(Trace::CarrierClosed { node, asleep }) => self.closes.push((node, asleep)),
            _ => {}
        }
    }
}

/// The model of one member.
#[derive(Clone, Default)]
struct Member {
    session: Option<SessionId>,
    /// When the carrier closed, while the node is known as gone.
    gone: Option<u64>,
    /// The held notice: when it was first accepted, and its clock.
    mark: Option<(u64, u64)>,
    /// Packets held for it, in order.
    held: Vec<Vec<u8>>,
    /// The notices it sent: clock and bytes.
    notices: Vec<(u64, Vec<u8>)>,
}

fn run(ops: &[Op]) {
    let day = 86_400_000_000_000u64;
    let me = keypair(10);
    let members: Vec<Keypair> = (1..=N).map(|i| keypair(u8::try_from(i).unwrap_or(1))).collect();
    let ids: Vec<NodeId> = members.iter().map(Keypair::node_id).collect();
    let other = keypair(20).node_id();
    let mut relay: Box<R> = Box::new(Relay::new(Config::new(me.node_id(), 7)));
    let mut now = T0;
    let mut sink = Seen::default();
    let sender = relay
        .carrier_opened(now, other, &mut sink)
        .expect("the other member opens a carrier");
    let mut m: Vec<Member> = vec![Member::default(); N];
    let mut last_sweep = 0u64;
    let mut counter = 0u32;
    for (step, op) in ops.iter().enumerate() {
        let mut seen = Seen::default();
        match *op {
            Op::Time(d) => {
                now += d;
                relay.handle_timeout(now, &mut seen);
                if now.saturating_sub(last_sweep) >= rule::SWEEP_NS {
                    last_sweep = now;
                    for x in &mut m {
                        if x.gone.is_some_and(|g| now - g >= rule::GONE_TTL_NS) {
                            x.gone = None;
                        }
                        if x.mark.is_some_and(|(at, _)| now - at >= day) {
                            x.mark = None;
                            x.held.clear();
                        }
                    }
                }
            }
            Op::Open(i) => {
                if m[i].session.is_some() {
                    continue;
                }
                let sid = relay
                    .carrier_opened(now, ids[i], &mut seen)
                    .expect("a member opens a carrier");
                let want: Vec<(NodeId, Vec<u8>)> = m[i].held.drain(..).map(|p| (ids[i], p)).collect();
                assert_eq!(
                    seen.delivered, want,
                    "step {step}: the held packets are handed over once, in order"
                );
                assert_eq!(
                    relay.mailbox_pending(&ids[i]).0,
                    0,
                    "step {step}: nothing stays held for a member back"
                );
                m[i] = Member {
                    session: Some(sid),
                    notices: std::mem::take(&mut m[i].notices),
                    ..Member::default()
                };
            }
            Op::Close(i) => {
                let Some(sid) = m[i].session else { continue };
                relay.carrier_closed(now, &ids[i], sid, &mut seen);
                let asleep = m[i]
                    .mark
                    .is_some_and(|(at, _)| at >= now.saturating_sub(rule::SLEEP_WIN_NS));
                assert_eq!(
                    seen.closes,
                    vec![(ids[i], asleep)],
                    "step {step}: the close is a suspension exactly after a notice"
                );
                assert_eq!(
                    relay.node_state(&ids[i]),
                    NodeState::Gone { since: now, asleep },
                    "step {step}: the node is gone"
                );
                m[i].session = None;
                m[i].gone = Some(now);
            }
            Op::Notice(i) | Op::Replay(i, _) => {
                let (ts, bytes, replay) = match *op {
                    Op::Replay(_, k) => match m[i].notices.get(k % m[i].notices.len().max(1)) {
                        Some((ts, b)) => (*ts, b.clone(), true),
                        None => continue,
                    },
                    _ => {
                        let ts = now / MS;
                        let mut b = vec![0u8; sleep::MAX_LEN];
                        let n = sleep::sign(&members[i], &me.node_id(), ts, &mut b).expect("a notice signs");
                        b.truncate(n);
                        m[i].notices.push((ts, b.clone()));
                        (ts, b, false)
                    }
                };
                let on_carrier = !replay && m[i].session.is_some();
                let r = match (on_carrier, m[i].session) {
                    (true, Some(sid)) => {
                        relay.carrier_frame(now, &ids[i], sid, &Frame::Sleep { notice: &bytes }, &mut seen)
                    }
                    _ => relay.sleep_notice(now, &bytes, None, &mut seen),
                };
                let accept =
                    (now / MS).abs_diff(ts) < sleep::SKEW_MS && (m[i].session.is_some() || m[i].gone.is_some());
                assert_eq!(
                    r.is_ok(),
                    accept,
                    "step {step}: the notice (replay {replay}) is taken: {r:?}"
                );
                if accept {
                    if m[i].mark.is_none_or(|(at, t)| t != ts || now - at >= day) {
                        m[i].mark = Some((now, ts));
                    }
                }
            }
            Op::Send(i, len) => {
                counter += 1;
                let mut packet = vec![0x40u8; len.max(5)];
                packet[1..5].copy_from_slice(&counter.to_be_bytes());
                let f = Frame::Send {
                    dst: ids[i],
                    flag: 0,
                    packet: &packet,
                };
                let r = relay.carrier_frame(now, &other, sender, &f, &mut seen);
                let to_i: Vec<Vec<u8>> = seen
                    .delivered
                    .iter()
                    .filter(|(to, _)| *to == ids[i])
                    .map(|(_, p)| p.clone())
                    .collect();
                if m[i].session.is_some() {
                    assert_eq!(
                        to_i,
                        vec![packet.clone()],
                        "step {step}: a packet to an open member is on its carrier"
                    );
                } else if let Some((at, _)) = m[i].mark.filter(|(at, _)| now - at < day) {
                    let held = relay.mailbox_pending(&ids[i]).0;
                    if held != m[i].held.len() + 1 {
                        let long = now - at >= rule::GONE_TTL_NS;
                        ephyra::signature(format!(
                            "not held for a member asleep {} 600 s",
                            if long { "over" } else { "under" }
                        ));
                    }
                    assert!(
                        r.is_ok(),
                        "step {step}: a packet for a sleeping member is refused: {r:?}"
                    );
                    assert_eq!(
                        held,
                        m[i].held.len() + 1,
                        "step {step}: a packet for a sleeping member is held"
                    );
                    if m[i].held.is_empty() {
                        assert!(
                            seen.woken.contains(&ids[i]),
                            "step {step}: the first held packet wakes the member"
                        );
                    }
                    assert!(
                        to_i.is_empty(),
                        "step {step}: a packet for a sleeping member went to a carrier"
                    );
                    m[i].held.push(packet);
                } else {
                    assert!(
                        to_i.is_empty(),
                        "step {step}: a packet for an absent member went to a carrier"
                    );
                    assert_eq!(
                        relay.mailbox_pending(&ids[i]).0,
                        m[i].held.len(),
                        "step {step}: held without a notice"
                    );
                }
            }
        }
        let wrong: Vec<&(NodeId, Vec<u8>)> = seen
            .delivered
            .iter()
            .filter(|(to, _)| *to != other && !ids.contains(to))
            .collect();
        assert!(
            wrong.is_empty(),
            "step {step}: a packet went to a node that is no member"
        );
    }
}

#[ephyra::test(gen = gens::vec(ephyra::any::<Op>()).len(1..=50), tests = 3000)]
fn a_sleeping_member_is_suspended_and_its_packets_held_until_it_returns(ops: Vec<Op>) {
    run(&ops);
}
