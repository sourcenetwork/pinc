//! Reproductions of `pinc-broadcast` bugs found by the property tests in `broadcast_world.rs`.

use std::collections::{BTreeSet, VecDeque};

use pinc_broadcast::{Config, Event, Host, IdKey, Lane, Limits, Topics};
use pinc_crypto::{IdentityAlg, Keypair};
use pinc_membership::NodeId;

const SEC: u64 = 1_000_000_000;
const WALL0: u64 = 1_700_000_000_000;
const NODES: usize = 4;
const HUBS: usize = 2;
const ORIGIN: usize = 2;
const MEMBER: usize = 3;
const TOPIC: &[u8] = b"t0";
const FLOOR: u8 = pinc_broadcast::wire::ty::FLOOR;

static SECRETS: [u64; 7] = [1, 2, 3, 4, 5, 6, 7];

#[derive(Default)]
struct H {
    out: Vec<(NodeId, Vec<u8>)>,
    delivered: Vec<[u8; 8]>,
    acp: Vec<u32>,
    reach: BTreeSet<NodeId>,
    hubs: BTreeSet<NodeId>,
    wall: u64,
}

impl Host for H {
    fn send(&mut self, peer: &NodeId, _lane: Lane, frame: &[u8]) -> bool {
        if !self.reach.contains(peer) {
            return false;
        }
        self.out.push((*peer, frame.to_vec()));
        true
    }

    fn send_member(&mut self, peer: &NodeId, frame: &[u8]) -> bool {
        if !self.reach.contains(peer) {
            return false;
        }
        self.out.push((*peer, frame.to_vec()));
        true
    }

    fn hub_up(&self, hub: &NodeId) -> bool {
        self.hubs.contains(hub)
    }

    fn in_view(&self, _member: &NodeId) -> bool {
        true
    }

    fn wall_ms(&self) -> u64 {
        self.wall
    }

    fn event(&mut self, event: Event<'_>) {
        match event {
            Event::Message { mid, .. } => self.delivered.push(mid),
            Event::AcpCheck { id, .. } => self.acp.push(id),
            _ => {},
        }
    }
}

fn keypair(i: usize) -> Keypair {
    Keypair::from_seed(IdentityAlg::Ed25519, &[u8::try_from(i + 1).unwrap_or(1); 32]).expect("a 32-byte seed")
}

/// Hubs 0 and 1, an origin member and the member that restarts, all sessions up, frames carried in order.
struct Net {
    now: u64,
    ids: Vec<NodeId>,
    t: Vec<Topics>,
    h: Vec<H>,
    q: VecDeque<(usize, usize, Vec<u8>)>,
}

impl Net {
    fn start(ids: &[NodeId], i: usize, now: u64, life: u64) -> Topics {
        let cfg = Config {
            me: ids[i],
            is_hub: i < HUBS,
            hubs: &ids[..HUBS],
            incarnation: ((WALL0 + now / 1_000_000 + 1) << 16) | life,
            trace: false,
            limits: Limits::default(),
            map_keys: IdKey::new(0x5eed + i as u64, &SECRETS).expect("a usable key"),
        };
        Topics::start(&cfg, Box::new(keypair(i)), now, WALL0 + now / 1_000_000).expect("a valid configuration")
    }

    fn new() -> Self {
        let ids: Vec<NodeId> = (0..NODES).map(|i| keypair(i).node_id().bytes).collect();
        let t = (0..NODES).map(|i| Self::start(&ids, i, 0, 0)).collect();
        let h = (0..NODES)
            .map(|i| H {
                reach: ids.iter().copied().filter(|x| *x != ids[i]).collect(),
                hubs: ids[..HUBS].iter().copied().collect(),
                wall: WALL0,
                ..H::default()
            })
            .collect();
        Self { now: 0, ids, t, h, q: VecDeque::new() }
    }

    fn flush(&mut self, i: usize) {
        for _ in 0..1000 {
            for (to, f) in std::mem::take(&mut self.h[i].out) {
                let j = self.ids.iter().position(|x| *x == to).unwrap_or(0);
                self.q.push_back((i, j, f));
            }
            let acp = std::mem::take(&mut self.h[i].acp);
            if acp.is_empty() {
                return;
            }
            for id in acp {
                self.t[i].acp_answer(&mut self.h[i], self.now, id, true);
            }
        }
    }

    fn settle(&mut self) {
        for _ in 0..100_000 {
            let Some((a, b, f)) = self.q.pop_front() else { return };
            let tl = usize::from(f[5]);
            let from = self.ids[a];
            self.h[b].wall = WALL0 + self.now / 1_000_000;
            self.t[b].frame(&mut self.h[b], self.now, &from, f[4], &f[6..6 + tl], &f[6 + tl..]);
            self.flush(b);
        }
        panic!("the network does not settle");
    }

    fn run(&mut self, dt: u64) {
        let end = self.now + dt;
        for _ in 0..100_000 {
            self.settle();
            match self.t.iter().filter_map(Topics::poll_timeout).min() {
                Some(x) if x <= end => {
                    self.now = self.now.max(x);
                    for i in 0..NODES {
                        if self.t[i].poll_timeout().is_some_and(|x| x <= self.now) {
                            self.h[i].wall = WALL0 + self.now / 1_000_000;
                            self.t[i].on_timer(&mut self.h[i], self.now);
                            self.flush(i);
                        }
                    }
                },
                _ => {
                    self.now = end;
                    return;
                },
            }
        }
        panic!("the timers do not end");
    }

    /// The FLOOR frame hub `j` writes for member `m`, as membership sends it on an attachment.
    fn floor_frame(&mut self, j: usize, m: usize) -> Vec<u8> {
        let mut body = vec![0u8; 65_536];
        let n = self.t[j].floor(&self.ids[m], &mut body);
        let mut f = u32::try_from(2 + n).unwrap_or(0).to_be_bytes().to_vec();
        f.extend_from_slice(&[FLOOR, 0]);
        f.extend_from_slice(&body[..n]);
        f
    }

    fn attach(&mut self, m: usize, hostile: bool) {
        for j in 0..HUBS {
            let mut f = self.floor_frame(j, m);
            if hostile && j == 1 {
                // One bit of the topic length byte: the frame now names a one-byte topic and the floor that follows
                // starts one byte late.
                f[5] ^= 1;
            }
            self.q.push_back((j, m, f));
        }
        let hub = self.ids[0];
        self.t[m].primary_changed(&mut self.h[m], self.now, None, &hub);
        self.flush(m);
        self.settle();
    }

    fn subscribe(&mut self, m: usize) {
        self.h[m].wall = WALL0 + self.now / 1_000_000;
        assert!(self.t[m].subscribe(&mut self.h[m], self.now, TOPIC).is_ok());
        self.flush(m);
        self.settle();
    }

    fn publish(&mut self, body: &[u8]) -> [u8; 8] {
        self.h[ORIGIN].wall = WALL0 + self.now / 1_000_000;
        let mid = self.t[ORIGIN].publish(&mut self.h[ORIGIN], self.now, TOPIC, body).expect("a publish");
        self.flush(ORIGIN);
        self.settle();
        mid
    }

    /// The member delivers a message, restarts, gets the FLOOR frames of both hubs (hub 1's with one bit of its topic length
    /// changed when `hostile`), and the origin publishes again after the floor wait. Whether the member delivers it.
    fn restart_and_publish(hostile: bool) -> bool {
        let mut n = Self::new();
        for m in [ORIGIN, MEMBER] {
            n.attach(m, false);
        }
        n.subscribe(MEMBER);
        n.run(2 * SEC);
        let first = n.publish(b"before the restart");
        n.run(5 * SEC);
        assert!(n.h[MEMBER].delivered.contains(&first), "the member did not deliver the first message");
        n.run(5 * SEC);
        n.t[MEMBER] = Self::start(&n.ids, MEMBER, n.now, 1);
        n.h[MEMBER].delivered.clear();
        let me = n.ids[MEMBER];
        for j in 0..HUBS {
            n.t[j].release(&mut n.h[j], &me);
            n.flush(j);
        }
        n.attach(MEMBER, hostile);
        n.subscribe(MEMBER);
        n.run(20 * SEC);
        let second = n.publish(b"after the restart");
        n.run(60 * SEC);
        n.h[MEMBER].delivered.contains(&second)
    }
}

/// The honest run of [`one_hub_with_a_future_floor_silences_a_restarted_member_for_every_origin`]: the member
/// delivers the message published after its restart.
#[test]
fn a_restarted_member_delivers_a_fresh_message_when_both_hubs_report_honest_floors() {
    assert!(Net::restart_and_publish(false));
}

/// Expected: a restarted member still delivers a message published after its restart while one hub is honest.
/// Source: the crate documentation, "A restarted member gathers the replay floors of the hubs for up to 15 s and
/// holds messages meanwhile", `docs/proofs/properties.md`, replay floors: "after a restart nothing at or below the
/// floors is redelivered" (a floor is what an earlier life was sent), and the doc of `floors.rs`: "A hub remembers
/// the newest timestamp it ever sent to each member ... and reports them in the FLOOR frame".
///
/// Actual: hub 1's FLOOR frame has one bit of its topic length byte flipped (the frame names a one-byte topic). The
/// member's `on_floor` (`crates/pinc-broadcast/src/floors.rs:160-186`) ignores the topic and reads the floor one
/// byte late: a wall time 256 times the real one (some ten thousand years ahead), no per-origin list. With one hub
/// lacking a list, `floor_settle` (`floors.rs:219-225`) takes the hub-wide floor as the maximum over the hubs, and
/// `is_old` (`floors.rs:283`) drops every later message of every origin as already delivered, through the honest
/// hub too. The message published 20 s after the restart is never delivered (the world test waited a further 60 s).
/// Two faults combine: a FLOOR frame `Topics::floor` never writes (non-empty topic) is taken, and a floor beyond any
/// clock in the network is not bounded by the member's own clock or by the other hub's report.
///
/// Who can trigger it: one authenticated hub, by a FLOOR frame on its membership stream; it silences each member
/// that restarts and attaches to it, for every origin and topic, despite the other hubs being honest.
#[test]
fn one_hub_with_a_future_floor_silences_a_restarted_member_for_every_origin() {
    assert!(Net::restart_and_publish(true), "the restarted member never delivered the message published after its restart");
}
