//! The big endpoint of the half-open trace beside one dialer on a simulated network, joined by hand, and the choice of
//! the times to run the timers at.

use vinc_core::{Command, Event, Role, SessionId};
use vinc_security::{KeyHandle, LocalIdentity};
use vinc_tests::*;
use vinc_transport::packet::LongHeader;
use vinc_wire::Reader;

use crate::common::{BK, LIFE, craft, kind_of, source};
use crate::rec::Rec;

/// A time to run the timers at, as a host with a millisecond clock might: its next deadline, the moment before, at
/// or after the end of a random unauthenticated session, or a little later than now.
pub fn pick_time<const K: usize, const D: usize>(r: &Rec<K, D>, rng: &mut SplitMix64, now: u64) -> u64 {
    let open = r.unauth();
    match rng.next_u64() % 6 {
        0 | 1 if !open.is_empty() => {
            let (_, s) = open[(rng.next_u64() % open.len() as u64) as usize];
            let end = s.created + LIFE;
            match rng.next_u64() % 3 {
                0 => end - MS_NS,
                1 => end,
                _ => end + MS_NS * (rng.next_u64() % 50),
            }
        }
        2 | 3 => r.ep.poll_timeout().map_or(now + SEC_NS, |t| t.div_ceil(MS_NS) * MS_NS),
        _ => now + MS_NS * (rng.next_u64() % 4000),
    }
}

/// The big endpoint beside one dialer on a `CoreNet`, joined by hand: the dialer's datagrams to the endpoint's
/// address go in through the recorder, the endpoint's go back.
pub struct Duo {
    pub net: CoreNet,
    pub r: Rec<BK, { BK * 10 }>,
    pub taken: usize,
    /// Damage the next first message the dialer sends, as a path that flips a bit would.
    pub damage: bool,
    /// Deliver what the dialer sent in one tick in reverse.
    pub reverse: bool,
}

/// Flip a bit of the message a first flight starts, 20 bytes into it.
pub fn damage(d: &mut [u8]) {
    let (_, hlen) = LongHeader::parse(d).unwrap();
    let mut r = Reader::new(&d[hlen..]);
    r.read_varint().unwrap();
    r.read_varint().unwrap();
    let at = hlen + r.position() + 20;
    d[at] ^= 1;
}

impl Duo {
    pub fn new(run: u32) -> Self {
        let mut net = CoreNet::new(MS_NS);
        net.add(2);
        net.capture = true;
        let r = Rec::new(net.now, run);
        Self {
            net,
            r,
            taken: 0,
            damage: false,
            reverse: false,
        }
    }

    /// Move the clock to `t` (a whole millisecond) and hand over what the dialer sent meanwhile.
    pub fn step_to(&mut self, t: u64) {
        if t > self.net.now {
            self.net.run_for(t - self.net.now);
        }
        let now = self.net.now;
        let mut batch = Vec::new();
        while let Some((from, to, mut d)) = self.net.captured.get(self.taken).cloned() {
            self.taken += 1;
            if to == self.r.addr {
                if self.damage && matches!(kind_of(&d), 1 | 2) {
                    self.damage = false;
                    self.reverse = true;
                    damage(&mut d);
                }
                batch.push((from, d));
            }
        }
        if self.reverse && batch.len() > 1 {
            // after the damage, what arrives together arrives in reverse, so the start of a repeated first message
            // is what completes it
            batch.reverse();
        }
        for (from, d) in batch {
            self.r.dgram(now, from, d, None);
        }
        self.r.tick(now);
        for (local, remote, d) in self.r.transmit(now) {
            self.net.inject(local, remote, d, 0);
        }
    }

    pub fn drive(&mut self, span: u64) {
        for _ in 0..span / MS_NS {
            let t = self.net.now + MS_NS;
            self.step_to(t);
        }
    }

    pub fn dial(&mut self, span: u64) -> SessionId {
        let id = LocalIdentity::from_keypair(&self.r.host.kp, KeyHandle(1)).unwrap();
        let (now, to) = (self.net.now, self.r.addr);
        let n0 = self.net.nodes[0].count(|e| matches!(e, Event::Connected { .. }));
        let rep = self.net.nodes[0]
            .connect(now, id.node_id(), ALPN_A, to, Role::Other)
            .unwrap();
        self.drive(span);
        assert_eq!(
            self.net.nodes[0].count(|e| matches!(e, Event::Connected { .. })),
            n0 + 1,
            "no session"
        );
        self.net.nodes[0].session(&rep)
    }

    pub fn hang_up(&mut self, session: SessionId) {
        let now = self.net.now;
        self.net.nodes[0]
            .cmd(now, Command::Close { session, error: 0 })
            .unwrap();
        self.drive(2 * SEC_NS);
    }

    /// A crafted first flight from a fresh address at the current time.
    pub fn forge(&mut self, odcid: u64, kind: u8, len: usize) {
        let now = self.net.now;
        self.r.dgram(
            now,
            source(odcid),
            craft(odcid, kind, len, 0, odcid as u8),
            (kind == 6).then_some(false),
        );
    }
}
