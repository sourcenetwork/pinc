//! The flight of a dial: the candidate paths of its first flight and of each later try, the dial itself, and what the
//! answer to a lookup changes. The decisions per try are in [`super::dial`]; the sessions the layer follows and the
//! timers are in [`super::drive`].

use core::net::SocketAddr;

use pinc_core::{Command, CommandError, Role, SessionId, Value};
use pinc_crypto::{NodeId, Provider};

use super::conn::Connectivity;
use super::dial::{
    Cand, HUB_FIRST_ADDRS, HUB_RELAY_DELAY, HUB_RELAY_PATH_DELAY, RelayView, Try, direct_first, flight_relays, select,
};
use super::drive::{Port, Sess};
use super::punch::Puncher;

impl<P: Provider, const R: usize, const PEERS: usize> Connectivity<P, R, PEERS> {
    /// The paths a flight to `node` can take, in this order: the caller's hints, the addresses of the peer's beacon,
    /// the addresses of its record, the peer's relay, then (`fwd`) our home relay. At most 16 paths are kept, so 16
    /// addresses push the relay paths out. With `fresh_at` set, the addresses of a record older than its time are
    /// left out: a dial looks such a peer up again and the flight goes through the relay, as for a peer with no record.
    pub(super) fn candidates_for(
        &mut self,
        node: &NodeId,
        hints: &[SocketAddr],
        fresh_at: Option<u64>,
        fwd: bool,
        out: &mut [Cand; 16],
    ) -> usize {
        let mut n = 0;
        let add = |c: Cand, out: &mut [Cand; 16], n: &mut usize| {
            if *n < out.len()
                && !out.get(..*n).unwrap_or_default().contains(&c)
                && let Some(s) = out.get_mut(*n)
            {
                *s = c;
                *n += 1;
            }
        };
        for a in hints {
            add(Cand::Udp(*a), out, &mut n);
        }
        if let Some(lp) = self.beacons.iter().flatten().find(|b| b.node == *node) {
            for a in lp.addrs.iter().flatten() {
                add(Cand::Udp(*a), out, &mut n);
            }
        }
        let found = self.found(node);
        if let Some(f) = found.filter(|_| fresh_at.is_none_or(|t| self.found_fresh(t, node).is_some())) {
            for a in f.addrs() {
                add(Cand::Udp(a), out, &mut n);
            }
        }
        // The peer's own relay when the record named one, and ours only for a dial that started without a usable
        // record (RELAY_FWD: `fwd`, kept until the session is established).
        let peer = self
            .relay_of(node)
            .or_else(|| found.and_then(|f| self.relay_of(&f.home)))
            .and_then(|r| u8::try_from(r).ok());
        let own = self.home().filter(|_| fwd).and_then(|r| u8::try_from(r).ok());
        for r in flight_relays(peer, own).into_iter().flatten() {
            add(Cand::Relay(r), out, &mut n);
        }
        n
    }

    pub(super) fn to_addr(&mut self, c: &Cand, node: &NodeId) -> SocketAddr {
        match c {
            Cand::Udp(a) => *a,
            Cand::Relay(r) => self.path_addr(usize::from(*r), node),
        }
    }

    /// Dial `node` for `alpn`. `hints` are addresses the caller already knows (a ticket, a record). A peer with no
    /// known address is looked up while the first flight goes through the home relay.
    ///
    /// # Errors
    /// The endpoint's refusal.
    pub fn dial<E: Port>(
        &mut self,
        now: u64,
        ep: &mut E,
        node: NodeId,
        alpn: &[u8],
        role: Role,
        hints: &[SocketAddr],
    ) -> Result<SessionId, CommandError> {
        let first = self.first_dial.is_none();
        let first_dial = *self.first_dial.get_or_insert(now);
        let mut cands = [Cand::Relay(0); 16];
        let hub = self.relay_of(&node);
        let no_record = hub.is_none() && self.found_fresh(now, &node).is_none();
        let lookup = no_record && hints.is_empty();
        // RELAY_FWD: a dial that started without a usable record also flies through our home relay; with no home yet
        // and a lookup to wait for (some relay to ask) it flies nowhere until the answer arrives.
        let fwd = no_record && self.home().is_some();
        let withheld = lookup && self.home().is_none() && self.has_relays();
        let nc = if withheld {
            0
        } else {
            self.candidates_for(&node, hints, Some(now), fwd, &mut cands)
        };
        let direct = hub.is_some() && direct_first(true, true, self.shared.restarted, first_dial, self.start);
        let mut chosen = [Cand::Relay(0); 16];
        let list: &[Cand] = cands.get(..nc).unwrap_or_default();
        let (m, carried) = if direct {
            // B8: a hub's first flight goes to its known UDP address only; the relay copy joins at the first resend.
            let mut k = 0;
            for c in list.iter().filter(|c| matches!(c, Cand::Udp(_))).take(HUB_FIRST_ADDRS) {
                if let Some(s) = chosen.get_mut(k) {
                    *s = *c;
                    k += 1;
                }
            }
            (k, None)
        } else {
            let t = Try {
                now,
                dialer: true,
                tries: 1,
                link_rtt: self.net.best_rtt(),
                no_rtt: self.node_rtt == 0,
                hs0: false,
                last_relay: None,
            };
            select(
                list,
                &t,
                |r| {
                    Some(RelayView {
                        live: self.relay_live(usize::from(r)),
                        generation: self.generation(usize::from(r)),
                    })
                },
                &mut chosen,
            )
        };
        let _ = first;
        let m = if m == 0 {
            let _ = (&mut chosen, list);
            0
        } else {
            m
        };
        let mut addrs = [self.me_addr_pub(); 16];
        let mut na = 0;
        for c in chosen.get(..m).unwrap_or_default() {
            let a = self.to_addr(c, &node);
            if let Some(s) = addrs.get_mut(na) {
                *s = a;
                na += 1;
            }
        }
        if na == 0 {
            // The session needs a path to be created on; a dial that flies nowhere yet keeps it unused.
            let first = self.home().or_else(|| (0..R).find(|i| self.relay_cfg(*i).is_some()));
            if let Some(r) = first.and_then(|r| u8::try_from(r).ok()) {
                let a = self.to_addr(&Cand::Relay(r), &node);
                if let Some(d) = addrs.get_mut(0) {
                    *d = a;
                    na = 1;
                }
            }
        }
        let primary = addrs.first().copied();
        let rep = self.cmd(
            ep,
            now,
            Command::Connect {
                node,
                alpn,
                addrs: addrs.get(..na.min(1)).unwrap_or_default(),
                role,
            },
        )?;
        let Value::Session(id) = rep.value else {
            return Err(CommandError::NoSession);
        };
        if withheld {
            let _ = self.cmd(
                ep,
                now,
                Command::FlightPaths {
                    session: id,
                    addrs: &[],
                    skip_primary: true,
                },
            );
        } else if na > 1 {
            let _ = self.cmd(
                ep,
                now,
                Command::FlightPaths {
                    session: id,
                    addrs: addrs.get(1..na).unwrap_or_default(),
                    skip_primary: false,
                },
            );
        }
        let mut relay_at = None;
        let mut readd_at = None;
        if direct {
            let _ = self.cmd(
                ep,
                now,
                Command::FirstResend {
                    session: id,
                    delay: HUB_RELAY_DELAY,
                },
            );
            relay_at = Some(now.saturating_add(HUB_RELAY_DELAY));
            readd_at = Some(now.saturating_add(HUB_RELAY_PATH_DELAY));
        }
        let entry = Sess {
            id,
            node,
            hub,
            dialed: now,
            punch: Puncher::off(),
            handshaking: true,
            tries: 1,
            relay_at,
            readd_at,
            pulse_on: false,
            last_relay: carried.map(|(r, g)| (r, g, now)),
            primary,
            relay_route: false,
            held: false,
            fwd,
            withheld,
        };
        if let Some(s) = self.sess.iter_mut().find(|s| s.is_none()) {
            *s = Some(entry);
        }
        if lookup {
            self.pending.add(node, id);
            self.lookup(now, &node);
        }
        Ok(id)
    }

    /// The node has no round trip of any kind yet (no address-discovery answer, no handshake average or
    /// peak, none remembered for `peer`).
    pub(super) fn heard_nothing<E: Port>(&self, ep: &E, peer: &NodeId) -> bool {
        self.net.best_rtt() == 0 && self.node_rtt == 0 && ep.peer(peer).is_none()
    }

    pub(super) fn found_dial<E: Port>(&mut self, now: u64, ep: &mut E, peer: &NodeId) {
        let waiting = self.pending.take(peer);
        if self.found(peer).is_none() {
            return;
        }
        for id in waiting.into_iter().flatten() {
            let Some(s) = self.sess.iter().flatten().find(|s| s.id == id).copied() else {
                continue;
            };
            let mut cands = [Cand::Relay(0); 16];
            let nc = self.candidates_for(peer, &[], None, s.fwd, &mut cands);
            let mut addrs = [self.me_addr_pub(); 16];
            let mut na = 0;
            for c in cands.get(..nc).unwrap_or_default() {
                let a = self.to_addr(c, peer);
                if let Some(d) = addrs.get_mut(na) {
                    *d = a;
                    na += 1;
                }
            }
            let list = addrs.get(..na).unwrap_or_default();
            // A flight that was withheld leaves now, and only on the paths the answer named.
            let skip_primary = s.withheld && s.primary.is_some_and(|p| !list.contains(&p));
            let _ = self.cmd(
                ep,
                now,
                Command::FlightPaths {
                    session: id,
                    addrs: list,
                    skip_primary,
                },
            );
            if s.withheld {
                let _ = self.cmd(ep, now, Command::FirstResend { session: id, delay: 0 });
                if let Some(x) = self.sess_mut(id) {
                    x.withheld = false;
                }
            }
        }
    }

    /// Register every known path of the session's peer but its first one, and fan the flight out over them.
    pub(super) fn add_paths<E: Port>(&mut self, now: u64, ep: &mut E, s: &Sess) {
        let mut cands = [Cand::Relay(0); 16];
        let nc = self.candidates_for(&s.node, &[], None, s.fwd, &mut cands);
        let mut addrs = [self.me_addr_pub(); 16];
        let mut na = 0;
        for c in cands.get(..nc).unwrap_or_default() {
            let a = self.to_addr(c, &s.node);
            if Some(a) != s.primary
                && let Some(d) = addrs.get_mut(na)
            {
                *d = a;
                na += 1;
            }
        }
        let _ = self.cmd(
            ep,
            now,
            Command::FlightPaths {
                session: s.id,
                addrs: addrs.get(..na).unwrap_or_default(),
                skip_primary: false,
            },
        );
    }

    /// From its third try on, a handshake that has not been answered checks the carriers it could ride: the relays
    /// among the peer's candidate paths and the home relay. A carrier that died without a close is found and dialed
    /// again at once, not at its keepalive.
    pub(super) fn check_dial_carriers(&mut self, now: u64, node: &NodeId, fwd: bool) {
        let mut cands = [Cand::Relay(0); 16];
        let nc = self.candidates_for(node, &[], None, fwd, &mut cands);
        for c in cands.get(..nc).unwrap_or_default() {
            if let Cand::Relay(r) = c {
                self.check_carrier(now, usize::from(*r));
            }
        }
        if let Some(h) = self.net.home() {
            self.check_carrier(now, h);
        }
    }

    pub(super) fn reselect<E: Port>(&mut self, now: u64, ep: &mut E, s: &mut Sess) {
        let mut cands = [Cand::Relay(0); 16];
        let mut nc = self.candidates_for(&s.node, &[], None, s.fwd, &mut cands);
        // A peer with no record and no relay is dialed at the address the caller gave: a retry keeps to it.
        if nc == 0
            && let Some(p) = s.primary
            && let Some(c) = cands.first_mut()
        {
            *c = Cand::Udp(p);
            nc = 1;
        }
        let t = Try {
            now,
            dialer: true,
            tries: s.tries,
            link_rtt: self.net.best_rtt(),
            no_rtt: self.node_rtt == 0,
            hs0: super::dial::hs0(
                s.hub.is_some(),
                s.tries,
                now.saturating_sub(s.dialed),
                self.heard_nothing(ep, &s.node),
            ),
            last_relay: s.last_relay,
        };
        let mut chosen = [Cand::Relay(0); 16];
        let (m, carried) = select(
            cands.get(..nc).unwrap_or_default(),
            &t,
            |r| {
                Some(RelayView {
                    live: self.relay_live(usize::from(r)),
                    generation: self.generation(usize::from(r)),
                })
            },
            &mut chosen,
        );
        if let Some((r, g)) = carried {
            s.last_relay = Some((r, g, now));
        }
        let mut addrs = [self.me_addr_pub(); 16];
        let mut na = 0;
        let mut primary_kept = false;
        for c in chosen.get(..m).unwrap_or_default() {
            let a = self.to_addr(c, &s.node);
            if Some(a) == s.primary {
                primary_kept = true;
            } else if let Some(d) = addrs.get_mut(na) {
                *d = a;
                na += 1;
            }
        }
        // THIN_HS: a try that does not include the primary path leaves it out of the flight.
        let skip_primary = s.primary.is_some() && !primary_kept;
        let _ = self.cmd(
            ep,
            now,
            Command::FlightPaths {
                session: s.id,
                addrs: addrs.get(..na).unwrap_or_default(),
                skip_primary,
            },
        );
    }
}

/// What one call of `candidates_for` read and built, for the trace test.
#[cfg(feature = "trace")]
#[derive(Debug, Clone, Copy)]
pub struct FlightProbe {
    /// The addresses of the local beacon heard from the node, or `None` when none was heard.
    pub beacon: Option<[Option<SocketAddr>; crate::local::MAX_ADDRS]>,
    /// The addresses of the record found for the node, or `None` when none was found.
    pub record: Option<[Option<SocketAddr>; crate::record::MAX_ADDRS]>,
    /// `fresh_at` is `None`, or the record is fresh at it.
    pub fresh: bool,
    /// `relay_of(node)`.
    pub peer_relay: Option<usize>,
    /// `relay_of` of the found record's home, whether or not the record is fresh.
    pub home_relay: Option<usize>,
    /// `home()`.
    pub home: Option<usize>,
    /// The candidates `candidates_for` wrote, `out[..n]`.
    pub out: [Cand; 16],
    /// How many it wrote.
    pub n: usize,
}

#[cfg(feature = "trace")]
impl<P: Provider, const R: usize, const PEERS: usize> Connectivity<P, R, PEERS> {
    /// Call `candidates_for` and report the tables it read, for the trace test.
    pub fn trace_candidates(
        &mut self,
        node: &NodeId,
        hints: &[SocketAddr],
        fresh_at: Option<u64>,
        fwd: bool,
    ) -> FlightProbe {
        let beacon = self.beacons.iter().flatten().find(|b| b.node == *node).map(|b| b.addrs);
        let found = self.found(node);
        let record = found.map(|f| {
            let mut addrs = [None; crate::record::MAX_ADDRS];
            for (d, a) in addrs.iter_mut().zip(f.addrs()) {
                *d = Some(a);
            }
            addrs
        });
        let fresh = fresh_at.is_none_or(|t| self.found_fresh(t, node).is_some());
        let peer_relay = self.relay_of(node);
        let home_relay = found.and_then(|f| self.relay_of(&f.home));
        let home = self.home();
        let mut out = [Cand::Relay(0); 16];
        let n = self.candidates_for(node, hints, fresh_at, fwd, &mut out);
        FlightProbe {
            beacon,
            record,
            fresh,
            peer_relay,
            home_relay,
            home,
            out,
            n,
        }
    }
}
