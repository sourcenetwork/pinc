//! The flight of a dial: the candidate paths of its first flight and of each later try, the dial itself, and what the
//! answer to a lookup changes. The decisions per try are in [`super::dial`]; the sessions the layer follows and the
//! timers are in [`super::drive`].

use core::net::SocketAddr;

use vinc_core::{Command, CommandError, Role, SessionId, Value};
use vinc_crypto::{NodeId, Provider};

use super::conn::Connectivity;
use super::dial::{
    Cand, HUB_FIRST_ADDRS, HUB_RELAY_DELAY, HUB_RELAY_PATH_DELAY, RelayView, Try, direct_first, flight_relays, select,
};
use super::drive::{Port, Sess};
use super::punch::Puncher;

impl<P: Provider, const R: usize, const PEERS: usize> Connectivity<P, R, PEERS> {
    /// The candidate paths for a dial to `node`: its known UDP addresses, then the relay path.
    /// The paths a flight to `node` can take. With `fresh_at` set, the addresses of a record older than its time are
    /// left out: a dial looks such a peer up again and the flight goes through the relay, as for a peer with no record.
    pub(super) fn candidates_for(
        &mut self,
        node: &NodeId,
        hints: &[SocketAddr],
        fresh_at: Option<u64>,
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
        // The peer's own relay when the record named one, and ours (RELAY_FORWARD on the first flight).
        let peer = self
            .relay_of(node)
            .or_else(|| found.and_then(|f| self.relay_of(&f.home)))
            .and_then(|r| u8::try_from(r).ok());
        let own = self
            .home()
            .or_else(|| (0..R).find(|i| self.relay_cfg(*i).is_some()))
            .and_then(|r| u8::try_from(r).ok());
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
        let nc = self.candidates_for(&node, hints, Some(now), &mut cands);
        let hub = self.relay_of(&node);
        let direct = hub.is_some() && direct_first(true, true, first_dial, self.start);
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
        if na > 1 {
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
        };
        if let Some(s) = self.sess.iter_mut().find(|s| s.is_none()) {
            *s = Some(entry);
        }
        if hub.is_none() && self.found_fresh(now, &node).is_none() && hints.is_empty() {
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
        let Some(f) = self.found(peer) else { return };
        let mut cands = [Cand::Relay(0); 16];
        let nc = self.candidates_for(peer, &[], None, &mut cands);
        for id in waiting.into_iter().flatten() {
            let mut addrs = [self.me_addr_pub(); 16];
            let mut na = 0;
            for c in cands.get(..nc).unwrap_or_default() {
                let a = self.to_addr(c, peer);
                if let Some(s) = addrs.get_mut(na) {
                    *s = a;
                    na += 1;
                }
            }
            let _ = self.cmd(
                ep,
                now,
                Command::FlightPaths {
                    session: id,
                    addrs: addrs.get(..na).unwrap_or_default(),
                    skip_primary: false,
                },
            );
        }
        let _ = f;
    }

    /// Register every known path of the session's peer but its first one, and fan the flight out over them.
    pub(super) fn add_paths<E: Port>(&mut self, now: u64, ep: &mut E, s: &Sess) {
        let mut cands = [Cand::Relay(0); 16];
        let nc = self.candidates_for(&s.node, &[], None, &mut cands);
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
    pub(super) fn check_dial_carriers(&mut self, now: u64, node: &NodeId) {
        let mut cands = [Cand::Relay(0); 16];
        let nc = self.candidates_for(node, &[], None, &mut cands);
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
        let mut nc = self.candidates_for(&s.node, &[], None, &mut cands);
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
