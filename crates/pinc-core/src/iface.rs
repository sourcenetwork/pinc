//! Interfaces, link changes and suspension.
//!
//! The host names its local addresses with [`Endpoint::add_iface`] and reports what happens to them with
//! [`Endpoint::iface_event`]: a link going down or coming back maps to the transport's link down and link return,
//! an address change adds the new route to every session that used the old one and wakes the peer on it, and a
//! suspension puts every established session to sleep. On resume the sessions wake, with one exception: a node that
//! changed address while suspended, and a session that was already timing out when its SLEEP went out, cannot be woken
//! reliably, so those sessions close at once with `Redial` and the application dials again instead of waiting for an
//! answer that will not come.
//! A link that comes back also reaches the sessions still in their handshake: a dialing side sends its flight at once.
//! A node that lost its link and was suspended before the link came back is in doubt too: its sessions close at once
//! with `Redial` on resume.
//!
//! After any resume or link return no keepalive is sent for 10 s unless something is in flight.
//!
//! Invariants: an interface id names one local address while it lives; every event applies to the sessions whose
//! active path leaves from the interface, except a suspension, which applies to all.

use core::net::SocketAddr;

use pinc_transport::conn::PathId;

use crate::endpoint::{MAX_IFACES, env, ep_impl};
use crate::keepalive::RESUME_QUIET;
use crate::slot::State;
use crate::trace::trace;

/// The name of a local interface.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IfaceId(pub usize);

/// What happened to an interface.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IfaceEvent {
    /// The link came back.
    Up,
    /// The link went down.
    Down,
    /// The interface has a new local address.
    AddrChange(SocketAddr),
    /// The node is suspended.
    Suspend,
    /// The node resumed; `moved` says its address changed meanwhile.
    Resume {
        /// Whether the address changed while suspended.
        moved: bool,
    },
}

ep_impl! {
    /// Add a local interface and return its name, or `None` when the table is full.
    pub fn add_iface(&mut self, local: SocketAddr) -> Option<IfaceId> {
        let i = self.ifaces.iter().position(Option::is_none)?;
        *self.ifaces.get_mut(i)? = Some(local);
        Some(IfaceId(i))
    }

    /// Remove an interface. Sessions that used it keep their paths until the transport declares them failed.
    pub fn remove_iface(&mut self, id: IfaceId) {
        if let Some(s) = self.ifaces.get_mut(id.0) {
            *s = None;
        }
    }

    /// Apply an event of interface `id` at time `now`.
    pub fn iface_event(&mut self, now: u64, id: IfaceId, ev: IfaceEvent) {
        let Some(local) = self.ifaces.get(id.0).copied().flatten() else { return };
        match ev {
            IfaceEvent::Down => {
                self.dark = true;
                self.link(now, local, true);
            }
            IfaceEvent::Up => {
                // While suspended the link coming back changes nothing yet: the resume is the return.
                self.dark &= self.suspended;
                self.quiet_until = now.saturating_add(RESUME_QUIET);
                self.link(now, local, false);
            }
            IfaceEvent::AddrChange(new) => {
                self.dark &= self.suspended;
                self.addr_change(now, id.0, local, new);
            }
            IfaceEvent::Suspend => self.suspend(now),
            IfaceEvent::Resume { moved } => self.resume(now, moved),
        }
    }

    /// The link of the sessions that leave from `local` went down (`down`) or came back, those still in their
    /// handshake included.
    fn link(&mut self, now: u64, local: SocketAddr, down: bool) {
        for i in 0..K {
            if !self.leaves_from(i, &local, true) {
                continue;
            }
            if let Some(conn) = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()) {
                trace!(self, now, Iface { slot: i as u64, call: if down { 1 } else { 2 } });
                let mut env = env!(self, now);
                conn.set_link_down(&mut env, down);
            }
            self.settle(i, now);
        }
    }

    /// Whether session `i` is established (or, with `handshaking`, still in its handshake) and its active path leaves
    /// from `local`.
    fn leaves_from(&self, i: usize, local: &SocketAddr, handshaking: bool) -> bool {
        self.slots
            .get(i)
            .filter(|s| {
                s.m.in_use && (s.m.state == State::Established || (handshaking && s.m.state == State::Handshaking))
            })
            .and_then(|s| s.conn.as_ref())
            .and_then(pinc_transport::conn::Connection::active_path)
            .and_then(|p| self.path_addrs(p))
            .is_some_and(|(l, _)| l == *local)
    }

    fn addr_change(&mut self, now: u64, iface: usize, old: SocketAddr, new: SocketAddr) {
        if let Some(s) = self.ifaces.get_mut(iface) {
            *s = Some(new);
        }
        if self.suspended {
            self.moved = true;
        }
        self.quiet_until = now.saturating_add(RESUME_QUIET);
        for i in 0..K {
            let wake = self.leaves_from(i, &old, false);
            // Every path of the session that leaves from the old address moves to the new one, not only the active one: a
            // standby path left on it would be chosen again later and carry nothing.
            for j in 0..D {
                let Some(((l, remote), generation)) = self.paths.at_index(j).map(|(k, g)| (*k, *g)) else { continue };
                if l != old {
                    continue;
                }
                let lost = PathId(u64::from(generation) << 32 | j as u64);
                let held = self.slots.get(i).and_then(|s| s.conn.as_ref()).is_some_and(|c| c.has_path(lost));
                if !held {
                    continue;
                }
                let pid = self.path_id(new, remote);
                let Some(slot) = self.slots.get_mut(i) else { continue };
                let Some(conn) = slot.conn.as_mut() else { continue };
                if conn.rebind_path(lost, pid).is_ok() {
                    // The same path to the same peer address, now leaving from the new address: it keeps what it knows,
                    // and the stamp of what was sent and heard on it follows.
                    if let Some(st) = slot.m.paths.iter_mut().flatten().find(|st| st.id == lost) {
                        st.id = pid;
                    }
                    trace!(self, now, Iface { slot: i as u64, call: 6 });
                    continue;
                }
                // The session already tracks a path to this peer from the new address: the old one is gone, and the
                // session leaves it as soon as the new one validates.
                let mut env = env!(self, now);
                let _ = conn.add_path(&mut env, pid, crate::commands::path_info(&remote, self.cfg.conn.interface_mtu));
                let _ = conn.path_lost(lost);
                trace!(self, now, Iface { slot: i as u64, call: 7 });
            }
            if wake && let Some(conn) = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()) {
                // The link went away and came back on the new address: the peer is woken on the new path.
                trace!(self, now, Iface { slot: i as u64, call: 1 });
                trace!(self, now, Iface { slot: i as u64, call: 2 });
                let mut env = env!(self, now);
                conn.set_link_down(&mut env, true);
                conn.set_link_down(&mut env, false);
            }
            self.settle(i, now);
        }
    }

    /// Put every established session to sleep.
    pub(crate) fn suspend(&mut self, now: u64) {
        self.suspended = true;
        for i in 0..K {
            let Some(slot) = self.slots.get_mut(i) else { break };
            if !slot.m.in_use || slot.m.state != State::Established {
                continue;
            }
            let Some(conn) = slot.conn.as_mut() else { continue };
            slot.m.sleep_doubt = conn.recovery().pto_count() > 0 || self.dark;
            let mut env = env!(self, now);
            trace!(self, now, Iface { slot: i as u64, call: 3 });
            conn.sleep(&mut env);
            self.settle(i, now);
        }
    }

    /// Wake every session, except the ones that cannot be woken: they close for a redial.
    pub(crate) fn resume(&mut self, now: u64, moved: bool) {
        let moved = moved || self.moved;
        self.moved = false;
        self.suspended = false;
        self.dark = false;
        self.quiet_until = now.saturating_add(RESUME_QUIET);
        for i in 0..K {
            let Some(slot) = self.slots.get_mut(i) else { break };
            if !slot.m.in_use || slot.m.state != State::Established {
                continue;
            }
            if moved || slot.m.sleep_doubt {
                slot.m.sleep_doubt = false;
                #[cfg(feature = "trace")]
                {
                    if slot.conn.is_some() {
                        trace!(self, now, Iface { slot: i as u64, call: 5 });
                    }
                }
                self.redial(i, now);
                continue;
            }
            if let Some(conn) = slot.conn.as_mut() {
                trace!(self, now, Iface { slot: i as u64, call: 4 });
                let mut env = env!(self, now);
                conn.wake(&mut env);
            }
            self.settle(i, now);
        }
    }

    /// The local address interface `id` names, if any.
    #[cfg(feature = "trace")]
    pub fn trace_iface(&self, id: usize) -> Option<SocketAddr> {
        self.ifaces.get(id).copied().flatten()
    }

    /// The node's flags: lost its link (dark), suspended, moved while suspended, and the time keepalives stay quiet
    /// until.
    #[cfg(feature = "trace")]
    pub const fn trace_iface_flags(&self) -> (bool, bool, bool, u64) {
        (self.dark, self.suspended, self.moved, self.quiet_until)
    }

    /// Session slot `i`: its state (0 free, 1 handshaking, 2 established, 3 closing; 0 when not in use), its
    /// generation, its sleep doubt, whether a probe timeout runs (`pto_count() > 0`; false without a connection) and
    /// the addresses of its active path (None without one).
    #[cfg(feature = "trace")]
    #[allow(clippy::type_complexity, reason = "a probe for the trace test, read as one tuple")]
    pub fn trace_iface_slot(&self, i: usize) -> Option<(u8, u32, bool, bool, Option<(SocketAddr, SocketAddr)>)> {
        let s = self.slots.get(i)?;
        let state = match (s.m.in_use, s.m.state) {
            (false, _) => 0,
            (true, State::Handshaking) => 1,
            (true, State::Established) => 2,
            (true, State::Closing) => 3,
        };
        let conn = s.conn.as_ref();
        Some((
            state,
            s.m.generation,
            s.m.sleep_doubt,
            conn.is_some_and(|c| c.recovery().pto_count() > 0),
            conn.and_then(pinc_transport::conn::Connection::active_path)
                .and_then(|p| self.path_addrs(p)),
        ))
    }

    /// The addresses of every path the connection of slot `i` holds: each entry `j` of the path table whose id
    /// (`generation << 32 | j`) the connection has (`has_path`), in table order.
    #[cfg(feature = "trace")]
    pub fn trace_slot_paths(&self, i: usize) -> impl Iterator<Item = (SocketAddr, SocketAddr)> + '_ {
        let conn = self.slots.get(i).and_then(|s| s.conn.as_ref());
        (0..D).filter_map(move |j| {
            let (key, generation) = self.paths.at_index(j)?;
            let id = PathId(u64::from(*generation) << 32 | j as u64);
            conn.is_some_and(|c| c.has_path(id)).then_some(*key)
        })
    }
}

const _: () = assert!(MAX_IFACES >= 1);
