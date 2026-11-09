//! Interfaces, link changes and suspension.
//!
//! The host names its local addresses with [`Endpoint::add_iface`] and reports what happens to them with
//! [`Endpoint::iface_event`]: a link going down or coming back maps to the transport's link down and link return,
//! an address change adds the new route to every session that used the old one and wakes the peer on it, and a
//! suspension puts every established session to sleep. On resume the sessions wake, with one exception: a node that
//! changed address while suspended, and a session that was already timing out when its SLEEP went out, cannot be woken
//! reliably, so those sessions close at once with `Redial` and the application dials again instead of waiting for an
//! answer that will not come.
//!
//! After any resume or link return no keepalive is sent for 10 s unless something is in flight.
//!
//! Invariants: an interface id names one local address while it lives; every event applies to the sessions whose
//! active path leaves from the interface, except a suspension, which applies to all.

use core::net::SocketAddr;

use crate::endpoint::{MAX_IFACES, env, ep_impl};
use crate::keepalive::RESUME_QUIET;
use crate::slot::State;

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
            IfaceEvent::Down => self.link(now, local, true),
            IfaceEvent::Up => {
                self.quiet_until = now.saturating_add(RESUME_QUIET);
                self.link(now, local, false);
            }
            IfaceEvent::AddrChange(new) => self.addr_change(now, id.0, local, new),
            IfaceEvent::Suspend => self.suspend(now),
            IfaceEvent::Resume { moved } => self.resume(now, moved),
        }
    }

    /// The link of the sessions that leave from `local` went down (`down`) or came back.
    fn link(&mut self, now: u64, local: SocketAddr, down: bool) {
        for i in 0..K {
            if !self.leaves_from(i, &local) {
                continue;
            }
            if let Some(conn) = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()) {
                let mut env = env!(self, now);
                conn.set_link_down(&mut env, down);
            }
            self.settle(i, now);
        }
    }

    /// Whether session `i` is live and its active path leaves from `local`.
    fn leaves_from(&self, i: usize, local: &SocketAddr) -> bool {
        self.slots
            .get(i)
            .filter(|s| s.m.in_use && s.m.state == State::Established)
            .and_then(|s| s.conn.as_ref())
            .and_then(vinc_transport::conn::Connection::active_path)
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
            if !self.leaves_from(i, &old) {
                continue;
            }
            let active = self
                .slots
                .get(i)
                .and_then(|s| s.conn.as_ref())
                .and_then(vinc_transport::conn::Connection::active_path);
            let Some((active, remote)) = active.and_then(|p| self.path_addrs(p).map(|(_, r)| (p, r))) else { continue };
            let pid = self.path_id(new, remote);
            if let Some(conn) = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()) {
                let mut env = env!(self, now);
                let _ = conn.add_path(&mut env, pid, crate::commands::path_info(&remote));
                // The old local address is gone: the session leaves its path as soon as the new one validates.
                let _ = conn.path_lost(active);
                // The link went away and came back on the new address: the peer is woken on the new path.
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
            slot.m.sleep_doubt = conn.recovery().pto_count() > 0;
            let mut env = env!(self, now);
            conn.sleep(&mut env);
            self.settle(i, now);
        }
    }

    /// Wake every session, except the ones that cannot be woken: they close for a redial.
    pub(crate) fn resume(&mut self, now: u64, moved: bool) {
        let moved = moved || self.moved;
        self.moved = false;
        self.suspended = false;
        self.quiet_until = now.saturating_add(RESUME_QUIET);
        for i in 0..K {
            let Some(slot) = self.slots.get_mut(i) else { break };
            if !slot.m.in_use || slot.m.state != State::Established {
                continue;
            }
            if moved || slot.m.sleep_doubt {
                slot.m.sleep_doubt = false;
                self.redial(i, now);
                continue;
            }
            if let Some(conn) = slot.conn.as_mut() {
                let mut env = env!(self, now);
                conn.wake(&mut env);
            }
            self.settle(i, now);
        }
    }
}

const _: () = assert!(MAX_IFACES >= 1);
