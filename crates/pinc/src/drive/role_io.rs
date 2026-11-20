//! The relay role on the driving future: what the future of [`Endpoint::run`](crate::Endpoint::run) does for the relay
//! that runs inside the endpoint, in the order a relay of its own would do it (see [`crate::role`]).
//!
//! A datagram that arrives is offered to the relay first and goes to the node only if the relay did not take it. What
//! the relay queued for the node's endpoint (packets from members' carriers, pulses for their sessions) is applied to
//! it, and the events of the members' sessions that the node reports are told to the relay. A packet the endpoint
//! addresses to a member leaves on the member's carrier instead of the socket; the relay's own datagrams leave on the
//! socket. The relay's next deadline joins the endpoint's, and its store writes and carrier operations are polled by
//! the driver, which holds them in its own locals: they live as long as the `run` that drives the role.
//!
//! Every call here is for an endpoint with a role; for one without, the callers' tests of [`Role::ON`] are constants
//! and none of it is compiled in.
//!
//! Invariants: the role is borrowed inside one call and never across an await or a call of a host closure; the relay
//! gets the relay clock and the endpoint the endpoint's, a fixed origin apart; nothing here runs until the role's
//! records are restored.

use alloc::vec::Vec;
use core::cell::RefMut;
use core::future::{pending, poll_fn};
use core::net::SocketAddr;
use core::pin::pin;
use core::task::Poll;

use super::Shared;
use crate::engine::Core;
use crate::host::Hosted;
use crate::role::Role;

/// The most rounds of applying and hearing one call works through before it yields.
const ROUNDS: usize = 64;

impl<H: Hosted> Shared<H> {
    /// The relay role, borrowed for one call. `None` only if a borrow is already open, which nothing that runs on this
    /// thread can arrange.
    pub(crate) fn role(&self) -> Option<RefMut<'_, H::Role>> {
        self.host.role().try_borrow_mut().ok()
    }

    /// The relay clock at endpoint time `now`.
    pub(super) fn relay_now(&self, now: u64) -> u64 {
        super::role_clock(self.role_wall0, now)
    }

    /// Run the relay's timers when they are due, apply what it queued for the endpoint and tell it what the endpoint
    /// reported; whether anything moved. The relay's next deadline is added to the endpoint's.
    pub(super) fn role_serve(&self, core: &mut Core<H::Keys, H::Access>, now: u64) -> bool {
        if !self.role_ready.get() {
            return false;
        }
        let Some(mut role) = self.role() else { return false };
        let rnow = self.relay_now(now);
        let mut moved = false;
        if role.due(rnow).is_some_and(|d| d <= rnow) {
            role.tick(rnow);
            moved = true;
        }
        let mut out = Vec::new();
        for _ in 0..ROUNDS {
            let mut did = role.pump(core.node.endpoint_mut(), now, &mut out);
            let heard = core.take_relay_events();
            did |= !heard.is_empty();
            for ev in &heard {
                role.heard(core.node.endpoint_mut(), now, rnow, ev, &mut out);
            }
            core.return_relay_events(heard);
            if !did {
                break;
            }
            moved = true;
            // What the commands of the relay raised joins the node's own loop; the events that come out of it are the
            // core's to take, and may name more members.
            core.node.relay_events(now, &out);
            out.clear();
            self.service(core, now);
        }
        if let Some(at) = role.due(rnow) {
            core.add_deadline(super::endpoint_clock(self.role_wall0, at));
        }
        moved
    }

    /// Datagrams that arrived from `from`, `segment` bytes each but the last: each is the relay's or the node's.
    pub(super) fn role_datagrams(
        &self,
        core: &mut Core<H::Keys, H::Access>,
        now: u64,
        from: SocketAddr,
        batch: &mut [u8],
        segment: usize,
    ) {
        let Some(mut role) = self.role() else {
            core.node.handle_batch(now, self.local, from, batch, segment);
            return;
        };
        if batch.is_empty() {
            core.node.handle_batch(now, self.local, from, batch, segment);
            return;
        }
        let rnow = self.relay_now(now);
        for d in batch.chunks_mut(segment.max(1)) {
            // An answer to one of the node's own requests (as a client of other relays) is the node's, not the relay's.
            let answer = d.first().is_some_and(|b| *b < 0x40) && !pinc_node::is_relay_request(d);
            if !answer && role.offer(core.node.endpoint(), rnow, from, d) {
                continue;
            }
            core.node.handle_batch(now, self.local, from, d, usize::MAX);
            if !answer {
                role.after_offer(core.node.endpoint(), rnow, from);
            }
        }
    }

    /// The endpoint wants to send `bytes` (datagrams of `segment` bytes) to `to`: whether `to` names a member of the
    /// relay, whose carrier then takes them and the socket sends nothing.
    pub(super) fn role_carries(
        &self,
        core: &mut Core<H::Keys, H::Access>,
        now: u64,
        to: &SocketAddr,
        bytes: &[u8],
        segment: usize,
    ) -> bool {
        if !pinc_core::is_relay_addr(to) {
            return false;
        }
        let Some(mut role) = self.role() else { return false };
        // Before the role restored its mailbox the packet is taken and dropped, as a lost one: the transport resends.
        if !self.role_ready.get() {
            role.lost();
            return true;
        }
        let rnow = self.relay_now(now);
        let mut carried = false;
        for d in bytes.chunks(segment.max(1)) {
            carried |= role.carry(rnow, to, d);
        }
        if carried {
            // The carrier has bytes to write: the driver polls the relay's carriers.
            core.wake_driver();
        }
        carried
    }

    /// The next datagram the relay itself sends: its remote, its length in `buf` and its segment size.
    pub(super) fn role_outgoing(&self, buf: &mut [u8]) -> Option<(SocketAddr, usize, usize)> {
        if !self.role_ready.get() {
            return None;
        }
        self.role()?.outgoing(buf).map(|(to, n)| (to, n, n))
    }

    /// The role's own work as one future that never completes; the driving future polls it. It restores what the
    /// store kept, then polls the host's carriers and the store writes, which its locals hold in flight.
    pub(super) async fn role_task(&self) {
        self.role_ready.set(false);
        // A run after a run (the future was dropped and awaited again): the role holds what the store kept already.
        if !self.role().is_some_and(|r| r.restored()) {
            let Some(load) = self.role().map(|r| r.load()) else {
                return pending().await;
            };
            let kept = match load.await {
                Ok(kept) => kept,
                Err(e) => {
                    // A relay does not start with an unknown set of records: the endpoint stops with the store's error.
                    if let Some(mut core) = self.lock() {
                        core.fail(e);
                    }
                    return pending().await;
                }
            };
            if let Some(mut role) = self.role() {
                role.restore(self.relay_now(self.now()), &kept);
            }
        }
        let Some(driver) = self.role().map(|r| r.start_io()) else {
            return pending().await;
        };
        let mut driver = pin!(driver);
        let mut persist = pin!(None);
        self.role_ready.set(true);
        self.rdirty.set(true);
        poll_fn(|cx| {
            let rnow = self.relay_now(self.now());
            let mut moved = false;
            // The host's own work comes first: the operations it finishes show up as completions below.
            let _ = driver.as_mut().poll(cx);
            if let Some(mut role) = self.role() {
                moved |= role.poll_io(cx, rnow);
                if persist.is_none()
                    && let Some(write) = role.next_write()
                {
                    persist.set(Some(write));
                }
            }
            if let Some(f) = persist.as_mut().as_pin_mut()
                && let Poll::Ready(r) = f.poll(cx)
            {
                persist.set(None);
                moved = true;
                if let Some(mut role) = self.role() {
                    role.written(r.is_ok());
                }
            }
            if moved {
                self.rdirty.set(true);
                cx.waker().wake_by_ref();
            }
            Poll::<()>::Pending
        })
        .await;
    }
}

/// Ends the relay role when the run that drove it ends, however it ends: every carrier is dropped and the host told.
pub(crate) struct RoleEnd<'a, H: Hosted>(pub(crate) &'a Shared<H>);

impl<H: Hosted> Drop for RoleEnd<'_, H> {
    fn drop(&mut self) {
        if !H::Role::ON {
            return;
        }
        self.0.role_ready.set(false);
        let rnow = self.0.relay_now(self.0.now());
        if let Some(mut role) = self.0.role() {
            role.end(rnow);
        }
    }
}
