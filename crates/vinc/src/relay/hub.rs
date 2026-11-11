//! The relay's own endpoint: the hub that members keep a validated UDP session with.
//!
//! A member that holds a session here can send packets through the relay over UDP (the tunnel) and receive packets
//! the relay holds for it; the endpoint's packets for a member that has no UDP session travel on the member's
//! carrier instead. The state machine decides which; this module runs the endpoint and answers its events.
//!
//! Invariants: a session is a member's only after the endpoint reported its peer; the table of slots that name
//! members in relay path addresses never grows past its bound and reuses the oldest first; the endpoint's key
//! requests are answered from the relay's identity and its own prekeys, so no key leaves its store.

use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::net::SocketAddr;

use vinc_core::{
    Answer, Command, EndpointConfig, Event, Query, Role, SessionId, Transmit, is_relay_addr, relay_addr, relay_parts,
};
use vinc_crypto::{Drbg, NodeId};
use vinc_keystore::KeyStore;
use vinc_security::{KeyRequest, KeyResponse, LocalIdentity};

use super::limits::Limits;
use crate::error::{Error, Result};
use crate::keys::{Identity, Prekeys, is_identity};
use crate::node::AnyEp;

/// The relay path addresses name a member by a 16-bit slot; this many are kept.
const SLOTS: usize = 4096;

/// What the endpoint's events ask of the state machine.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Note {
    /// A member's session woke without reopening its carrier.
    Awake(NodeId),
    /// A member's session ended.
    Gone(NodeId),
}

pub(crate) struct Hub {
    ep: AnyEp,
    prekeys: Prekeys,
    local: SocketAddr,
    members: Vec<(SessionId, NodeId)>,
    slots: Vec<NodeId>,
    next_slot: usize,
    pending: VecDeque<Event>,
}

impl Hub {
    pub(crate) fn new<K: KeyStore>(
        local: SocketAddr,
        alpns: &[Vec<u8>],
        identity: &mut Identity<K>,
        limits: &Limits,
        now: u64,
    ) -> Result<Self> {
        let mut seed = [0u8; 32];
        identity.random(&mut seed)?;
        let mut key = [0u8; 8];
        identity.random(&mut key)?;
        let mut cfg = EndpointConfig::new(u64::from_le_bytes(key));
        cfg.conn.max_gso = 1;
        let local_id: LocalIdentity = identity.local()?;
        let mut ep = AnyEp::new(
            limits.hub_sessions,
            now,
            Drbg::new(&seed),
            local_id,
            cfg,
            limits.hub_pool_chunks,
        )
        .ok_or_else(|| Error::config("the hub session limit is out of range"))?;
        for a in alpns {
            if !ep.register_alpn(a) {
                return Err(Error::config(
                    "the relay's hub accepts too many protocols, or one is too long",
                ));
            }
        }
        ep.add_iface(local)
            .ok_or_else(|| Error::config("the hub could not use the UDP address"))?;
        let mut prekeys = Prekeys::new()?;
        ep.set_prekey(prekeys.rotate(now)?);
        Ok(Self {
            ep,
            prekeys,
            local,
            members: Vec::new(),
            slots: Vec::new(),
            next_slot: 0,
            pending: VecDeque::new(),
        })
    }

    fn cmd(&mut self, now: u64, c: Command<'_, vinc_transport::stream::NoSource>) {
        if let Ok(r) = self.ep.command(now, c) {
            self.pending.extend(r.events.iter().copied());
        }
    }

    fn session_remote(&self, sid: SessionId) -> Option<SocketAddr> {
        match self.ep.query(Query::Stats(sid)) {
            Answer::Stats(st) if st.path_validated => st.route.map(|(_, r)| r).filter(|r| !is_relay_addr(r)),
            _ => None,
        }
    }

    /// The member whose validated session talks from `src`.
    pub(crate) fn member_at(&self, src: &SocketAddr) -> Option<NodeId> {
        self.members
            .iter()
            .find(|(sid, _)| self.session_remote(*sid) == Some(*src))
            .map(|(_, n)| *n)
    }

    /// The address of the member's validated session.
    pub(crate) fn member_addr(&self, node: &NodeId) -> Option<SocketAddr> {
        let (sid, _) = self.members.iter().find(|(_, n)| n == node)?;
        self.session_remote(*sid)
    }

    fn slot_of(&mut self, node: &NodeId) -> u16 {
        let i = self.slots.iter().position(|x| x == node).unwrap_or_else(|| {
            if self.slots.len() < SLOTS {
                self.slots.push(*node);
                self.slots.len() - 1
            } else {
                let i = self.next_slot;
                self.next_slot = (i + 1) % SLOTS;
                if let Some(s) = self.slots.get_mut(i) {
                    *s = *node;
                }
                i
            }
        });
        u16::try_from(i).unwrap_or(0)
    }

    /// A datagram of the endpoint's own protocol arrived from `src`.
    pub(crate) fn handle_datagram(&mut self, now: u64, src: SocketAddr, buf: &mut [u8]) {
        self.ep.handle_datagram(now, self.local, src, buf);
    }

    /// A packet the state machine routed to the relay's own endpoint, from `from`.
    pub(crate) fn local_packet(&mut self, now: u64, from: &NodeId, packet: &[u8]) {
        let slot = self.slot_of(from);
        let mut p = packet.to_vec();
        self.ep
            .handle_datagram(now, self.local, relay_addr(false, 0, slot), &mut p);
    }

    /// The member's carrier showed life: the endpoint's keepalive for its session need not fire.
    pub(crate) fn pulse(&mut self, now: u64, node: &NodeId) {
        let sid = self.members.iter().find(|(_, n)| n == node).map(|(s, _)| *s);
        if let Some(session) = sid {
            self.cmd(now, Command::Pulse { session, sent: true });
        }
    }

    /// Answer the endpoint's events; what the state machine must hear goes to `notes`.
    pub(crate) fn events<K: KeyStore>(&mut self, now: u64, identity: &mut Identity<K>, notes: &mut Vec<Note>) {
        if self.prekeys.due(now)
            && let Ok(info) = self.prekeys.rotate(now)
        {
            self.ep.set_prekey(info);
        }
        while let Some(ev) = self.pending.pop_front().or_else(|| self.ep.poll_event()) {
            match ev {
                Event::KeyRequest { session } => self.answer_key(now, session, identity),
                Event::AcpCheck { check, .. } => self.cmd(now, Command::AcpAnswer { check, allow: true }),
                Event::Incoming { session, node, .. } => {
                    self.members.push((session, node));
                    self.cmd(
                        now,
                        Command::SetRole {
                            session,
                            role: Role::Member,
                        },
                    );
                }
                Event::Closed { session, .. } => {
                    if let Some(i) = self.members.iter().position(|(s, _)| *s == session) {
                        let (_, node) = self.members.swap_remove(i);
                        notes.push(Note::Gone(node));
                    }
                }
                Event::PeerAwake { session } => {
                    if let Some((_, node)) = self.members.iter().find(|(s, _)| *s == session) {
                        notes.push(Note::Awake(*node));
                    }
                }
                _ => {}
            }
        }
    }

    fn answer_key<K: KeyStore>(&mut self, now: u64, session: SessionId, identity: &mut Identity<K>) {
        enum Owned {
            Sign(vinc_security::KeyHandle, Vec<u8>),
            Decap(vinc_security::KeyHandle, Vec<u8>),
        }
        let req = match self.ep.query(Query::KeyRequest(session)) {
            Answer::KeyRequest(KeyRequest::Sign { key, message, .. }) => Owned::Sign(key, message.to_vec()),
            Answer::KeyRequest(KeyRequest::Decapsulate { key, ct }) => Owned::Decap(key, ct.to_vec()),
            _ => return,
        };
        let sig;
        let response = match req {
            Owned::Sign(key, msg) => match is_identity(key).then(|| identity.sign(&msg).ok()).flatten() {
                Some(s) => {
                    sig = s;
                    KeyResponse::Signature(&sig)
                }
                None => KeyResponse::Failed,
            },
            Owned::Decap(key, ct) => match self.prekeys.decapsulate(key, &ct) {
                Some(s) => KeyResponse::SharedSecret(s),
                None => KeyResponse::Failed,
            },
        };
        self.cmd(now, Command::KeyResponse { session, response });
    }

    /// The next datagram the endpoint wants to send: its remote and its bytes in `out`.
    pub(crate) fn transmit(&mut self, now: u64, out: &mut [u8]) -> Option<(Target, usize)> {
        let t: Transmit = self.ep.poll_transmit(now, out)?;
        let target = match relay_parts(&t.remote) {
            Some((_, slot)) => match self.slots.get(usize::from(slot)) {
                Some(node) => Target::Member(*node),
                None => Target::Nowhere,
            },
            None => Target::Udp(t.remote),
        };
        Some((target, t.len))
    }

    pub(crate) fn handle_timeout(&mut self, now: u64) {
        self.ep.handle_timeout(now);
    }

    pub(crate) fn next_timeout(&self) -> Option<u64> {
        self.ep.poll_timeout()
    }

    pub(crate) const fn sessions(&self) -> usize {
        self.members.len()
    }
}

/// Where a datagram of the endpoint goes.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Target {
    /// Through the state machine, to a member that has no UDP session.
    Member(NodeId),
    /// Out of the UDP socket.
    Udp(SocketAddr),
    /// To a slot that names nobody.
    Nowhere,
}
