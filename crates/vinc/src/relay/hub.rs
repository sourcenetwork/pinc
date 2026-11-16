//! The relay host's own endpoint: the hub that members keep a validated UDP session with, for a relay that runs alone.
//!
//! A relay embedded in a node has no use for this: the node's endpoint is the hub, lent to the part at each call. Here
//! the host loop builds an endpoint of its own on the relay's identity, answers its key requests and its prekeys, tells
//! the part which of its events concern members, and hands it the datagrams the endpoint addresses to a member.
//!
//! Invariants: the endpoint's key requests are answered from the relay's identity and its own prekeys, so no key leaves
//! its store; a session is a member's only after the endpoint reported its peer.

use alloc::vec::Vec;
use core::net::SocketAddr;

use vinc_core::{Answer, Command, EndpointConfig, Event, Query, SessionId};
use vinc_crypto::Drbg;
use vinc_keystore::KeyStore;
use vinc_node::Ep as NodeEp;
use vinc_security::{KeyRequest, KeyResponse, LocalIdentity};

use super::access::Access;
use super::carriers::Carriers;
use super::limits::Limits;
use super::part::{Part, SharedIdentity};
use super::store::Store;
use crate::error::{Error, Result};
use crate::keys::{Prekeys, is_identity};
use crate::node::AnyEp;

/// The most rounds one cycle works through before it yields.
const ROUNDS: usize = 256;

pub(crate) struct Hub {
    ep: AnyEp,
    prekeys: Prekeys,
    local: SocketAddr,
    pending: Vec<Event>,
    tx: Vec<u8>,
}

impl Hub {
    pub(crate) fn new<K: KeyStore>(
        local: SocketAddr,
        alpns: &[Vec<u8>],
        identity: &SharedIdentity<K>,
        limits: &Limits,
        now: u64,
    ) -> Result<Self> {
        let mut seed = [0u8; 32];
        let mut key = [0u8; 8];
        let local_id: LocalIdentity = {
            let mut id = identity.borrow_mut();
            id.random(&mut seed)?;
            id.random(&mut key)?;
            id.local()?
        };
        let mut cfg = EndpointConfig::new(u64::from_le_bytes(key));
        cfg.conn.max_gso = 1;
        cfg.conn.tail_repair = false;
        let mut ep = AnyEp::new(
            limits.hub_sessions,
            now,
            Drbg::new(&seed),
            local_id,
            cfg,
            limits.hub_pool_chunks,
            true,
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
            pending: Vec::new(),
            tx: alloc::vec![0; vinc_core::MAX_DATAGRAM + 64],
        })
    }

    /// A datagram that is not the relay's own arrived from `src`.
    pub(crate) fn handle_datagram(&mut self, now: u64, src: SocketAddr, buf: &mut [u8]) {
        self.ep.handle_datagram(now, self.local, src, buf);
    }

    pub(crate) fn handle_timeout(&mut self, now: u64) {
        self.ep.handle_timeout(now);
    }

    pub(crate) fn next_timeout(&self) -> Option<u64> {
        self.ep.poll_timeout()
    }

    /// The part's view of the endpoint, for a datagram that came in.
    pub(crate) const fn ep(&self) -> &AnyEp {
        &self.ep
    }

    /// Work the part and the endpoint through until neither has anything left for the other.
    pub(crate) fn cycle<C, K, St, A>(&mut self, part: &mut Part<C, K, St, A>, now: u64)
    where
        C: Carriers,
        K: KeyStore,
        St: Store,
        A: Access,
    {
        for _ in 0..ROUNDS {
            if self.prekeys.due(now)
                && let Ok(info) = self.prekeys.rotate(now)
            {
                self.ep.set_prekey(info);
            }
            let mut did = part.hub(&mut self.ep, now, &mut self.pending);
            while let Some(ev) = (!self.pending.is_empty())
                .then(|| self.pending.remove(0))
                .or_else(|| self.ep.poll_event())
            {
                did = true;
                match ev {
                    Event::KeyRequest { session } => self.answer_key(now, session, &part.identity()),
                    Event::AcpCheck { check, .. } => self.cmd(now, Command::AcpAnswer { check, allow: true }),
                    other => part.hub_event(&mut self.ep, now, now, &other, &mut self.pending),
                }
            }
            let mut buf = core::mem::take(&mut self.tx);
            while let Some(t) = self.ep.poll_transmit(now, &mut buf) {
                did = true;
                let bytes = buf.get(..t.len).unwrap_or_default();
                if !part.tunnel(now, &t.remote, bytes) {
                    part.queue_udp(t.remote, bytes);
                }
            }
            self.tx = buf;
            if !did {
                return;
            }
        }
    }

    fn cmd(&mut self, now: u64, c: Command<'_, crate::Body>) {
        if let Ok(r) = vinc_connect::client::Port::command(&mut self.ep, now, c) {
            self.pending.extend(r.events.iter().copied());
        }
    }

    fn answer_key<K: KeyStore>(&mut self, now: u64, session: SessionId, identity: &SharedIdentity<K>) {
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
            Owned::Sign(key, msg) => match is_identity(key)
                .then(|| identity.borrow_mut().sign(&msg).ok())
                .flatten()
            {
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
}
