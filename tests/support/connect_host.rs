//! The host duties every simulated connectivity node shares: an endpoint with its key material, the answers to the
//! key requests of the endpoint, the carrier handshake and the layer's own signatures, and the access checks.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::missing_panics_doc,
    clippy::missing_errors_doc,
    clippy::must_use_candidate,
    clippy::large_stack_arrays
)]

use std::collections::{HashMap, VecDeque};
use std::net::SocketAddr;

use vinc_core::{Command, CommandError, Endpoint, EndpointConfig, Event, Query, Reply, SessionId};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Secret};
use vinc_security::{
    Env, KeyHandle, KeyRequest, KeyResponse, LocalIdentity, PrekeyInfo, PrekeyPolicy, SoftKeys, SoftPrekeys,
};
use vinc_transport::stream::NoSource;

use crate::{Caps, CoreEp, memory, slots};

pub const HUB_ALPN: &[u8] = b"vinc/a";

/// What a simulated node reports to the scenario.
#[derive(Debug, Clone)]
pub enum Ev {
    Ep(Event),
    Notice(vinc_connect::client::Notice),
    Stream(vinc_sim::StreamEvent),
    Trace(vinc_connect::relay::Trace),
    Wake(NodeId),
}

#[allow(clippy::large_enum_variant, reason = "a test type, built once per key request")]
/// A key answer that owns its bytes, so the request it answers can be dropped first.
pub enum Answer {
    Sig([u8; vinc_crypto::identity::MAX_SIGNATURE_LEN], usize),
    Secret(Secret<32>),
    Failed,
}

impl Answer {
    pub fn response(&self) -> KeyResponse<'_> {
        match self {
            Self::Sig(b, n) => KeyResponse::Signature(&b[..*n]),
            Self::Secret(s) => KeyResponse::SharedSecret(Secret::new(*s.expose())),
            Self::Failed => KeyResponse::Failed,
        }
    }
}

/// Answer a key request from software keys.
pub fn answer_parts(
    prov: &Caps,
    kp: &Keypair,
    prekeys: &SoftPrekeys<Caps>,
    drbg: &mut Drbg,
    now: u64,
    req: &KeyRequest<'_>,
) -> Answer {
    let soft = SoftKeys {
        signer: Some((KeyHandle(1), kp)),
        prekeys: Some(prekeys),
    };
    let mut env = Env {
        provider: prov,
        now,
        drbg,
    };
    let mut sig = [0u8; vinc_crypto::identity::MAX_SIGNATURE_LEN];
    match soft.answer(&mut env, req, &mut sig) {
        KeyResponse::Signature(s) => {
            let n = s.len();
            let mut out = [0u8; vinc_crypto::identity::MAX_SIGNATURE_LEN];
            out[..n].copy_from_slice(s);
            Answer::Sig(out, n)
        }
        KeyResponse::SharedSecret(s) => Answer::Secret(s),
        KeyResponse::Failed => Answer::Failed,
    }
}

/// The node's key material and an endpoint over it.
pub struct Host {
    pub ep: Box<CoreEp>,
    pub prov: Caps,
    pub drbg: Drbg,
    pub kp: Keypair,
    pub prekeys: SoftPrekeys<Caps>,
    pub prekey_info: PrekeyInfo,
    pub identity: LocalIdentity,
    pub me: NodeId,
    /// Every event the endpoint or the layer produced, with its time.
    pub log: Vec<(u64, Event)>,
    pub read: HashMap<(SessionId, u64), Vec<u8>>,
    /// Sessions that became established, in order.
    pub sessions: Vec<SessionId>,
    pub deny: bool,
    /// Events that commands of the host returned in their replies, waiting to be handled like polled ones.
    pub queue: VecDeque<Event>,
}

impl Host {
    pub fn new(tag: u8, addr: SocketAddr, now: u64) -> Self {
        let alg = IdentityAlg::Ed25519;
        let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
        let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
        let prov = Caps(vinc_crypto::Software, true);
        let mut drbg = Drbg::new(&[tag ^ 0x5a; 32]);
        let mut cfg = EndpointConfig::new(u64::from(tag) * 0x9E37_79B9);
        cfg.conn.max_gso = 1;
        let ep_drbg = Drbg::new(&[tag ^ 0xa5; 32]);
        let mut ep = Box::new(Endpoint::new(now, prov, ep_drbg, identity, cfg, slots()));
        let mut env = Env {
            provider: &prov,
            now,
            drbg: &mut drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
        let prekey_info = prekeys.acquire(&mut env).unwrap();
        ep.set_prekey(prekey_info.clone());
        assert!(ep.register_alpn(HUB_ALPN));
        ep.add_iface(addr).unwrap();
        let _ = memory;
        Self {
            ep,
            prov,
            drbg,
            kp,
            prekeys,
            prekey_info,
            identity,
            me: identity.node_id(),
            log: Vec::new(),
            read: HashMap::new(),
            sessions: Vec::new(),
            deny: false,
            queue: VecDeque::new(),
        }
    }

    /// Apply a command; the events its reply carries are queued for [`Host::next_event`].
    pub fn command(&mut self, now: u64, c: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        let r = self.ep.command(now, c)?;
        self.queue.extend(r.events.iter().copied());
        Ok(r)
    }

    /// The next event: one a command returned, else one the endpoint queued.
    pub fn next_event(&mut self) -> Option<Event> {
        self.queue.pop_front().or_else(|| self.ep.poll_event())
    }

    /// Answer a key request from the node's software keys.
    pub fn answer(&mut self, now: u64, req: &KeyRequest<'_>) -> Answer {
        answer_parts(&self.prov, &self.kp, &self.prekeys, &mut self.drbg, now, req)
    }

    /// The host duties of one endpoint event (key requests, access checks, reading streams).
    pub fn duty(&mut self, now: u64, ev: &Event) {
        self.log.push((now, *ev));
        match *ev {
            Event::KeyRequest { session } => {
                let Self {
                    ep,
                    prov,
                    kp,
                    prekeys,
                    drbg,
                    ..
                } = self;
                let owned = match ep.query(Query::KeyRequest(session)) {
                    vinc_core::Answer::KeyRequest(req) => Some(answer_parts(prov, kp, prekeys, drbg, now, &req)),
                    _ => None,
                };
                let Some(owned) = owned else { return };
                let _ = self.command(
                    now,
                    Command::KeyResponse {
                        session,
                        response: owned.response(),
                    },
                );
            }
            Event::AcpCheck { check, .. } => {
                let _ = self.command(
                    now,
                    Command::AcpAnswer {
                        check,
                        allow: !self.deny,
                    },
                );
            }
            Event::Connected { session, .. } | Event::Incoming { session, .. } => self.sessions.push(session),
            Event::StreamReadable { session, stream } => self.read_stream(now, session, stream),
            _ => {}
        }
    }

    pub fn read_stream(&mut self, now: u64, session: SessionId, stream: u64) {
        loop {
            let chunk = match self.ep.query(Query::Read { session, stream }) {
                vinc_core::Answer::Chunk(c) if !c.is_empty() => c.to_vec(),
                _ => break,
            };
            self.read
                .entry((session, stream))
                .or_default()
                .extend_from_slice(&chunk);
            let _ = self.command(
                now,
                Command::Consume {
                    session,
                    stream,
                    n: chunk.len(),
                },
            );
        }
    }

    /// Everything received on a session, in stream order.
    pub fn received(&self, session: SessionId) -> Vec<u8> {
        let mut keys: Vec<_> = self.read.keys().filter(|(s, _)| *s == session).collect();
        keys.sort();
        keys.into_iter().flat_map(|k| self.read[k].clone()).collect()
    }
}

/// A queue of datagrams and stream operations a node wants the simulator to carry out.
#[derive(Default)]
pub struct Outbox {
    pub datagrams: VecDeque<(SocketAddr, SocketAddr, Vec<u8>)>,
    pub ops: VecDeque<(vinc_sim::StreamOp, Vec<u8>)>,
}
