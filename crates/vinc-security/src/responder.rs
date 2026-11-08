//! The responder state machine: answers a full, prekey-short or resumption handshake.
//!
//! Invariants: no I/O, no clock, no randomness of its own; the shared caches ([`ResponderStores`]) are passed to
//! every call, so one set of stores serves any number of connections. The responder signs only after it derived the
//! handshake keys from the transcript it saw, and it is established only when the initiator's Finish authenticated
//! (full handshake) or when the ticket's binder verified (resumption). A ticket is removed from the store only after
//! its binder verified, so a Hello with a wrong binder cannot burn a ticket, and an exact replay of a good Hello
//! finds the ticket gone and is rejected. The initiator's prekey enters the cache only after that initiator
//! authenticated, so an unauthenticated peer cannot evict cached prekeys. A message the responder cannot place is
//! dropped with an error and changes nothing; a fatal failure stops it and is reported once as an event.
//!
//! A resumed responder is established at the Hello and keeps its Reply until [`Responder::shed`]: a repeated Hello
//! gets the Reply again while the repeats total under [`RESEND_BUDGET`] bytes (the initiator's Reply was lost), and
//! so does a full Initial under the same connection ids and smaller than three times the Reply (the initiator gave
//! up on the Hello, and its late Reply still completes the session).
//!
//! The transport buffers at most 8 early 1-RTT packets until the Finish arrives and never delivers data from an
//! unauthenticated peer; this crate only reports [`crate::Event::Established`] once the peer is authenticated.

use core::mem;

use vinc_crypto::identity::{MAX_SIGNATURE_LEN, verify};
use vinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use vinc_crypto::{Aead, NodeId, Provider, Secret, Transcript, ct_eq};
use zeroize::Zeroize;

use crate::cache::{DEFAULT_KEY_CACHE, PrekeyCache};
use crate::credit::CreditRecord;
use crate::error::Failure;
use crate::ids::{AeadSet, Alpn, AlpnList, ConnId, LocalIdentity, VERSION};
use crate::keys::{KeyResponse, SoftKeys};
use crate::labels;
use crate::message::{Finish, IdSig, Initial, MessageType, PrekeyField, Reject, Reply, ResumeHello, ResumeReply};
use crate::outbox::{Outbox, Pending};
use crate::schedule::{
    HelloFields, InitialFields, absorb_credit, absorb_identity, absorb_reply, absorb_resume_reply, application_secrets,
    binder, chain, confirmation, early_secret, echo, handshake_keys, hello_transcript, initial_transcript,
    open_handshake, psk_chain, seal_id_sig, signature_message,
};
use crate::session::{EarlyKeys, Env, Established, Output, Traffic};
use crate::tickets::{DEFAULT_SERVER_TICKETS, DEFAULT_TICKET_LIFETIME_S, ServerTickets, TicketBatch};

/// The most bytes of repeated Hellos and Initials a resumed responder answers with its Reply again.
pub const RESEND_BUDGET: usize = 4096;
/// The most bytes of full Initials a resumed responder answers with its Reply again.
pub const LATE_INITIAL_BUDGET: usize = 16_384;

/// The caches every connection of a responder shares.
#[derive(Debug, Default)]
pub struct ResponderStores<const PK: usize = DEFAULT_KEY_CACHE, const TK: usize = DEFAULT_SERVER_TICKETS> {
    /// Initiator prekeys by hash; capacity `PK` (0 disables the short Initial).
    pub prekeys: PrekeyCache<PK>,
    /// Outstanding resumption tickets; capacity `TK`.
    pub tickets: ServerTickets<TK>,
}

/// How a [`Responder`] behaves.
#[derive(Debug, Clone)]
pub struct ResponderConfig {
    /// This node's identity.
    pub identity: LocalIdentity,
    /// This side's connection id for the connection.
    pub scid: ConnId,
    /// The ALPNs this node serves.
    pub alpns: AlpnList,
    /// How many tickets to issue after a handshake (at most 4; 0 turns resumption off).
    pub tickets_per_session: u8,
    /// How long an issued ticket lives, in seconds.
    pub ticket_lifetime_s: u32,
    /// This node's credit record, sent to every initiator authenticated and remembered by its tickets.
    pub credit: CreditRecord,
}

impl ResponderConfig {
    /// A configuration issuing one ticket per session with the default lifetime.
    pub const fn new(identity: LocalIdentity, scid: ConnId, alpns: AlpnList) -> Self {
        Self {
            identity,
            scid,
            alpns,
            tickets_per_session: 1,
            ticket_lifetime_s: DEFAULT_TICKET_LIFETIME_S,
            credit: CreditRecord::NONE,
        }
    }
}

#[allow(clippy::large_enum_variant, reason = "the state lives inline; boxing would allocate")]
enum State {
    Idle,
    /// The Reply is built; waiting for the host to sign.
    Sign(Box1),
    /// The Reply is sent; waiting for the Finish.
    Finish(Wait),
    /// A resumption: established at the Hello, the Reply kept to send again.
    Resumed(Resent),
    Done,
    Failed,
}

/// What a resumed responder needs to recognise a repeat of the Hello it answered.
struct Resent {
    th_hello: [u8; 32],
    dcid: ConnId,
    scid: ConnId,
    spent: usize,
}

/// What the responder holds between the Initial and the signature.
struct Box1 {
    aead: Aead,
    alpn: Alpn,
    th0: [u8; 32],
    th1: [u8; 32],
    hs_initiator: Secret<32>,
    hs_responder: Secret<32>,
    ck1: Secret<32>,
    e: [u8; 32],
    ct: [u8; KEM_CIPHERTEXT_LEN],
    prekey: Option<([u8; 32], [u8; KEM_ENCAPS_KEY_LEN])>,
    peer_credit: CreditRecord,
}

/// What the responder holds between the Reply and the Finish.
struct Wait {
    aead: Aead,
    alpn: Alpn,
    th0: [u8; 32],
    th3: [u8; 32],
    hs_initiator: Secret<32>,
    ck1: Secret<32>,
    prekey: Option<([u8; 32], [u8; KEM_ENCAPS_KEY_LEN])>,
    peer_credit: CreditRecord,
}

/// The responder side of the handshake, one per connection.
pub struct Responder {
    cfg: ResponderConfig,
    th: Transcript,
    out: Outbox,
    state: State,
}

impl core::fmt::Debug for Responder {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Responder").finish_non_exhaustive()
    }
}

impl Responder {
    /// A responder waiting for the first message of a connection.
    pub fn new(cfg: ResponderConfig) -> Self {
        Self {
            cfg,
            th: Transcript::new(),
            out: Outbox::new(),
            state: State::Idle,
        }
    }

    /// The next thing to do: a message to send, a key operation to perform, or an event.
    pub fn poll_output(&mut self) -> Option<Output<'_>> {
        self.out.poll()
    }

    /// Feed a received handshake message.
    ///
    /// # Errors
    /// A non-fatal [`Failure`] (the input was dropped, the state is unchanged) or a fatal one (the machine stopped
    /// and queued [`crate::Event::Failed`]).
    pub fn handle<P: Provider, const PK: usize, const TK: usize>(
        &mut self,
        env: &mut Env<'_, P>,
        stores: &mut ResponderStores<PK, TK>,
        input: &[u8],
    ) -> Result<(), Failure> {
        if matches!(self.state, State::Failed) {
            return Err(Failure::Closed);
        }
        let result = match MessageType::of(input).map_err(Failure::Malformed) {
            Ok(MessageType::Initial | MessageType::ShortInitial) => self.on_initial(env, stores, input),
            Ok(MessageType::Finish) => self.on_finish(env, stores, input),
            Ok(MessageType::ResumeHello) => self.on_hello(env, stores, input),
            Ok(_) => Err(Failure::UnexpectedMessage),
            Err(e) => Err(e),
        };
        self.settle(result)
    }

    /// Deliver the host's answer to the key request last returned by `poll_output`.
    ///
    /// # Errors
    /// [`Failure::UnexpectedKeyResponse`] (nothing changes) if no request of that kind is outstanding; otherwise as
    /// [`Responder::handle`].
    pub fn on_key_response<P: Provider>(&mut self, env: &mut Env<'_, P>, resp: KeyResponse<'_>) -> Result<(), Failure> {
        if matches!(self.state, State::Failed) {
            return Err(Failure::Closed);
        }
        let result = match (self.out.pending(), resp) {
            (Some(Pending::Sign { .. }), KeyResponse::Signature(sig)) => {
                self.out.take_request();
                self.on_signed(env, sig)
            }
            (Some(_), KeyResponse::Failed) => {
                self.out.take_request();
                Err(Failure::KeyOperation)
            }
            _ => Err(Failure::UnexpectedKeyResponse),
        };
        self.settle(result)
    }

    /// Answer the outstanding key request at once from software keys. Returns whether there was one.
    ///
    /// # Errors
    /// As [`Responder::on_key_response`].
    pub fn answer_soft<P: Provider>(&mut self, env: &mut Env<'_, P>, keys: &SoftKeys<'_, P>) -> Result<bool, Failure> {
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let Some(resp) = self.out.answer_soft(env, keys, &mut sig) else {
            return Ok(false);
        };
        let result = self.on_key_response(env, resp);
        sig.zeroize();
        result.map(|()| true)
    }

    /// The host's loss timer fired while waiting for the Finish: queue the Reply again.
    pub fn retransmit(&mut self) {
        if matches!(self.state, State::Finish(_)) {
            self.out.resend();
        }
    }

    /// Release what the handshake no longer needs once the transport knows the peer has the session (it received a
    /// 1-RTT packet): the Reply a resumed responder keeps to send again.
    pub fn shed(&mut self) {
        if matches!(self.state, State::Resumed(_)) {
            self.state = State::Done;
        }
        if !matches!(self.state, State::Finish(_)) {
            self.out.clear_message();
        }
    }

    /// Whether a repeated message would still get the Reply again.
    pub const fn keeps_reply(&self) -> bool {
        matches!(self.state, State::Resumed(_))
    }

    fn settle(&mut self, result: Result<(), Failure>) -> Result<(), Failure> {
        if let Err(f) = result
            && f.is_fatal()
        {
            self.state = State::Failed;
            self.out.fail(f);
        }
        result
    }

    fn reject(&mut self, th: &[u8; 32], ty: MessageType) -> Result<(), Failure> {
        let reject = Reject { echo: echo(th) };
        self.out.build(0, |w| reject.write(w, ty))
    }

    fn on_initial<P: Provider, const PK: usize, const TK: usize>(
        &mut self,
        env: &mut Env<'_, P>,
        stores: &mut ResponderStores<PK, TK>,
        input: &[u8],
    ) -> Result<(), Failure> {
        let initial = Initial::parse(input).map_err(Failure::Malformed)?;
        let hash = initial.prekey_hash();
        let th = initial_transcript(&InitialFields {
            version: initial.version,
            dcid: &initial.dcid,
            scid: &initial.scid,
            alpn: initial.alpn,
            offer: initial.aead_offer,
            e: &initial.e,
            prekey_hash: &hash,
            credit: &initial.credit,
        });
        let th0 = th.snapshot();
        match &mut self.state {
            State::Idle => {}
            State::Finish(w) if w.th0 == th0 => {
                // The same Initial again (a retransmission, or its other form): send the same Reply again.
                self.out.resend();
                return Ok(());
            }
            State::Resumed(r) if r.dcid == initial.dcid && r.scid == initial.scid => {
                // The initiator gave up on its Hello and started a full handshake under the same ids: our Reply to
                // the Hello was lost or late. Send it again, but never answer more than it was asked.
                let size = self.out.len();
                r.spent = r.spent.saturating_add(input.len());
                if size <= input.len().saturating_mul(3) && r.spent <= LATE_INITIAL_BUDGET {
                    self.out.resend();
                    return Ok(());
                }
                return Err(Failure::UnexpectedMessage);
            }
            _ => return Err(Failure::UnexpectedMessage),
        }
        if initial.version != VERSION {
            return Err(Failure::UnsupportedVersion);
        }
        let alpn = self.cfg.alpns.find(initial.alpn).ok_or(Failure::UnknownAlpn)?;
        let p = env.provider;
        let aead = initial
            .aead_offer
            .choose(AeadSet::offer(p.capabilities()))
            .ok_or(Failure::NoCommonAead)?;
        let (ek_bytes, fresh) = match initial.prekey {
            PrekeyField::Full(k) => (*k, true),
            PrekeyField::Hash(h) => match stores.prekeys.get(h) {
                Some(k) => (*k, false),
                None => return self.reject(&th0, MessageType::PrekeyReject),
            },
        };
        let ek = p.kem_encaps_key(&ek_bytes).map_err(|_| Failure::InvalidPeerKey)?;
        let mut seed = env.random::<32>()?;
        let secret = p.x25519_secret(&seed);
        seed.zeroize();
        let e = p.x25519_public(&secret);
        let ss_x = p.x25519_dh(&secret, &initial.e).map_err(|_| Failure::InvalidPeerKey)?;
        let mut m = env.random::<32>()?;
        let encapsulated = p.kem_encapsulate(&ek, &m);
        m.zeroize();
        let (ct, ss_k) = encapsulated?;
        let ct = p.kem_ciphertext_bytes(&ct);
        let mut th = th;
        absorb_reply(&mut th, &self.cfg.scid, aead, &e, &ct);
        let th1 = th.snapshot();
        let hs = handshake_keys(&ss_k, &ss_x, &th1);
        absorb_identity(&mut th, self.cfg.identity.alg(), self.cfg.identity.public_key());
        absorb_credit(&mut th, self.cfg.credit);
        self.out.set_request(Pending::Sign {
            key: self.cfg.identity.key(),
            alg: self.cfg.identity.alg(),
            msg: signature_message(labels::SIGNATURE_RESPONDER, &th.snapshot()),
        });
        self.th = th;
        self.state = State::Sign(Box1 {
            aead,
            alpn,
            th0,
            th1,
            hs_initiator: hs.initiator,
            hs_responder: hs.responder,
            ck1: hs.ck1,
            e,
            ct,
            prekey: fresh.then_some((hash, ek_bytes)),
            peer_credit: initial.credit,
        });
        Ok(())
    }

    fn on_signed<P: Provider>(&mut self, env: &mut Env<'_, P>, signature: &[u8]) -> Result<(), Failure> {
        let State::Sign(b) = mem::replace(&mut self.state, State::Failed) else {
            return Err(Failure::UnexpectedKeyResponse);
        };
        let id = &self.cfg.identity;
        if signature.len() != id.alg().signature_len() {
            return Err(Failure::KeyOperation);
        }
        let sealed = seal_id_sig(
            env.provider,
            b.aead,
            &b.hs_responder,
            &b.th1,
            (id.alg(), id.public_key()),
            signature,
            Some(self.cfg.credit),
        )?;
        self.th.absorb(signature);
        let reply = Reply {
            scid: self.cfg.scid,
            aead: b.aead,
            e: b.e,
            ct: &b.ct,
            sealed: sealed.as_slice(),
        };
        self.out.build(0, |w| reply.write(w))?;
        self.state = State::Finish(Wait {
            aead: b.aead,
            alpn: b.alpn,
            th0: b.th0,
            th3: self.th.snapshot(),
            hs_initiator: b.hs_initiator,
            ck1: b.ck1,
            prekey: b.prekey,
            peer_credit: b.peer_credit,
        });
        Ok(())
    }

    fn on_finish<P: Provider, const PK: usize, const TK: usize>(
        &mut self,
        env: &mut Env<'_, P>,
        stores: &mut ResponderStores<PK, TK>,
        input: &[u8],
    ) -> Result<(), Failure> {
        if !matches!(self.state, State::Finish(_)) {
            return Err(Failure::UnexpectedMessage);
        }
        let finish = Finish::parse(input).map_err(Failure::Malformed)?;
        let State::Finish(w) = mem::replace(&mut self.state, State::Failed) else {
            return Err(Failure::UnexpectedMessage);
        };
        let opened = open_handshake(env.provider, w.aead, &w.hs_initiator, &w.th3, finish.sealed)?;
        let ids = IdSig::parse(opened.as_slice(), false).map_err(Failure::BadPayload)?;
        let peer = NodeId::from_public(ids.alg, ids.public_key).map_err(|_| Failure::InvalidPeerKey)?;
        absorb_identity(&mut self.th, ids.alg, ids.public_key);
        let th4 = self.th.snapshot();
        verify(
            ids.alg,
            ids.public_key,
            &signature_message(labels::SIGNATURE_INITIATOR, &th4),
            ids.signature,
        )
        .map_err(|_| Failure::BadSignature)?;
        self.th.absorb(ids.signature);
        let secrets = application_secrets(&w.ck1, &self.th.snapshot());
        let mut session = Established {
            peer,
            alpn: w.alpn,
            traffic: Traffic {
                aead: w.aead,
                send: secrets.responder,
                recv: secrets.initiator,
            },
            resume: secrets.resume,
            tickets: TicketBatch::new(),
            resumed: false,
            peer_credit: w.peer_credit,
            local_credit: self.cfg.credit,
            remembered_credit: CreditRecord::NONE,
            cid_secret: secrets.cid,
        };
        session.tickets = stores.tickets.issue_batch(
            env,
            &session,
            usize::from(self.cfg.tickets_per_session),
            self.cfg.ticket_lifetime_s,
        )?;
        if let Some((hash, ek)) = &w.prekey {
            stores.prekeys.insert(*hash, ek);
        }
        self.out.established = Some(session);
        self.state = State::Done;
        Ok(())
    }

    /// A repeat of the Hello we answered: our Reply was lost. Send it again, within the byte budget.
    fn on_repeated_hello(&mut self, hello: &ResumeHello<'_>, len: usize) -> Result<(), Failure> {
        let State::Resumed(r) = &mut self.state else {
            return Err(Failure::UnexpectedMessage);
        };
        let th_hello = hello_transcript(&HelloFields {
            version: hello.version,
            alpn: hello.alpn,
            dcid: &hello.dcid,
            scid: &hello.scid,
            aead: hello.aead,
            tid: &hello.tid,
            e: &hello.e,
            credit: &hello.credit,
        })
        .snapshot();
        r.spent = r.spent.saturating_add(len);
        if r.th_hello != th_hello || r.spent > RESEND_BUDGET {
            return Err(Failure::UnexpectedMessage);
        }
        self.out.resend();
        Ok(())
    }

    fn on_hello<P: Provider, const PK: usize, const TK: usize>(
        &mut self,
        env: &mut Env<'_, P>,
        stores: &mut ResponderStores<PK, TK>,
        input: &[u8],
    ) -> Result<(), Failure> {
        let hello = ResumeHello::parse(input).map_err(Failure::Malformed)?;
        if matches!(self.state, State::Resumed(_)) {
            return self.on_repeated_hello(&hello, input.len());
        }
        if !matches!(self.state, State::Idle) {
            return Err(Failure::UnexpectedMessage);
        }
        if hello.version != VERSION {
            return Err(Failure::UnsupportedVersion);
        }
        let alpn = self.cfg.alpns.find(hello.alpn).ok_or(Failure::UnknownAlpn)?;
        let mut th = hello_transcript(&HelloFields {
            version: hello.version,
            alpn: hello.alpn,
            dcid: &hello.dcid,
            scid: &hello.scid,
            aead: hello.aead,
            tid: &hello.tid,
            e: &hello.e,
            credit: &hello.credit,
        });
        let th_hello = th.snapshot();
        let found = stores.tickets.find(&hello.tid);
        let usable = found.and_then(|i| stores.tickets.get(i)).is_some_and(|s| {
            s.expiry >= env.now
                && s.alpn == alpn
                && s.aead == hello.aead
                && ct_eq(&binder(&s.psk, &th_hello), &hello.binder)
        });
        let Some(slot) = found.filter(|_| usable).and_then(|i| stores.tickets.remove(i)) else {
            // Unknown, expired or not matching: tell the initiator to start a full handshake.
            if let Some(i) = found.filter(|i| stores.tickets.get(*i).is_some_and(|s| s.expiry < env.now)) {
                stores.tickets.remove(i);
            }
            return self.reject(&th_hello, MessageType::ResumeReject);
        };
        let p = env.provider;
        let ck_psk = psk_chain(&slot.psk);
        let early = early_secret(&ck_psk, &th_hello);
        let mut seed = env.random::<32>()?;
        let secret = p.x25519_secret(&seed);
        seed.zeroize();
        let e = p.x25519_public(&secret);
        let ss_x = p.x25519_dh(&secret, &hello.e).map_err(|_| Failure::InvalidPeerKey)?;
        absorb_resume_reply(&mut th, &hello.binder, &self.cfg.scid, &e, self.cfg.credit);
        let ck1 = chain(&ck_psk, ss_x.expose());
        let secrets = application_secrets(&ck1, &th.snapshot());
        let mut session = Established {
            peer: slot.peer,
            alpn,
            traffic: Traffic {
                aead: slot.aead,
                send: secrets.responder,
                recv: secrets.initiator,
            },
            resume: secrets.resume,
            tickets: TicketBatch::new(),
            resumed: true,
            peer_credit: hello.credit,
            local_credit: self.cfg.credit,
            remembered_credit: slot.credit,
            cid_secret: secrets.cid,
        };
        session.tickets = stores.tickets.issue_batch(
            env,
            &session,
            usize::from(self.cfg.tickets_per_session),
            self.cfg.ticket_lifetime_s,
        )?;
        let mut encoded = [0u8; 81];
        let n = session.tickets.encode(&mut encoded).map_err(Failure::BadPayload)?;
        let confirm = confirmation(&secrets.confirm, &mut th, encoded.get(..n).unwrap_or_default());
        let reply = ResumeReply {
            scid: self.cfg.scid,
            e,
            tickets: session.tickets,
            credit: self.cfg.credit,
            confirm,
        };
        self.out.build(0, |w| reply.write(w))?;
        self.out.early = Some(EarlyKeys {
            aead: slot.aead,
            secret: early,
        });
        self.out.established = Some(session);
        self.state = State::Resumed(Resent {
            th_hello,
            dcid: hello.dcid,
            scid: hello.scid,
            spent: 0,
        });
        Ok(())
    }
}
