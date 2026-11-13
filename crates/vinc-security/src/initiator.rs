//! The initiator state machine: dials a node and completes a full, prekey-short or resumption handshake.
//!
//! Invariants: no I/O, no clock, no randomness of its own. `new` queues the first message; the host feeds received
//! bytes to `handle`, answers key requests with `on_key_response` (or `answer_soft`), tells it about lost flights
//! with `retransmit`, and drains `poll_output`. The machine authenticates the responder before it sends anything
//! identifying: the Finish (which carries the initiator's identity) goes out only after the responder's signature
//! verified and its node id equals the dialed one. A fatal failure stops the machine and is reported once as an
//! event; a malformed or misplaced message is dropped with an error and changes nothing.
//!
//! The full flow is: Initial (or the short Initial when the responder is known to cache the prekey), then Reply,
//! a prekey decapsulation request, a signature request, and the Finish together with the established session.
//! With a ticket the flow is: resume Hello (and the 0-RTT keys), then the resume Reply and the established session;
//! if the responder rejects the ticket the machine starts a full handshake by itself, and so it does when the Hello
//! stays unanswered: the third send is a full Initial under the same destination id. The machine then still accepts
//! a late resume Reply, which completes the resumed session and abandons the full handshake.
//!
//! The sends are counted from the first. A resend of the Initial is the short one while the host allows short Initials
//! ([`Initiator::set_short_until`]: it heard a validated UDP path lately), whichever form the first send had, and the
//! full one otherwise; sends 3, 6, 9 and so on always carry the full prekey, so a lost or unroutable reject never
//! leaves the machine sending short Initials only.

use core::mem;

use vinc_crypto::identity::{MAX_SIGNATURE_LEN, verify};
use vinc_crypto::{Aead, NodeId, Provider, Secret, Transcript, ct_eq};
use vinc_wire::WireError;
use zeroize::Zeroize;

use crate::credit::CreditRecord;
use crate::error::Failure;
use crate::ids::{AeadSet, Alpn, ConnId, LocalIdentity, VERSION};
use crate::keys::{KeyRequest, KeyResponse, PrekeyInfo, SoftKeys};
use crate::labels;
use crate::message::{
    Finish, IdSig, Initial, InitialForm, MAX_MESSAGE_LEN, MessageType, PrekeyField, Reject, Reply, ResumeHello,
    ResumeReply, min_initial_len,
};
use crate::outbox::{Outbox, Pending};
use crate::schedule::{
    AppSecrets, HelloFields, InitialFields, absorb_credit, absorb_identity, absorb_reply, absorb_resume_reply,
    application_secrets, binder, chain, confirmation, early_secret, echo, handshake_keys, hello_transcript,
    initial_transcript, open_handshake, psk_chain, seal_id_sig, signature_message,
};
use crate::session::{EarlyKeys, Env, Established, Output, Traffic};
use crate::tickets::{Ticket, TicketBatch};

/// The send on which an unanswered resume Hello gives way to a full handshake.
pub const RESUME_TRIES: u32 = 3;
/// Every this many sends the short Initial carries the full prekey.
pub const FULL_EVERY: u32 = 3;

/// What an [`Initiator`] needs to start.
#[derive(Debug)]
pub struct InitiatorParams<'a> {
    /// The node being dialed. The responder must prove it is this node.
    pub peer: NodeId,
    /// The application protocol to speak.
    pub alpn: &'a [u8],
    /// This side's connection id.
    pub scid: ConnId,
    /// This node's identity.
    pub identity: &'a LocalIdentity,
    /// The prekey to use for this handshake (from [`crate::SoftPrekeys::acquire`] or the host's key store).
    pub prekey: &'a PrekeyInfo,
    /// Whether the responder is known to cache the prekey and the host judges a short Initial usable now, so it can
    /// be tried first. It also leaves short resends allowed until the host says otherwise
    /// ([`Initiator::set_short_until`]).
    pub peer_has_prekey: bool,
    /// A ticket for this peer and ALPN to resume with, if one is held.
    pub ticket: Option<Ticket>,
    /// This side's credit record; the peer receives it authenticated.
    pub credit: CreditRecord,
}

enum State {
    /// Waiting for the Reply (or a prekey reject, while `short`: the short Initial is still in use).
    Reply {
        short: bool,
        echo: [u8; 16],
    },
    /// Waiting for the resume Reply (or a resume reject).
    Resume {
        ck_psk: Secret<32>,
        aead: Aead,
        binder: [u8; 32],
        echo: [u8; 16],
    },
    /// Waiting for the host to decapsulate.
    Decap {
        aead: Aead,
        th1: [u8; 32],
        ss_x: Secret<32>,
        /// What the machine goes back to when the Reply fails to open: a forged or damaged Reply is dropped (the
        /// transcript before it is in `back_th`).
        back: Back,
    },
    /// Waiting for the host to sign.
    Sign {
        aead: Aead,
        hs: Secret<32>,
        ck1: Secret<32>,
        th3: [u8; 32],
    },
    Done,
    Failed,
}

/// The state before a Reply was taken in.
#[derive(Clone, Copy)]
struct Back {
    short: bool,
    echo: [u8; 16],
}

/// A resumption the machine stopped waiting for but still accepts a reply to.
struct Late {
    ck_psk: Secret<32>,
    aead: Aead,
    binder: [u8; 32],
    th: Transcript,
    seed: Secret<32>,
    remembered: CreditRecord,
}

/// The initiator side of the handshake.
pub struct Initiator {
    peer: NodeId,
    alpn: Alpn,
    scid: ConnId,
    identity: LocalIdentity,
    prekey: PrekeyInfo,
    offer: AeadSet,
    credit: CreditRecord,
    peer_credit: CreditRecord,
    remembered: CreditRecord,
    dcid: ConnId,
    seed: Secret<32>,
    e: [u8; 32],
    th: Transcript,
    /// The transcript as it was before the Reply that is waiting to be opened.
    back_th: Transcript,
    sends: u32,
    /// A resend may be the short Initial while the clock is below this.
    short_until: u64,
    late: Option<Late>,
    out: Outbox,
    inbuf: [u8; MAX_MESSAGE_LEN],
    inlen: usize,
    state: State,
}

impl core::fmt::Debug for Initiator {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Initiator")
            .field("peer", &self.peer)
            .finish_non_exhaustive()
    }
}

impl Initiator {
    /// Start a handshake: queue the first message (a resume Hello if `params.ticket` is usable, else an Initial).
    ///
    /// # Errors
    /// [`Failure::InvalidParameter`] for an invalid ALPN; [`Failure::Randomness`] if the generator refuses.
    pub fn new<P: Provider>(env: &mut Env<'_, P>, params: InitiatorParams<'_>) -> Result<Self, Failure> {
        let alpn = Alpn::new(params.alpn).ok_or(Failure::InvalidParameter)?;
        let mut this = Self {
            peer: params.peer,
            alpn,
            scid: params.scid,
            identity: *params.identity,
            prekey: params.prekey.clone(),
            offer: AeadSet::offer(env.provider.capabilities()),
            credit: params.credit,
            peer_credit: CreditRecord::NONE,
            remembered: CreditRecord::NONE,
            dcid: ConnId::default(),
            seed: Secret::new([0; 32]),
            e: [0; 32],
            th: Transcript::new(),
            back_th: Transcript::new(),
            sends: 0,
            // The host that knew the peer caches the prekey judged a short Initial fine when it dialed.
            short_until: if params.peer_has_prekey { u64::MAX } else { 0 },
            late: None,
            out: Outbox::new(),
            inbuf: [0; MAX_MESSAGE_LEN],
            inlen: 0,
            state: State::Failed,
        };
        let usable = params
            .ticket
            .filter(|t| t.expiry >= env.now && t.peer == this.peer && t.alpn == this.alpn);
        match usable {
            Some(t) => this.begin_resume(env, &t)?,
            None => this.begin_full(env, params.peer_has_prekey, false)?,
        }
        Ok(this)
    }

    /// The key operation the machine waits for, if any: the same request `poll_output` announced once, readable
    /// again until `on_key_response` answers it.
    pub fn pending_key_request(&self) -> Option<KeyRequest<'_>> {
        self.out.request()
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
    pub fn handle<P: Provider>(&mut self, env: &mut Env<'_, P>, input: &[u8]) -> Result<(), Failure> {
        if matches!(self.state, State::Failed) {
            return Err(Failure::Closed);
        }
        let result = self.dispatch(env, input);
        self.settle(result)
    }

    /// Deliver the host's answer to the key request last returned by `poll_output`.
    ///
    /// # Errors
    /// [`Failure::UnexpectedKeyResponse`] (nothing changes) if no request of that kind is outstanding; otherwise as
    /// [`Initiator::handle`].
    pub fn on_key_response<P: Provider>(&mut self, env: &mut Env<'_, P>, resp: KeyResponse<'_>) -> Result<(), Failure> {
        if matches!(self.state, State::Failed) {
            return Err(Failure::Closed);
        }
        let result = self.dispatch_key(env, resp);
        self.settle(result)
    }

    /// Answer the outstanding key request at once from software keys. Returns whether there was one.
    ///
    /// # Errors
    /// As [`Initiator::on_key_response`].
    pub fn answer_soft<P: Provider>(&mut self, env: &mut Env<'_, P>, keys: &SoftKeys<'_, P>) -> Result<bool, Failure> {
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let Some(resp) = self.out.answer_soft(env, keys, &mut sig) else {
            return Ok(false);
        };
        let result = self.on_key_response(env, resp);
        sig.zeroize();
        result.map(|()| true)
    }

    /// Allow short Initials in resends while `env.now` is below `until`: the host heard a validated UDP path lately,
    /// so a lost reject costs one round trip, not a carrier's. Resends are full Initials once the time has passed.
    pub const fn set_short_until(&mut self, until: u64) {
        self.short_until = until;
    }

    fn short_ok(&self, now: u64) -> bool {
        now < self.short_until
    }

    /// The host's loss timer fired: queue the outstanding flight again. A resent Initial is the short one while the
    /// host allows it ([`Initiator::set_short_until`]), whichever form the first send had, except on the sends 3, 6, 9
    /// and so on, which carry the full prekey. A resume Hello that reaches [`RESUME_TRIES`] sends is not sent
    /// again: a full Initial under the same destination id takes its place, and a late resume Reply still completes
    /// the resumed session. Once the Finish has gone out it is queued again until [`Initiator::shed`].
    ///
    /// # Errors
    /// [`Failure::Randomness`] if the fallback needs the generator and it refuses.
    pub fn retransmit<P: Provider>(&mut self, env: &mut Env<'_, P>) -> Result<(), Failure> {
        let result = match self.state {
            State::Reply { short: true, .. } => {
                self.sends = self.sends.saturating_add(1);
                self.write_initial(self.sends.is_multiple_of(FULL_EVERY) || !self.short_ok(env.now))
            }
            State::Resume { .. } => {
                self.sends = self.sends.saturating_add(1);
                if self.sends >= RESUME_TRIES {
                    self.fall_back(env)
                } else {
                    self.out.resend();
                    Ok(())
                }
            }
            State::Reply { short: false, .. } | State::Done => {
                self.sends = self.sends.saturating_add(1);
                self.out.resend();
                Ok(())
            }
            State::Decap { .. } | State::Sign { .. } | State::Failed => Ok(()),
        };
        self.settle(result)
    }

    /// Release what the handshake no longer needs once the transport knows the peer has the session (it received a
    /// 1-RTT packet): the Finish that could be sent again, and the copy of the Reply.
    pub fn shed(&mut self) {
        self.out.clear_message();
        self.inbuf.zeroize();
        self.inlen = 0;
        self.late = None;
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

    fn dispatch<P: Provider>(&mut self, env: &mut Env<'_, P>, input: &[u8]) -> Result<(), Failure> {
        match MessageType::of(input).map_err(Failure::Malformed)? {
            MessageType::Reply => self.on_reply(env, input),
            MessageType::PrekeyReject => self.on_prekey_reject(input),
            MessageType::ResumeReply => self.on_resume_reply(env, input),
            MessageType::ResumeReject => self.on_resume_reject(env, input),
            _ => Err(Failure::UnexpectedMessage),
        }
    }

    fn dispatch_key<P: Provider>(&mut self, env: &mut Env<'_, P>, resp: KeyResponse<'_>) -> Result<(), Failure> {
        let fits = matches!(
            (self.out.pending(), &resp),
            (Some(Pending::Decap { .. }), KeyResponse::SharedSecret(_))
                | (Some(Pending::Sign { .. }), KeyResponse::Signature(_))
                | (Some(_), KeyResponse::Failed)
        );
        if !fits {
            return Err(Failure::UnexpectedKeyResponse);
        }
        self.out.take_request();
        match resp {
            KeyResponse::SharedSecret(ss_k) => self.on_decapsulated(env, &ss_k),
            KeyResponse::Signature(sig) => self.on_signed(env, sig),
            KeyResponse::Failed => Err(Failure::KeyOperation),
        }
    }

    /// Fresh destination connection id (unless `keep_dcid`) and ephemeral key.
    fn fresh_ephemeral<P: Provider>(&mut self, env: &mut Env<'_, P>, keep_dcid: bool) -> Result<(), Failure> {
        if !keep_dcid {
            self.dcid = ConnId::new(&env.random::<16>()?).ok_or(Failure::InvalidParameter)?;
        }
        let mut seed = env.random::<32>()?;
        let p = env.provider;
        self.e = p.x25519_public(&p.x25519_secret(&seed));
        self.seed = Secret::new(seed);
        seed.zeroize();
        Ok(())
    }

    /// Start (or restart) a full handshake with the short or the full Initial. `keep_dcid` keeps the destination id
    /// of the Hello it replaces, so the Initial reaches the responder's session if the Hello got through.
    fn begin_full<P: Provider>(&mut self, env: &mut Env<'_, P>, short: bool, keep_dcid: bool) -> Result<(), Failure> {
        self.fresh_ephemeral(env, keep_dcid)?;
        self.th = initial_transcript(&InitialFields {
            version: VERSION,
            dcid: &self.dcid,
            scid: &self.scid,
            alpn: self.alpn.as_bytes(),
            offer: self.offer,
            e: &self.e,
            prekey_hash: &self.prekey.hash,
            credit: &self.credit,
        });
        self.sends = 1;
        self.write_initial(!short)?;
        self.state = State::Reply {
            short: true,
            echo: echo(&self.th.snapshot()),
        };
        Ok(())
    }

    fn write_initial(&mut self, full: bool) -> Result<(), Failure> {
        let (prekey, form) = if full {
            (PrekeyField::Full(&self.prekey.encaps_key), InitialForm::Full)
        } else {
            (PrekeyField::Hash(&self.prekey.hash), InitialForm::Short)
        };
        let initial = Initial {
            version: VERSION,
            dcid: self.dcid,
            scid: self.scid,
            alpn: self.alpn.as_bytes(),
            aead_offer: self.offer,
            e: self.e,
            prekey,
            credit: self.credit,
        };
        self.out
            .build(min_initial_len(form, self.peer.alg), |w| initial.write(w))
    }

    /// Start a resumption with `ticket`: queue the Hello and the 0-RTT keys.
    fn begin_resume<P: Provider>(&mut self, env: &mut Env<'_, P>, ticket: &Ticket) -> Result<(), Failure> {
        self.fresh_ephemeral(env, false)?;
        let th = hello_transcript(&HelloFields {
            version: VERSION,
            alpn: self.alpn.as_bytes(),
            dcid: &self.dcid,
            scid: &self.scid,
            aead: ticket.aead,
            tid: &ticket.tid,
            e: &self.e,
            credit: &self.credit,
        });
        let th_hello = th.snapshot();
        let binder = binder(&ticket.psk, &th_hello);
        let hello = ResumeHello {
            version: VERSION,
            dcid: self.dcid,
            scid: self.scid,
            alpn: self.alpn.as_bytes(),
            aead: ticket.aead,
            tid: ticket.tid,
            e: self.e,
            binder,
            credit: self.credit,
        };
        self.remembered = ticket.credit;
        self.sends = 1;
        self.out.build(0, |w| hello.write(w))?;
        let ck_psk = psk_chain(&ticket.psk);
        self.out.early = Some(EarlyKeys {
            aead: ticket.aead,
            secret: early_secret(&ck_psk, &th_hello),
        });
        self.th = th;
        self.state = State::Resume {
            ck_psk,
            aead: ticket.aead,
            binder,
            echo: echo(&th_hello),
        };
        Ok(())
    }

    fn on_prekey_reject(&mut self, input: &[u8]) -> Result<(), Failure> {
        let State::Reply { short: true, echo } = self.state else {
            return Err(Failure::UnexpectedMessage);
        };
        let reject = Reject::parse(input, MessageType::PrekeyReject).map_err(Failure::Malformed)?;
        if !ct_eq(&reject.echo, &echo) {
            return Err(Failure::UnexpectedMessage);
        }
        self.write_initial(true)?;
        self.state = State::Reply { short: false, echo };
        Ok(())
    }

    fn on_resume_reject<P: Provider>(&mut self, env: &mut Env<'_, P>, input: &[u8]) -> Result<(), Failure> {
        let State::Resume { echo, .. } = self.state else {
            return Err(Failure::UnexpectedMessage);
        };
        let reject = Reject::parse(input, MessageType::ResumeReject).map_err(Failure::Malformed)?;
        if !ct_eq(&reject.echo, &echo) {
            return Err(Failure::UnexpectedMessage);
        }
        self.out.early = None;
        self.late = None;
        self.begin_full(env, false, false)?;
        self.out.set_resume_rejected();
        Ok(())
    }

    /// The Hello went unanswered: queue a full Initial under the same destination id and keep what a late resume
    /// Reply needs. The caller is told, as for a reject, so it sends its early data again under the 1-RTT keys.
    fn fall_back<P: Provider>(&mut self, env: &mut Env<'_, P>) -> Result<(), Failure> {
        let State::Resume {
            ck_psk, aead, binder, ..
        } = mem::replace(&mut self.state, State::Failed)
        else {
            return Err(Failure::UnexpectedMessage);
        };
        self.late = Some(Late {
            ck_psk,
            aead,
            binder,
            th: mem::take(&mut self.th),
            seed: mem::replace(&mut self.seed, Secret::new([0; 32])),
            remembered: self.remembered,
        });
        self.begin_full(env, false, true)?;
        self.out.set_resume_rejected();
        Ok(())
    }

    fn on_reply<P: Provider>(&mut self, env: &mut Env<'_, P>, input: &[u8]) -> Result<(), Failure> {
        if !matches!(self.state, State::Reply { .. }) {
            return Err(Failure::UnexpectedMessage);
        }
        let reply = Reply::parse(input).map_err(Failure::Malformed)?;
        let State::Reply { short, echo } = self.state else {
            return Err(Failure::UnexpectedMessage);
        };
        if !self.offer.contains(reply.aead) {
            return Err(Failure::NoCommonAead);
        }
        let p = env.provider;
        let ss_x = p
            .x25519_dh(&p.x25519_secret(self.seed.expose()), &reply.e)
            .map_err(|_| Failure::InvalidPeerKey)?;
        self.inbuf
            .get_mut(..input.len())
            .ok_or(Failure::InvalidParameter)?
            .copy_from_slice(input);
        self.inlen = input.len();
        let back = Back { short, echo };
        self.back_th = self.th.clone();
        absorb_reply(&mut self.th, &reply.scid, reply.aead, &reply.e, reply.ct);
        self.out.set_request(Pending::Decap {
            key: self.prekey.handle,
            ct: *reply.ct,
        });
        self.state = State::Decap {
            aead: reply.aead,
            th1: self.th.snapshot(),
            ss_x,
            back,
        };
        Ok(())
    }

    fn on_decapsulated<P: Provider>(&mut self, env: &mut Env<'_, P>, ss_k: &Secret<32>) -> Result<(), Failure> {
        let State::Decap { aead, th1, ss_x, back } = mem::replace(&mut self.state, State::Failed) else {
            return Err(Failure::UnexpectedKeyResponse);
        };
        let hs = handshake_keys(ss_k, &ss_x, &th1);
        let reply = Reply::parse(self.inbuf.get(..self.inlen).unwrap_or_default()).map_err(Failure::BadPayload)?;
        let opened = match open_handshake(env.provider, aead, &hs.responder, &th1, reply.sealed) {
            Ok(o) => o,
            Err(f) => {
                if f == Failure::Authentication {
                    // A damaged or forged Reply proves nothing: drop it and wait for the next one.
                    self.th = self.back_th.clone();
                    self.state = State::Reply {
                        short: back.short,
                        echo: back.echo,
                    };
                    self.inbuf.zeroize();
                    self.inlen = 0;
                }
                return Err(f);
            }
        };
        let ids = IdSig::parse(opened.as_slice(), true).map_err(Failure::BadPayload)?;
        let responder = NodeId::from_public(ids.alg, ids.public_key).map_err(|_| Failure::InvalidPeerKey)?;
        if responder != self.peer {
            return Err(Failure::WrongPeer);
        }
        absorb_identity(&mut self.th, ids.alg, ids.public_key);
        let credit = ids
            .credit
            .ok_or(Failure::BadPayload(WireError::Unexpected("credit record")))?;
        absorb_credit(&mut self.th, credit);
        self.peer_credit = credit;
        let th2 = self.th.snapshot();
        verify(
            ids.alg,
            ids.public_key,
            &signature_message(labels::SIGNATURE_RESPONDER, &th2),
            ids.signature,
        )
        .map_err(|_| Failure::BadSignature)?;
        self.th.absorb("sig", ids.signature);
        let th3 = self.th.snapshot();
        absorb_identity(&mut self.th, self.identity.alg(), self.identity.public_key());
        self.out.set_request(Pending::Sign {
            key: self.identity.key(),
            alg: self.identity.alg(),
            msg: signature_message(labels::SIGNATURE_INITIATOR, &self.th.snapshot()),
        });
        self.state = State::Sign {
            aead,
            hs: hs.initiator,
            ck1: hs.ck1,
            th3,
        };
        Ok(())
    }

    fn on_signed<P: Provider>(&mut self, env: &mut Env<'_, P>, signature: &[u8]) -> Result<(), Failure> {
        let State::Sign { aead, hs, ck1, th3 } = mem::replace(&mut self.state, State::Failed) else {
            return Err(Failure::UnexpectedKeyResponse);
        };
        if signature.len() != self.identity.alg().signature_len() {
            return Err(Failure::KeyOperation);
        }
        let sealed = seal_id_sig(
            env.provider,
            aead,
            &hs,
            &th3,
            (self.identity.alg(), self.identity.public_key()),
            signature,
            None,
        )?;
        self.th.absorb("sig", signature);
        let secrets = application_secrets(&ck1, &self.th.snapshot());
        self.out.build(0, |w| {
            Finish {
                sealed: sealed.as_slice(),
            }
            .write(w)
        })?;
        self.out.established = Some(Established {
            peer: self.peer,
            alpn: self.alpn,
            traffic: Traffic {
                aead,
                send: secrets.initiator,
                recv: secrets.responder,
            },
            resume: secrets.resume,
            tickets: TicketBatch::new(),
            resumed: false,
            peer_credit: self.peer_credit,
            local_credit: self.credit,
            remembered_credit: CreditRecord::NONE,
            cid_secret: secrets.cid,
        });
        self.inbuf.zeroize();
        self.inlen = 0;
        self.state = State::Done;
        Ok(())
    }

    fn on_resume_reply<P: Provider>(&mut self, env: &mut Env<'_, P>, input: &[u8]) -> Result<(), Failure> {
        let reply = ResumeReply::parse(input).map_err(Failure::Malformed)?;
        if matches!(self.state, State::Resume { .. }) {
            let State::Resume {
                ck_psk,
                aead,
                binder,
                echo,
            } = mem::replace(&mut self.state, State::Failed)
            else {
                return Err(Failure::UnexpectedMessage);
            };
            let (seed, remembered) = (self.seed.clone(), self.remembered);
            let th = mem::take(&mut self.th);
            let mut tried = th.clone();
            let secrets = match open_resume_reply(env, &seed, &ck_psk, &binder, &mut tried, &reply) {
                Ok(s) => s,
                Err(f) => {
                    // A reply that does not confirm is dropped; the Hello is still outstanding.
                    self.th = th;
                    self.state = State::Resume {
                        ck_psk,
                        aead,
                        binder,
                        echo,
                    };
                    return Err(f);
                }
            };
            self.th = tried;
            self.finish_resume(aead, secrets, reply, remembered);
            return Ok(());
        }
        // The Hello was given up for a full handshake: its reply may still come, and it only counts if it
        // authenticates against the Hello's own transcript. A forgery changes nothing.
        let (State::Reply { .. } | State::Decap { .. } | State::Sign { .. }) = self.state else {
            return Err(Failure::UnexpectedMessage);
        };
        let Some(late) = self.late.as_ref() else {
            return Err(Failure::UnexpectedMessage);
        };
        let mut th = late.th.clone();
        let secrets = open_resume_reply(env, &late.seed, &late.ck_psk, &late.binder, &mut th, &reply)
            .map_err(|_| Failure::UnexpectedMessage)?;
        let (aead, remembered) = (late.aead, late.remembered);
        self.late = None;
        self.out.take_request();
        self.finish_resume(aead, secrets, reply, remembered);
        Ok(())
    }

    /// Complete a resumption whose reply authenticated.
    fn finish_resume(&mut self, aead: Aead, secrets: AppSecrets, reply: ResumeReply, remembered: CreditRecord) {
        self.out.established = Some(Established {
            peer: self.peer,
            alpn: self.alpn,
            traffic: Traffic {
                aead,
                send: secrets.initiator,
                recv: secrets.responder,
            },
            resume: secrets.resume,
            tickets: reply.tickets,
            resumed: true,
            peer_credit: reply.credit,
            local_credit: self.credit,
            remembered_credit: remembered,
            cid_secret: secrets.cid,
        });
        // The Hello was answered: a later loss timer has nothing to send again.
        self.out.clear_message();
        self.inbuf.zeroize();
        self.inlen = 0;
        self.state = State::Done;
    }
}

/// Derive the session secrets of a resumption from its reply and check the confirmation tag.
fn open_resume_reply<P: Provider>(
    env: &Env<'_, P>,
    seed: &Secret<32>,
    ck_psk: &Secret<32>,
    binder: &[u8; 32],
    th: &mut Transcript,
    reply: &ResumeReply,
) -> Result<AppSecrets, Failure> {
    let p = env.provider;
    let ss_x = p
        .x25519_dh(&p.x25519_secret(seed.expose()), &reply.e)
        .map_err(|_| Failure::InvalidPeerKey)?;
    absorb_resume_reply(th, binder, &reply.scid, &reply.e, reply.credit);
    let ck1 = chain(ck_psk, ss_x.expose());
    let secrets = application_secrets(&ck1, &th.snapshot());
    let mut tickets = [0u8; 81];
    let n = reply.tickets.encode(&mut tickets).map_err(Failure::BadPayload)?;
    let expected = confirmation(&secrets.confirm, th, tickets.get(..n).unwrap_or_default());
    if ct_eq(&expected, &reply.confirm) {
        Ok(secrets)
    } else {
        Err(Failure::Authentication)
    }
}
