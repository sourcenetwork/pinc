//! The output queue shared by both state machines.
//!
//! Invariants: it holds at most one outgoing message (the last flight, kept so it can be sent again), at most one
//! outstanding key request, and at most one of each event. `poll` hands them out in a fixed order (key request,
//! message, early keys, established, failure) and each exactly once; a failure discards everything else queued.

use vinc_crypto::IdentityAlg;
use vinc_crypto::Provider;
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_crypto::provider::KEM_CIPHERTEXT_LEN;
use vinc_wire::{WireError, Writer};

use crate::error::Failure;
use crate::ids::KeyHandle;
use crate::keys::{KeyRequest, KeyResponse, SoftKeys};
use crate::message::MAX_MESSAGE_LEN;
use crate::schedule::SIGNATURE_MESSAGE_LEN;
use crate::session::{EarlyKeys, Env, Established, Event, Output};

/// An outstanding key request, owned.
#[allow(
    clippy::large_enum_variant,
    reason = "the request lives inline; boxing would allocate"
)]
pub(crate) enum Pending {
    Sign {
        key: KeyHandle,
        alg: IdentityAlg,
        msg: [u8; SIGNATURE_MESSAGE_LEN],
    },
    Decap {
        key: KeyHandle,
        ct: [u8; KEM_CIPHERTEXT_LEN],
    },
}

impl Pending {
    fn as_request(&self) -> KeyRequest<'_> {
        match self {
            Self::Sign { key, alg, msg } => KeyRequest::Sign {
                key: *key,
                alg: *alg,
                message: msg,
            },
            Self::Decap { key, ct } => KeyRequest::Decapsulate { key: *key, ct },
        }
    }
}

pub(crate) struct Outbox {
    msg: [u8; MAX_MESSAGE_LEN],
    len: usize,
    min_len: usize,
    send: bool,
    request: Option<Pending>,
    announced: bool,
    pub early: Option<EarlyKeys>,
    pub established: Option<Established>,
    resume_rejected: bool,
    failed: Option<Failure>,
}

impl Outbox {
    pub(crate) const fn new() -> Self {
        Self {
            msg: [0; MAX_MESSAGE_LEN],
            len: 0,
            min_len: 0,
            send: false,
            request: None,
            announced: false,
            early: None,
            established: None,
            resume_rejected: false,
            failed: None,
        }
    }

    /// Write a message into the buffer and queue it for sending.
    pub(crate) fn build(
        &mut self,
        min_len: usize,
        write: impl FnOnce(&mut Writer<'_>) -> Result<(), WireError>,
    ) -> Result<(), Failure> {
        let mut w = Writer::new(&mut self.msg);
        write(&mut w).map_err(Failure::BadPayload)?;
        self.len = w.written().len();
        self.min_len = min_len;
        self.send = true;
        Ok(())
    }

    /// Forget the message in the buffer: there is nothing left to send again.
    pub(crate) const fn clear_message(&mut self) {
        self.len = 0;
        self.send = false;
    }

    /// The length of the message in the buffer.
    pub(crate) const fn len(&self) -> usize {
        self.len
    }

    /// Queue the message in the buffer again.
    pub(crate) const fn resend(&mut self) {
        self.send = self.len > 0;
    }

    pub(crate) fn set_request(&mut self, req: Pending) {
        self.request = Some(req);
        self.announced = false;
    }

    pub(crate) const fn pending(&self) -> Option<&Pending> {
        self.request.as_ref()
    }

    pub(crate) const fn take_request(&mut self) -> Option<Pending> {
        self.announced = false;
        self.request.take()
    }

    pub(crate) const fn set_resume_rejected(&mut self) {
        self.resume_rejected = true;
    }

    /// Replace everything queued with the failure.
    pub(crate) fn fail(&mut self, failure: Failure) {
        self.send = false;
        self.request = None;
        self.early = None;
        self.established = None;
        self.resume_rejected = false;
        self.failed = Some(failure);
    }

    /// Answer the outstanding request, if any, from software keys.
    pub(crate) fn answer_soft<'b, P: Provider>(
        &self,
        env: &mut Env<'_, P>,
        keys: &SoftKeys<'_, P>,
        sig_buf: &'b mut [u8; MAX_SIGNATURE_LEN],
    ) -> Option<KeyResponse<'b>> {
        let req = self.request.as_ref()?.as_request();
        Some(keys.answer(env, &req, sig_buf))
    }

    pub(crate) fn poll(&mut self) -> Option<Output<'_>> {
        if !self.announced && self.request.is_some() {
            self.announced = true;
            return self.request.as_ref().map(|p| Output::Key(p.as_request()));
        }
        if self.send {
            self.send = false;
            let data = self.msg.get(..self.len)?;
            return Some(Output::Send {
                data,
                min_len: self.min_len,
            });
        }
        if let Some(e) = self.early.take() {
            return Some(Output::Event(Event::EarlyKeys(e)));
        }
        if self.resume_rejected {
            self.resume_rejected = false;
            return Some(Output::Event(Event::ResumeRejected));
        }
        if let Some(e) = self.established.take() {
            return Some(Output::Event(Event::Established(e)));
        }
        self.failed.take().map(|f| Output::Event(Event::Failed(f)))
    }
}
