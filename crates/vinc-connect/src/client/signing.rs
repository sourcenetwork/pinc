//! Signatures the layer needs from the node's identity key: its record, its sleep notices and its beacons.
//!
//! The layer never holds a private key. Each signature is a [`KeyRequest::Sign`] the host answers from wherever the
//! key lives (a software key, or a TPM through a `KeyHost`), exactly as it answers the carrier handshake
//! ([`Connectivity::key_request`]) and the endpoint's own requests. The host calls [`Connectivity::sign_request`]
//! after any call into the layer and answers with [`Connectivity::sign_response`].
//!
//! One request is outstanding at a time; the others wait as flags (a sleep notice per relay, the record, a beacon),
//! in that order of priority, so a suspending node's notices are never held behind a record.
//!
//! Invariants: a signature of the wrong length for the identity is refused, never sent; a refused or failed
//! signature is reported as [`Notice::SignFailed`] and the work it served is retried at its next due time, except a
//! sleep notice (the carriers close anyway); the layer closes its carriers for a suspension only after every notice
//! was signed or failed.

use core::net::SocketAddr;

use vinc_crypto::Provider;
use vinc_security::{KeyRequest, KeyResponse};

use super::conn::{Connectivity, Notice};
use crate::carrier::Frame;
use crate::local;
use crate::record::{self, MAX_ADDRS, MAX_RECORD_LEN, RecordFields};
use crate::relay::datagram::Datagram;
use crate::relay::{rule, sleep};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Record,
    Beacon,
    Sleep,
}

struct Job {
    kind: Kind,
    relay: usize,
    buf: [u8; MAX_RECORD_LEN],
    signed: usize,
    msg: [u8; sleep::MSG_LEN],
}

/// The signing work of a node.
pub(super) struct Signing {
    job: Option<Job>,
    record: bool,
    beacon: bool,
    sleep: u32,
    sleep_ms: u64,
    suspending: bool,
    close_at: Option<u64>,
    pub(super) wall_ms: Option<u64>,
}

impl Signing {
    pub(super) const fn new() -> Self {
        Self {
            job: None,
            record: false,
            beacon: false,
            sleep: 0,
            sleep_ms: 0,
            suspending: false,
            close_at: None,
            wall_ms: None,
        }
    }

    pub(super) const fn record_wanted(&self) -> bool {
        self.record || matches!(&self.job, Some(j) if matches!(j.kind, Kind::Record))
    }

    pub(super) const fn want_record(&mut self) {
        self.record = true;
    }

    pub(super) const fn want_beacon(&mut self) {
        self.beacon = true;
    }

    /// A suspension begins: owe a notice to every relay in `relays`.
    pub(super) const fn begin_suspend(&mut self, relays: u32, wall_ms: u64) {
        self.sleep = relays;
        self.sleep_ms = wall_ms;
        self.suspending = true;
    }

    /// The node resumed before its notices were signed: they are no longer wanted.
    pub(super) fn cancel_suspend(&mut self) {
        self.sleep = 0;
        self.suspending = false;
        self.close_at = None;
        if self.job.as_ref().is_some_and(|j| j.kind == Kind::Sleep) {
            self.job = None;
        }
    }
}

impl<P: Provider, const R: usize, const PEERS: usize> Connectivity<P, R, PEERS> {
    /// The signature the layer waits for, if any. Answer with [`Connectivity::sign_response`].
    pub fn sign_request(&self) -> Option<KeyRequest<'_>> {
        let j = self.sign.job.as_ref()?;
        let message = if j.kind == Kind::Sleep {
            j.msg.as_slice()
        } else {
            j.buf.get(..j.signed)?
        };
        Some(KeyRequest::Sign {
            key: self.identity.key(),
            alg: self.identity.alg(),
            message,
        })
    }

    /// Answer the signature request: the signature of the identity key over the request's message.
    pub fn sign_response(&mut self, now: u64, resp: KeyResponse<'_>) {
        self.clock = self.clock.max(now);
        let Some(mut job) = self.sign.job.take() else { return };
        let ok = match resp {
            KeyResponse::Signature(sig) if sig.len() == self.identity.alg().signature_len() => {
                self.complete(now, &mut job, sig)
            }
            _ => false,
        };
        if !ok {
            self.notice(Notice::SignFailed);
            // The work is tried again at its next due time; a failed record waits a retry period.
            if job.kind == Kind::Record {
                self.next_publish = now.saturating_add(super::netcheck::HOME_RETRY_NS);
            }
        }
        self.start_jobs(now);
        self.maybe_close_for_suspend(now);
    }

    fn complete(&mut self, now: u64, job: &mut Job, sig: &[u8]) -> bool {
        match job.kind {
            Kind::Record => {
                let Ok(len) = record::finish(&mut job.buf, job.signed, sig) else {
                    return false;
                };
                let frame = Frame::Publish {
                    record: job.buf.get(..len).unwrap_or_default(),
                };
                if self.frame_to(now, job.relay, &frame) {
                    self.next_publish = now.saturating_add(rule::RECORD_REPUBLISH_NS);
                } else {
                    // The carrier went away meanwhile: publish again when it opens.
                    self.next_publish = now;
                }
                true
            }
            Kind::Beacon => {
                let Ok(len) = local::finish(&mut job.buf, job.signed, sig) else {
                    return false;
                };
                let group = SocketAddr::new(
                    if self.v6 {
                        core::net::IpAddr::V6(local::GROUP_V6)
                    } else {
                        core::net::IpAddr::V4(local::GROUP_V4)
                    },
                    local::PORT,
                );
                self.enqueue_raw(group, job.buf.get(..len).unwrap_or_default());
                true
            }
            Kind::Sleep => {
                let Ok(len) = sleep::finish(&mut job.buf, job.signed, sig) else {
                    return false;
                };
                let Some(udp) = self.relay_cfg(job.relay).and_then(|c| c.udp) else {
                    return false;
                };
                let d = Datagram::Sleep {
                    notice: job.buf.get(..len).unwrap_or_default(),
                };
                // Twice, because a mobile uplink loses datagrams.
                for _ in 0..2 {
                    self.enqueue_udp_pub(udp, &d);
                }
                true
            }
        }
    }

    /// Prepare the next signature, if none is outstanding and some work waits.
    pub(super) fn start_jobs(&mut self, now: u64) {
        if self.sign.job.is_some() {
            return;
        }
        let Some(wall_ms) = self.sign.wall_ms else { return };
        if self.sign.sleep != 0 {
            let i = self.sign.sleep.trailing_zeros() as usize;
            self.sign.sleep &= !(1 << i);
            if let Some(job) = self.sleep_job(i) {
                self.sign.job = Some(job);
            } else {
                self.start_jobs(now);
            }
            return;
        }
        if self.sign.record {
            self.sign.record = false;
            match self.record_job(wall_ms) {
                Some(job) => self.sign.job = Some(job),
                None => self.next_publish = now.saturating_add(super::netcheck::HOME_RETRY_NS),
            }
            return;
        }
        if self.sign.beacon {
            self.sign.beacon = false;
            self.sign.job = self.beacon_job(wall_ms);
        }
    }

    fn blank(kind: Kind, relay: usize) -> Job {
        Job {
            kind,
            relay,
            buf: [0; MAX_RECORD_LEN],
            signed: 0,
            msg: [0; sleep::MSG_LEN],
        }
    }

    fn sleep_job(&self, relay: usize) -> Option<Job> {
        let cfg = self.relay_cfg(relay)?;
        let mut job = Self::blank(Kind::Sleep, relay);
        job.signed = sleep::prepare(&self.me, self.identity.public_key(), self.sign.sleep_ms, &mut job.buf).ok()?;
        job.msg = sleep::message(&cfg.id, &self.me, self.sign.sleep_ms).ok()?;
        Some(job)
    }

    fn record_job(&self, wall_ms: u64) -> Option<Job> {
        let home = self.net.home()?;
        let class = self.class?;
        let home_id = self.relay_cfg(home)?.id;
        let mut addrs = [self.me_addr_pub(); MAX_ADDRS];
        let n = self.candidates(&mut addrs);
        let fields = RecordFields {
            home: home_id,
            seq: wall_ms,
            reach: class,
            addrs: addrs.get(..n).unwrap_or_default(),
            hints: &[],
        };
        let mut job = Self::blank(Kind::Record, home);
        job.signed = record::prepare(&self.me, self.identity.public_key(), &fields, &mut job.buf).ok()?;
        Some(job)
    }

    fn beacon_job(&self, wall_ms: u64) -> Option<Job> {
        let mut local = [self.me_addr_pub(); MAX_ADDRS];
        let n = self.candidates(&mut local).min(local::MAX_ADDRS);
        let mut job = Self::blank(Kind::Beacon, 0);
        job.signed = local::prepare(
            &self.me,
            self.identity.public_key(),
            wall_ms,
            local.get(..n).unwrap_or_default(),
            &[],
            &mut job.buf,
        )
        .ok()?;
        Some(job)
    }

    /// The suspension's notices are all signed: the carriers close one tick later, so what the endpoint sent as the
    /// node went to sleep (its sleep announcements to the peers) leaves on them first.
    pub(super) fn maybe_close_for_suspend(&mut self, now: u64) {
        if self.sign.suspending && self.sign.sleep == 0 && self.sign.job.is_none() && self.sign.close_at.is_none() {
            self.sign.close_at = Some(now.saturating_add(1));
        }
    }

    /// Close the carriers of a suspending node once its tick has come.
    pub(super) fn close_for_suspend(&mut self, now: u64) {
        if self.sign.close_at.is_some_and(|t| now >= t) {
            self.sign.close_at = None;
            self.sign.suspending = false;
            for i in 0..R {
                if self
                    .rly
                    .get(i)
                    .is_some_and(|r| r.link.state() != super::link::State::Down)
                {
                    self.close_pub(i);
                }
            }
        }
    }

    /// When the carriers of a suspending node close, if they wait for it.
    pub(super) const fn close_deadline(&self) -> Option<u64> {
        self.sign.close_at
    }
}
