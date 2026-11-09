//! The receiving side of a delay-tolerant transfer: an offer is checked and charged, symbols are verified into a
//! partial bundle, and a whole bundle is opened (at its destination) or taken into custody and acknowledged.
//!
//! Invariants: the ledger is charged the full size of a bundle before its buffer exists; a symbol is kept only after
//! it hashed to the signed root; a refusal ends the transfer and names the reason.

use alloc::vec::Vec;

use vinc_core::SessionId;
use vinc_dag::ranges::VerifiedRanges;
use vinc_dtn::DtnError as DtnLibError;
use vinc_dtn::bundle::Reception;
use vinc_dtn::custody::{CustodyAck, Incoming};
use vinc_dtn::forward::{Held, Input};
use vinc_dtn::head::{BundleId, SignedHead};
use vinc_dtn::seal::decapsulate;
use vinc_dtn::store::{Class, Key, Space};
use vinc_transport::stream::StreamId;

use crate::apps::{Apps, DtnApp, ServeSource};
use crate::config::Store;
use crate::dtn::{DStream, Dtn, Partial, Role, RxCtx, Stop};
use crate::dtn_wire::{self as wire, Refusal};
use crate::ep::Ep;
use crate::event::NodeEvent;
use crate::node::Node;
use crate::trace::{NodeTrace, btag, tag};

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: vinc_crypto::Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: ServeSource<A::Values>,
{
    /// A holder offered a bundle: check it, charge it, and keep a place for its symbols.
    pub(crate) fn dtn_offered(&mut self, session: SessionId, stream: StreamId, body: &[u8]) -> Result<RxCtx, Stop> {
        let wall = self.io.wall_ms();
        let Some(peer) = self.io.lsess.get(&session).map(|s| s.peer) else {
            return Err(Stop::Break);
        };
        let from = self.io.full_id(&peer);
        let Some((copies, rest)) = wire::take_u16(body) else {
            return Err(Stop::Break);
        };
        let Some((offer, head)) = wire::take_u64(rest) else {
            return Err(Stop::Break);
        };
        let Ok(signed) = SignedHead::decode(head) else {
            return Err(Stop::Break);
        };
        let h = *signed.head();
        let id = h.id;
        let refuse = |why| Stop::Refuse(id, why);
        if signed.verify().is_err() {
            return Err(refuse(Refusal::Malformed));
        }
        if h.is_expired(wall) {
            return Err(refuse(Refusal::Expired));
        }
        let layout = h.layout().map_err(|_| refuse(Refusal::Malformed))?;
        let Some(d) = self.dtn.as_deref_mut() else {
            return Err(Stop::Break);
        };
        let ctx = RxCtx {
            bundle: id,
            from,
            copies,
            offer,
            ask: None,
        };
        // Already whole here: take custody again (a repeated offer or a hand-back) and acknowledge.
        if d.heads.contains_key(&id) || d.received.contains_key(&id) {
            return Err(self.dtn_complete(session, stream, &ctx, &signed, None));
        }
        if !d.partials.contains_key(&id) {
            let total = layout.total_len();
            let mut evicted: Vec<Key> = Vec::new();
            let admitted = d
                .led
                .admit(id.store_key(), total, Class::Transit, h.expires_at(), wall, |e| {
                    evicted.push(e.key);
                });
            let app = self.apps.dtn();
            for k in evicted.iter().filter(|k| k.space == Space::DTN) {
                d.forget(app, wall, &BundleId(k.id));
            }
            if admitted.is_err() {
                return Err(refuse(Refusal::NoRoom));
            }
            let sealed_len = usize::try_from(total).ok();
            let outboard_len = layout.outboard_len().ok().and_then(|n| usize::try_from(n).ok());
            let (Some(sealed_len), Some(outboard_len)) = (sealed_len, outboard_len) else {
                let _ = d.led.release(&id.store_key());
                return Err(refuse(Refusal::Malformed));
            };
            d.partials.insert(
                id,
                Partial {
                    signed,
                    sealed: alloc::vec![0; sealed_len],
                    outboard: alloc::vec![0; outboard_len],
                    have: VerifiedRanges::new(),
                    cursor: 0,
                },
            );
        }
        Ok(ctx)
    }

    /// Ask for the next run of symbols, or finish the bundle if every data symbol is held.
    pub(crate) fn dtn_advance(
        &mut self,
        session: SessionId,
        stream: StreamId,
        rx: &mut Option<RxCtx>,
    ) -> Result<(), Stop> {
        let Some(ctx) = rx.as_mut() else {
            return Err(Stop::Break);
        };
        let Some(d) = self.dtn.as_deref_mut() else {
            return Err(Stop::Break);
        };
        let Some(p) = d.partials.get_mut(&ctx.bundle) else {
            return Err(Stop::Break);
        };
        let Ok(layout) = p.signed.head().layout() else {
            return Err(Stop::Break);
        };
        if let Some((first, end)) = Dtn::want(&layout, p) {
            ctx.ask = Some((first, end));
            wire::start(&mut d.tx, wire::WANT);
            d.tx.extend_from_slice(&first.to_be_bytes());
            d.tx.extend_from_slice(&end.to_be_bytes());
            wire::finish(&mut d.tx);
            return if self.io.write(session, stream, &d.tx) {
                Ok(())
            } else {
                Err(Stop::Break)
            };
        }
        ctx.ask = None;
        let ctx = *ctx;
        Err(self.dtn_finish(session, stream, &ctx))
    }

    /// A DATA frame: the symbols asked for, with their proof.
    pub(crate) fn dtn_data(
        &mut self,
        session: SessionId,
        stream: StreamId,
        rx: &mut Option<RxCtx>,
        body: &[u8],
    ) -> Result<(), Stop> {
        let wall = self.io.wall_ms();
        let Some(ctx) = rx.as_mut() else {
            return Err(Stop::Break);
        };
        let id = ctx.bundle;
        let (Some((first, rest)), Some(d)) = (wire::take_u64(body), self.dtn.as_deref_mut()) else {
            return Err(Stop::Break);
        };
        let Some((end, proof)) = wire::take_u64(rest) else {
            return Err(Stop::Break);
        };
        if ctx.ask != Some((first, end)) {
            return Err(Stop::Break);
        }
        let Some(p) = d.partials.get_mut(&id) else {
            return Err(Stop::Break);
        };
        let have = core::mem::take(&mut p.have);
        let fed = match Reception::resume(&p.signed, &mut p.sealed, have, wall) {
            Ok(mut r) => {
                let res = r.feed(first..end, proof);
                let kept = r.have().clone();
                p.have = kept;
                res
            }
            Err(e) => Err(e),
        };
        if let Err(e) = fed {
            return Err(Stop::Refuse(
                id,
                if e == DtnLibError::Expired {
                    Refusal::Expired
                } else {
                    Refusal::BadProof
                },
            ));
        }
        self.io.trace(NodeTrace::DtnSymbols {
            bundle: btag(&id.0),
            peer: tag(&ctx.from.bytes),
            first,
        });
        self.dtn_advance(session, stream, rx)
    }

    /// Every data symbol is held: rebuild the rest, check the root, and take the bundle in.
    fn dtn_finish(&mut self, session: SessionId, stream: StreamId, ctx: &RxCtx) -> Stop {
        let wall = self.io.wall_ms();
        let Some(d) = self.dtn.as_deref_mut() else {
            return Stop::Break;
        };
        let id = ctx.bundle;
        let Some(mut p) = d.partials.remove(&id) else {
            return Stop::Break;
        };
        let refuse = |why| Stop::Refuse(id, why);
        let signed = p.signed.clone();
        let Ok(layout) = signed.head().layout() else {
            let _ = d.led.release(&id.store_key());
            return refuse(Refusal::Malformed);
        };
        let have = core::mem::take(&mut p.have);
        let Ok(mut rx) = Reception::resume(&p.signed, &mut p.sealed, have, wall) else {
            let _ = d.led.release(&id.store_key());
            return refuse(Refusal::Expired);
        };
        let Ok(scratch_len) = rx.scratch_len() else {
            let _ = d.led.release(&id.store_key());
            return refuse(Refusal::Malformed);
        };
        let mut scratch = alloc::vec![0u8; scratch_len];
        if let Err(e) = rx.finish(&mut p.outboard, &mut scratch) {
            let _ = d.led.release(&id.store_key());
            return refuse(if e == DtnLibError::Inconsistent {
                Refusal::Inconsistent
            } else {
                Refusal::Malformed
            });
        }
        self.io.trace(NodeTrace::DtnComplete {
            bundle: btag(&id.0),
            peer: tag(&ctx.from.bytes),
        });
        if signed.head().destination.bytes == self.ident.bytes {
            // This node is the destination: open the payload.
            let Some(keys) = self.apps.dtn().recipient() else {
                let _ = d.led.release(&id.store_key());
                return refuse(Refusal::CannotOpen);
            };
            let opened =
                decapsulate(&self.prov, keys.own, keys.kem_dk, keys.x25519, signed.head()).and_then(|cipher| {
                    let padded = usize::try_from(layout.padded_len()).map_err(|_| DtnLibError::Buffer)?;
                    let mut out = alloc::vec![0u8; padded];
                    let n = rx.open(&self.prov, &cipher, &mut out)?;
                    out.truncate(n);
                    Ok(out)
                });
            let _ = d.led.release(&id.store_key());
            let Ok(payload) = opened else {
                return refuse(Refusal::CannotOpen);
            };
            d.received.insert(id, signed.head().expires_at());
            self.io.emit(NodeEvent::DtnReceived {
                bundle: id.0,
                source: signed.head().source.bytes,
                payload,
            });
            return self.dtn_complete(session, stream, ctx, &signed, None);
        }
        if !self.apps.dtn().put(&id, &p.sealed, &p.outboard) {
            let _ = d.led.release(&id.store_key());
            return refuse(Refusal::NoRoom);
        }
        self.dtn_complete(session, stream, ctx, &signed, Some(layout.total_len()))
    }

    /// The bundle is here whole: take custody (a relay), hold the copies, and write the acknowledgement. `bytes` is
    /// the charge of a bundle that has just been stored; a bundle already held is acknowledged again. Returns how
    /// the transfer ends: [`Stop::Done`] after the acknowledgement was written.
    fn dtn_complete(
        &mut self,
        session: SessionId,
        stream: StreamId,
        ctx: &RxCtx,
        signed: &SignedHead,
        bytes: Option<u64>,
    ) -> Stop {
        let wall = self.io.wall_ms();
        let id = ctx.bundle;
        let h = *signed.head();
        let refuse = |why| Stop::Refuse(id, why);
        let to_me = h.destination.bytes == self.ident.bytes;
        let Some(d) = self.dtn.as_deref_mut() else {
            return Stop::Break;
        };
        d.hlc = d.hlc.tick(wall);
        let due = if to_me {
            None
        } else {
            let total = bytes
                .or_else(|| d.led.get(&id.store_key()).map(|e| e.bytes))
                .unwrap_or(0);
            let mut evicted: Vec<Key> = Vec::new();
            let accepted = d.book.accept(
                &mut d.led,
                Incoming {
                    bundle: id,
                    bytes: total,
                    expires: h.expires_at(),
                    previous: ctx.from,
                    offer: ctx.offer,
                },
                wall,
                |e| evicted.push(e.key),
            );
            for k in evicted.iter().filter(|k| k.space == Space::DTN && k.id != id.0) {
                d.forget(self.apps.dtn(), wall, &BundleId(k.id));
            }
            let Ok(due) = accepted else {
                self.apps.dtn().remove(&id);
                return refuse(Refusal::NoRoom);
            };
            // A repeated hold is ignored by the forwarder: the copies it would add are not new.
            let _ = d.fwd.step(
                wall,
                Input::Hold(Held {
                    id,
                    destination: h.destination,
                    expires: h.expires_at(),
                    copies: ctx.copies,
                }),
            );
            d.heads.entry(id).or_insert_with(|| signed.clone());
            Some(due)
        };
        let Some(key) = self.apps.dtn().signer() else {
            return refuse(Refusal::NoSigner);
        };
        let ack = match due {
            Some(due) => due.sign(d.hlc, key),
            None => CustodyAck::sign(id, ctx.from, ctx.offer, d.hlc, key),
        };
        let Ok(ack) = ack else {
            return refuse(Refusal::NoSigner);
        };
        wire::start(&mut d.tx, wire::ACK);
        let at = d.tx.len();
        d.tx.resize(at + ack.encoded_len(), 0);
        let encoded = d.tx.get_mut(at..).is_some_and(|dst| ack.encode(dst).is_ok());
        wire::finish(&mut d.tx);
        if !encoded || !self.io.write(session, stream, &d.tx) {
            return Stop::Break;
        }
        self.io.trace(NodeTrace::DtnCustody {
            bundle: btag(&id.0),
            peer: tag(&ctx.from.bytes),
        });
        if !to_me {
            self.io.emit(NodeEvent::DtnCustody {
                bundle: id.0,
                from: ctx.from.bytes,
            });
        }
        Stop::Done
    }

    /// Tell the holder this bundle is refused, and end the transfer.
    pub(crate) fn dtn_refuse(
        &mut self,
        session: SessionId,
        stream: StreamId,
        ds: &DStream,
        bundle: &BundleId,
        why: Refusal,
    ) {
        let peer = match &ds.role {
            Role::Sender { peer, .. } => *peer,
            Role::Receiver { rx } => rx.as_ref().map_or([0; 32], |c| c.from.bytes),
        };
        self.io.trace(NodeTrace::DtnRefused {
            bundle: btag(&bundle.0),
            peer: tag(&peer),
            reason: why as u64,
        });
        let Some(d) = self.dtn.as_deref_mut() else {
            return;
        };
        wire::start(&mut d.tx, wire::REFUSE);
        d.tx.push(why as u8);
        wire::finish(&mut d.tx);
        let _ = self.io.write(session, stream, &d.tx);
        self.io.close_stream(session, stream);
    }
}
