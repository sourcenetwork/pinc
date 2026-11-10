//! The value server: GHOST_FLIGHT and the proof side of WRITE_THROUGH.
//!
//! A request stream is collected (a REQ is at most 4114 bytes), checked against the store, and answered by handing the
//! session a [`ValueSource`]: queued and in-flight response bytes are only `(offset)` descriptors, and every packet
//! build or retransmission reads the store again, so the server buffers nothing. The source keeps a window of
//! [`SERVE_BATCH`](crate::knobs::SERVE_BATCH) = 16 frame descriptors.
//!
//! After a loss on a response stream, or when the receiver asks (`PROOF_REQ`), the server sends range proofs (PROOF
//! extension frames, up to 16 groups each, built from the outboard) for the groups from the lost one to a window
//! beyond the send frontier, so the receiver can verify out-of-order groups. A tree too deep for the proofs to fit
//! gets none.
//!
//! # Invariants
//!
//! - At most `S` requests are held; a request beyond that is refused with a reset, never queued.
//! - A request is answered only for a value the host provides and the store holds whole; anything else is reset as
//!   unavailable.
//! - A newer request from the same peer for the same value that overlaps an older response supersedes it.
//! - Nothing here allocates; a request that breaks the wire format is reset and its slot freed.

use vinc_dag::tree::{Layout, PARENT_LEN, RangeEncoder, Step};
use vinc_transport::frame::ext;
use vinc_transport::stream::StreamId;

use crate::knobs::{GROUP, GROUP_LOG, MAX_REQ_RANGES, WT_LEAD, WT_MAX_K, WT_MAXF, WT_MIN_K, WT_PMAX, code};
use crate::plan::Plan;
use crate::session::{Inbound, Provider};
use crate::source::ValueSource;
use crate::span::Span;
use crate::store::ValueRead;
use crate::trace::{Out, Trace};
use crate::wire::{PROOF_BODY_MAX, ProofFrame, ProofReq, REQ_FIXED, REQ_MAX, Req};

/// The inputs a server takes from the session.
#[derive(Debug, Clone, Copy)]
pub enum ServerIn<'a> {
    /// A peer opened a request stream.
    Opened {
        /// The stream.
        stream: StreamId,
        /// The requesting peer.
        peer: Provider,
    },
    /// Bytes arrived on a request stream.
    Readable(StreamId),
    /// A request stream was reset by the peer.
    Reset(StreamId),
    /// The session to a peer closed: its responses are dropped.
    Closed(Provider),
    /// A response stream ended: fully acknowledged or reset by either side. Its slot is freed.
    Done(StreamId),
    /// Stream bytes of a response were found lost.
    Loss {
        /// The stream.
        stream: StreamId,
        /// The absolute stream offset of the first lost byte.
        offset: u64,
        /// The highest stream offset sent so far.
        sent: u64,
        /// The sender's congestion window in bytes.
        window: u64,
    },
    /// Response bytes up to `sent` have been sent.
    Sent {
        /// The stream.
        stream: StreamId,
        /// The highest stream offset sent so far.
        sent: u64,
        /// The sender's congestion window in bytes.
        window: u64,
    },
    /// An extension frame arrived (a range-proof request).
    Ext {
        /// The frame type.
        ty: u64,
        /// The frame body.
        body: &'a [u8],
    },
}

#[derive(Debug, Clone)]
struct Serving {
    root: [u8; 32],
    plan: Plan,
    deep: bool,
    armed: bool,
    pf_to: u64,
    vfront: u64,
    window: u64,
}

#[derive(Debug, Clone)]
#[allow(
    clippy::large_enum_variant,
    reason = "slots live in a fixed array; boxing would allocate"
)]
enum Stage {
    Collect { n: usize, buf: [u8; REQ_MAX] },
    Serve(Serving),
}

#[derive(Debug, Clone)]
struct Slot {
    stream: StreamId,
    peer: Provider,
    stage: Stage,
}

/// What one request slot holds, for an observer: the stream and the peer, and the root and the plan once the request is
/// being served.
#[derive(Debug, Clone, Copy)]
pub struct SlotView<'a> {
    /// The request stream.
    pub stream: StreamId,
    /// The requesting peer.
    pub peer: Provider,
    /// The root and the plan of the response, once the request is answered.
    pub serving: Option<(&'a [u8; 32], &'a Plan)>,
}

/// The server over a read-only store handle `H` with room for `S` requests.
#[derive(Debug)]
pub struct Server<H: ValueRead + Clone, const S: usize = 32> {
    store: H,
    slots: [Option<Slot>; S],
}

impl<H: ValueRead + Clone, const S: usize> Server<H, S> {
    /// A server of the values in `store`.
    pub fn new(store: H) -> Self {
        Self {
            store,
            slots: core::array::from_fn(|_| None),
        }
    }

    /// The number of requests held.
    pub fn held(&self) -> usize {
        self.slots.iter().flatten().count()
    }

    /// What slot `i` holds, `None` when it is free or `i` is past the table.
    pub fn slot(&self, i: usize) -> Option<SlotView<'_>> {
        let s = self.slots.get(i)?.as_ref()?;
        Some(SlotView {
            stream: s.stream,
            peer: s.peer,
            serving: match &s.stage {
                Stage::Serve(sv) => Some((&sv.root, &sv.plan)),
                Stage::Collect { .. } => None,
            },
        })
    }

    fn find(&self, stream: StreamId) -> Option<usize> {
        self.slots
            .iter()
            .position(|s| s.as_ref().is_some_and(|s| s.stream == stream))
    }

    /// Feed one input at time `now`.
    pub fn on_event<Se: Inbound<H>, Ob: Out>(&mut self, se: &mut Se, out: &mut Ob, now: u64, ev: &ServerIn<'_>) {
        match *ev {
            ServerIn::Opened { stream, peer } => {
                if let Some(free) = self.slots.iter_mut().find(|s| s.is_none()) {
                    *free = Some(Slot {
                        stream,
                        peer,
                        stage: Stage::Collect {
                            n: 0,
                            buf: [0; REQ_MAX],
                        },
                    });
                } else {
                    se.reset(stream, code::BUSY);
                    out.trace(
                        now,
                        Trace::Refused {
                            stream,
                            code: code::BUSY,
                        },
                    );
                }
            }
            ServerIn::Readable(stream) => self.on_readable(se, out, now, stream),
            ServerIn::Reset(stream) | ServerIn::Done(stream) => {
                if let Some(s) = self.find(stream).and_then(|i| self.slots.get_mut(i)) {
                    *s = None;
                }
            }
            ServerIn::Closed(peer) => {
                for s in &mut self.slots {
                    if s.as_ref().is_some_and(|s| s.peer == peer) {
                        *s = None;
                    }
                }
            }
            ServerIn::Loss {
                stream,
                offset,
                sent,
                window,
            } => self.on_loss(se, out, now, stream, offset, sent, window),
            ServerIn::Sent { stream, sent, window } => self.on_sent(se, out, now, stream, sent, window),
            ServerIn::Ext { ty, body } => {
                if ty != ext::PROOF_REQ {
                    return;
                }
                let Ok(rq) = ProofReq::parse(body) else { return };
                let Some(i) = self.find(rq.sid) else { return };
                if let Some(Slot {
                    stage: Stage::Serve(s), ..
                }) = self.slots.get_mut(i).and_then(Option::as_mut)
                {
                    s.armed = true;
                }
                self.proofs(se, out, now, i, rq.from, rq.upto);
            }
        }
    }

    fn on_readable<Se: Inbound<H>, Ob: Out>(&mut self, se: &mut Se, out: &mut Ob, now: u64, stream: StreamId) {
        let Some(i) = self.find(stream) else { return };
        let Some(Slot {
            stage: Stage::Collect { n, buf },
            ..
        }) = self.slots.get_mut(i).and_then(Option::as_mut)
        else {
            return;
        };
        let mut bad = false;
        let from = *n as u64;
        se.visit(stream, from, |piece| {
            let mut taken = 0;
            while taken < piece.len() {
                let need = if *n < REQ_FIXED {
                    REQ_FIXED
                } else if let Some(Ok(t)) = buf.get(..REQ_FIXED).map(Req::total_len) {
                    t
                } else {
                    bad = true;
                    return taken;
                };
                if *n >= need {
                    break;
                }
                let k = (piece.len() - taken).min(need - *n);
                let (Some(dst), Some(src)) = (buf.get_mut(*n..*n + k), piece.get(taken..taken + k)) else {
                    return taken;
                };
                dst.copy_from_slice(src);
                *n += k;
                taken += k;
            }
            taken
        });
        let have = *n;
        if bad {
            return self.refuse(se, out, now, i, code::PROTOCOL);
        }
        if have < REQ_FIXED {
            return;
        }
        let Some(Ok(total)) = buf.get(..REQ_FIXED).map(Req::total_len) else {
            return self.refuse(se, out, now, i, code::PROTOCOL);
        };
        if have < total {
            return;
        }
        if se.has(stream, total as u64, 1) {
            return self.refuse(se, out, now, i, code::PROTOCOL);
        }
        let Some((root, spans, count)) = buf.get(..total).and_then(|b| Req::parse(b).ok()).map(|(r, _)| {
            let mut spans = [Span::default(); MAX_REQ_RANGES];
            let mut c = 0;
            for (slot, s) in spans.iter_mut().zip(r.ranges()) {
                *slot = s;
                c += 1;
            }
            (*r.root(), spans, c)
        }) else {
            return self.refuse(se, out, now, i, code::PROTOCOL);
        };
        self.answer(se, out, now, i, root, spans.get(..count).unwrap_or_default(), total);
    }

    /// Reset the request in slot `i` with `c` and free it.
    fn refuse<Se: Inbound<H>, Ob: Out>(&mut self, se: &mut Se, out: &mut Ob, now: u64, i: usize, c: u64) {
        if let Some(s) = self.slots.get_mut(i).and_then(Option::take) {
            se.reset(s.stream, c);
            out.trace(
                now,
                Trace::Refused {
                    stream: s.stream,
                    code: c,
                },
            );
        }
    }

    #[allow(clippy::too_many_arguments, reason = "one request's parts, passed once")]
    fn answer<Se: Inbound<H>, Ob: Out>(
        &mut self,
        se: &mut Se,
        out: &mut Ob,
        now: u64,
        i: usize,
        root: [u8; 32],
        spans: &[Span],
        req_len: usize,
    ) {
        let plan = se
            .provided(&root)
            .then(|| self.store.servable_len(&root))
            .flatten()
            .and_then(|len| Plan::new(len, spans).ok());
        let Some(plan) = plan else {
            return self.refuse(se, out, now, i, code::UNAVAILABLE);
        };
        let Some((stream, peer)) = self.slots.get(i).and_then(Option::as_ref).map(|s| (s.stream, s.peer)) else {
            return;
        };
        let total = plan.total();
        let source = ValueSource::new(self.store.clone(), root, plan.clone());
        if !se.serve(stream, source, total) {
            return self.refuse(se, out, now, i, code::UNAVAILABLE);
        }
        // SERVE_ONE: a newer request for bytes an older response from the same peer is still sending supersedes it.
        // The older responses are freed only now that the new one is accepted: a refused request costs nothing.
        for s2 in &mut self.slots {
            let old = s2.as_ref().is_some_and(|o| {
                o.stream != stream
                    && o.peer == peer
                    && matches!(&o.stage, Stage::Serve(sv) if sv.root == root && overlaps(&sv.plan, spans))
            });
            if old && let Some(o) = s2.take() {
                se.reset(o.stream, code::SUPERSEDED);
                out.trace(
                    now,
                    Trace::Refused {
                        stream: o.stream,
                        code: code::SUPERSEDED,
                    },
                );
            }
        }
        se.consume(stream, req_len as u64);
        out.trace(
            now,
            Trace::Serving {
                stream,
                ranges: u8::try_from(spans.len()).unwrap_or(u8::MAX),
                bytes: total,
            },
        );
        if let Some(s) = self.slots.get_mut(i).and_then(Option::as_mut) {
            s.stage = Stage::Serve(Serving {
                root,
                plan,
                deep: false,
                armed: false,
                pf_to: 0,
                vfront: 0,
                window: 0,
            });
        }
    }

    /// The value offset (end of sent data) that stream offset `sent` has reached.
    fn front_of(plan: &Plan, sent: u64) -> u64 {
        let Some(f) = plan.locate(sent.saturating_sub(1)) else {
            return 0;
        };
        f.off + sent.saturating_sub(f.data_start()).min(u64::from(f.dlen))
    }

    #[allow(clippy::too_many_arguments, reason = "the loss event's fields, passed once")]
    fn on_loss<Se: Inbound<H>, Ob: Out>(
        &mut self,
        se: &mut Se,
        out: &mut Ob,
        now: u64,
        stream: StreamId,
        offset: u64,
        sent: u64,
        window: u64,
    ) {
        let Some(i) = self.find(stream) else { return };
        let Some(Slot {
            stage: Stage::Serve(s), ..
        }) = self.slots.get_mut(i).and_then(Option::as_mut)
        else {
            return;
        };
        s.armed = true;
        s.window = window;
        s.vfront = s.vfront.max(Self::front_of(&s.plan, sent));
        let from = s.plan.locate(offset).map_or(0, |f| f.off);
        self.proofs(se, out, now, i, from, 0);
    }

    fn on_sent<Se: Inbound<H>, Ob: Out>(
        &mut self,
        se: &mut Se,
        out: &mut Ob,
        now: u64,
        stream: StreamId,
        sent: u64,
        window: u64,
    ) {
        let Some(i) = self.find(stream) else { return };
        let Some(Slot {
            stage: Stage::Serve(s), ..
        }) = self.slots.get_mut(i).and_then(Option::as_mut)
        else {
            return;
        };
        s.window = window;
        s.vfront = s.vfront.max(Self::front_of(&s.plan, sent));
        if s.armed && !s.deep && s.vfront.saturating_add(window / 2) > s.pf_to {
            let (from, upto) = (s.vfront.saturating_sub(1), s.vfront.saturating_add(window.min(WT_LEAD)));
            self.proofs(se, out, now, i, from, upto);
        }
    }

    /// WRITE_THROUGH: send range proofs from value offset `from` up to `upto` (0: the send frontier plus a window).
    fn proofs<Se: Inbound<H>, Ob: Out>(&mut self, se: &mut Se, out: &mut Ob, now: u64, i: usize, from: u64, upto: u64) {
        let Some(Slot {
            stream,
            stage: Stage::Serve(s),
            ..
        }) = self.slots.get_mut(i).and_then(Option::as_mut)
        else {
            return;
        };
        let stream = *stream;
        let ln = s.plan.value_len();
        if ln == 0 || s.deep {
            return;
        }
        // The end is peer-controlled (`upto`), so it saturates: a request near 2^64 must not wrap or panic.
        let end = if upto != 0 {
            upto.saturating_add(GROUP)
        } else {
            s.vfront.saturating_add(s.window).saturating_add(GROUP)
        };
        let end = end.min(ln).min(end - end % GROUP);
        let Some(k) = proof_k(ln) else {
            s.deep = true;
            return;
        };
        let Ok(layout) = Layout::new(ln, GROUP_LOG) else { return };
        // Frames are cut at multiples of `k` groups, so each is a subtree of the tree and fits its size bound.
        let block = k * GROUP;
        let start = (from / block * block).max(s.pf_to);
        let (mut at, root) = (start, s.root);
        let mut frames = 0;
        while at < end && frames < WT_MAXF {
            let wn = (block - at % block).min(end - at);
            let Some(len) = self.build_proof(&layout, &root, stream, at, wn, ln, se) else {
                break;
            };
            out.trace(
                now,
                Trace::ProofSent {
                    stream,
                    start: at,
                    bytes: u32::try_from(wn).unwrap_or(u32::MAX),
                },
            );
            at += wn;
            frames += 1;
            let _ = len;
        }
        if let Some(Slot {
            stage: Stage::Serve(s), ..
        }) = self.slots.get_mut(i).and_then(Option::as_mut)
        {
            s.pf_to = at;
        }
    }

    /// Build and send the PROOF frame for `[at, at + wn)`; the bytes sent, or `None` if it could not be sent.
    #[allow(clippy::too_many_arguments, reason = "one proof frame's fields, passed once")]
    fn build_proof<Se: Inbound<H>>(
        &self,
        layout: &Layout,
        root: &[u8; 32],
        stream: StreamId,
        at: u64,
        wn: u64,
        ln: u64,
        se: &mut Se,
    ) -> Option<usize> {
        let mut body = [0u8; PROOF_BODY_MAX];
        let head = ProofFrame::write_head(
            stream,
            u8::try_from(GROUP_LOG).ok()?,
            at,
            u32::try_from(wn).ok()?,
            ln,
            &mut body,
        )
        .ok()?;
        let mut len = head;
        for step in RangeEncoder::new(*layout, &(at..at + wn)).ok()? {
            let Step::Parent { outboard_offset } = step.ok()? else {
                continue;
            };
            let dst = body.get_mut(len..len + PARENT_LEN)?;
            if self.store.read_outboard(root, outboard_offset, dst) != PARENT_LEN {
                return None;
            }
            len += PARENT_LEN;
        }
        se.send_ext(stream, ext::PROOF, body.get(..len)?).then_some(len)
    }
}

/// The groups per range-proof frame for a value of `ln` bytes (`ln > 0`), or `None` when the tree is so deep that
/// fewer than [`WT_MIN_K`] groups fit a frame of at most [`WT_PMAX`] proof bytes (such a value gets no write-through).
///
/// A frame of `k` aligned groups holds the `k - 1` parents inside its subtree and at most one parent per level above
/// it, so `cost(k)` bounds its proof bytes; the frame size halves from [`WT_MAX_K`] until the bound fits.
pub fn proof_k(ln: u64) -> Option<u64> {
    let ngroups = ln.div_ceil(GROUP);
    let bits = |x: u64| u64::from(x.checked_ilog2().map_or(0, |b| b + 1));
    let dep = bits(ngroups.saturating_sub(1));
    let cost = |k: u64| PARENT_LEN as u64 * (k - 1) + PARENT_LEN as u64 * dep.saturating_sub(bits(k - 1)) + 8;
    let mut k = WT_MAX_K;
    while k > 1 && cost(k) > WT_PMAX as u64 {
        k /= 2;
    }
    (cost(k) <= WT_PMAX as u64 && k >= WT_MIN_K).then_some(k)
}

/// Whether any range of `plan` overlaps any of `spans`.
fn overlaps(plan: &Plan, spans: &[Span]) -> bool {
    (0..plan.ranges())
        .filter_map(|i| plan.range_span(i))
        .any(|r| spans.iter().any(|s| s.len > 0 && s.off < r.end() && r.off < s.end()))
}
