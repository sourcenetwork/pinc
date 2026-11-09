//! Building, serving and receiving bundles of verifiable slices.
//!
//! [`seal_bundle`] turns a payload into sealed symbols with Reed-Solomon parity and returns the signed head whose
//! root commits to all of them. [`serve`] produces the range proof for any run of symbols of a complete bundle. A
//! [`Reception`] is the receiving side: it verifies each arriving proof stream against the root, keeps only verified
//! symbols, remembers which ones it holds, and so is partial and resumable by construction.
//!
//! Invariants: a symbol enters a reception's buffer only after its group hashed to the signed root through the
//! proof; the set of held symbols only grows; the reception borrows the caller's buffer, which must be exactly the
//! sealed length the head commits to, so memory is bounded and charged by the caller before any byte arrives
//! ([`SliceLayout::total_len`] is the charge); decoding from any `k` symbols of a block checks the result against the
//! root, so a sender whose parity was not a code word is detected, never trusted; decoding runs in caller-provided
//! scratch and writes only symbols that are not held, so a held symbol keeps its verified bytes. No path allocates
//! or panics.

use core::ops::Range;

use vinc_crypto::provider::Provider;
use vinc_crypto::{Keypair, NodeId};
use vinc_dag::ranges::VerifiedRanges;
use vinc_dag::tree::{Layout, RangeVerifier, TreeError, build_outboard, encode_range, encoded_len};

use crate::error::DtnError;
use crate::head::{Erasure, Head, SignedHead};
use crate::hlc::Hlc;
use crate::layout::SliceLayout;
use crate::rs::{MAX_SYMBOLS, Rs};
use crate::seal::{Cipher, RecipientKeys, SealSeeds, encapsulate};

/// The sender's choices for one bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Plan {
    /// The creation time stamped into the head.
    pub created: Hlc,
    /// The lifetime in milliseconds.
    pub lifetime_ms: u64,
    /// The initial copy budget.
    pub copies: u16,
    /// The erasure parameters.
    pub erasure: Erasure,
    /// The slice size log (0 to 4: slices of 1 KiB to 16 KiB).
    pub slice_log: u8,
}

/// Everything about a bundle a sender decides: the recipient, the plan and the randomness.
pub struct Outgoing<'a> {
    /// The recipient's published keys.
    pub recipient: &'a RecipientKeys,
    /// The plan.
    pub plan: Plan,
    /// The per-bundle seeds.
    pub seeds: &'a SealSeeds,
}

fn usz(v: u64) -> Result<usize, DtnError> {
    usize::try_from(v).map_err(|_| DtnError::Buffer)
}

/// Seal `payload` into `sealed` (exactly [`SliceLayout::total_len`] bytes) with the tree outboard in `outboard`
/// (exactly [`SliceLayout::outboard_len`] bytes), and return the head signed by `signer`.
///
/// # Errors
/// [`DtnError::Params`] for invalid parameters or an empty payload; [`DtnError::Buffer`] for a wrong-sized buffer;
/// [`DtnError::Crypto`] for a failed encapsulation or signature.
pub fn seal_bundle<P: Provider>(
    p: &P,
    signer: &Keypair,
    out: &Outgoing<'_>,
    payload: &[u8],
    sealed: &mut [u8],
    outboard: &mut [u8],
) -> Result<SignedHead, DtnError> {
    let cfg = &out.plan;
    let payload_len = u64::try_from(payload.len()).map_err(|_| DtnError::Params)?;
    let layout = SliceLayout::new(cfg.erasure.k, cfg.erasure.m, cfg.slice_log, payload_len)?;
    if u64::try_from(sealed.len()) != Ok(layout.total_len())
        || u64::try_from(outboard.len()) != Ok(layout.outboard_len()?)
    {
        return Err(DtnError::Buffer);
    }
    let source = signer.node_id();
    let (id, envelope, cipher) = encapsulate(p, out.recipient, &source, cfg.created, out.seeds)?;
    let (g, plain) = (usz(layout.slice_len())?, usz(layout.plain_len())?);
    let per_block = (usize::from(cfg.erasure.k) + usize::from(cfg.erasure.m)) * g;
    for (b, region) in (0u64..).zip(sealed.chunks_mut(per_block)) {
        let block_k = layout.block_k(b);
        for (t, symbol) in (0u64..).zip(region.chunks_exact_mut(g).take(block_k)) {
            let d = b * u64::from(cfg.erasure.k) + t;
            let (pt, tag_slot) = symbol.split_at_mut(plain);
            let from = usz(d)?.saturating_mul(plain);
            let src = payload
                .get(from..from.saturating_add(plain).min(payload.len()))
                .unwrap_or(&[]);
            let (filled, pad) = pt.split_at_mut(src.len());
            filled.copy_from_slice(src);
            pad.fill(0);
            tag_slot.copy_from_slice(&cipher.seal_slice(p, d, pt)?);
        }
        Rs::new(block_k, usize::from(cfg.erasure.m))?.encode(g, region)?;
    }
    let root = build_outboard(sealed, u32::from(cfg.slice_log), outboard)?;
    let head = Head {
        id,
        source,
        destination: out.recipient.node,
        created: cfg.created,
        lifetime_ms: cfg.lifetime_ms,
        copies: cfg.copies,
        erasure: cfg.erasure,
        slice_log: cfg.slice_log,
        payload_len,
        root,
        envelope,
    };
    SignedHead::sign(head, signer)
}

fn tree_layout(layout: &SliceLayout) -> Result<Layout, DtnError> {
    Ok(Layout::new(layout.total_len(), u32::from(layout.slice_log()))?)
}

/// The length of the proof stream [`serve`] writes for `symbols`.
///
/// # Errors
/// [`DtnError::Buffer`] for a bad range; [`DtnError::Tree`] if the stream would be too long.
pub fn serve_len(layout: &SliceLayout, symbols: &Range<u64>) -> Result<usize, DtnError> {
    let bytes = layout.byte_range(symbols)?;
    usz(encoded_len(tree_layout(layout)?, &bytes)?)
}

/// Write the range proof for `symbols` of a complete bundle (`sealed` and its `outboard`) into `out`, returning the
/// bytes written; [`serve_len`] sizes `out`.
///
/// # Errors
/// [`DtnError::Buffer`] for a bad range; [`DtnError::Tree`] for a wrong-sized buffer.
pub fn serve(
    layout: &SliceLayout,
    sealed: &[u8],
    outboard: &[u8],
    symbols: &Range<u64>,
    out: &mut [u8],
) -> Result<usize, DtnError> {
    let bytes = layout.byte_range(symbols)?;
    Ok(encode_range(
        sealed,
        outboard,
        u32::from(layout.slice_log()),
        &bytes,
        out,
    )?)
}

fn run_verifier<const G: usize>(
    root: [u8; 32],
    len: u64,
    range: &Range<u64>,
    stream: &[u8],
    sink: &mut impl FnMut(u64, &[u8]),
) -> Result<(), DtnError> {
    let mut verifier = RangeVerifier::<G>::new(root, len, range)?;
    let mut rest = stream;
    while !verifier.is_complete() {
        if rest.is_empty() {
            return Err(TreeError::Incomplete.into());
        }
        let fed = verifier.feed(rest)?;
        let consumed = fed.consumed;
        if let Some(group) = fed.verified {
            sink(group.offset, group.data);
        } else if consumed == 0 {
            return Err(TreeError::Incomplete.into());
        }
        rest = rest.get(consumed..).unwrap_or(&[]);
    }
    if rest.is_empty() {
        Ok(())
    } else {
        Err(TreeError::TooMuchData.into())
    }
}

/// Verify a proof stream for the byte `range` against `root` and hand each verified group to `sink`, which receives
/// the group's offset and bytes. Groups verified before an error stay delivered.
fn verify_stream(
    log: u8,
    root: [u8; 32],
    len: u64,
    range: &Range<u64>,
    stream: &[u8],
    mut sink: impl FnMut(u64, &[u8]),
) -> Result<(), DtnError> {
    match log {
        0 => run_verifier::<1024>(root, len, range, stream, &mut sink),
        1 => run_verifier::<2048>(root, len, range, stream, &mut sink),
        2 => run_verifier::<4096>(root, len, range, stream, &mut sink),
        3 => run_verifier::<8192>(root, len, range, stream, &mut sink),
        4 => run_verifier::<16384>(root, len, range, stream, &mut sink),
        _ => Err(DtnError::Params),
    }
}

/// The receiving side of one bundle: verified symbols in a caller-owned buffer, and which ones are held.
///
/// `W` bounds the number of disjoint held intervals; an arrival that would need more is refused with
/// [`DtnError::ReceptionFull`] (the symbol is simply fetched again later).
#[derive(Debug)]
pub struct Reception<'a, const W: usize> {
    head: Head,
    layout: SliceLayout,
    buf: &'a mut [u8],
    have: VerifiedRanges<W>,
}

impl<'a, const W: usize> Reception<'a, W> {
    /// Start receiving a bundle into `buf`, which must be exactly [`SliceLayout::total_len`] bytes.
    ///
    /// # Errors
    /// As [`Reception::resume`].
    pub fn new(signed: &SignedHead, buf: &'a mut [u8], now: u64) -> Result<Self, DtnError> {
        Self::resume(signed, buf, VerifiedRanges::new(), now)
    }

    /// Continue a reception from state the caller kept: the same buffer and the held-range set it had. The caller
    /// vouches that `buf` holds the verified bytes of every interval in `have` (it got them from a previous
    /// reception of this same bundle).
    ///
    /// # Errors
    /// [`DtnError::Crypto`] if the head's signature does not verify; [`DtnError::Expired`] if it is expired at
    /// `now`; [`DtnError::Params`] for an invalid head; [`DtnError::Buffer`] if `buf` is the wrong size.
    pub fn resume(signed: &SignedHead, buf: &'a mut [u8], have: VerifiedRanges<W>, now: u64) -> Result<Self, DtnError> {
        signed.verify()?;
        let head = *signed.head();
        if head.is_expired(now) {
            return Err(DtnError::Expired);
        }
        let layout = head.layout()?;
        if u64::try_from(buf.len()) != Ok(layout.total_len()) {
            return Err(DtnError::Buffer);
        }
        Ok(Self {
            head,
            layout,
            buf,
            have,
        })
    }

    /// The verified head.
    pub const fn head(&self) -> &Head {
        &self.head
    }

    /// The geometry of the bundle.
    pub const fn layout(&self) -> &SliceLayout {
        &self.layout
    }

    /// The held byte ranges, to keep for a later [`Reception::resume`].
    pub const fn have(&self) -> &VerifiedRanges<W> {
        &self.have
    }

    /// Verify the proof `stream` for `symbols` (end exclusive) and keep every symbol that verifies.
    ///
    /// # Errors
    /// [`DtnError::Buffer`] for a bad range; [`DtnError::Tree`] if the stream does not verify against the root, is
    /// short or has trailing bytes (symbols verified before the fault are kept); [`DtnError::ReceptionFull`] if the
    /// held set is full.
    pub fn feed(&mut self, symbols: Range<u64>, stream: &[u8]) -> Result<(), DtnError> {
        let bytes = self.layout.byte_range(&symbols)?;
        if bytes.is_empty() {
            return Ok(());
        }
        let mut fault = None;
        let (buf, have) = (&mut *self.buf, &mut self.have);
        let verdict = verify_stream(
            self.head.slice_log,
            self.head.root,
            self.layout.total_len(),
            &bytes,
            stream,
            |offset, data| {
                let at = usize::try_from(offset).unwrap_or(usize::MAX);
                match buf.get_mut(at..at.saturating_add(data.len())) {
                    Some(dst) => dst.copy_from_slice(data),
                    None => fault = Some(DtnError::Buffer),
                }
                if have.insert(offset..offset + data.len() as u64).is_err() {
                    fault = Some(DtnError::ReceptionFull);
                }
            },
        );
        verdict.and_then(|()| fault.map_or(Ok(()), Err))
    }

    /// Whether symbol `s` is held.
    pub fn holds(&self, s: u64) -> bool {
        let g = self.layout.slice_len();
        s < self.layout.total_symbols() && self.have.contains_range(s * g..(s + 1) * g)
    }

    /// The first run of unheld symbols at or after symbol `from`, as symbol indices: what to ask for next.
    pub fn next_missing(&self, from: u64) -> Option<Range<u64>> {
        let g = self.layout.slice_len();
        let total = self.layout.total_len();
        let mut at = from.saturating_mul(g);
        for iv in self.have.iter() {
            if iv.end <= at {
                continue;
            }
            if iv.start > at {
                return Some(at / g..iv.start.min(total) / g);
            }
            at = iv.end;
        }
        (at < total).then(|| at / g..total / g)
    }

    /// Whether every symbol is held.
    pub fn is_complete(&self) -> bool {
        self.have.contains_range(0..self.layout.total_len())
    }

    /// Whether every block holds at least `k` of its symbols, so [`Reception::finish`] can succeed.
    pub fn is_decodable(&self) -> bool {
        (0..self.layout.blocks()).all(|b| {
            let start = self.layout.block_start(b);
            let held = (0..self.layout.block_n(b) as u64)
                .filter(|s| self.holds(start + s))
                .count();
            held >= self.layout.block_k(b)
        })
    }

    /// The size of the scratch buffer [`Reception::finish`] needs: one erasure block of symbols, the largest one.
    ///
    /// # Errors
    /// [`DtnError::Buffer`] if the size does not fit `usize`.
    pub fn scratch_len(&self) -> Result<usize, DtnError> {
        usz(self.layout.slice_len())?
            .checked_mul(self.layout.block_n(0))
            .ok_or(DtnError::Buffer)
    }

    /// Recover every missing symbol from any `k` of its block, rebuild the outboard into `outboard` (exactly
    /// [`SliceLayout::outboard_len`] bytes) and check the result against the signed root. Afterwards the buffer is
    /// the complete sealed bundle: it can be served and opened.
    ///
    /// Each block is reconstructed in `scratch` (exactly [`Reception::scratch_len`] bytes), and only the symbols
    /// that are not held are copied back, so a held symbol is never written over, even when the check fails.
    ///
    /// # Errors
    /// [`DtnError::Buffer`] for a wrong-sized `outboard` or `scratch` (nothing changes);
    /// [`DtnError::Incomplete`] if a block holds fewer than `k` symbols (earlier blocks are already completed);
    /// [`DtnError::Inconsistent`] if the decoded bundle does not hash to the root (the sender's parity was not a code
    /// word; nothing is marked held and no held symbol was touched).
    pub fn finish(&mut self, outboard: &mut [u8], scratch: &mut [u8]) -> Result<(), DtnError> {
        if u64::try_from(outboard.len()) != Ok(self.layout.outboard_len()?) || scratch.len() != self.scratch_len()? {
            return Err(DtnError::Buffer);
        }
        let g = usz(self.layout.slice_len())?;
        for b in 0..self.layout.blocks() {
            let (start, n) = (self.layout.block_start(b), self.layout.block_n(b));
            let mut present = [false; MAX_SYMBOLS];
            let present = present.get_mut(..n).ok_or(DtnError::Params)?;
            for (s, flag) in (start..).zip(present.iter_mut()) {
                *flag = self.holds(s);
            }
            if present.iter().all(|p| *p) {
                continue;
            }
            let from = usz(start)? * g;
            let region = self.buf.get_mut(from..from + n * g).ok_or(DtnError::Buffer)?;
            let work = scratch.get_mut(..n * g).ok_or(DtnError::Buffer)?;
            work.copy_from_slice(region);
            Rs::new(self.layout.block_k(b), usize::from(self.layout.m()))?.reconstruct(g, work, present)?;
            for ((dst, src), held) in region.chunks_exact_mut(g).zip(work.chunks_exact(g)).zip(present.iter()) {
                if !held {
                    dst.copy_from_slice(src);
                }
            }
        }
        let root = build_outboard(self.buf, u32::from(self.layout.slice_log()), outboard)?;
        if root != self.head.root {
            return Err(DtnError::Inconsistent);
        }
        self.have
            .insert(0..self.layout.total_len())
            .map_err(|_| DtnError::ReceptionFull)
    }

    /// The sealed bundle bytes; every symbol is valid once [`Reception::is_complete`].
    pub const fn sealed(&self) -> &[u8] {
        &*self.buf
    }

    /// Open every data slice into `out`, which must be exactly [`SliceLayout::padded_len`] bytes, and return the
    /// payload length: the payload is `out[..n]`. Needs every data symbol held, not the parity.
    ///
    /// # Errors
    /// [`DtnError::Buffer`] for a wrong-sized `out`; [`DtnError::Incomplete`] if a data symbol is not held;
    /// [`DtnError::Crypto`] if a slice fails authentication (a tampered slice, or a wrong key).
    pub fn open<P: Provider>(&self, p: &P, cipher: &Cipher<P>, out: &mut [u8]) -> Result<usize, DtnError> {
        if u64::try_from(out.len()) != Ok(self.layout.padded_len()) {
            return Err(DtnError::Buffer);
        }
        let (g, plain) = (usz(self.layout.slice_len())?, usz(self.layout.plain_len())?);
        for (d, dst) in (0u64..).zip(out.chunks_exact_mut(plain)) {
            let s = self.layout.data_symbol(d).ok_or(DtnError::Buffer)?;
            if !self.holds(s) {
                return Err(DtnError::Incomplete);
            }
            let from = usz(s)? * g;
            let symbol = self.buf.get(from..from + g).ok_or(DtnError::Buffer)?;
            let (ct, tag) = symbol.split_at(plain);
            let tag: &[u8; 16] = tag.try_into().map_err(|_| DtnError::Buffer)?;
            dst.copy_from_slice(ct);
            cipher.open_slice(p, d, dst, tag)?;
        }
        usz(self.layout.payload_len())
    }

    /// The node the bundle is addressed to.
    pub const fn destination(&self) -> &NodeId {
        &self.head.destination
    }
}
