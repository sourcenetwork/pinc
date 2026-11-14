import Vinc.ConnectFrameThm

/-!
# The batch builder

`BatchBuilder` and `BatchState` of `carrier/frame.rs`, as total functions over unbounded naturals. The model is the one of
`proofs/tla/ConnectPackOps.tla` (`offer` is the operator `Offer`, `seal` is `Seal`), and the Rust test
`trace_connect_pack` replays the real code against both.

A configuration has `F` (`BATCH_MAX_FRAMES`), `B` (`BATCH_MAX_BYTES`), `head` (`BATCH_HEAD_MAX`, two bytes and three per
frame) and `cap` (the length of the buffer; the code asks for `MAX_FRAME_LEN`, which is `B + head`). The state is the
encodings of the accepted frames in order (the code keeps their lengths and the bytes in the buffer; here the bytes
are kept too, so that the record can be decoded). The frames lie back to back from offset `head` of the buffer, so
the header can be written right before them once the count is known.

An offered frame (`Cand`) has its encoding (`raw`; for a frame whose encoder fails, the bytes written before it
fails), whether it is a long-header packet or a BATCH frame, and whether and how its encoder fails. A put that
does not fit the room left fails before the encoder's own check: that is the wire error `BufferTooSmall`.
-/

namespace Vinc.ConnPack
open Vinc.ConnCodec

structure Cfg where
  F : Nat
  B : Nat
  head : Nat
  cap : Nat

/-- An offered frame. -/
structure Cand where
  raw : List Nat
  long : Bool
  isBatch : Bool
  bad : Bool
  err : Nat

def Cand.n (f : Cand) : Nat := f.raw.length

/-- The accepted frames, in order, as the bytes they were encoded to. -/
structure St where
  ps : List (List Nat)

def St.used (st : St) : Nat := (st.ps.map List.length).sum
def St.count (st : St) : Nat := st.ps.length

/-- What `offer` answers: the frame joined, was refused, or an error (`NoRoom`, `BufferTooSmall` of the first frame,
or the encoder's own, with its code). -/
inductive Res where
  | added
  | refused
  | noroom
  | small
  | bad (e : Nat)
  deriving DecidableEq, Repr

/-- `BatchBuilder::offer`. -/
def offer (c : Cfg) (st : St) (f : Cand) : Res × St :=
  if f.isBatch = true ∨ f.long = true ∨ c.F ≤ st.count then (.refused, st)
  else if c.cap < c.head + st.used then (.noroom, st)
  else if c.cap - (c.head + st.used) < f.n then
    (if 0 < st.count then (.refused, st) else (.small, st))
  else if f.bad = true then (.bad f.err, st)
  else if c.B < st.used + f.n then (.refused, st)
  else (.added, ⟨st.ps ++ [f.raw]⟩)

/-- The header of a batch: the type byte, the count, the lengths as varints. -/
def headBytes (ps : List (List Nat)) : List Nat := 13 :: ps.length :: lensBytes ps

inductive Kind where
  | none
  | single
  | batch
  deriving DecidableEq, Repr

/-- `BatchBuilder::finish`: the kind of record. -/
def kind (st : St) : Kind :=
  match st.ps with
  | [] => .none
  | [_] => .single
  | _ => .batch

/-- The record `finish` returns: nothing, the frame as it is, or the header and the frames. -/
def record (st : St) : List Nat :=
  match st.ps with
  | [] => []
  | [p] => p
  | ps => headBytes ps ++ ps.flatten

/-- Whether the header fits the `head` bytes kept for it (the code's `NoRoom` otherwise). -/
def headFits (c : Cfg) (st : St) : Bool :=
  match st.ps with
  | [] | [_] => true
  | ps => decide ((headBytes ps).length ≤ c.head)

end Vinc.ConnPack
