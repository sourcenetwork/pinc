import Pinc.MachineEnc

/-!
# The range verifier at the byte level

`Tree` models `RangeVerifier::feed` for one completed stream item. This module models the real call: the
buffer, `filled`, a piece of any size, the zero-copy fast path when the whole next item is in the input and
nothing is buffered, and the slow path that copies into the buffer.

* `feedCode` is the code of `RangeVerifier::feed` (`pinc-dag/src/tree/verify.rs`), with the `usize`
  arithmetic on a `w`-bit `usize` (32 or 64), written as the code writes it. The buffer is the list of its
  filled bytes: the bytes beyond `filled` are never read, because the item hashed is `buf[..need]` and
  `filled` reaches `need` only after bytes `0 .. need` were all written.
* `bytes` is the reference: the same verifier fed one byte at a time. A pending item grows by one byte, and
  when it reaches the size the top node needs it is completed with the item model `Tree.feed`.
* `feedCode_sim`: one call is the reference run over exactly the bytes the call consumed, on the fast path
  and on the slow path alike, and no step of it fails (no overflow, no narrowing failure, no
  `OutputTooSmall` from the buffer, no wrong `TooMuchData`).
* `split_invariance`: feeding a stream in any split into pieces, the caller feeding the unconsumed tail of
  each piece until it is used up and stopping at the first error, gives exactly the reference run over the
  concatenated stream: the same decisions, the same released groups and bytes, the same final state.
* `stream_equiv`: for a stream cut at item boundaries that runs from a state with an empty buffer, that run is
  the item-by-item model `Tree.run`, whatever the split.

What the value model cannot say, and the traces check: that the released group of the fast path borrows the
input and that of the slow path borrows the buffer (aliasing), and the hash values themselves.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Pinc.VerifyBytes
open Pinc.Layout Pinc.Tree Pinc.Machine

/-- Stream bytes (each below 256 in the code; the model never uses that). -/
abbrev Bytes := List Nat

/-- The errors `feed` returns. -/
inductive E where
  | parentMismatch
  | groupMismatch
  | tooMuchData
  | outputTooSmall
  deriving DecidableEq

/-- What a call tells the caller: a released group (its byte offset and its bytes) or an error. -/
inductive Obs where
  | released (off : Nat) (data : Bytes)
  | err (e : E)
  deriving DecidableEq

/-- The fixed parameters of a verifier: the hash, the item reader (how a completed item's bytes are read as
two chaining values or a group), the value length, the group log, the group count and the group range. -/
structure Cfg (Cv : Type) where
  H : Hash Cv Bytes
  rd : Bytes → Raw Cv Bytes
  len : Nat
  log : Nat
  n : Nat
  first : Nat
  last : Nat

/-- The verifier state: the item model's state, the filled prefix of the buffer, and the stored error
(`true` for a group mismatch) once failed. -/
structure BS (Cv : Type) where
  core : State Cv Bytes
  buf : Bytes
  errk : Bool

/-- The error a failed verifier repeats. -/
def errOf (k : Bool) : E := if k then .groupMismatch else .parentMismatch

/-- The size of the item the node needs: a group's bytes or one parent pair. -/
def needN {Cv : Type} (len log : Nat) (nd : Node Cv) : Nat := if nd.hi - nd.lo = 1 then groupSize len log nd.lo else 64

section
variable {Cv : Type} [DecidableEq Cv]

/-- `Walk::complete` on a whole item, with the verifier bookkeeping around it: the item model's step, the
buffer emptied, and what the caller sees (the released group, or the mismatch error). -/
def completeItem (c : Cfg Cv) (s : BS Cv) (nd : Node Cv) (item : Bytes) : BS Cv × Option Obs :=
  let core := Tree.feed c.H c.n c.first c.last s.core (c.rd item)
  let leaf := decide (nd.hi - nd.lo = 1)
  if core.failed then
    ({ core := core, buf := [], errk := leaf }, some (.err (errOf leaf)))
  else
    ({ core := core, buf := [], errk := s.errk }, if leaf then some (.released (nd.lo * groupLen c.log) item) else none)

/-- The reference verifier, one byte at a time: a pending item grows by the byte and is completed when it
reaches the size the top node needs. -/
def stepByte (c : Cfg Cv) (s : BS Cv) (b : Nat) : BS Cv × Option Obs :=
  if s.core.failed then (s, some (.err (errOf s.errk)))
  else match s.core.stack with
    | [] => (s, some (.err .tooMuchData))
    | nd :: _ =>
      if (s.buf ++ [b]).length < needN c.len c.log nd then ({ s with buf := s.buf ++ [b] }, none)
      else completeItem c s nd (s.buf ++ [b])

/-- The observable list of an optional event. -/
def obsList : Option Obs → List Obs
  | none => []
  | some o => [o]

/-- The reference run over a byte string: the final state and the observable events, ending at the first
error (the caller stops there). -/
def bytes (c : Cfg Cv) : BS Cv → Bytes → BS Cv × List Obs
  | s, [] => (s, [])
  | s, b :: bs =>
    match stepByte c s b with
    | (s1, none) => bytes c s1 bs
    | (s1, some (.err e)) => (s1, [.err e])
    | (s1, some (.released off d)) =>
      match bytes c s1 bs with
      | (s2, o) => (s2, .released off d :: o)

/-- Whether an event list holds an error. -/
def hasErr (o : List Obs) : Bool := o.any fun x => match x with | .err _ => true | _ => false

/-- The outcome of a `feed` call. -/
inductive Res where
  | ok (consumed : Nat) (verified : Option (Nat × Bytes))
  | err (e : E)

/-- The `Res` of a completed item that consumed `k` bytes. -/
def resOf (k : Nat) : Option Obs → Res
  | none => .ok k none
  | some (.released off d) => .ok k (some (off, d))
  | some (.err e) => .err e

/-- `next_item`'s item size narrowed to a `w`-bit `usize`: `usize::try_from(size).ok()?`. -/
def needW {Cv : Type} (w len log : Nat) (nd : Node Cv) : Option Nat := tryFrom w (needN len log nd)

/-- `RangeVerifier::feed` on a `w`-bit `usize`, as the code writes it. `none` is an arithmetic failure (an
overflow, an underflow): `feedCode_sim` shows it does not happen. The buffer holds `groupLen log` bytes
(`Layout.for_group_bytes`, `forGroupBytesM_iff`). -/
def feedCode (w : Nat) (c : Cfg Cv) (s : BS Cv) (input : Bytes) : Option (Res × BS Cv) :=
  if s.core.failed then some (.err (errOf s.errk), s)
  else if input = [] then some (.ok 0 none, s)
  else match s.core.stack with
    | [] => some (.err .tooMuchData, s)
    | nd :: _ =>
      match needW w c.len c.log nd with
      | none => some (.err .tooMuchData, s)
      | some need =>
        if s.buf = [] ∧ need ≤ input.length then
          match completeItem c s nd (input.take need) with
          | (s1, o) => some (resOf need o, s1)
        else
          match Machine.sub w need s.buf.length with
          | none => none
          | some room =>
            match Machine.add w s.buf.length (min input.length room) with
            | none => none
            | some e =>
              if groupLen c.log < e then some (.err .outputTooSmall, s)
              else if e < need then
                some (.ok (min input.length room) none, { s with buf := s.buf ++ input.take (min input.length room) })
              else if groupLen c.log < need then some (.err .outputTooSmall, s)
              else
                match completeItem c s nd (s.buf ++ input.take (min input.length room)) with
                | (s1, o) => some (resOf (min input.length room) o, s1)

/-- The events of a verified group, if any. -/
def relOf : Option (Nat × Bytes) → List Obs
  | none => []
  | some (off, d) => [.released off d]

/-- The caller's loop over one piece: feed the unconsumed tail until the piece is used up or a call fails.
`fuel` only makes the recursion structural; `drivePiece_eq` shows that the length of the piece is enough. -/
def drivePiece (w : Nat) (c : Cfg Cv) : Nat → BS Cv → Bytes → Option (BS Cv × List Obs)
  | 0, s, p => if p = [] then some (s, []) else none
  | f + 1, s, p =>
    if p = [] then some (s, []) else
    match feedCode w c s p with
    | none => none
    | some (.err e, s1) => some (s1, [.err e])
    | some (.ok k v, s1) =>
      match drivePiece w c f s1 (p.drop k) with
      | none => none
      | some (s2, o) => some (s2, relOf v ++ o)

/-- The caller feeding a list of pieces in order, stopping at the first error. -/
def driveAll (w : Nat) (c : Cfg Cv) : BS Cv → List Bytes → Option (BS Cv × List Obs)
  | s, [] => some (s, [])
  | s, p :: ps =>
    match drivePiece w c p.length s p with
    | none => none
    | some (s1, o1) =>
      if hasErr o1 then some (s1, o1) else
      match driveAll w c s1 ps with
      | none => none
      | some (s2, o2) => some (s2, o1 ++ o2)

/-- The item-by-item model: each item is completed whole. -/
def itemwise (c : Cfg Cv) : BS Cv → List Bytes → BS Cv × List Obs
  | s, [] => (s, [])
  | s, it :: its =>
    match s.core.stack with
    | [] => (s, [.err .tooMuchData])
    | nd :: _ =>
      match completeItem c s nd it with
      | (s1, none) => itemwise c s1 its
      | (s1, some (.err e)) => (s1, [.err e])
      | (s1, some (.released off d)) =>
        match itemwise c s1 its with
        | (s2, o) => (s2, .released off d :: o)

/-! ## Invariants -/

/-- A verifier state a stream can leave: the item model's invariant, a supported layout, and a buffer that
holds a proper prefix of the item the top node needs. -/
def Wf (c : Cfg Cv) (s : BS Cv) : Prop :=
  Inv c.n c.first c.last s.core ∧ c.len ≤ u64Max ∧ c.log ≤ 20 ∧ c.n = groups c.len c.log ∧ c.last ≤ c.n ∧
    (s.buf ≠ [] → ∃ nd rest, s.core.stack = nd :: rest ∧ s.buf.length < needN c.len c.log nd ∧ s.core.failed = false)

theorem needN_pos (c : Cfg Cv) (hwf : c.len ≤ u64Max ∧ c.n = groups c.len c.log) (nd : Node Cv)
    (h : nd.lo < nd.hi ∧ nd.hi ≤ c.n) : 1 ≤ needN c.len c.log nd := by
  unfold needN
  by_cases hl : nd.hi - nd.lo = 1
  · simp only [hl, ite_true]
    have := (groupSize_pos_iff c.len c.log nd.lo hwf.1).2 (by omega)
    omega
  · simp only [hl, ite_false]; omega

theorem needN_le (c : Cfg Cv) (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20) (nd : Node Cv) :
    needN c.len c.log nd ≤ groupLen c.log := by
  unfold needN
  have h1 := groupLen_ge c.log
  by_cases hl : nd.hi - nd.lo = 1
  · simp only [hl, ite_true]; exact groupSize_le_len c.len c.log nd.lo hlen
  · simp only [hl, ite_false]; omega

theorem needW_eq (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20)
    (nd : Node Cv) : needW w c.len c.log nd = some (needN c.len c.log nd) := by
  have h1 := needN_le c hlen hlog nd
  have h2 := groupLen_le c.log hlog
  have h3 : (2 : Nat) ^ 30 < 2 ^ w := by
    have : (2 : Nat) ^ 30 < 2 ^ 32 := by decide
    have h32 : 2 ^ 32 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  simp only [needW, tryFrom, show needN c.len c.log nd < 2 ^ w by omega, ite_true]

/-! ## The reference run -/

theorem bytes_nc (c : Cfg Cv) : ∀ (xs : Bytes) (s : BS Cv) (nd : Node Cv) (rest : List (Node Cv)),
    s.core.failed = false → s.core.stack = nd :: rest → s.buf.length + xs.length < needN c.len c.log nd →
    bytes c s xs = ({ s with buf := s.buf ++ xs }, []) := by
  intro xs
  induction xs with
  | nil => intro s nd rest _ _ _; simp [bytes]
  | cons b xs ih =>
    intro s nd rest hf hs hl
    have hl1 : s.buf.length + 1 < needN c.len c.log nd := by simp at hl ⊢; omega
    have hstep : stepByte c s b = ({ s with buf := s.buf ++ [b] }, none) := by
      simp [stepByte, hf, hs, hl1]
    have := ih { s with buf := s.buf ++ [b] } nd rest hf hs (by simp at hl ⊢; omega)
    simp only [bytes, hstep]
    rw [this]
    simp

theorem bytes_c (c : Cfg Cv) : ∀ (xs : Bytes) (s : BS Cv) (nd : Node Cv) (rest : List (Node Cv)),
    s.core.failed = false → s.core.stack = nd :: rest → xs ≠ [] → s.buf.length + xs.length = needN c.len c.log nd →
    bytes c s xs = ((completeItem c s nd (s.buf ++ xs)).1, obsList (completeItem c s nd (s.buf ++ xs)).2) := by
  intro xs
  induction xs with
  | nil => intro s nd rest _ _ h; exact absurd rfl h
  | cons b xs ih =>
    intro s nd rest hf hs _ hl
    by_cases hx : xs = []
    · subst hx
      have hl1 : ¬ s.buf.length + 1 < needN c.len c.log nd := by simp at hl ⊢; omega
      have hstep : stepByte c s b = completeItem c s nd (s.buf ++ [b]) := by
        simp [stepByte, hf, hs, hl1]
      simp only [bytes, hstep, List.append_nil, List.singleton_append] at *
      rcases hco : completeItem c s nd (s.buf ++ [b]) with ⟨s1, o⟩
      rcases o with _ | o
      · simp [bytes, obsList]
      · cases o <;> simp [bytes, obsList]
    · have hl1 : s.buf.length + 1 < needN c.len c.log nd := by
        have : xs.length ≥ 1 := by
          cases xs with
          | nil => exact absurd rfl hx
          | cons _ _ => simp
        simp at hl ⊢; omega
      have hstep : stepByte c s b = ({ s with buf := s.buf ++ [b] }, none) := by
        simp [stepByte, hf, hs, hl1]
      have := ih { s with buf := s.buf ++ [b] } nd rest hf hs hx (by simp at hl ⊢; omega)
      simp only [bytes, hstep]
      rw [this]
      simp [completeItem, List.append_assoc]

theorem bytes_append_err (c : Cfg Cv) : ∀ (xs ys : Bytes) (s : BS Cv), hasErr (bytes c s xs).2 = true →
    bytes c s (xs ++ ys) = bytes c s xs := by
  intro xs
  induction xs with
  | nil => intro ys s h; simp [bytes, hasErr] at h
  | cons b xs ih =>
    intro ys s h
    simp only [List.cons_append, bytes]
    rcases hs : stepByte c s b with ⟨s1, o⟩
    rcases o with _ | o
    · simp only [bytes, hs] at h
      simp only []
      exact ih ys s1 h
    · cases o with
      | err e => simp
      | released off d =>
        simp only [bytes, hs] at h ⊢
        rcases hb : bytes c s1 xs with ⟨s2, o2⟩
        rw [hb] at h
        have h' : hasErr o2 = true := by simpa [hasErr] using h
        have := ih ys s1 (by rw [hb]; exact h')
        rw [this, hb]

theorem bytes_append_ok (c : Cfg Cv) : ∀ (xs ys : Bytes) (s : BS Cv), hasErr (bytes c s xs).2 = false →
    bytes c s (xs ++ ys) =
      ((bytes c (bytes c s xs).1 ys).1, (bytes c s xs).2 ++ (bytes c (bytes c s xs).1 ys).2) := by
  intro xs
  induction xs with
  | nil => intro ys s h; simp [bytes]
  | cons b xs ih =>
    intro ys s h
    simp only [List.cons_append, bytes]
    rcases hs : stepByte c s b with ⟨s1, o⟩
    rcases o with _ | o
    · simp only [bytes, hs] at h ⊢
      exact ih ys s1 h
    · cases o with
      | err e => simp [bytes, hs, hasErr] at h
      | released off d =>
        simp only [bytes, hs] at h ⊢
        rcases hb : bytes c s1 xs with ⟨s2, o2⟩
        rw [hb] at h
        have h' : hasErr o2 = false := by simpa [hasErr] using h
        have := ih ys s1 (by rw [hb]; exact h')
        rw [this, hb]
        simp

/-! ## One call is the reference run over the bytes it consumed -/

/-- The events a call reports. -/
def resObs : Res → List Obs
  | .ok _ v => relOf v
  | .err e => [.err e]

theorem completeItem_cases (c : Cfg Cv) (s : BS Cv) (nd : Node Cv) (item : Bytes) :
    ((completeItem c s nd item).1.core.failed = true ∧
      ∃ e, (completeItem c s nd item).2 = some (.err e) ∧ (e = .parentMismatch ∨ e = .groupMismatch)) ∨
    ((completeItem c s nd item).1.core.failed = false ∧
      ((completeItem c s nd item).2 = none ∨ ∃ off d, (completeItem c s nd item).2 = some (.released off d))) := by
  unfold completeItem
  by_cases h : (Tree.feed c.H c.n c.first c.last s.core (c.rd item)).failed = true
  · left
    by_cases hl : nd.hi - nd.lo = 1 <;> simp [h, hl, errOf]
  · right
    have h' : (Tree.feed c.H c.n c.first c.last s.core (c.rd item)).failed = false := by simpa using h
    by_cases hl : nd.hi - nd.lo = 1 <;> simp [h', hl]

theorem completeItem_wf (c : Cfg Cv) (s : BS Cv) (hwf : Wf c s) (nd : Node Cv) (item : Bytes) :
    Wf c (completeItem c s nd item).1 := by
  obtain ⟨hI, h2, h3, h4, h5, _⟩ := hwf
  have hf := feed_inv c.H c.n c.first c.last s.core (c.rd item) h5 hI
  unfold completeItem
  by_cases h : (Tree.feed c.H c.n c.first c.last s.core (c.rd item)).failed = true
  · simp only [h, ite_true]; exact ⟨hf, h2, h3, h4, h5, fun hb => absurd rfl hb⟩
  · simp only [h, ite_false]; exact ⟨hf, h2, h3, h4, h5, fun hb => absurd rfl hb⟩

/-- (One call.) From a state a stream can leave, a call with a nonempty input is the reference run over exactly
the bytes it consumed: the same state, the same events. The call does not fail arithmetically, narrows without
loss, never raises `OutputTooSmall` and never reports `TooMuchData` for a verifier that is not complete. On
success it consumes between 1 and `input.length` bytes, and the verifier is not failed. -/
theorem feedCode_sim (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (s : BS Cv) (hwf : Wf c s)
    (hnf : s.core.failed = false) (input : Bytes) (hne : input ≠ []) :
    ∃ r s1, feedCode w c s input = some (r, s1) ∧ Wf c s1 ∧
      ∃ k, k ≤ input.length ∧ 1 ≤ k ∧ bytes c s (input.take k) = (s1, resObs r) ∧
        (∀ k' v, r = .ok k' v → k' = k ∧ s1.core.failed = false) ∧
        (∀ e, r = .err e → e ≠ .outputTooSmall ∧ (e = .tooMuchData → s.core.stack = [])) := by
  have hwf' := hwf
  obtain ⟨hI, hlen, hlog, hn, hlast, hbuf⟩ := hwf
  have hlen1 : 1 ≤ input.length := by
    cases input with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  rcases hst : s.core.stack with _ | ⟨nd, rest⟩
  · refine ⟨.err .tooMuchData, s, by simp [feedCode, hnf, hst, hne], hwf', 1, hlen1, Nat.le_refl _, ?_, ?_, ?_⟩
    · cases input with
      | nil => exact absurd rfl hne
      | cons b t => simp [bytes, stepByte, hnf, hst, resObs]
    · intro k' v h; cases h
    · intro e h; cases h; simp [hst]
  · have hnd := hI.1 nd (by rw [hst]; exact List.mem_cons_self ..)
    have hp := needN_pos c ⟨hlen, hn⟩ nd ⟨hnd.1, hnd.2.1⟩
    have hle := needN_le c hlen hlog nd
    have hW := needW_eq w hw c hlen hlog nd
    have hg2 := groupLen_le c.log hlog
    have h32 : (2 : Nat) ^ 30 < 2 ^ w := by
      have : (2 : Nat) ^ 30 < 2 ^ 32 := by decide
      have h32 : 2 ^ 32 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hfill : s.buf.length < needN c.len c.log nd := by
      by_cases hb : s.buf = []
      · simp [hb]; omega
      · obtain ⟨nd', rest', hs', hl', _⟩ := hbuf hb
        rw [hst] at hs'
        obtain ⟨rfl, rfl⟩ := List.cons.inj hs'
        exact hl'
    by_cases hfast : s.buf = [] ∧ needN c.len c.log nd ≤ input.length
    · -- the fast path: the whole item is in the input and nothing is buffered
      rcases hco : completeItem c s nd (input.take (needN c.len c.log nd)) with ⟨s1, o⟩
      have hcw := completeItem_wf c s hwf' nd (input.take (needN c.len c.log nd))
      rw [hco] at hcw
      have hlen_take : (input.take (needN c.len c.log nd)).length = needN c.len c.log nd := by
        simp; omega
      have hb := bytes_c c (input.take (needN c.len c.log nd)) s nd rest hnf hst
        (by intro h; rw [h] at hlen_take; simp at hlen_take; omega) (by rw [hfast.1]; simp [hlen_take])
      rw [hfast.1] at hb
      simp only [List.nil_append] at hb
      rw [hco] at hb
      have hcases := completeItem_cases c s nd (input.take (needN c.len c.log nd))
      rw [hco] at hcases
      refine ⟨resOf (needN c.len c.log nd) o, s1, ?_, hcw, needN c.len c.log nd, hfast.2, hp, ?_, ?_, ?_⟩
      · simp [feedCode, hnf, hne, hst, hW, hfast.1, hfast.2, hco]
      · rw [hb]
        congr 1
        rcases o with _ | o
        · rfl
        · cases o <;> rfl
      · intro k' v h
        rcases hcases with ⟨hf, e, he, _⟩ | ⟨hf, ho⟩
        · subst he; simp [resOf] at h
        · rcases ho with ho | ⟨off, d, ho⟩ <;> subst ho <;> simp [resOf] at h <;> exact ⟨h.1.symm, hf⟩
      · intro e h
        rcases hcases with ⟨hf, e', he, hk⟩ | ⟨hf, ho⟩
        · subst he
          simp [resOf] at h
          subst h
          rcases hk with rfl | rfl <;> simp
        · rcases ho with ho | ⟨off, d, ho⟩ <;> subst ho <;> simp [resOf] at h
    · -- the buffered path
      have hroom : Machine.sub w (needN c.len c.log nd) s.buf.length = some (needN c.len c.log nd - s.buf.length) := by
        simp [Machine.sub]; omega
      have htake1 : 1 ≤ min input.length (needN c.len c.log nd - s.buf.length) := by omega
      have htakeL : min input.length (needN c.len c.log nd - s.buf.length) ≤ input.length := Nat.min_le_left _ _
      have htakeN : s.buf.length + min input.length (needN c.len c.log nd - s.buf.length) ≤ needN c.len c.log nd := by
        omega
      have hend : Machine.add w s.buf.length (min input.length (needN c.len c.log nd - s.buf.length)) =
          some (s.buf.length + min input.length (needN c.len c.log nd - s.buf.length)) := by
        simp only [Machine.add]
        rw [if_pos (by omega)]
      have hxs : (input.take (min input.length (needN c.len c.log nd - s.buf.length))).length =
          min input.length (needN c.len c.log nd - s.buf.length) := by
        simp
      have hg1 : ¬ groupLen c.log < s.buf.length + min input.length (needN c.len c.log nd - s.buf.length) := by omega
      by_cases hlt : s.buf.length + min input.length (needN c.len c.log nd - s.buf.length) < needN c.len c.log nd
      · -- the item is still incomplete: the bytes are buffered
        have hb := bytes_nc c (input.take (min input.length (needN c.len c.log nd - s.buf.length))) s nd rest hnf hst
          (by rw [hxs]; omega)
        have hwf2 : Wf c { s with buf := s.buf ++ input.take (min input.length (needN c.len c.log nd - s.buf.length)) } := by
          refine ⟨hI, hlen, hlog, hn, hlast, ?_⟩
          intro _
          refine ⟨nd, rest, hst, ?_, hnf⟩
          simp only [List.length_append, hxs]
          omega
        refine ⟨.ok (min input.length (needN c.len c.log nd - s.buf.length)) none, { s with buf := s.buf ++ input.take (min input.length (needN c.len c.log nd - s.buf.length)) }, ?_, hwf2, (min input.length (needN c.len c.log nd - s.buf.length)), htakeL, htake1, hb, ?_, ?_⟩
        · simp [feedCode, hnf, hne, hst, hW, hfast, hroom, hend, hg1, hlt]
        · intro k' v h; cases h; exact ⟨rfl, hnf⟩
        · intro e h; cases h
      · -- the item completes with this call
        have heq : s.buf.length + min input.length (needN c.len c.log nd - s.buf.length) = needN c.len c.log nd := by omega
        have hg2' : ¬ groupLen c.log < needN c.len c.log nd := by omega
        rcases hco : completeItem c s nd (s.buf ++ input.take (min input.length (needN c.len c.log nd - s.buf.length))) with ⟨s1, o⟩
        have hcw := completeItem_wf c s hwf' nd
          (s.buf ++ input.take (min input.length (needN c.len c.log nd - s.buf.length)))
        rw [hco] at hcw
        have hb := bytes_c c (input.take (min input.length (needN c.len c.log nd - s.buf.length))) s nd rest hnf hst
          (by intro h; rw [h] at hxs; simp at hxs; omega) (by rw [hxs]; exact heq)
        rw [hco] at hb
        have hcases := completeItem_cases c s nd
          (s.buf ++ input.take (min input.length (needN c.len c.log nd - s.buf.length)))
        rw [hco] at hcases
        refine ⟨resOf (min input.length (needN c.len c.log nd - s.buf.length)) o, s1, ?_, hcw, (min input.length (needN c.len c.log nd - s.buf.length)), htakeL, htake1, ?_, ?_, ?_⟩
        · simp [feedCode, hnf, hne, hst, hW, hfast, hroom, hend, hg1, hlt, hg2', hco]
        · rw [hb]
          congr 1
          rcases o with _ | o
          · rfl
          · cases o <;> rfl
        · intro k' v h
          rcases hcases with ⟨hf, e, he, _⟩ | ⟨hf, ho⟩
          · subst he; simp [resOf] at h
          · rcases ho with ho | ⟨off, d, ho⟩ <;> subst ho <;> simp [resOf] at h <;> exact ⟨h.1.symm, hf⟩
        · intro e h
          rcases hcases with ⟨hf, e', he, hk⟩ | ⟨hf, ho⟩
          · subst he
            simp [resOf] at h
            subst h
            rcases hk with rfl | rfl <;> simp
          · rcases ho with ho | ⟨off, d, ho⟩ <;> subst ho <;> simp [resOf] at h

/-! ## Any split of the stream -/

/-- One piece: the caller's loop is the reference run over the piece, step for step, and never gets stuck. -/
theorem drivePiece_eq (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) :
    ∀ (f : Nat) (s : BS Cv) (p : Bytes), p.length ≤ f → Wf c s → s.core.failed = false →
      ∃ s1 o, drivePiece w c f s p = some (s1, o) ∧ bytes c s p = (s1, o) ∧ Wf c s1 ∧
        (hasErr o = false → s1.core.failed = false) := by
  intro f
  induction f with
  | zero =>
    intro s p hp hwf hnf
    have : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨s, [], by simp [drivePiece], by simp [bytes], hwf, fun _ => hnf⟩
  | succ f ih =>
    intro s p hp hwf hnf
    by_cases hpn : p = []
    · subst hpn
      exact ⟨s, [], by simp [drivePiece], by simp [bytes], hwf, fun _ => hnf⟩
    · obtain ⟨r, s1, hfc, hw1, k, hk, hk1, hb, hok, herr⟩ := feedCode_sim w hw c s hwf hnf p hpn
      cases r with
      | err e =>
        have hs : hasErr (bytes c s (p.take k)).2 = true := by rw [hb]; simp [resObs, hasErr]
        have := bytes_append_err c (p.take k) (p.drop k) s hs
        rw [List.take_append_drop] at this
        refine ⟨s1, [.err e], by simp [drivePiece, hpn, hfc], ?_, hw1, by simp [hasErr]⟩
        rw [this, hb]; rfl
      | ok k' v =>
        obtain ⟨hkk, hnf1⟩ := hok k' v rfl
        subst hkk
        have hs : hasErr (bytes c s (p.take k')).2 = false := by
          rw [hb]; rcases v with _ | ⟨off, d⟩ <;> simp [resObs, relOf, hasErr]
        have hap := bytes_append_ok c (p.take k') (p.drop k') s hs
        rw [List.take_append_drop, hb] at hap
        dsimp only at hap
        have hlen : (p.drop k').length ≤ f := by simp; omega
        obtain ⟨s2, o2, hd, hb2, hw2, hf2⟩ := ih s1 (p.drop k') hlen hw1 hnf1
        refine ⟨s2, relOf v ++ o2, ?_, ?_, hw2, ?_⟩
        · simp [drivePiece, hpn, hfc, hd]
        · have hres : bytes c s p = (s2, resObs (.ok k' v) ++ o2) := by rw [hap, hb2]
          exact hres
        · intro h
          apply hf2
          rcases v with _ | ⟨off, d⟩ <;> simpa [relOf, hasErr] using h

/-- Any list of pieces: the caller feeding them in order is the reference run over the concatenated stream. -/
theorem driveAll_eq (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) :
    ∀ (ps : List Bytes) (s : BS Cv), Wf c s → s.core.failed = false →
      ∃ s1 o, driveAll w c s ps = some (s1, o) ∧ bytes c s ps.flatten = (s1, o) := by
  intro ps
  induction ps with
  | nil => intro s _ _; exact ⟨s, [], by simp [driveAll], by simp [bytes]⟩
  | cons p ps ih =>
    intro s hwf hnf
    obtain ⟨s1, o1, hd, hb, hw1, hf1⟩ := drivePiece_eq w hw c p.length s p (Nat.le_refl _) hwf hnf
    by_cases he : hasErr o1 = true
    · have := bytes_append_err c p ps.flatten s (by rw [hb]; exact he)
      refine ⟨s1, o1, by simp [driveAll, hd, he], ?_⟩
      simp only [List.flatten_cons]
      rw [this, hb]
    · have he' : hasErr o1 = false := by simpa using he
      obtain ⟨s2, o2, hd2, hb2⟩ := ih s1 hw1 (hf1 he')
      have hap := bytes_append_ok c p ps.flatten s (by rw [hb]; exact he')
      refine ⟨s2, o1 ++ o2, by simp [driveAll, hd, he, hd2], ?_⟩
      simp only [List.flatten_cons]
      rw [hap, hb]
      simp only [hb2]

/-- (Split invariance.) Feeding a stream in any split into pieces, the caller feeding the unconsumed tail of
each piece until it is used up and stopping at the first error, gives exactly the reference run over the whole
stream: the same final state, the same errors and the same released groups with the same bytes. In particular two
splits of the same stream, such as one piece against single bytes, agree on everything. -/
theorem split_invariance (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (s : BS Cv) (hwf : Wf c s)
    (hnf : s.core.failed = false) (ps qs : List Bytes) (h : ps.flatten = qs.flatten) :
    ∃ s1 o, driveAll w c s ps = some (s1, o) ∧ driveAll w c s qs = some (s1, o) ∧ bytes c s ps.flatten = (s1, o) := by
  obtain ⟨s1, o, hd, hb⟩ := driveAll_eq w hw c ps s hwf hnf
  obtain ⟨s2, o2, hd2, hb2⟩ := driveAll_eq w hw c qs s hwf hnf
  rw [← h, hb] at hb2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hb2
  exact ⟨s1, o, hd, hd2, hb⟩

/-- A fresh verifier (`RangeVerifier::new`: the root alone on the stack, nothing buffered, not failed) is a state
the theorems above apply to. -/
theorem wf_init (c : Cfg Cv) (root : Cv) (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20)
    (hn : c.n = groups c.len c.log) (hl : c.last ≤ c.n) :
    Wf c ⟨Tree.init root c.n c.first c.last, [], false⟩ ∧
      (⟨Tree.init root c.n c.first c.last, [], false⟩ : BS Cv).core.failed = false :=
  ⟨⟨init_inv root c.n c.first c.last hl, hlen, hlog, hn, hl, fun h => absurd rfl h⟩, rfl⟩

/-! ## Item boundaries -/

/-- A list of items that the verifier takes whole one after the other from a state with an empty buffer: each
has the size the top node needs. -/
def Aligned (c : Cfg Cv) : BS Cv → List Bytes → Prop
  | _, [] => True
  | s, it :: its =>
    s.core.failed = false ∧ s.buf = [] ∧
      ∃ nd rest, s.core.stack = nd :: rest ∧ it.length = needN c.len c.log nd ∧
        Aligned c (completeItem c s nd it).1 its

theorem bytes_items (c : Cfg Cv) : ∀ (its : List Bytes) (s : BS Cv), Wf c s → Aligned c s its →
    bytes c s its.flatten = itemwise c s its := by
  intro its
  induction its with
  | nil => intro s _ _; simp [bytes, itemwise]
  | cons it its ih =>
    intro s hwf ⟨hnf, hb, nd, rest, hst, hlen, hal⟩
    obtain ⟨hI, hl, hlog, hn, hlast, _⟩ := hwf
    have hnd := hI.1 nd (by rw [hst]; exact List.mem_cons_self ..)
    have hp := needN_pos c ⟨hl, hn⟩ nd ⟨hnd.1, hnd.2.1⟩
    have hne : it ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    have hc := bytes_c c it s nd rest hnf hst hne (by rw [hb]; simpa using hlen)
    rw [hb, List.nil_append] at hc
    have hwf' : Wf c s := ⟨hI, hl, hlog, hn, hlast, fun h => absurd hb h⟩
    have hw1 := completeItem_wf c s hwf' nd it
    simp only [List.flatten_cons, itemwise, hst]
    rcases hco : completeItem c s nd it with ⟨s1, o⟩
    rw [hco] at hc hw1 hal
    dsimp only at hc hw1 hal
    rcases o with _ | o
    · have hap := bytes_append_ok c it its.flatten s (by rw [hc]; simp [obsList, hasErr])
      rw [hap, hc]
      simp only [obsList, List.nil_append]
      exact ih s1 hw1 hal
    · cases o with
      | err e =>
        have := bytes_append_err c it its.flatten s (by rw [hc]; simp [obsList, hasErr])
        rw [this, hc]; rfl
      | released off d =>
        have hap := bytes_append_ok c it its.flatten s (by rw [hc]; simp [obsList, hasErr])
        rw [hap, hc]
        simp only [obsList]
        rw [ih s1 hw1 hal]
        rfl

/-- The item-by-item run ends in the state of the item model `Tree.run` over the items read. -/
theorem itemwise_core (c : Cfg Cv) : ∀ (its : List Bytes) (s : BS Cv), Aligned c s its →
    (itemwise c s its).1.core = Tree.run c.H c.n c.first c.last s.core (its.map c.rd) := by
  intro its
  induction its with
  | nil => intro s _; simp [itemwise, Tree.run]
  | cons it its ih =>
    intro s ⟨hnf, hb, nd, rest, hst, hlen, hal⟩
    simp only [itemwise, hst, List.map_cons, Tree.run, List.foldl_cons]
    rcases hco : completeItem c s nd it with ⟨s1, o⟩
    have hcore : s1.core = Tree.feed c.H c.n c.first c.last s.core (c.rd it) := by
      have := congrArg (fun x => x.1.core) hco
      simp only [completeItem] at this
      split at this <;> simpa using this.symm
    rw [hco] at hal
    have hrec := ih s1 hal
    rcases o with _ | o
    · simpa [Tree.run, hcore] using hrec
    · cases o with
      | err e =>
        have hf : s1.core.failed = true := by
          rcases completeItem_cases c s nd it with ⟨hf, _⟩ | ⟨hf, ho⟩
          · rw [hco] at hf; exact hf
          · rw [hco] at ho; rcases ho with ho | ⟨_, _, ho⟩ <;> simp at ho
        cases its with
        | nil => simpa [Tree.run] using hcore
        | cons x xs =>
          dsimp only at hal
          exact absurd hal.1 (by simp [hf])
      | released off d =>
        simp only []
        simpa [Tree.run, hcore] using hrec

/-- (Stream equivalence.) A stream that is a sequence of items the verifier takes whole, fed in any split into
pieces, gives the item-by-item run: the caller's result is the item model's, and its core state is the
state of `Tree.run` over the items read. -/
theorem stream_equiv (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (s : BS Cv) (hwf : Wf c s)
    (hnf : s.core.failed = false) (its : List Bytes) (hal : Aligned c s its) (ps : List Bytes)
    (hps : ps.flatten = its.flatten) :
    driveAll w c s ps = some (itemwise c s its) ∧
      (itemwise c s its).1.core = Tree.run c.H c.n c.first c.last s.core (its.map c.rd) := by
  obtain ⟨s1, o, hd, hb⟩ := driveAll_eq w hw c ps s hwf hnf
  rw [hps, bytes_items c its s hwf hal] at hb
  exact ⟨by rw [hb]; exact hd, itemwise_core c its s hal⟩

/-! ## The arithmetic of `Walk::complete` and `next_item` -/

/-- Every `u64` operation of `next_item` and `Walk::complete` succeeds on a node of the stack: the subtraction
`hi - lo`, the group offset `lo * group_len`, the split `lo + left_groups(hi - lo)`. -/
theorem complete_arith (il : Nat → Nat) (hil : ∀ x, 0 < x → x < 2 ^ 64 → IsIlog2 x (il x)) (len log n : Nat)
    (hn : n = groups len log) (hlen : len ≤ u64Max) (hlog : log ≤ 20) (nd : Node Cv)
    (h : nd.lo < nd.hi ∧ nd.hi ≤ n) :
    Machine.sub 64 nd.hi nd.lo = some (nd.hi - nd.lo) ∧
    (nd.hi - nd.lo = 1 → Machine.mul 64 nd.lo (groupLen log) = some (nd.lo * groupLen log)) ∧
    (nd.hi - nd.lo ≠ 1 → leftGroupsM il (nd.hi - nd.lo) = some (leftGroups (nd.hi - nd.lo)) ∧
      Machine.add 64 nd.lo (leftGroups (nd.hi - nd.lo)) = some (nd.lo + leftGroups (nd.hi - nd.lo))) := by
  have hb : n ≤ 2 ^ 54 := hn ▸ groups_le len log hlen
  have e54 : (2 : Nat) ^ 54 < 2 ^ 64 := by decide
  refine ⟨by simp [Machine.sub]; omega, ?_, ?_⟩
  · intro h1
    have hlt : nd.lo < groups len log := by omega
    have hm := (lt_groups_iff len log nd.lo).1 hlt
    have : nd.lo * groupLen log < 2 ^ 64 := by unfold u64Max at hlen; omega
    simp [Machine.mul, this]
  · intro h1
    have h2 : nd.hi - nd.lo ≥ 2 := by omega
    have hl3 := leftGroups_lt _ h2
    have hc : nd.hi - nd.lo < 2 ^ 64 := by omega
    refine ⟨leftGroupsM_eq il hil _ hc, ?_⟩
    have : nd.lo + leftGroups (nd.hi - nd.lo) < 2 ^ 64 := by omega
    simp [Machine.add, this]

end

end Pinc.VerifyBytes

#audit_axioms Pinc.VerifyBytes.feedCode_sim
#audit_axioms Pinc.VerifyBytes.split_invariance
#audit_axioms Pinc.VerifyBytes.stream_equiv
#audit_axioms Pinc.VerifyBytes.complete_arith
#audit_axioms Pinc.VerifyBytes.wf_init
#audit_axioms Pinc.VerifyBytes.needW_eq
#audit_axioms Pinc.VerifyBytes.drivePiece_eq
#audit_axioms Pinc.VerifyBytes.driveAll_eq
#audit_axioms Pinc.VerifyBytes.bytes_items
#audit_axioms Pinc.VerifyBytes.itemwise_core
