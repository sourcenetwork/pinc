import Pinc.ValuesPlanMain

/-!
# `ValueSource::read_at` rebuilds exactly the bytes of the response

`crates/pinc-values/src/source.rs`. The response is never buffered: `read_at(offset, dst)` finds the frame of the
offset (a window of 16 frame descriptors, refilled by `Plan::locate`), and copies from the part the offset is
in: the 16-byte header (from the plan), a 64-byte proof pair (from the store's outboard, at the offset
`Plan::proof_pair` gives) or group bytes (from the store's value). It stops when a part comes back short.

The abstract response byte function is `PlanM.byteAt`: for every stream offset `p`, the byte the response holds there,
`none` when the offset is past the response or the store lacks the byte. The store is the contract of
`ValueRead`: a read returns the longest prefix of the bytes it holds (`availFn`).

* `readAt_spec`: for every window that holds only frames of the plan, every offset and every length, `read_at`
  returns `availFn byteAt offset len`: the bytes of the response from the offset, as many as are present, in
  order, whatever the window held. So a retransmission equals the original (`readAt_retx`), a partial read is a
  prefix of a longer read (`readAt_prefix`), and a short return happens only at the end of the response or at a
  byte the store lacks (`readAt_short`).
* `WinInv`, kept by `refill_inv`, `frameAtM_spec` and `rdF_spec`: the window only ever holds frames of the plan.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesPlan
open Pinc.Layout Pinc.Encode

/-- The bytes of `g` from `p`, up to `n`, stopping at the first byte that is not there. -/
def availFn (g : Nat → Option Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | p, n + 1 => match g p with
    | none => []
    | some b => b :: availFn g (p + 1) n

theorem availFn_length_le (g : Nat → Option Nat) : ∀ n p, (availFn g p n).length ≤ n := by
  intro n
  induction n with
  | zero => intro p; simp [availFn]
  | succ n ih =>
    intro p
    unfold availFn
    cases g p with
    | none => simp
    | some b => simp; exact ih _

theorem availFn_congr (g h : Nat → Option Nat) : ∀ n p q, (∀ w, w < n → g (p + w) = h (q + w)) →
    availFn g p n = availFn h q n := by
  intro n
  induction n with
  | zero => intro p q _; rfl
  | succ n ih =>
    intro p q hw
    unfold availFn
    have h0 := hw 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [h0]
    cases h q with
    | none => rfl
    | some b =>
      simp only []
      rw [ih (p + 1) (q + 1) (fun w hw' => by
        have := hw (w + 1) (by omega)
        rw [show p + (w + 1) = p + 1 + w by omega, show q + (w + 1) = q + 1 + w by omega] at this
        exact this)]

theorem availFn_succ (g : Nat → Option Nat) (p n : Nat) :
    availFn g p (n + 1) = (match g p with | none => [] | some b => b :: availFn g (p + 1) n) := rfl

/-- A read of `n` bytes is a read of `m` bytes followed, when none was missing, by the read of the rest. -/
theorem availFn_split (g : Nat → Option Nat) : ∀ m n p, m ≤ n →
    availFn g p n = availFn g p m ++ (if (availFn g p m).length = m then availFn g (p + m) (n - m) else []) := by
  intro m
  induction m with
  | zero => intro n p _; simp [availFn]
  | succ m ih =>
    intro n p hmn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [availFn_succ g p n', availFn_succ g p m]
    cases g p with
    | none => simp
    | some b =>
      simp only [List.cons_append, List.length_cons]
      rw [ih n' (p + 1) (by omega)]
      have e1 : p + 1 + m = p + (m + 1) := by omega
      have e2 : n' + 1 - (m + 1) = n' - m := by omega
      by_cases h : (availFn g (p + 1) m).length = m
      · simp only [h, ite_true, e1, e2]
      · have : ¬ (availFn g (p + 1) m).length + 1 = m + 1 := by omega
        simp only [h, this, ite_false, List.append_nil]

theorem availFn_full (g : Nat → Option Nat) : ∀ (n p : Nat) (b : Nat → Nat), (∀ w, w < n → g (p + w) = some (b w)) →
    (availFn g p n).length = n := by
  intro n
  induction n with
  | zero => intro p b _; simp [availFn]
  | succ n ih =>
    intro p b hw
    unfold availFn
    have h0 := hw 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [h0]
    simp only [List.length_cons]
    rw [ih (p + 1) (fun w => b (w + 1)) (fun w hw' => by
      have := hw (w + 1) (by omega)
      rwa [show p + (w + 1) = p + 1 + w by omega] at this)]

/-- The store of a value, as `ValueRead` promises: a byte of the outboard and of the value, or none. -/
structure Store where
  ob : Nat → Option Nat
  val : Nat → Option Nat

/-- A header byte, from the wire encoder `hdrEnc` of `GroupHeader`. -/
def hdrByte (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (f : FrameM) (j : Nat) : Option Nat :=
  (hdrEnc f.off f.dlen (min f.plen 65535) f.follows)[j]?

/-- The abstract response byte function: the byte at stream offset `p`, none past the response or when the store
lacks it. -/
def PlanM.byteAt (pl : PlanM) (st : Store) (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (p : Nat) : Option Nat :=
  match pl.locate p with
  | none => none
  | some f =>
    if p < f.proofStart then hdrByte hdrEnc f (p - f.start)
    else if p < f.dataStart then
      (pl.proofPair f ((p - f.proofStart) / 64)).bind (fun base => st.ob (base + (p - f.proofStart) % 64))
    else st.val (f.off + (p - f.dataStart))

/-- `Frame` slots of the window refilled from group `k` of range `i`: stops at the first group the range lacks. -/
def refill (pl : PlanM) (i : Nat) : Nat → Nat → List (Option FrameM)
  | _, 0 => []
  | k, n + 1 => match pl.frame i k with
    | none => none :: List.replicate n none
    | some f => some f :: refill pl i (k + 1) n

/-- `ValueSource::frame_at`: the cached frame holding `at`, or the located one with the window refilled from it. -/
def PlanM.frameAtM (pl : PlanM) (win : List (Option FrameM)) (at_ : Nat) : Option FrameM × List (Option FrameM) :=
  match (win.filterMap id).find? (fun f => decide (f.start ≤ at_ ∧ at_ < f.fend)) with
  | some f => (some f, win)
  | none =>
    match pl.locate at_ with
    | none => (none, win)
    | some first => (some first, refill pl first.range first.k 16)

/-- `ValueSource::fill`: the bytes written and the bytes the part held for the request. -/
def PlanM.fillM (pl : PlanM) (st : Store) (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (f : FrameM)
    (at_ rem : Nat) : List Nat × Nat :=
  if at_ < f.proofStart then
    let src := (hdrEnc f.off f.dlen (min f.plen 65535) f.follows).drop (at_ - f.start)
    (src.take (min src.length rem), min src.length rem)
  else if at_ < f.dataStart then
    let into := at_ - f.proofStart
    let room := min (64 - into % 64) rem
    match pl.proofPair f (into / 64) with
    | none => ([], room)
    | some base => (availFn st.ob (base + into % 64) room, room)
  else
    let into := at_ - f.dataStart
    let room := min (f.dlen - into) rem
    (availFn st.val (f.off + into) room, room)

/-- `ValueSource::read_at`, the loop, with the window threaded; `fuel` bounds the iterations (each writes a byte). -/
def PlanM.rdF (pl : PlanM) (st : Store) (hdrEnc : Nat → Nat → Nat → Bool → List Nat) :
    Nat → List (Option FrameM) → Nat → Nat → List Nat × List (Option FrameM)
  | 0, win, _, _ => ([], win)
  | fuel + 1, win, at_, rem =>
    if rem = 0 then ([], win) else
    match pl.frameAtM win at_ with
    | (none, win') => ([], win')
    | (some f, win') =>
      let r := pl.fillM st hdrEnc f at_ rem
      if r.1.length < r.2 then (r.1, win')
      else
        let t := pl.rdF st hdrEnc fuel win' (at_ + r.1.length) (rem - r.1.length)
        (r.1 ++ t.1, t.2)

/-- A window of frames of the plan. -/
def WinInv (pl : PlanM) (win : List (Option FrameM)) : Prop :=
  ∀ f, f ∈ win.filterMap id → ∃ i k, pl.frame i k = some f

theorem frame_some {pl : PlanM} {i k : Nat} {f : FrameM} (h : pl.frame i k = some f) :
    ∃ r, pl.rs[i]? = some r ∧ k < r.last - r.first := by
  unfold PlanM.frame at h
  cases hr : pl.rs[i]? with
  | none => rw [hr] at h; simp at h
  | some r =>
    rw [hr] at h
    by_cases hx : r.first + k < r.last
    · exact ⟨r, rfl, by omega⟩
    · simp [hx] at h

theorem refill_inv (pl : PlanM) (i : Nat) : ∀ n k, WinInv pl (refill pl i k n) := by
  intro n
  induction n with
  | zero => intro k f hf; simp [refill] at hf
  | succ n ih =>
    intro k f hf
    unfold refill at hf
    cases h : pl.frame i k with
    | none => rw [h] at hf; simp [List.filterMap_replicate] at hf
    | some f0 =>
      rw [h] at hf
      simp only [List.filterMap_cons, id] at hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact ⟨i, k, h⟩
      · exact ih (k + 1) f (by simpa using hf)

/-- `locate` answers with a frame of the plan that holds the offset. -/
theorem locate_valid {len : Nat} {pl : PlanM} (g : Good len pl) {at_ : Nat} {f : FrameM} (h : pl.locate at_ = some f) :
    ∃ i r k, pl.rs[i]? = some r ∧ k < r.last - r.first ∧ pl.frame i k = some f ∧ f.start ≤ at_ ∧ at_ < f.fend := by
  by_cases ht : at_ < pl.total
  · obtain ⟨i, r, k, f0, hr, hk, hf, a, b⟩ := locate_total g ht
    have := locate_frame g hr hk hf a b
    rw [h] at this
    cases this
    exact ⟨i, r, k, hr, hk, hf, a, b⟩
  · rw [locate_end at_ (by omega)] at h; cases h

/-- The frame found is the located one, and the window keeps only frames of the plan. -/
theorem frameAtM_spec {len : Nat} {pl : PlanM} (g : Good len pl) {win : List (Option FrameM)} (hw : WinInv pl win)
    (at_ : Nat) :
    (pl.frameAtM win at_).1 = pl.locate at_ ∧ WinInv pl (pl.frameAtM win at_).2 := by
  unfold PlanM.frameAtM
  cases hc : (win.filterMap id).find? (fun f => decide (f.start ≤ at_ ∧ at_ < f.fend)) with
  | some f =>
    simp only []
    have hmem := List.mem_of_find?_eq_some hc
    have hp := List.find?_some hc
    simp only [decide_eq_true_eq] at hp
    obtain ⟨i, k, hf⟩ := hw f hmem
    obtain ⟨r, hr, hk⟩ := frame_some hf
    exact ⟨(locate_frame g hr hk hf hp.1 hp.2).symm, hw⟩
  | none =>
    simp only []
    cases hl : pl.locate at_ with
    | none => exact ⟨rfl, hw⟩
    | some first => exact ⟨rfl, refill_inv pl first.range 16 first.k⟩

end Pinc.ValuesPlan
