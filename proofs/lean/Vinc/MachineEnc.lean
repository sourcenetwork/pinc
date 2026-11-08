import Vinc.Machine

/-!
# Machine integers in the range encoder

`RangeEncoder::step` and `encode_range` of `vinc-dag/src/tree/encode.rs` as the code writes them, on `u64`
and on `usize` of 32 or 64 bits (`Machine`).

* `encStepM_eq`, `encRunM_eq`: the iterator does no overflowing or underflowing operation on any node it
  visits, for every value of at most `u64::MAX` bytes, and takes the steps of the model `Encode.encRun`.
* `encodeRange_exact`: `encode_range` returns `OutputTooSmall` exactly when the output buffer is smaller than
  the stream (the sum of the sizes of the steps), and the stream's size in bytes otherwise; every `u64` to
  `usize` conversion of an offset or length succeeds on both widths (so none truncates), and the reads stay
  inside the value and the outboard, so `RangeOutOfBounds` is not raised.
* `encodedLen_exact`: `encoded_len` adds the step sizes in `u64` without a check; it overflows exactly when the
  stream is longer than `u64::MAX` bytes, which a layout of a value close to `u64::MAX` bytes over its whole
  range produces. See `Vinc.Machine.encodedLen_overflows_iff`.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Vinc.Machine
open Vinc.Layout Vinc.Tree Vinc.Encode

theorem NodeInv.idx_lt {n first last : Nat} {e : ENode} (h : NodeInv n first last e) (h2 : e.hi - e.lo ≥ 2) :
    e.idx < n - 1 := by
  obtain ⟨_, _, _, _, t, ht⟩ := h
  have hs := slice_head n e.idx e.lo e.hi t h2 ht
  have := (List.getElem?_eq_some_iff.1 hs).1
  rw [pre_length] at this
  simpa using this

/-- The nodes the encoder pushes keep the invariant. -/
theorem encStep_nodeInv (len log first last n : Nat) (e : ENode) (h : NodeInv n first last e) :
    ∀ x ∈ (encStep len log first last e).2, NodeInv n first last x := by
  obtain ⟨a1, a2, a3, a4, t, ht⟩ := h
  by_cases hleaf : e.hi - e.lo = 1
  · simp [encStep, hleaf]
  · have h2 : e.hi - e.lo ≥ 2 := by omega
    have h1 := leftGroups_pos _ h2
    have h3 := leftGroups_lt _ h2
    intro x hx
    simp only [encStep, hleaf, ite_false, List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hx
    rcases hx with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
    · have sl := slice_left n e.idx e.lo e.hi t h2 ht
      exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, hc, _, sl⟩
    · have sl := slice_right n e.idx e.lo e.hi t h2 ht
      exact ⟨by dsimp only; omega, by dsimp only; omega, hc, by dsimp only; omega, _, sl⟩

/-- `RangeEncoder::step`, evaluated as the code does. -/
def encStepM (il : Nat → Nat) (len log first last : Nat) (nd : ENode) : Option (Step × List ENode) := do
  let count ← sub 64 nd.hi nd.lo
  if count = 1 then do
    let g ← groupLenM log
    let off ← mul 64 nd.lo g
    let sz ← groupSizeM len log nd.lo
    some (Step.group off sz, [])
  else do
    let left ← leftGroupsM il count
    let mid ← add 64 nd.lo left
    let r ← if mid < last then do
        let i ← add 64 nd.idx left
        some [ENode.mk mid nd.hi i]
      else some []
    let l ← if first < mid then do
        let i ← add 64 nd.idx 1
        some [ENode.mk nd.lo mid i]
      else some []
    let off ← mul 64 nd.idx 64
    some (Step.parent off, l ++ r)

theorem encStepM_eq (il : Nat → Nat) (hil : ∀ x, 0 < x → x < 2 ^ 64 → IsIlog2 x (il x))
    (len log first last n : Nat) (hn : groups len log = n) (hlen : len < 2 ^ 64) (hlog : log ≤ 20)
    (nd : ENode) (h : NodeInv n first last nd) :
    encStepM il len log first last nd = some (encStep len log first last nd) := by
  have hb : n ≤ 2 ^ 54 := hn ▸ groups_le len log (by unfold u64Max; omega)
  obtain ⟨a1, a2, a3, a4, _⟩ := h
  have hsub : nd.lo ≤ nd.hi := by omega
  by_cases hleaf : nd.hi - nd.lo = 1
  · have hlt : nd.lo < groups len log := by omega
    have hm := (lt_groups_iff len log nd.lo).1 hlt
    have hmul : nd.lo * groupLen log < 2 ^ 64 := by omega
    simp [encStepM, encStep, sub, hsub, hleaf, groupLenM_eq log hlog, mul, hmul, groupSizeM_eq len log _ hlog]
  · have h2 : nd.hi - nd.lo ≥ 2 := by omega
    have h1 := leftGroups_pos _ h2
    have h3 := leftGroups_lt _ h2
    have hidx := NodeInv.idx_lt ⟨a1, a2, a3, a4, by assumption⟩ h2
    have hc : nd.hi - nd.lo < 2 ^ 64 := Nat.lt_of_le_of_lt (by omega) (Nat.lt_of_le_of_lt hb (by decide))
    have hl := leftGroupsM_eq il hil _ hc
    have e54 : (2 : Nat) ^ 54 < 2 ^ 63 := by decide
    have e64 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
    have hmid : nd.lo + leftGroups (nd.hi - nd.lo) < 2 ^ 64 := by omega
    have hi1 : nd.idx + leftGroups (nd.hi - nd.lo) < 2 ^ 64 := by omega
    have hi2 : nd.idx + 1 < 2 ^ 64 := by omega
    have hm64 : nd.idx * 64 < 2 ^ 64 := by
      have : (2 : Nat) ^ 54 * 64 < 2 ^ 64 := by decide
      omega
    simp [encStepM, encStep, sub, hsub, hleaf, hl, add, mul, hmid, hi1, hi2, hm64]
    split <;> split <;> simp

/-- The iterator, evaluated as the code does. -/
def encRunM (il : Nat → Nat) (len log first last : Nat) : Nat → List ENode → Option (List Step × List ENode)
  | 0, st => some ([], st)
  | _ + 1, [] => some ([], [])
  | f + 1, nd :: rest => do
    let r1 ← encStepM il len log first last nd
    let r ← encRunM il len log first last f (r1.2 ++ rest)
    some (r1.1 :: r.1, r.2)

theorem encRunM_eq (il : Nat → Nat) (hil : ∀ x, 0 < x → x < 2 ^ 64 → IsIlog2 x (il x))
    (len log first last n : Nat) (hn : groups len log = n) (hlen : len < 2 ^ 64) (hlog : log ≤ 20) :
    ∀ (f : Nat) (E : List ENode), (∀ x ∈ E, NodeInv n first last x) →
      encRunM il len log first last f E = some (encRun len log first last f E) := by
  intro f
  induction f with
  | zero => intro E _; simp [encRunM, encRun]
  | succ f ih =>
    intro E hE
    cases E with
    | nil => simp [encRunM, encRun]
    | cons nd rest =>
      have hnd := hE nd (List.mem_cons_self ..)
      have hs := encStepM_eq il hil len log first last n hn hlen hlog nd hnd
      have hE' : ∀ x ∈ (encStep len log first last nd).2 ++ rest, NodeInv n first last x := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact encStep_nodeInv len log first last n nd hnd x hx
        · exact hE x (List.mem_cons_of_mem _ hx)
      simp [encRunM, encRun, hs, ih _ hE']

/-! ## `encode_range` -/

/-- `slice_at(data, offset, len)` on a `w`-bit `usize`: the length of the slice, `none` when a conversion or
the addition fails or the slice is out of bounds (`RangeOutOfBounds`). -/
def sliceAt (w dlen offset l : Nat) : Option Nat := do
  let s ← tryFrom w offset
  let n ← tryFrom w l
  let e ← add w s n
  if e ≤ dlen then some n else none

/-- The errors of the copy loop of `encode_range`. -/
inductive EncErr where
  | outputTooSmall
  | rangeOutOfBounds
  deriving DecidableEq

/-- The source slice of a step: a parent pair from the outboard, a group from the value. -/
def srcLen (w vlen oblen : Nat) : Step → Option Nat
  | .parent o => sliceAt w oblen o 64
  | .group o l => sliceAt w vlen o l

/-- The loop of `encode_range`: for each step slice its source, then `at.checked_add(src.len())` and the
bounds check of `out.get_mut(at..end)`; returns the bytes written. -/
def copyLoop (w vlen oblen outLen : Nat) : Nat → List Step → Except EncErr Nat
  | pos, [] => .ok pos
  | pos, stp :: rest =>
    match srcLen w vlen oblen stp with
    | none => .error .rangeOutOfBounds
    | some n =>
      match add w pos n with
      | none => .error .outputTooSmall
      | some e => if e ≤ outLen then copyLoop w vlen oblen outLen e rest else .error .outputTooSmall

theorem srcLen_eq (w vlen oblen len log : Nat) (hv : vlen < 2 ^ w) (ho : oblen < 2 ^ w) (hvl : vlen = len)
    (hol : oblen = outboardSize len log) (stp : Step) (h : InBounds len log stp) :
    srcLen w vlen oblen stp = some stp.size := by
  cases stp with
  | parent o =>
    obtain ⟨_, h2⟩ := h
    simp only [srcLen, Step.size, sliceAt, tryFrom, add]
    have a1 : o < 2 ^ w := by omega
    have a2 : (64 : Nat) < 2 ^ w := by omega
    have a3 : o + 64 < 2 ^ w := by omega
    simp [a1, a2, a3, show o + 64 ≤ oblen by omega]
  | group o l =>
    obtain ⟨h1, _, _⟩ := h
    simp only [srcLen, Step.size, sliceAt, tryFrom, add]
    have a1 : o < 2 ^ w := by omega
    have a2 : l < 2 ^ w := by omega
    have a3 : o + l < 2 ^ w := by omega
    simp [a1, a2, a3, show o + l ≤ vlen by omega]

/-- With every read in bounds and fitting the integer width, the copy loop succeeds with the total size
exactly when the buffer holds it, and fails with `OutputTooSmall` otherwise. -/
theorem copyLoop_eq (w vlen oblen outLen : Nat) (hv : vlen < 2 ^ w) (ho : oblen < 2 ^ w) (hout : outLen < 2 ^ w)
    (len log : Nat) (hvl : vlen = len) (hol : oblen = outboardSize len log) :
    ∀ (steps : List Step) (pos : Nat), (∀ stp ∈ steps, InBounds len log stp) → pos ≤ outLen →
      copyLoop w vlen oblen outLen pos steps =
        if pos + (steps.map Step.size).sum ≤ outLen then .ok (pos + (steps.map Step.size).sum)
        else .error .outputTooSmall := by
  intro steps
  induction steps with
  | nil => intro pos _ hpos; simp [copyLoop, hpos]
  | cons stp rest ih =>
    intro pos hb hpos
    have hstp := hb stp (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, InBounds len log x := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hk := srcLen_eq w vlen oblen len log hv ho hvl hol stp hstp
    simp only [copyLoop, hk, List.map_cons, List.sum_cons]
    by_cases hov : pos + stp.size < 2 ^ w
    · by_cases hle : pos + stp.size ≤ outLen
      · simp only [add, hov, ite_true, hle]
        rw [ih _ hrest hle]
        simp only [Nat.add_assoc]
      · have h2 : ¬ pos + (stp.size + (rest.map Step.size).sum) ≤ outLen := by omega
        simp only [add, hov, ite_true, hle, ite_false]
        rw [if_neg h2]
    · have h2 : ¬ pos + (stp.size + (rest.map Step.size).sum) ≤ outLen := by omega
      simp only [add, hov, ite_false]
      rw [if_neg h2]

/-- `encode_range` on a `w`-bit `usize`: the iterator and then the copy loop. -/
def encodeRangeM (il : Nat → Nat) (w vlen oblen len log first last outLen : Nat) : Option (Except EncErr Nat) := do
  let n ← groupsM len log
  let r ← encRunM il len log first last (2 * n) (encInit len log first last)
  some (copyLoop w vlen oblen outLen 0 r.1)

/-- (`encode_range`.) For a value of `len < 2^w` bytes and its outboard, on a `w`-bit `usize` (32 or 64), the
function returns `OutputTooSmall` exactly when the output buffer is smaller than the stream, and the stream's
size in bytes (the sum of the step sizes, which is `encoded_len`) otherwise. No conversion truncates and no
read leaves the value or the outboard: the other error, `RangeOutOfBounds`, does not occur. -/
theorem encodeRange_exact (il : Nat → Nat) (hil : ∀ x, 0 < x → x < 2 ^ 64 → IsIlog2 x (il x)) (w : Nat)
    (hw : w = 32 ∨ w = 64) (len log s e first last outLen : Nat) (hlen : len < 2 ^ w)
    (hob : outboardSize len log < 2 ^ w) (hout : outLen < 2 ^ w) (hlog : log ≤ 20) (hse : s ≤ e) (hel : e ≤ len)
    (hr : groupRange len log s e = some (first, last)) :
    let steps := (encRun len log first last (2 * groups len log) (encInit len log first last)).1
    encodeRangeM il w len (outboardSize len log) len log first last outLen =
      some (if (steps.map Step.size).sum ≤ outLen then .ok (steps.map Step.size).sum else .error .outputTooSmall) := by
  intro steps
  have hw64 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  have hlen64 : len < 2 ^ 64 := by omega
  -- the groups range and the encoder's initial node
  obtain ⟨hlast, hinit⟩ : last ≤ groups len log ∧ ∀ x ∈ encInit len log first last, NodeInv (groups len log) first last x := by
    by_cases hlt : s < e
    · obtain ⟨a, b, hab, hab2, hbn, _⟩ := groupRange_spec len log s e hlt hel
      rw [hr] at hab
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hab)
      refine ⟨hbn, ?_⟩
      intro x hx
      unfold encInit at hx
      simp only [hab2, ite_true, List.mem_singleton] at hx
      subst hx
      exact ⟨by dsimp only; omega, Nat.le_refl _, by dsimp only; omega, by dsimp only; omega, [], by simp⟩
    · have hs : s = e := by omega
      subst hs
      rw [groupRange_empty len log s hel] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
      exact ⟨Nat.zero_le _, by simp [encInit]⟩
  -- every step of the genuine run is in bounds: the completeness theorem, for the trivial hash
  let H : Hash Unit Unit := ⟨fun _ _ _ => (), fun _ _ _ => ()⟩
  have hc := complete_accepts H (fun _ => ()) (fun _ => ((), ())) () () len log s e first last (groups len log) rfl
    (by unfold u64Max; omega) hse hel hr (fun _ _ _ _ => rfl)
  obtain ⟨_, _, _, _, _, hbounds⟩ := hc
  have hmach := encRunM_eq il hil len log first last (groups len log) rfl hlen64 hlog (2 * groups len log) _ hinit
  simp only [encodeRangeM, groupsM_eq len log hlen64 hlog, Option.bind_some, Option.bind_eq_bind, hmach]
  rw [copyLoop_eq w len (outboardSize len log) outLen hlen hob hout len log rfl rfl _ 0 hbounds (Nat.zero_le _)]
  simp only [Nat.zero_add]
  rfl

/-- `encoded_len`: the checked sum of the step sizes in `u64`, where the code adds without a check. -/
def foldAdd : Nat → List Nat → Option Nat
  | acc, [] => some acc
  | acc, x :: xs => do
    let a ← add 64 acc x
    foldAdd a xs

theorem foldAdd_eq (xs : List Nat) :
    ∀ acc, acc < 2 ^ 64 → foldAdd acc xs = if acc + xs.sum < 2 ^ 64 then some (acc + xs.sum) else none := by
  induction xs with
  | nil => intro acc h; simp [foldAdd, h]
  | cons x xs ih =>
    intro acc hacc
    by_cases h : acc + x < 2 ^ 64
    · simp only [foldAdd, add, h, ite_true, Option.bind_some, Option.bind_eq_bind, ih _ h]
      simp only [List.sum_cons, Nat.add_assoc]
      rfl
    · have h2 : ¬ acc + (x :: xs).sum < 2 ^ 64 := by simp only [List.sum_cons]; omega
      simp only [foldAdd, add, h, ite_false, h2]
      rfl

/-- `encoded_len` overflows `u64` exactly when the stream is longer than `u64::MAX` bytes; it then panics in a
debug build and wraps in a release build, because the sum is not checked. -/
theorem encodedLen_overflows_iff (steps : List Step) :
    foldAdd 0 (steps.map Step.size) = none ↔ 2 ^ 64 ≤ (steps.map Step.size).sum := by
  rw [foldAdd_eq _ 0 (by decide)]
  by_cases h : 0 + (steps.map Step.size).sum < 2 ^ 64 <;> simp [h] <;> omega

end Vinc.Machine

#audit_axioms Vinc.Machine.encRunM_eq
#audit_axioms Vinc.Machine.encodeRange_exact
#audit_axioms Vinc.Machine.encodedLen_overflows_iff
#audit_axioms Vinc.Machine.encStepM_eq
#audit_axioms Vinc.Machine.copyLoop_eq
#audit_axioms Vinc.Machine.foldAdd_eq
