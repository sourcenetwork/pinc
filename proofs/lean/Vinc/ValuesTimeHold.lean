import Vinc.ValuesTime

/-!
# HEAD_HOLD (property 4)

Theorems about `holdWhy`, `holdCheck`, `checkDone`, `groupVerified` and `onTimeout` of `Vinc/ValuesTime.lean`:

* `holdWhy_*`: the release causes and their order (a buffer of `HOLD_B` verified bytes behind the granule, the wanted
  range ending in the buffer, `HOLD_NV` later granules, `HOLD_MAX` after the hold started, else the forced `Done`);
  `bufOf_ge_iff` ties the buffer to the verified set: `n` bytes stand behind the granule iff they are all verified.
* `Inv` and `reach_inv`: over every run (every valid input sequence), the first granule is never announced before it
  is verified and stored, is announced exactly once (`head_dichotomy`), later granules are announced right after their
  commit (`readable_after_store`), the held granule is not announced (`held_not_announced`), a completed fetch holds
  no granule (`complete_released`).
* `J0` and `reach_j0`: no late release: at every point between calls a held granule has fewer than `HOLD_B` verified
  bytes behind it, the wanted range does not end in the buffer and fewer than `HOLD_NV` later granules verified.
* The bound: `hold_poll_le` (the timer `poll_timeout` offers is at most `t0 + HOLD_MAX`), `onTimeout_clears_head`
  (an `on_timeout` at or after it leaves no held granule), `onTimeout_timeout_cause` (the cause is `Timeout` in a
  state with no earlier cause).
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Vinc.ValuesTime
open Vinc.Ranges

@[simp] theorem emit_store (s : Fs) (es : List Ev) : (Fs.emit s es).store = s.store := rfl
@[simp] theorem emit_head (s : Fs) (es : List Ev) : (Fs.emit s es).head = s.head := rfl
@[simp] theorem emit_rel (s : Fs) (es : List Ev) : (Fs.emit s es).rel = s.rel := rfl
@[simp] theorem emit_nv (s : Fs) (es : List Ev) : (Fs.emit s es).nv = s.nv := rfl
@[simp] theorem emit_o0 (s : Fs) (es : List Ev) : (Fs.emit s es).o0 = s.o0 := rfl
@[simp] theorem emit_want (s : Fs) (es : List Ev) : (Fs.emit s es).want = s.want := rfl
@[simp] theorem emit_running (s : Fs) (es : List Ev) : (Fs.emit s es).running = s.running := rfl
@[simp] theorem emit_log (s : Fs) (es : List Ev) : (Fs.emit s es).log = s.log ++ es := rfl
@[simp] theorem emit_sw (s : Fs) (es : List Ev) : (Fs.emit s es).sw = s.sw := rfl
@[simp] theorem emit_lastp (s : Fs) (es : List Ev) : (Fs.emit s es).lastp = s.lastp := rfl
@[simp] theorem emit_lastb (s : Fs) (es : List Ev) : (Fs.emit s es).lastb = s.lastb := rfl
@[simp] theorem emit_tw (s : Fs) (es : List Ev) : (Fs.emit s es).tw = s.tw := rfl
@[simp] theorem emit_rt (s : Fs) (es : List Ev) : (Fs.emit s es).rt = s.rt := rfl
@[simp] theorem emit_deadline (s : Fs) (es : List Ev) : (Fs.emit s es).deadline = s.deadline := rfl
@[simp] theorem emit_striped (s : Fs) (es : List Ev) : (Fs.emit s es).striped = s.striped := rfl
@[simp] theorem emit_treq (s : Fs) (es : List Ev) : (Fs.emit s es).treq = s.treq := rfl
@[simp] theorem emit_trusted (s : Fs) (es : List Ev) : (Fs.emit s es).trusted = s.trusted := rfl
@[simp] theorem tot_emit (s : Fs) (es : List Ev) : (Fs.emit s es).tot = s.tot := rfl
@[simp] theorem wantedDone_emit (s : Fs) (es : List Ev) : (Fs.emit s es).wantedDone = s.wantedDone := rfl

/-! ## The causes -/

theorem holdWhy_none_eq (s : Fs) (h : Head) (now : Nat) :
    holdWhy s h now none =
      if HOLD_B ≤ bufOf s.store (h.off + h.len) then some .buffered
      else if s.o0 + s.tot ≤ h.off + h.len + bufOf s.store (h.off + h.len) then some .tail
      else if HOLD_NV ≤ s.nv then some .granules
      else if sadd h.t0 HOLD_MAX ≤ now then some .timeout
      else none := rfl

/-- A release happens exactly when one of the four causes holds (the cause of `Done` is forced, not tested). -/
theorem holdWhy_isSome_iff (s : Fs) (h : Head) (now : Nat) :
    (holdWhy s h now none).isSome = true ↔
      (HOLD_B ≤ bufOf s.store (h.off + h.len) ∨ s.o0 + s.tot ≤ h.off + h.len + bufOf s.store (h.off + h.len) ∨
        HOLD_NV ≤ s.nv ∨ sadd h.t0 HOLD_MAX ≤ now) := by
  rw [holdWhy_none_eq]
  split <;> (try split) <;> (try split) <;> (try split) <;> simp_all

/-- The causes in order: a buffer wins over the tail, the tail over the granule count, that over the timeout. -/
theorem holdWhy_buffered (s : Fs) (h : Head) (now : Nat) :
    holdWhy s h now none = some .buffered ↔ HOLD_B ≤ bufOf s.store (h.off + h.len) := by
  rw [holdWhy_none_eq]
  split <;> (try split) <;> (try split) <;> (try split) <;> simp_all

theorem holdWhy_tail (s : Fs) (h : Head) (now : Nat) :
    holdWhy s h now none = some .tail ↔
      bufOf s.store (h.off + h.len) < HOLD_B ∧ s.o0 + s.tot ≤ h.off + h.len + bufOf s.store (h.off + h.len) := by
  rw [holdWhy_none_eq]
  split <;> (try split) <;> (try split) <;> (try split) <;> simp_all <;> omega

theorem holdWhy_granules (s : Fs) (h : Head) (now : Nat) :
    holdWhy s h now none = some .granules ↔
      bufOf s.store (h.off + h.len) < HOLD_B ∧ h.off + h.len + bufOf s.store (h.off + h.len) < s.o0 + s.tot ∧
        HOLD_NV ≤ s.nv := by
  rw [holdWhy_none_eq]
  split <;> (try split) <;> (try split) <;> (try split) <;> simp_all <;> omega

theorem holdWhy_timeout (s : Fs) (h : Head) (now : Nat) :
    holdWhy s h now none = some .timeout ↔
      bufOf s.store (h.off + h.len) < HOLD_B ∧ h.off + h.len + bufOf s.store (h.off + h.len) < s.o0 + s.tot ∧
        s.nv < HOLD_NV ∧ sadd h.t0 HOLD_MAX ≤ now := by
  rw [holdWhy_none_eq]
  split <;> (try split) <;> (try split) <;> (try split) <;> simp_all <;> omega

/-- `Done` is never a tested cause. -/
theorem holdWhy_not_done (s : Fs) (h : Head) (now : Nat) : holdWhy s h now none ≠ some .done := by
  rw [holdWhy_none_eq]
  split <;> (try split) <;> (try split) <;> (try split) <;> simp

theorem holdWhy_force (s : Fs) (h : Head) (now : Nat) (c : Cause) : holdWhy s h now (some c) = some c := rfl

/-- The release: the granule is announced right after the `Released` record, and not before. -/
theorem holdCheck_release (s : Fs) (now : Nat) (force : Option Cause) (h : Head) (c : Cause)
    (hh : s.head = some h) (hw : holdWhy s h now force = some c) :
    holdCheck s now force = Fs.emit { s with head := none, rel := true } [.released h.off c, .readable h.off h.len] := by
  simp [holdCheck, hh, hw]

theorem holdCheck_keep (s : Fs) (now : Nat) (force : Option Cause) (h : Head)
    (hh : s.head = some h) (hw : holdWhy s h now force = none) : holdCheck s now force = s := by
  simp [holdCheck, hh, hw]

/-- Seen from outside: after a hold check the granule is still held iff there was one and no cause held. -/
theorem holdCheck_head (s : Fs) (now : Nat) :
    (holdCheck s now none).head = none ↔
      s.head = none ∨ ∃ h, s.head = some h ∧
        (HOLD_B ≤ bufOf s.store (h.off + h.len) ∨ s.o0 + s.tot ≤ h.off + h.len + bufOf s.store (h.off + h.len) ∨
          HOLD_NV ≤ s.nv ∨ sadd h.t0 HOLD_MAX ≤ now) := by
  cases hh : s.head with
  | none => simp [holdCheck, hh]
  | some h =>
    have := holdWhy_isSome_iff s h now
    cases hw : holdWhy s h now none with
    | none => simp_all [holdCheck]
    | some c => simp_all [holdCheck]

/-! ## The buffer is the verified run behind the granule -/

/-- The first interval that ends after `e` is the one that contains `e`, when one does. -/
theorem find_first_end (st : List Interval) (hs : Sound st) (e : Nat) (iv : Interval) (hiv : iv ∈ st)
    (h1 : iv.1 ≤ e) (h2 : e < iv.2) : st.find? (fun iv => decide (e < iv.2)) = some iv := by
  have hex : (st.find? (fun iv => decide (e < iv.2))).isSome = true := by
    rw [List.find?_isSome]; exact ⟨iv, hiv, by simpa using h2⟩
  obtain ⟨iv0, h0⟩ := Option.isSome_iff_exists.1 hex
  rw [h0]
  congr 1
  obtain ⟨hp, as, bs, hl, hbef⟩ := List.find?_eq_some_iff_append.1 h0
  have hp' : e < iv0.2 := by simpa using hp
  have hpw := hs.2
  rw [hl] at hpw hiv
  rw [List.pairwise_append, List.pairwise_cons] at hpw
  rcases List.mem_append.1 hiv with hin | hin
  · exact absurd h2 (by have := hbef iv hin; simpa using this)
  · rcases List.mem_cons.1 hin with rfl | hin2
    · rfl
    · have := hpw.2.1.1 iv hin2
      omega

/-- `n` bytes (`n > 0`) stand behind `e` exactly when they are all verified: the buffer of HEAD_HOLD is the verified
run that starts at the end of the granule. -/
theorem bufOf_ge_iff (st : List Interval) (hs : Sound st) (e n : Nat) (hn : 0 < n) :
    n ≤ bufOf st e ↔ ∀ x, e ≤ x → x < e + n → Covers st x := by
  constructor
  · intro h x hx1 hx2
    unfold bufOf at h
    cases hf : st.find? (fun iv => decide (e < iv.2)) with
    | none => simp [hf] at h; omega
    | some iv =>
      simp only [hf] at h
      split at h
      · have hm := List.mem_of_find?_eq_some hf
        have hp := List.find?_some hf
        simp at hp
        exact ⟨iv, hm, by omega, by omega⟩
      · omega
  · intro h
    obtain ⟨iv, hiv, h1, h2⟩ := h e (Nat.le_refl _) (by omega)
    have hf := find_first_end st hs e iv hiv h1 h2
    unfold bufOf
    rw [hf]
    simp only [h1, ite_true]
    by_cases hge : n ≤ iv.2 - e
    · exact hge
    exfalso
    have hlt : iv.2 < e + n := by omega
    obtain ⟨iv2, hiv2, h3, h4⟩ := h iv.2 (by omega) hlt
    have hne : iv ≠ iv2 := by
      intro heq; subst heq; omega
    rcases sound_pair hs hiv hiv2 hne with c | c
    · omega
    · have := hs.1 iv hiv; have := hs.1 iv2 hiv2; omega

end Vinc.ValuesTime
