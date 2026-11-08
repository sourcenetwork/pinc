import Vinc.Axioms

/-!
# The anti-replay window

A step-for-step model of `vinc-security/src/replay.rs` for a window of `B` packet numbers (`1 <= B <= 1024`).

The code keeps a ring of `B` bits in sixteen 64-bit words, indexed by `pn % B`. Here the ring is a function
`Nat -> Bool` over the same positions; the packing of those positions into words (`pos / 64`, `1 << (pos % 64)`) is
not modelled and is checked by the recorded traces of the real window. Packet numbers are `Nat`s: the code's
arithmetic is `u64` with `highest - pn` guarded by `pn <= highest`, `pn.saturating_sub(highest)` (the truncated
subtraction of `Nat`) and `highest + 1 ..= pn` inside `pn > highest`, so the `Nat` model and the `u64` code agree.

A ghost set `acc` records the numbers whose `insert` succeeded. `Inv` says the ring is faithful to `acc` for every
number in the window, and `Reach` is the set of states a sequence of `insert`s produces from `new`.
-/

namespace Vinc.ReplayWindow

/-- `ReplayError`. -/
inductive Err where
  | dup
  | tooOld
  deriving DecidableEq, Repr

/-- `ReplayWindow<B>`: the ring, the highest number and whether any number was accepted. -/
structure State where
  ring : Nat → Bool
  highest : Nat
  started : Bool

/-- `ReplayWindow::new`. -/
def State.new : State := ⟨fun _ => false, 0, false⟩

/-- `assign`: set or clear the ring position of `pn`. -/
def assign (B : Nat) (ring : Nat → Bool) (pn : Nat) (on : Bool) : Nat → Bool :=
  fun p => if p = pn % B then on else ring p

/-- `check`. -/
def check (B : Nat) (s : State) (pn : Nat) : Except Err Unit :=
  if !s.started || pn > s.highest then .ok ()
  else if s.highest - pn ≥ B then .error .tooOld
  else if s.ring (pn % B) then .error .dup else .ok ()

/-- The loop `for gone in highest + 1 ..= pn { assign(gone, false) }`, over the numbers in `l`. -/
def clearL (B : Nat) (ring : Nat → Bool) (l : List Nat) : Nat → Bool :=
  l.foldl (fun r g => assign B r g false) ring

/-- The ring after the first part of `insert`: cleared, slid or untouched. -/
def slide (B : Nat) (s : State) (pn : Nat) : Nat → Bool :=
  if !s.started || pn - s.highest ≥ B then fun _ => false
  else if pn > s.highest then clearL B s.ring (List.range' (s.highest + 1) (pn - s.highest))
  else s.ring

/-- `insert`: the new state, or the error with nothing recorded. -/
def insert (B : Nat) (s : State) (pn : Nat) : Except Err State :=
  match check B s pn with
  | .error e => .error e
  | .ok () =>
    let ring := slide B s pn
    if !s.started || pn > s.highest then
      .ok ⟨assign B ring pn true, pn, true⟩
    else .ok ⟨assign B ring pn true, s.highest, s.started⟩

/-! ## The loop that clears the ring -/

theorem clearL_hit (B : Nat) (l : List Nat) : ∀ (ring : Nat → Bool) (p : Nat),
    (∃ g ∈ l, g % B = p) → clearL B ring l p = false := by
  induction l with
  | nil => intro _ _ ⟨g, hg, _⟩; simp at hg
  | cons a l ih =>
    intro ring p ⟨g, hg, hp⟩
    simp only [clearL, List.foldl_cons]
    by_cases h : ∃ g' ∈ l, g' % B = p
    · exact ih _ _ h
    · have hga : g = a := by
        rcases List.mem_cons.1 hg with h1 | h1
        · exact h1
        · exact absurd ⟨g, h1, hp⟩ h
      subst hga
      have key : ∀ (l : List Nat) (r : Nat → Bool), (¬ ∃ g' ∈ l, g' % B = p) → clearL B r l p = r p := by
        intro l; induction l with
        | nil => intro r _; rfl
        | cons b l ih2 =>
          intro r hn
          simp only [clearL, List.foldl_cons]
          have h1 : ¬ ∃ g' ∈ l, g' % B = p := fun ⟨x, hx, hxp⟩ => hn ⟨x, List.mem_cons_of_mem _ hx, hxp⟩
          have h2 : b % B ≠ p := fun e => hn ⟨b, List.mem_cons_self .., e⟩
          have := ih2 (assign B r b false) h1
          simp only [clearL] at this
          rw [this]; simp [assign, Ne.symm h2]
      have := key l (assign B ring g false) h
      simp only [clearL] at this
      rw [this]; simp [assign, hp]

theorem clearL_miss (B : Nat) (l : List Nat) : ∀ (ring : Nat → Bool) (p : Nat),
    (¬ ∃ g ∈ l, g % B = p) → clearL B ring l p = ring p := by
  induction l with
  | nil => intro r _ _; rfl
  | cons b l ih2 =>
    intro r p hn
    simp only [clearL, List.foldl_cons]
    have h1 : ¬ ∃ g' ∈ l, g' % B = p := fun ⟨x, hx, hxp⟩ => hn ⟨x, List.mem_cons_of_mem _ hx, hxp⟩
    have h2 : b % B ≠ p := fun e => hn ⟨b, List.mem_cons_self .., e⟩
    have := ih2 (assign B r b false) p h1
    simp only [clearL] at this
    rw [this]; simp [assign, Ne.symm h2]

/-- Two numbers closer than `B` have different ring positions. -/
theorem mod_ne {a b B : Nat} (hab : a < b) (hbB : b < a + B) : a % B ≠ b % B := by
  intro h
  have h0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  have : b - a < B := by omega
  rw [Nat.mod_eq_of_lt this] at h0
  omega

/-! ## The invariant -/

/-- The ring is faithful to the set `acc` of accepted numbers inside the window, and `acc` lies at or below the
highest number. -/
structure Inv (B : Nat) (s : State) (acc : Nat → Prop) : Prop where
  bound : ∀ n, acc n → s.started = true ∧ n ≤ s.highest
  ring : ∀ n, s.started = true → n ≤ s.highest → s.highest < n + B → (s.ring (n % B) = true ↔ acc n)

theorem inv_new (B : Nat) : Inv B State.new (fun _ => False) :=
  ⟨fun _ h => h.elim, fun _ h => by simp [State.new] at h⟩

/-- The states reachable by `insert`s from `new`, with the ghost set of accepted numbers. -/
inductive Reach (B : Nat) : State → (Nat → Prop) → Prop where
  | init : Reach B State.new (fun _ => False)
  | step {s acc s'} (pn : Nat) : Reach B s acc → insert B s pn = .ok s' → Reach B s' (fun n => acc n ∨ n = pn)

/-! ## The check -/

/-- `check` accepts exactly the numbers that are above the highest, or inside the window and not accepted
before. -/
theorem check_ok_iff {B : Nat} {s : State} {acc : Nat → Prop} (hI : Inv B s acc) (pn : Nat) :
    check B s pn = .ok () ↔ (s.started = false ∨ s.highest < pn ∨ (s.highest < pn + B ∧ ¬ acc pn)) := by
  unfold check
  by_cases h1 : s.started = false
  · simp [h1]
  · have h1' : s.started = true := by simpa using h1
    by_cases h2 : s.highest < pn
    · simp [h1', h2]
    · have h2' : pn ≤ s.highest := by omega
      by_cases h3 : s.highest - pn ≥ B
      · have : ¬ s.highest < pn + B := by omega
        simp [h1', h2, h3, this]
      · have h3' : s.highest < pn + B := by omega
        have hr := hI.ring pn h1' h2' h3'
        by_cases h4 : s.ring (pn % B) = true
        · have : acc pn := hr.1 h4
          simp [h1', h2, h3, h4, h3', this]
        · have : ¬ acc pn := fun a => h4 (hr.2 a)
          simp [h1', h2, h3, h4, h3', this]

/-- A number accepted before is never accepted again: `check` succeeds only for a number not in `acc`. -/
theorem accepted_once {B : Nat} {s : State} {acc : Nat → Prop} (hI : Inv B s acc) {pn : Nat}
    (h : check B s pn = .ok ()) : ¬ acc pn := by
  rcases (check_ok_iff hI pn).1 h with h1 | h1 | ⟨_, h1⟩
  · intro a; have := (hI.bound pn a).1; simp_all
  · intro a; have := (hI.bound pn a).2; omega
  · exact h1

/-- Anything below the window (`pn + B <= highest`) is refused as too old. -/
theorem too_old {B : Nat} {s : State} {pn : Nat} (hs : s.started = true) (h : pn + B ≤ s.highest) :
    check B s pn = .error .tooOld := by
  unfold check
  have h1 : ¬ s.highest < pn := by omega
  have h2 : s.highest - pn ≥ B := by omega
  simp [hs, h1, h2]

/-- Nothing in the window or above it that was not inserted is refused. -/
theorem fresh_accepted {B : Nat} {s : State} {acc : Nat → Prop} (hI : Inv B s acc) {pn : Nat}
    (hw : s.started = false ∨ s.highest < pn + B) (hn : ¬ acc pn) : check B s pn = .ok () := by
  rw [check_ok_iff hI]
  rcases hw with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨h, hn⟩)

/-- `Duplicate` only for a number that was accepted, inside the window. -/
theorem dup_only_accepted {B : Nat} {s : State} {acc : Nat → Prop} (hI : Inv B s acc) {pn : Nat}
    (h : check B s pn = .error .dup) : acc pn ∧ s.started = true ∧ pn ≤ s.highest ∧ s.highest < pn + B := by
  by_cases hok : check B s pn = .ok ()
  · rw [hok] at h; cases h
  unfold check at h
  by_cases h1 : (!s.started || pn > s.highest) = true
  · simp [h1] at h
  have h1' : s.started = true := by simp at h1; exact h1.1
  have h2 : pn ≤ s.highest := by simp at h1; omega
  by_cases h3 : s.highest - pn ≥ B
  · simp [h1, h3] at h
  have h3' : s.highest < pn + B := by omega
  by_cases h4 : s.ring (pn % B) = true
  · exact ⟨(hI.ring pn h1' h2 h3').1 h4, h1', h2, h3'⟩
  · simp [h1, h3, h4] at h

/-- `TooOld` only below the window. -/
theorem too_old_only_below {s : State} {B pn : Nat} (h : check B s pn = .error .tooOld) :
    s.started = true ∧ pn + B ≤ s.highest := by
  unfold check at h
  by_cases h1 : (!s.started || pn > s.highest) = true
  · simp [h1] at h
  have h1' : s.started = true := by simp at h1; exact h1.1
  have h2 : pn ≤ s.highest := by simp at h1; omega
  by_cases h3 : s.highest - pn ≥ B
  · exact ⟨h1', by omega⟩
  · by_cases h4 : s.ring (pn % B) = true <;> simp [h1, h3, h4] at h

/-! ## The insert -/

/-- `insert` fails exactly when `check` fails, with the same error, and records nothing then. -/
theorem insert_error {B : Nat} {s : State} {pn : Nat} {e : Err} :
    insert B s pn = .error e ↔ check B s pn = .error e := by
  unfold insert
  cases hc : check B s pn with
  | error e' => simp
  | ok u => cases u; simp only []; split <;> simp

theorem insert_ok_check {B : Nat} {s s' : State} {pn : Nat} (h : insert B s pn = .ok s') : check B s pn = .ok () := by
  unfold insert at h
  cases hc : check B s pn with
  | error e' => rw [hc] at h; cases h
  | ok u => cases u; rfl

/-- A successful `insert` keeps the invariant with `pn` added to the accepted set. -/
theorem inv_insert {B : Nat} (hB : 0 < B) {s s' : State} {acc : Nat → Prop} (hI : Inv B s acc) {pn : Nat}
    (h : insert B s pn = .ok s') : Inv B s' (fun n => acc n ∨ n = pn) := by
  have hc := insert_ok_check h
  have hnot := accepted_once hI hc
  have hcok := (check_ok_iff hI pn).1 hc
  unfold insert at h
  rw [hc] at h
  simp only at h
  -- the post-state in each branch
  by_cases hnew : (!s.started || pn > s.highest) = true
  · simp only [hnew, ite_true] at h
    cases h
    have hnew' : s.started = false ∨ s.highest < pn := by simpa using hnew
    refine ⟨?_, ?_⟩
    · intro n hn
      refine ⟨rfl, ?_⟩
      show n ≤ pn
      rcases hn with hn | hn
      · have := hI.bound n hn
        have := this.2
        rcases hnew' with h1 | h1
        · have := (hI.bound n hn).1; simp_all
        · omega
      · omega
    · intro n _ hle hlt
      dsimp only at hle hlt
      show (assign B (slide B s pn) pn true (n % B) = true) ↔ (acc n ∨ n = pn)
      unfold assign
      by_cases hn : n = pn
      · subst hn; simp
      · have hlt' : n < pn := by omega
        have hne : n % B ≠ pn % B := mod_ne hlt' (by omega)
        simp only [eq_false hne, ite_false, hn, or_false]
        by_cases hca : (!s.started || pn - s.highest ≥ B) = true
        · have hsl : slide B s pn = fun _ => false := by unfold slide; simp only [hca, ite_true]
          rw [hsl]
          simp only [Bool.false_eq_true, false_iff]
          intro ha
          have hb := hI.bound n ha
          have hs := hb.1
          have : pn - s.highest ≥ B := by simpa [hs] using hca
          omega
        · have hs : s.started = true := by simp at hca; exact hca.1
          have hgt : s.highest < pn := by simpa [hs] using hnew'
          have hsl : slide B s pn = clearL B s.ring (List.range' (s.highest + 1) (pn - s.highest)) := by
            unfold slide
            have : ¬ (pn - s.highest ≥ B) := by simp [hs] at hca; omega
            simp [hs, hgt, this]
          rw [hsl]
          have hsub : pn - s.highest < B := by simp [hs] at hca; omega
          by_cases hn2 : s.highest < n
          · have hhit : ∃ g ∈ List.range' (s.highest + 1) (pn - s.highest), g % B = n % B :=
              ⟨n, by rw [List.mem_range'_1]; omega, rfl⟩
            rw [clearL_hit B _ _ _ hhit]
            simp only [Bool.false_eq_true, false_iff]
            intro ha; have := (hI.bound n ha).2; omega
          · have hmiss : ¬ ∃ g ∈ List.range' (s.highest + 1) (pn - s.highest), g % B = n % B := by
              rintro ⟨g, hg, hgn⟩
              rw [List.mem_range'_1] at hg
              exact mod_ne (a := n) (b := g) (by omega) (by omega) hgn.symm
            rw [clearL_miss B _ _ _ hmiss]
            exact hI.ring n hs (by omega) (by omega)
  · simp only [hnew] at h
    cases h
    have hs : s.started = true := by simp at hnew; exact hnew.1
    have hle : pn ≤ s.highest := by simp at hnew; omega
    have hwin : s.highest < pn + B := by
      rcases hcok with h1 | h1 | h1
      · simp_all
      · omega
      · exact h1.1
    refine ⟨?_, ?_⟩
    · intro n hn
      refine ⟨hs, ?_⟩
      show n ≤ s.highest
      rcases hn with hn | hn
      · exact (hI.bound n hn).2
      · omega
    · intro n _ hle' hlt
      dsimp only at hle' hlt
      show (assign B (slide B s pn) pn true (n % B) = true) ↔ (acc n ∨ n = pn)
      unfold assign
      by_cases hn : n = pn
      · subst hn; simp
      · have hne : n % B ≠ pn % B := by
          rcases Nat.lt_or_gt_of_ne hn with h1 | h1
          · exact mod_ne h1 (by omega)
          · exact (mod_ne h1 (by omega)).symm
        simp only [eq_false hne, ite_false, hn, or_false]
        have : slide B s pn = s.ring := by
          unfold slide
          have : ¬ (!s.started || pn - s.highest ≥ B) = true := by
            simp [hs]; omega
          simp [this, show ¬ s.highest < pn by omega]
        rw [this]
        exact hI.ring n hs hle' hlt

/-- Every reachable state satisfies the invariant. -/
theorem reach_inv {B : Nat} (hB : 0 < B) {s : State} {acc : Nat → Prop} (h : Reach B s acc) : Inv B s acc := by
  induction h with
  | init => exact inv_new B
  | step pn _ hi ih => exact inv_insert hB ih hi

/-- A successful `insert` accepted a number that was not accepted before, and the accepted set grows by exactly
that number. -/
theorem insert_fresh {B : Nat} {s s' : State} {acc : Nat → Prop} (hI : Inv B s acc) {pn : Nat}
    (h : insert B s pn = .ok s') : ¬ acc pn :=
  accepted_once hI (insert_ok_check h)

/-- After a successful `insert` the highest number is the larger of the old one and `pn`. -/
theorem insert_highest {B : Nat} {s s' : State} {pn : Nat} (h : insert B s pn = .ok s') :
    s'.started = true ∧ (s.started = false ∨ s.highest < pn → s'.highest = pn) ∧
      (s.started = true → pn ≤ s.highest → s'.highest = s.highest) := by
  have hc := insert_ok_check h
  unfold insert at h
  rw [hc] at h
  simp only at h
  by_cases hnew : (!s.started || pn > s.highest) = true
  · simp only [hnew, ite_true] at h; cases h
    refine ⟨rfl, fun _ => rfl, ?_⟩
    intro hs hle; simp [hs] at hnew; omega
  · simp only [hnew] at h; cases h
    have hs : s.started = true := by simp at hnew; exact hnew.1
    refine ⟨hs, ?_, fun _ _ => rfl⟩
    intro h1; rcases h1 with h1 | h1
    · simp_all
    · simp at hnew; omega

end Vinc.ReplayWindow

#audit_axioms Vinc.ReplayWindow.reach_inv
#audit_axioms Vinc.ReplayWindow.check_ok_iff
#audit_axioms Vinc.ReplayWindow.accepted_once
#audit_axioms Vinc.ReplayWindow.too_old
#audit_axioms Vinc.ReplayWindow.fresh_accepted
#audit_axioms Vinc.ReplayWindow.dup_only_accepted
#audit_axioms Vinc.ReplayWindow.too_old_only_below
#audit_axioms Vinc.ReplayWindow.insert_error
#audit_axioms Vinc.ReplayWindow.inv_insert
#audit_axioms Vinc.ReplayWindow.insert_fresh
#audit_axioms Vinc.ReplayWindow.insert_highest
