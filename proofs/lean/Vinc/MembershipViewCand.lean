import Vinc.MembershipViewThm

/-!
# Membership view: the union of the fresh hub copies, the highest incarnation winning (properties 3 and 4)

`recompute_one` decides a member's place from the hub copies. This file proves what the decision is:

* `candidates_none_iff`: no candidate exists exactly when every eligible copy either does not list the member or lists it
  with an omission that has lasted a full lease;
* `candidates_listed`: a candidate is the record of some eligible copy that lists the member, not expired;
* `candidates_max`: no eligible, non-expired copy lists a higher incarnation than the candidate (the highest incarnation
  wins);
* `candidates_congr`: the candidate depends only on the hub copies, the source and which hubs are up, so two nodes with
  the same copies and the same source compute the same candidate (convergence after a heal).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

/-- Whether hub `hub` feeds the view, for source `src`. -/
def N.eligible (n : N) (now : Nat) (src : Source) (hub : Nat) : Bool :=
  match src.only with
  | some o => o == hub
  | none => !src.anyFresh || n.hubUp now hub

/-- An omission that has lasted a full lease. -/
def expiredAbs (now : Nat) (ce : CopyEntry) : Bool :=
  match ce.absentSince with | some t => decide (LEASE ≤ now - t) | none => false

/-- The step of the fold of `candidates`. -/
def candStep (n : N) (now : Nat) (src : Source) (m : Nat) (acc : Option (Rec × Bool) × Bool) (p : Nat × HubCopy) :
    Option (Rec × Bool) × Bool :=
  let (best, expired) := acc
  let hub := p.1
  if !n.eligible now src hub then acc
  else match p.2.entries.get? m with
    | none => acc
    | some ce =>
      let absent := ce.absentSince.isSome
      if expiredAbs now ce then (best, true)
      else
        let better := match best with
          | none => true
          | some (b, babs) => decide (b.inc < ce.rc.inc) || (ce.rc.inc == b.inc && babs && !absent)
        if better then (some (ce.rc, absent), expired) else acc

theorem candidates_eq (n : N) (now : Nat) (src : Source) (m : Nat) :
    n.candidates now src m = n.hv.foldl (candStep n now src m) (none, false) := rfl

/-- A live listing: eligible hub, entry present, omission not expired. -/
def Live (n : N) (now : Nat) (src : Source) (m : Nat) (p : Nat × HubCopy) (ce : CopyEntry) : Prop :=
  n.eligible now src p.1 = true ∧ p.2.entries.get? m = some ce ∧ expiredAbs now ce = false

theorem fold_best_mono (n : N) (now : Nat) (src : Source) (m : Nat) (L : List (Nat × HubCopy))
    (acc : Option (Rec × Bool) × Bool) (b : Rec) (ba : Bool) (h : acc.1 = some (b, ba)) :
    ∃ b' ba', (L.foldl (candStep n now src m) acc).1 = some (b', ba') ∧ b.inc ≤ b'.inc := by
  induction L generalizing acc b ba with
  | nil => exact ⟨b, ba, h, Nat.le_refl _⟩
  | cons p r ih =>
    simp only [List.foldl_cons]
    obtain ⟨best, expired⟩ := acc
    simp only at h
    subst h
    have hstep : ∃ b2 ba2, (candStep n now src m (some (b, ba), expired) p).1 = some (b2, ba2) ∧ b.inc ≤ b2.inc := by
      unfold candStep
      dsimp only
      by_cases he : (!n.eligible now src p.1) = true
      · simp [he]
      · simp only [he, if_false]
        cases hg : p.2.entries.get? m with
        | none => simp
        | some ce =>
          simp only []
          by_cases hx : expiredAbs now ce = true
          · simp [hx]
          · simp only [hx, if_false]
            by_cases hb : (decide (b.inc < ce.rc.inc) || (ce.rc.inc == b.inc && ba && !ce.absentSince.isSome)) = true
            · simp only [hb, if_true]
              refine ⟨ce.rc, ce.absentSince.isSome, rfl, ?_⟩
              simp at hb
              rcases hb with hb | hb
              · omega
              · omega
            · simp only [hb, if_false]; exact ⟨b, ba, rfl, Nat.le_refl _⟩
    obtain ⟨b2, ba2, h2, hle⟩ := hstep
    obtain ⟨b3, ba3, h3, hle2⟩ := ih (candStep n now src m (some (b, ba), expired) p) b2 ba2 h2
    exact ⟨b3, ba3, h3, Nat.le_trans hle hle2⟩


/-- One step of the fold: what it does to the candidate. -/
theorem step_spec (n : N) (now : Nat) (src : Source) (m : Nat) (acc : Option (Rec × Bool) × Bool) (p : Nat × HubCopy) :
    let acc' := candStep n now src m acc p
    -- a live listing is dominated by the new candidate
    (∀ ce, Live n now src m p ce → ∃ b ba, acc'.1 = some (b, ba) ∧ ce.rc.inc ≤ b.inc) ∧
    -- an old candidate is never lowered
    (∀ b ba, acc.1 = some (b, ba) → ∃ b' ba', acc'.1 = some (b', ba') ∧ b.inc ≤ b'.inc) ∧
    -- the new candidate is the old one or a live listing
    (∀ b ba, acc'.1 = some (b, ba) → acc.1 = some (b, ba) ∨ ∃ ce, Live n now src m p ce ∧ ce.rc = b) ∧
    (acc'.1 = none → acc.1 = none ∧ ∀ ce, ¬ Live n now src m p ce) := by
  obtain ⟨best, expired⟩ := acc
  unfold candStep Live
  dsimp only
  by_cases he : (!n.eligible now src p.1) = true
  · simp only [he, if_true]
    have : n.eligible now src p.1 = false := by simpa using he
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ce h; simp [this] at h
    · intro b ba h; exact ⟨b, ba, h, Nat.le_refl _⟩
    · intro b ba h; exact Or.inl h
    · intro h; exact ⟨h, fun ce hc => by simp [this] at hc⟩
  · simp only [he, if_false]
    have hel : n.eligible now src p.1 = true := by simpa using he
    cases hg : p.2.entries.get? m with
    | none =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ce h; simp [hg] at h
      · intro b ba h; exact ⟨b, ba, h, Nat.le_refl _⟩
      · intro b ba h; exact Or.inl h
      · intro h; exact ⟨h, fun ce hc => by simp [hg] at hc⟩
    | some ce =>
      by_cases hx : expiredAbs now ce = true
      · simp only [hx, if_true]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro ce' h; obtain ⟨_, h1, h2⟩ := h; have h1' := Option.some.inj h1; subst h1'; simp [hx] at h2
        · intro b ba h; exact ⟨b, ba, h, Nat.le_refl _⟩
        · intro b ba h; exact Or.inl h
        · intro h; exact ⟨h, fun ce' hc => by obtain ⟨_, h1, h2⟩ := hc; simp [hg] at h1; subst h1; simp [hx] at h2⟩
      · simp only [hx, if_false]
        have hx' : expiredAbs now ce = false := by simpa using hx
        have live : n.eligible now src p.1 = true ∧ some ce = some ce ∧ expiredAbs now ce = false := ⟨hel, rfl, hx'⟩
        cases best with
        | none =>
          simp only [decide_true, Bool.true_or, if_true]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro ce' h
            have : ce' = ce := by obtain ⟨_, h1, _⟩ := h; simp [hg] at h1; exact h1.symm
            subst this; exact ⟨ce'.rc, ce'.absentSince.isSome, rfl, Nat.le_refl _⟩
          · intro b ba h; simp at h
          · intro b ba h; simp at h; right; exact ⟨ce, live, h.1⟩
          · intro h; simp at h
        | some bb =>
          obtain ⟨b, babs⟩ := bb
          by_cases hb : (decide (b.inc < ce.rc.inc) || (ce.rc.inc == b.inc && babs && !ce.absentSince.isSome)) = true
          · simp only [hb, if_true]
            have hlt : b.inc ≤ ce.rc.inc := by simp at hb; rcases hb with hb | hb <;> omega
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro ce' h
              have : ce' = ce := by obtain ⟨_, h1, _⟩ := h; simp [hg] at h1; exact h1.symm
              subst this; exact ⟨ce'.rc, ce'.absentSince.isSome, rfl, Nat.le_refl _⟩
            · intro b2 ba2 h; simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨ce.rc, ce.absentSince.isSome, rfl, hlt⟩
            · intro b2 ba2 h; simp at h; right; exact ⟨ce, live, h.1⟩
            · intro h; simp at h
          · simp only [hb, if_false]
            have hge : ce.rc.inc ≤ b.inc := by simp at hb; omega
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro ce' h
              have : ce' = ce := by obtain ⟨_, h1, _⟩ := h; simp [hg] at h1; exact h1.symm
              subst this; exact ⟨b, babs, rfl, hge⟩
            · intro b2 ba2 h; exact ⟨b2, ba2, h, Nat.le_refl _⟩
            · intro b2 ba2 h; exact Or.inl h
            · intro h; simp at h


theorem fold_spec (n : N) (now : Nat) (src : Source) (m : Nat) (L : List (Nat × HubCopy)) :
    ∀ acc : Option (Rec × Bool) × Bool,
    (∀ p ∈ L, ∀ ce, Live n now src m p ce → ∃ b ba, (L.foldl (candStep n now src m) acc).1 = some (b, ba) ∧ ce.rc.inc ≤ b.inc) ∧
    (∀ b ba, acc.1 = some (b, ba) → ∃ b' ba', (L.foldl (candStep n now src m) acc).1 = some (b', ba') ∧ b.inc ≤ b'.inc) ∧
    (∀ b ba, (L.foldl (candStep n now src m) acc).1 = some (b, ba) →
      acc.1 = some (b, ba) ∨ ∃ p ∈ L, ∃ ce, Live n now src m p ce ∧ ce.rc = b) ∧
    ((L.foldl (candStep n now src m) acc).1 = none → acc.1 = none ∧ ∀ p ∈ L, ∀ ce, ¬ Live n now src m p ce) := by
  induction L with
  | nil =>
    intro acc
    refine ⟨by simp, fun b ba h => ⟨b, ba, h, Nat.le_refl _⟩, fun b ba h => Or.inl h, fun h => ⟨h, by simp⟩⟩
  | cons q r ih =>
    intro acc
    obtain ⟨hs1, hs2, hs3, hs4⟩ := step_spec n now src m acc q
    obtain ⟨hA, hB, hC, hD⟩ := ih (candStep n now src m acc q)
    simp only [List.foldl_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp ce hl
      rcases List.mem_cons.mp hp with rfl | hp
      · obtain ⟨b, ba, h1, h2⟩ := hs1 ce hl
        obtain ⟨b', ba', h3, h4⟩ := hB b ba h1
        exact ⟨b', ba', h3, Nat.le_trans h2 h4⟩
      · exact hA p hp ce hl
    · intro b ba h
      obtain ⟨b1, ba1, h1, h2⟩ := hs2 b ba h
      obtain ⟨b', ba', h3, h4⟩ := hB b1 ba1 h1
      exact ⟨b', ba', h3, Nat.le_trans h2 h4⟩
    · intro b ba h
      rcases hC b ba h with h1 | ⟨p, hp, ce, hl, he⟩
      · rcases hs3 b ba h1 with h2 | ⟨ce, hl, he⟩
        · exact Or.inl h2
        · exact Or.inr ⟨q, List.mem_cons_self .., ce, hl, he⟩
      · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, ce, hl, he⟩
    · intro h
      obtain ⟨h1, h2⟩ := hD h
      obtain ⟨h3, h4⟩ := hs4 h1
      refine ⟨h3, ?_⟩
      intro p hp ce hl
      rcases List.mem_cons.mp hp with rfl | hp
      · exact h4 ce hl
      · exact h2 p hp ce hl

/-- The highest incarnation wins: a live listing of `m` is never above the candidate. -/
theorem candidates_max (n : N) (now : Nat) (src : Source) (m : Nat) (p : Nat × HubCopy) (hp : p ∈ n.hv) (ce : CopyEntry)
    (hl : Live n now src m p ce) :
    ∃ b ba, (n.candidates now src m).1 = some (b, ba) ∧ ce.rc.inc ≤ b.inc := by
  rw [candidates_eq]
  exact (fold_spec n now src m n.hv (none, false)).1 p hp ce hl

/-- A candidate is the record of a live listing: some eligible copy lists the member with that record. -/
theorem candidates_listed (n : N) (now : Nat) (src : Source) (m : Nat) (b : Rec) (ba : Bool)
    (h : (n.candidates now src m).1 = some (b, ba)) :
    ∃ p ∈ n.hv, ∃ ce, Live n now src m p ce ∧ ce.rc = b := by
  rw [candidates_eq] at h
  rcases (fold_spec n now src m n.hv (none, false)).2.2.1 b ba h with h1 | h1
  · simp at h1
  · exact h1

/-- No candidate exactly when no eligible copy lists the member with a live omission state. -/
theorem candidates_none_iff (n : N) (now : Nat) (src : Source) (m : Nat) :
    (n.candidates now src m).1 = none ↔ ∀ p ∈ n.hv, ∀ ce, ¬ Live n now src m p ce := by
  constructor
  · intro h
    rw [candidates_eq] at h
    exact ((fold_spec n now src m n.hv (none, false)).2.2.2 h).2
  · intro h
    cases hc : (n.candidates now src m).1 with
    | none => rfl
    | some x =>
      obtain ⟨b, ba⟩ := x
      obtain ⟨p, hp, ce, hl, _⟩ := candidates_listed n now src m b ba hc
      exact absurd hl (h p hp ce)

/-- Two nodes with the same hub copies, the same source and the same live hubs compute the same candidate: the
view is a function of the copies (convergence after a heal). -/
theorem candidates_congr (n n' : N) (now : Nat) (src : Source) (m : Nat) (hv : n'.hv = n.hv)
    (hup : ∀ h, n'.hubUp now h = n.hubUp now h) : n'.candidates now src m = n.candidates now src m := by
  have he : ∀ h, n'.eligible now src h = n.eligible now src h := by
    intro h; unfold N.eligible; rw [hup]
  rw [candidates_eq, candidates_eq, hv]
  have : candStep n' now src m = candStep n now src m := by
    funext acc p; simp only [candStep, he]
  rw [this]

end Vinc.Membership
