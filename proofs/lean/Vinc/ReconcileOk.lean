import Vinc.ReconcileSession

/-!
# Reconcile Ok: a postcondition calculus for the `Except` monad of the machine

`Ok P x` says every successful result of `x` satisfies `P`. The rules follow the shape of the `do` blocks of the
machine (`bind`, `pure`, `throw`, `if`), so a property of a handler that holds on every success path is proved by
walking the block once, without a case split per branch.
-/

namespace Vinc.Reconcile

/-- Every success of `x` satisfies `P`. -/
def Ok {ε α : Type} (P : α → Prop) (x : Except ε α) : Prop := ∀ v, x = .ok v → P v

namespace Ok
variable {ε α β : Type} {P : α → Prop} {Q : β → Prop}

theorem pure (a : α) (h : P a) : Ok P (Pure.pure a : Except ε α) := by
  intro v hv; cases hv; exact h

theorem throw (e : ε) : Ok P (throw e : Except ε α) := by
  intro v hv; cases hv

theorem triv (x : Except ε α) : Ok (fun _ => True) x := fun _ _ => trivial

theorem mono {P P' : α → Prop} {x : Except ε α} (h : Ok P x) (hp : ∀ a, P a → P' a) : Ok P' x :=
  fun v hv => hp v (h v hv)

theorem bind {x : Except ε α} {f : α → Except ε β} (hx : Ok P x) (hf : ∀ a, P a → Ok Q (f a)) :
    Ok Q (x >>= f) := by
  intro v hv
  cases hx' : x with
  | error e => rw [hx'] at hv; cases hv
  | ok a =>
    rw [hx'] at hv
    exact hf a (hx a hx') v hv

theorem ite {c : Prop} [Decidable c] {x y : Except ε α} (h1 : c → Ok P x) (h2 : ¬c → Ok P y) :
    Ok P (if c then x else y) := by
  split
  · next h => exact h1 h
  · next h => exact h2 h

theorem map {x : Except ε α} {f : α → β} (h : Ok P x) (hf : ∀ a, P a → Q (f a)) : Ok Q (f <$> x) := by
  intro v hv
  cases hx : x with
  | error e => simp [hx, Functor.map, Except.map] at hv
  | ok a =>
    simp only [hx, Functor.map, Except.map] at hv
    cases hv; exact hf a (h a hx)

theorem mapError {x : Except ε α} {f : ε → ε'} (h : Ok P x) : Ok P (x.mapError f) := by
  intro v hv
  cases hx : x with
  | error e => simp [hx, Except.mapError] at hv
  | ok a => simp only [hx, Except.mapError] at hv; cases hv; exact h _ hx

end Ok

/-- A step keeps the fields that no part rule writes (the frames, the limits, the counters, the scratch bound). -/
def Keeps (c c' : Core) : Prop :=
  c'.frames = c.frames ∧ c'.lim = c.lim ∧ c'.n = c.n ∧ c'.init = c.init ∧ c'.exact = c.exact ∧
    c'.rounds = c.rounds ∧ c'.coldAt = c.coldAt ∧ c'.coldLo = c.coldLo ∧ c'.hdr = c.hdr

theorem Keeps.refl (c : Core) : Keeps c c := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {a b c : Core} (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7, b8.trans a8,
    b9.trans a9⟩

-- One step of the walk through a `do` block whose every success returns a core that `Keeps` the input `c` in its
-- first component: `bind` with a trivial intermediate postcondition, `if`, `pure`, `throw`.
set_option hygiene false in
macro "okstep" : tactic => `(tactic| first
  | (refine Ok.bind (P := fun p : Option Item × List Nat × Core => Keeps c p.2.2) ?_ ?_; (rotate_left; rintro ⟨_, _, _⟩ _))
  | (refine Ok.bind (P := fun _ => True) (Ok.triv _) ?_; intro x _; first | (rcases x with ⟨_, _, _, _⟩) | (rcases x with ⟨_, _, _⟩) | (rcases x with ⟨_, _⟩) | (rcases x with _ | _) | skip)
  | (refine Ok.ite ?_ ?_ <;> intro _)
  | (apply Ok.pure; first | assumption | exact Keeps.refl _ | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | (refine Keeps.trans (by assumption) ?_; unfold Keeps Core.bump; first | simp | (split <;> simp)))
  | exact Ok.throw _
  | (dsimp only [letFun])
  | (dsimp only))

end Vinc.Reconcile
