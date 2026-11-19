import Pinc.ReconcileRefTail
import Pinc.ReconcileOk

/-!
# Reconcile keeps: a part rule writes only the reply, the part counters, the report arenas and the leaf flag

`tailPart_keeps` walks the arms of `procPart` once with the `Ok` calculus: every success returns a core that `Keeps` the
frames, the limits, the item count, the role, the exact flag, the round counter, the cold cursor and the header of its
input. The walk never looks at the value a step returns (`Ok.bind_any`): no part rule takes its core from a monadic
result, so the postcondition holds whatever the reads and the index return. `procPart_keeps` and `answerLoop_keeps`
follow, and with the guard of `pushFrame` they give the frame stack bound (`ReconcileFrames`).
-/

namespace Pinc.Reconcile

/-- The postcondition does not look at the value of the first step: every continuation satisfies it. -/
theorem Ok.bind_any {ε α β : Type} {P : β → Prop} {x : Except ε α} {f : α → Except ε β}
    (h : ∀ a, Ok P (f a)) : Ok P (x >>= f) := Ok.bind (P := fun _ => True) (Ok.triv _) (fun a _ => h a)

macro "closeKeeps" : tactic => `(tactic| first
  | exact Keeps.refl _
  | (unfold Keeps Core.bump; (try split) <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))

macro "okw" : tactic => `(tactic| first
  | (refine Ok.bind_any (fun _ => ?_))
  | (refine Ok.ite (fun _ => ?_) (fun _ => ?_))
  | (apply Ok.pure; closeKeeps)
  | exact Ok.throw _
  | split
  | (dsimp only [letFun])
  | (dsimp only))

theorem tailPart_keeps (o : Oracle) (S : List Item) (c : Core) (kind : Nat) (lo : Item) (hi : Option Item)
    (r : List Nat) (mark : Nat) : Ok (fun p => Keeps c p.1) (tailPart o S c kind lo hi r mark) := by
  unfold tailPart
  repeat' okw

theorem procPart_keeps (o : Oracle) (S : List Item) (c : Core) (r : List Nat) (mark : Nat) :
    Ok (fun p => Keeps c p.1) (procPart o S c r mark) := by
  rw [procPart_eq]
  cases h : readHead c.blast r c.lim.maxItem with
  | error e => intro v hv; simp at hv
  | ok q =>
    obtain ⟨⟨kind, lo, hi⟩, l, r1⟩ := q
    refine Ok.mono (tailPart_keeps o S { c with blast := l } kind lo hi r1 mark) ?_
    intro p hp
    have h0 : Keeps c { c with blast := l } := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact Keeps.trans h0 hp

theorem answerLoop_keeps (o : Oracle) (S : List Item) :
    ∀ (k : Nat) (c : Core) (r : List Nat), Ok (fun p => Keeps c p.1) (answerLoop o S c r k) := by
  intro k
  induction k with
  | zero => intro c r; simp only [answerLoop]; exact Ok.pure _ (Keeps.refl _)
  | succ k ih =>
    intro c r
    simp only [answerLoop]
    refine Ok.bind (P := fun p : Core × List Nat => Keeps { c with out := (c.out.mark).2, bsnap := c.blast } p.1)
      (procPart_keeps _ _ _ _ _) ?_
    rintro ⟨c', r'⟩ hk
    have hk0 : Keeps c { c with out := (c.out.mark).2, bsnap := c.blast } := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hk1 := Keeps.trans hk0 hk
    refine Ok.ite (fun _ => Ok.ite (fun _ => Ok.throw _) (fun _ => Ok.pure _ ?_)) (fun _ => ?_)
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hk1
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
    · refine Ok.mono (ih c' r') ?_
      intro p hp; exact Keeps.trans hk1 hp

#audit_axioms Pinc.Reconcile.procPart_keeps
#audit_axioms Pinc.Reconcile.answerLoop_keeps

end Pinc.Reconcile
