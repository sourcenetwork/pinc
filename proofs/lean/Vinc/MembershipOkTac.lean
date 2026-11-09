import Vinc.MembershipSuspReach
import Lean

/-!
# The view never lists the node itself or a revoked node: the invariant and the walk of a step (property 6, 9)

`VOK n`: every entry of every hub copy, and every member of the view, is a node other than this one and not revoked
(`HvOK`, `MemOK`). This file defines it and the tactic `vk_go` that walks the body of a step of the machine (peeling
`let`s and pair matches, splitting `if`s and `match`es, applying a lemma for each call) the way the table-bound proof does
for its invariant; the lemmas for each call are in `MembershipOk*.lean`.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

/-- `m` is not this node and not revoked. -/
def Clean (n : N) (m : Nat) : Prop := m ≠ n.me ∧ n.revoked.has m = false

def HvOK (n : N) : Prop := ∀ p ∈ n.hv, ∀ m, p.2.entries.has m = true → Clean n m
def MemOK (n : N) : Prop := ∀ m, n.members.has m = true → Clean n m

structure VOK (n : N) : Prop where
  hv : HvOK n
  mem : MemOK n

theorem vk_let (v : N) (b : N → N) (hv : VOK v) (hb : ∀ x, VOK x → VOK (b x)) : VOK (b v) := hb v hv
theorem vk_letP {β : Type} (v : N) (b : N → N × β) (hv : VOK v) (hb : ∀ x, VOK x → VOK (b x).1) : VOK (b v).1 := hb v hv
theorem vk_match {β : Type} (X : N × β) (k : N → β → N) (hX : VOK X.1) (hk : ∀ a b, VOK a → VOK (k a b)) :
    VOK (k X.1 X.2) := hk _ _ hX
theorem vk_matchP {β γ : Type} (X : N × β) (k : N → β → N × γ) (hX : VOK X.1) (hk : ∀ a b, VOK a → VOK (k a b).1) :
    VOK (k X.1 X.2).1 := hk _ _ hX
theorem vk_match3 {β γ : Type} (X : N × β × γ) (k : N → β → γ → N) (hX : VOK X.1)
    (hk : ∀ a b c, VOK a → VOK (k a b c)) : VOK (k X.1 X.2.1 X.2.2) := hk _ _ _ hX
theorem vk_match3P {β γ δ : Type} (X : N × β × γ) (k : N → β → γ → N × δ) (hX : VOK X.1)
    (hk : ∀ a b c, VOK a → VOK (k a b c).1) : VOK (k X.1 X.2.1 X.2.2).1 := hk _ _ _ hX

open Lean Elab Tactic Meta in
/-- Peel the outermost `let` (of a node, or of any other value) or pair `match` of the node in a goal `VOK e` or
`VOK e.1`: for a node, the goals "the value keeps `VOK`" and "the body keeps it for every node that has it". -/
elab "vk_let" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some e := (match t.consumeMData.getAppFnArgs with | (``VOK, #[e]) => some e.consumeMData | _ => none)
    | throwError m!"vk_let: not a VOK goal {t}"
  let (wrapped, e') := match e.getAppFnArgs with | (``Prod.fst, #[_, _, i]) => (true, i) | _ => (false, e)
  let nT := mkConst ``N
  let invB (x : Expr) : Expr := mkApp (mkConst ``VOK) x
  let invOf (β : Expr) (x : Expr) : Expr :=
    invB (if wrapped then mkApp3 (mkConst ``Prod.fst [Level.zero, Level.zero]) nT β x else x)
  let β ← if wrapped then
      match (← whnf (← inferType e')).getAppFnArgs with | (``Prod, #[_, β]) => pure β | _ => throwError "vk_let: not a pair"
    else pure (mkConst ``Nat)
  match e' with
  | .letE nm ty v b _ =>
    if ty.isConstOf ``N then
      let bFun := Expr.lam nm ty b .default
      let hv ← mkFreshExprSyntheticOpaqueMVar (invB v)
      let hbT := Expr.forallE nm ty
        (Expr.forallE `hx (invB (.bvar 0)) (invOf β (b.liftLooseBVars 0 1)) .default) .default
      let hb ← mkFreshExprSyntheticOpaqueMVar hbT
      let pf := if wrapped then mkApp5 (mkConst ``vk_letP) β v bFun hv hb else mkApp4 (mkConst ``vk_let) v bFun hv hb
      g.assign pf
      let (_, g2) ← hb.mvarId!.introN 2 [`x, `hx]
      replaceMainGoal [hv.mvarId!, g2]
    else
      let nb := b.instantiate1 v
      let nb ← if wrapped then mkAppM ``Prod.fst #[nb] else pure nb
      let g' ← g.replaceTargetDefEq (invB nb)
      replaceMainGoal [g']
  | _ =>
    let some mApp ← matchMatcherApp? e' | throwError "vk_let: neither a let nor a match"
    unless mApp.discrs.size == 1 && mApp.alts.size == 1 do throwError "vk_let: not a pair match"
    let X := mApp.discrs[0]!
    let (``Prod, #[xa, β2]) := (← whnf (← inferType X)).getAppFnArgs | throwError "vk_let: not a pair"
    unless xa.isConstOf ``N do throwError "vk_let: not a node pair"
    let k := mApp.alts[0]!
    let np := mApp.altNumParams[0]!
    let hX ← mkFreshExprSyntheticOpaqueMVar (invB (mkApp3 (mkConst ``Prod.fst [Level.zero, Level.zero]) nT β2 X))
    if np == 2 then
      let hbT ← withLocalDeclD `a nT fun a => withLocalDeclD `b β2 fun b => withLocalDeclD `hx (invB a) fun hxv => do
        let body := (mkApp2 k a b).headBeta
        mkForallFVars #[a, b, hxv] (invOf β body)
      let hb ← mkFreshExprSyntheticOpaqueMVar hbT
      let pf := if wrapped then mkApp6 (mkConst ``vk_matchP) β2 β X k hX hb else mkApp5 (mkConst ``vk_match) β2 X k hX hb
      g.assign pf
      let (_, g2) ← hb.mvarId!.introN 3 [`n, `b, `hx]
      replaceMainGoal [hX.mvarId!, g2]
    else if np == 3 then
      let (``Prod, #[b1, b2]) := (← whnf β2).getAppFnArgs | throwError "vk_let: not a triple"
      let hbT ← withLocalDeclD `a nT fun a => withLocalDeclD `b b1 fun b => withLocalDeclD `c b2 fun c => withLocalDeclD `hx (invB a) fun hxv => do
        let body := (mkApp3 k a b c).headBeta
        mkForallFVars #[a, b, c, hxv] (invOf β body)
      let hb ← mkFreshExprSyntheticOpaqueMVar hbT
      let pf := if wrapped then mkApp7 (mkConst ``vk_match3P) b1 b2 β X k hX hb else mkApp6 (mkConst ``vk_match3) b1 b2 X k hX hb
      g.assign pf
      let (_, g2) ← hb.mvarId!.introN 4 [`n, `b, `c, `hx]
      replaceMainGoal [hX.mvarId!, g2]
    else throwError "vk_let: pattern arity"

/-- A fold whose step keeps a property of the accumulator keeps it. -/
theorem vk_foldl_gen {α β : Type} (P : β → Prop) (f : β → α → β) (hf : ∀ b a, P b → P (f b a)) (l : List α) (b : β)
    (h : P b) : P (l.foldl f b) := by
  induction l generalizing b with
  | nil => exact h
  | cons x r ih => exact ih _ (hf b x h)

theorem vk_foldl {α : Type} (f : N → α → N) (hf : ∀ n a, VOK n → VOK (f n a)) (l : List α) {n : N} (h : VOK n) :
    VOK (l.foldl f n) :=
  vk_foldl_gen VOK f hf l n h

theorem vk_foldl2 {α β : Type} (f : N × β → α → N × β) (hf : ∀ a x, VOK a.1 → VOK (f a x).1) (l : List α) {a : N × β}
    (h : VOK a.1) : VOK (l.foldl f a).1 :=
  vk_foldl_gen (fun p : N × β => VOK p.1) f hf l a h

theorem vk_forKeys {ks : List Nat} {f : Nat → N → N} (hf : ∀ k n, VOK n → VOK (f k n)) {n : N} (h : VOK n) :
    VOK (forKeys ks f n) := by
  unfold forKeys
  induction ks generalizing n with
  | nil => exact h
  | cons k r ih => exact ih (hf k n h)

theorem prod_fst_mk' {α β : Type} (a : α) (b : β) : (a, b).1 = a := rfl

/-- Extend with the lemmas `VOK n → VOK (f ... n)` of the later files. -/
macro "vk_apply" : tactic => `(tactic| fail "no vk lemma")

theorem vk_of {x y : N} (h : VOK x) (e1 : y.hv = x.hv) (e2 : y.members = x.members) (e3 : y.revoked = x.revoked)
    (e4 : y.me = x.me) : VOK y := by
  refine ⟨fun p hp m hm => ?_, fun m hm => ?_⟩
  · rw [e1] at hp
    have := h.hv p hp m hm
    unfold Clean at *; rw [e3, e4]; exact this
  · rw [e2] at hm
    have := h.mem m hm
    unfold Clean at *; rw [e3, e4]; exact this

/-- A node built by an update of fields other than the hub copies, the view, `revoked` and `me`. -/
macro "vk_leaf" : tactic => `(tactic| (refine vk_of ?_ ?_ ?_ ?_ ?_ <;> first | assumption | with_reducible rfl))

/-- The whole walk of a step: peel lets and pair matches, split ifs and matches, apply a lemma for a call, check a leaf. -/
macro "vk_go" : tactic =>
  `(tactic| (repeat' (first | with_reducible assumption | rw [prod_fst_mk'] | vk_let | (with_reducible vk_apply) | split | refine vk_foldl _ (fun n a hx => ?_) _ ?_ | refine vk_foldl2 _ (fun a x hx => ?_) _ ?_ | vk_leaf)))

end Vinc.Membership
