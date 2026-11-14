import Vinc.MembershipInvTab
import Lean

/-!
# Property 9, part 2: the helpers keep `Inv`

The helpers every step is built from: `trace`, `emit`, `tx`, `bc`, `close`, the cursor loop `forKeys`, `home_delta`,
`bump`, and the tactics the later files use to close the field goals of `Inv` after a table update.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

variable {B : List Nat}

theorem inv_let (v : N) (b : N → N) (hv : Inv B v) (hb : ∀ x, x = v → Inv B x → Inv B (b x)) : Inv B (b v) := hb v rfl hv
theorem inv_letP {β : Type} (v : N) (b : N → N × β) (hv : Inv B v) (hb : ∀ x, x = v → Inv B x → Inv B (b x).1) : Inv B (b v).1 := hb v rfl hv
theorem inv_match {β : Type} (X : N × β) (k : N → β → N) (hX : Inv B X.1) (hk : ∀ a b, X = (a, b) → Inv B a → Inv B (k a b)) :
    Inv B (k X.1 X.2) := hk _ _ rfl hX
theorem inv_matchP {β γ : Type} (X : N × β) (k : N → β → N × γ) (hX : Inv B X.1) (hk : ∀ a b, X = (a, b) → Inv B a → Inv B (k a b).1) :
    Inv B (k X.1 X.2).1 := hk _ _ rfl hX

theorem inv_match3 {β γ : Type} (X : N × β × γ) (k : N → β → γ → N) (hX : Inv B X.1)
    (hk : ∀ a b c, X = (a, b, c) → Inv B a → Inv B (k a b c)) : Inv B (k X.1 X.2.1 X.2.2) := hk _ _ _ rfl hX
theorem inv_match3P {β γ δ : Type} (X : N × β × γ) (k : N → β → γ → N × δ) (hX : Inv B X.1)
    (hk : ∀ a b c, X = (a, b, c) → Inv B a → Inv B (k a b c).1) : Inv B (k X.1 X.2.1 X.2.2).1 := hk _ _ _ rfl hX

open Lean Elab Tactic Meta in
/-- Peel the outermost `let` (of a node, or of any other value) or pair `match` of the node in a goal `Inv B e` or
`Inv B e.1`: for a node, the goals "the value keeps `Inv`" and "the body keeps it for every node that has it". -/
elab "inv_let" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some (Bx, e) := (match t.consumeMData.getAppFnArgs with | (``Inv, #[b, e]) => some (b, e.consumeMData) | _ => none)
    | throwError m!"inv_let: not an Inv goal {t}"
  let (wrapped, e') := match e.getAppFnArgs with | (``Prod.fst, #[_, _, i]) => (true, i) | _ => (false, e)
  let nT := mkConst ``N
  let invB (x : Expr) : Expr := mkApp2 (mkConst ``Inv) Bx x
  let invOf (β : Expr) (x : Expr) : Expr :=
    invB (if wrapped then mkApp3 (mkConst ``Prod.fst [Level.zero, Level.zero]) nT β x else x)
  let β ← if wrapped then
      match (← whnf (← inferType e')).getAppFnArgs with | (``Prod, #[_, β]) => pure β | _ => throwError "inv_let: not a pair"
    else pure (mkConst ``Nat)
  match e' with
  | .letE nm ty v b _ =>
    if ty.isConstOf ``N then
      let bFun := Expr.lam nm ty b .default
      let hv ← mkFreshExprSyntheticOpaqueMVar (invB v)
      let hbT := Expr.forallE nm ty
        (Expr.forallE `hxe (mkApp3 (mkConst ``Eq [Level.succ Level.zero]) nT (.bvar 0) v)
          (Expr.forallE `hx (invB (.bvar 1)) (invOf β (b.liftLooseBVars 0 2)) .default) .default) .default
      let hb ← mkFreshExprSyntheticOpaqueMVar hbT
      let pf := if wrapped then mkApp6 (mkConst ``inv_letP) Bx β v bFun hv hb else mkApp5 (mkConst ``inv_let) Bx v bFun hv hb
      g.assign pf
      let (_, g2) ← hb.mvarId!.introN 3 [`x, `hxe, `hx]
      replaceMainGoal [hv.mvarId!, g2]
    else
      let nb := b.instantiate1 v
      let nb ← if wrapped then mkAppM ``Prod.fst #[nb] else pure nb
      let g' ← g.replaceTargetDefEq (invB nb)
      replaceMainGoal [g']
  | _ =>
    let some mApp ← matchMatcherApp? e' | throwError "inv_let: neither a let nor a match"
    unless mApp.discrs.size == 1 && mApp.alts.size == 1 do throwError "inv_let: not a pair match"
    let X := mApp.discrs[0]!
    let (``Prod, #[xa, β2]) := (← whnf (← inferType X)).getAppFnArgs | throwError "inv_let: not a pair"
    unless xa.isConstOf ``N do throwError "inv_let: not a node pair"
    let k := mApp.alts[0]!
    let np := mApp.altNumParams[0]!
    let hX ← mkFreshExprSyntheticOpaqueMVar (invB (mkApp3 (mkConst ``Prod.fst [Level.zero, Level.zero]) nT β2 X))
    if np == 2 then
      let hbT ← withLocalDeclD `a nT fun a => withLocalDeclD `b β2 fun b => do
        let eqT ← mkEq X (← mkAppM ``Prod.mk #[a, b])
        withLocalDeclD `hXe eqT fun hXe => withLocalDeclD `hx (invB a) fun hxv => do
        let body := (mkApp2 k a b).headBeta
        mkForallFVars #[a, b, hXe, hxv] (invOf β body)
      let hb ← mkFreshExprSyntheticOpaqueMVar hbT
      let pf := if wrapped then mkApp7 (mkConst ``inv_matchP) Bx β2 β X k hX hb else mkApp6 (mkConst ``inv_match) Bx β2 X k hX hb
      g.assign pf
      let (_, g2) ← hb.mvarId!.introN 4 [`n, `b, `hXe, `hx]
      replaceMainGoal [hX.mvarId!, g2]
    else if np == 3 then
      let (``Prod, #[b1, b2]) := (← whnf β2).getAppFnArgs | throwError "inv_let: not a triple"
      let hbT ← withLocalDeclD `a nT fun a => withLocalDeclD `b b1 fun b => withLocalDeclD `c b2 fun c => do
        let eqT ← mkEq X (← mkAppM ``Prod.mk #[a, ← mkAppM ``Prod.mk #[b, c]])
        withLocalDeclD `hXe eqT fun hXe => withLocalDeclD `hx (invB a) fun hxv => do
        let body := (mkApp3 k a b c).headBeta
        mkForallFVars #[a, b, c, hXe, hxv] (invOf β body)
      let hb ← mkFreshExprSyntheticOpaqueMVar hbT
      let pf := if wrapped then mkApp8 (mkConst ``inv_match3P) Bx b1 b2 β X k hX hb else mkApp7 (mkConst ``inv_match3) Bx b1 b2 X k hX hb
      g.assign pf
      let (_, g2) ← hb.mvarId!.introN 5 [`n, `b, `c, `hXe, `hx]
      replaceMainGoal [hX.mvarId!, g2]
    else throwError "inv_let: pattern arity"

theorem isBoot_mem {n : N} (h : Inv B n) {p : Nat} (hb : n.isBoot p = true) : p ∈ B := by
  have := h.bootEq; unfold N.isBoot at hb; rw [this] at hb; simpa using hb

open Lean Elab Tactic Meta in
/-- Close `p ∈ B` from a hypothesis `n.isBoot p = true` and the `Inv B n` of the same node, wherever they sit in the context. -/
elab "inv_boot" : tactic => withMainContext do
  let g ← getMainGoal
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, _) := ty.eq? | continue
    let lhs := lhs.consumeMData
    unless lhs.isAppOfArity ``N.isBoot 2 do continue
    let n := lhs.appFn!.appArg!
    for d2 in (← getLCtx) do
      if d2.isImplementationDetail then continue
      let ty2 ← instantiateMVars d2.type
      unless ty2.isAppOfArity ``Inv 2 do continue
      if (← isDefEq ty2.appArg! n) then
        let pf ← mkAppM ``isBoot_mem #[d2.toExpr, d.toExpr]
        unless (← isDefEq (← g.getType) (← inferType pf)) do continue
        g.assign pf
        replaceMainGoal []
        return
  throwError "inv_boot: no isBoot hypothesis"

/-- The guard of an insert: from the branch hypotheses of the code. -/
macro "inv_guard" : tactic =>
  `(tactic| first
    | assumption
    | (simp only [AMap.len, ASet.len] at *; assumption)
    | ((try simp only [Bool.or_eq_true] at *); (try simp only [decide_eq_true_eq] at *); (try simp only [AMap.len, ASet.len] at *); assumption)
    | (left; (try simp only [Bool.and_eq_true, Bool.or_eq_true] at *); (try simp only [decide_eq_true_eq] at *);
       (try simp only [AMap.len, ASet.len] at *); have e1 : MAX_TABLE = 4096 := rfl; have e2 : MAX_HUBS = 64 := rfl; omega)
    | (right; assumption)
    | (right; exact AMap.has_of_get? _ _ _ (by assumption))
    | (refine Classical.byContradiction fun hn => ?_; simp_all [AMap.len, ASet.len, MAX_TABLE, MAX_HUBS]; done)
    | (refine Classical.byContradiction fun hn => ?_; simp_all [AMap.len, ASet.len, MAX_TABLE, MAX_HUBS]; omega))

set_option hygiene false in
/-- A table known from the latest `Inv` hypothesis `hx`. -/
macro "inv_src" : tactic =>
  `(tactic| first
    | exact hx.roster | exact hx.attached | exact hx.homed | exact hx.susp | exact hx.downed | exact hx.revoked
    | exact hx.up | exact hx.members | exact hx.recheck | exact hx.left | exact hx.goneVer | exact hx.heard
    | exact hx.hrtt | exact hx.hsent | exact hx.helloAt | exact hx.hv | assumption
    | exact HvB.entries hx.hv _ _ (by assumption))

set_option hygiene false in
/-- A node id is one of the bootstrap hubs. -/
macro "inv_mem" : tactic => `(tactic| first | assumption | inv_boot | (have hb := hx.bootEq; simp_all [N.isBoot]; done))

set_option hygiene false in
/-- A table goal: a table already known, or an erase, an update or a guarded insert of one. -/
macro "inv_tab" : tactic =>
  `(tactic| first
    | inv_src
    | exact hx.bootEq | exact hx.bootLen | exact hx.bootNodup | exact hx.events | exact hx.traces
    | exact Bnd.nil | exact KBnd.nil | exact HvB.nil
    | (apply Bnd.erase; inv_src)
    | (apply Bnd.modify; inv_src)
    | (apply KBnd.erase; inv_src)
    | (apply KBnd.modify; inv_src)
    | (apply KBnd.unset; inv_src)
    | (apply HvB.erase; inv_src)
    | (apply HvB.map_erase; inv_src)
    | (refine Bnd.insert ?_ _ _ ?_ <;> first | inv_src | inv_guard)
    | (refine Bnd.orIns ?_ _ _ ?_ <;> first | inv_src | inv_guard)
    | (refine HvB.insert ?_ _ _ ?_ ?_ <;> first | inv_src | (dsimp only; first | exact Bnd.nil | inv_src | (apply Bnd.erase; inv_src) | (apply Bnd.modify; inv_src) | (refine Bnd.insert ?_ _ _ ?_ <;> first | inv_src | inv_guard)) | inv_guard)
    | (refine KBnd.insert ?_ _ _ ?_ <;> first | inv_src | inv_mem))

/-- Extend with the lemmas `Inv B n → Inv B (f ... n)` of the later files. -/
macro "inv_apply" : tactic => `(tactic| fail "no inv lemma")

set_option hygiene false in
/-- A node built field by field from the latest node `hx`. -/
macro "inv_leaf" : tactic =>
  `(tactic| (constructor <;> (try dsimp -zeta only) <;> inv_tab))

/-- A fold over the bootstrap hubs whose step keeps `Inv` for a hub of the node. -/
theorem inv_foldl_boot (f : N → Nat → N) (hf : ∀ n a, a ∈ B → Inv B n → Inv B (f n a)) (n : N) (h : Inv B n) :
    Inv B (n.boot.foldl f n) := by
  suffices H : ∀ (l : List Nat) (n : N), (∀ a ∈ l, a ∈ B) → Inv B n → Inv B (l.foldl f n) from
    H n.boot n (fun a ha => h.bootEq ▸ ha) h
  intro l
  induction l with
  | nil => intro n _ h; exact h
  | cons x r ih =>
    intro n hl h
    simp only [List.foldl_cons]
    exact ih (f n x) (fun a ha => hl a (List.mem_cons_of_mem _ ha)) (hf n x (hl x (List.mem_cons_self ..)) h)

theorem prod_fst_mk {α β : Type} (a : α) (b : β) : (a, b).1 = a := rfl

open Lean Elab Tactic Meta in
/-- Rewrite `Inv B (a, b).1` to `Inv B a`, only when the pair is written out (a syntactic test: cheap on any other goal). -/
elab "inv_fst" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let .app f x := t.consumeMData | throwError "inv_fst: not an Inv goal"
  let x := x.consumeMData
  unless x.isAppOfArity ``Prod.fst 3 do throwError "inv_fst: no projection"
  let pr := x.appArg!.consumeMData
  unless pr.isAppOfArity ``Prod.mk 4 do throwError "inv_fst: not a written pair"
  replaceMainGoal [← g.replaceTargetDefEq (mkApp f (pr.getArg! 2))]

set_option hygiene false in
/-- The whole walk of a step: peel lets and pair matches, split ifs and matches, apply a lemma for a call, check a leaf. -/
macro "inv_go" : tactic =>
  `(tactic| (repeat' (first | with_reducible assumption | inv_let | inv_fst | (with_reducible inv_apply) | split | with_reducible refine inv_foldl_boot _ (fun n a ha hx => ?_) _ ?_ | with_reducible refine inv_foldl2 _ (fun a x hx => ?_) _ ?_ | with_reducible refine inv_foldl _ (fun n a hx => ?_) _ ?_ | inv_boot | inv_leaf)))

theorem inv_trace {n : N} (h : Inv B n) (t : Tr) : Inv B (n.trace t) := by
  unfold N.trace
  split
  · exact h
  · split
    · inv_keep h
    · inv_keep h
      simp only [List.length_append, List.length_singleton]
      have := h.traces; rename_i h1 h2; simp at h2; unfold QUEUE_CAP at *; omega

theorem inv_emit {n : N} (h : Inv B n) (e : Ev) : Inv B (n.emit e) := by
  unfold N.emit
  split
  · inv_keep h
  · inv_keep h
    simp only [List.length_append, List.length_singleton]
    have := h.events; rename_i h2; simp at h2; unfold QUEUE_CAP at *; omega

theorem inv_tx {e : Env} {n : N} (h : Inv B n) (p : Nat) (r : Route) (f : NFrame) : Inv B (N.tx e n p r f).1 := by
  unfold N.tx
  split
  · exact h
  · dsimp only
    inv_keep (inv_trace h (Tr.frameOut p f.ty))

theorem inv_deltaTo {e : Env} {n : N} (h : Inv B n) (p m : Nat) (rc : Rec) (a : Alive) : Inv B (N.deltaTo e n p m rc a) :=
  inv_tx h _ _ _

theorem inv_bc {n : N} (h : Inv B n) (b : Bc) : Inv B (n.bc b) := by unfold N.bc; inv_keep h
theorem inv_close {n : N} (h : Inv B n) (p : Nat) (r : CloseR) : Inv B (n.close p r) := by unfold N.close; inv_keep h

theorem inv_beginQuiet {n : N} (h : Inv B n) (now cause : Nat) : Inv B (n.beginQuiet now cause) := by
  unfold N.beginQuiet
  refine inv_trace ?_ _
  have hr : Bnd (if (cause == 0) = true then n.recheck.map (fun (p : Nat × (Nat × Bool)) => (p.1, (satAdd now QUIET, false))) else n.recheck) := by
    split
    · exact h.recheck.map_keys _ (fun _ => rfl)
    · exact h.recheck
  inv_keep h
  exact hr

theorem inv_bump {n : N} (h : Inv B n) : Inv B n.bump := by
  unfold N.bump; exact inv_emit (by inv_keep h) _


theorem inv_forKeys {ks : List Nat} {f : Nat → N → N} (hf : ∀ k n, Inv B n → Inv B (f k n)) {n : N} (h : Inv B n) :
    Inv B (forKeys ks f n) := by
  unfold forKeys
  induction ks generalizing n with
  | nil => exact h
  | cons k r ih => exact ih (hf k n h)

/-- A fold whose step keeps a property of the accumulator keeps it. -/
theorem foldl_inv_inv {α β : Type} (P : β → Prop) (f : β → α → β) (hf : ∀ b a, P b → P (f b a)) (l : List α) (b : β)
    (h : P b) : P (l.foldl f b) := by
  induction l generalizing b with
  | nil => exact h
  | cons x r ih => exact ih _ (hf b x h)

theorem inv_foldl {α : Type} (f : N → α → N) (hf : ∀ n a, Inv B n → Inv B (f n a)) (l : List α) {n : N} (h : Inv B n) :
    Inv B (l.foldl f n) :=
  foldl_inv_inv (Inv B) f hf l n h

/-- A fold of `(node, flag)` accumulators. -/
theorem inv_foldl2 {α β : Type} (f : N × β → α → N × β) (hf : ∀ a x, Inv B a.1 → Inv B (f a x).1) (l : List α) {a : N × β}
    (h : Inv B a.1) : Inv B (l.foldl f a).1 :=
  foldl_inv_inv (fun p : N × β => Inv B p.1) f hf l a h

theorem inv_homeDelta {e : Env} {n : N} (h : Inv B n) (m : Nat) (rc : Rec) (a : Alive) : Inv B (N.homeDelta e n m rc a) := by
  unfold N.homeDelta
  exact inv_forKeys (fun k n hn => by split; exact inv_deltaTo hn _ _ _ _; exact hn) h

/-! ## Field frames of the helpers (what they leave alone) -/

theorem forKeys_field {α : Type} (g : N → α) {f : Nat → N → N} (hf : ∀ k n, g (f k n) = g n) (ks : List Nat) (n : N) :
    g (forKeys ks f n) = g n := by
  unfold forKeys
  induction ks generalizing n with
  | nil => rfl
  | cons k r ih => simp only [List.foldl_cons]; rw [ih, hf]

theorem homeDelta_members_inv (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).members = n.members := by
  unfold N.homeDelta
  refine forKeys_field (fun x => x.members) (fun k n => ?_) _ n
  split
  · exact (tx_tables e n k _ _).2.1
  · rfl

macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_trace)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_emit)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_bc)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_close)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_bump)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_beginQuiet)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_homeDelta)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_deltaTo)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_tx)

end Vinc.Membership
