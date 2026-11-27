import Pinc.MembershipModelLemmas

/-!
# Hub theorems, part 1: what the helpers of the roster leave alone

The hub rules (`hub.rs`) call `push_delta`, which folds a roster change into the node's own view
(`apply_delta`, `recompute_one`, `remove_from_view`, `home_delta`, `bump`). None of these touches the hub's own
tables or the broadcast-layer calls; the hub theorems follow the roster, the suspicions, the held members, the
revocations and the broadcast-layer list through these calls with the relation `HT`.

`recompute_one` and `apply_delta` are large; to keep the proofs small they are restated as compositions of small
named functions (`recomputeOneS`, `applyDeltaCoreS`), and the restatement is proved equal to the model by `rfl`
(`recomputeOne_eq`, `applyDeltaCore_eq`), so nothing is assumed.
-/

set_option linter.unusedVariables false

namespace Pinc.Membership
open Pinc.MemInc

/-- The hub tables, the facts the hub rules read, and the broadcast-layer and close lists. -/
def N.HT (a b : N) : Prop :=
  a.roster = b.roster ∧ a.susp = b.susp ∧ a.downed = b.downed ∧ a.revoked = b.revoked ∧ a.attached = b.attached ∧ a.homed = b.homed ∧ a.up = b.up ∧ a.heard = b.heard ∧ a.me = b.me ∧ a.boot = b.boot ∧ a.isHub = b.isHub ∧ a.outBc = b.outBc ∧ a.outClose = b.outClose

theorem N.HT_refl (n : N) : n.HT n := by unfold N.HT; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem N.HT_trans {a b c : N} (h1 : a.HT b) (h2 : b.HT c) : a.HT c := by
  unfold N.HT at *
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12⟩ := h1
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12⟩ := h2
  exact ⟨x0.trans y0, x1.trans y1, x2.trans y2, x3.trans y3, x4.trans y4, x5.trans y5, x6.trans y6, x7.trans y7, x8.trans y8, x9.trans y9, x10.trans y10, x11.trans y11, x12.trans y12⟩

theorem trace_ht (n : N) (t : Tr) : (n.trace t).HT n := by
  unfold N.trace N.HT; split <;> (try split) <;> simp

theorem emit_ht (n : N) (e : Ev) : (n.emit e).HT n := by
  unfold N.emit N.HT; split <;> simp

theorem tx_ht (e : Env) (n : N) (p : Nat) (r : Route) (f : NFrame) : (N.tx e n p r f).1.HT n := by
  unfold N.tx
  split
  · exact N.HT_refl n
  · exact N.HT_trans (b := n.trace (Tr.frameOut p f.ty)) (by unfold N.HT; simp) (trace_ht n _)

theorem deltaTo_ht (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).HT n :=
  tx_ht e n p _ _

theorem forKeys_ht (ks : List Nat) (f : Nat → N → N) (h : ∀ k n, (f k n).HT n) (n : N) : (forKeys ks f n).HT n := by
  unfold forKeys
  induction ks generalizing n with
  | nil => exact N.HT_refl n
  | cons k r ih => simp only [List.foldl_cons]; exact N.HT_trans (ih (f k n)) (h k n)

theorem bump_ht (n : N) : n.bump.HT n := by
  unfold N.bump; exact N.HT_trans (emit_ht _ _) (by unfold N.HT; simp)

theorem homeDelta_ht (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).HT n := by
  unfold N.homeDelta
  exact forKeys_ht _ _ (fun k n => by split; exact deltaTo_ht ..; exact N.HT_refl n) n

theorem ite_ht (c : Prop) [Decidable c] (a b n : N) (h1 : a.HT n) (h2 : b.HT n) : (if c then a else b).HT n := by
  split <;> assumption

/-! ## Field facts as simp lemmas -/

@[simp] theorem trace_roster (n : N) (t : Tr) : (n.trace t).roster = n.roster := let h := trace_ht n t; h.1
@[simp] theorem emit_roster (n : N) (e : Ev) : (n.emit e).roster = n.roster := let h := emit_ht n e; h.1
@[simp] theorem tx_roster (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.roster = n.roster := let h := tx_ht e n p r fr; h.1
@[simp] theorem deltaTo_roster (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).roster = n.roster := let h := deltaTo_ht e n p m rc a; h.1
@[simp] theorem bump_roster (n : N) : n.bump.roster = n.roster := let h := bump_ht n; h.1
@[simp] theorem homeDelta_roster (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).roster = n.roster := let h := homeDelta_ht e n m rc a; h.1
@[simp] theorem ite_roster (c : Prop) [Decidable c] (a b : N) : (if c then a else b).roster = if c then a.roster else b.roster := by split <;> rfl
@[simp] theorem trace_susp (n : N) (t : Tr) : (n.trace t).susp = n.susp := let h := trace_ht n t; h.2.1
@[simp] theorem emit_susp (n : N) (e : Ev) : (n.emit e).susp = n.susp := let h := emit_ht n e; h.2.1
@[simp] theorem tx_susp (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.susp = n.susp := let h := tx_ht e n p r fr; h.2.1
@[simp] theorem deltaTo_susp (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).susp = n.susp := let h := deltaTo_ht e n p m rc a; h.2.1
@[simp] theorem bump_susp (n : N) : n.bump.susp = n.susp := let h := bump_ht n; h.2.1
@[simp] theorem homeDelta_susp (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).susp = n.susp := let h := homeDelta_ht e n m rc a; h.2.1
@[simp] theorem ite_susp (c : Prop) [Decidable c] (a b : N) : (if c then a else b).susp = if c then a.susp else b.susp := by split <;> rfl
@[simp] theorem trace_downed (n : N) (t : Tr) : (n.trace t).downed = n.downed := let h := trace_ht n t; h.2.2.1
@[simp] theorem emit_downed (n : N) (e : Ev) : (n.emit e).downed = n.downed := let h := emit_ht n e; h.2.2.1
@[simp] theorem tx_downed (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.downed = n.downed := let h := tx_ht e n p r fr; h.2.2.1
@[simp] theorem deltaTo_downed (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).downed = n.downed := let h := deltaTo_ht e n p m rc a; h.2.2.1
@[simp] theorem bump_downed (n : N) : n.bump.downed = n.downed := let h := bump_ht n; h.2.2.1
@[simp] theorem homeDelta_downed (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).downed = n.downed := let h := homeDelta_ht e n m rc a; h.2.2.1
@[simp] theorem ite_downed (c : Prop) [Decidable c] (a b : N) : (if c then a else b).downed = if c then a.downed else b.downed := by split <;> rfl
@[simp] theorem trace_revoked (n : N) (t : Tr) : (n.trace t).revoked = n.revoked := let h := trace_ht n t; h.2.2.2.1
@[simp] theorem emit_revoked (n : N) (e : Ev) : (n.emit e).revoked = n.revoked := let h := emit_ht n e; h.2.2.2.1
@[simp] theorem tx_revoked (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.revoked = n.revoked := let h := tx_ht e n p r fr; h.2.2.2.1
@[simp] theorem deltaTo_revoked (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).revoked = n.revoked := let h := deltaTo_ht e n p m rc a; h.2.2.2.1
@[simp] theorem bump_revoked (n : N) : n.bump.revoked = n.revoked := let h := bump_ht n; h.2.2.2.1
@[simp] theorem homeDelta_revoked (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).revoked = n.revoked := let h := homeDelta_ht e n m rc a; h.2.2.2.1
@[simp] theorem ite_revoked (c : Prop) [Decidable c] (a b : N) : (if c then a else b).revoked = if c then a.revoked else b.revoked := by split <;> rfl
@[simp] theorem trace_attached (n : N) (t : Tr) : (n.trace t).attached = n.attached := let h := trace_ht n t; h.2.2.2.2.1
@[simp] theorem emit_attached (n : N) (e : Ev) : (n.emit e).attached = n.attached := let h := emit_ht n e; h.2.2.2.2.1
@[simp] theorem tx_attached (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.attached = n.attached := let h := tx_ht e n p r fr; h.2.2.2.2.1
@[simp] theorem deltaTo_attached (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).attached = n.attached := let h := deltaTo_ht e n p m rc a; h.2.2.2.2.1
@[simp] theorem bump_attached (n : N) : n.bump.attached = n.attached := let h := bump_ht n; h.2.2.2.2.1
@[simp] theorem homeDelta_attached (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).attached = n.attached := let h := homeDelta_ht e n m rc a; h.2.2.2.2.1
@[simp] theorem ite_attached (c : Prop) [Decidable c] (a b : N) : (if c then a else b).attached = if c then a.attached else b.attached := by split <;> rfl
@[simp] theorem trace_homed (n : N) (t : Tr) : (n.trace t).homed = n.homed := let h := trace_ht n t; h.2.2.2.2.2.1
@[simp] theorem emit_homed (n : N) (e : Ev) : (n.emit e).homed = n.homed := let h := emit_ht n e; h.2.2.2.2.2.1
@[simp] theorem tx_homed (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.homed = n.homed := let h := tx_ht e n p r fr; h.2.2.2.2.2.1
@[simp] theorem deltaTo_homed (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).homed = n.homed := let h := deltaTo_ht e n p m rc a; h.2.2.2.2.2.1
@[simp] theorem bump_homed (n : N) : n.bump.homed = n.homed := let h := bump_ht n; h.2.2.2.2.2.1
@[simp] theorem homeDelta_homed (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).homed = n.homed := let h := homeDelta_ht e n m rc a; h.2.2.2.2.2.1
@[simp] theorem ite_homed (c : Prop) [Decidable c] (a b : N) : (if c then a else b).homed = if c then a.homed else b.homed := by split <;> rfl
@[simp] theorem trace_up (n : N) (t : Tr) : (n.trace t).up = n.up := let h := trace_ht n t; h.2.2.2.2.2.2.1
@[simp] theorem emit_up (n : N) (e : Ev) : (n.emit e).up = n.up := let h := emit_ht n e; h.2.2.2.2.2.2.1
@[simp] theorem tx_up (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.up = n.up := let h := tx_ht e n p r fr; h.2.2.2.2.2.2.1
@[simp] theorem deltaTo_up (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).up = n.up := let h := deltaTo_ht e n p m rc a; h.2.2.2.2.2.2.1
@[simp] theorem bump_up (n : N) : n.bump.up = n.up := let h := bump_ht n; h.2.2.2.2.2.2.1
@[simp] theorem homeDelta_up (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).up = n.up := let h := homeDelta_ht e n m rc a; h.2.2.2.2.2.2.1
@[simp] theorem ite_up (c : Prop) [Decidable c] (a b : N) : (if c then a else b).up = if c then a.up else b.up := by split <;> rfl
@[simp] theorem trace_heard (n : N) (t : Tr) : (n.trace t).heard = n.heard := let h := trace_ht n t; h.2.2.2.2.2.2.2.1
@[simp] theorem emit_heard (n : N) (e : Ev) : (n.emit e).heard = n.heard := let h := emit_ht n e; h.2.2.2.2.2.2.2.1
@[simp] theorem tx_heard (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.heard = n.heard := let h := tx_ht e n p r fr; h.2.2.2.2.2.2.2.1
@[simp] theorem deltaTo_heard (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).heard = n.heard := let h := deltaTo_ht e n p m rc a; h.2.2.2.2.2.2.2.1
@[simp] theorem bump_heard (n : N) : n.bump.heard = n.heard := let h := bump_ht n; h.2.2.2.2.2.2.2.1
@[simp] theorem homeDelta_heard (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).heard = n.heard := let h := homeDelta_ht e n m rc a; h.2.2.2.2.2.2.2.1
@[simp] theorem ite_heard (c : Prop) [Decidable c] (a b : N) : (if c then a else b).heard = if c then a.heard else b.heard := by split <;> rfl
@[simp] theorem trace_me (n : N) (t : Tr) : (n.trace t).me = n.me := let h := trace_ht n t; h.2.2.2.2.2.2.2.2.1
@[simp] theorem emit_me (n : N) (e : Ev) : (n.emit e).me = n.me := let h := emit_ht n e; h.2.2.2.2.2.2.2.2.1
@[simp] theorem tx_me (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.me = n.me := let h := tx_ht e n p r fr; h.2.2.2.2.2.2.2.2.1
@[simp] theorem deltaTo_me (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).me = n.me := let h := deltaTo_ht e n p m rc a; h.2.2.2.2.2.2.2.2.1
@[simp] theorem bump_me (n : N) : n.bump.me = n.me := let h := bump_ht n; h.2.2.2.2.2.2.2.2.1
@[simp] theorem homeDelta_me (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).me = n.me := let h := homeDelta_ht e n m rc a; h.2.2.2.2.2.2.2.2.1
@[simp] theorem ite_me (c : Prop) [Decidable c] (a b : N) : (if c then a else b).me = if c then a.me else b.me := by split <;> rfl
@[simp] theorem trace_boot (n : N) (t : Tr) : (n.trace t).boot = n.boot := let h := trace_ht n t; h.2.2.2.2.2.2.2.2.2.1
@[simp] theorem emit_boot (n : N) (e : Ev) : (n.emit e).boot = n.boot := let h := emit_ht n e; h.2.2.2.2.2.2.2.2.2.1
@[simp] theorem tx_boot (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.boot = n.boot := let h := tx_ht e n p r fr; h.2.2.2.2.2.2.2.2.2.1
@[simp] theorem deltaTo_boot (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).boot = n.boot := let h := deltaTo_ht e n p m rc a; h.2.2.2.2.2.2.2.2.2.1
@[simp] theorem bump_boot (n : N) : n.bump.boot = n.boot := let h := bump_ht n; h.2.2.2.2.2.2.2.2.2.1
@[simp] theorem homeDelta_boot (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).boot = n.boot := let h := homeDelta_ht e n m rc a; h.2.2.2.2.2.2.2.2.2.1
@[simp] theorem ite_boot (c : Prop) [Decidable c] (a b : N) : (if c then a else b).boot = if c then a.boot else b.boot := by split <;> rfl
@[simp] theorem trace_isHub (n : N) (t : Tr) : (n.trace t).isHub = n.isHub := let h := trace_ht n t; h.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem emit_isHub (n : N) (e : Ev) : (n.emit e).isHub = n.isHub := let h := emit_ht n e; h.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem tx_isHub (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.isHub = n.isHub := let h := tx_ht e n p r fr; h.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem deltaTo_isHub (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).isHub = n.isHub := let h := deltaTo_ht e n p m rc a; h.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem bump_isHub (n : N) : n.bump.isHub = n.isHub := let h := bump_ht n; h.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem homeDelta_isHub (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).isHub = n.isHub := let h := homeDelta_ht e n m rc a; h.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem ite_isHub (c : Prop) [Decidable c] (a b : N) : (if c then a else b).isHub = if c then a.isHub else b.isHub := by split <;> rfl
@[simp] theorem trace_outBc (n : N) (t : Tr) : (n.trace t).outBc = n.outBc := let h := trace_ht n t; h.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem emit_outBc (n : N) (e : Ev) : (n.emit e).outBc = n.outBc := let h := emit_ht n e; h.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem tx_outBc (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.outBc = n.outBc := let h := tx_ht e n p r fr; h.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem deltaTo_outBc (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).outBc = n.outBc := let h := deltaTo_ht e n p m rc a; h.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem bump_outBc (n : N) : n.bump.outBc = n.outBc := let h := bump_ht n; h.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem homeDelta_outBc (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).outBc = n.outBc := let h := homeDelta_ht e n m rc a; h.2.2.2.2.2.2.2.2.2.2.2.1
@[simp] theorem ite_outBc (c : Prop) [Decidable c] (a b : N) : (if c then a else b).outBc = if c then a.outBc else b.outBc := by split <;> rfl
@[simp] theorem trace_outClose (n : N) (t : Tr) : (n.trace t).outClose = n.outClose := let h := trace_ht n t; h.2.2.2.2.2.2.2.2.2.2.2.2
@[simp] theorem emit_outClose (n : N) (e : Ev) : (n.emit e).outClose = n.outClose := let h := emit_ht n e; h.2.2.2.2.2.2.2.2.2.2.2.2
@[simp] theorem tx_outClose (e : Env) (n : N) (p : Nat) (r : Route) (fr : NFrame) : (N.tx e n p r fr).1.outClose = n.outClose := let h := tx_ht e n p r fr; h.2.2.2.2.2.2.2.2.2.2.2.2
@[simp] theorem deltaTo_outClose (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).outClose = n.outClose := let h := deltaTo_ht e n p m rc a; h.2.2.2.2.2.2.2.2.2.2.2.2
@[simp] theorem bump_outClose (n : N) : n.bump.outClose = n.outClose := let h := bump_ht n; h.2.2.2.2.2.2.2.2.2.2.2.2
@[simp] theorem homeDelta_outClose (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta e n m rc a).outClose = n.outClose := let h := homeDelta_ht e n m rc a; h.2.2.2.2.2.2.2.2.2.2.2.2
@[simp] theorem ite_outClose (c : Prop) [Decidable c] (a b : N) : (if c then a else b).outClose = if c then a.outClose else b.outClose := by split <;> rfl
@[simp] theorem ite_fst {β : Type} (c : Prop) [Decidable c] (a b : N × β) : (if c then a else b).1 = if c then a.1 else b.1 := by split <;> rfl

theorem removeFromView_ht (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (ex : Bool) :
    (N.removeFromView e n now m cur src ex).1.HT n := by
  unfold N.removeFromView N.HT
  repeat' split
  all_goals simp

/-! ## `recompute_one` in small pieces -/

def N.rcOldVer (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : N :=
  match old with
  | some (ver, th) => if ver != best.ver then n.emit (.stack m best.ver) else n
  | none => n

def N.rcOldBoth (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : N :=
  match old with
  | some (ver, th) =>
    let n := if ver != best.ver then n.emit (.stack m best.ver) else n
    if th != best.th then n.emit (.addr m) else n
  | none => n

def N.rcVer (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : N × Bool :=
  if best.ver != c.rc.ver then
    (({ n with members := n.members.modify m (fun x => { x with rc := { x.rc with ver := best.ver } }) }).emit (.stack m best.ver), true)
  else (n, false)

def N.rcTh (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : N × Bool :=
  if best.th != c.rc.th then
    (({ n with members := n.members.modify m (fun x => { x with rc := { x.rc with th := best.th } }) }).emit (.addr m), true)
  else (n, false)

/-- A known member whose best record is of the same epoch and not older. -/
def N.rcSame (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : N × Bool × Bool :=
  let n := { n with members := n.members.modify m (fun x => { x with rc := { x.rc with inc := best.inc } }) }
  let (n, ch1) := n.rcVer m best c
  let (n, ch2) := n.rcTh m best c
  (n, ch1 || ch2, false)

/-- A known member whose best record is of another epoch, newer or older: the best copy's record replaces it. -/
def N.rcNewer (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : N × Bool × Bool :=
  let n := { n with members := n.members.insert m ⟨best⟩ }
  let n := n.emit (.joined m)
  let old := (some (c.rc.ver, c.rc.th)).orElse (fun _ => n.goneVer.get? m)
  let n := { n with goneVer := n.goneVer.erase m }
  let n := N.rcOldVer n m best old
  (n, true, false)

/-- A new member, if the table has room. -/
def N.rcFresh (n : N) (m : Nat) (best : Rec) : N × Bool × Bool :=
  if n.members.len ≥ MAX_TABLE then (n, false, true)
  else
    let n := { n with members := n.members.insert m ⟨best⟩ }
    let n := n.emit (.joined m)
    let old := n.goneVer.get? m
    let n := { n with goneVer := n.goneVer.erase m }
    let n := N.rcOldBoth n m best old
    (n, true, false)

/-- The arm of `recompute_one` for a known or a new member. -/
def N.rcArm (n : N) (m : Nat) (best : Rec) (cur : Option ViewEntry) : N × Bool × Bool :=
  match cur with
  | some c =>
    if best.inc / 65536 = c.rc.inc / 65536 then
      if best.inc / 65536 == c.rc.inc / 65536 && c.rc.inc ≤ best.inc then n.rcSame m best c
      else (n, false, false)
    else n.rcNewer m best c
  | none => n.rcFresh m best

def N.rcSusp (n : N) (_m : Nat) (_absent : Bool) (changed : Bool) : N × Bool :=
  (n, changed)

def N.rcAfter (e : Env) (n : N) (m : Nat) (best : Rec) (absent : Bool) (cur : Option ViewEntry) : N × Bool :=
  let n := if n.isHub && (match cur with | none => true | some c => decide (c.rc ≠ best)) then
      N.homeDelta e n m best .alive else n
  let (n, changed, early) := n.rcArm m best cur
  if early then (n, false) else n.rcSusp m absent changed

def N.recomputeOneS (e : Env) (n : N) (now m : Nat) : N × Bool :=
  let src := n.source now
  let (best, expired) := n.candidates now src m
  let cur := n.members.get? m
  match best with
  | none => N.removeFromView e n now m cur src expired
  | some (best, absent) => N.rcAfter e n m best absent cur

theorem recomputeOne_eq (e : Env) (n : N) (now m : Nat) : N.recomputeOne e n now m = N.recomputeOneS e n now m := by
  unfold N.recomputeOne N.recomputeOneS N.rcAfter N.rcArm N.rcSusp
  rfl

theorem rcOldVer_ht (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : (n.rcOldVer m best old).HT n := by
  unfold N.rcOldVer N.HT
  repeat' split
  all_goals simp

theorem rcOldBoth_ht (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : (n.rcOldBoth m best old).HT n := by
  unfold N.rcOldBoth N.HT
  repeat' split
  all_goals simp

theorem rcSusp_ht (n : N) (m : Nat) (a c : Bool) : (n.rcSusp m a c).1.HT n := by
  unfold N.rcSusp N.HT
  repeat' split
  all_goals simp

theorem members_ht (n : N) (f : AMap ViewEntry) : ({ n with members := f } : N).HT n := by unfold N.HT; simp
theorem goneVer_ht (n : N) (f : AMap (Nat × List Nat)) : ({ n with goneVer := f } : N).HT n := by unfold N.HT; simp

theorem rcVer_ht (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : (n.rcVer m best c).1.HT n := by
  unfold N.rcVer
  split
  · exact N.HT_trans (emit_ht _ _) (members_ht _ _)
  · exact N.HT_refl n

theorem rcTh_ht (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : (n.rcTh m best c).1.HT n := by
  unfold N.rcTh
  split
  · exact N.HT_trans (emit_ht _ _) (members_ht _ _)
  · exact N.HT_refl n

theorem rcSame_ht (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : (n.rcSame m best c).1.HT n := by
  unfold N.rcSame
  dsimp only
  generalize hn : ({ n with members := n.members.modify m (fun x => { x with rc := { x.rc with inc := best.inc } }) } : N) = n1
  have h1 : n1.HT n := hn ▸ members_ht _ _
  have h2 := rcVer_ht n1 m best c
  have h3 := rcTh_ht (n1.rcVer m best c).1 m best c
  exact N.HT_trans h3 (N.HT_trans h2 h1)

theorem rcNewer_ht (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : (n.rcNewer m best c).1.HT n := by
  unfold N.rcNewer
  dsimp only
  exact N.HT_trans (rcOldVer_ht _ _ _ _)
    (N.HT_trans (goneVer_ht _ _) (N.HT_trans (emit_ht _ _) (members_ht _ _)))

theorem rcFresh_ht (n : N) (m : Nat) (best : Rec) : (n.rcFresh m best).1.HT n := by
  unfold N.rcFresh
  split
  · exact N.HT_refl n
  · dsimp only
    exact N.HT_trans (rcOldBoth_ht _ _ _ _)
      (N.HT_trans (goneVer_ht _ _) (N.HT_trans (emit_ht _ _) (members_ht _ _)))

theorem rcArm_ht (n : N) (m : Nat) (best : Rec) (cur : Option ViewEntry) : (n.rcArm m best cur).1.HT n := by
  unfold N.rcArm
  cases cur with
  | none => exact rcFresh_ht n m best
  | some c =>
    dsimp only
    split
    · split
      · exact rcSame_ht n m best c
      · exact N.HT_refl n
    · exact rcNewer_ht n m best c

theorem rcAfter_ht (e : Env) (n : N) (m : Nat) (best : Rec) (absent : Bool) (cur : Option ViewEntry) :
    (N.rcAfter e n m best absent cur).1.HT n := by
  unfold N.rcAfter
  dsimp only
  generalize hn : (if n.isHub && (match cur with | none => true | some c => decide (c.rc ≠ best)) then N.homeDelta e n m best .alive else n) = n1
  have h1 : n1.HT n := hn ▸ (ite_ht _ _ _ _ (homeDelta_ht ..) (N.HT_refl n))
  have h2 := rcArm_ht n1 m best cur
  generalize hr : n1.rcArm m best cur = r
  obtain ⟨n2, ch, early⟩ := r
  rw [hr] at h2
  split
  · exact N.HT_trans h2 h1
  · exact N.HT_trans (N.HT_trans (rcSusp_ht n2 m absent ch) h2) h1

theorem recomputeOne_ht (e : Env) (n : N) (now m : Nat) : (N.recomputeOne e n now m).1.HT n := by
  rw [recomputeOne_eq]
  unfold N.recomputeOneS
  dsimp only
  split
  · exact removeFromView_ht ..
  · exact rcAfter_ht ..

/-! ## `apply_delta` and `push_delta` -/

def N.adEnsure (n : N) (hub : Nat) : N × Bool :=
  if !n.hv.has hub then
    if MAX_HUBS ≤ n.hv.len then (n, false)
    else ({ n with hv := n.hv.insert hub ⟨[], 0, false⟩ }, true)
  else (n, true)

def N.adDown (n : N) (hub m : Nat) (rc : Rec) (a : Alive) (c : HubCopy) : N :=
  match c.entries.get? m with
  | some x =>
    if x.rc.inc / 65536 ≤ rc.inc / 65536 then
      let n := { n with hv := n.hv.insert hub { c with entries := c.entries.erase m } }
      if a == .left && n.left.len < MAX_TABLE then { n with left := n.left.ins m } else n
    else n
  | none => n

def N.adEntries (n : N) (hub m : Nat) (rc : Rec) (a : Alive) : N :=
  match n.hv.get? hub with
  | none => n
  | some c =>
    match a with
    | .alive =>
      if c.entries.len < MAX_TABLE || c.entries.has m then
        { n with hv := n.hv.insert hub { c with entries := c.entries.insert m ⟨rc, c.round, none⟩ }, left := n.left.del m }
      else n
    | .down | .left => n.adDown hub m rc a c

def N.applyDeltaCoreS (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) : N :=
  if n.revoked.has m then n
  else
    let (n, ok) := n.adEnsure hub
    if !ok then n
    else
      let n := n.adEntries hub m rc a
      let (n, ch) := N.recomputeOne e n now m
      if ch then n.bump else n

theorem applyDeltaCore_eq (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    N.applyDeltaCore e n now hub m rc a = N.applyDeltaCoreS e n now hub m rc a := by
  unfold N.applyDeltaCore N.applyDeltaCoreS N.adEnsure N.adEntries N.adDown
  rfl

theorem hv_ht (n : N) (f : AMap HubCopy) : ({ n with hv := f } : N).HT n := by unfold N.HT; simp
theorem hvleft_ht (n : N) (f : AMap HubCopy) (l : ASet) : ({ n with hv := f, left := l } : N).HT n := by unfold N.HT; simp
theorem left_ht (n : N) (l : ASet) : ({ n with left := l } : N).HT n := by unfold N.HT; simp

theorem adEnsure_ht (n : N) (hub : Nat) : (n.adEnsure hub).1.HT n := by
  unfold N.adEnsure
  split
  · split
    · exact N.HT_refl n
    · exact hv_ht _ _
  · exact N.HT_refl n

theorem adDown_ht (n : N) (hub m : Nat) (rc : Rec) (a : Alive) (c : HubCopy) : (n.adDown hub m rc a c).HT n := by
  unfold N.adDown
  split
  · split
    · dsimp only
      split
      · unfold N.HT; simp
      · exact hv_ht _ _
    · exact N.HT_refl n
  · exact N.HT_refl n

theorem adEntries_ht (n : N) (hub m : Nat) (rc : Rec) (a : Alive) : (n.adEntries hub m rc a).HT n := by
  unfold N.adEntries
  split
  · exact N.HT_refl n
  · split
    · split
      · exact hvleft_ht _ _ _
      · exact N.HT_refl n
    · exact adDown_ht ..
    · exact adDown_ht ..

theorem applyDeltaCore_ht (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    (N.applyDeltaCore e n now hub m rc a).HT n := by
  rw [applyDeltaCore_eq]
  unfold N.applyDeltaCoreS
  split
  · exact N.HT_refl n
  · dsimp only
    generalize hE : n.adEnsure hub = r
    obtain ⟨n1, ok⟩ := r
    have h1 : n1.HT n := by have := adEnsure_ht n hub; rw [hE] at this; exact this
    split
    · exact h1
    · generalize hR : N.recomputeOne e (n1.adEntries hub m rc a) now m = r2
      obtain ⟨n2, ch⟩ := r2
      have h2 : n2.HT n1 := N.HT_trans (by have := recomputeOne_ht e (n1.adEntries hub m rc a) now m; rw [hR] at this; exact this) (adEntries_ht ..)
      dsimp only
      split
      · exact N.HT_trans (bump_ht _) (N.HT_trans h2 h1)
      · exact N.HT_trans h2 h1

theorem pushDelta_ht (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) : (N.pushDelta e n now m rc a).HT n := by
  unfold N.pushDelta
  dsimp only
  have h1 : (forKeys n.attached.keys
      (fun p n => if p != m && (n.isBoot p || (m == n.me && n.homed.has p)) then N.deltaTo e n p m rc a else n) n).HT n :=
    forKeys_ht _ _ (fun k n => by split; exact deltaTo_ht ..; exact N.HT_refl n) n
  split
  · exact h1
  · exact N.HT_trans (applyDeltaCore_ht ..) h1

end Pinc.Membership
