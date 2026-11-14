import Vinc.MembershipInvStep
import Vinc.MembershipModelNode

/-!
# Property 9, part 3: the view steps keep `Inv`

`remove_from_view`, `recompute_one`, `apply_delta` (the core and the self entry), `push_delta`, `mark_absent`, `mark_view_absent`,
`apply_snap`, `sweep_absent`, `renew` and `reselect`: every insert into a table is behind the guard the code tests,
and every other update erases or rewrites an entry.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

variable {B : List Nat}

macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_trace)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_emit)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_bc)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_close)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_bump)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_beginQuiet)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_homeDelta)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_deltaTo)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_tx)

theorem inv_removeFromView {e : Env} {n : N} (hx : Inv B n) (now m : Nat) (cur : Option ViewEntry) (src : Source)
    (ex : Bool) : Inv B (N.removeFromView e n now m cur src ex).1 := by
  unfold N.removeFromView
  inv_go

set_option hygiene false in
macro_rules | `(tactic| inv_apply) => `(tactic| refine inv_forKeys (fun k n hx => ?_) ?_)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_removeFromView)

theorem inv_bumpRecord {n : N} (hx : Inv B n) : Inv B n.bumpRecord := by
  unfold N.bumpRecord
  inv_go

theorem ite_homeDelta_members (c : Prop) [Decidable c] (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) :
    (if c then N.homeDelta e n m rc a else n).members = n.members := by
  by_cases h : c
  · rw [if_pos h]; exact homeDelta_members_inv ..
  · rw [if_neg h]

theorem inv_recomputeOne {e : Env} {n : N} (hx : Inv B n) (now m : Nat) : Inv B (N.recomputeOne e n now m).1 := by
  unfold N.recomputeOne
  inv_go
  have hm : x.members = n.members := by
    rw [hxe]; exact ite_homeDelta_members ..
  have hg : x.members.has m = true := by rw [hm]; exact AMap.has_of_get? _ _ _ ‹n.members.get? m = some _›
  inv_leaf

macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_bumpRecord)
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_recomputeOne)

theorem inv_refreshLocal {e : Env} {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.refreshLocal e n now) := by
  unfold N.refreshLocal
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_refreshLocal)

theorem inv_helloTo {e : Env} {n : N} (hx : Inv B n) (peer : Nat) (snap : Bool) : Inv B (N.helloTo e n peer snap) := by
  unfold N.helloTo
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_helloTo)

theorem inv_applyDeltaCore {e : Env} {n : N} (hx : Inv B n) (now hub m : Nat) (rc : Rec) (a : Alive) :
    Inv B (N.applyDeltaCore e n now hub m rc a) := by
  unfold N.applyDeltaCore
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_applyDeltaCore)

theorem inv_pushDelta {e : Env} {n : N} (hx : Inv B n) (now m : Nat) (rc : Rec) (a : Alive) :
    Inv B (N.pushDelta e n now m rc a) := by
  unfold N.pushDelta
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_pushDelta)

theorem inv_renew {e : Env} {n : N} (hx : Inv B n) (now : Nat) (forceSnap periodic : Bool) : Inv B (N.renew e n now forceSnap periodic) := by
  unfold N.renew
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_renew)

theorem inv_onSelfEntry {e : Env} {n : N} (hx : Inv B n) (now hub : Nat) (rc : Rec) (a : Alive) : Inv B (N.onSelfEntry e n now hub rc a) := by
  unfold N.onSelfEntry
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_onSelfEntry)

theorem inv_applyDelta {e : Env} {n : N} (hx : Inv B n) (now hub m : Nat) (rc : Rec) (a : Alive) : Inv B (N.applyDelta e n now hub m rc a) := by
  unfold N.applyDelta
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_applyDelta)

theorem inv_applyDown {e : Env} {n : N} (hx : Inv B n) (now hub member inc : Nat) : Inv B (N.applyDown e n now hub member inc) := by
  unfold N.applyDown
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_applyDown)

theorem inv_dropGone {n : N} (hx : Inv B n) (hub round : Nat) : Inv B (n.dropGone hub round) := by
  unfold N.dropGone
  split
  · rename_i c hc
    inv_keep hx
    exact hx.hv.insert hub _ ((hx.hv.entries hub c hc).filter _) (Or.inr (AMap.has_of_get? _ _ _ hc))
  · exact hx
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_dropGone)

theorem inv_markAbsent {e : Env} {n : N} (hx : Inv B n) (now hub round : Nat) : Inv B (N.markAbsent e n now hub round).1 := by
  unfold N.markAbsent
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_markAbsent)

theorem inv_markViewAbsent {e : Env} {n : N} (hx : Inv B n) (now hub round : Nat) :
    Inv B (N.markViewAbsent e n now hub round).1 := by
  unfold N.markViewAbsent
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_markViewAbsent)

theorem inv_snapAbsent {e : Env} {n : N} (hx : Inv B n) (now hub round : Nat) : Inv B (N.snapAbsent e n now hub round).1 := by
  unfold N.snapAbsent
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_snapAbsent)

theorem inv_applySnap {e : Env} {n : N} (hx : Inv B n) (now hub : Nat) (partial_ more : Bool) (es : List (Nat × Rec)) : Inv B (N.applySnap e n now hub partial_ more es) := by
  unfold N.applySnap
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_applySnap)

theorem inv_sweepAbsent {e : Env} {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.sweepAbsent e n now) := by
  unfold N.sweepAbsent
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_sweepAbsent)

theorem inv_rttSample {n : N} (hx : Inv B n) (hub r : Nat) (hh : hub ∈ B) : Inv B (N.rttSample n hub r) := by
  unfold N.rttSample
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_rttSample)

theorem inv_reselect {e : Env} {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.reselect e n now) := by
  unfold N.reselect
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_reselect)

theorem inv_recheckNow {e : Env} {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.recheckNow e n now) := by
  unfold N.recheckNow
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_recheckNow)

end Vinc.Membership
