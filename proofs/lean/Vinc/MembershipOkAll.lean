import Vinc.MembershipInvReach
import Vinc.MembershipOkDelta
import Vinc.MembershipOkView

/-!
# The view never lists the node itself or a revoked node: every call of the machine

`VOK` (`MembershipOkTac.lean`) holds for the node `start` returns and is kept by every public call, so it holds for
every reachable node (`reach_vok`): no hub copy and no view entry names the node itself or a revoked node. The inserts
into the copies are `apply_delta` (which tests `revoked` and, for the node itself, takes `on_self_entry`) and
`apply_snap` (the same two tests); the inserts into the view are `recompute_one`'s, which lists only what a copy lists
(`MembershipOkView.lean`); `revoke` adds to `revoked` and erases the member from every copy and from the view.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 400000

namespace Vinc.Membership
open Vinc.MemInc

/-- As `vk_go`, with a leaf closed by plain `rfl` (the update leaves the four fields alone). -/
macro "vk_go2" : tactic =>
  `(tactic| (repeat' (first | with_reducible assumption | rw [prod_fst_mk'] | vk_let | (with_reducible vk_apply) | split | refine vk_foldl _ (fun n a hx => ?_) _ ?_ | refine vk_foldl2 _ (fun a x hx => ?_) _ ?_ | (refine vk_of ?_ rfl rfl rfl rfl; assumption))))

theorem vk_sendSnapshot {e : Env} {n : N} (hx : VOK n) (now peer : Nat) : VOK (N.sendSnapshot e n now peer) := by
  unfold N.sendSnapshot
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_sendSnapshot)

theorem vk_sendFloor {e : Env} {n : N} (hx : VOK n) (peer : Nat) : VOK (N.sendFloor e n peer) := by
  unfold N.sendFloor
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_sendFloor)

theorem vk_bumpRecord {n : N} (hx : VOK n) : VOK n.bumpRecord := by
  unfold N.bumpRecord
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_bumpRecord)

theorem vk_refreshLocal {e : Env} {n : N} (hx : VOK n) (now : Nat) : VOK (N.refreshLocal e n now) := by
  unfold N.refreshLocal
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_refreshLocal)

theorem vk_helloTo {e : Env} {n : N} (hx : VOK n) (peer : Nat) (snap : Bool) : VOK (N.helloTo e n peer snap) := by
  unfold N.helloTo
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_helloTo)

theorem vk_renew {e : Env} {n : N} (hx : VOK n) (now : Nat) (fs p : Bool) : VOK (N.renew e n now fs p) := by
  unfold N.renew
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_renew)

theorem vk_onSelfEntry {e : Env} {n : N} (hx : VOK n) (now hub : Nat) (rc : Rec) (a : Alive) :
    VOK (N.onSelfEntry e n now hub rc a) := by
  unfold N.onSelfEntry
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_onSelfEntry)

theorem vk_applyDelta {e : Env} {n : N} (hx : VOK n) (now hub m : Nat) (rc : Rec) (a : Alive) :
    VOK (N.applyDelta e n now hub m rc a) := by
  unfold N.applyDelta
  split
  · exact vk_onSelfEntry hx _ _ _ _
  · rename_i h
    exact vk_applyDeltaCore hx _ _ _ _ _ (by simpa using h)
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_applyDelta)

theorem vk_applyDown {e : Env} {n : N} (hx : VOK n) (now hub member inc : Nat) : VOK (N.applyDown e n now hub member inc) := by
  unfold N.applyDown
  exact vk_applyDelta hx _ _ _ _ _
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_applyDown)

theorem vk_rttSample {n : N} (hx : VOK n) (hub r : Nat) : VOK (N.rttSample n hub r) := by
  unfold N.rttSample
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_rttSample)

theorem vk_reselect {e : Env} {n : N} (hx : VOK n) (now : Nat) : VOK (N.reselect e n now) := by
  unfold N.reselect
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_reselect)

theorem vk_recheckNow {e : Env} {n : N} (hx : VOK n) (now : Nat) : VOK (N.recheckNow e n now) := by
  unfold N.recheckNow
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_recheckNow)

theorem vk_onHello {e : Env} {n : N} (hx : VOK n) (now peer : Nat) (rc : Rec) (snap homed : Bool) :
    VOK (N.onHello e n now peer rc snap homed) := by
  unfold N.onHello
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_onHello)

theorem vk_hubDown {e : Env} {n : N} (hx : VOK n) (now member : Nat) (cause : Cause) : VOK (N.hubDown e n now member cause) := by
  unfold N.hubDown
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_hubDown)

theorem vk_onDown {e : Env} {n : N} (hx : VOK n) (now m inc : Nat) (pf : Proof) : VOK (N.onDown e n now m inc pf) := by
  unfold N.onDown
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_onDown)

theorem vk_carrierReturn {e : Env} {n : N} (hx : VOK n) (now member : Nat) : VOK (N.carrierReturn e n now member) := by
  unfold N.carrierReturn
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_carrierReturn)

theorem vk_scheduleConfirm {n : N} (hx : VOK n) (now at_ : Nat) : VOK (N.scheduleConfirm n now at_) := by
  unfold N.scheduleConfirm
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_scheduleConfirm)

theorem vk_confirm {e : Env} {n : N} (hx : VOK n) (now m : Nat) (sp : Susp) (l : Lease) : VOK (N.confirm e n now m sp l) := by
  unfold N.confirm
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_confirm)

theorem vk_newSusp {e : Env} {n : N} (hx : VOK n) (now m since : Nat) (ev : Option Evid) : VOK (N.newSusp e n now m since ev) := by
  unfold N.newSusp
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_newSusp)

theorem vk_carrierWatch {e : Env} {n : N} (hx : VOK n) (now m : Nat) : VOK (N.carrierWatch e n now m) := by
  unfold N.carrierWatch
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_carrierWatch)

theorem vk_carrierGone {e : Env} {n : N} (hx : VOK n) (now member : Nat) : VOK (N.carrierGone e n now member) := by
  unfold N.carrierGone
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_carrierGone)

theorem vk_hubTick {e : Env} {n : N} (hx : VOK n) (now : Nat) : VOK (N.hubTick e n now) := by
  unfold N.hubTick
  vk_go2
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_hubTick)

end Vinc.Membership
