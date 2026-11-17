import Vinc.MembershipInvView
import Vinc.MembershipModelHub

/-!
# Property 9, part 4: the hub roster steps keep `Inv`

`send_snapshot`, `send_floor`, `on_hello`, `hub_down`, `on_down`, `carrier_return`, `schedule_confirm`, `confirm`,
`N.newSusp` (the model's cut of `carrier_watch`), `carrier_watch`, `carrier_gone` and `hub_tick`: every insert into `roster`, `attached`, `homed`, `downed`,
`susp` is behind the guard the code tests (`MAX_TABLE`), so a full table refuses instead of growing.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

variable {B : List Nat}

theorem inv_sendSnapshot {e : Env} {n : N} (hx : Inv B n) (now peer : Nat) : Inv B (N.sendSnapshot e n now peer) := by
  unfold N.sendSnapshot
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_sendSnapshot)

theorem inv_sendFloor {e : Env} {n : N} (hx : Inv B n) (peer : Nat) : Inv B (N.sendFloor e n peer) := by
  unfold N.sendFloor
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_sendFloor)

theorem inv_onHello {e : Env} {n : N} (hx : Inv B n) (now peer : Nat) (rc : Rec) (snap homed : Bool) : Inv B (N.onHello e n now peer rc snap homed) := by
  unfold N.onHello
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_onHello)

theorem inv_hubDown {e : Env} {n : N} (hx : Inv B n) (now member : Nat) (cause : Cause) : Inv B (N.hubDown e n now member cause) := by
  unfold N.hubDown
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_hubDown)

theorem inv_onDown {e : Env} {n : N} (hx : Inv B n) (now m inc : Nat) (pf : Proof) : Inv B (N.onDown e n now m inc pf) := by
  unfold N.onDown
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_onDown)

theorem inv_onLeft {e : Env} {n : N} (hx : Inv B n) (now m : Nat) (rc : Rec) : Inv B (N.onLeft e n now m rc) := by
  unfold N.onLeft
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_onLeft)

theorem inv_carrierReturn {e : Env} {n : N} (hx : Inv B n) (now member : Nat) : Inv B (N.carrierReturn e n now member) := by
  unfold N.carrierReturn
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_carrierReturn)

theorem inv_scheduleConfirm {n : N} (hx : Inv B n) (now at_ : Nat) : Inv B (N.scheduleConfirm n now at_) := by
  unfold N.scheduleConfirm
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_scheduleConfirm)

theorem inv_confirm {e : Env} {n : N} (hx : Inv B n) (now m : Nat) (sp : Susp) (l : Lease) : Inv B (N.confirm e n now m sp l) := by
  unfold N.confirm
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_confirm)

theorem inv_newSusp {e : Env} {n0 : N} (hx : Inv B n0) (now m since : Nat) (ev : Option Evid) : Inv B (N.newSusp e n0 now m since ev) := by
  unfold N.newSusp
  inv_go
  all_goals
    have hs : n.susp = n0.susp := by
      subst_vars
      split at hXe <;> (simp only [Prod.mk.injEq] at hXe; obtain ⟨h1, -⟩ := hXe; subst h1; simp)
    inv_leaf
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_newSusp)

theorem rewatch_has {n : N} (now m : Nat) (sp : Susp) (h : n.susp.get? m = some sp) :
    (N.rewatch n now sp).susp.has m = true := by
  rw [rewatch_susp]; exact AMap.has_of_get? _ _ _ h

theorem inv_rewatch {n : N} (hx : Inv B n) (now : Nat) (sp : Susp) : Inv B (N.rewatch n now sp) := by
  unfold N.rewatch
  split
  · exact inv_scheduleConfirm hx _ _
  · exact hx
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_rewatch)

theorem inv_carrierWatch {e : Env} {n : N} (hx : Inv B n) (now m : Nat) : Inv B (N.carrierWatch e n now m) := by
  unfold N.carrierWatch
  inv_go
  all_goals
    have hg : x.susp.has m = true := by
      subst_vars; simpa using rewatch_has now m _ ‹n.susp.get? m = some _›
    inv_leaf
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_carrierWatch)

theorem inv_carrierGone {e : Env} {n : N} (hx : Inv B n) (now member : Nat) : Inv B (N.carrierGone e n now member) := by
  unfold N.carrierGone
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_carrierGone)

theorem inv_hubTick {e : Env} {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.hubTick e n now) := by
  unfold N.hubTick
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_hubTick)

end Vinc.Membership
