import Vinc.MembershipSuspAll

/-!
# `SuspOk` holds in every reachable state (property 3, hub side)

`SuspReach n`: `n` is the state of a node after any sequence of calls into the machine, from `start`. Every call keeps the
suspension table well formed (`MembershipSuspAll.lean`), so a record whose second probe is recorded sent it on the
direct path or through another hub (`SuspOk`). Hence `carrierWatch_keeps_unless`, which assumed `SuspOk`, holds without
that assumption in every reachable state (`carrierWatch_keeps_unless_reach`): a member leaves the roster in
`carrier_watch` only under the confirmation rule of the design (`ConfirmCond`).
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

/-- The states a node can be in: after `start`, then any calls. -/
inductive SuspReach : N → Prop
  | start {e : Env} {me : Nat} {isHub : Bool} {hubs : List Nat} {tr : Bool} {now wall floor : Nat} {n : N} :
      N.start e me isHub hubs tr now wall floor = .ok n → SuspReach n
  | onTimeout {n : N} (e : Env) (now : Nat) : SuspReach n → SuspReach (N.onTimeout e n now)
  | onFrame {n : N} (e : Env) (now peer : Nat) (f : NFrame) : SuspReach n → SuspReach (N.onFrame e n now peer f)
  | onBytes {n : N} (e : Env) (now peer : Nat) (fs : List NFrame) (bad : Bool) :
      SuspReach n → SuspReach (N.onBytes e n now peer fs bad)
  | sessionUp {n : N} (e : Env) (now peer : Nat) (incoming : Bool) : SuspReach n → SuspReach (N.sessionUp e n now peer incoming)
  | sessionDown {n : N} (e : Env) (now peer code : Nat) : SuspReach n → SuspReach (N.sessionDown e n now peer code)
  | carrierGone {n : N} (e : Env) (now member : Nat) : SuspReach n → SuspReach (N.carrierGone e n now member)
  | carrierReturn {n : N} (e : Env) (now member : Nat) : SuspReach n → SuspReach (N.carrierReturn e n now member)
  | leave {n : N} : SuspReach n → SuspReach n.leave
  | revoke {n n' : N} (e : Env) (now member : Nat) : SuspReach n → N.revoke e n now member = some n' → SuspReach n'
  | addressChanged {n : N} (now : Nat) : SuspReach n → SuspReach (n.addressChanged now)
  | clearOut {n : N} : SuspReach n → SuspReach n.clearOut
  | drained {n : N} : SuspReach n → SuspReach n.drained

theorem SuspReach.suspOk {n : N} (h : SuspReach n) : n.SuspOk := by
  induction h with
  | start hs => exact start_so _ _ _ _ _ _ _ _ _ hs
  | onTimeout e now _ ih => exact onTimeout_so e _ now ih
  | onFrame e now peer f _ ih => exact onFrame_so e _ now peer f ih
  | onBytes e now peer fs bad _ ih => exact onBytes_so e _ now peer fs bad ih
  | sessionUp e now peer inc _ ih => exact SuspOk.of_eq (sessionUp_susp e _ now peer inc) ih
  | sessionDown e now peer code _ ih => exact sessionDown_so e _ now peer code ih
  | carrierGone e now member _ ih => exact carrierGone_so e _ now member ih
  | carrierReturn e now member _ ih => exact carrierReturn_so e _ now member ih
  | leave _ ih => exact SuspOk.of_eq (leave_susp _) ih
  | revoke e now member _ hr ih => exact revoke_so e _ _ now member hr ih
  | addressChanged now _ ih => exact SuspOk.of_eq (addressChanged_susp _ now) ih
  | clearOut _ ih => exact SuspOk.of_eq rfl ih
  | drained _ ih => exact SuspOk.of_eq rfl ih

/-- `carrierWatch_keeps_unless` without its assumption: in every reachable state, `carrier_watch` removes a member from the
roster only under the confirmation rule (`ConfirmCond`): the carrier is gone since `since`, nothing excuses the drop, a
suspension for this very drop exists whose second probe went on the direct path or through another hub, and every
deadline (drop + `CONFIRM`, each probe + its wait) has passed. -/
theorem carrierWatch_keeps_unless_reach (e : Env) (n : N) (now m : Nat) (l : Lease) (hr : SuspReach n)
    (hl : n.roster.get? m = some l) :
    (N.carrierWatch e n now m).roster.has m = true ∨ ConfirmCond e n now m l :=
  carrierWatch_keeps_unless e n now m l hr.suspOk hl

end Vinc.Membership
