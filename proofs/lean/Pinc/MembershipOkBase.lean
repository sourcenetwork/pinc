import Pinc.MembershipOkTac

/-!
# The view never lists the node itself or a revoked node: the helpers and `recompute_one`

`VOK` (`MembershipOkTac.lean`) is kept by the helpers every step is built from (trace, emit, send, broadcast, close, the
cursor loop, home delta) because they touch none of the hub copies, the view, the revocation set and the node's id
(`vk_of`). `recompute_one` is the one place that inserts into the view: `vk_recomputeOne` shows it inserts a member only
when some hub copy lists it (`candidates_listed`), and the copies only list nodes other than this one and not revoked.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Pinc.Membership
open Pinc.MemInc

theorem vk_trace {n : N} (h : VOK n) (t : Tr) : VOK (n.trace t) :=
  vk_of h (trace_hv n t) (trace_members n t) (trace_revoked_v n t) (trace_me_v n t)

theorem vk_emit {n : N} (h : VOK n) (e : Ev) : VOK (n.emit e) :=
  vk_of h (emit_hv n e) (emit_members n e) (emit_revoked_v n e) (emit_me_v n e)

theorem vk_bc {n : N} (h : VOK n) (b : Bc) : VOK (n.bc b) := vk_of h rfl rfl rfl rfl
theorem vk_close {n : N} (h : VOK n) (p : Nat) (r : CloseR) : VOK (n.close p r) := vk_of h rfl rfl rfl rfl

theorem vk_tx {e : Env} {n : N} (h : VOK n) (p : Nat) (r : Route) (f : NFrame) : VOK (N.tx e n p r f).1 :=
  vk_of h (OutOnly.hv (tx_out e n p r f)) (OutOnly.members (tx_out e n p r f)) (OutOnly.revoked (tx_out e n p r f))
    (OutOnly.me (tx_out e n p r f))

theorem vk_deltaTo {e : Env} {n : N} (h : VOK n) (p m : Nat) (rc : Rec) (a : Alive) : VOK (N.deltaTo e n p m rc a) :=
  vk_tx h _ _ _

theorem vk_beginQuiet {n : N} (h : VOK n) (now cause : Nat) : VOK (n.beginQuiet now cause) := by
  unfold N.beginQuiet
  refine vk_trace (vk_of h ?_ ?_ ?_ ?_) _ <;> rfl

theorem vk_bump {n : N} (h : VOK n) : VOK n.bump := by
  unfold N.bump
  dsimp only
  refine vk_emit (vk_of h ?_ ?_ ?_ ?_) _ <;> rfl

theorem vk_homeDelta {e : Env} {n : N} (h : VOK n) (m : Nat) (rc : Rec) (a : Alive) : VOK (N.homeDelta e n m rc a) :=
  vk_of h (OutOnly.hv (homeDelta_out e n m rc a)) (OutOnly.members (homeDelta_out e n m rc a))
    (OutOnly.revoked (homeDelta_out e n m rc a)) (OutOnly.me (homeDelta_out e n m rc a))

macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_trace)
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_emit)
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_bc)
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_close)
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_bump)
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_beginQuiet)
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_homeDelta)
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_deltaTo)
macro_rules | `(tactic| vk_apply) => `(tactic| apply vk_tx)

end Pinc.Membership
