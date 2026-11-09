import Vinc.MembershipInvReach
import Vinc.MembershipSuspAll
import Vinc.MembershipFlap

/-!
# The behaviours the node composition relies on

`Session::give_up` as the heal bound, `Membership::set_max_frame`, `Frame::read_with`, `hub_is_up`, `in_view`,
`snapshot_to`, the `Option` tables `hello_at` and `hsent` whose cleared entries stay, and a leaving node whose `hello_to` does nothing. The model is the code (`MembershipModel*.lean`); these theorems state what the code does in each case.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership

/-- A peer the host does not list has the default give-up bound `HEAL_SILENCE`. -/
theorem giveUp_default (e : Env) (p : Nat) (h : e.gu.get? p = none) : e.giveUp p = HEAL_SILENCE := by
  unfold Env.giveUp; simp [h]

/-- A peer the host lists has the bound the host gives. -/
theorem giveUp_listed (e : Env) (p g : Nat) (h : e.gu.get? p = some g) : e.giveUp p = g := by
  unfold Env.giveUp; simp [h]

/-- **A heal is silence past the transport's bound.** A member that hears a hub again after longer than the host's
give-up bound for it opens the quiet window, whatever the bound is. -/
theorem ofHub1_heal (e : Env) (n : N) (now peer t : Nat) (hm : n.isHub = false) (hh : n.heard.get? peer = some t)
    (hs : e.giveUp peer < now - t) : (N.ofHub1 e n now peer).quietUntil = satAdd now QUIET := by
  unfold N.ofHub1
  simp only [hh, hs, hm, decide_true, Bool.not_false, Bool.true_and, if_true]
  exact (beginQuiet_window _ _ _).1

/-- A hub never opens a quiet window on silence (`give_up` is for members only). -/
theorem ofHub1_hub_keeps (e : Env) (n : N) (now peer : Nat) (hm : n.isHub = true) :
    (N.ofHub1 e n now peer).quietUntil = n.quietUntil := by
  unfold N.ofHub1
  simp [hm]

/-- The frame limit never goes below the default. -/
theorem setMaxFrame_ge (n : N) (mb : Nat) : Vinc.MemCodec.maxBody ≤ (N.setMaxFrame n mb).maxFrame := by
  unfold N.setMaxFrame; exact Nat.le_max_right _ _

/-- A request above the default is taken as it is. -/
theorem setMaxFrame_raise (n : N) (mb : Nat) (h : Vinc.MemCodec.maxBody ≤ mb) : (N.setMaxFrame n mb).maxFrame = mb := by
  unfold N.setMaxFrame; simp [Nat.max_eq_left h]

/-- `hub_is_up` is the model's `hubUp`: this node, or a session that heard a frame within `HUB_STALE`. -/
theorem hubIsUp_iff (n : N) (now x : Nat) :
    n.hubUp now x = true ↔ (x = n.me ∨ (n.up.has x = true ∧ ∃ t, n.heard.get? x = some t ∧ now - t < HUB_STALE)) := by
  unfold N.hubUp
  cases h : n.heard.get? x <;> simp [h] <;> omega

/-- `in_view` answers whether the view holds an entry for the member. -/
theorem inView_iff (n : N) (m : Nat) : n.members.has m = true ↔ ∃ x, n.members.get? m = some x := by
  rw [AMap.has_iff_get]
  cases n.members.get? m <;> simp

/-- `hello_to` of a node that left sends nothing and changes nothing. -/
theorem helloTo_leaving (e : Env) (n : N) (peer : Nat) (snap : Bool) (h : n.leaving = true) :
    N.helloTo e n peer snap = n := by
  unfold N.helloTo; simp [h]

/-- `snapshot_to` of a member node, or of a peer that is not attached, does nothing. -/
theorem snapshotTo_unattached (e : Env) (n : N) (now peer : Nat) (h : n.isHub = false ∨ n.attached.has peer = false) :
    N.snapshotTo e n now peer = n := by
  unfold N.snapshotTo
  rcases h with h | h <;> simp [h]

/-- `snapshot_to` of an attached peer is the snapshot the HELLO handler sends. -/
theorem snapshotTo_attached (e : Env) (n : N) (now peer : Nat) (hh : n.isHub = true) (ha : n.attached.has peer = true) :
    N.snapshotTo e n now peer = N.sendSnapshot e n now peer := by
  unfold N.snapshotTo; simp [hh, ha]

/-- `snapshot_to` changes no attachment and no lease. -/
theorem snapshotTo_tables (e : Env) (n : N) (now peer : Nat) :
    (N.snapshotTo e n now peer).roster = n.roster := by
  unfold N.snapshotTo; split <;> simp

/-- A cleared entry of `hello_at` or `hsent` stays in the table: no key appears or disappears. -/
theorem unset_keys (m : AMap (Option Nat)) (k : Nat) : (m.unset k).keys = m.keys := by
  unfold AMap.unset; exact AMap.keys_modify _ _ _

/-- A cleared entry reads as no time. -/
theorem unset_timeAt (m : AMap (Option Nat)) (k : Nat) : (m.unset k).timeAt k = none := by
  unfold AMap.unset AMap.timeAt AMap.modify AMap.get?
  induction m with
  | nil => simp
  | cons p r ih =>
    by_cases h : p.1 = k <;> simp [h] <;> simp_all

/-- A HELLO keeps an armed watchdog time and arms an unarmed one. -/
theorem markHello_helloAt (n : N) (hub now : Nat) :
    ((n.markHello hub now).helloAt.timeAt hub) = (match n.helloAt.timeAt hub with | some t => some t | none => some now) := by
  unfold N.markHello AMap.timeAt
  simp only [AMap.get?_insert_self, Option.getD_some]
  cases n.helloAt.get? hub with
  | none => simp [AMap.timeAt]
  | some v => cases v <;> simp [AMap.timeAt]

end Vinc.Membership
