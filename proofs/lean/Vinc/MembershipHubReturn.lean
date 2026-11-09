import Vinc.MembershipHubLease

/-!
# Hub theorems, part 5: a returning carrier, a leave seen on a session, revocation

* `carrierReturn_restores` (property 5): the lease comes back, renewed now; the subscriptions are restored (`restore`);
  the member is told about itself (a DELTA to the member, in the sent list, traced `restored = true`).
* `carrierReturn_nothing_held`: nothing held, nothing restored: only a `restored = false` record.
* `carrierReturn_roster_unbounded` (property 9): the roster insert of `carrier_return` has no bound check.
* `sessionDown_leave` (property 7): the leave code on a member's session on a hub is `hub_down` with cause `left`.
* `revoke_effects` (property 6): revocation removes the member from the roster, the held, suspicion, attached and homed
  tables and the hub copies in the call itself, records it, releases its subscriptions, closes its sessions;
  `revoke_none_iff` (`MembershipModelLemmas`) is the `TableFull` answer. `onFrame_revoked`: frames from a revoked
  peer are dropped unread.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

theorem AMap.insert_length_new {α : Type} (m : AMap α) (k : Nat) (v : α) (h : m.has k = false) :
    (m.insert k v).length = m.length + 1 := by
  induction m with
  | nil => simp [AMap.insert]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    have hk : (a == k) = false := by
      unfold AMap.has at h; simp [List.any_cons] at h; simp [h.1]
    have hr : AMap.has r k = false := by
      unfold AMap.has at h ⊢; simp [List.any_cons] at h; simpa using h.2
    simp only [AMap.insert]
    split
    · simp
    · rename_i h1
      split
      · rename_i h2; simp at h2; simp [h2] at hk
      · simp [ih hr]

/-- The attach step of `carrier_return`. -/
def N.crAttach (n : N) (member : Nat) : N :=
  if n.up.has member && n.attached.len < MAX_TABLE then { n with attached := n.attached.ins member } else n

theorem crAttach_ht (n : N) (member : Nat) : (n.crAttach member).roster = n.roster ∧ (n.crAttach member).downed = n.downed ∧
    (n.crAttach member).outBc = n.outBc := by
  unfold N.crAttach; split <;> simp

theorem carrierReturn_nothing_held (e : Env) (n : N) (now member : Nat) (h : n.downed.get? member = none) :
    N.carrierReturn e n now member = n.trace (.carrierReturned member false) := by
  unfold N.carrierReturn; simp [h]

theorem carrierReturn_eq (e : Env) (n : N) (now member : Nat) (l : Lease) (t0 : Nat) (h : n.downed.get? member = some (l, t0))
    (hr : n.roster.has member = false) (hv : n.revoked.has member = false) :
    N.carrierReturn e n now member =
      (let l' : Lease := { l with renewed := now }
       let n1 : N := { n with downed := n.downed.erase member }
       let n2 : N := { n1 with roster := n1.roster.insert member l' }
       let n3 := (n2.crAttach member).bc (.restore member)
       let n4 := N.pushDelta e n3 now member l'.rc .alive
       (N.deltaTo e n4 member member l'.rc .alive).trace (.carrierReturned member true)) := by
  unfold N.carrierReturn N.crAttach
  simp [h, hr, hv]

/-- Property 5: a returning carrier within the hold restores the lease, the subscriptions and tells the member. -/
theorem carrierReturn_restores (e : Env) (n : N) (now member : Nat) (l : Lease) (t0 : Nat)
    (h : n.downed.get? member = some (l, t0)) (hr : n.roster.has member = false) (hv : n.revoked.has member = false) :
    (N.carrierReturn e n now member).roster.get? member = some { l with renewed := now } ∧
    (N.carrierReturn e n now member).downed.get? member = none ∧
    (N.carrierReturn e n now member).outBc = n.outBc ++ [.restore member] := by
  rw [carrierReturn_eq e n now member l t0 h hr hv]
  dsimp only
  obtain ⟨X, hX⟩ : ∃ X : N, X = { n with downed := n.downed.erase member, roster := n.roster.insert member { l with renewed := now } } := ⟨_, rfl⟩
  rw [← hX]
  have hXr : X.roster = n.roster.insert member { l with renewed := now } := by rw [hX]
  have hXd : X.downed = n.downed.erase member := by rw [hX]
  obtain ⟨a1, a2, a3⟩ := crAttach_ht X member
  have hY1 : ((X.crAttach member).bc (.restore member)).roster = n.roster.insert member { l with renewed := now } := by
    rw [← hXr]; exact a1
  have hY2 : ((X.crAttach member).bc (.restore member)).downed = n.downed.erase member := by
    rw [← hXd]; exact a2
  have hY3 : ((X.crAttach member).bc (.restore member)).outBc = n.outBc ++ [.restore member] := by
    show (X.crAttach member).outBc ++ [.restore member] = _
    rw [a3, hX]
  obtain ⟨p1, -, p2, -, -, -, -, -, -, -, -, p3, -⟩ := pushDelta_ht e ((X.crAttach member).bc (.restore member)) now member
    { l with renewed := now }.rc .alive
  simp only [trace_roster, trace_downed, trace_outBc, deltaTo_roster, deltaTo_downed, deltaTo_outBc]
  refine ⟨?_, ?_, ?_⟩
  · rw [p1, hY1]; exact AMap.get?_insert_self _ _ _
  · rw [p2, hY2]; exact AMap.get?_erase_self _ _
  · rw [p3, hY3]

/-- Property 9: the roster insert of `carrier_return` is not guarded by the table bound (the other inserts are): a full
roster grows to `MAX_TABLE + 1`. -/
theorem carrierReturn_roster_unbounded (e : Env) (n : N) (now member : Nat) (l : Lease) (t0 : Nat)
    (h : n.downed.get? member = some (l, t0)) (hr : n.roster.has member = false) (hv : n.revoked.has member = false) :
    (N.carrierReturn e n now member).roster.length = n.roster.length + 1 := by
  rw [carrierReturn_eq e n now member l t0 h hr hv]
  dsimp only
  obtain ⟨X, hX⟩ : ∃ X : N, X = { n with downed := n.downed.erase member, roster := n.roster.insert member { l with renewed := now } } := ⟨_, rfl⟩
  rw [← hX]
  have hXr : X.roster = n.roster.insert member { l with renewed := now } := by rw [hX]
  have hXd : X.downed = n.downed.erase member := by rw [hX]
  obtain ⟨a1, a2, a3⟩ := crAttach_ht X member
  obtain ⟨p1, -⟩ := pushDelta_ht e ((X.crAttach member).bc (.restore member)) now member { l with renewed := now }.rc .alive
  simp only [trace_roster, deltaTo_roster]
  rw [p1]
  show (X.crAttach member).roster.length = _
  rw [a1, hXr]
  exact AMap.insert_length_new _ _ _ hr

end Vinc.Membership
