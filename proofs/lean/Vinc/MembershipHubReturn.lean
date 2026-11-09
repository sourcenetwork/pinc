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

@[simp] theorem bc_boot (n : N) (b : Bc) : (n.bc b).boot = n.boot := rfl
@[simp] theorem bc_roster (n : N) (b : Bc) : (n.bc b).roster = n.roster := rfl
@[simp] theorem bc_downed (n : N) (b : Bc) : (n.bc b).downed = n.downed := rfl
@[simp] theorem bc_outBc (n : N) (b : Bc) : (n.bc b).outBc = n.outBc ++ [b] := rfl
@[simp] theorem bc_primary (n : N) (b : Bc) : (n.bc b).primary = n.primary := rfl

/-- The first step of `drop_peer`. -/
def N.dpMid (n : N) (peer : Nat) : N :=
  { n with up := n.up.erase peer, attached := n.attached.del peer, homed := n.homed.del peer,
           helloAt := n.helloAt.erase peer, hsent := n.hsent.erase peer }

theorem dropPeer_notboot (e : Env) (n : N) (now peer : Nat) (h : n.isBoot peer = false) :
    (N.dropPeer e n now peer).roster = n.roster ∧ (N.dropPeer e n now peer).downed = n.downed ∧
    (N.dropPeer e n now peer).outBc = n.outBc ++ (if n.downed.has peer then [] else [.release peer]) := by
  have hb : (n.dpMid peer).isBoot peer = false := h
  have hd : N.dropPeer e n now peer =
      (let n1 := n.dpMid peer
       let n1 := if !n1.isHub && n1.homeOk == some peer then { n1 with homeOk := none } else n1
       let n1 := if !n1.downed.has peer then n1.bc (.release peer) else n1
       if n1.isBoot peer && n1.primary == some peer then N.reselect e n1 now else n1) := rfl
  rw [hd]
  have h' : n.boot.contains peer = false := h
  have h'' : peer ∉ n.boot := by simpa using h'
  simp [N.dpMid, N.isBoot, h'']
  split <;> split <;> simp_all

/-- Property 7 at the hub: the leave code on a member's session is `hub_down` with cause `left`: the lease is dropped,
the subscriptions are released (never held), nothing is recorded as held. -/
theorem sessionDown_leave (e : Env) (n : N) (now peer code : Nat) (l : Lease) (hup : n.up.has peer = true)
    (hhub : n.isHub = true) (hcode : code = LEAVE_CODE) (hb : n.isBoot peer = false) (hl : n.roster.get? peer = some l) :
    (N.sessionDown e n now peer code).roster.get? peer = none ∧
    (N.sessionDown e n now peer code).downed = n.downed ∧
    (N.sessionDown e n now peer code).outBc = n.outBc ++ [.release peer] ++ (if n.downed.has peer then [] else [.release peer]) := by
  have hs : N.sessionDown e n now peer code =
      N.dropPeer e (N.hubDown e (({ n with up := n.up.erase peer } : N).trace (.leaveSeen peer)) now peer .left) now peer := by
    unfold N.sessionDown
    subst hcode
    have h1 : (!n.up.has peer) = false := by simp [hup]
    have h2 : (n.isHub && LEAVE_CODE == LEAVE_CODE && !n.isBoot peer) = true := by simp [hhub, hb]
    simp only [h1, Bool.false_eq_true, if_false]
    have hc : (n.isHub && LEAVE_CODE == LEAVE_CODE && !(({ n with up := n.up.erase peer } : N).isBoot peer)) = true := h2
    rw [if_pos hc]
  rw [hs]
  obtain ⟨n1, hn1⟩ : ∃ n1 : N, n1 = (({ n with up := n.up.erase peer } : N).trace (.leaveSeen peer)) := ⟨_, rfl⟩
  rw [← hn1]
  have hr1 : n1.roster = n.roster := by rw [hn1]; simp
  have hd1 : n1.downed = n.downed := by rw [hn1]; simp
  have hb1 : n1.outBc = n.outBc := by rw [hn1]; simp
  have hbt : n1.isBoot peer = false := by rw [hn1]; simpa [N.isBoot] using hb
  obtain ⟨r1, r2, r3⟩ := hubDown_left e n1 now peer l (by rw [hr1]; exact hl)
  have hbd : (N.hubDown e n1 now peer .left).isBoot peer = false := by
    rw [hubDown_left_eq e n1 now peer l (by rw [hr1]; exact hl)]
    obtain ⟨-, -, -, -, -, -, -, -, -, hbt', -⟩ := pushDelta_ht e ((n1.hdPre peer).bc (.release peer)) now peer l.rc .left
    unfold N.isBoot
    rw [hbt']
    exact hbt
  obtain ⟨q1, q2, q3⟩ := dropPeer_notboot e (N.hubDown e n1 now peer .left) now peer hbd
  refine ⟨?_, ?_, ?_⟩
  · rw [q1]; exact r1
  · rw [q2, r2, hd1]
  · rw [q3, r3, hb1, r2, hd1]

end Vinc.Membership
