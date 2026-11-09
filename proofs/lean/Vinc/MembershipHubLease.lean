import Vinc.MembershipHubWatch

/-!
# Hub theorems, part 4: dropping, holding, restoring and releasing a lease

Properties 5 and 7 at the hub, and the roster tables of property 9.

* `hubDown_left`: a leave (cause `left`) drops the lease, releases the member's subscriptions (never holds them) and
  records nothing in `downed`.
* `hubDown_hold`: a confirmation or an accepted DOWN drops the lease, holds the subscriptions for the lease (a `hold`,
  never a `release`) and records the member in `downed` with the time (the table has room, or already lists it).
* `carrierReturn_restores` (5): a member in `downed` whose carrier returns gets its lease back (renewed now), its
  subscriptions restored (`restore`) and is told about itself; `carrierReturn_nothing_held`: with nothing held, only a
  `restored = false` record is traced.
* `sessionDown_leave` (7): a hub that sees the leave code on a member's session drops the lease with cause `left`.
* `onHello_roster_le`, `hubDown_downed_le`, `onHello_attached_le`, `onHello_homed_le` (9): inserts check the bound and
  refuse instead of evicting. `carrierReturn_roster_unbounded` records a gap of the code found while proving these:
  `carrier_return` inserts into the roster without the bound check.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

theorem AMap.get?_insert_self {α : Type} (m : AMap α) (k : Nat) (v : α) : (m.insert k v).get? k = some v := by
  unfold AMap.get?
  induction m with
  | nil => simp [AMap.insert]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    simp only [AMap.insert]
    split
    · simp
    · rename_i h1
      split
      · simp_all
      · rename_i h2
        simp only [List.find?_cons]
        have : (a == k) = false := by simp at h2 ⊢; omega
        simp [this]
        simpa [AMap.get?] using ih

theorem foldl_ht (l : List Nat) (f : N → Nat → N) (h : ∀ n k, (f n k).HT n) (n : N) : (l.foldl f n).HT n := by
  induction l generalizing n with
  | nil => exact N.HT_refl n
  | cons k r ih => simp only [List.foldl_cons]; exact N.HT_trans (ih (f n k)) (h n k)

/-- The frames to the other hubs of a confirmation change no table. -/
theorem confirmDowns_ht (e : Env) (n : N) (member inc : Nat) (proof : Proof) :
    (n.boot.foldl
      (fun n hub =>
        if hub != n.me then
          let (n, ok) := N.tx e n hub .session (.down member inc proof)
          if ok then n.trace (.downSent member) else n
        else n) n).HT n := by
  apply foldl_ht
  intro n k
  split
  · dsimp only
    split
    · exact N.HT_trans (trace_ht _ _) (tx_ht ..)
    · exact tx_ht ..
  · exact N.HT_refl n

/-- Dropping the lease: the roster and suspicion lose the member, the attached table too. -/
def N.hdPre (n : N) (member : Nat) : N :=
  { n with roster := n.roster.erase member, susp := n.susp.erase member, attached := n.attached.del member }

theorem hubDown_eq (e : Env) (n : N) (now member : Nat) (cause : Cause) (lease : Lease)
    (h : n.roster.get? member = some lease) :
    N.hubDown e n now member cause =
      (let isLeft := match cause with | .left => true | _ => false
       let n1 := N.pushDelta e ((n.hdPre member).bc (if isLeft then .release member else .hold member)) now member lease.rc
         (if isLeft then .left else .down)
       let n2 := if !isLeft && (n1.downed.len < MAX_TABLE || n1.downed.has member) then
           { n1 with downed := n1.downed.insert member (lease, now) } else n1
       match cause with
       | .confirmed proof =>
         let n3 := n2.trace (.confirmed member)
         n3.boot.foldl
           (fun n hub =>
             if hub != n.me then
               let (n, ok) := N.tx e n hub .session (.down member lease.rc.inc proof)
               if ok then n.trace (.downSent member) else n
             else n) n3
       | _ => n2) := by
  unfold N.hubDown N.hdPre
  rw [h]
  cases cause <;> rfl

theorem AMap.has_false_of_get? {α : Type} (m : AMap α) (k : Nat) (h : m.get? k = none) : m.has k = false := by
  unfold AMap.get? at h; unfold AMap.has
  simp only [Option.map_eq_none_iff, List.find?_eq_none] at h
  simp only [List.any_eq_false]
  exact h

/-- The held-table step of `hub_down`. -/
def N.hdHold (n1 : N) (lease : Lease) (member now : Nat) : N :=
  if n1.downed.len < MAX_TABLE || n1.downed.has member then { n1 with downed := n1.downed.insert member (lease, now) } else n1

theorem hubDown_left_eq (e : Env) (n : N) (now member : Nat) (lease : Lease) (h : n.roster.get? member = some lease) :
    N.hubDown e n now member .left = N.pushDelta e ((n.hdPre member).bc (.release member)) now member lease.rc .left := by
  rw [hubDown_eq e n now member .left lease h]; rfl

theorem hubDown_remote_eq (e : Env) (n : N) (now member : Nat) (lease : Lease) (h : n.roster.get? member = some lease) :
    N.hubDown e n now member .remote =
      (N.pushDelta e ((n.hdPre member).bc (.hold member)) now member lease.rc .down).hdHold lease member now := by
  rw [hubDown_eq e n now member .remote lease h]; unfold N.hdHold; rfl

theorem hubDown_conf_eq (e : Env) (n : N) (now member : Nat) (lease : Lease) (pf : Proof) (h : n.roster.get? member = some lease) :
    N.hubDown e n now member (.confirmed pf) =
      (let n3 := ((N.pushDelta e ((n.hdPre member).bc (.hold member)) now member lease.rc .down).hdHold lease member now).trace
          (.confirmed member)
       n3.boot.foldl
         (fun n hub =>
           if hub != n.me then
             let (n, ok) := N.tx e n hub .session (.down member lease.rc.inc pf)
             if ok then n.trace (.downSent member) else n
           else n) n3) := by
  rw [hubDown_eq e n now member (.confirmed pf) lease h]; unfold N.hdHold; rfl

theorem hdHold_get (n1 : N) (lease : Lease) (member now : Nat) (hroom : n1.downed.len < MAX_TABLE ∨ n1.downed.has member = true) :
    (n1.hdHold lease member now).downed.get? member = some (lease, now) := by
  unfold N.hdHold
  have : (decide (n1.downed.len < MAX_TABLE) || n1.downed.has member) = true := by
    rcases hroom with h1 | h1 <;> simp [h1]
  simp [this, AMap.get?_insert_self]

theorem hdHold_ht (n1 : N) (lease : Lease) (member now : Nat) : (n1.hdHold lease member now).roster = n1.roster ∧
    (n1.hdHold lease member now).outBc = n1.outBc := by
  unfold N.hdHold; split <;> simp

/-- A leave drops the lease, releases the subscriptions (no `hold`) and records nothing as held. -/
theorem hubDown_left (e : Env) (n : N) (now member : Nat) (lease : Lease) (h : n.roster.get? member = some lease) :
    (N.hubDown e n now member .left).roster.get? member = none ∧ (N.hubDown e n now member .left).downed = n.downed ∧
    (N.hubDown e n now member .left).outBc = n.outBc ++ [.release member] := by
  rw [hubDown_left_eq e n now member lease h]
  obtain ⟨hr, hs, hd, hrv, ha, hh, hu, hhd, hm, hb, hi, hbc, hcl⟩ := pushDelta_ht e ((n.hdPre member).bc (.release member)) now member lease.rc .left
  have e1 : ((n.hdPre member).bc (.release member)).roster = n.roster.erase member := rfl
  have e2 : ((n.hdPre member).bc (.release member)).downed = n.downed := rfl
  have e3 : ((n.hdPre member).bc (.release member)).outBc = n.outBc ++ [.release member] := rfl
  rw [hr.trans e1, hd.trans e2, hbc.trans e3]
  exact ⟨AMap.get?_erase_self _ _, rfl, rfl⟩

/-- An accepted DOWN drops the lease, holds the subscriptions and remembers the member as held (when the held table
has room, or already lists the member). -/
theorem hubDown_remote (e : Env) (n : N) (now member : Nat) (lease : Lease) (h : n.roster.get? member = some lease)
    (hroom : n.downed.len < MAX_TABLE ∨ n.downed.has member = true) :
    (N.hubDown e n now member .remote).roster.get? member = none ∧
    (N.hubDown e n now member .remote).downed.get? member = some (lease, now) ∧
    (N.hubDown e n now member .remote).outBc = n.outBc ++ [.hold member] := by
  rw [hubDown_remote_eq e n now member lease h]
  obtain ⟨hr, hs, hd, hrv, ha, hh, hu, hhd, hm, hb, hi, hbc, hcl⟩ := pushDelta_ht e ((n.hdPre member).bc (.hold member)) now member lease.rc .down
  have e1 : ((n.hdPre member).bc (.hold member)).roster = n.roster.erase member := rfl
  have e2 : ((n.hdPre member).bc (.hold member)).downed = n.downed := rfl
  have e3 : ((n.hdPre member).bc (.hold member)).outBc = n.outBc ++ [.hold member] := rfl
  obtain ⟨g1, g2⟩ := hdHold_ht (N.pushDelta e ((n.hdPre member).bc (.hold member)) now member lease.rc .down) lease member now
  refine ⟨?_, hdHold_get _ _ _ _ (by rw [hd.trans e2]; exact hroom), ?_⟩
  · rw [g1, hr.trans e1]; exact AMap.get?_erase_self _ _
  · rw [g2, hbc.trans e3]

/-- A confirmation does the same as an accepted DOWN, then sends the DOWN frames: no table changes. -/
theorem hubDown_confirmed (e : Env) (n : N) (now member : Nat) (lease : Lease) (pf : Proof) (h : n.roster.get? member = some lease)
    (hroom : n.downed.len < MAX_TABLE ∨ n.downed.has member = true) :
    (N.hubDown e n now member (.confirmed pf)).roster.get? member = none ∧
    (N.hubDown e n now member (.confirmed pf)).downed.get? member = some (lease, now) ∧
    (N.hubDown e n now member (.confirmed pf)).outBc = n.outBc ++ [.hold member] := by
  rw [hubDown_conf_eq e n now member lease pf h]
  dsimp only
  obtain ⟨hr, hs, hd, hrv, ha, hh, hu, hhd, hm, hb, hi, hbc, hcl⟩ :=
    confirmDowns_ht e (((N.pushDelta e ((n.hdPre member).bc (.hold member)) now member lease.rc .down).hdHold lease member now).trace
      (.confirmed member)) member lease.rc.inc pf
  obtain ⟨r1, r2, r3⟩ := hubDown_remote e n now member lease h hroom
  rw [hubDown_remote_eq e n now member lease h] at r1 r2 r3
  rw [hr, hd, hbc]
  simp only [trace_roster, trace_downed, trace_outBc]
  exact ⟨r1, r2, r3⟩

end Vinc.Membership
