import Vinc.MembershipInvHub
import Vinc.MembershipModelNode

/-!
# Property 9, part 5: every call of the machine keeps `Inv`

`drop_peer`, `pulse_refresh`, the periodic sweeps, `tick`, `on_timeout`, `on_frame`, `on_bytes`, `session_up`,
`session_down`, `leave`, `address_changed` and `start`: from a node whose tables are all within their capacity,
every public call yields one (`inv_start` gives the first such node), and `revoke` yields one or refuses with
`TableFull` (`none`). So the tables of the membership machine never exceed their capacity, whatever the sequence of
calls.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

variable {B : List Nat}

theorem inv_dropPeer {e : Env} {n : N} (hx : Inv B n) (now peer : Nat) : Inv B (N.dropPeer e n now peer) := by
  unfold N.dropPeer
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_dropPeer)

theorem inv_pulseRefresh {e : Env} {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.pulseRefresh e n now) := by
  unfold N.pulseRefresh
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_pulseRefresh)

theorem inv_sampleSessionRtts {e : Env} {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.sampleSessionRtts e n now) := by
  unfold N.sampleSessionRtts
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_sampleSessionRtts)

theorem inv_dropStaleHubs {e : Env} {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.dropStaleHubs e n now) := by
  unfold N.dropStaleHubs
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_dropStaleHubs)

theorem inv_slowTick {e : Env} {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.slowTick e n now) := by
  unfold N.slowTick
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_slowTick)

theorem inv_tick {e : Env} {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.tick e n now) := by
  unfold N.tick
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_tick)

theorem inv_onTimeout {e : Env} {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.onTimeout e n now) := by
  unfold N.onTimeout
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_onTimeout)

theorem inv_onFrame {e : Env} {n : N} (hx : Inv B n) (now peer : Nat) (f : NFrame) : Inv B (N.onFrame e n now peer f) := by
  unfold N.onFrame
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_onFrame)

theorem inv_onBytes {e : Env} {n : N} (hx : Inv B n) (now peer : Nat) (fs : List NFrame) (bad : Bool) : Inv B (N.onBytes e n now peer fs bad) := by
  unfold N.onBytes
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_onBytes)

theorem inv_sessionUp {e : Env} {n : N} (hx : Inv B n) (now peer : Nat) (incoming : Bool) : Inv B (N.sessionUp e n now peer incoming) := by
  unfold N.sessionUp
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_sessionUp)

theorem inv_sessionDown {e : Env} {n : N} (hx : Inv B n) (now peer code : Nat) : Inv B (N.sessionDown e n now peer code) := by
  unfold N.sessionDown
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_sessionDown)

theorem inv_leave {n : N} (hx : Inv B n) : Inv B (N.leave n) := by
  unfold N.leave
  inv_go
macro_rules | `(tactic| inv_apply) => `(tactic| apply inv_leave)

theorem inv_addressChanged {n : N} (hx : Inv B n) (now : Nat) : Inv B (N.addressChanged n now) := by
  unfold N.addressChanged
  inv_go

theorem inv_snapshotTo {e : Env} {n : N} (hx : Inv B n) (now peer : Nat) : Inv B (N.snapshotTo e n now peer) := by
  unfold N.snapshotTo
  inv_go

theorem inv_setMaxFrame {n : N} (hx : Inv B n) (mb : Nat) : Inv B (N.setMaxFrame n mb) := by
  unfold N.setMaxFrame
  inv_go

/-- The body of `revoke` after the `TableFull` test, as a node (`revoke_eq_body` checks it is the model's by `rfl`). -/
def N.revokeBody (e : Env) (n : N) (now member : Nat) : N :=
    let n := { n with revoked := n.revoked.ins member }
    let n := { n with hv := n.hv.map (fun (p : Nat × HubCopy) => (p.1, { p.2 with entries := p.2.entries.erase member })) }
    let n := { n with recheck := n.recheck.erase member, left := n.left.del member, susp := n.susp.erase member,
                      downed := n.downed.erase member, attached := n.attached.del member, homed := n.homed.del member }
    let n := match n.members.get? member with
      | some x =>
        let n := (({ n with members := n.members.erase member }).trace (.removed member Removal.revoked.toNat))
        let n := { n with goneVer := n.goneVer.erase member }
        let n := if n.isHub then N.homeDelta e n member x.rc .down else n
        n.bump
      | none => n
    let n := match n.roster.get? member with
      | some l => N.pushDelta e { n with roster := n.roster.erase member } now member l.rc .down
      | none => n
    let n := n.bc (.release member)
    let n := if n.up.has member then n.close member .revoked else n
    n.emit (.revoked member)

theorem revoke_eq_body (e : Env) (n : N) (now member : Nat) :
    N.revoke e n now member =
      if !n.revoked.has member && MAX_TABLE ≤ n.revoked.len then none else some (N.revokeBody e n now member) := rfl

/-- `revoke` leaves `Inv`, or refuses with `TableFull`. -/
theorem inv_revoke {e : Env} {n : N} (hx : Inv B n) (now member : Nat) (n' : N)
    (h : N.revoke e n now member = some n') : Inv B n' := by
  rw [revoke_eq_body] at h
  by_cases hc : (!n.revoked.has member && decide (MAX_TABLE ≤ n.revoked.len)) = true
  · rw [if_pos hc] at h; cases h
  · rw [if_neg hc] at h
    have hg : n.revoked.len < MAX_TABLE ∨ n.revoked.has member = true := by
      by_cases hh : n.revoked.has member = true
      · exact Or.inr hh
      · refine Or.inl ?_
        simp only [Bool.not_eq_true] at hh
        simp only [hh, Bool.not_false, Bool.true_and, decide_eq_true_eq] at hc
        exact Nat.lt_of_not_le hc
    injection h with h
    rw [← h]
    clear h hc
    unfold N.revokeBody
    inv_go

/-! ## The first node -/

theorem dedup_nodup (hubs : List Nat) (acc : List Nat) (h : acc.Nodup) :
    (hubs.foldl (fun acc h => if acc.contains h then acc else acc ++ [h]) acc).Nodup := by
  induction hubs generalizing acc with
  | nil => exact h
  | cons x r ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h
    · rename_i hc
      simp only [List.contains_eq_any_beq, List.any_eq_true, not_exists, not_and, beq_iff_eq] at hc
      rw [List.nodup_append]
      refine ⟨h, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro hab; subst hab
      exact hc a ha rfl

theorem inv_start {e : Env} {me : Nat} {isHub : Bool} {hubs : List Nat} {tracing : Bool} {now wall floor : Nat} {n : N}
    (h : N.start e me isHub hubs tracing now wall floor = .ok n) : ∃ B, Inv B n := by
  unfold N.start at h
  dsimp only at h
  generalize hb0 : List.foldl (fun acc h => if acc.contains h = true then acc else acc ++ [h]) [] hubs = boot0 at h
  generalize hb : (if (isHub && !boot0.contains me) = true then boot0 ++ [me] else boot0) = boot at h
  have hnd0 : boot0.Nodup := hb0 ▸ dedup_nodup hubs [] List.nodup_nil
  have hnd : boot.Nodup := by
    rw [← hb]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      rw [List.nodup_append]
      refine ⟨hnd0, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, ?_⟩
      have hme : me ∉ boot0 := by simpa using hc.2
      intro a ha b hb' hab
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact hme (hab ▸ ha)
    · exact hnd0
  by_cases h1 : MAX_HUBS < boot.length
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    split at h
    · cases h
    · cases h
    · rename_i inc loc hs
      injection h with h
      subst h
      refine ⟨boot, inv_trace (B := boot) ?_ _⟩
      refine ⟨Bnd.nil, Bnd.nil, Bnd.nil, Bnd.nil, Bnd.nil, Bnd.nil, Bnd.nil, Bnd.nil, Bnd.nil, Bnd.nil, Bnd.nil,
        KBnd.nil, KBnd.nil, KBnd.nil, KBnd.nil, ?_, rfl, Nat.le_of_not_lt h1, hnd, ?_, ?_⟩
      · dsimp only
        split
        · refine HvB.insert HvB.nil _ _ Bnd.nil (Or.inl ?_)
          decide
        · exact HvB.nil
      · simp
      · simp

end Vinc.Membership
