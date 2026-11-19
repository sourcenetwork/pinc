import Pinc.MembershipHubReturn

/-!
# Hub theorems, part 6: revocation (property 6)

`revoke_effects`: a revocation that is accepted takes effect inside the call (zero time, within the 5 s bound): the
member is recorded as revoked, its lease, its held entry, its suspicion, its attachment and its home registration are
gone, its subscriptions are released, and every session with it is closed. `TableFull` is the only refusal
(`revoke_none_iff`). `onFrame_revoked`: a frame from a revoked peer is dropped unread. `sessionUp_revoked`: a session
from a revoked peer is closed at once.
-/

set_option linter.unusedVariables false

namespace Pinc.Membership
open Pinc.MemInc

/-! ## Field facts -/

@[simp] theorem close_revoked' (n : N) (p : Nat) (r : CloseR) : (n.close p r).revoked = n.revoked := rfl
@[simp] theorem bc_revoked' (n : N) (b : Bc) : (n.bc b).revoked = n.revoked := rfl
@[simp] theorem close_roster' (n : N) (p : Nat) (r : CloseR) : (n.close p r).roster = n.roster := rfl
@[simp] theorem bc_roster' (n : N) (b : Bc) : (n.bc b).roster = n.roster := rfl
@[simp] theorem close_downed' (n : N) (p : Nat) (r : CloseR) : (n.close p r).downed = n.downed := rfl
@[simp] theorem bc_downed' (n : N) (b : Bc) : (n.bc b).downed = n.downed := rfl
@[simp] theorem close_susp' (n : N) (p : Nat) (r : CloseR) : (n.close p r).susp = n.susp := rfl
@[simp] theorem bc_susp' (n : N) (b : Bc) : (n.bc b).susp = n.susp := rfl
@[simp] theorem close_attached' (n : N) (p : Nat) (r : CloseR) : (n.close p r).attached = n.attached := rfl
@[simp] theorem bc_attached' (n : N) (b : Bc) : (n.bc b).attached = n.attached := rfl
@[simp] theorem close_homed' (n : N) (p : Nat) (r : CloseR) : (n.close p r).homed = n.homed := rfl
@[simp] theorem bc_homed' (n : N) (b : Bc) : (n.bc b).homed = n.homed := rfl
@[simp] theorem close_up' (n : N) (p : Nat) (r : CloseR) : (n.close p r).up = n.up := rfl
@[simp] theorem bc_up' (n : N) (b : Bc) : (n.bc b).up = n.up := rfl
@[simp] theorem close_outBc' (n : N) (p : Nat) (r : CloseR) : (n.close p r).outBc = n.outBc := rfl
@[simp] theorem bc_outClose' (n : N) (b : Bc) : (n.bc b).outClose = n.outClose := rfl
@[simp] theorem close_heard' (n : N) (p : Nat) (r : CloseR) : (n.close p r).heard = n.heard := rfl
@[simp] theorem bc_heard' (n : N) (b : Bc) : (n.bc b).heard = n.heard := rfl
@[simp] theorem close_me' (n : N) (p : Nat) (r : CloseR) : (n.close p r).me = n.me := rfl
@[simp] theorem bc_me' (n : N) (b : Bc) : (n.bc b).me = n.me := rfl
@[simp] theorem close_boot' (n : N) (p : Nat) (r : CloseR) : (n.close p r).boot = n.boot := rfl
@[simp] theorem bc_boot' (n : N) (b : Bc) : (n.bc b).boot = n.boot := rfl
@[simp] theorem close_isHub' (n : N) (p : Nat) (r : CloseR) : (n.close p r).isHub = n.isHub := rfl
@[simp] theorem bc_isHub' (n : N) (b : Bc) : (n.bc b).isHub = n.isHub := rfl
@[simp] theorem close_outClose' (n : N) (p : Nat) (r : CloseR) : (n.close p r).outClose = n.outClose ++ [(p, r)] := rfl

def N.rvPre (n : N) (member : Nat) : N :=
  let n := { n with revoked := n.revoked.ins member }
  let n := { n with hv := n.hv.map (fun (p : Nat × HubCopy) => (p.1, { p.2 with entries := p.2.entries.erase member })) }
  { n with recheck := n.recheck.erase member, left := n.left.del member, susp := n.susp.erase member,
           downed := n.downed.erase member, attached := n.attached.del member, homed := n.homed.del member }

def N.rvMembers (e : Env) (n : N) (now member : Nat) : N :=
  match n.members.get? member with
  | some x =>
    let n := (({ n with members := n.members.erase member }).trace (.removed member Removal.revoked.toNat))
    let n := { n with goneVer := n.goneVer.erase member }
    let n := if n.isHub then N.homeDelta e n member x.rc .down else n
    n.bump
  | none => n

def N.rvRoster (e : Env) (n : N) (now member : Nat) : N :=
  match n.roster.get? member with
  | some l => N.pushDelta e { n with roster := n.roster.erase member } now member l.rc .down
  | none => n

def N.rvEnd (n : N) (member : Nat) : N :=
  let n := n.bc (.release member)
  let n := if n.up.has member then n.close member .revoked else n
  n.emit (.revoked member)

theorem revoke_eq (e : Env) (n : N) (now member : Nat) (h : ¬ (n.revoked.has member = false ∧ MAX_TABLE ≤ n.revoked.len)) :
    N.revoke e n now member = some (((n.rvPre member |> fun x => N.rvMembers e x now member) |> fun x => N.rvRoster e x now member).rvEnd member) := by
  unfold N.revoke N.rvPre N.rvMembers N.rvRoster N.rvEnd
  have : (!n.revoked.has member && MAX_TABLE ≤ n.revoked.len) = false := by
    simp at h ⊢; intro h1; exact h h1
  simp only [this]
  rfl

theorem rvMembers_ht (e : Env) (n : N) (now member : Nat) : (N.rvMembers e n now member).HT n := by
  unfold N.rvMembers
  split
  · dsimp only
    split
    · exact N.HT_trans (bump_ht _) (N.HT_trans (homeDelta_ht ..) (N.HT_trans (goneVer_ht _ _) (N.HT_trans (trace_ht _ _) (members_ht _ _))))
    · exact N.HT_trans (bump_ht _) (N.HT_trans (goneVer_ht _ _) (N.HT_trans (trace_ht _ _) (members_ht _ _)))
  · exact N.HT_refl n

theorem roster_ht' (n : N) (f : AMap Lease) : ({ n with roster := f } : N).roster = f := rfl

theorem rvRoster_spec (e : Env) (n : N) (now member : Nat) :
    (N.rvRoster e n now member).roster.get? member = none ∧ (N.rvRoster e n now member).downed = n.downed ∧
    (N.rvRoster e n now member).outBc = n.outBc ∧ (N.rvRoster e n now member).susp = n.susp ∧
    (N.rvRoster e n now member).attached = n.attached ∧ (N.rvRoster e n now member).homed = n.homed ∧
    (N.rvRoster e n now member).revoked = n.revoked ∧ (N.rvRoster e n now member).up = n.up ∧
    (N.rvRoster e n now member).outClose = n.outClose := by
  unfold N.rvRoster
  cases hr : n.roster.get? member with
  | none => exact ⟨hr, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | some l =>
    dsimp only
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
      pushDelta_ht e ({ n with roster := n.roster.erase member } : N) now member l.rc .down
    exact ⟨by rw [p1]; exact AMap.get?_erase_self _ _, p3, p12, p2, p5, p6, p4, p7, p13⟩

theorem revoke_effects (e : Env) (n n' : N) (now member : Nat) (h : N.revoke e n now member = some n') :
    n'.revoked.has member = true ∧ n'.roster.get? member = none ∧ n'.downed.get? member = none ∧
    n'.susp.get? member = none ∧ n'.attached.has member = false ∧ n'.homed.has member = false ∧
    n'.outBc = n.outBc ++ [.release member] ∧ (n.up.has member = true → n'.outClose = n.outClose ++ [(member, .revoked)]) := by
  have hc : ¬ (n.revoked.has member = false ∧ MAX_TABLE ≤ n.revoked.len) := by
    intro hh; rw [(revoke_none_iff e n now member).2 hh] at h; cases h
  rw [revoke_eq e n now member hc] at h
  injection h with h; subst h
  dsimp only
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := rvMembers_ht e (n.rvPre member) now member
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := rvRoster_spec e (N.rvMembers e (n.rvPre member) now member) now member
  have a_rev : (n.rvPre member).revoked = n.revoked.ins member := rfl
  have a_dn : (n.rvPre member).downed = n.downed.erase member := rfl
  have a_su : (n.rvPre member).susp = n.susp.erase member := rfl
  have a_at : (n.rvPre member).attached = n.attached.del member := rfl
  have a_ho : (n.rvPre member).homed = n.homed.del member := rfl
  have a_bc : (n.rvPre member).outBc = n.outBc := rfl
  have a_cl : (n.rvPre member).outClose = n.outClose := rfl
  have a_up : (n.rvPre member).up = n.up := rfl
  generalize N.rvMembers e (n.rvPre member) now member = B at *
  generalize N.rvRoster e B now member = C at *
  have e_dn : C.downed = n.downed.erase member := by rw [c2, b3, a_dn]
  have e_su : C.susp = n.susp.erase member := by rw [c4, b2, a_su]
  have e_at : C.attached = n.attached.del member := by rw [c5, b5, a_at]
  have e_ho : C.homed = n.homed.del member := by rw [c6, b6, a_ho]
  have e_rv : C.revoked = n.revoked.ins member := by rw [c7, b4, a_rev]
  have e_bc : C.outBc = n.outBc := by rw [c3, b12, a_bc]
  have e_up : C.up = n.up := by rw [c8, b7, a_up]
  have e_cl : C.outClose = n.outClose := by rw [c9, b13, a_cl]
  unfold N.rvEnd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only; split <;> simp [e_rv, ASet.ins, ASet.has, AMap.has_insert_self]
  · dsimp only; split <;> simp [c1]
  · dsimp only; split <;> simp [e_dn, AMap.get?_erase_self]
  · dsimp only; split <;> simp [e_su, AMap.get?_erase_self]
  · dsimp only; split <;> simp [e_at, ASet.del, ASet.has, AMap.has_erase_self]
  · dsimp only; split <;> simp [e_ho, ASet.del, ASet.has, AMap.has_erase_self]
  · dsimp only; split <;> simp [e_bc]
  · intro hu
    dsimp only
    simp [e_up, hu, e_cl]

/-- Frames from a revoked peer are dropped unread. -/
theorem onFrame_revoked (e : Env) (n : N) (now peer : Nat) (f : NFrame) (h : n.revoked.has peer = true) :
    N.onFrame e n now peer f = n := by
  unfold N.onFrame; simp [h]

/-- A session from a revoked peer is closed at once, with the revocation reason, and nothing else happens. -/
theorem sessionUp_revoked (e : Env) (n : N) (now peer : Nat) (incoming : Bool) (hne : peer ≠ n.me)
    (h : n.revoked.has peer = true) : N.sessionUp e n now peer incoming = n.close peer .revoked := by
  unfold N.sessionUp
  have : (peer == n.me) = false := by simpa using hne
  simp [this, h]

/-- The steps of `on_hello` before the roster is touched. -/
def N.ohPre (e : Env) (n : N) (now peer : Nat) (snap homed : Bool) : N :=
  let n := if homed && !n.isBoot peer then
      (if n.homed.len < MAX_TABLE then { n with homed := n.homed.ins peer } else n)
    else { n with homed := n.homed.del peer }
  let n := if n.downed.has peer then (N.bc { n with downed := n.downed.erase peer } (.restore peer)) else n
  let newAttach := !n.attached.has peer
  let n := if newAttach && n.attached.len < MAX_TABLE then { n with attached := n.attached.ins peer } else n
  let n := if newAttach then N.sendFloor e (n.trace (.attached peer)) peer else n
  if snap || newAttach then N.sendSnapshot e n now peer else (N.tx e n peer .session .ack).1

theorem sendFloor_roster (e : Env) (n : N) (peer : Nat) : (N.sendFloor e n peer).roster = n.roster := by
  unfold N.sendFloor; dsimp only; split <;> simp

theorem foldlG_ht {α : Type} (l : List α) (f : N → α → N) (h : ∀ n a, (f n a).HT n) (n : N) : (l.foldl f n).HT n := by
  induction l generalizing n with
  | nil => exact N.HT_refl n
  | cons k r ih => simp only [List.foldl_cons]; exact N.HT_trans (ih (f n k)) (h n k)

theorem sendSnapshot_ht (e : Env) (n : N) (now peer : Nat) : (N.sendSnapshot e n now peer).HT n := by
  unfold N.sendSnapshot
  dsimp only
  exact foldlG_ht _ _ (fun n c => tx_ht ..) n

theorem sendFloor_ht (e : Env) (n : N) (peer : Nat) : (N.sendFloor e n peer).HT n := by
  unfold N.sendFloor; dsimp only; split
  · exact N.HT_refl n
  · exact tx_ht ..

@[simp] theorem sendFloor_r (e : Env) (n : N) (peer : Nat) : (N.sendFloor e n peer).roster = n.roster := (sendFloor_ht e n peer).1
@[simp] theorem sendSnapshot_r (e : Env) (n : N) (now peer : Nat) : (N.sendSnapshot e n now peer).roster = n.roster :=
  (sendSnapshot_ht e n now peer).1

theorem ohPre_roster (e : Env) (n : N) (now peer : Nat) (snap homed : Bool) : (n.ohPre e now peer snap homed).roster = n.roster := by
  unfold N.ohPre
  dsimp only
  simp only [ite_roster, bc_roster', trace_roster, sendFloor_r, sendSnapshot_r, tx_roster, ite_self]

/-- Property 9: a HELLO from a member the full roster does not list is refused instead of evicting: the roster does
not change. -/
theorem onHello_full_refuses (e : Env) (n : N) (now peer : Nat) (rc : Rec) (snap homed : Bool)
    (hn : n.roster.has peer = false) (hfull : MAX_TABLE ≤ n.roster.len) :
    (N.onHello e n now peer rc snap homed).roster = n.roster := by
  have hq : N.onHello e n now peer rc snap homed =
      (let n1 := n.ohPre e now peer snap homed
       match n1.roster.get? peer with
       | some held =>
         if rc.inc < held.rc.inc then
           let n := { n1 with roster := n1.roster.modify peer (fun l => { l with renewed := now }) }
           N.deltaTo e n peer peer held.rc .alive
         else if held.rc == rc then
           { n1 with roster := n1.roster.modify peer (fun l => { l with renewed := now }) }
         else if MAX_TABLE ≤ n1.roster.len && !n1.roster.has peer then n1
         else
           let n := { n1 with roster := n1.roster.insert peer ⟨rc, now⟩ }
           N.pushDelta e n now peer rc .alive
       | none =>
         if MAX_TABLE ≤ n1.roster.len then n1
         else
           let n := { n1 with roster := n1.roster.insert peer ⟨rc, now⟩ }
           N.pushDelta e n now peer rc .alive) := rfl
  rw [hq]
  dsimp only
  have hr := ohPre_roster e n now peer snap homed
  have hg : (n.ohPre e now peer snap homed).roster.get? peer = none := by
    rw [hr]; unfold AMap.get? AMap.has at *
    simpa [List.any_eq_false, List.find?_eq_none] using hn
  rw [hg]
  have : MAX_TABLE ≤ (n.ohPre e now peer snap homed).roster.len := by rw [hr]; exact hfull
  rw [if_pos this]; exact hr

end Pinc.Membership
