import Pinc.MembershipModelLemmas

/-!
# Membership view: frame lemmas

What the output-only operations (`emit`, `trace`, `tx`, `deltaTo`, `homeDelta`, `bc`) leave alone, and what
`recompute_one`, `remove_from_view`, `bump` do to the tables. These are the building blocks of the view theorems in
`MembershipViewThm.lean` and `MembershipViewInv.lean`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Pinc.Membership
open Pinc.MemInc

variable {α : Type}
namespace AMap

theorem get?_insert_ne (m : AMap α) (k j : Nat) (v : α) (h : j ≠ k) : (m.insert k v).get? j = m.get? j := by
  have hkj : (k == j) = false := by simp; omega
  unfold get?
  induction m with
  | nil => simp [insert, List.find?, hkj]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    simp only [insert]
    by_cases h1 : k < a
    · rw [if_pos h1]; simp [List.find?, hkj]
    · rw [if_neg h1]
      by_cases h2 : (k == a) = true
      · rw [if_pos h2]; simp at h2; subst h2; simp [List.find?, hkj]
      · rw [if_neg h2]; simp only [List.find?]
        cases (a == j) <;> simp_all

theorem get?_insert_self (m : AMap α) (k : Nat) (v : α) : (m.insert k v).get? k = some v := by
  unfold get?
  induction m with
  | nil => simp [insert]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    simp only [insert]
    by_cases h1 : k < a
    · rw [if_pos h1]; simp [List.find?]
    · rw [if_neg h1]
      by_cases h2 : (k == a) = true
      · rw [if_pos h2]; simp [List.find?]
      · rw [if_neg h2]; simp only [List.find?]
        have : (a == k) = false := by simp at h2 ⊢; omega
        simp [this]; simpa using ih

theorem get?_erase_ne (m : AMap α) (k j : Nat) (h : j ≠ k) : (m.erase k).get? j = m.get? j := by
  unfold erase get?
  induction m with
  | nil => simp
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    by_cases h1 : a = k
    · subst h1; have : (a == j) = false := by simp; omega
      simp [List.filter_cons, List.find?, this]; simpa using ih
    · simp [List.filter_cons, h1, List.find?]
      cases hh : (a == j) <;> simp_all
  

theorem get?_modify_ne (m : AMap α) (k j : Nat) (f : α → α) (h : j ≠ k) : (m.modify k f).get? j = m.get? j := by
  induction m with
  | nil => simp [modify, get?]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    by_cases h1 : a = k
    · subst h1
      have : (a == j) = false := by simp; omega
      simp only [modify, get?, List.map_cons, List.find?_cons] at ih ⊢
      simp [this] at ih ⊢; exact ih
    · have hak : (a == k) = false := by simp; omega
      simp only [modify, get?, List.map_cons, List.find?_cons] at ih ⊢
      simp [hak]
      cases hh : (a == j) <;> simp_all

theorem has_modify (m : AMap α) (k j : Nat) (f : α → α) : (m.modify k f).has j = m.has j := by
  unfold modify has
  induction m with
  | nil => simp
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    by_cases h1 : a = k
    · subst h1; simp [List.any_cons] at ih ⊢; simp [ih]
    · simp [List.any_cons, h1] at ih ⊢; simp [ih]

theorem has_iff_get (m : AMap α) (k : Nat) : m.has k = (m.get? k).isSome := by
  unfold has get?
  induction m with
  | nil => simp
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    by_cases h1 : a = k
    · subst h1; simp [List.find?]
    · have : (a == k) = false := by simp; omega
      simp [List.find?, this]; simpa using ih

end AMap

/-- `n'` differs from `n` only in the output lists (events, traces, effects on the host). -/
def OutOnly (n n' : N) : Prop :=
  ∃ a b c d e f g, n' = { n with events := a, lostEvents := b, traces := c, lostTraces := d, outSent := e, outBc := f, outClose := g }

theorem OutOnly.refl (n : N) : OutOnly n n := ⟨n.events, n.lostEvents, n.traces, n.lostTraces, n.outSent, n.outBc, n.outClose, rfl⟩

theorem OutOnly.trans {a b c : N} (h1 : OutOnly a b) (h2 : OutOnly b c) : OutOnly a c := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h1
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, rfl⟩ := h2
  exact ⟨x1, x2, x3, x4, x5, x6, x7, rfl⟩

theorem emit_out (n : N) (e : Ev) : OutOnly n (n.emit e) := by
  unfold N.emit; split
  · exact ⟨n.events, _, n.traces, n.lostTraces, n.outSent, n.outBc, n.outClose, rfl⟩
  · exact ⟨_, n.lostEvents, n.traces, n.lostTraces, n.outSent, n.outBc, n.outClose, rfl⟩

theorem trace_out (n : N) (t : Tr) : OutOnly n (n.trace t) := by
  unfold N.trace; split
  · exact OutOnly.refl n
  · split
    · exact ⟨n.events, n.lostEvents, n.traces, _, n.outSent, n.outBc, n.outClose, rfl⟩
    · exact ⟨n.events, n.lostEvents, _, n.lostTraces, n.outSent, n.outBc, n.outClose, rfl⟩

theorem bc_out (n : N) (b : Bc) : OutOnly n (n.bc b) :=
  ⟨n.events, n.lostEvents, n.traces, n.lostTraces, n.outSent, _, n.outClose, rfl⟩

theorem tx_out (e : Env) (n : N) (p : Nat) (r : Route) (f : NFrame) : OutOnly n (N.tx e n p r f).1 := by
  unfold N.tx; split
  · exact OutOnly.refl n
  · obtain ⟨a, b, c, d, e', f', g, h⟩ := trace_out n (.frameOut p f.ty)
    refine ⟨a, b, c, d, e' ++ [(p, r, f, e.acc.has p)], f', g, ?_⟩
    dsimp only
    rw [h]

theorem deltaTo_out (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : OutOnly n (N.deltaTo e n p m rc a) :=
  tx_out e n p _ _

theorem foldl_out {α : Type} (l : List α) (f : α → N → N) (n : N) (h : ∀ a n, OutOnly n (f a n)) :
    OutOnly n (l.foldl (fun n a => f a n) n) := by
  induction l generalizing n with
  | nil => exact OutOnly.refl n
  | cons x r ih => exact (h x n).trans (ih _)

theorem homeDelta_out (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : OutOnly n (N.homeDelta e n m rc a) := by
  unfold N.homeDelta forKeys
  apply foldl_out
  intro p n
  split
  · exact deltaTo_out _ _ _ _ _ _
  · exact OutOnly.refl n

theorem OutOnly.members {n n' : N} (h : OutOnly n n') : n'.members = n.members := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.hv {n n' : N} (h : OutOnly n n') : n'.hv = n.hv := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.epoch {n n' : N} (h : OutOnly n n') : n'.epoch = n.epoch := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.revoked {n n' : N} (h : OutOnly n n') : n'.revoked = n.revoked := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.me {n n' : N} (h : OutOnly n n') : n'.me = n.me := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.isHub {n n' : N} (h : OutOnly n n') : n'.isHub = n.isHub := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.homed {n n' : N} (h : OutOnly n n') : n'.homed = n.homed := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.left {n n' : N} (h : OutOnly n n') : n'.left = n.left := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.recheck {n n' : N} (h : OutOnly n n') : n'.recheck = n.recheck := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.goneVer {n n' : N} (h : OutOnly n n') : n'.goneVer = n.goneVer := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl

/-! ## Output-only operations leave the tables alone (simp lemmas) -/

theorem OutOnly.roster {n n' : N} (h : OutOnly n n') : n'.roster = n.roster := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.attached {n n' : N} (h : OutOnly n n') : n'.attached = n.attached := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.boot {n n' : N} (h : OutOnly n n') : n'.boot = n.boot := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.up {n n' : N} (h : OutOnly n n') : n'.up = n.up := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.heard {n n' : N} (h : OutOnly n n') : n'.heard = n.heard := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.susp {n n' : N} (h : OutOnly n n') : n'.susp = n.susp := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.downed {n n' : N} (h : OutOnly n n') : n'.downed = n.downed := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.primary {n n' : N} (h : OutOnly n n') : n'.primary = n.primary := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.homeOk {n n' : N} (h : OutOnly n n') : n'.homeOk = n.homeOk := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.quietUntil {n n' : N} (h : OutOnly n n') : n'.quietUntil = n.quietUntil := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl
theorem OutOnly.born {n n' : N} (h : OutOnly n n') : n'.born = n.born := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl

@[simp] theorem emit_hv (n : N) (e : Ev) : (n.emit e).hv = n.hv := OutOnly.hv (emit_out n e)
@[simp] theorem emit_members (n : N) (e : Ev) : (n.emit e).members = n.members := OutOnly.members (emit_out n e)
@[simp] theorem emit_epoch (n : N) (e : Ev) : (n.emit e).epoch = n.epoch := OutOnly.epoch (emit_out n e)
@[simp] theorem emit_revoked_v (n : N) (e : Ev) : (n.emit e).revoked = n.revoked := OutOnly.revoked (emit_out n e)
@[simp] theorem emit_me_v (n : N) (e : Ev) : (n.emit e).me = n.me := OutOnly.me (emit_out n e)
@[simp] theorem emit_isHub_v (n : N) (e : Ev) : (n.emit e).isHub = n.isHub := OutOnly.isHub (emit_out n e)
@[simp] theorem emit_homed_v (n : N) (e : Ev) : (n.emit e).homed = n.homed := OutOnly.homed (emit_out n e)
@[simp] theorem emit_left (n : N) (e : Ev) : (n.emit e).left = n.left := OutOnly.left (emit_out n e)
@[simp] theorem emit_recheck (n : N) (e : Ev) : (n.emit e).recheck = n.recheck := OutOnly.recheck (emit_out n e)
@[simp] theorem emit_goneVer (n : N) (e : Ev) : (n.emit e).goneVer = n.goneVer := OutOnly.goneVer (emit_out n e)
@[simp] theorem emit_roster_v (n : N) (e : Ev) : (n.emit e).roster = n.roster := OutOnly.roster (emit_out n e)
@[simp] theorem emit_attached_v (n : N) (e : Ev) : (n.emit e).attached = n.attached := OutOnly.attached (emit_out n e)
@[simp] theorem emit_boot_v (n : N) (e : Ev) : (n.emit e).boot = n.boot := OutOnly.boot (emit_out n e)
@[simp] theorem emit_up_v (n : N) (e : Ev) : (n.emit e).up = n.up := OutOnly.up (emit_out n e)
@[simp] theorem emit_heard_v (n : N) (e : Ev) : (n.emit e).heard = n.heard := OutOnly.heard (emit_out n e)
@[simp] theorem emit_susp_v (n : N) (e : Ev) : (n.emit e).susp = n.susp := OutOnly.susp (emit_out n e)
@[simp] theorem emit_downed_v (n : N) (e : Ev) : (n.emit e).downed = n.downed := OutOnly.downed (emit_out n e)
@[simp] theorem emit_primary (n : N) (e : Ev) : (n.emit e).primary = n.primary := OutOnly.primary (emit_out n e)
@[simp] theorem emit_homeOk (n : N) (e : Ev) : (n.emit e).homeOk = n.homeOk := OutOnly.homeOk (emit_out n e)
@[simp] theorem emit_quietUntil (n : N) (e : Ev) : (n.emit e).quietUntil = n.quietUntil := OutOnly.quietUntil (emit_out n e)
@[simp] theorem emit_born (n : N) (e : Ev) : (n.emit e).born = n.born := OutOnly.born (emit_out n e)
@[simp] theorem trace_hv (n : N) (t : Tr) : (n.trace t).hv = n.hv := OutOnly.hv (trace_out n t)
@[simp] theorem trace_members (n : N) (t : Tr) : (n.trace t).members = n.members := OutOnly.members (trace_out n t)
@[simp] theorem trace_epoch (n : N) (t : Tr) : (n.trace t).epoch = n.epoch := OutOnly.epoch (trace_out n t)
@[simp] theorem trace_revoked_v (n : N) (t : Tr) : (n.trace t).revoked = n.revoked := OutOnly.revoked (trace_out n t)
@[simp] theorem trace_me_v (n : N) (t : Tr) : (n.trace t).me = n.me := OutOnly.me (trace_out n t)
@[simp] theorem trace_isHub_v (n : N) (t : Tr) : (n.trace t).isHub = n.isHub := OutOnly.isHub (trace_out n t)
@[simp] theorem trace_homed_v (n : N) (t : Tr) : (n.trace t).homed = n.homed := OutOnly.homed (trace_out n t)
@[simp] theorem trace_left (n : N) (t : Tr) : (n.trace t).left = n.left := OutOnly.left (trace_out n t)
@[simp] theorem trace_recheck (n : N) (t : Tr) : (n.trace t).recheck = n.recheck := OutOnly.recheck (trace_out n t)
@[simp] theorem trace_goneVer (n : N) (t : Tr) : (n.trace t).goneVer = n.goneVer := OutOnly.goneVer (trace_out n t)
@[simp] theorem trace_roster_v (n : N) (t : Tr) : (n.trace t).roster = n.roster := OutOnly.roster (trace_out n t)
@[simp] theorem trace_attached_v (n : N) (t : Tr) : (n.trace t).attached = n.attached := OutOnly.attached (trace_out n t)
@[simp] theorem trace_boot_v (n : N) (t : Tr) : (n.trace t).boot = n.boot := OutOnly.boot (trace_out n t)
@[simp] theorem trace_up_v (n : N) (t : Tr) : (n.trace t).up = n.up := OutOnly.up (trace_out n t)
@[simp] theorem trace_heard_v (n : N) (t : Tr) : (n.trace t).heard = n.heard := OutOnly.heard (trace_out n t)
@[simp] theorem trace_susp_v (n : N) (t : Tr) : (n.trace t).susp = n.susp := OutOnly.susp (trace_out n t)
@[simp] theorem trace_downed_v (n : N) (t : Tr) : (n.trace t).downed = n.downed := OutOnly.downed (trace_out n t)
@[simp] theorem trace_primary (n : N) (t : Tr) : (n.trace t).primary = n.primary := OutOnly.primary (trace_out n t)
@[simp] theorem trace_homeOk (n : N) (t : Tr) : (n.trace t).homeOk = n.homeOk := OutOnly.homeOk (trace_out n t)
@[simp] theorem trace_quietUntil (n : N) (t : Tr) : (n.trace t).quietUntil = n.quietUntil := OutOnly.quietUntil (trace_out n t)
@[simp] theorem trace_born (n : N) (t : Tr) : (n.trace t).born = n.born := OutOnly.born (trace_out n t)
@[simp] theorem bc_hv (n : N) (b : Bc) : (n.bc b).hv = n.hv := OutOnly.hv (bc_out n b)
@[simp] theorem bc_members (n : N) (b : Bc) : (n.bc b).members = n.members := OutOnly.members (bc_out n b)
@[simp] theorem bc_epoch (n : N) (b : Bc) : (n.bc b).epoch = n.epoch := OutOnly.epoch (bc_out n b)
@[simp] theorem bc_revoked (n : N) (b : Bc) : (n.bc b).revoked = n.revoked := OutOnly.revoked (bc_out n b)
@[simp] theorem bc_me (n : N) (b : Bc) : (n.bc b).me = n.me := OutOnly.me (bc_out n b)
@[simp] theorem bc_isHub (n : N) (b : Bc) : (n.bc b).isHub = n.isHub := OutOnly.isHub (bc_out n b)
@[simp] theorem bc_homed (n : N) (b : Bc) : (n.bc b).homed = n.homed := OutOnly.homed (bc_out n b)
@[simp] theorem bc_left (n : N) (b : Bc) : (n.bc b).left = n.left := OutOnly.left (bc_out n b)
@[simp] theorem bc_recheck (n : N) (b : Bc) : (n.bc b).recheck = n.recheck := OutOnly.recheck (bc_out n b)
@[simp] theorem bc_goneVer (n : N) (b : Bc) : (n.bc b).goneVer = n.goneVer := OutOnly.goneVer (bc_out n b)
@[simp] theorem bc_roster_v (n : N) (b : Bc) : (n.bc b).roster = n.roster := OutOnly.roster (bc_out n b)
@[simp] theorem bc_attached (n : N) (b : Bc) : (n.bc b).attached = n.attached := OutOnly.attached (bc_out n b)
@[simp] theorem bc_boot_v (n : N) (b : Bc) : (n.bc b).boot = n.boot := OutOnly.boot (bc_out n b)
@[simp] theorem bc_up (n : N) (b : Bc) : (n.bc b).up = n.up := OutOnly.up (bc_out n b)
@[simp] theorem bc_heard (n : N) (b : Bc) : (n.bc b).heard = n.heard := OutOnly.heard (bc_out n b)
@[simp] theorem bc_susp (n : N) (b : Bc) : (n.bc b).susp = n.susp := OutOnly.susp (bc_out n b)
@[simp] theorem bc_downed_v (n : N) (b : Bc) : (n.bc b).downed = n.downed := OutOnly.downed (bc_out n b)
@[simp] theorem bc_primary_v (n : N) (b : Bc) : (n.bc b).primary = n.primary := OutOnly.primary (bc_out n b)
@[simp] theorem bc_homeOk (n : N) (b : Bc) : (n.bc b).homeOk = n.homeOk := OutOnly.homeOk (bc_out n b)
@[simp] theorem bc_quietUntil (n : N) (b : Bc) : (n.bc b).quietUntil = n.quietUntil := OutOnly.quietUntil (bc_out n b)
@[simp] theorem bc_born (n : N) (b : Bc) : (n.bc b).born = n.born := OutOnly.born (bc_out n b)
@[simp] theorem tx_hv (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.hv = n.hv := OutOnly.hv (tx_out E n p r f)
@[simp] theorem tx_members (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.members = n.members := OutOnly.members (tx_out E n p r f)
@[simp] theorem tx_epoch (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.epoch = n.epoch := OutOnly.epoch (tx_out E n p r f)
@[simp] theorem tx_revoked_v (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.revoked = n.revoked := OutOnly.revoked (tx_out E n p r f)
@[simp] theorem tx_me_v (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.me = n.me := OutOnly.me (tx_out E n p r f)
@[simp] theorem tx_isHub_v (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.isHub = n.isHub := OutOnly.isHub (tx_out E n p r f)
@[simp] theorem tx_homed_v (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.homed = n.homed := OutOnly.homed (tx_out E n p r f)
@[simp] theorem tx_left (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.left = n.left := OutOnly.left (tx_out E n p r f)
@[simp] theorem tx_recheck (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.recheck = n.recheck := OutOnly.recheck (tx_out E n p r f)
@[simp] theorem tx_goneVer (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.goneVer = n.goneVer := OutOnly.goneVer (tx_out E n p r f)
@[simp] theorem tx_roster_v (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.roster = n.roster := OutOnly.roster (tx_out E n p r f)
@[simp] theorem tx_attached_v (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.attached = n.attached := OutOnly.attached (tx_out E n p r f)
@[simp] theorem tx_boot_v (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.boot = n.boot := OutOnly.boot (tx_out E n p r f)
@[simp] theorem tx_up_v (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.up = n.up := OutOnly.up (tx_out E n p r f)
@[simp] theorem tx_heard_v (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.heard = n.heard := OutOnly.heard (tx_out E n p r f)
@[simp] theorem tx_susp_v (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.susp = n.susp := OutOnly.susp (tx_out E n p r f)
@[simp] theorem tx_downed_v (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.downed = n.downed := OutOnly.downed (tx_out E n p r f)
@[simp] theorem tx_primary (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.primary = n.primary := OutOnly.primary (tx_out E n p r f)
@[simp] theorem tx_homeOk (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.homeOk = n.homeOk := OutOnly.homeOk (tx_out E n p r f)
@[simp] theorem tx_quietUntil (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.quietUntil = n.quietUntil := OutOnly.quietUntil (tx_out E n p r f)
@[simp] theorem tx_born (n : N) (E : Env) (p : Nat) (r : Route) (f : NFrame) : (N.tx E n p r f).1.born = n.born := OutOnly.born (tx_out E n p r f)
@[simp] theorem deltaTo_hv (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).hv = n.hv := OutOnly.hv (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_members (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).members = n.members := OutOnly.members (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_epoch (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).epoch = n.epoch := OutOnly.epoch (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_revoked_v (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).revoked = n.revoked := OutOnly.revoked (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_me_v (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).me = n.me := OutOnly.me (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_isHub_v (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).isHub = n.isHub := OutOnly.isHub (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_homed_v (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).homed = n.homed := OutOnly.homed (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_left (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).left = n.left := OutOnly.left (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_recheck (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).recheck = n.recheck := OutOnly.recheck (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_goneVer (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).goneVer = n.goneVer := OutOnly.goneVer (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_roster_v (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).roster = n.roster := OutOnly.roster (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_attached_v (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).attached = n.attached := OutOnly.attached (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_boot_v (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).boot = n.boot := OutOnly.boot (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_up_v (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).up = n.up := OutOnly.up (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_heard_v (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).heard = n.heard := OutOnly.heard (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_susp_v (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).susp = n.susp := OutOnly.susp (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_downed_v (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).downed = n.downed := OutOnly.downed (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_primary (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).primary = n.primary := OutOnly.primary (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_homeOk (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).homeOk = n.homeOk := OutOnly.homeOk (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_quietUntil (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).quietUntil = n.quietUntil := OutOnly.quietUntil (deltaTo_out E n p m rc a)
@[simp] theorem deltaTo_born (n : N) (E : Env) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo E n p m rc a).born = n.born := OutOnly.born (deltaTo_out E n p m rc a)
@[simp] theorem homeDelta_hv (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).hv = n.hv := OutOnly.hv (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_members (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).members = n.members := OutOnly.members (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_epoch (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).epoch = n.epoch := OutOnly.epoch (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_revoked_v (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).revoked = n.revoked := OutOnly.revoked (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_me_v (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).me = n.me := OutOnly.me (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_isHub_v (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).isHub = n.isHub := OutOnly.isHub (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_homed_v (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).homed = n.homed := OutOnly.homed (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_left (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).left = n.left := OutOnly.left (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_recheck (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).recheck = n.recheck := OutOnly.recheck (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_goneVer (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).goneVer = n.goneVer := OutOnly.goneVer (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_roster_v (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).roster = n.roster := OutOnly.roster (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_attached_v (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).attached = n.attached := OutOnly.attached (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_boot_v (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).boot = n.boot := OutOnly.boot (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_up_v (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).up = n.up := OutOnly.up (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_heard_v (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).heard = n.heard := OutOnly.heard (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_susp_v (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).susp = n.susp := OutOnly.susp (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_downed_v (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).downed = n.downed := OutOnly.downed (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_primary (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).primary = n.primary := OutOnly.primary (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_homeOk (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).homeOk = n.homeOk := OutOnly.homeOk (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_quietUntil (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).quietUntil = n.quietUntil := OutOnly.quietUntil (homeDelta_out E n m rc a)
@[simp] theorem homeDelta_born (n : N) (E : Env) (m : Nat) (rc : Rec) (a : Alive) : (N.homeDelta E n m rc a).born = n.born := OutOnly.born (homeDelta_out E n m rc a)

end Pinc.Membership
