import Vinc.MembershipModelNode

/-!
# The membership machine: structural lemmas

Facts about the model of `crates/vinc-membership` that every property proof uses: the sorted tables, the output
queues and their cap, the view epoch, the one place that sends (`tx`), the cursor loops, and the revocation.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

/-! ## Sorted tables -/

namespace AMap
variable {α : Type}

theorem insert_length_le (m : AMap α) (k : Nat) (v : α) : (m.insert k v).length ≤ m.length + 1 := by
  induction m with
  | nil => simp [insert]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    simp only [insert]
    split
    · simp
    · split
      · simp
      · simp only [List.length_cons]; omega

theorem erase_length_le (m : AMap α) (k : Nat) : (m.erase k).length ≤ m.length := by
  unfold erase; exact List.length_filter_le _ _

theorem get?_erase_self (m : AMap α) (k : Nat) : (m.erase k).get? k = none := by
  unfold erase get?
  simp [List.find?_filter]

theorem has_erase_self (m : AMap α) (k : Nat) : (m.erase k).has k = false := by
  unfold erase has
  simp [List.any_filter]

theorem has_insert_self (m : AMap α) (k : Nat) (v : α) : (m.insert k v).has k = true := by
  unfold has
  induction m with
  | nil => simp [insert]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    simp only [insert]
    split
    · simp
    · rename_i h1
      split
      · simp_all
      · rename_i h2; simp_all [List.any_cons]
end AMap

/-! ## Output queues -/

theorem emit_events_le (n : N) (e : Ev) (h : n.events.length ≤ QUEUE_CAP) : (n.emit e).events.length ≤ QUEUE_CAP := by
  unfold N.emit; split
  · exact h
  · simp; unfold QUEUE_CAP at *; omega

theorem trace_traces_le (n : N) (t : Tr) (h : n.traces.length ≤ QUEUE_CAP) : (n.trace t).traces.length ≤ QUEUE_CAP := by
  unfold N.trace; split
  · exact h
  · split
    · exact h
    · simp; unfold QUEUE_CAP at *; omega

/-- A full queue counts what it drops: nothing is lost silently. -/
theorem emit_full_counts (n : N) (e : Ev) (h : QUEUE_CAP ≤ n.events.length) :
    (n.emit e).lostEvents = n.lostEvents + 1 ∧ (n.emit e).events = n.events := by
  unfold N.emit; simp [h]

theorem trace_off (n : N) (t : Tr) (h : n.tracing = false) : n.trace t = n := by
  unfold N.trace; simp [h]

/-! ## The view epoch -/

theorem bump_epoch (n : N) : n.bump.epoch = n.epoch + 1 := by
  unfold N.bump N.emit; dsimp only; split <;> rfl

theorem bump_members (n : N) : n.bump.members = n.members := by
  unfold N.bump N.emit; dsimp only; split <;> rfl

/-! ## Sending -/

/-- Nothing is sent to a revoked peer or to the node itself. -/
theorem tx_refuses (e : Env) (n : N) (peer : Nat) (r : Route) (f : NFrame) (h : n.revoked.has peer = true ∨ peer = n.me) :
    N.tx e n peer r f = (n, false) := by
  unfold N.tx
  rcases h with h | h <;> simp [h]

theorem tx_snd (e : Env) (n : N) (peer : Nat) (r : Route) (f : NFrame) :
    (N.tx e n peer r f).2 = (!(n.revoked.has peer || peer == n.me) && e.acc.has peer) := by
  unfold N.tx; split
  · rename_i h; simp [h]
  · rename_i h; simp at h; simp [h]

/-- A send only appends to the sent list and the trace; no table changes. -/
theorem tx_tables (e : Env) (n : N) (peer : Nat) (r : Route) (f : NFrame) :
    (N.tx e n peer r f).1.roster = n.roster ∧ (N.tx e n peer r f).1.members = n.members ∧
    (N.tx e n peer r f).1.revoked = n.revoked ∧ (N.tx e n peer r f).1.hv = n.hv := by
  unfold N.tx; split
  · simp
  · unfold N.trace; split <;> (try split) <;> simp

/-! ## Cursor loops -/

/-- A key lies after the cursor. -/
def gt (c : Option Nat) (k : Nat) : Bool := match c with | none => true | some a => decide (a < k)

/-- The first key of `ks` strictly after `after`. -/
def nextL (ks : List Nat) (after : Option Nat) : Option Nat := ks.find? (gt after)

/-- The keys a cursor loop visits over a fixed table, with `fuel` steps. -/
def cursorList (ks : List Nat) : Nat → Option Nat → List Nat
  | 0, _ => []
  | f + 1, c => match nextL ks c with
    | none => []
    | some k => k :: cursorList ks f (some k)

theorem nextKey_eq {α : Type} (m : AMap α) (a : Option Nat) : AMap.nextKey m a = nextL m.keys a := by
  unfold AMap.nextKey nextL AMap.keys
  rw [List.find?_map]
  cases a <;> rfl

theorem filter_next (ks : List Nat) (hs : ks.Pairwise (· < ·)) (c : Option Nat) (k : Nat) (hn : nextL ks c = some k) :
    ks.filter (gt c) = k :: ks.filter (gt (some k)) := by
  induction ks with
  | nil => simp [nextL] at hn
  | cons x r ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨hx, hr⟩ := hs
    by_cases hg : gt c x = true
    · have hk : k = x := by simp [nextL, hg] at hn; exact hn.symm
      subst hk
      rw [List.filter_cons_of_pos hg, List.filter_cons_of_neg (by simp [gt])]
      congr 1
      rw [List.filter_eq_self.mpr, List.filter_eq_self.mpr]
      · intro y hy; simp only [gt, decide_eq_true_eq]; exact hx y hy
      · intro y hy
        have hxy := hx y hy
        cases c with
        | none => rfl
        | some a => simp only [gt, decide_eq_true_eq] at hg ⊢; omega
    · have hg' : gt c x = false := by simpa using hg
      have hn' : nextL r c = some k := by simpa [nextL, List.find?_cons, hg'] using hn
      have hkr : k ∈ r := by
        unfold nextL at hn'; exact List.mem_of_find?_eq_some hn'
      have hxk := hx k hkr
      rw [List.filter_cons_of_neg (by simpa using hg'), List.filter_cons_of_neg (by simp [gt]; omega)]
      exact ih hr hn'

theorem filter_next_none (ks : List Nat) (c : Option Nat) (hn : nextL ks c = none) : ks.filter (gt c) = [] := by
  unfold nextL at hn
  rw [List.find?_eq_none] at hn
  apply List.filter_eq_nil_iff.mpr
  intro x hx; simpa using hn x hx

/-- A cursor loop over a sorted table visits exactly the keys after the cursor, in order, if it has the fuel. -/
theorem cursor_filter (ks : List Nat) (hs : ks.Pairwise (· < ·)) :
    ∀ (f : Nat) (c : Option Nat), (ks.filter (gt c)).length ≤ f → cursorList ks f c = ks.filter (gt c) := by
  intro f
  induction f with
  | zero =>
    intro c h
    have : ks.filter (gt c) = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [cursorList, this]
  | succ f ih =>
    intro c h
    simp only [cursorList]
    cases hn : nextL ks c with
    | none => simp [filter_next_none ks c hn]
    | some k =>
      have e := filter_next ks hs c k hn
      rw [e] at h ⊢
      simp only [List.length_cons] at h
      simp [ih (some k) (by omega)]

/-- The cursor loop of the code over a table equals the loop over its keys at the start, when the fuel is the table
size: this is the shape `forKeys` has. -/
theorem cursor_keys (ks : List Nat) (hs : ks.Pairwise (· < ·)) : cursorList ks ks.length none = ks := by
  have e : ks.filter (gt none) = ks := List.filter_eq_self.mpr (by intro x _; rfl)
  have := cursor_filter ks hs ks.length none (by rw [e]; exact Nat.le_refl _)
  rw [this, e]

/-! ## Revocation -/

/-- `revoke` refuses exactly when the revocation table is full and the member is new: it returns `TableFull`
(`none`) instead of overflowing. -/
theorem revoke_none_iff (e : Env) (n : N) (now m : Nat) :
    N.revoke e n now m = none ↔ (n.revoked.has m = false ∧ MAX_TABLE ≤ n.revoked.len) := by
  unfold N.revoke
  by_cases h : !n.revoked.has m && MAX_TABLE ≤ n.revoked.len
  · simp only [h, if_true]; simp at h; simp [h]
  · simp only [h]; simp at h ⊢
    intro h1; exact h h1

end Vinc.Membership
