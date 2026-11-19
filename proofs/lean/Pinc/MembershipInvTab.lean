import Pinc.MembershipHubFrame

/-!
# Property 9, part 1: bounded sorted tables and the invariant `Inv`

Every table of a node (`roster`, `attached`, `homed`, `susp`, `downed`, `revoked`, `up`, `members`, `recheck`,
`left`, `goneVer`, each hub copy's `entries`) is a sorted association list of at most `MAX_TABLE` entries (`Bnd`);
`hv` holds at most `MAX_HUBS` copies; the tables `heard`, `hrtt`, `hsent`, `helloAt` only have keys among the
bootstrap hubs `B` (the node's `boot`, which never changes), which are at most `MAX_HUBS` and distinct (`KBnd`); the event and trace queues hold at most
`QUEUE_CAP` records (a full queue counts what it drops in `lostEvents` / `lostTraces`, the one extra `Lost` record
is produced by `drainEvents` / `drainTraces` and is not queued). The lists `outSent`, `outBc`, `outClose` are the
effects of the calls since they were last taken (the host consumes them after every call); they are not tables
of the node and are not bounded here.

This file has the table lemmas (an insert behind its guard, an erase and an update keep a table bounded and
sorted); the other files prove `Inv` for the steps and the calls.
-/

set_option linter.unusedVariables false

namespace Pinc.Membership
open Pinc.MemInc

/-! ## Sorted tables -/

namespace AMap
variable {α : Type}

theorem mem_keys_insert (m : AMap α) (k : Nat) (v : α) (x : Nat) : x ∈ (m.insert k v).keys ↔ x = k ∨ x ∈ m.keys := by
  induction m with
  | nil => simp [insert, keys]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    simp only [insert, keys] at *
    split
    · simp
    · rename_i h1
      split
      · rename_i h2
        have : k = a := by simpa using h2
        subst this; simp
      · simp only [List.map_cons, List.mem_cons, ih]; exact or_left_comm

theorem sorted_insert (m : AMap α) (k : Nat) (v : α) (h : m.keys.Pairwise (· < ·)) :
    (m.insert k v).keys.Pairwise (· < ·) := by
  induction m with
  | nil => simp [insert, keys]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    have h' : (∀ y ∈ AMap.keys r, a < y) ∧ (AMap.keys r).Pairwise (· < ·) := by
      simpa [keys, List.pairwise_cons] using h
    obtain ⟨h1, h2⟩ := h'
    simp only [insert]
    split
    · rename_i hk
      simp only [keys, List.map_cons, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at *
      refine ⟨⟨hk, fun y hy => Nat.lt_trans hk (h1 y hy)⟩, h1, h2⟩
    · rename_i hk
      split
      · rename_i he
        have : k = a := by simpa using he
        subst this
        simp only [keys, List.map_cons, List.pairwise_cons] at *
        exact ⟨h1, h2⟩
      · rename_i he
        have hak : a < k := by
          have : k ≠ a := by simpa using he
          omega
        have := ih h2
        simp only [keys, List.map_cons, List.pairwise_cons] at *
        refine ⟨fun y hy => ?_, this⟩
        have := (mem_keys_insert r k v y).1 hy
        rcases this with rfl | hy
        · exact hak
        · exact h1 y hy

theorem insert_length_of_has (m : AMap α) (k : Nat) (v : α) (h : m.keys.Pairwise (· < ·)) (hk : m.has k = true) :
    (m.insert k v).length ≤ m.length := by
  induction m with
  | nil => simp [has] at hk
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    have h' : (∀ y ∈ AMap.keys r, a < y) ∧ (AMap.keys r).Pairwise (· < ·) := by
      simpa [keys, List.pairwise_cons] using h
    obtain ⟨h1, h2⟩ := h'
    simp only [insert]
    split
    · rename_i hlt
      exfalso
      simp only [has, List.any_cons, Bool.or_eq_true, beq_iff_eq] at hk
      rcases hk with hk | hk
      · omega
      · obtain ⟨q, hq, hqk⟩ := List.any_eq_true.1 hk
        have := h1 q.1 (List.mem_map.2 ⟨q, hq, rfl⟩)
        simp at hqk; omega
    · split
      · simp
      · rename_i hlt he
        have hne : a ≠ k := by intro e; subst e; simp at he
        have hk' : AMap.has r k = true := by
          simp only [has, List.any_cons, Bool.or_eq_true, beq_iff_eq] at hk
          rcases hk with hk | hk
          · exact absurd hk hne
          · exact hk
        have := ih h2 hk'
        simp only [List.length_cons]; omega

theorem sorted_erase (m : AMap α) (k : Nat) (h : m.keys.Pairwise (· < ·)) : (m.erase k).keys.Pairwise (· < ·) := by
  unfold erase keys at *
  exact List.Pairwise.sublist (List.Sublist.map _ (List.filter_sublist)) h

theorem keys_erase_sub (m : AMap α) (k : Nat) : (m.erase k).keys ⊆ m.keys := by
  unfold erase keys; exact (List.Sublist.map _ List.filter_sublist).subset

theorem keys_modify (m : AMap α) (k : Nat) (f : α → α) : (m.modify k f).keys = m.keys := by
  unfold modify keys
  rw [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  split <;> rfl

theorem length_modify (m : AMap α) (k : Nat) (f : α → α) : (m.modify k f).length = m.length := by
  unfold modify; exact List.length_map _

theorem mem_of_get? (m : AMap α) (k : Nat) (v : α) (h : m.get? k = some v) : (k, v) ∈ m := by
  unfold get? at h
  cases hf : m.find? (fun p => p.1 == k) with
  | none => simp [hf] at h
  | some q =>
    simp [hf] at h
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    obtain ⟨q1, q2⟩ := q
    simp at h2; subst h2; simp at h; subst h; exact h1

theorem has_of_get? (m : AMap α) (k : Nat) (v : α) (h : m.get? k = some v) : m.has k = true := by
  have := mem_of_get? m k v h
  unfold has
  exact List.any_eq_true.2 ⟨_, this, by simp⟩

theorem mem_insert (m : AMap α) (k : Nat) (v : α) (p : Nat × α) (h : p ∈ m.insert k v) : p = (k, v) ∨ p ∈ m := by
  induction m with
  | nil => simp [insert] at h; exact Or.inl h
  | cons q r ih =>
    obtain ⟨a, b⟩ := q
    simp only [insert] at h
    split at h
    · simp at h; rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
      · exact Or.inr (by simp [h])
    · split at h
      · simp at h; rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])
      · simp at h; rcases h with h | h
        · exact Or.inr (by simp [h])
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (by simp [h])

theorem mem_erase (m : AMap α) (k : Nat) (p : Nat × α) (h : p ∈ m.erase k) : p ∈ m := by
  unfold erase at h; exact (List.mem_filter.1 h).1
end AMap

/-! ## Bounded tables -/

/-- A table of at most `MAX_TABLE` entries, sorted by key. -/
def Bnd {α : Type} (m : AMap α) : Prop := m.keys.Pairwise (· < ·) ∧ m.length ≤ MAX_TABLE

/-- A table sorted by key whose keys all lie in `b`. -/
def KBnd {α : Type} (m : AMap α) (b : List Nat) : Prop := m.keys.Pairwise (· < ·) ∧ ∀ k ∈ m.keys, k ∈ b

/-- The hub copies: sorted, at most `MAX_HUBS`, each with a bounded entry table. -/
def HvB (hv : AMap HubCopy) : Prop := hv.keys.Pairwise (· < ·) ∧ hv.length ≤ MAX_HUBS ∧ ∀ p ∈ hv, Bnd p.2.entries

namespace Bnd
variable {α : Type} {m : AMap α}

theorem nil : Bnd ([] : AMap α) := by simp [Bnd, AMap.keys, MAX_TABLE]

/-- An insert behind its guard: room in the table, or the key is already there. -/
theorem insert (h : Bnd m) (k : Nat) (v : α) (g : m.length < MAX_TABLE ∨ m.has k = true) : Bnd (m.insert k v) := by
  refine ⟨AMap.sorted_insert m k v h.1, ?_⟩
  rcases g with g | g
  · have := AMap.insert_length_le m k v; omega
  · have := AMap.insert_length_of_has m k v h.1 g; have := h.2; omega

theorem insert_lt (h : Bnd m) (k : Nat) (v : α) (g : m.length < MAX_TABLE) : Bnd (m.insert k v) := h.insert k v (Or.inl g)
theorem insert_has (h : Bnd m) (k : Nat) (v : α) (g : m.has k = true) : Bnd (m.insert k v) := h.insert k v (Or.inr g)

theorem erase (h : Bnd m) (k : Nat) : Bnd (m.erase k) :=
  ⟨AMap.sorted_erase m k h.1, Nat.le_trans (AMap.erase_length_le m k) h.2⟩

theorem modify (h : Bnd m) (k : Nat) (f : α → α) : Bnd (m.modify k f) := by
  refine ⟨by rw [AMap.keys_modify]; exact h.1, ?_⟩
  rw [AMap.length_modify]; exact h.2

/-- A table filtered by any test (`retain`). -/
theorem filter (h : Bnd m) (f : Nat × α → Bool) : Bnd (m.filter f) := by
  refine ⟨?_, Nat.le_trans (List.length_filter_le _ _) h.2⟩
  have h1 := h.1
  unfold AMap.keys at h1 ⊢
  exact List.Pairwise.sublist (List.Sublist.map _ List.filter_sublist) h1

/-- `entry(k).or_insert(v)` behind the guard of an insert. -/
theorem orIns (h : Bnd m) (k : Nat) (v : α) (g : m.length < MAX_TABLE ∨ m.has k = true) : Bnd (m.orIns k v) := by
  unfold AMap.orIns
  split
  · exact h
  · exact h.insert k v g

/-- A table whose values change and whose keys stay. -/
theorem map_keys {β : Type} (h : Bnd m) (f : Nat × α → Nat × β) (hf : ∀ p, (f p).1 = p.1) : Bnd (m.map f) := by
  have hk : AMap.keys (m.map f) = AMap.keys m := by
    unfold AMap.keys
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    simp only [Function.comp]
    exact hf p
  exact ⟨by rw [hk]; exact h.1, by rw [List.length_map]; exact h.2⟩
end Bnd

namespace KBnd
variable {α : Type} {m : AMap α} {b : List Nat}

theorem nil : KBnd ([] : AMap α) b := by simp [KBnd, AMap.keys]

theorem insert (h : KBnd m b) (k : Nat) (v : α) (hk : k ∈ b) : KBnd (m.insert k v) b := by
  refine ⟨AMap.sorted_insert m k v h.1, fun x hx => ?_⟩
  rcases (AMap.mem_keys_insert m k v x).1 hx with rfl | hx
  · exact hk
  · exact h.2 x hx

theorem erase (h : KBnd m b) (k : Nat) : KBnd (m.erase k) b := by
  exact ⟨AMap.sorted_erase m k h.1, fun x hx => h.2 x (AMap.keys_erase_sub m k hx)⟩

theorem modify (h : KBnd m b) (k : Nat) (f : α → α) : KBnd (m.modify k f) b := by
  refine ⟨by rw [AMap.keys_modify]; exact h.1, by rw [AMap.keys_modify]; exact h.2⟩

theorem unset {m : AMap (Option Nat)} (h : KBnd m b) (k : Nat) : KBnd (m.unset k) b := h.modify k _

/-- The table is no longer than the (distinct) keys it may hold. -/
theorem length_le (h : KBnd m b) (hb : b.Nodup) : m.length ≤ b.length := by
  have hn : m.keys.Nodup := h.1.imp (fun {a b} h => Nat.ne_of_lt h)
  have := hn.length_le_of_subset (fun x hx => h.2 x hx)
  simpa [AMap.keys] using this
end KBnd

namespace HvB
variable {hv : AMap HubCopy}

theorem nil : HvB [] := by simp [HvB, AMap.keys]

theorem insert (h : HvB hv) (k : Nat) (c : HubCopy) (hc : Bnd c.entries) (g : hv.length < MAX_HUBS ∨ hv.has k = true) :
    HvB (hv.insert k c) := by
  refine ⟨AMap.sorted_insert hv k c h.1, ?_, ?_⟩
  · rcases g with g | g
    · have := AMap.insert_length_le hv k c; omega
    · have := AMap.insert_length_of_has hv k c h.1 g; have := h.2.1; omega
  · intro p hp
    rcases AMap.mem_insert hv k c p hp with rfl | hp
    · exact hc
    · exact h.2.2 p hp

theorem erase (h : HvB hv) (k : Nat) : HvB (hv.erase k) :=
  ⟨AMap.sorted_erase hv k h.1, Nat.le_trans (AMap.erase_length_le hv k) h.2.1, fun p hp => h.2.2 p (AMap.mem_erase hv k p hp)⟩

theorem entries (h : HvB hv) (k : Nat) (c : HubCopy) (hc : hv.get? k = some c) : Bnd c.entries :=
  h.2.2 (k, c) (AMap.mem_of_get? hv k c hc)

/-- Replace every copy's entries by an erased table (`revoke`). -/
theorem map_erase (h : HvB hv) (member : Nat) :
    HvB (hv.map (fun (p : Nat × HubCopy) => (p.1, { p.2 with entries := p.2.entries.erase member }))) := by
  refine ⟨?_, ?_, ?_⟩
  · have : AMap.keys (hv.map (fun (p : Nat × HubCopy) => (p.1, { p.2 with entries := p.2.entries.erase member }))) = hv.keys := by
      unfold AMap.keys; rw [List.map_map]; rfl
    rw [this]; exact h.1
  · rw [List.length_map]; exact h.2.1
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact (h.2.2 q hq).erase member
end HvB

/-! ## The invariant -/

/-- Property 9 for one node whose bootstrap hubs are `B`: every table within its capacity. -/
structure Inv (B : List Nat) (n : N) : Prop where
  roster : Bnd n.roster
  attached : Bnd n.attached
  homed : Bnd n.homed
  susp : Bnd n.susp
  downed : Bnd n.downed
  revoked : Bnd n.revoked
  up : Bnd n.up
  members : Bnd n.members
  recheck : Bnd n.recheck
  left : Bnd n.left
  goneVer : Bnd n.goneVer
  heard : KBnd n.heard B
  hrtt : KBnd n.hrtt B
  hsent : KBnd n.hsent B
  helloAt : KBnd n.helloAt B
  hv : HvB n.hv
  bootEq : n.boot = B
  bootLen : B.length ≤ MAX_HUBS
  bootNodup : B.Nodup
  events : n.events.length ≤ QUEUE_CAP
  traces : n.traces.length ≤ QUEUE_CAP

/-- Close every field of `Inv` that the update left alone. -/
macro "inv_keep " h:term : tactic =>
  `(tactic| (constructor <;> first
    | exact ($h).roster | exact ($h).attached | exact ($h).homed | exact ($h).susp | exact ($h).downed
    | exact ($h).revoked | exact ($h).up | exact ($h).members | exact ($h).recheck | exact ($h).left
    | exact ($h).goneVer | exact ($h).heard | exact ($h).hrtt | exact ($h).hsent | exact ($h).helloAt
    | exact ($h).hv | exact ($h).bootEq | exact ($h).bootLen | exact ($h).bootNodup | exact ($h).events
    | exact ($h).traces | skip))

/-- The length bounds of the boot-keyed tables. -/
theorem Inv.heard_len {B : List Nat} {n : N} (h : Inv B n) : n.heard.length ≤ MAX_HUBS := Nat.le_trans (h.heard.length_le h.bootNodup) h.bootLen
theorem Inv.hrtt_len {B : List Nat} {n : N} (h : Inv B n) : n.hrtt.length ≤ MAX_HUBS := Nat.le_trans (h.hrtt.length_le h.bootNodup) h.bootLen
theorem Inv.hsent_len {B : List Nat} {n : N} (h : Inv B n) : n.hsent.length ≤ MAX_HUBS := Nat.le_trans (h.hsent.length_le h.bootNodup) h.bootLen
theorem Inv.helloAt_len {B : List Nat} {n : N} (h : Inv B n) : n.helloAt.length ≤ MAX_HUBS := Nat.le_trans (h.helloAt.length_le h.bootNodup) h.bootLen

end Pinc.Membership
