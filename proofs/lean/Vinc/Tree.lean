import Vinc.Layout

/-!
# Range verifier

A model of `RangeVerifier` in `vinc-dag/src/tree/verify.rs` as a state machine over a tree whose node values
are abstract hashes. The state is the stack of pending nodes `(cv, lo, hi)`, the sticky failure flag and the
log of released groups. One `feed` is one completed stream item: a parent pair (two chaining values) or a
group (its bytes); the bytes are read according to the kind of the node on top of the stack, so an adversary
chooses a whole `Raw` item and the node decides how it is read. The buffer, partial feeds and the
zero-copy path do not change which items are checked or released, so they are not modelled.

Hashes are a structure of functions, nothing is postulated. The security theorems take collision resistance as a
hypothesis (`CollisionFree`): the leaf hash is injective in (group index, bytes) and the parent hash is
injective in the pair of children, for each root flag.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Vinc.Tree
open Vinc.Layout

section
variable {Cv D : Type} [DecidableEq Cv]

/-- The abstract hash: a leaf hash of (is-root, group index, group bytes), a parent hash of (is-root, left,
right). -/
structure Hash (Cv D : Type) where
  leaf : Bool → Nat → D → Cv
  parent : Bool → Cv → Cv → Cv

/-- Collision resistance on the inputs the verifier hashes: the hypothesis of the security theorems. -/
structure CollisionFree (H : Hash Cv D) : Prop where
  leaf_inj : ∀ b i d i' d', H.leaf b i d = H.leaf b i' d' → i = i' ∧ d = d'
  parent_inj : ∀ b l r l' r', H.parent b l r = H.parent b l' r' → l = l' ∧ r = r'

/-- Whether `[lo, hi)` is the root of the tree of `n` groups (the `is_root` of `complete`). -/
def isRoot (n lo hi : Nat) : Bool := decide (lo = 0 ∧ hi = n)

/-- The genuine chaining value of the node `[lo, hi)` of the tree over `data`. -/
def gcv (H : Hash Cv D) (data : Nat → D) (n : Nat) (lo hi : Nat) : Cv :=
  if h : hi - lo ≥ 2 then
    have h1 := leftGroups_pos (hi - lo) h
    have h2 := leftGroups_lt (hi - lo) h
    H.parent (isRoot n lo hi) (gcv H data n lo (lo + leftGroups (hi - lo)))
      (gcv H data n (lo + leftGroups (hi - lo)) hi)
  else H.leaf (isRoot n lo hi) lo (data lo)
termination_by hi - lo

theorem gcv_parent (H : Hash Cv D) (data : Nat → D) (n lo hi : Nat) (h : hi - lo ≥ 2) :
    gcv H data n lo hi = H.parent (isRoot n lo hi) (gcv H data n lo (lo + leftGroups (hi - lo)))
      (gcv H data n (lo + leftGroups (hi - lo)) hi) := by
  rw [gcv, dif_pos h]

theorem gcv_leaf (H : Hash Cv D) (data : Nat → D) (n lo hi : Nat) (h : ¬ hi - lo ≥ 2) :
    gcv H data n lo hi = H.leaf (isRoot n lo hi) lo (data lo) := by
  rw [gcv, dif_neg h]

/-- A pending node: the chaining value it must hash to, and its group interval. -/
structure Node (Cv : Type) where
  cv : Cv
  lo : Nat
  hi : Nat

/-- One stream item as the verifier can read it: two chaining values (a parent pair) or group bytes. -/
structure Raw (Cv D : Type) where
  l : Cv
  r : Cv
  d : D

/-- The verifier state. -/
structure State (Cv D : Type) where
  stack : List (Node Cv)
  failed : Bool
  released : List (Nat × D)

/-- `RangeVerifier::new` for the group range `[first, last)` of a tree of `n` groups with root `root`. -/
def init (root : Cv) (n first last : Nat) : State Cv D :=
  { stack := if first < last then [⟨root, 0, n⟩] else [], failed := false, released := [] }

/-- `RangeVerifier::feed` for one completed item. -/
def feed (H : Hash Cv D) (n first last : Nat) (s : State Cv D) (it : Raw Cv D) : State Cv D :=
  if s.failed then s else
  match s.stack with
  | [] => s
  | nd :: rest =>
    let root := isRoot n nd.lo nd.hi
    if nd.hi - nd.lo = 1 then
      if H.leaf root nd.lo it.d = nd.cv then
        { s with stack := rest, released := s.released ++ [(nd.lo, it.d)] }
      else { s with failed := true }
    else if H.parent root it.l it.r = nd.cv then
      let mid := nd.lo + leftGroups (nd.hi - nd.lo)
      { s with stack :=
          (if first < mid then [⟨it.l, nd.lo, mid⟩] else []) ++
          (if mid < last then [⟨it.r, mid, nd.hi⟩] else []) ++ rest }
    else { s with failed := true }

/-- Feed a sequence of items. -/
def run (H : Hash Cv D) (n first last : Nat) (s : State Cv D) (items : List (Raw Cv D)) : State Cv D :=
  items.foldl (feed H n first last) s

/-- `is_complete`. -/
def Complete (s : State Cv D) : Prop := s.failed = false ∧ s.stack = []

/-! ## Bookkeeping invariant -/

/-- The group indices of the range that the node covers. -/
def clip (first last : Nat) (nd : Node Cv) : List Nat :=
  List.range' (max nd.lo first) (min nd.hi last - max nd.lo first)

/-- Every pending node is a nonempty interval inside the tree that meets the range, and what has been released
plus what the stack still covers is exactly the requested groups, in order. -/
def Inv (n first last : Nat) (s : State Cv D) : Prop :=
  (∀ nd ∈ s.stack, nd.lo < nd.hi ∧ nd.hi ≤ n ∧ nd.lo < last ∧ first < nd.hi) ∧
  s.released.map Prod.fst ++ s.stack.flatMap (clip first last) = List.range' first (last - first)

theorem flatMap_ite_singleton (f : Node Cv → List Nat) (c : Prop) [Decidable c] (x : Node Cv) :
    List.flatMap f (if c then [x] else []) = if c then f x else [] := by
  by_cases h : c <;> simp [h]

theorem clip_split (first last lo mid hi : Nat) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    (if first < mid then List.range' (max lo first) (min mid last - max lo first) else []) ++
      (if mid < last then List.range' (max mid first) (min hi last - max mid first) else []) =
    List.range' (max lo first) (min hi last - max lo first) := by
  by_cases a : first < mid <;> by_cases b : mid < last
  · simp only [a, b, ite_true]
    have := @List.range'_append (max lo first) (mid - max lo first) (min hi last - mid) 1
    rw [show max lo first + 1 * (mid - max lo first) = mid by omega] at this
    rw [show max mid first = mid by omega, show min mid last = mid by omega, this]
    congr 1
    omega
  · simp only [a, b, ite_true, ite_false, List.append_nil]
    congr 1 <;> omega
  · simp only [a, b, ite_true, ite_false, List.nil_append]
    congr 1 <;> omega
  · simp only [a, b, ite_false, List.append_nil]
    rw [show min hi last - max lo first = 0 by omega]
    rfl

theorem init_inv (root : Cv) (n first last : Nat) (h : last ≤ n) :
    Inv n first last (init root n first last : State Cv D) := by
  unfold init Inv
  by_cases hf : first < last
  · simp only [hf, ite_true]
    refine ⟨?_, ?_⟩
    · intro nd hnd
      simp at hnd
      subst hnd
      simp
      omega
    · simp only [List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, clip]
      congr 1 <;> omega
  · simp only [hf, ite_false]
    refine ⟨by simp, ?_⟩
    simp only [List.map_nil, List.flatMap_nil, List.append_nil]
    rw [show last - first = 0 by omega]
    rfl

theorem feed_inv (H : Hash Cv D) (n first last : Nat) (s : State Cv D) (it : Raw Cv D) (hl : last ≤ n)
    (h : Inv n first last s) : Inv n first last (feed H n first last s it) := by
  obtain ⟨hn, hc⟩ := h
  by_cases hf : s.failed = true
  · have : feed H n first last s it = s := by simp [feed, hf]
    rw [this]; exact ⟨hn, hc⟩
  · rcases hs : s.stack with _ | ⟨nd, rest⟩
    · have : feed H n first last s it = s := by simp [feed, hf, hs]
      rw [this]; exact ⟨hn, hc⟩
    · rw [hs] at hn hc
      have hnd := hn nd (List.mem_cons_self ..)
      have hrest : ∀ x ∈ rest, x.lo < x.hi ∧ x.hi ≤ n ∧ x.lo < last ∧ first < x.hi :=
        fun x hx => hn x (List.mem_cons_of_mem _ hx)
      unfold feed
      simp only [hf, hs, Bool.false_eq_true, ite_false]
      by_cases hleaf : nd.hi - nd.lo = 1
      · simp only [hleaf, ite_true]
        by_cases hh : H.leaf (isRoot n nd.lo nd.hi) nd.lo it.d = nd.cv
        · simp only [hh, ite_true]
          refine ⟨hrest, ?_⟩
          simp only [List.map_append, List.map_cons, List.map_nil, List.flatMap_cons] at hc ⊢
          have hcl : clip first last nd = [nd.lo] := by
            unfold clip
            rw [show max nd.lo first = nd.lo by omega, show min nd.hi last - nd.lo = 1 by omega]
            rfl
          rw [hcl] at hc
          rw [← hc]
          simp
        · simp only [hh, ite_false]
          rw [hs] at *
          exact ⟨by simpa [hs] using hn, by simpa [hs] using hc⟩
      · simp only [hleaf, ite_false]
        by_cases hh : H.parent (isRoot n nd.lo nd.hi) it.l it.r = nd.cv
        · simp only [hh, ite_true]
          have h2 : nd.hi - nd.lo ≥ 2 := by omega
          have h1 := leftGroups_pos _ h2
          have h3 := leftGroups_lt _ h2
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hx
            rcases hx with (⟨hc1, rfl⟩ | ⟨hc1, rfl⟩) | hx
            · simp only; omega
            · simp only; omega
            · exact hrest x hx
          · simp only [List.flatMap_cons, List.flatMap_append, flatMap_ite_singleton] at hc ⊢
            rw [← hc]
            have hsplit := clip_split first last nd.lo (nd.lo + leftGroups (nd.hi - nd.lo)) nd.hi
              (by omega) (by omega)
            simp only [clip] at hsplit ⊢
            rw [← hsplit]
        · simp only [hh, ite_false]
          rw [hs] at *
          exact ⟨by simpa [hs] using hn, by simpa [hs] using hc⟩

/-! ## Genuineness -/

/-- Every pending node carries the genuine chaining value of its interval, and every released group is the
genuine group. -/
def Genuine (H : Hash Cv D) (data : Nat → D) (n : Nat) (s : State Cv D) : Prop :=
  (∀ nd ∈ s.stack, nd.cv = gcv H data n nd.lo nd.hi) ∧ ∀ g ∈ s.released, g.2 = data g.1

theorem init_genuine (H : Hash Cv D) (data : Nat → D) (n first last : Nat) :
    Genuine H data n (init (gcv H data n 0 n) n first last : State Cv D) := by
  unfold init Genuine
  refine ⟨?_, by simp⟩
  intro nd hnd
  by_cases hf : first < last
  · simp only [hf, ite_true, List.mem_singleton] at hnd
    subst hnd; rfl
  · simp [hf] at hnd

theorem feed_genuine (H : Hash Cv D) (cf : CollisionFree H) (data : Nat → D) (n first last : Nat)
    (s : State Cv D) (it : Raw Cv D) (hI : Inv n first last s) (hG : Genuine H data n s) :
    Genuine H data n (feed H n first last s it) := by
  obtain ⟨hn, _⟩ := hI
  obtain ⟨hg1, hg2⟩ := hG
  by_cases hf : s.failed = true
  · have : feed H n first last s it = s := by simp [feed, hf]
    rw [this]; exact ⟨hg1, hg2⟩
  · rcases hs : s.stack with _ | ⟨nd, rest⟩
    · have : feed H n first last s it = s := by simp [feed, hf, hs]
      rw [this]; exact ⟨hg1, hg2⟩
    · rw [hs] at hn hg1
      have hnd := hn nd (List.mem_cons_self ..)
      have hcv := hg1 nd (List.mem_cons_self ..)
      have hrest : ∀ x ∈ rest, x.cv = gcv H data n x.lo x.hi := fun x hx => hg1 x (List.mem_cons_of_mem _ hx)
      unfold feed
      simp only [hf, hs, Bool.false_eq_true, ite_false]
      by_cases hleaf : nd.hi - nd.lo = 1
      · simp only [hleaf, ite_true]
        by_cases hh : H.leaf (isRoot n nd.lo nd.hi) nd.lo it.d = nd.cv
        · simp only [hh, ite_true]
          rw [gcv_leaf H data n _ _ (by omega)] at hcv
          have := (cf.leaf_inj _ _ _ _ _ (hh.trans hcv)).2
          refine ⟨hrest, ?_⟩
          intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact hg2 g hg
          · simp at hg; subst hg; exact this
        · simp only [hh, ite_false]
          exact ⟨by simpa [hs] using hg1, hg2⟩
      · simp only [hleaf, ite_false]
        by_cases hh : H.parent (isRoot n nd.lo nd.hi) it.l it.r = nd.cv
        · simp only [hh, ite_true]
          have h2 : nd.hi - nd.lo ≥ 2 := by omega
          rw [gcv_parent H data n _ _ h2] at hcv
          obtain ⟨e1, e2⟩ := cf.parent_inj _ _ _ _ _ (hh.trans hcv)
          refine ⟨?_, hg2⟩
          intro x hx
          simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hx
          rcases hx with (⟨hc1, rfl⟩ | ⟨hc1, rfl⟩) | hx
          · exact e1
          · exact e2
          · exact hrest x hx
        · simp only [hh, ite_false]
          exact ⟨by simpa [hs] using hg1, hg2⟩

theorem run_inv (H : Hash Cv D) (n first last : Nat) (hl : last ≤ n) (data : Nat → D) (items : List (Raw Cv D)) :
    ∀ s : State Cv D, Inv n first last s → Genuine H data n s → CollisionFree H →
      Inv n first last (run H n first last s items) ∧ Genuine H data n (run H n first last s items) := by
  induction items with
  | nil => intro s h g _; exact ⟨h, g⟩
  | cons it t ih =>
    intro s h g cf
    exact ih _ (feed_inv H n first last s it hl h) (feed_genuine H cf data n first last s it h g) cf

/-! ## The theorems -/

variable (H : Hash Cv D) (data : Nat → D) (n first last : Nat)

/-- The state after feeding any items to a verifier started at the genuine root. -/
abbrev runGen (items : List (Raw Cv D)) : State Cv D :=
  run H n first last (init (gcv H data n 0 n) n first last) items

/-- (a) Given the genuine root and collision resistance, every released group is the genuine group at its
index, whatever items the adversary feeds. -/
theorem released_genuine (cf : CollisionFree H) (hl : last ≤ n) (items : List (Raw Cv D)) :
    ∀ g ∈ (runGen H data n first last items).released, g.2 = data g.1 :=
  ((run_inv H n first last hl data items _ (init_inv _ n first last hl) (init_genuine H data n first last) cf).2).2

theorem run_inv_only (hl : last ≤ n) (items : List (Raw Cv D)) :
    ∀ s : State Cv D, Inv n first last s → Inv n first last (run H n first last s items) := by
  induction items with
  | nil => intro s h; exact h
  | cons it t ih => intro s h; exact ih _ (feed_inv H n first last s it hl h)

/-- The bookkeeping identity holds after any items, for any root: what is released plus what the stack still
covers is exactly `[first, last)`, in order. -/
theorem run_bookkeeping (hl : last ≤ n) (root : Cv) (items : List (Raw Cv D)) :
    let s := run H n first last (init root n first last) items
    s.released.map Prod.fst ++ s.stack.flatMap (clip first last) = List.range' first (last - first) :=
  (run_inv_only H n first last hl items _ (init_inv root n first last hl)).2

/-- (b) Releases come in strictly ascending order of group index. -/
theorem released_ascending (hl : last ≤ n) (root : Cv) (items : List (Raw Cv D)) :
    (run H n first last (init root n first last) items).released.map Prod.fst |>.Pairwise (· < ·) := by
  have h := run_bookkeeping H n first last hl root items
  simp only at h
  have hp : (List.range' first (last - first)).Pairwise (· < ·) := List.pairwise_lt_range'
  rw [← h] at hp
  exact hp.sublist (List.sublist_append_left _ _)

/-- Every released group lies in the requested range. -/
theorem released_in_range (hl : last ≤ n) (root : Cv) (items : List (Raw Cv D)) :
    ∀ g ∈ (run H n first last (init root n first last) items).released, first ≤ g.1 ∧ g.1 < last := by
  intro g hg
  have h := run_bookkeeping H n first last hl root items
  simp only at h
  have : g.1 ∈ List.range' first (last - first) := by
    rw [← h]; exact List.mem_append_left _ (List.mem_map_of_mem hg)
  simp [List.mem_range'_1] at this
  omega

/-- (b) At completion the verifier has released exactly the groups of the requested range, in order. -/
theorem complete_releases_range (hl : last ≤ n) (root : Cv) (items : List (Raw Cv D))
    (hc : Complete (run H n first last (init root n first last) items)) :
    (run H n first last (init root n first last) items).released.map Prod.fst = List.range' first (last - first) := by
  have h := run_bookkeeping H n first last hl root items
  simp only [hc.2, List.flatMap_nil, List.append_nil] at h
  exact h

/-- A failed verifier stays failed and unchanged: every later feed returns the same state. -/
theorem feed_failed (s : State Cv D) (it : Raw Cv D) (h : s.failed = true) : feed H n first last s it = s := by
  simp [feed, h]

/-- A rejected item releases nothing: the failing step leaves the released list as it was. -/
theorem feed_reject_releases_nothing (s : State Cv D) (it : Raw Cv D) (hs : s.failed = false)
    (hf : (feed H n first last s it).failed = true) :
    (feed H n first last s it).released = s.released := by
  rcases hst : s.stack with _ | ⟨nd, rest⟩
  · simp [feed, hs, hst] at hf
  · unfold feed at hf ⊢
    simp only [hs, hst, Bool.false_eq_true, ite_false] at hf ⊢
    by_cases hleaf : nd.hi - nd.lo = 1
    · simp only [hleaf, ite_true] at hf ⊢
      by_cases hh : H.leaf (isRoot n nd.lo nd.hi) nd.lo it.d = nd.cv
      · simp [hh] at hf
      · simp [hh]
    · simp only [hleaf, ite_false] at hf ⊢
      by_cases hh : H.parent (isRoot n nd.lo nd.hi) it.l it.r = nd.cv
      · simp [hh] at hf
      · simp [hh]

/-- A group is released only when its bytes hash to the chaining value committed by verified parents. -/
theorem feed_release_verified (s : State Cv D) (it : Raw Cv D) (nd : Node Cv) (rest : List (Node Cv))
    (hs : s.failed = false) (hst : s.stack = nd :: rest)
    (hr : (feed H n first last s it).released ≠ s.released) :
    nd.hi - nd.lo = 1 ∧ H.leaf (isRoot n nd.lo nd.hi) nd.lo it.d = nd.cv ∧
      (feed H n first last s it).released = s.released ++ [(nd.lo, it.d)] := by
  unfold feed at hr ⊢
  simp only [hs, hst, Bool.false_eq_true, ite_false] at hr ⊢
  by_cases hleaf : nd.hi - nd.lo = 1
  · simp only [hleaf, ite_true] at hr ⊢
    by_cases hh : H.leaf (isRoot n nd.lo nd.hi) nd.lo it.d = nd.cv
    · simp [hh]
    · simp [hh] at hr
  · simp only [hleaf, ite_false] at hr
    by_cases hh : H.parent (isRoot n nd.lo nd.hi) it.l it.r = nd.cv <;> simp [hh] at hr

/-- The whole story for a byte range: for a value of `len` bytes in groups of `1024 << log`, a request for
bytes `[s, e)` and the genuine root, whatever items the adversary feeds, every released group is the genuine
group, and once the verifier completes it has released exactly the groups that intersect the request. -/
theorem verifier_correct (cf : CollisionFree H) (len log s e : Nat) (hse : s < e) (hel : e ≤ len)
    (first last : Nat) (hr : groupRange len log s e = some (first, last))
    (items : List (Raw Cv D)) :
    let n := groups len log
    let st := run H n first last (init (gcv H data n 0 n) n first last) items
    (∀ g ∈ st.released, g.2 = data g.1) ∧
    (Complete st → ∀ k, k ∈ st.released.map Prod.fst ↔
      (k * groupLen log < e ∧ s < (k + 1) * groupLen log)) := by
  obtain ⟨a, b, hab, hlt, hbn, hiff⟩ := groupRange_spec len log s e hse hel
  rw [hr] at hab
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hab)
  intro n st
  refine ⟨released_genuine H data n first last cf hbn items, ?_⟩
  intro hc k
  have := complete_releases_range H n first last hbn (gcv H data n 0 n) items hc
  rw [this, List.mem_range'_1, ← hiff k]
  omega

end

end Vinc.Tree

#audit_axioms Vinc.Tree.released_genuine
#audit_axioms Vinc.Tree.released_ascending
#audit_axioms Vinc.Tree.complete_releases_range
#audit_axioms Vinc.Tree.feed_failed
#audit_axioms Vinc.Tree.feed_reject_releases_nothing
#audit_axioms Vinc.Tree.feed_release_verified
#audit_axioms Vinc.Tree.verifier_correct
