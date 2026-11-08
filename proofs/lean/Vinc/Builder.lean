import Vinc.Encode

/-!
# Outboard builder

A model of `OutboardBuilder` in `vinc-dag/src/tree/builder.rs`: a binary counter over the groups, with the
hash abstract as in `Tree` (the leaf hash of group `i` is `H.leaf (isRoot) i (data i)`, a merge is
`H.parent (isRoot) left right`). After each group the builder pushes that group's chaining value and, while the
two entries on top have the same size, merges them into a parent of twice the size; `finish` merges what is
left from the right. Every merge writes the parent's 64-byte pair at the slot `preorder_index(groups, lo, hi)`
of the outboard (here: it appends a `Write` to a log).

Main theorem `builder_correct`: for a tree of `n >= 2` groups the builder writes, for each slot `0 .. n-2`,
exactly the pair of the parent that `Layout.pre` puts at that slot, every parent is written once (`n - 1`
writes), every write lands on its pre-order slot, and the root the builder returns is the genuine root.
`builder_correct_one` covers a single group (no parents, the root is the leaf hash). The empty value is the
constant hash of the empty input in both the builder and the verifier and has no tree.

Assumed: the BLAKE3 hasher the builder uses per group (`update` over pieces, `set_input_offset`,
`finalize_non_root`) and the merges (`merge_subtrees_non_root`, `merge_subtrees_root`) compute the abstract
`leaf` and `parent` values the verifier checks; that is the same assumption as in `Tree`, and it is what the
hash round trip tests (`root == blake3::hash`, verifier accepts the builder's outboard) check on real data.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Vinc.Builder
open Vinc.Layout Vinc.Tree Vinc.Encode

/-! ## Arithmetic of the binary counter -/

theorem leftGroups_eq (c a : Nat) (h1 : 2 ^ a < c) (h2 : c ≤ 2 ^ (a + 1)) : leftGroups c = 2 ^ a := by
  have hc : 2 ≤ c := by have := Nat.two_pow_pos a; omega
  obtain ⟨m, hm⟩ := leftGroups_pow c hc
  have hmax := leftGroups_max c hc a h1
  have hlt := leftGroups_lt c hc
  rw [hm] at hmax hlt ⊢
  have h3 : a ≤ m := (Nat.pow_le_pow_iff_right (show 1 < 2 by omega)).1 hmax
  have h4 : m < a + 1 := by
    refine Classical.byContradiction fun h => ?_
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show a + 1 ≤ m by omega)
    omega
  congr 1; omega

/-- An aligned block of `2^j` groups inside a tree is a node of it. -/
theorem sub_pow : ∀ (T nlo a j : Nat), nlo ≤ a → a + 2 ^ j ≤ nlo + T → 2 ^ j ∣ (a - nlo) →
    Sub nlo (nlo + T) a (a + 2 ^ j) := by
  intro T
  induction T using Nat.strongRecOn with
  | _ T ih =>
    intro nlo a j h1 h2 h3
    have hp := Nat.two_pow_pos j
    by_cases hT : T = 2 ^ j
    · have : a = nlo := by omega
      subst this
      rw [hT]
      exact Sub.refl _ _
    · have hT2 : 2 ^ j < T := by omega
      have e : nlo + T - nlo = T := by omega
      have hge : nlo + T - nlo ≥ 2 := by omega
      have hL := leftGroups_max T (by omega) j hT2
      have hLlt := leftGroups_lt T (by omega)
      have hLpos := leftGroups_pos T (by omega)
      obtain ⟨m, hm⟩ := leftGroups_pow T (by omega)
      have hjm : j ≤ m := (Nat.pow_le_pow_iff_right (show 1 < 2 by omega)).1 (by rw [← hm]; exact hL)
      have hdvd : 2 ^ j ∣ leftGroups T := by rw [hm]; exact Nat.pow_dvd_pow 2 hjm
      by_cases hc : a + 2 ^ j ≤ nlo + leftGroups T
      · have := ih (leftGroups T) (by omega) nlo a j h1 hc h3
        exact Sub.left hge (by rw [e]; exact this)
      · have hge2 : nlo + leftGroups T ≤ a := by
          refine Classical.byContradiction fun hlt => ?_
          obtain ⟨p, hp'⟩ := h3
          obtain ⟨u, hu⟩ := hdvd
          have hlt' : 2 ^ j * p < 2 ^ j * u := by omega
          have := Nat.lt_of_mul_lt_mul_left hlt'
          have := Nat.mul_le_mul_left (2 ^ j) (show p + 1 ≤ u by omega)
          rw [Nat.mul_succ] at this
          omega
        have hd2 : 2 ^ j ∣ a - (nlo + leftGroups T) := by
          have : a - (nlo + leftGroups T) = (a - nlo) - leftGroups T := by omega
          rw [this]; exact Nat.dvd_sub h3 hdvd
        have := ih (T - leftGroups T) (by omega) (nlo + leftGroups T) a j hge2 (by omega) hd2
        have e2 : nlo + leftGroups T + (T - leftGroups T) = nlo + T := by omega
        rw [e2] at this
        exact Sub.right hge (by rw [e]; exact this)

/-- The nodes `[nhi - T mod 2^t, nhi)` along the right edge of a tree are its nodes. -/
theorem sub_spine : ∀ (T nlo t : Nat), 0 < T % 2 ^ t → Sub nlo (nlo + T) (nlo + T - T % 2 ^ t) (nlo + T) := by
  intro T
  induction T using Nat.strongRecOn with
  | _ T ih =>
    intro nlo t h0
    by_cases hlt : T < 2 ^ t
    · rw [Nat.mod_eq_of_lt hlt, show nlo + T - T = nlo by omega]
      exact Sub.refl _ _
    · have hp := Nat.two_pow_pos t
      have hT : 2 ^ t < T := by
        have := Nat.mod_lt T hp
        refine Classical.byContradiction fun h => ?_
        have : T = 2 ^ t := by omega
        rw [this, Nat.mod_self] at h0
        omega
      have e : nlo + T - nlo = T := by omega
      have hge : nlo + T - nlo ≥ 2 := by omega
      have hLlt := leftGroups_lt T (by omega)
      have hLpos := leftGroups_pos T (by omega)
      have h2L := le_two_leftGroups T (by omega)
      obtain ⟨m, hm⟩ := leftGroups_pow T (by omega)
      have htm : t ≤ m := by
        refine Classical.byContradiction fun h => ?_
        have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show m + 1 ≤ t by omega)
        rw [Nat.pow_succ] at this
        omega
      obtain ⟨u, hu⟩ : 2 ^ t ∣ leftGroups T := by rw [hm]; exact Nat.pow_dvd_pow 2 htm
      have hmod : T % 2 ^ t = (T - leftGroups T) % 2 ^ t := by
        rw [Nat.mul_comm] at hu
        have : T = (T - leftGroups T) + u * 2 ^ t := by omega
        conv => lhs; rw [this]
        exact Nat.add_mul_mod_self_right _ _ _
      rw [hmod] at h0 ⊢
      have := ih (T - leftGroups T) (by omega) (nlo + leftGroups T) t h0
      have e2 : nlo + leftGroups T + (T - leftGroups T) = nlo + T := by omega
      rw [e2] at this
      exact Sub.right hge (by rw [e]; exact this)

/-- A duplicate-free list inside another of no more elements covers it. -/
theorem nodup_cover {α : Type} [DecidableEq α] : ∀ (l1 l2 : List α), l1.Nodup → (∀ a ∈ l1, a ∈ l2) →
    l2.length ≤ l1.length → ∀ x ∈ l2, x ∈ l1 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ _ hl x hx
    cases l2 with
    | nil => exact absurd hx (by simp)
    | cons => simp at hl
  | cons a t ih =>
    intro l2 hnd hsub hl x hx
    have ha : a ∈ l2 := hsub a (List.mem_cons_self ..)
    have hnd' := List.nodup_cons.1 hnd
    have := ih (l2.erase a) hnd'.2 (fun b hb => List.mem_erase_of_ne (by
        rintro rfl; exact hnd'.1 hb) |>.2 (hsub b (List.mem_cons_of_mem _ hb)))
      (by rw [List.length_erase_of_mem ha]; simp at hl; omega)
    by_cases hxa : x = a
    · simp [hxa]
    · exact List.mem_cons_of_mem _ (this x ((List.mem_erase_of_ne hxa).2 hx))


/-! ## The builder -/

section
variable {Cv D : Type} [DecidableEq Cv]

/-- One parent written to the outboard: its node and its pair of chaining values. -/
structure Write (Cv : Type) where
  lo : Nat
  hi : Nat
  l : Cv
  r : Cv

/-- The builder state: the stack of `(chaining value, size in groups)` (top first), the log of writes in
order, and the root cell. -/
structure BS (Cv : Type) where
  stack : List (Cv × Nat)
  w : List (Write Cv)
  root : Cv

/-- `Builder::parent` followed by the push of the merged entry: write the pair, store the root when the node is
the whole tree. -/
def BS.write (H : Hash Cv D) (n : Nat) (s : BS Cv) (lo hi : Nat) (l r : Cv) (rest : List (Cv × Nat))
    (size : Nat) : BS Cv :=
  { stack := (H.parent (isRoot n lo hi) l r, size) :: rest, w := s.w ++ [⟨lo, hi, l, r⟩],
    root := if isRoot n lo hi then H.parent (isRoot n lo hi) l r else s.root }

/-- One iteration of the merge loop of `complete_group` after `k` groups: merge the two top entries when they
have the same size. -/
def mergeTop (H : Hash Cv D) (n k : Nat) (s : BS Cv) : Option (BS Cv) :=
  match s.stack with
  | (r, rs) :: (l, ls) :: rest => if rs = ls then some (s.write H n (k - 2 * rs) k l r rest (2 * rs)) else none
  | _ => none

/-- The merge loop; each iteration shortens the stack, so its length is enough fuel. -/
def merge (H : Hash Cv D) (n k : Nat) : Nat → BS Cv → BS Cv
  | 0, s => s
  | f + 1, s => match mergeTop H n k s with
    | some s' => merge H n k f s'
    | none => s

/-- `complete_group` for the `k`-th group (index `k - 1`): a single group is the root, otherwise push the
group's chaining value and run the merge loop. -/
def groupStep (H : Hash Cv D) (data : Nat → D) (n k : Nat) (s : BS Cv) : BS Cv :=
  let leaf := H.leaf (isRoot n (k - 1) k) (k - 1) (data (k - 1))
  if n = 1 then { s with root := leaf }
  else merge H n k (s.stack.length + 1) { s with stack := (leaf, 1) :: s.stack }

/-- The state after the first `k` groups (`c0` is the initial root cell). -/
def mainPhase (H : Hash Cv D) (data : Nat → D) (n : Nat) (c0 : Cv) : Nat → BS Cv
  | 0 => ⟨[], [], c0⟩
  | k + 1 => groupStep H data n (k + 1) (mainPhase H data n c0 k)

/-- One iteration of the loop of `finish`: merge the two top entries into the node that ends at the last
group. -/
def finishTop (H : Hash Cv D) (n : Nat) (s : BS Cv) : Option (BS Cv) :=
  match s.stack with
  | (r, rs) :: (l, ls) :: rest => some (s.write H n (n - (ls + rs)) n l r rest (ls + rs))
  | _ => none

def finish (H : Hash Cv D) (n : Nat) : Nat → BS Cv → BS Cv
  | 0, s => s
  | f + 1, s => match finishTop H n s with
    | some s' => finish H n f s'
    | none => s

/-- The whole builder for a value of `n` groups. -/
def build (H : Hash Cv D) (data : Nat → D) (n : Nat) (c0 : Cv) : BS Cv :=
  finish H n (mainPhase H data n c0 n).stack.length (mainPhase H data n c0 n)

/-! ## Invariants -/

/-- The stack of the builder after `k` groups: the binary decomposition of `k`. Entries are `(cv, size)`, top
first; sizes are powers of two growing downwards, they tile `[0, k)` from the bottom, each entry starts at a
multiple of its size, and its value is the genuine chaining value of its interval. -/
inductive Dec (H : Hash Cv D) (data : Nat → D) (n : Nat) : Nat → List (Cv × Nat) → Prop
  | nil : Dec H data n 0 []
  | cons {k' k : Nat} {cv : Cv} {s : Nat} {rest : List (Cv × Nat)} :
      Dec H data n k' rest → (∃ a, s = 2 ^ a) → s ∣ k' → (∀ c t, rest.head? = some (c, t) → s < t) →
      k = k' + s → cv = gcv H data n k' k → Dec H data n k ((cv, s) :: rest)

theorem Dec.nil_k {H : Hash Cv D} {data : Nat → D} {n k : Nat} (h : Dec H data n k []) : k = 0 := by
  cases h; rfl

theorem Dec.end_dvd {H : Hash Cv D} {data : Nat → D} {n k t : Nat} {cv : Cv} {rest : List (Cv × Nat)}
    (h : Dec H data n k ((cv, t) :: rest)) : t ∣ k := by
  cases h with
  | cons _ _ hd _ hk _ => rw [hk]; exact Nat.dvd_add hd (Nat.dvd_refl _)

/-- The size of the top entry; 0 for an empty stack. -/
def topSize : List (Cv × Nat) → Nat
  | [] => 0
  | (_, s) :: _ => s

theorem Dec.top_le {H : Hash Cv D} {data : Nat → D} {n k : Nat} {st : List (Cv × Nat)}
    (h : Dec H data n k st) : topSize st ≤ k := by
  cases h with
  | nil => simp [topSize]
  | cons _ _ _ _ hk _ => simp [topSize]; omega

/-- Two distinct powers of two: twice the smaller still divides, and is at most, the larger. -/
theorem pow2_lt {s t : Nat} (hs : ∃ a, s = 2 ^ a) (ht : ∃ b, t = 2 ^ b) (h : s < t) : 2 * s ∣ t ∧ 2 * s ≤ t := by
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, rfl⟩ := ht
  have hab : a < b := by
    refine Classical.byContradiction fun hh => ?_
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show b ≤ a by omega)
    omega
  refine ⟨?_, ?_⟩
  · rw [← Nat.pow_succ']; exact Nat.pow_dvd_pow 2 hab
  · rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by omega) hab

/-- The sort key of a write: by end, then by size. Strictly increasing along the log. -/
def keyOf (n : Nat) (w : Write Cv) : Nat := w.hi * (n + 1) + (w.hi - w.lo)

/-- A write is the genuine pair of a parent node of the tree. -/
def WGood (H : Hash Cv D) (data : Nat → D) (n : Nat) (w : Write Cv) : Prop :=
  Sub 0 n w.lo w.hi ∧ 2 ≤ w.hi - w.lo ∧ w.l = gcv H data n w.lo (w.lo + leftGroups (w.hi - w.lo)) ∧
    w.r = gcv H data n (w.lo + leftGroups (w.hi - w.lo)) w.hi

/-- What the log and the root cell satisfy after `k` groups, on top of the stack shape. -/
structure WInv (H : Hash Cv D) (data : Nat → D) (n k : Nat) (c0 : Cv) (s : BS Cv) : Prop where
  good : ∀ w ∈ s.w, WGood H data n w ∧ w.hi ≤ k
  sorted : (s.w.map (keyOf n)).Pairwise (· < ·)
  bound : ∀ w ∈ s.w, keyOf n w ≤ k * (n + 1) + topSize s.stack
  count : s.w.length + s.stack.length = k
  root : (s.root = c0 ∧ ∀ w ∈ s.w, ¬ (w.lo = 0 ∧ w.hi = n)) ∨ s.root = gcv H data n 0 n

/-- A merge writes a genuine parent, keeps the log sorted and counted, and sets the root cell right. -/
theorem write_inv (H : Hash Cv D) (data : Nat → D) (n k : Nat) (c0 : Cv) (s : BS Cv) (r l : Cv) (rs ls : Nat)
    (rest : List (Cv × Nat)) (lo size : Nat) (hst : s.stack = (r, rs) :: (l, ls) :: rest)
    (hI : WInv H data n k c0 s) (hrs : 0 < rs) (hsz : rs < size) (hlo : lo + size = k)
    (hg : WGood H data n ⟨lo, k, l, r⟩) : WInv H data n k c0 (s.write H n lo k l r rest size) := by
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  simp only at hg2 hg3 hg4
  have hpar : H.parent (isRoot n lo k) l r = gcv H data n lo k := by
    rw [gcv_parent H data n lo k hg2, hg3, hg4]
  have hbound := hI.bound
  have hcount := hI.count
  simp only [hst, topSize, List.length_cons] at hbound hcount
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    simp only [BS.write, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hI.good w hw
    · exact ⟨⟨hg1, hg2, hg3, hg4⟩, Nat.le_refl _⟩
  · simp only [BS.write, List.map_append, List.map_cons, List.map_nil]
    refine List.pairwise_append.2 ⟨hI.sorted, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    rw [List.mem_singleton] at hb
    subst hb
    have := hbound w hw
    simp only [keyOf] at this ⊢
    omega
  · intro w hw
    simp only [BS.write, topSize, List.mem_append, List.mem_singleton] at hw ⊢
    rcases hw with hw | rfl
    · have := hbound w hw; omega
    · simp only [keyOf]; omega
  · simp only [BS.write, List.length_append, List.length_cons, List.length_nil]
    omega
  · simp only [BS.write]
    by_cases hr : isRoot n lo k = true
    · right
      simp only [hr, ite_true]
      have : lo = 0 ∧ k = n := by simpa [isRoot] using hr
      obtain ⟨rfl, rfl⟩ := this
      rw [hr] at hpar
      exact hpar
    · have hnr : ¬ (lo = 0 ∧ k = n) := by simpa [isRoot] using hr
      simp only [hr, ite_false, Bool.false_eq_true]
      rcases hI.root with ⟨h1, h2⟩ | h
      · refine Or.inl ⟨h1, ?_⟩
        intro w hw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact h2 w hw
        · exact hnr
      · exact Or.inr h
  
/-- The stack while the merge loop runs: a valid decomposition below, and a top entry that may have the size of
the one below it. -/
def Top (H : Hash Cv D) (data : Nat → D) (n k : Nat) (st : List (Cv × Nat)) : Prop :=
  ∃ cv s k' rest, st = (cv, s) :: rest ∧ Dec H data n k' rest ∧ (∃ a, s = 2 ^ a) ∧ s ∣ k' ∧
    (∀ c t, rest.head? = some (c, t) → s ≤ t) ∧ k = k' + s ∧ cv = gcv H data n k' k

theorem Dec.top {H : Hash Cv D} {data : Nat → D} {n k : Nat} {cv : Cv} {s : Nat} {rest : List (Cv × Nat)}
    (h : Dec H data n k ((cv, s) :: rest)) : Top H data n k ((cv, s) :: rest) := by
  cases h with
  | cons h1 h2 h3 h4 h5 h6 =>
    exact ⟨_, _, _, _, rfl, h1, h2, h3, fun c t ht => Nat.le_of_lt (h4 c t ht), h5, h6⟩

theorem Dec.head_pow2 {H : Hash Cv D} {data : Nat → D} {n k t : Nat} {c : Cv} {rest : List (Cv × Nat)}
    (h : Dec H data n k ((c, t) :: rest)) : ∃ b, t = 2 ^ b := by
  cases h with
  | cons _ hh _ _ _ _ => exact hh

/-- Below an entry of size `s` whose neighbour is larger, everything ends at a multiple of `2 * s` and is at
least `2 * s` large. -/
theorem Dec.double {H : Hash Cv D} {data : Nat → D} {n k s : Nat} {rest : List (Cv × Nat)}
    (hd : Dec H data n k rest) (hs : ∃ a, s = 2 ^ a) (hlt : ∀ c t, rest.head? = some (c, t) → s < t) :
    2 * s ∣ k ∧ ∀ c t, rest.head? = some (c, t) → 2 * s ≤ t := by
  cases rest with
  | nil => exact ⟨by rw [hd.nil_k]; exact Nat.dvd_zero _, by simp⟩
  | cons e rest2 =>
    obtain ⟨c, t⟩ := e
    have ht := hd.head_pow2
    have hp := pow2_lt hs ht (hlt c t rfl)
    refine ⟨Nat.dvd_trans hp.1 hd.end_dvd, ?_⟩
    intro c' t' h'
    simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact hp.2

/-- A merge keeps the stack shape and the log invariants. -/
theorem mergeTop_some (H : Hash Cv D) (data : Nat → D) (n k : Nat) (c0 : Cv) (hk : k ≤ n) (s s1 : BS Cv)
    (h : mergeTop H n k s = some s1) (hT : Top H data n k s.stack) (hI : WInv H data n k c0 s) :
    Top H data n k s1.stack ∧ WInv H data n k c0 s1 ∧ s1.stack.length + 1 = s.stack.length := by
  unfold mergeTop at h
  rcases hst : s.stack with _ | ⟨⟨r, rs⟩, st1⟩
  · simp [hst] at h
  rcases st1 with _ | ⟨⟨l, ls⟩, rest⟩
  · simp [hst] at h
  simp only [hst] at h
  by_cases hq : rs = ls
  · simp only [hq, ite_true, Option.some.injEq] at h
    subst h
    obtain ⟨cv, s0, k', rest0, heq, hdec, hp2, hdvd, hle, hkk, hcv⟩ := hT
    rw [hst] at heq
    simp only [List.cons.injEq, Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    cases hdec with
    | @cons k'' _ l _ _ hd2 hp2' hdvd' hlt hk2 hl =>
      subst hq
      obtain ⟨a, ha⟩ := hp2
      obtain ⟨hdv, hhead⟩ := hd2.double ⟨a, ha⟩ hlt
      have hrs : 0 < rs := by rw [ha]; exact Nat.two_pow_pos a
      have hL : leftGroups (2 * rs) = rs := by
        have := leftGroups_eq (2 * rs) a (by rw [ha]; have := Nat.two_pow_pos a; omega)
          (by rw [ha, Nat.pow_succ]; omega)
        rw [this, ha]
      have e2 : k - 2 * rs = k'' := by omega
      have hmid : k'' + rs = k' := by omega
      have hsub : Sub 0 n k'' k := by
        have := sub_pow n 0 k'' (a + 1) (Nat.zero_le _) (by rw [Nat.pow_succ]; omega)
          (by rw [Nat.sub_zero, Nat.pow_succ, ← ha, Nat.mul_comm]; exact hdv)
        rw [Nat.zero_add, Nat.pow_succ, ← ha, Nat.mul_comm] at this
        rwa [show k'' + 2 * rs = k by omega] at this
      have hgd : WGood H data n ⟨k - 2 * rs, k, l, r⟩ := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · show Sub 0 n (k - 2 * rs) k
          rw [e2]; exact hsub
        · show 2 ≤ k - (k - 2 * rs); omega
        · show l = gcv H data n (k - 2 * rs) ((k - 2 * rs) + leftGroups (k - (k - 2 * rs)))
          rw [e2, show k - k'' = 2 * rs by omega, hL, hmid, hl]
        · show r = gcv H data n ((k - 2 * rs) + leftGroups (k - (k - 2 * rs))) k
          rw [e2, show k - k'' = 2 * rs by omega, hL, hmid, hcv]
      have hcvk : H.parent (isRoot n (k - 2 * rs) k) l r = gcv H data n k'' k := by
        have := gcv_parent H data n k'' k (by omega)
        rw [this, show k - k'' = 2 * rs by omega, hL, hmid, ← hl, ← hcv, e2]
      refine ⟨⟨_, 2 * rs, k'', rest, rfl, hd2, ⟨a + 1, by rw [Nat.pow_succ, ← ha]; omega⟩, hdv, hhead,
        by omega, hcvk⟩, ?_, ?_⟩
      · exact write_inv H data n k c0 s r l rs rs rest (k - 2 * rs) (2 * rs) hst hI hrs (by omega) (by omega) hgd
      · simp [BS.write]
  · simp [hq] at h

/-- A stack with no equal top pair is a valid decomposition. -/
theorem top_dec (H : Hash Cv D) (data : Nat → D) (n k : Nat) (s : BS Cv) (hm : mergeTop H n k s = none)
    (hT : Top H data n k s.stack) : Dec H data n k s.stack := by
  obtain ⟨cv, s0, k', rest, heq, hdec, hp2, hdvd, hle, hkk, hcv⟩ := hT
  rw [heq]
  refine Dec.cons hdec hp2 hdvd ?_ hkk hcv
  intro c t ht
  cases rest with
  | nil => simp at ht
  | cons e rest2 =>
    obtain ⟨c', t'⟩ := e
    simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    have hle' := hle c' t' rfl
    refine Nat.lt_of_le_of_ne hle' ?_
    rintro rfl
    unfold mergeTop at hm
    simp [heq] at hm

/-- The merge loop ends in a valid decomposition and keeps the log invariants. -/
theorem merge_inv (H : Hash Cv D) (data : Nat → D) (n k : Nat) (c0 : Cv) (hk : k ≤ n) :
    ∀ (f : Nat) (s : BS Cv), s.stack.length ≤ f → Top H data n k s.stack → WInv H data n k c0 s →
      Dec H data n k (merge H n k f s).stack ∧ WInv H data n k c0 (merge H n k f s) := by
  intro f
  induction f with
  | zero =>
    intro s hl hT _
    obtain ⟨cv, s0, k', rest, heq, _⟩ := hT
    rw [heq] at hl
    simp at hl
  | succ f ih =>
    intro s hl hT hI
    simp only [merge]
    rcases hm : mergeTop H n k s with _ | s1
    · exact ⟨top_dec H data n k s hm hT, hI⟩
    · obtain ⟨h1, h2, h3⟩ := mergeTop_some H data n k c0 hk s s1 hm hT hI
      exact ih s1 (by omega) h1 h2

theorem groupStep_inv (H : Hash Cv D) (data : Nat → D) (n k : Nat) (c0 : Cv) (hn : 2 ≤ n) (hk : k ≤ n)
    (hk1 : 1 ≤ k) (s : BS Cv) (hD : Dec H data n (k - 1) s.stack) (hI : WInv H data n (k - 1) c0 s) :
    Dec H data n k (groupStep H data n k s).stack ∧ WInv H data n k c0 (groupStep H data n k s) := by
  have hn1 : n ≠ 1 := by omega
  simp only [groupStep, hn1, ite_false]
  refine merge_inv H data n k c0 hk _ _ (Nat.le_refl _) ?_ ?_
  · refine ⟨_, 1, k - 1, s.stack, rfl, hD, ⟨0, rfl⟩, Nat.one_dvd _, ?_, by omega, ?_⟩
    · intro c t ht
      cases hst : s.stack with
      | nil => rw [hst] at ht; simp at ht
      | cons e rest =>
        obtain ⟨c', t'⟩ := e
        rw [hst] at ht hD
        simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        obtain ⟨b, hb⟩ := hD.head_pow2
        rw [hb]; exact Nat.two_pow_pos b
    · rw [gcv_leaf H data n _ _ (by omega)]
  · obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hD hI ⊢
    have hmul : (k0 + 1) * (n + 1) = k0 * (n + 1) + (n + 1) := by rw [Nat.succ_mul]
    have htop := hD.top_le
    refine ⟨?_, hI.sorted, ?_, ?_, hI.root⟩
    · intro w hw
      have := hI.good w hw
      exact ⟨this.1, by omega⟩
    · intro w hw
      have := hI.bound w hw
      simp only [topSize]
      omega
    · have := hI.count
      simp only [List.length_cons]
      omega

theorem mainPhase_inv (H : Hash Cv D) (data : Nat → D) (n : Nat) (c0 : Cv) (hn : 2 ≤ n) :
    ∀ k, k ≤ n → Dec H data n k (mainPhase H data n c0 k).stack ∧ WInv H data n k c0 (mainPhase H data n c0 k) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Dec.nil, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [mainPhase, topSize]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    exact groupStep_inv H data n (k + 1) c0 hn hk (by omega) _ (by simpa using h1) (by simpa using h2)

/-- The state of the finish loop: the log invariants, the chain on top (a merged run of the smallest entries,
ending at the last group, smaller than the entry below) and a valid decomposition below it. -/
def FinInv (H : Hash Cv D) (data : Nat → D) (n : Nat) (c0 : Cv) (s : BS Cv) : Prop :=
  WInv H data n n c0 s ∧ ∃ cv S st2, s.stack = (cv, S) :: st2 ∧ Dec H data n (n - S) st2 ∧
    cv = gcv H data n (n - S) n ∧ 0 < S ∧ S ≤ n ∧ ∀ c t, st2.head? = some (c, t) → S < t

theorem finishTop_some (H : Hash Cv D) (data : Nat → D) (n : Nat) (c0 : Cv) (s s1 : BS Cv)
    (h : finishTop H n s = some s1) (hF : FinInv H data n c0 s) :
    FinInv H data n c0 s1 ∧ s1.stack.length + 1 = s.stack.length := by
  unfold finishTop at h
  obtain ⟨hI, cv, S, st2, hst, hdec, hcv, hS0, hSn, hSlt⟩ := hF
  rcases hs : s.stack with _ | ⟨⟨r, rs⟩, st1⟩
  · simp [hs] at h
  rcases st1 with _ | ⟨⟨l, ls⟩, rest⟩
  · simp [hs] at h
  simp only [hs, Option.some.injEq] at h
  subst h
  rw [hs] at hst
  simp only [List.cons.injEq, Prod.mk.injEq] at hst
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hst
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 = n - rs := ⟨_, rfl⟩
  rw [← hk0] at hdec
  cases hdec with
  | @cons k'' _ cvl _ _ hd2 hp2 hdvd hlt hk2 hcvl =>
    obtain ⟨a, ha⟩ := hp2
    have hSls : rs < ls := hSlt l ls rfl
    have hdv : 2 * ls ∣ k'' := (hd2.double ⟨a, ha⟩ hlt).1
    have hhead := (hd2.double ⟨a, ha⟩ hlt).2
    have hls : 0 < ls := by rw [ha]; exact Nat.two_pow_pos a
    have hL : leftGroups (ls + rs) = ls := by
      have := leftGroups_eq (ls + rs) a (by omega) (by rw [Nat.pow_succ, ← ha]; omega)
      rw [this]; exact ha.symm
    have e1 : n - (ls + rs) = k'' := by omega
    have e2 : n - rs = k0 := by omega
    have hsub : Sub 0 n k'' n := by
      obtain ⟨m, hm⟩ := hdv
      have hmod : n % 2 ^ (a + 1) = ls + rs := by
        have h2 : 2 ^ (a + 1) = 2 * ls := by rw [Nat.pow_succ, ← ha]; omega
        rw [h2, show n = (ls + rs) + (2 * ls) * m by rw [← hm]; omega]
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      have := sub_spine n 0 (a + 1) (by rw [hmod]; omega)
      rw [hmod, Nat.zero_add, e1] at this
      exact this
    have hgd : WGood H data n ⟨n - (ls + rs), n, l, r⟩ := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · show Sub 0 n (n - (ls + rs)) n
        rw [e1]; exact hsub
      · show 2 ≤ n - (n - (ls + rs)); omega
      · show l = gcv H data n (n - (ls + rs)) ((n - (ls + rs)) + leftGroups (n - (n - (ls + rs))))
        rw [show n - (n - (ls + rs)) = ls + rs by omega, hL, e1, show k'' + ls = k0 by omega, hcvl]
      · show r = gcv H data n ((n - (ls + rs)) + leftGroups (n - (n - (ls + rs)))) n
        rw [show n - (n - (ls + rs)) = ls + rs by omega, hL, e1, show k'' + ls = k0 by omega, ← e2, hcv]
    have hcvn : H.parent (isRoot n (n - (ls + rs)) n) l r = gcv H data n k'' n := by
      have := gcv_parent H data n k'' n (by omega)
      rw [e1, this, show n - k'' = ls + rs by omega, hL, show k'' + ls = k0 by omega, hcvl, ← e2, ← hcv]
    refine ⟨⟨write_inv H data n n c0 s r l rs ls rest (n - (ls + rs)) (ls + rs) hs hI hS0 (by omega) (by omega) hgd,
      _, ls + rs, rest, rfl, ?_, ?_, by omega, by omega, ?_⟩, by simp [BS.write]⟩
    · rw [show n - (ls + rs) = k'' by omega]; exact hd2
    · rw [e1] at hcvn ⊢; exact hcvn
    · intro c t ht; have := hhead c t ht; omega

theorem finish_inv (H : Hash Cv D) (data : Nat → D) (n : Nat) (c0 : Cv) :
    ∀ (f : Nat) (s : BS Cv), s.stack.length ≤ f → FinInv H data n c0 s →
      WInv H data n n c0 (finish H n f s) ∧ (finish H n f s).stack = [(gcv H data n 0 n, n)] := by
  intro f
  induction f with
  | zero =>
    intro s hl hF
    obtain ⟨_, cv, S, st2, hst, _⟩ := hF
    rw [hst] at hl; simp at hl
  | succ f ih =>
    intro s hl hF
    simp only [finish]
    rcases hm : finishTop H n s with _ | s1
    · obtain ⟨hI, cv, S, st2, hst, hdec, hcv, hS0, hSn, hSlt⟩ := hF
      have hst2 : st2 = [] := by
        cases st2 with
        | nil => rfl
        | cons e rest =>
          obtain ⟨l, ls⟩ := e
          unfold finishTop at hm
          simp [hst] at hm
      subst hst2
      have := hdec.nil_k
      have hSn' : S = n := by omega
      subst hSn'
      refine ⟨hI, ?_⟩
      rw [hst, hcv]
      simp
    · obtain ⟨h1, h2⟩ := finishTop_some H data n c0 s s1 hm hF
      exact ih s1 (by omega) h1

/-! ## The result -/

/-- Every parent of a subtree lies inside it and has at least two groups. -/
theorem pre_bounds (lo hi : Nat) : ∀ x ∈ pre lo hi, lo ≤ x.1 ∧ x.1 + 2 ≤ x.2 ∧ x.2 ≤ hi := by
  generalize hn : hi - lo = n
  induction n using Nat.strongRecOn generalizing lo hi with
  | _ n ih =>
    by_cases h : n ≥ 2
    · have h1 := leftGroups_pos (hi - lo) (by omega)
      have h2 := leftGroups_lt (hi - lo) (by omega)
      rw [pre_unfold lo hi (by omega)]
      intro x hx
      simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · simp only; omega
      · have := ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (by omega) x hx
        omega
      · have := ih (n - leftGroups (hi - lo)) (by omega) (lo + leftGroups (hi - lo)) hi (by omega) x hx
        omega
    · rw [pre_small lo hi (by omega)]; simp

/-- The parents of a subtree are pairwise distinct, so a node has one pre-order position. -/
theorem pre_nodup (lo hi : Nat) : (pre lo hi).Nodup := by
  generalize hn : hi - lo = n
  induction n using Nat.strongRecOn generalizing lo hi with
  | _ n ih =>
    by_cases h : n ≥ 2
    · have h1 := leftGroups_pos (hi - lo) (by omega)
      have h2 := leftGroups_lt (hi - lo) (by omega)
      rw [pre_unfold lo hi (by omega)]
      refine List.nodup_cons.2 ⟨?_, List.nodup_append.2 ⟨?_, ?_, ?_⟩⟩
      · intro hm
        rcases List.mem_append.1 hm with hm | hm
        · have := pre_bounds _ _ _ hm; simp only at this; omega
        · have := pre_bounds _ _ _ hm; simp only at this; omega
      · exact ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (by omega)
      · exact ih (n - leftGroups (hi - lo)) (by omega) (lo + leftGroups (hi - lo)) hi (by omega)
      · intro a ha b hb heq
        have h3 := pre_bounds _ _ _ ha
        have h4 := pre_bounds _ _ _ hb
        subst heq
        omega
    · rw [pre_small lo hi (by omega)]; exact List.nodup_nil

/-- (Builder.) For a tree of `n >= 2` groups, the builder
* returns the genuine root,
* writes `n - 1` parents, no node twice and every parent of the tree once (`Layout.pre`),
* writes each at its pre-order slot: `preorder_index` of the node finds exactly that node in the pre-order
  list of parents, and the pair written is the pair of the genuine chaining values of its two children. -/
theorem builder_correct (H : Hash Cv D) (data : Nat → D) (n : Nat) (c0 : Cv) (hn : 2 ≤ n) :
    let b := build H data n c0
    b.root = gcv H data n 0 n ∧ b.w.length = n - 1 ∧
    (∀ w ∈ b.w, (pre 0 n)[preorderIndex n w.lo w.hi]? = some (w.lo, w.hi) ∧
      w.l = gcv H data n w.lo (w.lo + leftGroups (w.hi - w.lo)) ∧
      w.r = gcv H data n (w.lo + leftGroups (w.hi - w.lo)) w.hi) ∧
    (∀ nd ∈ pre 0 n, ∃ w ∈ b.w, (w.lo, w.hi) = nd) ∧
    (b.w.map fun w => (w.lo, w.hi)).Nodup := by
  intro b
  obtain ⟨hD, hI⟩ := mainPhase_inv H data n c0 hn n (Nat.le_refl _)
  -- the start of the finish loop
  have hF : FinInv H data n c0 (mainPhase H data n c0 n) := by
    refine ⟨hI, ?_⟩
    obtain ⟨K, hK⟩ : ∃ K, K = n := ⟨n, rfl⟩
    have hD2 : Dec H data n K (mainPhase H data n c0 n).stack := by rw [hK]; exact hD
    rcases hst : (mainPhase H data n c0 n).stack with _ | ⟨⟨cv, S⟩, st2⟩
    · rw [hst] at hD2; have := hD2.nil_k; omega
    · rw [hst] at hD2
      cases hD2 with
      | @cons k' _ _ _ _ hd2 hp2 hdvd hlt hk2 hcv' =>
        refine ⟨cv, S, st2, rfl, ?_, ?_, ?_, ?_, hlt⟩
        · rw [show n - S = k' by omega]; exact hd2
        · rw [show n - S = k' by omega, hcv', hK]
        · obtain ⟨a, ha⟩ := hp2; rw [ha]; exact Nat.two_pow_pos a
        · omega
  obtain ⟨hI2, hst2⟩ := finish_inv H data n c0 _ _ (Nat.le_refl _) hF
  have hb : b = finish H n (mainPhase H data n c0 n).stack.length (mainPhase H data n c0 n) := rfl
  rw [← hb] at hI2 hst2
  have hlen : b.w.length = n - 1 := by
    have := hI2.count
    rw [hst2] at this
    simp at this
    omega
  have hgood := hI2.good
  have hnodes : (b.w.map fun w => (w.lo, w.hi)).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    have := hI2.sorted
    rw [List.pairwise_map] at this ⊢
    refine this.imp ?_
    intro a c hlt heq
    simp only [keyOf] at hlt
    simp only [Prod.mk.injEq] at heq
    rw [heq.1, heq.2] at hlt
    omega
  have hsub : ∀ a ∈ b.w.map (fun w => (w.lo, w.hi)), a ∈ pre 0 n := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    obtain ⟨⟨hs, h2, _, _⟩, _⟩ := hgood w hw
    exact List.mem_of_getElem? (preorderIndex_correct hs h2)
  have hcover : ∀ nd ∈ pre 0 n, ∃ w ∈ b.w, (w.lo, w.hi) = nd := by
    intro nd hnd
    have := nodup_cover _ _ hnodes hsub (by rw [pre_length]; simp [hlen]) nd hnd
    obtain ⟨w, hw, h⟩ := List.mem_map.1 this
    exact ⟨w, hw, h⟩
  refine ⟨?_, hlen, ?_, hcover, hnodes⟩
  · rcases hI2.root with ⟨_, hnone⟩ | h
    · exfalso
      have h0 : ((0, n) : Nat × Nat) ∈ pre 0 n := by rw [pre_unfold 0 n (by omega)]; simp
      obtain ⟨w, hw, hwn⟩ := hcover _ h0
      simp only [Prod.mk.injEq] at hwn
      exact hnone w hw hwn
    · exact h
  · intro w hw
    obtain ⟨⟨hs, h2, hl, hr⟩, _⟩ := hgood w hw
    exact ⟨preorderIndex_correct hs h2, hl, hr⟩

/-- In a list without duplicates an element has one position. -/
theorem nodup_idx_inj {α : Type} : ∀ (l : List α), l.Nodup → ∀ (i j : Nat) (x : α), l[i]? = some x → l[j]? = some x → i = j := by
  intro l
  induction l with
  | nil => intro _ i j x h _; simp at h
  | cons a t ih =>
    intro hnd i j x hi hj
    have hnd' := List.nodup_cons.1 hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        simp only [List.getElem?_cons_succ] at hj
        exact absurd (List.mem_of_getElem? hj) hnd'.1
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [List.getElem?_cons_succ] at hi
        exact absurd (List.mem_of_getElem? hi) hnd'.1
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi hj
        exact congrArg (· + 1) (ih hnd'.2 i j x hi hj)

/-- Against any genuine outboard: every slot `idx < n - 1` is written, and everything written to it is the
outboard's pair. -/
theorem builder_outboard (H : Hash Cv D) (data : Nat → D) (n : Nat) (c0 : Cv) (hn : 2 ≤ n)
    (ob : Nat → Cv × Cv) (hob : GenuineOb H data n ob) :
    let b := build H data n c0
    ∀ idx, idx < n - 1 →
      (∃ w ∈ b.w, preorderIndex n w.lo w.hi = idx) ∧
      ∀ w ∈ b.w, preorderIndex n w.lo w.hi = idx → (w.l, w.r) = ob idx := by
  intro b idx hidx
  obtain ⟨_, hlen, hw, hcover, _⟩ := builder_correct H data n c0 hn
  have hl : idx < (pre 0 n).length := by rw [pre_length]; omega
  have hget := List.getElem?_eq_getElem hl
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hwm, hwn⟩ := hcover _ (List.getElem_mem hl)
    refine ⟨w, hwm, ?_⟩
    obtain ⟨h1, _, _⟩ := hw w hwm
    rw [hwn] at h1
    exact nodup_idx_inj _ (pre_nodup 0 n) _ _ _ h1 (List.getElem?_eq_getElem hl)
  · intro w hwm hslot
    obtain ⟨h1, hl', hr'⟩ := hw w hwm
    rw [hslot] at h1
    have := hob idx w.lo w.hi h1
    rw [hl', hr', this]

/-- A single group: no parent is written and the root is the group's own (root) hash. -/
theorem builder_correct_one (H : Hash Cv D) (data : Nat → D) (c0 : Cv) :
    let b := build H data 1 c0
    b.w = [] ∧ b.stack = [] ∧ b.root = gcv H data 1 0 1 := by
  intro b
  rw [gcv_leaf H data 1 0 1 (by omega)]
  simp [b, build, mainPhase, groupStep, finish]

/-- The entries of the stack are powers of two growing downwards, so `len` entries need at least `2^len - 1`
groups. -/
theorem Dec.len_pow {H : Hash Cv D} {data : Nat → D} {n k : Nat} {st : List (Cv × Nat)} (h : Dec H data n k st) :
    ∀ m, (∀ c s, st.head? = some (c, s) → 2 ^ m ≤ s) → 2 ^ m * 2 ^ st.length ≤ k + 2 ^ m := by
  induction h with
  | nil => intro m _; simp
  | @cons k' k cv s rest hd hp hdvd hlt hk hcv ih =>
    intro m hm
    have hs := hm cv s rfl
    have hrest : ∀ c t, rest.head? = some (c, t) → 2 ^ (m + 1) ≤ t := by
      intro c t ht
      have h1 := hlt c t ht
      have hp2 : ∃ b, t = 2 ^ b := by
        cases rest with
        | nil => simp at ht
        | cons e r =>
          simp only [List.head?_cons, Option.some.injEq] at ht
          subst ht
          exact hd.head_pow2
      obtain ⟨a, ha⟩ := hp
      have hm' : ∃ b, 2 ^ m = 2 ^ b := ⟨m, rfl⟩
      have hh := (pow2_lt (s := 2 ^ m) ⟨m, rfl⟩ hp2 (by omega)).2
      rw [Nat.pow_succ]; omega
    have := ih (m + 1) hrest
    have e : 2 ^ m * 2 ^ (rest.length + 1) = 2 ^ (m + 1) * 2 ^ rest.length := by
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    simp only [List.length_cons]
    rw [e]
    have e2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    omega

/-- The builder stack after any number of groups of a value of at most `2^64 - 1` bytes holds at most 54
entries; the merge loop pushes one more before it shrinks the stack, and `finish` only shrinks it, so the
64-entry capacity is never reached. -/
theorem mainPhase_stack_le (H : Hash Cv D) (data : Nat → D) (n : Nat) (c0 : Cv) (hn : 2 ≤ n) (hn54 : n ≤ 2 ^ 54)
    (k : Nat) (hk : k ≤ n) : (mainPhase H data n c0 k).stack.length ≤ 54 := by
  obtain ⟨hD, _⟩ := mainPhase_inv H data n c0 hn k hk
  have := hD.len_pow 0 (by
    intro c s hs
    cases hst : (mainPhase H data n c0 k).stack with
    | nil => rw [hst] at hs; simp at hs
    | cons e r =>
      rw [hst] at hs hD
      simp only [List.head?_cons, Option.some.injEq] at hs
      subst hs
      obtain ⟨b, hb⟩ := hD.head_pow2
      rw [hb]; have := Nat.two_pow_pos b; simp; omega)
  simp only [Nat.pow_zero, Nat.one_mul] at this
  refine Classical.byContradiction fun h => ?_
  have h55 : 2 ^ 55 ≤ 2 ^ (mainPhase H data n c0 k).stack.length :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have e : (2 : Nat) ^ 55 = 2 * 2 ^ 54 := by decide
  omega

end

end Vinc.Builder

#audit_axioms Vinc.Builder.builder_correct
#audit_axioms Vinc.Builder.builder_outboard
#audit_axioms Vinc.Builder.builder_correct_one
#audit_axioms Vinc.Builder.mainPhase_stack_le
