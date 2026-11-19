import Pinc.Encode
import Pinc.Sizes

/-!
# The reference of the response geometry

`crates/pinc-values/src/plan.rs` gives the stream position of every GROUP frame of a response in closed form. The
reference it must equal is the frame sequence of the concatenated `pinc-dag` range encodings: per range, the
`RangeEncoder` steps of the groups `[a, b)` (a parent pair at its outboard offset, or a group), cut into frames
by the groups, a frame being a 16-byte header, the parent pairs the previous group leaves open, then the group.

* `ref` is the step list of the encoder as a recursion over the tree. `encRun_ref` proves that it is exactly what
  the stack machine of `Pinc.Encode` (the model of `RangeEncoder`) produces, so everything below is about the
  encoder of `pinc-dag` and not about a second encoder.
* `fs` cuts a step list into frames. `fs_ref` is the structure theorem: the frames of the range `[a, b)` are the
  groups `max lo a ..< min hi b` in order, the pairs of the first frame are the whole root-to-leaf path and the
  pairs of every later frame are the nodes of the path of its group that start at the group.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesPlan
open Pinc.Layout Pinc.Encode

/-- The steps of the encoder for the groups `[a, b)` in the node `[lo, hi)` with pre-order index `idx`: the
node's pair, then the steps of the left child, then those of the right child, a child only when it meets
`[a, b)` (`RangeEncoder::step`). -/
def ref (len log a b : Nat) (lo hi idx : Nat) : List Step :=
  if h : hi - lo ≥ 2 then
    have h1 := leftGroups_pos (hi - lo) h
    have h2 := leftGroups_lt (hi - lo) h
    .parent (idx * 64) ::
      ((if a < lo + leftGroups (hi - lo) then ref len log a b lo (lo + leftGroups (hi - lo)) (idx + 1) else []) ++
       (if lo + leftGroups (hi - lo) < b then
          ref len log a b (lo + leftGroups (hi - lo)) hi (idx + leftGroups (hi - lo)) else []))
  else [.group (lo * groupLen log) (groupSize len log lo)]
termination_by hi - lo

theorem ref_leaf (len log a b lo hi idx : Nat) (h : ¬ hi - lo ≥ 2) :
    ref len log a b lo hi idx = [.group (lo * groupLen log) (groupSize len log lo)] := by
  rw [ref]; simp [h]

theorem ref_node (len log a b lo hi idx : Nat) (h : hi - lo ≥ 2) :
    ref len log a b lo hi idx = .parent (idx * 64) ::
      ((if a < lo + leftGroups (hi - lo) then ref len log a b lo (lo + leftGroups (hi - lo)) (idx + 1) else []) ++
       (if lo + leftGroups (hi - lo) < b then
          ref len log a b (lo + leftGroups (hi - lo)) hi (idx + leftGroups (hi - lo)) else [])) := by
  rw [ref]; simp [h]

/-- One step of the stack machine unfolds the reference. -/
theorem ref_step (len log a b : Nat) (nd : ENode) (h : nd.hi - nd.lo ≥ 1) :
    ref len log a b nd.lo nd.hi nd.idx = (encStep len log a b nd).1 ::
      (encStep len log a b nd).2.flatMap (fun c => ref len log a b c.lo c.hi c.idx) := by
  by_cases h2 : nd.hi - nd.lo ≥ 2
  · have hne : ¬ nd.hi - nd.lo = 1 := by omega
    rw [ref_node _ _ _ _ _ _ _ h2]
    simp only [encStep, hne, ite_false]
    by_cases hl : a < nd.lo + leftGroups (nd.hi - nd.lo) <;>
    by_cases hr : nd.lo + leftGroups (nd.hi - nd.lo) < b <;> simp [hl, hr]
  · have he : nd.hi - nd.lo = 1 := by omega
    rw [ref_leaf _ _ _ _ _ _ _ h2]
    simp [encStep, he]

theorem encStep_children (len log a b : Nat) (nd : ENode) (h : nd.hi - nd.lo ≥ 1) :
    (∀ c ∈ (encStep len log a b nd).2, c.hi - c.lo ≥ 1) ∧
      muSum (encStep len log a b nd).2 + 1 ≤ mu nd := by
  by_cases h2 : nd.hi - nd.lo ≥ 2
  · have hne : ¬ nd.hi - nd.lo = 1 := by omega
    have h1 := leftGroups_pos (nd.hi - nd.lo) h2
    have h3 := leftGroups_lt (nd.hi - nd.lo) h2
    simp only [encStep, hne, ite_false, muSum, mu]
    by_cases hl : a < nd.lo + leftGroups (nd.hi - nd.lo) <;>
    by_cases hr : nd.lo + leftGroups (nd.hi - nd.lo) < b <;> simp [hl, hr, mu] <;> omega
  · have he : nd.hi - nd.lo = 1 := by omega
    simp [encStep, he, muSum, mu]

/-- The stack machine, run with enough fuel, yields the reference steps of every node on the stack in order. -/
theorem encRun_ref (len log a b : Nat) :
    ∀ (f : Nat) (L : List ENode), (∀ nd ∈ L, nd.hi - nd.lo ≥ 1) → muSum L ≤ f →
      encRun len log a b f L = (L.flatMap (fun nd => ref len log a b nd.lo nd.hi nd.idx), []) := by
  intro f
  induction f with
  | zero =>
    intro L hL hm
    cases L with
    | nil => simp [encRun]
    | cons nd rest =>
      have := hL nd (List.mem_cons_self ..)
      simp [muSum, mu] at hm
      omega
  | succ f ih =>
    intro L hL hm
    cases L with
    | nil => simp [encRun]
    | cons nd rest =>
      have h1 := hL nd (List.mem_cons_self ..)
      obtain ⟨hc, hmu⟩ := encStep_children len log a b nd h1
      have hrest : ∀ x ∈ rest, x.hi - x.lo ≥ 1 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
      have hm' : muSum ((encStep len log a b nd).2 ++ rest) ≤ f := by
        simp only [muSum, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hm hmu ⊢
        omega
      rw [encRun, ih _ (by
        intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hc x h
        · exact hrest x h) hm']
      simp only [List.flatMap_cons, List.flatMap_append]
      rw [ref_step len log a b nd h1]
      simp

/-- The reference is the encoder of `pinc-dag`: from the root with `2 * groups` fuel, the model of `RangeEncoder`
yields `ref`. -/
theorem encoder_eq_ref (len log first last : Nat) (hf : first < last) (hn : 1 ≤ groups len log) :
    (encRun len log first last (2 * groups len log) (encInit len log first last)).1 =
      ref len log first last 0 (groups len log) 0 := by
  have hi : encInit len log first last = [⟨0, groups len log, 0⟩] := by simp [encInit, hf]
  rw [hi, encRun_ref len log first last _ _ (by simp; omega) (by simp [muSum, mu])]
  simp

/-! ## Frames -/

/-- The path to group `x` through the node `[lo, hi)` with index `idx`: the parents above the group, root first,
as `(lo, idx)` (`plan.rs path`). -/
def chain (x : Nat) (lo hi idx : Nat) : List (Nat × Nat) :=
  if h : hi - lo ≥ 2 then
    have h1 := leftGroups_pos (hi - lo) h
    have h2 := leftGroups_lt (hi - lo) h
    (lo, idx) :: (if x < lo + leftGroups (hi - lo) then chain x lo (lo + leftGroups (hi - lo)) (idx + 1)
      else chain x (lo + leftGroups (hi - lo)) hi (idx + leftGroups (hi - lo)))
  else []
termination_by hi - lo

theorem chain_node (x lo hi idx : Nat) (h : hi - lo ≥ 2) :
    chain x lo hi idx = (lo, idx) :: (if x < lo + leftGroups (hi - lo) then chain x lo (lo + leftGroups (hi - lo)) (idx + 1)
      else chain x (lo + leftGroups (hi - lo)) hi (idx + leftGroups (hi - lo))) := by
  rw [chain]; simp [h]

theorem chain_leaf (x lo hi idx : Nat) (h : ¬ hi - lo ≥ 2) : chain x lo hi idx = [] := by
  rw [chain]; simp [h]

/-- The outboard byte offsets of a list of path nodes. -/
def offs (l : List (Nat × Nat)) : List Nat := l.map (fun p => p.2 * 64)

/-- The nodes of the path of `x` that start at `x`. -/
def starts (x : Nat) (l : List (Nat × Nat)) : List (Nat × Nat) := l.filter (fun p => decide (p.1 = x))

/-- On the left spine of a node every path node starts at the node's own left end. -/
theorem chain_spine (lo hi idx : Nat) : ∀ p ∈ chain lo lo hi idx, p.1 = lo := by
  generalize hn : hi - lo = n
  induction n using Nat.strongRecOn generalizing hi idx with
  | _ n ih =>
    intro p hp
    by_cases h : hi - lo ≥ 2
    · have h1 := leftGroups_pos (hi - lo) h
      have h2 := leftGroups_lt (hi - lo) h
      rw [chain_node _ _ _ _ h] at hp
      rcases List.mem_cons.1 hp with rfl | hp
      · rfl
      · have : lo < lo + leftGroups (hi - lo) := by omega
        simp only [this, ite_true] at hp
        exact ih (leftGroups (hi - lo)) (by omega) (lo + leftGroups (hi - lo)) (idx + 1) (by omega) p hp
    · rw [chain_leaf _ _ _ _ h] at hp; simp at hp

theorem starts_spine (lo hi idx : Nat) : starts lo (chain lo lo hi idx) = chain lo lo hi idx := by
  unfold starts
  exact List.filter_eq_self.2 (fun p hp => by simpa using chain_spine lo hi idx p hp)

/-- A list of `n` consecutive values of `f` from `s`. -/
def tab {α : Type} (f : Nat → α) : Nat → Nat → List α
  | _, 0 => []
  | s, n + 1 => f s :: tab f (s + 1) n

theorem tab_append {α : Type} (f : Nat → α) (s m n : Nat) : tab f s (m + n) = tab f s m ++ tab f (s + m) n := by
  induction m generalizing s with
  | zero => simp [tab]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [tab, List.cons_append]
    rw [ih (s + 1), show s + 1 + m = s + (m + 1) by omega]

theorem tab_congr {α : Type} (f g : Nat → α) (s n : Nat) (h : ∀ x, s ≤ x → x < s + n → f x = g x) :
    tab f s n = tab g s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [tab]
    rw [h s (by omega) (by omega), ih (s + 1) (fun x h1 h2 => h x (by omega) (by omega))]

theorem tab_length {α : Type} (f : Nat → α) (s n : Nat) : (tab f s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [tab, ih]

theorem tab_getElem {α : Type} (f : Nat → α) (s n k : Nat) (hk : k < n) : (tab f s n)[k]? = some (f (s + k)) := by
  induction n generalizing s k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [tab]
    | succ k => simp only [tab, List.getElem?_cons_succ]; rw [ih (s + 1) k (by omega)]; congr 2; omega

/-- A frame: the parent pairs it opens (outboard offsets), the group's value offset and its length. -/
abbrev Frame := List Nat × Nat × Nat

/-- Cut a step list into frames: the parents seen since the previous group are the pairs of the next group's
frame. Returns the frames and the parents left open at the end. -/
def fs : List Step → List Nat → List Frame × List Nat
  | [], acc => ([], acc)
  | .parent o :: t, acc => fs t (acc ++ [o])
  | .group off l :: t, acc => ((acc, off, l) :: (fs t []).1, (fs t []).2)

theorem fs_append (L R : List Step) (acc : List Nat) :
    fs (L ++ R) acc = ((fs L acc).1 ++ (fs R (fs L acc).2).1, (fs R (fs L acc).2).2) := by
  induction L generalizing acc with
  | nil => simp [fs]
  | cons s T ih =>
    cases s with
    | parent o => simp only [List.cons_append, fs]; exact ih _
    | group off l => simp only [List.cons_append, fs, ih, List.cons_append]

/-- The frame of group `g` in the node `[lo, hi)` (index `idx`) whose first frame is the group `g0` and starts
with the parents `acc` already open. -/
def frameOf (len log lo hi idx g0 : Nat) (acc : List Nat) (g : Nat) : Frame :=
  (if g = g0 then acc ++ offs (chain g lo hi idx) else offs (starts g (chain g lo hi idx)),
    g * groupLen log, groupSize len log g)

/-- The structure of the frames of the reference: group by group, in order, each with the pairs the closed
form of `plan.rs` computes. -/
theorem fs_ref (len log a b : Nat) :
    ∀ (n lo hi idx : Nat) (acc : List Nat), hi - lo = n → lo < hi → lo < b → a < hi → a < b →
      fs (ref len log a b lo hi idx) acc =
        (tab (frameOf len log lo hi idx (max lo a) acc) (max lo a) (min hi b - max lo a), []) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi idx acc hn hlh hlb hah hab
    by_cases h2 : hi - lo ≥ 2
    · have h1 := leftGroups_pos (hi - lo) h2
      have h3 := leftGroups_lt (hi - lo) h2
      rw [ref_node _ _ _ _ _ _ _ h2]
      simp only [fs]
      -- the cases on which children meet [a, b)
      by_cases hl : a < lo + leftGroups (hi - lo) <;> by_cases hr : lo + leftGroups (hi - lo) < b
      · -- both children
        simp only [hl, hr, ite_true]
        rw [fs_append]
        have iL := ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (idx + 1)
          (acc ++ [idx * 64]) (by omega) (by omega) hlb hl hab
        have iR := ih (hi - (lo + leftGroups (hi - lo))) (by omega) (lo + leftGroups (hi - lo)) hi
          (idx + leftGroups (hi - lo)) [] (by omega) (by omega) hr (by omega) hab
        rw [iL]
        simp only []
        rw [iR]
        simp only [List.append_nil, Prod.mk.injEq, and_true]
        have e1 : min (lo + leftGroups (hi - lo)) b = lo + leftGroups (hi - lo) := by omega
        have e2 : max (lo + leftGroups (hi - lo)) a = lo + leftGroups (hi - lo) := by omega
        rw [e1, e2, show min hi b - max lo a = (lo + leftGroups (hi - lo) - max lo a) + (min hi b - (lo + leftGroups (hi - lo))) by omega,
          tab_append]
        congr 1
        · apply tab_congr
          intro g hg1 hg2
          simp only [frameOf]
          have hgl : g < lo + leftGroups (hi - lo) := by omega
          rw [chain_node _ _ _ _ h2]
          simp only [hgl, ite_true]
          by_cases hg : g = max lo a
          · simp [hg, offs]
          · have : ¬ lo = g := by omega
            simp [hg, offs, starts, List.filter_cons, this]
        · rw [show max lo a + (lo + leftGroups (hi - lo) - max lo a) = lo + leftGroups (hi - lo) by omega]
          apply tab_congr
          intro g hg1 hg2
          simp only [frameOf]
          have hgl : ¬ g < lo + leftGroups (hi - lo) := by omega
          rw [chain_node _ _ _ _ h2]
          simp only [hgl, ite_false]
          have hg0 : ¬ g = max lo a := by omega
          have hlg : ¬ lo = g := by omega
          by_cases hgm : g = lo + leftGroups (hi - lo)
          · subst hgm
            have hs := starts_spine (lo + leftGroups (hi - lo)) hi (idx + leftGroups (hi - lo))
            simp only [starts] at hs
            have hL : leftGroups (hi - lo) ≠ 0 := by omega
            simp [hg0, offs, starts, List.filter_cons, hlg, hs, hL]
          · simp [hg0, hgm, offs, starts, List.filter_cons, hlg]
      · -- only the left child
        simp only [hl, hr, ite_true, ite_false, List.append_nil]
        have iL := ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (idx + 1)
          (acc ++ [idx * 64]) (by omega) (by omega) hlb hl hab
        rw [iL]
        have e1 : min (lo + leftGroups (hi - lo)) b = min hi b := by omega
        rw [e1]
        simp only [Prod.mk.injEq, and_true]
        apply tab_congr
        intro g hg1 hg2
        simp only [frameOf]
        have hgl : g < lo + leftGroups (hi - lo) := by omega
        rw [chain_node _ _ _ _ h2]
        simp only [hgl, ite_true]
        by_cases hg : g = max lo a
        · simp [hg, offs]
        · have : ¬ lo = g := by omega
          simp [hg, offs, starts, List.filter_cons, this]
      · -- only the right child
        simp only [hl, hr, ite_true, ite_false, List.nil_append]
        have iR := ih (hi - (lo + leftGroups (hi - lo))) (by omega) (lo + leftGroups (hi - lo)) hi
          (idx + leftGroups (hi - lo)) (acc ++ [idx * 64]) (by omega) (by omega) (by omega) (by omega) hab
        rw [iR]
        have e2 : max (lo + leftGroups (hi - lo)) a = max lo a := by omega
        rw [e2]
        simp only [Prod.mk.injEq, and_true]
        apply tab_congr
        intro g hg1 hg2
        simp only [frameOf]
        have hgl : ¬ g < lo + leftGroups (hi - lo) := by omega
        rw [chain_node _ _ _ _ h2]
        simp only [hgl, ite_false]
        by_cases hg : g = max lo a
        · simp [hg, offs]
        · have : ¬ lo = g := by omega
          simp [hg, offs, starts, List.filter_cons, this]
      · omega
    · have he : hi = lo + 1 := by omega
      subst he
      rw [ref_leaf _ _ _ _ _ _ _ h2]
      have e1 : max lo a = lo := by omega
      have e2 : min (lo + 1) b - lo = 1 := by omega
      rw [e1, e2]
      simp [fs, tab, frameOf, chain_leaf _ _ _ _ h2, offs]

end Pinc.ValuesPlan

#audit_axioms Pinc.ValuesPlan.encRun_ref
#audit_axioms Pinc.ValuesPlan.fs_ref
