import Pinc.Tree
import Pinc.Sizes

/-!
# Range encoder and completeness

A model of `RangeEncoder` and `encode_range` in `pinc-dag/src/tree/encode.rs`: the encoder is a stack machine
over nodes `(lo, hi, idx)`, where `idx` is the node's pre-order index among the parents, that yields one `Step`
per pop (a parent pair at an outboard offset, or one whole group); `encode_range` reads each step's bytes from
the value and the outboard. As in `Tree`, the hash is abstract: the value is `data : Nat → D`, the genuine
chaining value of a node is `Tree.gcv`, and the genuine outboard stores at pre-order position `k` the pair of
chaining values of the children of the `k`-th parent.

Main results:

* `complete_accepts`: for a genuine value and outboard, the stream the encoder produces for a byte range is
  accepted by the verifier started at the genuine root: no step is rejected, the verifier completes, and it
  releases exactly the groups that intersect the range, each with its genuine bytes. No collision resistance is
  involved: completeness holds for any hash.
* The encoder reads inside the value and the outboard (`InBounds`), so `encode_range` raises neither
  `RangeOutOfBounds` nor an overflow on a genuine input, and each step's size is the size the verifier expects
  (`encStep_size`).

The model has no stack capacity; `Pinc.Bounds` proves the 64-entry capacity of the Rust stack is never reached.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Pinc.Encode
open Pinc.Layout Pinc.Tree

/-- An encoder node: the interval `[lo, hi)` and its pre-order index among the parents. -/
structure ENode where
  lo : Nat
  hi : Nat
  idx : Nat

/-- One element of the encoded stream: the outboard byte offset of a parent pair, or a group at a value byte
offset with its length. -/
inductive Step where
  | parent (off : Nat)
  | group (off len : Nat)

/-- The stream bytes a step stands for. -/
def Step.size : Step → Nat
  | .parent _ => 64
  | .group _ l => l

/-- `RangeEncoder::new`: the root node when the group range is not empty. -/
def encInit (len log first last : Nat) : List ENode :=
  if first < last then [⟨0, groups len log, 0⟩] else []

/-- `RangeEncoder::step`: the step for a node and the nodes it pushes (left on top of right). -/
def encStep (len log first last : Nat) (nd : ENode) : Step × List ENode :=
  if nd.hi - nd.lo = 1 then (.group (nd.lo * groupLen log) (groupSize len log nd.lo), [])
  else
    let left := leftGroups (nd.hi - nd.lo)
    let mid := nd.lo + left
    (.parent (nd.idx * 64),
      (if first < mid then [⟨nd.lo, mid, nd.idx + 1⟩] else []) ++
      (if mid < last then [⟨mid, nd.hi, nd.idx + left⟩] else []))

/-- Run the iterator for at most `fuel` steps: the steps in order and the stack that remains. -/
def encRun (len log first last : Nat) : Nat → List ENode → List Step × List ENode
  | 0, st => ([], st)
  | _ + 1, [] => ([], [])
  | f + 1, nd :: rest =>
    let r := encRun len log first last f ((encStep len log first last nd).2 ++ rest)
    ((encStep len log first last nd).1 :: r.1, r.2)

/-- The largest stack length the iterator reaches in `fuel` steps from `st`. -/
def encPeak (len log first last : Nat) : Nat → List ENode → Nat
  | 0, st => st.length
  | _ + 1, [] => 0
  | f + 1, nd :: rest =>
    max (nd :: rest).length (encPeak len log first last f ((encStep len log first last nd).2 ++ rest))

/-- `encode_range`: the bytes of a step, as the verifier reads them: a parent pair read from the outboard at
its slot, or a group's bytes read from the value at its offset. The filler values are never read by the
verifier for that kind of item. -/
def readStep {Cv D : Type} (g : Nat) (data : Nat → D) (ob : Nat → Cv × Cv) (c0 : Cv) (d0 : D) : Step → Raw Cv D
  | .parent off => ⟨(ob (off / 64)).1, (ob (off / 64)).2, d0⟩
  | .group off _ => ⟨c0, c0, data (off / g)⟩

/-- The size of the stream item the verifier expects for a node: the group's size or one parent pair. -/
def needOf (len log : Nat) (lo hi : Nat) : Nat := if hi - lo = 1 then groupSize len log lo else 64

theorem encStep_size (len log first last : Nat) (nd : ENode) :
    (encStep len log first last nd).1.size = needOf len log nd.lo nd.hi := by
  unfold encStep needOf
  by_cases h : nd.hi - nd.lo = 1 <;> simp [h, Step.size]

/-- The reads of a step stay inside the value and the outboard. -/
def InBounds (len log : Nat) : Step → Prop
  | .parent off => off % 64 = 0 ∧ off + 64 ≤ outboardSize len log
  | .group off l => off + l ≤ len ∧ l = groupSize len log (off / groupLen log) ∧ off % groupLen log = 0

section
variable {Cv D : Type} [DecidableEq Cv]

/-- The genuine outboard: the pair stored at pre-order position `k` is the pair of the `k`-th parent. -/
def GenuineOb (H : Hash Cv D) (data : Nat → D) (n : Nat) (ob : Nat → Cv × Cv) : Prop :=
  ∀ k lo hi, (pre 0 n)[k]? = some (lo, hi) →
    ob k = (gcv H data n lo (lo + leftGroups (hi - lo)), gcv H data n (lo + leftGroups (hi - lo)) hi)

/-- The encoder stack and the verifier stack hold the same nodes, the verifier's with their genuine values. -/
def Rel (H : Hash Cv D) (data : Nat → D) (n : Nat) : List ENode → List (Node Cv) → Prop
  | [], [] => True
  | e :: E, v :: V => v.lo = e.lo ∧ v.hi = e.hi ∧ v.cv = gcv H data n e.lo e.hi ∧ Rel H data n E V
  | _, _ => False

theorem Rel_append (H : Hash Cv D) (data : Nat → D) (n : Nat) :
    ∀ (A E : List ENode) (B V : List (Node Cv)), Rel H data n A B → Rel H data n E V →
      Rel H data n (A ++ E) (B ++ V) := by
  intro A
  induction A with
  | nil => intro E B V hA hE; cases B with
    | nil => simpa using hE
    | cons => exact hA.elim
  | cons a A ih => intro E B V hA hE; cases B with
    | nil => exact hA.elim
    | cons b B =>
      obtain ⟨h1, h2, h3, h4⟩ := hA
      exact ⟨h1, h2, h3, ih E B V h4 hE⟩

/-- The facts an encoder node carries: a nonempty interval of the tree meeting the range, and its pre-order
index points at its own parents inside the pre-order of the whole tree. -/
def NodeInv (n first last : Nat) (e : ENode) : Prop :=
  e.lo < e.hi ∧ e.hi ≤ n ∧ e.lo < last ∧ first < e.hi ∧
    ∃ t, (pre 0 n).drop e.idx = pre e.lo e.hi ++ t

/-- The decreasing measure of a node: the number of tree nodes below and including it. -/
def mu (e : ENode) : Nat := 2 * (e.hi - e.lo) - 1

def muSum (E : List ENode) : Nat := (E.map mu).sum

theorem slice_left (n idx lo hi : Nat) (t : List (Nat × Nat)) (h : hi - lo ≥ 2)
    (hs : (pre 0 n).drop idx = pre lo hi ++ t) :
    (pre 0 n).drop (idx + 1) = pre lo (lo + leftGroups (hi - lo)) ++ (pre (lo + leftGroups (hi - lo)) hi ++ t) := by
  rw [← List.drop_drop, hs, pre_unfold lo hi h]
  simp

theorem slice_right (n idx lo hi : Nat) (t : List (Nat × Nat)) (h : hi - lo ≥ 2)
    (hs : (pre 0 n).drop idx = pre lo hi ++ t) :
    (pre 0 n).drop (idx + leftGroups (hi - lo)) = pre (lo + leftGroups (hi - lo)) hi ++ t := by
  have h1 := leftGroups_pos (hi - lo) h
  have h2 := leftGroups_lt (hi - lo) h
  have hlen := pre_length lo (lo + leftGroups (hi - lo))
  have e : idx + leftGroups (hi - lo) = (idx + 1) + (pre lo (lo + leftGroups (hi - lo))).length := by omega
  rw [e, ← List.drop_drop, slice_left n idx lo hi t h hs, List.drop_left' rfl]

theorem slice_head (n idx lo hi : Nat) (t : List (Nat × Nat)) (h : hi - lo ≥ 2)
    (hs : (pre 0 n).drop idx = pre lo hi ++ t) : (pre 0 n)[idx]? = some (lo, hi) := by
  have : (pre 0 n)[idx]? = ((pre 0 n).drop idx)[0]? := by rw [List.getElem?_drop]; simp
  rw [this, hs, pre_unfold lo hi h]
  simp

theorem feed_leaf_ok (H : Hash Cv D) (n first last : Nat) (V : State Cv D) (it : Raw Cv D) (v : Node Cv)
    (V' : List (Node Cv)) (hf : V.failed = false) (hs : V.stack = v :: V') (hl : v.hi - v.lo = 1)
    (hh : H.leaf (isRoot n v.lo v.hi) v.lo it.d = v.cv) :
    feed H n first last V it = { V with stack := V', released := V.released ++ [(v.lo, it.d)] } := by
  simp [feed, hf, hs, hl, hh]

theorem feed_parent_ok (H : Hash Cv D) (n first last : Nat) (V : State Cv D) (it : Raw Cv D) (v : Node Cv)
    (V' : List (Node Cv)) (hf : V.failed = false) (hs : V.stack = v :: V') (hl : ¬ v.hi - v.lo = 1)
    (hh : H.parent (isRoot n v.lo v.hi) it.l it.r = v.cv) :
    feed H n first last V it = { V with stack :=
      (if first < v.lo + leftGroups (v.hi - v.lo) then [⟨it.l, v.lo, v.lo + leftGroups (v.hi - v.lo)⟩] else []) ++
      (if v.lo + leftGroups (v.hi - v.lo) < last then [⟨it.r, v.lo + leftGroups (v.hi - v.lo), v.hi⟩] else []) ++ V' } := by
  simp [feed, hf, hs, hl, hh]

/-- The lockstep invariant of the encoder and the verifier, run to the end. -/
theorem lockstep (H : Hash Cv D) (data : Nat → D) (ob : Nat → Cv × Cv) (c0 : Cv) (d0 : D)
    (len log first last n : Nat) (hn : groups len log = n) (hlen : len ≤ u64Max) (hob : GenuineOb H data n ob) :
    ∀ (f : Nat) (E : List ENode) (V : State Cv D),
      muSum E ≤ f → (∀ e ∈ E, NodeInv n first last e) → Rel H data n E V.stack → V.failed = false →
      (∀ g ∈ V.released, g.2 = data g.1) →
      let r := encRun len log first last f E
      let V2 := run H n first last V (r.1.map (readStep (groupLen log) data ob c0 d0))
      r.2 = [] ∧ V2.failed = false ∧ V2.stack = [] ∧ (∀ g ∈ V2.released, g.2 = data g.1) ∧
        (∀ s ∈ r.1, InBounds len log s) := by
  intro f
  induction f with
  | zero =>
    intro E V hm hE hR hf hg
    cases E with
    | nil =>
      cases hv : V.stack with
      | nil =>
        simp only [encRun, run, List.map_nil, List.foldl_nil, List.not_mem_nil, false_implies, implies_true, and_true, true_and]
        exact ⟨hf, hv, hg⟩
      | cons => rw [hv] at hR; exact hR.elim
    | cons e E =>
      have := (hE e (List.mem_cons_self ..)).1
      simp [muSum, mu] at hm
      omega
  | succ f ih =>
    intro E V hm hE hR hf hg
    cases E with
    | nil =>
      cases hv : V.stack with
      | nil =>
        simp only [encRun, run, List.map_nil, List.foldl_nil, List.not_mem_nil, false_implies, implies_true, and_true, true_and]
        exact ⟨hf, hv, hg⟩
      | cons => rw [hv] at hR; exact hR.elim
    | cons e E =>
      obtain ⟨hlo, hhi, hlast, hfirst, t, ht⟩ := hE e (List.mem_cons_self ..)
      have hE' : ∀ x ∈ E, NodeInv n first last x := fun x hx => hE x (List.mem_cons_of_mem _ hx)
      cases hv : V.stack with
      | nil => rw [hv] at hR; exact hR.elim
      | cons v V' =>
        rw [hv] at hR
        obtain ⟨hvlo, hvhi, hvcv, hR'⟩ := hR
        have hmE : muSum E + mu e ≤ f + 1 := by simp [muSum] at hm ⊢; omega
        by_cases hleaf : e.hi - e.lo = 1
        · -- a group
          have hstep : encStep len log first last e = (.group (e.lo * groupLen log) (groupSize len log e.lo), []) := by
            simp [encStep, hleaf]
          have hg0 := groupLen_pos log
          have hit : readStep (groupLen log) data ob c0 d0 (.group (e.lo * groupLen log) (groupSize len log e.lo)) =
              ⟨c0, c0, data e.lo⟩ := by
            simp [readStep, Nat.mul_div_cancel _ hg0]
          have hvl : v.hi - v.lo = 1 := by omega
          have hh : H.leaf (isRoot n v.lo v.hi) v.lo (data e.lo) = v.cv := by
            rw [hvcv, gcv_leaf H data n _ _ (by omega), hvlo, hvhi]
          have hfd := feed_leaf_ok H n first last V ⟨c0, c0, data e.lo⟩ v V' hf hv hvl hh
          have hmu : mu e = 1 := by simp [mu]; omega
          have hlt : e.lo < n := by omega
          have hsz := (groupSize_pos_iff len log e.lo hlen).2 (by omega)
          have hb := groupSize_le len log e.lo hlen
          have ihh := ih E { V with stack := V', released := V.released ++ [(v.lo, data e.lo)] }
            (by simp [muSum] at hm ⊢; omega) hE' hR' (by simpa using hf) (by
              intro g hg'
              simp only [List.mem_append, List.mem_singleton] at hg'
              rcases hg' with h | h
              · exact hg g h
              · subst h; simp [hvlo])
          simp only [encRun, hstep, List.nil_append, List.map_cons, run, List.foldl_cons, hit, hfd]
          obtain ⟨i1, i2, i3, i4, i5⟩ := ihh
          refine ⟨i1, i2, i3, i4, ?_⟩
          intro s hs'
          simp only [List.mem_cons] at hs'
          rcases hs' with rfl | hs'
          · exact ⟨by omega, by rw [Nat.mul_div_cancel _ hg0], Nat.mul_mod_left _ _⟩
          · exact i5 s hs'
        · -- a parent
          have h2 : e.hi - e.lo ≥ 2 := by omega
          have h1 := leftGroups_pos (e.hi - e.lo) h2
          have h3 := leftGroups_lt (e.hi - e.lo) h2
          obtain ⟨mid, hmid⟩ : ∃ mid, e.lo + leftGroups (e.hi - e.lo) = mid := ⟨_, rfl⟩
          have hstep : encStep len log first last e = (.parent (e.idx * 64),
              (if first < mid then [⟨e.lo, mid, e.idx + 1⟩] else []) ++
              (if mid < last then [⟨mid, e.hi, e.idx + leftGroups (e.hi - e.lo)⟩] else [])) := by
            simp [encStep, hleaf, hmid]
          have hslot := slice_head n e.idx e.lo e.hi t h2 ht
          have hob' := hob e.idx e.lo e.hi hslot
          rw [hmid] at hob'
          have hit : readStep (groupLen log) data ob c0 d0 (.parent (e.idx * 64)) =
              ⟨(gcv H data n e.lo mid), (gcv H data n mid e.hi), d0⟩ := by
            simp [readStep, hob']
          have hvl : ¬ v.hi - v.lo = 1 := by omega
          have hh : H.parent (isRoot n v.lo v.hi) (gcv H data n e.lo mid) (gcv H data n mid e.hi) = v.cv := by
            rw [hvcv, gcv_parent H data n _ _ h2, hvlo, hvhi, hmid]
          have hfd := feed_parent_ok H n first last V ⟨gcv H data n e.lo mid, gcv H data n mid e.hi, d0⟩ v V' hf hv hvl hh
          have hvmid : v.lo + leftGroups (v.hi - v.lo) = mid := by rw [hvlo, hvhi, hmid]
          rw [hvmid] at hfd
          have hlen2 : (pre 0 n).length = n - 1 := by simpa using pre_length 0 n
          have hidx : e.idx < n - 1 := by
            rw [← hlen2]; exact (List.getElem?_eq_some_iff.1 hslot).1
          have hmuE : muSum ((if first < mid then [⟨e.lo, mid, e.idx + 1⟩] else []) ++
              (if mid < last then [⟨mid, e.hi, e.idx + leftGroups (e.hi - e.lo)⟩] else []) ++ E) + 1 ≤ f + 1 := by
            have hm1 : mu e = 2 * (e.hi - e.lo) - 1 := rfl
            by_cases a : first < mid <;> by_cases b : mid < last <;>
              simp [muSum, mu, a, b] at hm hmE ⊢ <;> omega
          have hR2 : Rel H data n ((if first < mid then [⟨e.lo, mid, e.idx + 1⟩] else []) ++
              (if mid < last then [⟨mid, e.hi, e.idx + leftGroups (e.hi - e.lo)⟩] else []) ++ E)
              ((if first < mid then [⟨gcv H data n e.lo mid, v.lo, mid⟩] else []) ++
              (if mid < last then [⟨gcv H data n mid e.hi, mid, v.hi⟩] else []) ++ V') := by
            refine Rel_append _ _ _ _ _ _ _ (Rel_append _ _ _ _ _ _ _ ?_ ?_) hR'
            · by_cases a : first < mid <;> simp [a, Rel, hvlo]
            · by_cases b : mid < last <;> simp [b, Rel, hvhi]
          have hE2 : ∀ x ∈ ((if first < mid then [⟨e.lo, mid, e.idx + 1⟩] else []) ++
              (if mid < last then [⟨mid, e.hi, e.idx + leftGroups (e.hi - e.lo)⟩] else []) ++ E : List ENode),
              NodeInv n first last x := by
            intro x hx
            simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hx
            rcases hx with (⟨hc, rfl⟩ | ⟨hc, rfl⟩) | hx
            · have sl := slice_left n e.idx e.lo e.hi t h2 ht
              rw [hmid] at sl
              show NodeInv n first last ⟨e.lo, mid, e.idx + 1⟩
              exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, hc, _, sl⟩
            · have sl := slice_right n e.idx e.lo e.hi t h2 ht
              rw [hmid] at sl
              show NodeInv n first last ⟨mid, e.hi, e.idx + leftGroups (e.hi - e.lo)⟩
              exact ⟨by dsimp only; omega, by dsimp only; omega, hc, by dsimp only; omega, _, sl⟩
            · exact hE' x hx
          have ihh := ih _ { V with stack :=
              (if first < mid then [⟨gcv H data n e.lo mid, v.lo, mid⟩] else []) ++
              (if mid < last then [⟨gcv H data n mid e.hi, mid, v.hi⟩] else []) ++ V' }
            (by omega) hE2 hR2 (by simpa using hf) (by simpa using hg)
          simp only [encRun, hstep, List.map_cons, run, List.foldl_cons, hit]
          rw [hfd]
          obtain ⟨i1, i2, i3, i4, i5⟩ := ihh
          refine ⟨i1, i2, i3, i4, ?_⟩
          intro s hs'
          simp only [List.mem_cons] at hs'
          rcases hs' with rfl | hs'
          · refine ⟨Nat.mul_mod_left _ _, ?_⟩
            have hos := outboardSize_eq len log
            have : outboardSize len log = 64 * (n - 1) := by rw [hos, hn, ← hlen2]
            have := Nat.mul_le_mul_right 64 (show e.idx + 1 ≤ n - 1 by omega)
            omega
          · exact i5 s hs'

/-- (Completeness.) For a genuine value (`data`) and its genuine outboard, the stream that `RangeEncoder` /
`encode_range` produces for the byte range `[s, e)` is accepted by the verifier started at the genuine root:
the iterator ends with an empty stack, no item is rejected, the verifier is complete, and it has released
exactly the groups `first ..< last` that intersect the range, each with its genuine bytes. Every read of the
encoder is inside the value and the outboard, so `encode_range` raises no `RangeOutOfBounds`. No hash property
is assumed: the statement holds for any `Hash`. -/
theorem complete_accepts (H : Hash Cv D) (data : Nat → D) (ob : Nat → Cv × Cv) (c0 : Cv) (d0 : D)
    (len log s e first last n : Nat) (hn : groups len log = n) (hlen : len ≤ u64Max) (hse : s ≤ e)
    (hel : e ≤ len) (hr : groupRange len log s e = some (first, last)) (hob : GenuineOb H data n ob) :
    let r := encRun len log first last (2 * n) (encInit len log first last)
    let st := run H n first last (init (gcv H data n 0 n) n first last)
      (r.1.map (readStep (groupLen log) data ob c0 d0))
    r.2 = [] ∧ Complete st ∧
      st.released = (List.range' first (last - first)).map (fun k => (k, data k)) ∧
      (s < e → ∀ k, k ∈ st.released.map Prod.fst ↔ (k * groupLen log < e ∧ s < (k + 1) * groupLen log)) ∧
      (s = e → st.released = []) ∧
      (∀ stp ∈ r.1, InBounds len log stp) := by
  intro r st
  subst hn
  obtain ⟨hl, hspec, hz⟩ : last ≤ groups len log ∧ (s < e → ∀ k, (first ≤ k ∧ k < last) ↔ (k * groupLen log < e ∧ s < (k + 1) * groupLen log)) ∧ (s = e → first = 0 ∧ last = 0) := by
    by_cases hlt : s < e
    · obtain ⟨a, b, hab, _, hbn, hiff⟩ := groupRange_spec len log s e hlt hel
      rw [hr] at hab
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hab)
      exact ⟨hbn, fun _ => hiff, fun h => absurd h (by omega)⟩
    · have hs : s = e := by omega
      subst hs
      rw [groupRange_empty len log s hel] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
      exact ⟨Nat.zero_le _, fun h => absurd h hlt, fun _ => ⟨rfl, rfl⟩⟩
  have hmain := lockstep H data ob c0 d0 len log first last (groups len log) rfl hlen hob (2 * groups len log)
    (encInit len log first last) (init (gcv H data (groups len log) 0 (groups len log)) (groups len log) first last)
    (by
      unfold encInit muSum mu
      by_cases h : first < last
      · simp [h]
      · simp [h])
    (by
      intro x hx
      unfold encInit at hx
      by_cases h : first < last
      · simp only [h, ite_true, List.mem_singleton] at hx
        subst hx
        show NodeInv (groups len log) first last ⟨0, groups len log, 0⟩
        exact ⟨by dsimp only; omega, Nat.le_refl _, by dsimp only; omega, by dsimp only; omega, [], by simp⟩
      · simp [h] at hx)
    (by
      unfold encInit init
      by_cases h : first < last <;> simp [h, Rel])
    rfl
    (by simp [init])
  obtain ⟨h1, h2, h3, h4, h5⟩ := hmain
  have hc : Complete st := ⟨h2, h3⟩
  have hfst := complete_releases_range H (groups len log) first last hl (gcv H data (groups len log) 0 (groups len log)) _ hc
  have hrel : st.released = (List.range' first (last - first)).map (fun k => (k, data k)) := by
    rw [← hfst, List.map_map]
    conv => lhs; rw [← List.map_id st.released]
    exact List.map_congr_left fun g hg => Prod.ext rfl (h4 g hg)
  refine ⟨h1, hc, hrel, ?_, ?_, h5⟩
  · intro hlt k
    rw [hfst, List.mem_range'_1, ← hspec hlt k]
    omega
  · intro hs
    obtain ⟨rfl, rfl⟩ := hz hs
    rw [hrel]; rfl

end

end Pinc.Encode

#audit_axioms Pinc.Encode.complete_accepts
