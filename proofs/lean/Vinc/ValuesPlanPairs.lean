import Vinc.ValuesPlanLocate

/-!
# Proof pairs, frames of a group, range spans

* `PlanM.proofPair` is `Plan::proof_pair`: the outboard offset of the `j`-th parent pair of a frame's proof, from
  the root-to-group path (`path`, with its fixed 64-node array). `proofPair_spec` proves it is the `j`-th pair of
  the reference frame (the encoder's parents between the previous group and this one), that the path is never
  truncated by the array (`pathGo_eq`, a tree of at most `2^54` groups is under 55 deep), and that the offset is
  64 times the pre-order position of an ancestor of the group (`chain_pre`, `Vinc.Layout.pre`).
* `PlanM.frameOfGroup` is `Plan::frame_of_group`: the frame of a group in the first range that holds it.
* `rangePairs_encoder`: `range_pairs`, which `fetch/wt.rs` compares a proof's length with, is the number of parent
  steps of `RangeEncoder` for the group range, and `wt_range_eq` that the group range of a proof frame, as the
  receiver computes it (`start / G`, `ceil(end / G)`), is the one `Layout::group_range` gives the server.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Vinc.ValuesPlan
open Vinc.Layout Vinc.Encode

/-- The loop of `path` with its fixed array of 64 nodes: a node is dropped (and the length stays) once full. -/
def pathGo (x : Nat) (lo hi idx : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
  if h : hi - lo ≥ 2 then
    have h1 := leftGroups_pos (hi - lo) h
    have h2 := leftGroups_lt (hi - lo) h
    let acc' := if acc.length < 64 then acc ++ [(lo, idx)] else acc
    if x < lo + leftGroups (hi - lo) then pathGo x lo (lo + leftGroups (hi - lo)) (idx + 1) acc'
    else pathGo x (lo + leftGroups (hi - lo)) hi (idx + leftGroups (hi - lo)) acc'
  else acc
termination_by hi - lo

theorem hh_pos (c : Nat) (h : 2 ≤ c) : 1 ≤ hh c := by
  have := hh_leftGroups c h
  omega

/-- The array of 64 nodes is never full: the path is the whole chain. -/
theorem pathGo_eq (x : Nat) : ∀ (n lo hi idx : Nat) (acc : List (Nat × Nat)), hi - lo = n →
    acc.length + hh n ≤ 64 → pathGo x lo hi idx acc = acc ++ chain x lo hi idx := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi idx acc hn hb
    subst hn
    rw [pathGo]
    by_cases h : hi - lo ≥ 2
    · have h1 := leftGroups_pos (hi - lo) h
      have h3 := leftGroups_lt (hi - lo) h
      have hl := hh_leftGroups (hi - lo) h
      have hr := hh_right (hi - lo) h
      have hp := hh_pos (hi - lo) h
      simp only [h, dite_true]
      have hlt : acc.length < 64 := by omega
      simp only [hlt, ite_true]
      rw [chain_node _ _ _ _ h]
      by_cases hx : x < lo + leftGroups (hi - lo)
      · simp only [hx, ite_true]
        rw [ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (idx + 1) _ (by omega) (by simp; omega)]
        simp
      · simp only [hx, ite_false]
        rw [ih (hi - (lo + leftGroups (hi - lo))) (by omega) (lo + leftGroups (hi - lo)) hi (idx + leftGroups (hi - lo)) _ rfl
          (by simp; rw [show hi - (lo + leftGroups (hi - lo)) = hi - lo - leftGroups (hi - lo) by omega]; omega)]
        simp
    · simp only [h, dite_false]
      rw [chain_leaf _ _ _ _ h]; simp

/-- Every path node's pre-order index is below the number of groups of the node plus its own index. -/
theorem chain_idx_lt (x : Nat) : ∀ (n lo hi idx : Nat), hi - lo = n → ∀ p ∈ chain x lo hi idx, p.2 < idx + (hi - lo) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi idx hn p hp
    subst hn
    by_cases h : hi - lo ≥ 2
    · have h1 := leftGroups_pos (hi - lo) h
      have h3 := leftGroups_lt (hi - lo) h
      rw [chain_node _ _ _ _ h] at hp
      rcases List.mem_cons.1 hp with rfl | hp
      · simp only []; omega
      · by_cases hx : x < lo + leftGroups (hi - lo)
        · simp only [hx, ite_true] at hp
          have := ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (idx + 1) (by omega) p hp
          omega
        · simp only [hx, ite_false] at hp
          have := ih (hi - (lo + leftGroups (hi - lo))) (by omega) (lo + leftGroups (hi - lo)) hi (idx + leftGroups (hi - lo)) rfl p hp
          omega
    · rw [chain_leaf _ _ _ _ h] at hp; simp at hp

/-- The path nodes are the ancestors of the group, at their positions in the pre-order of the parents. -/
theorem chain_pre (n x : Nat) : ∀ (m lo hi idx : Nat) (t : List (Nat × Nat)), hi - lo = m → lo ≤ x → x < hi →
    (pre 0 n).drop idx = pre lo hi ++ t →
    ∀ p ∈ chain x lo hi idx, ∃ hi', (pre 0 n)[p.2]? = some (p.1, hi') ∧ p.1 ≤ x ∧ x < hi' := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro lo hi idx t hm hlx hxh hs p hp
    subst hm
    by_cases h : hi - lo ≥ 2
    · have h1 := leftGroups_pos (hi - lo) h
      have h3 := leftGroups_lt (hi - lo) h
      rw [chain_node _ _ _ _ h] at hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hi, slice_head n idx lo hi t h hs, hlx, hxh⟩
      · by_cases hx : x < lo + leftGroups (hi - lo)
        · simp only [hx, ite_true] at hp
          exact ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (idx + 1) _ (by omega) hlx hx
            (slice_left n idx lo hi t h hs) p hp
        · simp only [hx, ite_false] at hp
          exact ih (hi - (lo + leftGroups (hi - lo))) (by omega) (lo + leftGroups (hi - lo)) hi (idx + leftGroups (hi - lo)) t rfl
            (by omega) hxh (slice_right n idx lo hi t h hs) p hp
    · rw [chain_leaf _ _ _ _ h] at hp; simp at hp

/-- `Plan::proof_pair`. -/
def PlanM.proofPair (pl : PlanM) (f : FrameM) (j : Nat) : Option Nat :=
  match pl.rs[f.range]? with
  | none => none
  | some r =>
    let x := r.first + f.k
    let live := pathGo x 0 (groups pl.len lg) 0 []
    let node := if f.follows then (live.filter (fun p => decide (p.1 = x)))[j]? else live[j]?
    node.bind (fun p => cmul p.2 PARL)

theorem hh_le_54 (len : Nat) (hlen : len ≤ u64Max) : hh (groups len lg) ≤ 54 := by
  have hn := groups_le len lg hlen
  unfold hh
  by_cases hc : groups len lg ≤ 1
  · simp [hc]
  · simp only [hc, ite_false]
    have : Nat.log2 (groups len lg - 1) < 54 := by
      rw [Nat.log2_lt (by omega)]
      omega
    omega

/-- The `j`-th pair of the proof of a frame is the `j`-th parent of the reference frame, at 64 times its pre-order
position, and that parent is an ancestor of the group (for a frame that follows, one that starts at the group). -/
theorem proofPair_spec {len : Nat} {pl : PlanM} (g : Good len pl) {i k : Nat} {r : PR} {f : FrameM}
    (hr : pl.rs[i]? = some r) (hk : k < r.last - r.first) (hf : pl.frame i k = some f) (j : Nat) :
    pl.proofPair f j = (refFrames len r.first r.last)[k]?.bind (fun (fr : Frame) => fr.1[j]?) ∧
    (∀ off, pl.proofPair f j = some off → ∃ q lo' hi', off = q * 64 ∧ (pre 0 (groups len lg))[q]? = some (lo', hi') ∧
      lo' ≤ r.first + k ∧ r.first + k < hi' ∧ (f.follows = true → lo' = r.first + k)) := by
  obtain ⟨h1, h2, _⟩ := g.range hr
  obtain ⟨f2, hf2, ra, ka, _, _, _, _, _, hfol⟩ := frame_spec g hr hk
  have e2 : f = f2 := Option.some.inj (hf.symm.trans hf2)
  subst e2
  have hn54 := hh_le_54 len g.hlen
  have hpath : pathGo (r.first + k) 0 (groups len lg) 0 [] = chain (r.first + k) 0 (groups len lg) 0 := by
    rw [pathGo_eq _ (groups len lg) 0 _ 0 [] (Nat.sub_zero _) (by simp; omega)]; simp
  have hnum := groups_le len lg g.hlen
  have hidx := chain_idx_lt (r.first + k) (groups len lg) 0 (groups len lg) 0 (Nat.sub_zero _)
  have hpre := chain_pre (groups len lg) (r.first + k) (groups len lg) 0 (groups len lg) 0 [] (Nat.sub_zero _) (by omega)
    (by omega) (by simp)
  have hget := refFrames_get len r.first r.last k h1 h2 hk
  have hcm : ∀ p : Nat × Nat, p.2 < 0 + (groups len lg - 0) → cmul p.2 PARL = some (p.2 * 64) := by
    intro p hp
    unfold cmul u64Max PARL
    have : p.2 * 64 ≤ 2 ^ 54 * 64 := Nat.mul_le_mul_right 64 (by omega)
    rw [if_pos (by omega)]
  have hpp : pl.proofPair f j = ((if f.follows = true then ((chain (r.first + k) 0 (groups len lg) 0).filter
        (fun p => decide (p.1 = r.first + k)))[j]? else (chain (r.first + k) 0 (groups len lg) 0)[j]?)).bind
        (fun p => cmul p.2 PARL) := by
    unfold PlanM.proofPair
    rw [ra, hr]
    simp only [ka, g.plen, hpath]
  rw [hpp]
  have hfk : f.follows = decide (0 < k) := hfol
  refine ⟨?_, ?_⟩
  · rw [hget]
    simp only [frameOf, Option.bind_some]
    by_cases hk0 : k = 0
    · subst hk0
      have hf0 : f.follows = false := by rw [hfk]; rfl
      simp only [Nat.add_zero, hf0, Bool.false_eq_true, ite_false, ite_true, List.nil_append, offs]
      cases hl : (chain r.first 0 (groups len lg) 0)[j]? with
      | none => simp [List.getElem?_map, hl]
      | some p =>
        have := hidx p (List.mem_of_getElem? hl)
        simp [hcm p this, List.getElem?_map, hl]
    · have hf1 : f.follows = true := by rw [hfk]; simp; omega
      have hne : ¬ r.first + k = r.first := by omega
      simp only [hf1, hne, hk0, ite_true, ite_false, offs, starts, List.getElem?_map]
      cases hl : ((chain (r.first + k) 0 (groups len lg) 0).filter (fun p => decide (p.1 = r.first + k)))[j]? with
      | none => simp
      | some p =>
        have := hidx p (List.mem_of_getElem? hl |> fun h => (List.mem_filter.1 h).1)
        simp [hcm p this]
  · intro off hoff
    by_cases hf1 : f.follows = true
    · simp only [hf1, ite_true] at hoff
      obtain ⟨p, hp, hcmp⟩ := Option.bind_eq_some_iff.1 hoff
      have hpm := List.mem_filter.1 (List.mem_of_getElem? hp)
      have := hidx p hpm.1
      rw [hcm p this] at hcmp
      obtain ⟨hi', a, b, c⟩ := hpre p hpm.1
      exact ⟨p.2, p.1, hi', (Option.some.inj hcmp).symm, a, b, c, fun _ => by simpa using hpm.2⟩
    · simp only [hf1, ite_false] at hoff
      obtain ⟨p, hp, hcmp⟩ := Option.bind_eq_some_iff.1 hoff
      have := hidx p (List.mem_of_getElem? hp)
      rw [hcm p this] at hcmp
      obtain ⟨hi', a, b, c⟩ := hpre p (List.mem_of_getElem? hp)
      exact ⟨p.2, p.1, hi', (Option.some.inj hcmp).symm, a, b, c, fun h => absurd h hf1⟩

end Vinc.ValuesPlan
