import Vinc.ValuesPlanPairs

/-!
# The plan: frame of a group, range spans, proof lengths, and the main statements

* `PlanM.frameOfGroup` (`Plan::frame_of_group`): the frame of a group in the first range that holds it.
* `PlanM.rangeSpan` (`Plan::range_span`): the value bytes a range covers after rounding to groups; it contains
  the requested span and stays inside the value.
* `rangePairs_encoder` and `wt_range_eq`: the proof length `fetch/wt.rs` accepts is the pair count of the
  encoder's group range, which is the group range the server's `RangeEncoder` runs on.
* `plan_main`: for a plan `Plan::new` accepts, the response is exactly the frames of the reference, in order,
  tiling `[0, total)`, `total <= 2^62 - 1`; `locate` inverts `frame`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Vinc.ValuesPlan
open Vinc.Layout Vinc.Encode

/-- `Plan::frame_of_group`. -/
def PlanM.frameOfGroup (pl : PlanM) (off : Nat) : Option FrameM :=
  if off % G ≠ 0 then none else
  match pl.rs.findIdx? (fun r => decide (r.first ≤ off / G ∧ off / G < r.last)) with
  | none => none
  | some i =>
    match pl.rs[i]? with
    | none => none
    | some r => pl.frame i (off / G - r.first)

theorem frameOfGroup_spec {len : Nat} {pl : PlanM} (g : Good len pl) (x : Nat) :
    (∀ (i : Nat) (r : PR), pl.rs[i]? = some r → r.first ≤ x → x < r.last →
      (∀ (j : Nat) (r' : PR), j < i → pl.rs[j]? = some r' → ¬ (r'.first ≤ x ∧ x < r'.last)) →
      ∃ f, pl.frameOfGroup (x * G) = some f ∧ pl.frame i (x - r.first) = some f ∧ f.off = x * G) ∧
    ((∀ (i : Nat) (r : PR), pl.rs[i]? = some r → ¬ (r.first ≤ x ∧ x < r.last)) → pl.frameOfGroup (x * G) = none) := by
  have hG := G_pos
  have hm : x * G % G = 0 := Nat.mul_mod_left x G
  have hd : x * G / G = x := Nat.mul_div_cancel x hG
  constructor
  · intro i r hr h1 h2 hbefore
    have hi : i < pl.rs.length :=
      Classical.byContradiction fun hc => by rw [List.getElem?_eq_none (by omega)] at hr; cases hr
    have hrs : pl.rs[i] = r := by rw [List.getElem?_eq_getElem hi] at hr; exact Option.some.inj hr
    have hfi : pl.rs.findIdx (fun r => decide (r.first ≤ x ∧ x < r.last)) = i := by
      rw [List.findIdx_eq hi]
      refine ⟨by simp [hrs, h1, h2], fun j hj => ?_⟩
      have := hbefore j pl.rs[j] hj (List.getElem?_eq_getElem (by omega))
      simpa using this
    have hex := List.findIdx?_eq_some_of_exists (xs := pl.rs) (p := fun r => decide (r.first ≤ x ∧ x < r.last))
      ⟨r, List.mem_of_getElem? hr, by simp [h1, h2]⟩
    rw [hfi] at hex
    obtain ⟨h3, h4, _⟩ := g.range hr
    have hk : x - r.first < r.last - r.first := by omega
    obtain ⟨f, hf, _, _, hoff, _⟩ := frame_spec g hr hk
    refine ⟨f, ?_, hf, by rw [hoff]; congr 1; omega⟩
    simp only [PlanM.frameOfGroup, hm, hd, ne_eq, not_true_eq_false, ite_false, hex, hr]
    exact hf
  · intro hn
    simp only [PlanM.frameOfGroup, hm, hd, ne_eq, not_true_eq_false, ite_false]
    have : pl.rs.findIdx? (fun r => decide (r.first ≤ x ∧ x < r.last)) = none := by
      rw [List.findIdx?_eq_none_iff]
      intro r hr
      obtain ⟨i, hi⟩ := List.getElem_of_mem hr
      have := hn i r (by rw [List.getElem?_eq_getElem hi.1, hi.2])
      simpa using this
    rw [this]

theorem frameOfGroup_unaligned {len : Nat} {pl : PlanM} (off : Nat) (h : off % G ≠ 0) : pl.frameOfGroup off = none := by
  simp [PlanM.frameOfGroup, h]

/-- `Plan::range_span`. -/
def PlanM.rangeSpan (pl : PlanM) (i : Nat) : Option (Nat × Nat) :=
  match pl.rs[i]? with
  | none => none
  | some r => some (r.first * G, min (r.last * G) pl.len - r.first * G)

/-- A range's span covers the span it was made from and stays inside the value. -/
theorem rangeSpan_covers {len : Nat} (hlen : len ≤ u64Max) (off n : Nat) (h0 : n ≠ 0) (h : off + n ≤ len) :
    (off / G) * G ≤ off ∧ off + n ≤ (off / G) * G + (min (divCeil (off + n) G * G) len - (off / G) * G) ∧
      (off / G) * G + (min (divCeil (off + n) G * G) len - (off / G) * G) ≤ len := by
  have hb := divCeil_bounds (off + n) len (by omega) h
  have hg := G_pos
  have := Nat.div_mul_le_self off G
  omega

/-- The proof length the receiver checks is the pair count of the group range, which is what the server's encoder
runs on. -/
theorem rangePairs_encoder (len a b : Nat) (hab : a < b) (hb : b ≤ groups len lg) :
    parentsIn a b 0 (groups len lg) =
      np (encRun len lg a b (2 * groups len lg) (encInit len lg a b)).1 := by
  rw [encoder_eq_ref len lg a b hab (by omega)]
  exact parentsIn_eq len lg a b _ 0 _ 0 rfl (by omega) (by omega) (by omega) hab

/-- The group range of a proof frame `[s, e)` as the receiver computes it is the one `Layout::group_range` gives. -/
theorem wt_range_eq (len s e : Nat) (hse : s < e) (hel : e ≤ len) :
    groupRange len lg s e = some (s / G, divCeil e G) := by
  have hg := G_pos
  unfold groupRange divCeil
  have : ¬ (s > e ∨ e > len) := by omega
  have h2 : s ≠ e := by omega
  simp only [this, h2, ite_false]
  congr 2
  have : G = groupLen lg := rfl
  rw [← this]
  have h3 : (e - 1) / G + 1 = (e - 1 + G) / G := by
    rw [Nat.add_div_right _ hg]
  rw [h3]; congr 1; omega

/-- `locate` of a frame's first byte is that frame: `locate` inverts `frame`. -/
theorem locate_start {len : Nat} {pl : PlanM} (g : Good len pl) {i k : Nat} {r : PR} {f : FrameM}
    (hr : pl.rs[i]? = some r) (hk : k < r.last - r.first) (hf : pl.frame i k = some f) :
    pl.locate f.start = some f := by
  obtain ⟨f2, hf2, _, _, _, _, e, hp, _⟩ := frame_spec g hr hk
  have e2 : f = f2 := Option.some.inj (hf.symm.trans hf2)
  subst e2
  apply locate_frame g hr hk hf (Nat.le_refl _)
  unfold FrameM.fend FrameM.dataStart
  unfold HDR; omega

/-- Every offset below the response length is located, in a frame that holds it. -/
theorem locate_some {len : Nat} {pl : PlanM} (g : Good len pl) {at_ : Nat} (h : at_ < pl.total) :
    ∃ f, pl.locate at_ = some f ∧ f.start ≤ at_ ∧ at_ < f.fend := by
  obtain ⟨i, r, k, f, hr, hk, hf, a, b⟩ := locate_total g h
  exact ⟨f, locate_frame g hr hk hf a b, a, b⟩

end Vinc.ValuesPlan

#audit_axioms Vinc.ValuesPlan.encoder_eq_ref
#audit_axioms Vinc.ValuesPlan.fs_ref
#audit_axioms Vinc.ValuesPlan.parentsIn_eq
#audit_axioms Vinc.ValuesPlan.sufGo_eq
#audit_axioms Vinc.ValuesPlan.pbGo_eq
#audit_axioms Vinc.ValuesPlan.parentsBefore_sum
#audit_axioms Vinc.ValuesPlan.refSize_eq
#audit_axioms Vinc.ValuesPlan.planNew_eq_spec
#audit_axioms Vinc.ValuesPlan.planNew_ok
#audit_axioms Vinc.ValuesPlan.frame_spec
#audit_axioms Vinc.ValuesPlan.frame_end_start
#audit_axioms Vinc.ValuesPlan.range_ends
#audit_axioms Vinc.ValuesPlan.start_strict
#audit_axioms Vinc.ValuesPlan.frame_end_le_total
#audit_axioms Vinc.ValuesPlan.frame_u32
#audit_axioms Vinc.ValuesPlan.bsGo_spec
#audit_axioms Vinc.ValuesPlan.locate_frame
#audit_axioms Vinc.ValuesPlan.locate_start
#audit_axioms Vinc.ValuesPlan.locate_some
#audit_axioms Vinc.ValuesPlan.locate_end
#audit_axioms Vinc.ValuesPlan.frame_unique
#audit_axioms Vinc.ValuesPlan.pathGo_eq
#audit_axioms Vinc.ValuesPlan.proofPair_spec
#audit_axioms Vinc.ValuesPlan.frameOfGroup_spec
#audit_axioms Vinc.ValuesPlan.rangeSpan_covers
#audit_axioms Vinc.ValuesPlan.rangePairs_encoder
#audit_axioms Vinc.ValuesPlan.wt_range_eq
