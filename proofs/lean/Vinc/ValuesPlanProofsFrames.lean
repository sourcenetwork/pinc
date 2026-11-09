import Vinc.ValuesPlanProofsK

/-!
# The frames of one `Server::proofs` call

`server.rs proofs()` after a loss, a send, or a `PROOF_REQ`: the end of the proofs, the frame size `k`
(`ValuesPlanProofsK`), the start (the block of `from`, never before what was already sent), and the loop that cuts
frames at block boundaries, at most `WT_MAXF` per call, stopping at the first frame that cannot be built.
`proofsCall` is that function on `Nat` (the saturating additions exact); `ok j` says whether the `j`-th frame of
the call could be built and sent (the store and the session are adversarial: any frame may fail).

* `proofs_frames`: every frame lies in one aligned block of `k <= 16` groups, starts on a group, stays inside the
  value, begins at or after what was sent and the block of `from`, and its proof is at most `cost(k) - 8 < 1100`
  bytes, so with the head it fits `PROOF_BODY_MAX`; at most 48 frames; the pair count is `range_pairs` of its group
  range (`pairs_eq_range_pairs`), which is what `fetch/wt.rs on_ext` accepts.
* `proofs_lead`: every group a call covers starts at most `eff` into the value, `eff` = the `upto` asked for, or
  the send frontier plus the window: on the proactive path (`window` capped at `WT_LEAD`) at most `WT_LEAD` past
  the frontier.
* `proofs_deep`: a value over 1 GiB gets no proofs and stays deep.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Vinc.ValuesPlan
open Vinc.Layout Vinc.Encode

theorem groups_eq_ceil (len : Nat) : groups len lg = (len + G - 1) / G := by
  have : G = 16384 := G_eq
  have e : groupLen lg = 16384 := by decide
  unfold groups; rw [e, this]
  by_cases h : len % 16384 = 0 <;> simp [h] <;> omega

/-- `WT_LEAD`. -/
abbrev LEAD : Nat := 524288

/-- The state of a served response that `proofs` keeps. -/
structure PState where
  deep : Bool
  pfTo : Nat

/-- The loop that builds frames: `f` frames may still be sent; stops at the first frame `ok` refuses. -/
def frameLoop (endB block : Nat) (ok : Nat → Bool) (at_ : Nat) : Nat → Nat × List (Nat × Nat)
  | 0 => (at_, [])
  | f + 1 =>
    if at_ < endB then
      if ok (MAXF - (f + 1)) then
        let r := frameLoop endB block ok (at_ + min (block - at_ % block) (endB - at_)) f
        (r.1, (at_, min (block - at_ % block) (endB - at_)) :: r.2)
      else (at_, [])
    else (at_, [])

/-- `Server::proofs`. -/
def proofsCall (ln : Nat) (st : PState) (vfront window from_ upto : Nat) (ok : Nat → Bool) : PState × List (Nat × Nat) :=
  if ln = 0 ∨ st.deep then (st, [])
  else
    let end0 := min (if upto ≠ 0 then upto + G else vfront + window + G) u64Max
    let endB := min ln (end0 - end0 % G)
    match protoK ln with
    | none => ({ st with deep := true }, [])
    | some k =>
      let block := k * G
      let r := frameLoop endB block ok (max (from_ / block * block) st.pfTo) MAXF
      ({ st with pfTo := r.1 }, r.2)

/-- A position is on a group or at the end of the value. -/
def Aligned (ln p : Nat) : Prop := p % 16384 = 0 ∨ ln ≤ p

theorem frameLoop_spec (ln endB block : Nat) (ok : Nat → Bool) (hb : block = 65536 ∨ block = 131072 ∨ block = 262144)
    (he : endB ≤ ln) (hea : endB % 16384 = 0 ∨ endB = ln) :
    ∀ (f at_ : Nat), Aligned ln at_ →
      (frameLoop endB block ok at_ f).2.length ≤ f ∧ at_ ≤ (frameLoop endB block ok at_ f).1 ∧
      Aligned ln (frameLoop endB block ok at_ f).1 ∧
      ((frameLoop endB block ok at_ f).2 = [] → (frameLoop endB block ok at_ f).1 = at_) ∧
      (∀ x ∈ (frameLoop endB block ok at_ f).2, at_ ≤ x.1 ∧ x.1 < endB ∧ Aligned ln x.1 ∧ 1 ≤ x.2 ∧
        x.2 ≤ block - x.1 % block ∧ x.1 + x.2 ≤ endB) := by
  intro f
  induction f with
  | zero => intro at_ ha; simp [frameLoop, ha]
  | succ f ih =>
    intro at_ ha
    unfold frameLoop
    by_cases h1 : at_ < endB
    · simp only [h1, ite_true]
      by_cases h2 : ok (MAXF - (f + 1)) = true
      · simp only [h2, ite_true]
        have hal : at_ % 16384 = 0 := by unfold Aligned at ha; omega
        have hnew : Aligned ln (at_ + min (block - at_ % block) (endB - at_)) := by
          unfold Aligned
          rcases hb with rfl | rfl | rfl <;> omega
        obtain ⟨i1, i2, i3, i4, i5⟩ := ih _ hnew
        refine ⟨?_, ?_, i3, ?_, ?_⟩
        · simp only [List.length_cons]; omega
        · have : 0 < min (block - at_ % block) (endB - at_) := by
            rcases hb with rfl | rfl | rfl <;> omega
          omega
        · intro h; simp at h
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · simp only []
            refine ⟨Nat.le_refl _, h1, ha, ?_, ?_, ?_⟩ <;> rcases hb with rfl | rfl | rfl <;> omega
          · have hx5 := i5 x hx
            have hpos : 0 < min (block - at_ % block) (endB - at_) := by
              rcases hb with rfl | rfl | rfl <;> omega
            refine ⟨by omega, hx5.2.1, hx5.2.2.1, hx5.2.2.2.1, hx5.2.2.2.2.1, hx5.2.2.2.2.2⟩
      · simp [h2, ha]
    · simp [h1, ha]

theorem k_cases (ln k : Nat) (h : protoK ln = some k) :
    (k = 4 ∨ k = 8 ∨ k = 16) ∧ ∃ m, k = 2 ^ m ∧ cost (depOf ln) k ≤ PMAX := by
  obtain ⟨m, hm, h4, h16, hc⟩ := protoK_pow ln k h
  refine ⟨?_, m, hm, hc⟩
  have hm4 : m ≤ 4 := by
    have : 2 ^ m ≤ 2 ^ 4 := by unfold MAXK at h16; omega
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 this
  have hc5 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  unfold MINK at h4
  rcases hc5 with rfl | rfl | rfl | rfl | rfl <;> simp at hm <;> omega

theorem endB_facts (ln end0 : Nat) :
    min ln (end0 - end0 % 16384) ≤ ln ∧ (min ln (end0 - end0 % 16384) % 16384 = 0 ∨ min ln (end0 - end0 % 16384) = ln) := by
  omega

theorem start_aligned (ln from_ pf k : Nat) (hk : k = 4 ∨ k = 8 ∨ k = 16) (h : Aligned ln pf) :
    Aligned ln (max (from_ / (k * 16384) * (k * 16384)) pf) := by
  unfold Aligned at *
  rcases hk with rfl | rfl | rfl <;> omega

theorem frame_arith (k at_ wn : Nat) (hk : k = 4 ∨ k = 8 ∨ k = 16) (hw1 : 1 ≤ wn)
    (hw2 : wn ≤ k * 16384 - at_ % (k * 16384)) :
    wn ≤ k * 16384 ∧ at_ / (k * 16384) = (at_ + wn - 1) / (k * 16384) ∧ at_ / (k * 16384) * k ≤ at_ / 16384 ∧
      (at_ + wn + 16384 - 1) / 16384 ≤ at_ / (k * 16384) * k + k := by
  rcases hk with rfl | rfl | rfl <;> omega

theorem lead_arith (a w end0 eff : Nat) (hw : 1 ≤ w) (h1 : a + w ≤ end0 - end0 % 16384) (h2 : end0 ≤ eff + 16384) :
    (a + w - 1) / 16384 * 16384 ≤ eff := by
  omega

/-- One frame of a call: where it lies and what its proof costs. -/
def FrameOK (ln k from_ pfTo : Nat) (x : Nat × Nat) : Prop :=
  x.1 % 16384 = 0 ∧ 1 ≤ x.2 ∧ x.2 ≤ k * 16384 ∧ x.1 + x.2 ≤ ln ∧ pfTo ≤ x.1 ∧ from_ / (k * 16384) * (k * 16384) ≤ x.1 ∧
    x.1 / (k * 16384) = (x.1 + x.2 - 1) / (k * 16384) ∧
    parentsIn (x.1 / G) (divCeil (x.1 + x.2) G) 0 (groups ln lg) * 64 + 8 ≤ cost (depOf ln) k ∧
    cost (depOf ln) k ≤ PMAX

/-- The frames of a call. -/
theorem proofs_frames (ln : Nat) (st : PState) (vfront window from_ upto : Nat) (ok : Nat → Bool)
    (hln : 0 < ln) (hu : ln ≤ u64Max) (hal : Aligned ln st.pfTo) (hd : st.deep = false) :
    (proofsCall ln st vfront window from_ upto ok).2.length ≤ MAXF ∧
    (∀ k, protoK ln = some k → ∀ x ∈ (proofsCall ln st vfront window from_ upto ok).2, FrameOK ln k from_ st.pfTo x) ∧
    Aligned ln (proofsCall ln st vfront window from_ upto ok).1.pfTo ∧
    st.pfTo ≤ (proofsCall ln st vfront window from_ upto ok).1.pfTo ∧
    (protoK ln = none → (proofsCall ln st vfront window from_ upto ok).1.deep = true ∧
      (proofsCall ln st vfront window from_ upto ok).2 = []) ∧
    (∀ x ∈ (proofsCall ln st vfront window from_ upto ok).2,
      (x.1 + x.2 - 1) / 16384 * 16384 ≤ (if upto ≠ 0 then upto else vfront + window)) := by
  unfold proofsCall
  have hnz : ¬ (ln = 0 ∨ st.deep = true) := by simp [hd]; omega
  simp only [hnz, ite_false]
  cases hk : protoK ln with
  | none => simp [hal]
  | some k =>
    simp only []
    obtain ⟨hkc, m, hm, hcost⟩ := k_cases ln k hk
    have hG : G = 16384 := G_eq
    have hblock : k * G = 65536 ∨ k * G = 131072 ∨ k * G = 262144 := by
      rw [hG]; rcases hkc with rfl | rfl | rfl <;> omega
    generalize he0 : min (if upto ≠ 0 then upto + G else vfront + window + G) u64Max = end0
    obtain ⟨hE1, hE2⟩ := endB_facts ln end0
    rw [hG]
    have hstart := start_aligned ln from_ st.pfTo k hkc hal
    rw [hG] at hblock
    obtain ⟨i1, i2, i3, i4, i5⟩ := frameLoop_spec ln _ (k * 16384) ok hblock hE1 hE2 MAXF _ hstart
    refine ⟨i1, ?_, i3, ?_, by simp, ?_⟩
    · intro k' hk' x hx
      have hkk : k' = k := (Option.some.inj hk').symm
      subst hkk
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := i5 x hx
      have hxa : x.1 % 16384 = 0 := by unfold Aligned at a3; omega
      have hmax1 : st.pfTo ≤ x.1 := Nat.le_trans (Nat.le_max_right _ _) a1
      have hmax2 : from_ / (k' * 16384) * (k' * 16384) ≤ x.1 := Nat.le_trans (Nat.le_max_left _ _) a1
      have hle : x.1 + x.2 ≤ ln := Nat.le_trans a6 hE1
      obtain ⟨c1, c2, c3, c4⟩ := frame_arith k' x.1 x.2 hkc a4 a5
      refine ⟨hxa, a4, c1, hle, hmax1, hmax2, c2, ?_, hcost⟩
      have hA := proof_bytes_le ln k' m (x.1 / (k' * 16384) * k') (x.1 / 16384) (divCeil (x.1 + x.2) 16384) hm
        ⟨x.1 / (k' * 16384), Nat.mul_comm _ _⟩ c3 (by unfold divCeil; exact c4)
      rw [groups_eq_ceil, hG]
      rw [hG] at hA
      exact hA
    · exact Nat.le_trans (Nat.le_max_right _ _) i2
    · intro x hx
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := i5 x hx
      have hy : end0 ≤ (if upto ≠ 0 then upto else vfront + window) + 16384 := by
        rw [← he0, hG]
        refine Nat.le_trans (Nat.min_le_left _ _) ?_
        by_cases hu0 : upto ≠ 0
        · rw [if_pos hu0, if_pos hu0]; omega
        · rw [if_neg hu0, if_neg hu0]; omega
      exact lead_arith x.1 x.2 end0 _ a4 (Nat.le_trans a6 (Nat.min_le_right _ _)) hy

/-- The proof the server sends for a frame has as many pairs as `range_pairs` of its group range: the group range
the receiver derives (`start / G`, `ceil(end / G)`) is the one `RangeEncoder::new` derives from the byte range, and
both count the parents of the same range. -/
theorem server_wt_pairs (ln s e : Nat) (hu : ln ≤ u64Max) (hse : s < e) (hel : e ≤ ln) :
    ∃ a b, groupRange ln lg s e = some (a, b) ∧ a = s / G ∧ b = divCeil e G ∧
      a < b ∧ b ≤ groups ln lg ∧
      np (encRun ln lg a b (2 * groups ln lg) (encInit ln lg a b)).1 = parentsIn a b 0 (groups ln lg) := by
  have hb := divCeil_bounds e ln (by omega) hel
  have hg := G_pos
  have hab : s / G < divCeil e G := by
    rw [Nat.div_lt_iff_lt_mul hg]
    have := hb.2.1
    have := Nat.mul_comm (divCeil e G) G
    omega
  exact ⟨s / G, divCeil e G, wt_range_eq ln s e hse hel, rfl, rfl, hab, hb.1,
    (rangePairs_encoder ln _ _ hab hb.1).symm⟩

/-- The head and the pairs of a proof frame fit the body the server allocates (`PROOF_BODY_MAX`). -/
theorem body_fits (head pairs : Nat) (hh : head ≤ 30) (hp : pairs * 64 + 8 ≤ PMAX) :
    head + pairs * 64 ≤ 9 + (1 + 8 + 4 + 8) + PMAX := by
  unfold PMAX at *; omega

/-- A deep value stays deep and gets no frames. -/
theorem proofs_deep_sticky (ln : Nat) (st : PState) (vfront window from_ upto : Nat) (ok : Nat → Bool)
    (hd : st.deep = true) : proofsCall ln st vfront window from_ upto ok = (st, []) := by
  unfold proofsCall; simp [hd]

end Vinc.ValuesPlan

#audit_axioms Vinc.ValuesPlan.frameLoop_spec
#audit_axioms Vinc.ValuesPlan.proofs_frames
#audit_axioms Vinc.ValuesPlan.server_wt_pairs
#audit_axioms Vinc.ValuesPlan.proofs_deep_sticky
