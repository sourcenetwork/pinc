import Pinc.ValuesPlanSource

/-!
# `read_at` is `availFn byteAt`

The chunk `fill` writes is the response bytes of its part (`fill_spec`); the loop of `read_at` strings the
chunks and stops on a short one (`rdF_spec`); the window never changes the answer. See `ValuesPlanSource`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesPlan
open Pinc.Layout Pinc.Encode

theorem availFn_list (g : Nat → Option Nat) (l : List Nat) : ∀ n p, (∀ w, w < n → g (p + w) = l[w]?) →
    n ≤ l.length → availFn g p n = l.take n := by
  intro n
  induction n generalizing l with
  | zero => intro p _ _; simp [availFn]
  | succ n ih =>
    intro p hw hn
    rw [availFn_succ]
    have h0 := hw 0 (by omega)
    simp only [Nat.add_zero] at h0
    cases l with
    | nil => simp at hn
    | cons x t =>
      simp only [List.getElem?_cons_zero] at h0
      rw [h0]
      simp only [List.take_succ_cons]
      rw [ih t (p + 1) (fun w hw' => by
        have := hw (w + 1) (by omega)
        rwa [show p + (w + 1) = p + 1 + w by omega, List.getElem?_cons_succ] at this) (by simpa using hn)]

/-- Every pair of a frame's proof has an offset. -/
theorem proofPair_some {len : Nat} {pl : PlanM} (g : Good len pl) {i k : Nat} {r : PR} {f : FrameM}
    (hr : pl.rs[i]? = some r) (hk : k < r.last - r.first) (hfr : pl.frame i k = some f) (pair : Nat)
    (hpair : pair * 64 < f.plen) : ∃ base, pl.proofPair f pair = some base := by
  obtain ⟨h1, h2, _⟩ := g.range hr
  obtain ⟨f2, hf2, ra, ka, _, _, _, hplen, hdlen, _⟩ := frame_spec g hr hk
  have e2 : f = f2 := Option.some.inj (hfr.symm.trans hf2)
  subst e2
  obtain ⟨hpp, _⟩ := proofPair_spec g hr hk hfr pair
  rw [refFrames_get len r.first r.last k h1 h2 hk] at hpp
  have hpl2 := frame_pend len lg (groups len lg) r.first k
  rw [hpp]
  simp only [Option.bind_some]
  have : ((frameOf len lg 0 (groups len lg) 0 r.first [] (r.first + k)).1)[pair]? ≠ none := by
    rw [Ne, List.getElem?_eq_none_iff]; simp only [Nat.not_le]; rw [hpl2]
    unfold PARL at hplen; omega
  exact Option.ne_none_iff_exists'.1 this

/-- What a chunk of the part the offset is in is. -/
theorem fill_spec {len : Nat} {pl : PlanM} (g : Good len pl) (st : Store) (hdrEnc : Nat → Nat → Nat → Bool → List Nat)
    (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16) {at_ rem : Nat} {f : FrameM} (hf : pl.locate at_ = some f)
    (hrem : 1 ≤ rem) :
    1 ≤ (pl.fillM st hdrEnc f at_ rem).2 ∧ (pl.fillM st hdrEnc f at_ rem).2 ≤ rem ∧
      at_ + (pl.fillM st hdrEnc f at_ rem).2 ≤ f.fend ∧
      (pl.fillM st hdrEnc f at_ rem).1 = availFn (pl.byteAt st hdrEnc) at_ (pl.fillM st hdrEnc f at_ rem).2 := by
  obtain ⟨i, r, k, hr, hk, hfr, hs, he⟩ := locate_valid g hf
  obtain ⟨f2, hf2, ra, ka, _, _, _, hplen, hdlen, _⟩ := frame_spec g hr hk
  have e2 : f = f2 := Option.some.inj (hfr.symm.trans hf2)
  subst e2
  obtain ⟨h1, h2, _⟩ := g.range hr
  have hdpos : 0 < f.dlen := by
    rw [hdlen]
    exact (groupSize_pos_iff len lg _ g.hlen).2 (by omega)
  have hloc : ∀ p, f.start ≤ p → p < f.fend → pl.locate p = some f := fun p a b => locate_frame g hr hk hfr a b
  unfold PlanM.fillM
  by_cases hp1 : at_ < f.proofStart
  · simp only [hp1, ite_true]
    have hH := hlen f.off f.dlen (min f.plen 65535) f.follows
    have hrel : f.proofStart = f.start + 16 := rfl
    have hn : min ((hdrEnc f.off f.dlen (min f.plen 65535) f.follows).drop (at_ - f.start)).length rem ≥ 1 := by
      simp only [List.length_drop, hH]; omega
    have hpf : f.proofStart ≤ f.fend := by unfold FrameM.fend FrameM.dataStart FrameM.proofStart; omega
    refine ⟨hn, by omega, ?_, ?_⟩
    · simp only [List.length_drop, hH]; omega
    · symm
      apply availFn_list
      · intro w hw
        simp only [List.length_drop, hH] at hw
        have hl := hloc (at_ + w) (by omega) (by omega)
        unfold PlanM.byteAt
        rw [hl]
        simp only [show at_ + w < f.proofStart by omega, ite_true, hdrByte, List.getElem?_drop]
        congr 1; omega
      · simp only [List.length_drop, hH]; omega
  · by_cases hp2 : at_ < f.dataStart
    · simp only [hp1, hp2, ite_true, ite_false]
      have hpl : f.plen = pendLen (groups len lg) r.first k * PARL := hplen
      have hinto : at_ - f.proofStart < f.plen := by unfold FrameM.dataStart FrameM.proofStart at *; omega
      have hpair : (at_ - f.proofStart) / 64 < pendLen (groups len lg) r.first k := by
        unfold PARL at hpl; omega
      have hsome : ∃ base, pl.proofPair f ((at_ - f.proofStart) / 64) = some base :=
        proofPair_some g hr hk hfr _ (by omega)
      obtain ⟨base, hbase⟩ := hsome
      simp only [hbase]
      have hroom : 1 ≤ min (64 - (at_ - f.proofStart) % 64) rem := by
        have : (at_ - f.proofStart) % 64 < 64 := Nat.mod_lt _ (by omega)
        omega
      refine ⟨hroom, by omega, ?_, ?_⟩
      · unfold FrameM.fend FrameM.dataStart FrameM.proofStart at *
        have : (at_ - (f.start + HDR)) / 64 * 64 + 64 ≤ f.plen := by
          unfold PARL at hpl; unfold HDR at *; omega
        omega
      · symm
        apply availFn_congr
        intro w hw
        have hw1 : w < 64 - (at_ - f.proofStart) % 64 := by omega
        have hmod : (at_ - f.proofStart) % 64 < 64 := Nat.mod_lt _ (by omega)
        have hdiv : (at_ + w - f.proofStart) / 64 = (at_ - f.proofStart) / 64 := by omega
        have hmod2 : (at_ + w - f.proofStart) % 64 = (at_ - f.proofStart) % 64 + w := by omega
        have hlt : at_ + w < f.dataStart := by
          have : (at_ - f.proofStart) / 64 * 64 + 64 ≤ f.plen := by
            unfold PARL at hpl; omega
          unfold FrameM.dataStart FrameM.proofStart at *; omega
        have hl := hloc (at_ + w) (by unfold FrameM.proofStart at *; omega)
          (by unfold FrameM.fend; omega)
        unfold PlanM.byteAt
        rw [hl]
        simp only [show ¬ at_ + w < f.proofStart by omega, hlt, ite_true, ite_false, hdiv, hmod2, hbase, Option.bind_some]
        congr 1; omega
    · simp only [hp1, hp2, ite_false]
      have hroom : 1 ≤ min (f.dlen - (at_ - f.dataStart)) rem := by
        have : at_ < f.fend := he
        unfold FrameM.fend at this; omega
      refine ⟨hroom, by omega, ?_, ?_⟩
      · have : at_ < f.fend := he
        unfold FrameM.fend at *; omega
      · symm
        apply availFn_congr
        intro w hw
        have hl := hloc (at_ + w) (by unfold FrameM.dataStart FrameM.proofStart at *; omega)
          (by unfold FrameM.fend at *; omega)
        unfold PlanM.byteAt
        rw [hl]
        simp only [show ¬ at_ + w < f.proofStart by unfold FrameM.dataStart FrameM.proofStart at *; omega,
          show ¬ at_ + w < f.dataStart by omega, ite_false]
        congr 1; omega

/-- The loop of `read_at` returns the response bytes from the offset, as many as are present. -/
theorem rdF_spec {len : Nat} {pl : PlanM} (g : Good len pl) (st : Store) (hdrEnc : Nat → Nat → Nat → Bool → List Nat)
    (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16) :
    ∀ (fuel : Nat) (win : List (Option FrameM)) (at_ rem : Nat), WinInv pl win → rem ≤ fuel →
      (pl.rdF st hdrEnc fuel win at_ rem).1 = availFn (pl.byteAt st hdrEnc) at_ rem ∧
        WinInv pl (pl.rdF st hdrEnc fuel win at_ rem).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro win at_ rem hw hr
    have : rem = 0 := by omega
    subst this
    simp [PlanM.rdF, availFn, hw]
  | succ fuel ih =>
    intro win at_ rem hw hr
    by_cases h0 : rem = 0
    · subst h0; simp [PlanM.rdF, availFn, hw]
    · obtain ⟨hfa, hwin'⟩ := frameAtM_spec g hw at_
      unfold PlanM.rdF
      simp only [h0, ite_false]
      rcases hfa' : pl.frameAtM win at_ with ⟨o, win'⟩
      rw [hfa'] at hfa hwin'
      simp only [] at hfa hwin'
      subst hfa
      cases hl : pl.locate at_ with
      | none =>
        simp only []
        refine ⟨?_, hwin'⟩
        obtain ⟨r', rfl⟩ : ∃ r', rem = r' + 1 := ⟨rem - 1, by omega⟩
        rw [availFn_succ]
        simp [PlanM.byteAt, hl]
      | some f =>
        simp only []
        obtain ⟨a1, a2, a3, a4⟩ := fill_spec g st hdrEnc hlen hl (show 1 ≤ rem by omega)
        rw [a4]
        generalize hw' : (pl.fillM st hdrEnc f at_ rem).2 = wanted at a1 a2 a3 ⊢
        have hsplit := availFn_split (pl.byteAt st hdrEnc) wanted rem at_ a2
        have hle := availFn_length_le (pl.byteAt st hdrEnc) wanted at_
        by_cases hs : (availFn (pl.byteAt st hdrEnc) at_ wanted).length < wanted
        · simp only [hs, ite_true]
          refine ⟨?_, hwin'⟩
          rw [hsplit, if_neg (by omega)]; simp
        · simp only [hs, ite_false]
          have heq : (availFn (pl.byteAt st hdrEnc) at_ wanted).length = wanted := by omega
          rw [heq]
          obtain ⟨b1, b2⟩ := ih win' (at_ + wanted) (rem - wanted) hwin' (by omega)
          refine ⟨?_, b2⟩
          rw [b1, hsplit, if_pos heq]

/-- `ValueSource::read_at` from a fresh window. -/
def PlanM.readAt (pl : PlanM) (st : Store) (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (offset n : Nat) : List Nat :=
  (pl.rdF st hdrEnc n (List.replicate 16 none) offset n).1

theorem WinInv_empty (pl : PlanM) : WinInv pl (List.replicate 16 none) := by
  intro f hf; simp [List.filterMap_replicate] at hf

/-- `read_at` returns exactly the response bytes from the offset: as many as asked, fewer only at the end of the
response or where the store lacks the byte. -/
theorem readAt_spec {len : Nat} {pl : PlanM} (g : Good len pl) (st : Store)
    (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16) (offset n : Nat) :
    pl.readAt st hdrEnc offset n = availFn (pl.byteAt st hdrEnc) offset n :=
  (rdF_spec g st hdrEnc hlen n _ offset n (WinInv_empty pl) (Nat.le_refl _)).1

/-- A retransmission, from any window of the plan's frames, equals the first send. -/
theorem readAt_retx {len : Nat} {pl : PlanM} (g : Good len pl) (st : Store)
    (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16)
    (win : List (Option FrameM)) (hw : WinInv pl win) (offset n : Nat) :
    (pl.rdF st hdrEnc n win offset n).1 = pl.readAt st hdrEnc offset n := by
  rw [readAt_spec g st hdrEnc hlen]
  exact (rdF_spec g st hdrEnc hlen n win offset n hw (Nat.le_refl _)).1

/-- A read is a prefix of a longer read from the same offset. -/
theorem readAt_prefix {len : Nat} {pl : PlanM} (g : Good len pl) (st : Store)
    (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16) (offset m n : Nat)
    (h : m ≤ n) : pl.readAt st hdrEnc offset m =
      (pl.readAt st hdrEnc offset n).take m := by
  rw [readAt_spec g st hdrEnc hlen, readAt_spec g st hdrEnc hlen]
  have hs := availFn_split (pl.byteAt st hdrEnc) m n offset h
  have hl := availFn_length_le (pl.byteAt st hdrEnc) m offset
  rw [hs]
  by_cases hc : (availFn (pl.byteAt st hdrEnc) offset m).length = m
  · rw [if_pos hc, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  · rw [if_neg hc, List.append_nil, List.take_of_length_le (by omega)]

/-- The byte function is none exactly past the response or at a byte the store lacks. -/
theorem byteAt_none {len : Nat} {pl : PlanM} (g : Good len pl) (st : Store)
    (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16) {p : Nat}
    (h : pl.byteAt st hdrEnc p = none) :
    pl.total ≤ p ∨ ∃ f, pl.locate p = some f ∧
      ((f.dataStart ≤ p ∧ st.val (f.off + (p - f.dataStart)) = none) ∨
       (f.proofStart ≤ p ∧ p < f.dataStart ∧ ∃ base, pl.proofPair f ((p - f.proofStart) / 64) = some base ∧
          st.ob (base + (p - f.proofStart) % 64) = none)) := by
  by_cases ht : pl.total ≤ p
  · exact Or.inl ht
  · right
    obtain ⟨f, hl, hs, he⟩ := locate_some g (show p < pl.total by omega)
    refine ⟨f, hl, ?_⟩
    unfold PlanM.byteAt at h
    rw [hl] at h
    simp only [] at h
    by_cases hp1 : p < f.proofStart
    · simp only [hp1, ite_true, hdrByte] at h
      have := hlen f.off f.dlen (min f.plen 65535) f.follows
      rw [List.getElem?_eq_none_iff] at h
      have hH : HDR = 16 := rfl
      unfold FrameM.proofStart at hp1; omega
    · by_cases hp2 : p < f.dataStart
      · simp only [hp1, hp2, ite_true, ite_false] at h
        obtain ⟨i, r, k, hr, hk, hfr, _, _⟩ := locate_valid g hl
        obtain ⟨f2, hf2, ra, ka, _, _, _, hplen, _, _⟩ := frame_spec g hr hk
        have e2 : f = f2 := Option.some.inj (hfr.symm.trans hf2)
        subst e2
        have hpair : (p - f.proofStart) / 64 * 64 < f.plen := by
          unfold FrameM.dataStart FrameM.proofStart at *
          unfold PARL at hplen; omega
        obtain ⟨base, hbase⟩ := proofPair_some g hr hk hfr _ hpair
        rw [hbase] at h
        exact Or.inr ⟨by omega, hp2, base, hbase, by simpa using h⟩
      · simp only [hp1, hp2, ite_false] at h
        exact Or.inl ⟨by omega, h⟩

/-- A short return happens only at the end of the response or at a byte the store lacks. -/
theorem readAt_short {len : Nat} {pl : PlanM} (g : Good len pl) (st : Store)
    (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16) (offset n : Nat)
    (h : (pl.readAt st hdrEnc offset n).length < n) :
    pl.byteAt st hdrEnc (offset + (pl.readAt st hdrEnc offset n).length) = none := by
  rw [readAt_spec g st hdrEnc hlen] at h ⊢
  clear hlen
  generalize pl.byteAt st hdrEnc = bf at *
  induction n generalizing offset with
  | zero => simp [availFn] at h
  | succ n ih =>
    rw [availFn_succ] at h ⊢
    cases hb : bf offset with
    | none => simp [hb]
    | some b =>
      simp only [hb, List.length_cons] at h ⊢
      have := ih (offset + 1) (by omega)
      rw [show offset + ((availFn bf (offset + 1) n).length + 1) = offset + 1 + (availFn bf (offset + 1) n).length by omega]
      exact this

end Pinc.ValuesPlan

#audit_axioms Pinc.ValuesPlan.fill_spec
#audit_axioms Pinc.ValuesPlan.rdF_spec
#audit_axioms Pinc.ValuesPlan.readAt_spec
#audit_axioms Pinc.ValuesPlan.readAt_retx
#audit_axioms Pinc.ValuesPlan.readAt_prefix
#audit_axioms Pinc.ValuesPlan.byteAt_none
#audit_axioms Pinc.ValuesPlan.readAt_short
#audit_axioms Pinc.ValuesPlan.frameAtM_spec
