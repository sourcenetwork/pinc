import Pinc.ValuesPlanSourceRead

/-!
# The response is the concatenation of its frames

`PlanM.byteAt` finds the frame of an offset with `locate` and reads one of its three parts. This file shows it is
the flat byte string of the response: `flat` is the concatenation, over every frame of the plan in order (range by
range, `Plan::frame` by `Plan::frame`), of the frame's bytes: the 16-byte header, the proof (the pairs, 64 bytes each,
from the store's outboard at the offsets `proof_pair` gives) and the group bytes (from the store's value).

* `flat_length`: the flat string is `total` bytes long.
* `byteAt_flat`: `byteAt p` is the byte of the flat string at `p`, for every `p` (none past the end).
* `readAt_closed`: `read_at(offset, n)` is the bytes of `flat[offset, offset + n)` up to the first byte the store
  lacks (`takeSome`).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesPlan
open Pinc.Layout Pinc.Encode

/-- The bytes of the proof of a frame: the pair `q` at bytes `64 q .. 64 q + 64`, each from the store's outboard at
the offset `proof_pair` gives; `none` where the pair has no offset or the store lacks the byte. -/
def PlanM.proofOpts (pl : PlanM) (st : Store) (f : FrameM) : List (Option Nat) :=
  (List.range f.plen).map (fun j => (pl.proofPair f (j / 64)).bind (fun base => st.ob (base + j % 64)))

/-- The bytes of one frame: header, proof, group. -/
def PlanM.frameOpts (pl : PlanM) (st : Store) (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (f : FrameM) :
    List (Option Nat) :=
  (hdrEnc f.off f.dlen (min f.plen 65535) f.follows).map some ++ pl.proofOpts st f ++
    (List.range f.dlen).map (fun j => st.val (f.off + j))

/-- The frames of range `i`, by `Plan::frame` for `k = 0, 1, ...`. -/
def PlanM.rangeFrames (pl : PlanM) (i : Nat) : List FrameM :=
  match pl.rs[i]? with
  | none => []
  | some r => (List.range (r.last - r.first)).filterMap (pl.frame i)

/-- Every frame of the plan, in the order of the response. -/
def PlanM.allFrames (pl : PlanM) : List FrameM := (List.range pl.rs.length).flatMap pl.rangeFrames

/-- The flat bytes of the response. -/
def PlanM.flat (pl : PlanM) (st : Store) (hdrEnc : Nat → Nat → Nat → Bool → List Nat) : List (Option Nat) :=
  pl.allFrames.flatMap (pl.frameOpts st hdrEnc)

/-- The byte at `p` of a list of optional bytes; none past the end. -/
def ixOpt (l : List (Option Nat)) (p : Nat) : Option Nat := (l[p]?).getD none

/-- The frames of the list are laid back to back from `s` to `t`. -/
def Chain : Nat → List FrameM → Nat → Prop
  | s, [], t => s = t
  | s, f :: L, t => f.start = s ∧ Chain f.fend L t

theorem Chain_append : ∀ (L1 L2 : List FrameM) (s m t : Nat), Chain s L1 m → Chain m L2 t → Chain s (L1 ++ L2) t := by
  intro L1
  induction L1 with
  | nil => intro L2 s m t h1 h2; simp only [Chain] at h1; subst h1; simpa using h2
  | cons f L ih =>
    intro L2 s m t h1 h2
    exact ⟨h1.1, ih L2 _ m t h1.2 h2⟩

theorem frameOpts_length (pl : PlanM) (st : Store) (hdrEnc : Nat → Nat → Nat → Bool → List Nat)
    (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16) (f : FrameM) :
    (pl.frameOpts st hdrEnc f).length = f.fend - f.start := by
  unfold PlanM.frameOpts PlanM.proofOpts FrameM.fend FrameM.dataStart
  simp only [List.length_append, List.length_map, List.length_range, hlen]
  have : HDR = 16 := rfl
  omega

theorem frameOpts_get {len : Nat} {pl : PlanM} (g : Good len pl) (st : Store)
    (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16)
    {i k : Nat} {f : FrameM} (hfr : pl.frame i k = some f) (j : Nat) (hj : j < f.fend - f.start) :
    ixOpt (pl.frameOpts st hdrEnc f) j = pl.byteAt st hdrEnc (f.start + j) := by
  obtain ⟨r, hr, hk⟩ := frame_some hfr
  have hloc : pl.locate (f.start + j) = some f := locate_frame g hr hk hfr (by omega) (by omega)
  have hH := hlen f.off f.dlen (min f.plen 65535) f.follows
  unfold PlanM.byteAt ixOpt
  rw [hloc]
  simp only []
  unfold PlanM.frameOpts PlanM.proofOpts
  have hs : f.fend = f.start + HDR + f.plen + f.dlen := rfl
  have hH16 : HDR = 16 := rfl
  by_cases hp1 : j < HDR
  · have hp1' : f.start + j < f.proofStart := by unfold FrameM.proofStart; omega
    simp only [hp1', ite_true, hdrByte, Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left (by simp [hH]; unfold HDR at hp1; omega),
      List.getElem?_append_left (by simp [hH]; unfold HDR at hp1; omega)]
    rw [List.getElem?_map]
    cases hb : (hdrEnc f.off f.dlen (min f.plen 65535) f.follows)[j]? <;> simp
  · by_cases hp2 : j < HDR + f.plen
    · have hp1' : ¬ f.start + j < f.proofStart := by unfold FrameM.proofStart; omega
      have hp2' : f.start + j < f.dataStart := by unfold FrameM.dataStart; omega
      simp only [hp1', hp2', ite_true, ite_false]
      rw [List.getElem?_append_left (by simp [hH]; omega), List.getElem?_append_right (by simp [hH]; omega)]
      simp only [List.length_map, hH, List.getElem?_map, List.getElem?_range, show j - 16 < f.plen by unfold HDR at *; omega,
        ite_true, Option.map_some]
      unfold FrameM.proofStart
      have e : f.start + j - (f.start + HDR) = j - 16 := by unfold HDR; omega
      rw [e]; simp
    · have hp1' : ¬ f.start + j < f.proofStart := by unfold FrameM.proofStart; omega
      have hp2' : ¬ f.start + j < f.dataStart := by unfold FrameM.dataStart; omega
      simp only [hp1', hp2', ite_false]
      rw [List.getElem?_append_right (by simp [hH, PlanM.proofOpts]; omega)]
      simp only [List.length_append, List.length_map, List.length_range, hH]
      have e : f.start + j - f.dataStart = j - (16 + f.plen) := by unfold FrameM.dataStart HDR; omega
      rw [e]
      simp [List.getElem?_map, List.getElem?_range, show j - (16 + f.plen) < f.dlen by unfold HDR at *; omega]

theorem flat_chain (pl : PlanM) (st : Store) (hdrEnc : Nat → Nat → Nat → Bool → List Nat)
    (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16) {len : Nat} (g : Good len pl) :
    ∀ (L : List FrameM) (s t : Nat), Chain s L t → (∀ f ∈ L, ∃ i k, pl.frame i k = some f) →
      (L.flatMap (pl.frameOpts st hdrEnc)).length = t - s ∧ s ≤ t ∧
      ∀ p, p < t - s → ixOpt (L.flatMap (pl.frameOpts st hdrEnc)) p = pl.byteAt st hdrEnc (s + p) := by
  intro L
  induction L with
  | nil => intro s t h _; simp only [Chain] at h; subst h; simp
  | cons f L ih =>
    intro s t h hm
    obtain ⟨hs, hc⟩ := h
    obtain ⟨i, k, hfr⟩ := hm f (List.mem_cons_self ..)
    obtain ⟨a, b, c⟩ := ih f.fend t hc (fun x hx => hm x (List.mem_cons_of_mem _ hx))
    have hl := frameOpts_length pl st hdrEnc hlen f
    have hfs : f.start < f.fend := by unfold FrameM.fend FrameM.dataStart; unfold HDR; omega
    refine ⟨?_, by omega, ?_⟩
    · simp only [List.flatMap_cons, List.length_append, hl, a]; omega
    · intro p hp
      simp only [List.flatMap_cons]
      unfold ixOpt
      by_cases hpl : p < f.fend - f.start
      · rw [List.getElem?_append_left (by rw [hl]; exact hpl)]
        have := frameOpts_get g st hdrEnc hlen hfr p hpl
        unfold ixOpt at this
        rw [this, hs]
      · rw [List.getElem?_append_right (by rw [hl]; omega), hl]
        have := c (p - (f.fend - f.start)) (by omega)
        unfold ixOpt at this
        have e : f.fend + (p - (f.fend - f.start)) = s + p := by omega
        rw [this, e]

theorem rangeFrames_chain {len : Nat} {pl : PlanM} (g : Good len pl) {i : Nat} {r : PR} (hr : pl.rs[i]? = some r) :
    ∀ n, n ≤ r.last - r.first →
      Chain r.start ((List.range n).filterMap (pl.frame i)) (r.start + sumTo (fb len r.first) n) := by
  intro n
  induction n with
  | zero => intro _; simp [Chain, sumTo]
  | succ n ih =>
    intro hn
    obtain ⟨f, hf, _, _, _, s1, e1, _⟩ := frame_spec g hr (show n < r.last - r.first by omega)
    rw [List.range_succ, List.filterMap_append]
    refine Chain_append _ _ _ _ _ (ih (by omega)) ?_
    simp only [List.filterMap_cons, List.filterMap_nil, hf]
    exact ⟨s1, by rw [e1]; trivial⟩

theorem allFrames_chain {len : Nat} {pl : PlanM} (g : Good len pl) :
    ∀ n, n ≤ pl.rs.length →
      Chain 0 ((List.range n).flatMap pl.rangeFrames) (((pl.rs.take n).map (szr len)).sum) := by
  intro n
  induction n with
  | zero => intro _; simp [Chain]
  | succ n ih =>
    intro hn
    have hi : n < pl.rs.length := by omega
    obtain ⟨r, hr⟩ : ∃ r, pl.rs[n]? = some r := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨h1, h2, h3⟩ := g.range hr
    rw [List.range_succ, List.flatMap_append]
    have hc := rangeFrames_chain g hr (r.last - r.first) (Nat.le_refl _)
    refine Chain_append _ _ _ _ _ (ih (by omega)) ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, PlanM.rangeFrames, hr]
    have e := frame_range_end g hr
    rw [List.take_succ, hr]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil]
    rw [h3] at hc e
    rw [show ((pl.rs.take n).map (szr len)).sum + (szr len r + 0) =
      ((pl.rs.take n).map (szr len)).sum + szr len r by omega, ← e]
    exact hc

theorem allFrames_mem {pl : PlanM} {f : FrameM} (h : f ∈ pl.allFrames) : ∃ i k, pl.frame i k = some f := by
  unfold PlanM.allFrames at h
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.1 h
  unfold PlanM.rangeFrames at hi
  cases hr : pl.rs[i]? with
  | none => rw [hr] at hi; simp at hi
  | some r =>
    rw [hr] at hi
    obtain ⟨k, _, hk⟩ := List.mem_filterMap.1 hi
    exact ⟨i, k, hk⟩

theorem allFrames_chain_total {len : Nat} {pl : PlanM} (g : Good len pl) : Chain 0 pl.allFrames pl.total := by
  obtain ⟨_, htot, _⟩ := RO_index len pl.rs 0 pl.total g.ro
  have := allFrames_chain g pl.rs.length (Nat.le_refl _)
  rw [List.take_length, ← Nat.zero_add (pl.rs.map (szr len)).sum, ← htot] at this
  exact this

/-- The response is `total` bytes. -/
theorem flat_length {len : Nat} {pl : PlanM} (g : Good len pl) (st : Store)
    (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16) :
    (pl.flat st hdrEnc).length = pl.total := by
  have := (flat_chain pl st hdrEnc hlen g _ _ _ (allFrames_chain_total g) (fun f hf => allFrames_mem hf)).1
  unfold PlanM.flat; omega

/-- `byteAt` is the byte of the flat concatenation of the frames, at every offset. -/
theorem byteAt_flat {len : Nat} {pl : PlanM} (g : Good len pl) (st : Store)
    (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16) (p : Nat) :
    pl.byteAt st hdrEnc p = ixOpt (pl.flat st hdrEnc) p := by
  by_cases hp : p < pl.total
  · have := (flat_chain pl st hdrEnc hlen g _ _ _ (allFrames_chain_total g) (fun f hf => allFrames_mem hf)).2.2 p (by omega)
    unfold PlanM.flat
    rw [Nat.zero_add] at this
    exact this.symm
  · have h1 := flat_length g st hdrEnc hlen
    unfold ixOpt
    rw [List.getElem?_eq_none (by omega)]
    simp [PlanM.byteAt, locate_end (pl := pl) p (by omega)]

/-- The leading present bytes of a list of optional bytes. -/
def takeSome : List (Option Nat) → List Nat
  | [] => []
  | none :: _ => []
  | some b :: t => b :: takeSome t

theorem availFn_flat (g : Nat → Option Nat) (l : List (Option Nat)) (hg : ∀ p, g p = ixOpt l p) :
    ∀ n p, availFn g p n = takeSome ((l.drop p).take n) := by
  intro n
  induction n with
  | zero => intro p; simp [availFn, takeSome]
  | succ n ih =>
    intro p
    rw [availFn_succ, hg p]
    unfold ixOpt
    by_cases hp : p < l.length
    · rw [List.getElem?_eq_getElem hp]
      have hd : l.drop p = l[p] :: l.drop (p + 1) := List.drop_eq_getElem_cons hp
      rw [hd, List.take_succ_cons]
      cases hb : l[p] with
      | none => simp [takeSome]
      | some b => simp only [Option.getD_some, takeSome]; rw [ih (p + 1)]
    · rw [List.getElem?_eq_none (by omega)]
      simp [List.drop_eq_nil_of_le (show l.length ≤ p by omega), takeSome]

/-- The closed form of `read_at`: the flat bytes of the response from the offset, `n` of them, up to the first byte
the store lacks. -/
theorem readAt_closed {len : Nat} {pl : PlanM} (g : Good len pl) (st : Store)
    (hdrEnc : Nat → Nat → Nat → Bool → List Nat) (hlen : ∀ a b c d, (hdrEnc a b c d).length = 16) (offset n : Nat) :
    pl.readAt st hdrEnc offset n = takeSome (((pl.flat st hdrEnc).drop offset).take n) := by
  rw [readAt_spec g st hdrEnc hlen]
  exact availFn_flat _ _ (byteAt_flat g st hdrEnc hlen) n offset

end Pinc.ValuesPlan

#audit_axioms Pinc.ValuesPlan.frameOpts_get
#audit_axioms Pinc.ValuesPlan.flat_length
#audit_axioms Pinc.ValuesPlan.byteAt_flat
#audit_axioms Pinc.ValuesPlan.readAt_closed
