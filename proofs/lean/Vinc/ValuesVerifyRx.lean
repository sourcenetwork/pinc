import Vinc.ValuesVerifySound

/-!
# The receive state (`fetch/rx.rs`) and the verifier: always at an item boundary

`Rx::pump` frames the response of one request stream: a 16-byte GROUP header, `plen` bytes of proof pairs, then the
group bytes. This module models the part of it that talks to `GroupVerifier` (`RxM`): the header step
(`hdrDone`), `proof`, `enter_data` (`enterData`: the verifier must be waiting for exactly this frame's group at the
start of it; when the store already holds the group verified, `skip_group`), and `data` (feeding the group bytes, or
nothing when skipped). A `none` result is the provider being reported (`Pump::Bad`).

`RxInv` is the invariant and `hdrDone_inv`, `proofStep_inv`, `dataStep_inv` the preservation:

* in the `Header` phase the verifier is at the start of an item (`at_boundary`), so a new frame starts cleanly;
* in the proof phase it holds no half-fed group; `enter_data` accepts only at a boundary, so a proof that does not
  end on a pair boundary is refused;
* in the data phase of a group that is fed, the verifier waits for exactly that group (offset and length) and has
  taken `len - left` of its bytes; in the data phase of a skipped group it is at a boundary and untouched;
* `enterData_total`: after the checks of `enter_data` the `skip_group` it calls cannot fail;
* `feedG_group_nf` (used by `dataStep_inv`): the `data` call is always given a verifier that takes all `min(piece, left)` bytes, so the
  `fed.consumed != take` refusal is unreachable.

The verifier of the next range is a fresh one (`initG`), at a boundary, the same state as at the start.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Vinc.ValuesVerify
open Vinc.Layout Vinc.Tree Vinc.Machine Vinc.VerifyBytes

/-- The phase of one frame (`Phase`). -/
inductive Ph where
  | header
  | proof (left : Nat)
  | data (left : Nat) (skip : Bool)

/-- The part of `Rx` that talks to the verifier: the verifier, the phase, the header being served (offset, length). -/
structure RxM (Cv : Type) where
  ver : GS Cv
  ph : Ph
  cur : Option (Nat × Nat)

section
variable {Cv : Type} [DecidableEq Cv]

/-- `Rx::enter_data`: the proof is fully fed. `d` is ghost (the store's verified bytes of the group, used when it
is stored). -/
def enterData (c : Cfg Cv) (stored : Bool) (d : Bytes) (rx : RxM Cv) : Option (RxM Cv) :=
  match rx.cur with
  | none => none
  | some (off, len) =>
    if nextItemG c rx.ver = some (.group off len) ∧ atBoundaryG rx.ver = true then
      if stored then
        match skipG c rx.ver d with
        | (.error _, _) => none
        | (.ok _, v1) => some { rx with ver := v1, ph := .data len true }
      else some { rx with ph := .data len false }
    else none

/-- `Rx::header` once the 16 header bytes are in and parse: the proof of `plen` bytes follows (`enter_data` at once if
there is none). -/
def hdrDone (c : Cfg Cv) (off len plen : Nat) (stored : Bool) (d : Bytes) (rx : RxM Cv) : Option (RxM Cv) :=
  let rx1 : RxM Cv := { rx with cur := some (off, len), ph := .proof plen }
  if plen = 0 then enterData c stored d rx1 else some rx1

/-- `Rx::proof` on a piece: `take = min(piece, left)` bytes to the verifier, which must be waiting for a pair. -/
def proofStep (w : Nat) (c : Cfg Cv) (stored : Bool) (d : Bytes) (rx : RxM Cv) (left : Nat) (piece : Bytes) :
    Option (RxM Cv) :=
  if nextItemG c rx.ver ≠ some .pair then none
  else
    match feedG w c rx.ver (piece.take (min piece.length left)) with
    | some (.ok consumed _, v1) =>
      if left - consumed = 0 then enterData c stored d { rx with ver := v1, ph := .proof 0 }
      else some { rx with ver := v1, ph := .proof (left - consumed) }
    | _ => none

/-- `Rx::data` on a piece of a group: the verifier takes all of `min(piece, left)` bytes (or nothing is fed when the
group is skipped); the frame ends when no byte is left. -/
def dataStep (w : Nat) (c : Cfg Cv) (rx : RxM Cv) (left : Nat) (skip : Bool) (piece : Bytes) : Option (RxM Cv) :=
  let take := min piece.length left
  let v1 : Option (GS Cv) :=
    if skip then some rx.ver
    else match feedG w c rx.ver (piece.take take) with
      | some (.ok consumed _, v1) => if consumed = take then some v1 else none
      | _ => none
  match v1 with
  | none => none
  | some v1 =>
    if 0 < left - take then some { rx with ver := v1, ph := .data (left - take) skip }
    else some { rx with ver := v1, ph := .header, cur := none }

/-- WHOLE_GROUP (`fetch/recv.rs` `drain`): the fetch feeds a group only once all of its bytes are stored, in the
pieces the session keeps them in (at most two for a 16 KiB group: one per receive chunk), never one per packet. So
each `data` step is given every stored byte up to the end of its piece, and the last one holds all `left` bytes the
group still needs. Such a step finishes the frame: it ends in the header phase with no header open.
(`group_split_invariance` says the verifier decides the same for every split, so feeding later decides the same.) -/
theorem dataStep_whole (w : Nat) (c : Cfg Cv) (rx rx' : RxM Cv) (left : Nat) (skip : Bool) (piece : Bytes)
    -- the piece holds every byte the group still needs
    (hge : left ≤ piece.length)
    -- and the step accepted it
    (h : dataStep w c rx left skip piece = some rx') :
    rx'.ph = .header ∧ rx'.cur = none := by
  -- the step takes `min piece.length left = left` bytes, so none of the group is left after it
  have hm : min piece.length left = left := Nat.min_eq_right hge
  unfold dataStep at h
  simp only [hm, Nat.sub_self, Nat.lt_irrefl, ite_false] at h
  -- whatever the verifier did, an accepted step can only be the branch that closes the frame
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- The invariant of the receive state. -/
def RxInv (w : Nat) (c : Cfg Cv) (root : Cv) (rx : RxM Cv) : Prop :=
  Reach w c root rx.ver ∧
  match rx.ph with
  | .header => atBoundaryG rx.ver = true ∧ rx.cur = none
  | .proof left => rx.ver.hb = [] ∧ rx.cur.isSome = true ∧ 0 < left
  | .data left false => ∃ off len, rx.cur = some (off, len) ∧ nextItemG c rx.ver = some (.group off len) ∧
      rx.ver.pair = [] ∧ rx.ver.hb.length + left = len ∧ 0 < left
  | .data left true => atBoundaryG rx.ver = true ∧ 0 < left

theorem nextItem_failed (c : Cfg Cv) (s : GS Cv) (it : GItem) (h : nextItemG c s = some it) : s.failed = none := by
  cases hfs : s.failed with
  | none => rfl
  | some e => simp [nextItemG, hfs] at h

theorem nextItem_pair (c : Cfg Cv) (s : GS Cv) (h : nextItemG c s = some .pair) :
    s.failed = none ∧ ∃ nd rest, s.stack = nd :: rest ∧ ¬ nd.hi - nd.lo = 1 := by
  refine ⟨nextItem_failed c s _ h, ?_⟩
  have hf := nextItem_failed c s _ h
  rcases hs : s.stack with _ | ⟨nd, rest⟩
  · simp [nextItemG, hf, hs] at h
  · refine ⟨nd, rest, rfl, ?_⟩
    intro hl; simp [nextItemG, hf, hs, hl] at h

theorem nextItem_group (c : Cfg Cv) (s : GS Cv) (off len : Nat) (h : nextItemG c s = some (.group off len)) :
    s.failed = none ∧ ∃ nd rest, s.stack = nd :: rest ∧ nd.hi - nd.lo = 1 ∧ off = nd.lo * groupLen c.log ∧
      len = groupSize c.len c.log nd.lo := by
  refine ⟨nextItem_failed c s _ h, ?_⟩
  have hf := nextItem_failed c s _ h
  rcases hs : s.stack with _ | ⟨nd, rest⟩
  · simp [nextItemG, hf, hs] at h
  · refine ⟨nd, rest, rfl, ?_⟩
    by_cases hl : nd.hi - nd.lo = 1
    · simp [nextItemG, hf, hs, hl] at h; exact ⟨hl, h.1.symm, h.2.symm⟩
    · simp [nextItemG, hf, hs, hl] at h

/-- After the checks of `enter_data`, the `skip_group` it calls does not fail, and `enter_data` accepts. -/
theorem enterData_total (c : Cfg Cv) (stored : Bool) (d : Bytes) (rx : RxM Cv) (off len : Nat)
    (hcur : rx.cur = some (off, len)) (hi : nextItemG c rx.ver = some (.group off len))
    (hb : atBoundaryG rx.ver = true) : ∃ rx1, enterData c stored d rx = some rx1 := by
  obtain ⟨nd, rest, hs, hsk⟩ := skipG_ok c rx.ver d off len hi hb
  by_cases hst : stored = true
  · refine ⟨{ rx with ver := (skipG c rx.ver d).2, ph := .data len true }, ?_⟩
    simp [enterData, hcur, hi, hb, hst, hsk]
  · exact ⟨{ rx with ph := .data len false }, by simp [enterData, hcur, hi, hb, hst]⟩

theorem finishGroupG_ok_state (c : Cfg Cv) (s s1 : GS Cv) (nd : Node Cv) (rest : List (Node Cv)) (data : Bytes)
    (take size k : Nat) (v : Option (Nat × Nat))
    (h : finishGroupG c s nd rest data take size = some (.ok k v, s1)) :
    k = take ∧ s1.hb = [] ∧ s1.pair = s.pair := by
  unfold finishGroupG at h
  split at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq, GR.ok.injEq] at h
      obtain ⟨⟨h1, -⟩, rfl⟩ := h
      exact ⟨h1.symm, rfl, rfl⟩
  · simp at h

section
variable (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hrd : ∀ b, (c.rd b).d = b)
  (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20) (hn : c.n = groups c.len c.log) (hl : c.last ≤ c.n)
include hw hrd hlen hlog hn hl

theorem group_len_pos {s : GS Cv} (hg : Good c s) (off len : Nat) (h : nextItemG c s = some (.group off len)) :
    0 < len := by
  obtain ⟨-, nd, rest, hs, hleaf, -, hlenE⟩ := nextItem_group c s off len h
  have hnd := hg.nodes nd rest hs
  have := (groupSize_pos_iff c.len c.log nd.lo hlen).2 (by rw [← hn]; omega)
  omega

variable {root : Cv}

/-- `enter_data` keeps the invariant: it accepts only a verifier waiting for this frame's group at the start of it, and
the `skip_group` it calls then succeeds (`enterData_total`). When the group is stored, `d` is the store's verified
copy: the length of the group, hashing to the chaining value committed for it. -/
theorem enterData_inv (stored : Bool) (d : Bytes) (rx rx' : RxM Cv) (hR : Reach w c root rx.ver)
    (hstore : stored = true → ∀ nd rest, rx.ver.stack = nd :: rest → nd.hi - nd.lo = 1 →
      c.H.leaf (isRoot c.n nd.lo nd.hi) nd.lo d = nd.cv ∧ d.length = groupSize c.len c.log nd.lo)
    (h : enterData c stored d rx = some rx') : RxInv w c root rx' := by
  have hg := reach_good w hw c hrd hlen hlog hn hl hR
  unfold enterData at h
  split at h
  · simp at h
  · rename_i off len hcur
    split at h
    · rename_i hcond
      obtain ⟨hi, hb⟩ := hcond
      have hpos := group_len_pos w hw c hrd hlen hlog hn hl hg off len hi
      have hb' : rx.ver.pair.length = 0 ∧ rx.ver.hb.length = 0 := by simpa [atBoundaryG] using hb
      by_cases hst : stored = true
      · simp only [hst, ite_true] at h
        obtain ⟨nd, rest, hs, hsk⟩ := skipG_ok c rx.ver d off len hi hb
        rw [hsk] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨?_, ?_, hpos⟩
        · have := Reach.skip (w := w) (c := c) (root := root) d hR (hstore hst)
          rw [hsk] at this
          exact this
        · simp [atBoundaryG, hb'.1, hb'.2]
      · have hst' : stored = false := by simpa using hst
        simp only [hst', Bool.false_eq_true, ite_false, Option.some.injEq] at h
        subst h
        refine ⟨hR, off, len, hcur, hi, List.length_eq_zero_iff.1 hb'.1, by simp [hb'.2], hpos⟩
    · simp at h

/-- The header is complete: the verifier is at the start of an item, and stays so unless `enter_data` runs at once. -/
theorem hdrDone_inv (off len plen : Nat) (stored : Bool) (d : Bytes) (rx rx' : RxM Cv)
    (hI : RxInv w c root rx) (hph : rx.ph = .header)
    (hstore : stored = true → ∀ nd rest, rx.ver.stack = nd :: rest → nd.hi - nd.lo = 1 →
      c.H.leaf (isRoot c.n nd.lo nd.hi) nd.lo d = nd.cv ∧ d.length = groupSize c.len c.log nd.lo)
    (h : hdrDone c off len plen stored d rx = some rx') : RxInv w c root rx' := by
  obtain ⟨hR, hb, -⟩ : Reach w c root rx.ver ∧ atBoundaryG rx.ver = true ∧ rx.cur = none := by
    obtain ⟨hR, hrest⟩ := hI
    rw [hph] at hrest
    exact ⟨hR, hrest.1, hrest.2⟩
  unfold hdrDone at h
  by_cases hp : plen = 0
  · simp only [hp, ite_true] at h
    exact enterData_inv w hw c hrd hlen hlog hn hl stored d { rx with cur := some (off, len), ph := .proof plen } rx' hR hstore h
  · simp only [hp, ite_false, Option.some.injEq] at h
    subst h
    have hb' : rx.ver.pair.length = 0 ∧ rx.ver.hb.length = 0 := by simpa [atBoundaryG] using hb
    exact ⟨hR, List.length_eq_zero_iff.1 hb'.2, by simp, by omega⟩

/-- A call on a pair leaves the half-fed group (there is none) as it was. -/
theorem feedG_pair_hb {s s1 : GS Cv} (hg : Good c s) (hpair : nextItemG c s = some .pair) (input : Bytes)
    (hne : input ≠ []) (g : GR) (h : feedG w c s input = some (g, s1)) : s1.hb = s.hb := by
  obtain ⟨hf, nd, rest, hs, hleaf⟩ := nextItem_pair c s hpair
  have hnd0 := hg.nodes nd rest hs
  rcases feedG_nf w hw c s hg hlen hlog hn hf nd rest hs input hne with ⟨hl, -, -, -⟩ | ⟨-, -, -, hn1⟩
  · exact absurd hl hleaf
  · rw [hn1] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; rfl
    · unfold finishPairG at h
      split at h
      · simp at h
      · rename_i s2 hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨hbd, hnd⟩ : HBnd (hh c.n) s.stack ∧ (nd.lo < nd.hi ∧ nd.hi ≤ c.n) := by
          obtain ⟨r, hrel, hwf, hb⟩ := hg
          exact ⟨hrel.stack ▸ hb, hnd0⟩
        obtain ⟨s3, hc3, -, -, hh3, -⟩ := completePairG_eq c hlen hlog hn s nd rest _ hf hs hnd hleaf hbd
        rw [hc3] at hc
        obtain rfl := Option.some.inj hc
        exact hh3

/-- A call on the group that is next, with at most the bytes it still needs. -/
theorem feedG_group_nf {s : GS Cv} (hg : Good c s) (off len left : Nat) (hi : nextItemG c s = some (.group off len))
    (hleft : s.hb.length + left = len) (input : Bytes) (hne : input ≠ []) (hle : input.length ≤ left) :
    ∃ nd rest, s.stack = nd :: rest ∧ s.pair = [] ∧ nd.hi - nd.lo = 1 ∧ len = groupSize c.len c.log nd.lo ∧
      (input.length < left → feedG w c s input = some (.ok input.length none, { s with hb := s.hb ++ input })) ∧
      (¬ input.length < left → feedG w c s input = finishGroupG c s nd rest (s.hb ++ input) input.length len) := by
  obtain ⟨hf, nd, rest, hs, hleaf, -, hlenE⟩ := nextItem_group c s off len hi
  rcases feedG_nf w hw c s hg hlen hlog hn hf nd rest hs input hne with ⟨-, hp, hfill, hn1⟩ | ⟨hl, -⟩
  · rw [← hlenE] at hfill hn1
    have hmin : min input.length (len - s.hb.length) = input.length := by omega
    rw [hmin, List.take_length] at hn1
    refine ⟨nd, rest, hs, hp, hleaf, hlenE, ?_, ?_⟩
    · intro hlt
      rw [hn1, if_pos (by omega)]
    · intro hlt
      rw [hn1, if_neg (by omega)]
  · exact absurd hleaf hl

/-- `proof` keeps the invariant: the verifier must be waiting for a pair, so no half-fed group is ever open in the
proof phase, and what `enter_data` finds at the end of the proof is a verifier at an item boundary or a refusal. -/
theorem proofStep_inv (stored : Bool) (d : Bytes) (rx rx' : RxM Cv) (left : Nat) (piece : Bytes)
    (hI : RxInv w c root rx) (hph : rx.ph = .proof left) (hne : piece ≠ [])
    (hstore : ∀ v1 : GS Cv, stored = true → ∀ nd rest, v1.stack = nd :: rest → nd.hi - nd.lo = 1 →
      c.H.leaf (isRoot c.n nd.lo nd.hi) nd.lo d = nd.cv ∧ d.length = groupSize c.len c.log nd.lo)
    (h : proofStep w c stored d rx left piece = some rx') : RxInv w c root rx' := by
  obtain ⟨hR, hb, hcur, hleft⟩ : Reach w c root rx.ver ∧ rx.ver.hb = [] ∧ rx.cur.isSome = true ∧ 0 < left := by
    obtain ⟨hR, hrest⟩ := hI
    rw [hph] at hrest
    exact ⟨hR, hrest⟩
  have hg := reach_good w hw c hrd hlen hlog hn hl hR
  unfold proofStep at h
  by_cases hp : nextItemG c rx.ver ≠ some .pair
  · simp [hp] at h
  · have hp' : nextItemG c rx.ver = some .pair := by simpa using hp
    simp only [hp, ite_false] at h
    have htake : (piece.take (min piece.length left)) ≠ [] := by
      intro he
      have := congrArg List.length he
      simp at this
      rcases this with h1 | h1
      · exact hne h1
      · omega
    cases hfe : feedG w c rx.ver (piece.take (min piece.length left)) with
    | none => simp [hfe] at h
    | some r =>
      obtain ⟨g, v1⟩ := r
      cases g with
      | err e => simp [hfe] at h
      | ok consumed grp =>
        simp only [hfe] at h
        have hR1 : Reach w c root v1 := Reach.feed _ _ hR hfe
        have hh1 := feedG_pair_hb w hw c hrd hlen hlog hn hl hg hp' _ htake _ hfe
        by_cases h0 : left - consumed = 0
        · simp only [h0, ite_true] at h
          exact enterData_inv w hw c hrd hlen hlog hn hl stored d { rx with ver := v1, ph := .proof 0 } rx' hR1
            (hstore v1) h
        · simp only [h0, ite_false, Option.some.injEq] at h
          subst h
          exact ⟨hR1, by rw [hh1, hb], hcur, by omega⟩

/-- `data` keeps the invariant, and a verifier in the data phase of a fed group always takes all the bytes given:
the refusal for fewer is unreachable (`fed.consumed != take`). -/
theorem dataStep_inv (rx rx' : RxM Cv) (left : Nat) (skip : Bool) (piece : Bytes)
    (hI : RxInv w c root rx) (hph : rx.ph = .data left skip) (hne : piece ≠ [])
    (h : dataStep w c rx left skip piece = some rx') : RxInv w c root rx' := by
  obtain ⟨hR, hrest⟩ := hI
  rw [hph] at hrest
  have hle : min piece.length left ≤ left := Nat.min_le_right _ _
  have hlen1 : min piece.length left ≤ piece.length := Nat.min_le_left _ _
  unfold dataStep at h
  cases skip with
  | true =>
    obtain ⟨hb, hleft⟩ := hrest
    have hpos : 1 ≤ min piece.length left := by
      have : 0 < piece.length := List.length_pos_iff.2 hne
      omega
    simp only [↓reduceIte] at h
    by_cases h0 : 0 < left - min piece.length left
    · simp only [h0, ite_true, Option.some.injEq] at h
      subst h
      exact ⟨hR, hb, h0⟩
    · simp only [h0, ite_false, Option.some.injEq] at h
      subst h
      exact ⟨hR, hb, rfl⟩
  | false =>
    obtain ⟨off, len, hcur, hi, hpair, hleft, hpos⟩ := hrest
    simp only [Bool.false_eq_true, ite_false] at h
    have htake : (piece.take (min piece.length left)) ≠ [] := by
      intro he
      have := congrArg List.length he
      simp at this
      rcases this with h1 | h1
      · exact hne h1
      · omega
    have hlenT : (piece.take (min piece.length left)).length = min piece.length left := by
      rw [List.length_take]; omega
    have hlt : (piece.take (min piece.length left)).length ≤ left := by rw [hlenT]; exact hle
    obtain ⟨nd, rest, hs, hp, hleaf, hlenE, hpart, hfin⟩ :=
      feedG_group_nf w hw c hrd hlen hlog hn hl (reach_good w hw c hrd hlen hlog hn hl hR) off len left hi hleft
        _ htake hlt
    rw [hlenT] at hpart hfin
    by_cases hc : min piece.length left < left
    · have hfe := hpart hc
      rw [hfe] at h
      simp only [↓reduceIte] at h
      have hR1 : Reach w c root _ := Reach.feed _ _ hR hfe
      have hlt2 : 0 < left - min piece.length left := by omega
      simp only [hlt2, ↓reduceIte, Option.some.injEq] at h
      subst h
      refine ⟨hR1, off, len, hcur, ?_, hpair, ?_, hlt2⟩
      · simpa [nextItemG] using hi
      · simp only [List.length_append, hlenT]; omega
    · have hfe := hfin hc
      rw [hfe] at h
      cases hF : finishGroupG c rx.ver nd rest (rx.ver.hb ++ piece.take (min piece.length left)) (min piece.length left) len with
      | none => simp [hF] at h
      | some r =>
        obtain ⟨g, v1⟩ := r
        cases g with
        | err e => simp [hF] at h
        | ok k v =>
          obtain ⟨hk, hb1, hp1⟩ := finishGroupG_ok_state c _ _ nd rest _ _ _ k v hF
          have hfe' : feedG w c rx.ver (piece.take (min piece.length left)) = some (.ok k v, v1) := by
            rw [hfe, hF]
          have hz : ¬ 0 < left - min piece.length left := by omega
          simp only [hF, hk, ↓reduceIte, hz, Option.some.injEq] at h
          subst h
          refine ⟨Reach.feed _ _ hR hfe', ?_, rfl⟩
          simp [atBoundaryG, hb1, hp1, hp]

end

end

end Vinc.ValuesVerify

#audit_axioms Vinc.ValuesVerify.enterData_total
#audit_axioms Vinc.ValuesVerify.enterData_inv
#audit_axioms Vinc.ValuesVerify.hdrDone_inv
#audit_axioms Vinc.ValuesVerify.proofStep_inv
#audit_axioms Vinc.ValuesVerify.dataStep_inv
#audit_axioms Vinc.ValuesVerify.dataStep_whole
