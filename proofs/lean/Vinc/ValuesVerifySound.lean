import Vinc.ValuesVerifySim

/-!
# `GroupVerifier`: soundness, sticky failure, `skip_group`

* `skipG_eq_feedG`: `skip_group` of a group whose bytes the caller holds verified (they hash to the committed
  chaining value) leaves the verifier in exactly the state that feeding the whole group would have left it in, with
  the same group reported, minus the hashing; `skipG_spec` says exactly when it refuses.
* `Reach` are the states a caller drives a fresh verifier to with any calls of `feed` and any `skip_group` under that
  contract; `reach_rel`: each is related (`Rel`) to a `RangeVerifier` state that satisfies the item model's invariant.
* `released_genuine`: with the genuine root and a collision resistant hash, every group a reachable verifier has
  passed is the genuine group of its index, whatever bytes the adversary sent. `feedG_release_verified`: a group is
  reported only by the call whose bytes hash to the chaining value its verified parents committed to.
  `feedG_reject`, `feedG_sticky`: a rejected item releases nothing and fails the verifier for good.
  `released_bookkeeping`, `released_ascending`, `released_in_range`, `complete_releases_range`: the groups passed are
  ascending, inside the request, and exactly the request once the verifier is complete.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Vinc.ValuesVerify
open Vinc.Layout Vinc.Tree Vinc.Machine Vinc.VerifyBytes

section
variable {Cv : Type} [DecidableEq Cv]

/-- A `RangeVerifier` call changes its item-model state by at most one `Tree.feed` step. -/
theorem feedCode_core (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (r : BS Cv) (hwf : Wf c r) (input : Bytes)
    (res : Res) (r1 : BS Cv) (h : feedCode w c r input = some (res, r1)) :
    r1.core = r.core ∨ ∃ it, r1.core = Tree.feed c.H c.n c.first c.last r.core it := by
  by_cases hf : r.core.failed = true
  · simp [feedCode, hf] at h; obtain ⟨-, rfl⟩ := h; exact Or.inl rfl
  · have hnf : r.core.failed = false := by simpa using hf
    by_cases hin : input = []
    · simp [feedCode, hnf, hin] at h; obtain ⟨-, rfl⟩ := h; exact Or.inl rfl
    · rcases hst : r.core.stack with _ | ⟨nd, rest⟩
      · simp [feedCode, hnf, hin, hst] at h; obtain ⟨-, rfl⟩ := h; exact Or.inl rfl
      · rw [feedCode_nf w hw c r hwf hnf nd rest hst input hin _ rfl] at h
        by_cases hlt : r.buf.length + min input.length (needN c.len c.log nd - r.buf.length) < needN c.len c.log nd
        · rw [if_pos hlt] at h; simp at h; obtain ⟨-, rfl⟩ := h; exact Or.inl rfl
        · rw [if_neg hlt] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          right
          refine ⟨c.rd (r.buf ++ input.take (min input.length (needN c.len c.log nd - r.buf.length))), ?_⟩
          simp only [completeItem]
          split <;> rfl

theorem skipG_ok (c : Cfg Cv) (s : GS Cv) (d : Bytes) (off len : Nat) (hn : nextItemG c s = some (.group off len))
    (hb : atBoundaryG s = true) :
    ∃ nd rest, s.stack = nd :: rest ∧ skipG c s d =
      (.ok (off, len), { s with stack := rest, released := s.released ++ [(nd.lo, d)] }) := by
  have hf : s.failed.isSome = false := by
    revert hn; unfold nextItemG; split <;> simp_all
  rcases hs : s.stack with _ | ⟨nd, rest⟩
  · simp [nextItemG, hs, hf] at hn
  · refine ⟨nd, rest, rfl, ?_⟩
    simp [skipG, hf, hb, hn, hs]

/-- `skip_group` refuses (with `TooMuchData`, the verifier unchanged) when the verifier is failed, not at the start of
an item, or the next item is not a group. -/
theorem skipG_err (c : Cfg Cv) (s : GS Cv) (d : Bytes)
    (hn : s.failed.isSome ∨ atBoundaryG s = false ∨ ∀ off len, nextItemG c s ≠ some (.group off len)) :
    skipG c s d = (.error .tooMuchData, s) := by
  unfold skipG
  by_cases h1 : s.failed.isSome ∨ atBoundaryG s = false
  · simp [h1]
  · rw [if_neg h1]
    have h2 : ∀ off len, nextItemG c s ≠ some (.group off len) := by
      rcases hn with h | h | h
      · exact absurd (Or.inl h) h1
      · exact absurd (Or.inr h) h1
      · exact h
    cases hi : nextItemG c s with
    | none => simp
    | some it =>
      cases it with
      | pair => simp
      | group off len => exact absurd hi (h2 off len)

/-- (`skip_group` is feeding the group, minus the hashing.) If the next item is a group, the verifier is at the start
of it, and the group's bytes `d` (the caller's verified copy) hash to the committed chaining value, `skip_group`
reports the group and leaves the verifier exactly as feeding `d` whole would. -/
theorem skipG_eq_feedG (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20)
    (hn : c.n = groups c.len c.log) (s : GS Cv) (d : Bytes) (off len : Nat)
    (hi : nextItemG c s = some (.group off len)) (hb : atBoundaryG s = true)
    (hnd : ∀ nd rest, s.stack = nd :: rest → nd.lo < nd.hi ∧ nd.hi ≤ c.n)
    (hd : ∀ nd rest, s.stack = nd :: rest → nd.hi - nd.lo = 1 → c.H.leaf (isRoot c.n nd.lo nd.hi) nd.lo d = nd.cv ∧
      d.length = groupSize c.len c.log nd.lo) :
    ∃ s1, skipG c s d = (.ok (off, len), s1) ∧ feedG w c s d = some (.ok len (some (off, len)), s1) := by
  obtain ⟨nd, rest, hs, hsk⟩ := skipG_ok c s d off len hi hb
  have hf : s.failed = none := by
    have : s.failed.isSome = false := by revert hi; unfold nextItemG; split <;> simp_all
    simpa using this
  simp only [nextItemG, hf, hs, Option.isSome_none, Bool.false_eq_true, ite_false] at hi
  have hleaf : nd.hi - nd.lo = 1 := by
    refine Classical.byContradiction fun hc => ?_
    simp [hc] at hi
  simp only [hleaf, ite_true, Option.some.injEq, GItem.group.injEq] at hi
  obtain ⟨hoff, hlenE⟩ := hi
  have hb' : s.pair.length = 0 ∧ s.hb.length = 0 := by simpa [atBoundaryG] using hb
  have hp : s.pair = [] := List.length_eq_zero_iff.1 hb'.1
  have hh : s.hb = [] := List.length_eq_zero_iff.1 hb'.2
  obtain ⟨hmatch, hdl⟩ := hd nd rest hs hleaf
  obtain ⟨hlo, hhi⟩ := hnd nd rest hs
  have hpos : 1 ≤ groupSize c.len c.log nd.lo := by
    have := (groupSize_pos_iff c.len c.log nd.lo hlen).2 (by rw [← hn]; omega)
    omega
  have hle := groupSize_le_len c.len c.log nd.lo hlen
  have hdne : d ≠ [] := by intro h; rw [h] at hdl; simp at hdl; omega
  refine ⟨_, hsk, ?_⟩
  have hnf := feedGroupG_nf w hw c hlog s nd rest d (groupSize c.len c.log nd.lo) (groupSize c.len c.log nd.lo) rfl hle
    (by rw [hh, hdl]; simp) (by rw [hh]; simp; omega)
  have hlt : ¬ s.hb.length + groupSize c.len c.log nd.lo < groupSize c.len c.log nd.lo := by omega
  rw [if_neg hlt] at hnf
  have hmul := (complete_arith Nat.log2 isIlog2_log2 c.len c.log c.n hn hlen hlog nd ⟨hlo, hhi⟩).2.1 hleaf
  have hdtake : s.hb ++ d.take (groupSize c.len c.log nd.lo) = d := by
    rw [hh]; simp [← hdl]
  have : feedG w c s d = some (.ok len (some (off, len)),
      ({ s with stack := rest, released := s.released ++ [(nd.lo, d)] } : GS Cv)) := by
    simp only [feedG, hf, hdne, hs, hleaf, ite_true, if_false]
    rw [hnf, hdtake]
    simp [finishGroupG, hmatch, hmul, ← hoff, ← hlenE, hh, hf]
  exact this

/-! ## Reachable states -/

/-- The states a caller drives a fresh `GroupVerifier` (`initG c root`) to: any calls of `feed` with any bytes, and
`skip_group` of a group whose bytes `d` the caller holds verified, that is, they have the length of the group and hash
to the chaining value the verifier committed to for it (the store holds only bytes verified against the same root). -/
inductive Reach (w : Nat) (c : Cfg Cv) (root : Cv) : GS Cv → Prop
  | init : Reach w c root (initG c root)
  | feed {s s1 : GS Cv} (input : Bytes) (g : GR) (h : Reach w c root s) (hf : feedG w c s input = some (g, s1)) :
      Reach w c root s1
  | skip {s : GS Cv} (d : Bytes) (h : Reach w c root s)
      (hd : ∀ nd rest, s.stack = nd :: rest → nd.hi - nd.lo = 1 →
        c.H.leaf (isRoot c.n nd.lo nd.hi) nd.lo d = nd.cv ∧ d.length = groupSize c.len c.log nd.lo) :
      Reach w c root (skipG c s d).2

/-- A state with a related `RangeVerifier` state that satisfies the item model's invariant. -/
def Good (c : Cfg Cv) (s : GS Cv) : Prop := ∃ r : BS Cv, Rel s r ∧ Wf c r ∧ HBnd (hh c.n) r.core.stack

/-- Every stack node of a good state is a valid node of the tree. -/
theorem Good.nodes {c : Cfg Cv} {s : GS Cv} (h : Good c s) :
    ∀ nd rest, s.stack = nd :: rest → nd.lo < nd.hi ∧ nd.hi ≤ c.n := by
  obtain ⟨r, hrel, hwf, -⟩ := h
  intro nd rest hs
  have := hwf.1.1 nd (by rw [← hrel.stack, hs]; exact List.mem_cons_self ..)
  exact ⟨this.1, this.2.1⟩

section
variable (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hrd : ∀ b, (c.rd b).d = b)
  (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20) (hn : c.n = groups c.len c.log) (hl : c.last ≤ c.n)
include hw hrd hlen hlog hn hl

/-- A call keeps a state good, and the item-model state changes by at most one `Tree.feed` step. -/
theorem good_feed {s s1 : GS Cv} {g : GR} (input : Bytes) (hg : Good c s) (hfe : feedG w c s input = some (g, s1)) :
    Good c s1 ∧ (absR s1 = absR s ∨ ∃ it, absR s1 = Tree.feed c.H c.n c.first c.last (absR s) it) := by
  obtain ⟨r, hrel, hwf, hbd⟩ := hg
  obtain ⟨g', s1', res, r1, h1, h2, h3, h4, h5, h6⟩ := feedG_sim w hw c hrd s r hwf hbd hrel input
  rw [hfe] at h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
  refine ⟨⟨r1, h6, h4, h5⟩, ?_⟩
  rw [h6.core, hrel.core]
  exact feedCode_core w hw c r hwf input res r1 h2

theorem good_init (root : Cv) : Good c (initG c root) := by
  obtain ⟨hwf, hbd, hrel, -⟩ := init_ready c root hlen hlog hn hl
  exact ⟨_, hrel, hwf, hbd⟩

/-- Every reachable state is good. -/
theorem reach_good {root : Cv} {s : GS Cv} (h : Reach w c root s) : Good c s := by
  induction h with
  | init => exact good_init w hw c hrd hlen hlog hn hl root
  | feed input g _ hf ih => exact (good_feed w hw c hrd hlen hlog hn hl input ih hf).1
  | @skip s d _ hd ih =>
    by_cases hok : ∃ off len, nextItemG c s = some (.group off len) ∧ atBoundaryG s = true
    · obtain ⟨off, len, hi, hb⟩ := hok
      obtain ⟨s1, hs1, hs2⟩ := skipG_eq_feedG w hw c hlen hlog hn s d off len hi hb ih.nodes hd
      rw [hs1]
      exact (good_feed w hw c hrd hlen hlog hn hl d ih hs2).1
    · have : skipG c s d = (.error .tooMuchData, s) := by
        apply skipG_err
        by_cases hb : atBoundaryG s = true
        · by_cases hf : s.failed.isSome = true
          · exact Or.inl hf
          · right; right
            intro off len hi
            exact hok ⟨off, len, hi, hb⟩
        · right; left; simpa using hb
      rw [this]; exact ih

end

/-! ## Local facts of one call -/

theorem pushG_released (s : GS Cv) (n : Node Cv) : (pushG s n).released = s.released := by
  unfold pushG; split <;> try rfl
  split <;> rfl

theorem pushG_failed (s : GS Cv) (n : Node Cv) (e : Err) (h : s.failed = some e) : (pushG s n).failed = some e := by
  simp [pushG, h]

theorem completePairG_released (c : Cfg Cv) (s : GS Cv) (nd : Node Cv) (rest : List (Node Cv)) (pair : Bytes)
    (s1 : GS Cv) (h : completePairG c s nd rest pair = some s1) : s1.released = s.released := by
  unfold completePairG at h
  by_cases hp : c.H.parent (isRoot c.n nd.lo nd.hi) (c.rd pair).l (c.rd pair).r = nd.cv
  · simp only [hp, ite_true] at h
    cases hs : Machine.sub 64 nd.hi nd.lo with
    | none => simp [hs] at h
    | some span =>
      cases hl : leftGroupsM Nat.log2 span with
      | none => simp [hs, hl] at h
      | some off =>
        cases ha : Machine.add 64 nd.lo off with
        | none => simp [hs, hl, ha] at h
        | some mid =>
          simp only [hs, hl, ha, Option.some.injEq] at h
          subst h
          by_cases a : c.first < mid <;> by_cases b : mid < c.last <;> simp [a, b, pushG_released]
  · simp [hp] at h; subst h; rfl

/-- (The shape of a call on a good state.) -/
theorem feedG_nf (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (s : GS Cv) (hg : Good c s)
    (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20) (hn : c.n = groups c.len c.log)
    (hf : s.failed = none) (nd : Node Cv) (rest : List (Node Cv)) (hs : s.stack = nd :: rest) (input : Bytes)
    (hne : input ≠ []) :
    (nd.hi - nd.lo = 1 ∧ s.pair = [] ∧ s.hb.length < groupSize c.len c.log nd.lo ∧
      feedG w c s input =
        if s.hb.length + min input.length (groupSize c.len c.log nd.lo - s.hb.length) < groupSize c.len c.log nd.lo
        then some (.ok (min input.length (groupSize c.len c.log nd.lo - s.hb.length)) none,
          { s with hb := s.hb ++ input.take (min input.length (groupSize c.len c.log nd.lo - s.hb.length)) })
        else finishGroupG c s nd rest (s.hb ++ input.take (min input.length (groupSize c.len c.log nd.lo - s.hb.length)))
          (min input.length (groupSize c.len c.log nd.lo - s.hb.length)) (groupSize c.len c.log nd.lo)) ∨
    (¬ nd.hi - nd.lo = 1 ∧ s.hb = [] ∧ s.pair.length < 64 ∧
      feedG w c s input =
        if s.pair.length + min input.length (64 - s.pair.length) < 64
        then some (.ok (min input.length (64 - s.pair.length)) none,
          { s with pair := s.pair ++ input.take (min input.length (64 - s.pair.length)) })
        else finishPairG c s nd rest (s.pair ++ input.take (min input.length (64 - s.pair.length)))
          (min input.length (64 - s.pair.length))) := by
  obtain ⟨r, hrel, hwf, hbd⟩ := hg
  obtain ⟨hI, -, -, -, -, hbuf⟩ := hwf
  have hss := hs
  have hst : r.core.stack = nd :: rest := hrel.stack.symm.trans hs
  have hnd := hI.1 nd (by rw [hst]; exact List.mem_cons_self ..)
  have hpos := needN_pos c ⟨hlen, hn⟩ nd ⟨hnd.1, hnd.2.1⟩
  have hnf : r.core.failed = false := by
    have := hrel.failed; rw [hf] at this; simpa using this.symm
  have hfill : r.buf.length < needN c.len c.log nd := by
    by_cases hb : r.buf = []
    · simp [hb]; omega
    · obtain ⟨nd', rest', hs', hl', _⟩ := hbuf hb
      rw [hst] at hs'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hs'
      exact hl'
  have hle := needN_le c hlen hlog nd
  by_cases hleaf : nd.hi - nd.lo = 1
  · left
    have hp : s.pair = [] := by
      refine Classical.byContradiction fun h => ?_
      obtain ⟨nd', rest', h1, h2⟩ := hrel.pairK h
      rw [hs] at h1
      obtain ⟨rfl, rfl⟩ := List.cons.inj h1
      exact h2 hleaf
    have hbl : r.buf = s.hb := by rw [hrel.buf, hp]; simp
    have hneed : needN c.len c.log nd = groupSize c.len c.log nd.lo := by simp [needN, hleaf]
    rw [hneed] at hfill hle
    rw [hbl] at hfill
    refine ⟨hleaf, hp, hfill, ?_⟩
    have := feedGroupG_nf w hw c hlog s nd rest input (groupSize c.len c.log nd.lo)
      (min input.length (groupSize c.len c.log nd.lo - s.hb.length)) rfl hle rfl hfill
    have e : feedG w c s input = feedGroupG w c s nd rest input := by
      simp only [feedG, hf, hne, hs, hleaf, ite_true, if_false]
    rw [e]; exact this
  · right
    have hh0 : s.hb = [] := by
      refine Classical.byContradiction fun h => ?_
      obtain ⟨nd', rest', h1, h2⟩ := hrel.hbK h
      rw [hs] at h1
      obtain ⟨rfl, rfl⟩ := List.cons.inj h1
      exact hleaf h2
    have hbl : r.buf = s.pair := by rw [hrel.buf, hh0]; simp
    have hneed : needN c.len c.log nd = 64 := by simp [needN, hleaf]
    rw [hneed] at hfill
    rw [hbl] at hfill
    refine ⟨hleaf, hh0, hfill, ?_⟩
    have := feedPairG_nf w hw c s nd rest input (min input.length (64 - s.pair.length)) rfl hfill
    have e : feedG w c s input = feedPairG w c s nd rest input := by
      simp only [feedG, hf, hne, hs, hleaf, if_false]
    rw [e]; exact this

/-- (A rejected item releases nothing.) A call on a good state that returns an error leaves the passed groups as
they were. -/
theorem feedG_reject (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (s s1 : GS Cv) (hg : Good c s)
    (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20) (hn : c.n = groups c.len c.log) (input : Bytes) (e : Err)
    (h : feedG w c s input = some (.err e, s1)) : s1.released = s.released := by
  by_cases hfs : s.failed.isSome = true
  · obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.1 hfs
    simp [feedG, he0] at h; obtain ⟨-, rfl⟩ := h; rfl
  · have hf : s.failed = none := by simpa using hfs
    by_cases hin : input = []
    · simp [feedG, hf, hin] at h
    · rcases hs : s.stack with _ | ⟨nd, rest⟩
      · simp [feedG, hf, hin, hs] at h; obtain ⟨-, rfl⟩ := h; rfl
      · rcases feedG_nf w hw c s hg hlen hlog hn hf nd rest hs input hin with ⟨-, -, -, hn1⟩ | ⟨-, -, -, hn1⟩
        · rw [hn1] at h
          split at h
          · simp at h
          · unfold finishGroupG at h
            split at h
            · split at h <;> simp at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h; rfl
        · rw [hn1] at h
          split at h
          · simp at h
          · unfold finishPairG at h
            split at h
            · simp at h
            · rename_i s2 hc
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact completePairG_released c s _ _ _ s2 hc

theorem finishGroupG_ok (c : Cfg Cv) (s : GS Cv) (nd : Node Cv) (rest : List (Node Cv)) (data : Bytes)
    (take size k : Nat) (p : Nat × Nat) (s1 : GS Cv)
    (hm : Machine.mul 64 nd.lo (groupLen c.log) = some (nd.lo * groupLen c.log))
    (h : finishGroupG c s nd rest data take size = some (.ok k (some p), s1)) :
    c.H.leaf (isRoot c.n nd.lo nd.hi) nd.lo data = nd.cv ∧ s1.released = s.released ++ [(nd.lo, data)] ∧
      p = (nd.lo * groupLen c.log, size) := by
  unfold finishGroupG at h
  by_cases hp : c.H.leaf (isRoot c.n nd.lo nd.hi) nd.lo data = nd.cv
  · simp only [hp, ite_true, hm, Option.some.injEq, Prod.mk.injEq, GR.ok.injEq] at h
    obtain ⟨⟨-, hp2⟩, rfl⟩ := h
    exact ⟨hp, rfl, hp2.symm⟩
  · simp [hp] at h

/-- (Release only after a match.) A call reports a group only if the verifier was not failed, a group was the next
item, and the bytes hashed for it hash, as that group, to the chaining value committed for it by already verified
parents; the group is logged with those bytes, and it is reported with its offset and its length. -/
theorem feedG_release_verified (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (s s1 : GS Cv) (hg : Good c s)
    (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20) (hn : c.n = groups c.len c.log) (input : Bytes) (k : Nat)
    (p : Nat × Nat) (h : feedG w c s input = some (.ok k (some p), s1)) :
    s.failed = none ∧ ∃ nd rest data, s.stack = nd :: rest ∧ nd.hi - nd.lo = 1 ∧
      c.H.leaf (isRoot c.n nd.lo nd.hi) nd.lo data = nd.cv ∧ s1.released = s.released ++ [(nd.lo, data)] ∧
      p = (nd.lo * groupLen c.log, groupSize c.len c.log nd.lo) := by
  have hf : s.failed = none := by
    cases hfs : s.failed with
    | none => rfl
    | some e => simp [feedG, hfs] at h
  by_cases hin : input = []
  · simp [feedG, hf, hin] at h
  · rcases hs : s.stack with _ | ⟨nd, rest⟩
    · simp [feedG, hf, hin, hs] at h
    · refine ⟨hf, nd, rest, ?_⟩
      have hnd := hg.nodes nd rest hs
      rcases feedG_nf w hw c s hg hlen hlog hn hf nd rest hs input hin with ⟨hleaf, -, -, hn1⟩ | ⟨-, -, -, hn1⟩
      · rw [hn1] at h
        have hmul := (complete_arith Nat.log2 isIlog2_log2 c.len c.log c.n hn hlen hlog nd hnd).2.1 hleaf
        split at h
        · simp at h
        · obtain ⟨h1, h2, h3⟩ := finishGroupG_ok c s nd rest _ _ _ k p s1 hmul h
          exact ⟨_, rfl, hleaf, h1, h2, h3⟩
      · rw [hn1] at h
        split at h
        · simp at h
        · unfold finishPairG at h
          split at h
          · simp at h
          · rename_i s2 hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, -⟩ := h
            revert h1
            split <;> simp

/-- (The failure is sticky.) A failed verifier answers every call with the same error, changes nothing, and has no
next item. -/
theorem feedG_sticky (w : Nat) (c : Cfg Cv) (s : GS Cv) (e : Err) (hf : s.failed = some e) (input : Bytes) :
    feedG w c s input = some (.err e, s) ∧ nextItemG c s = none ∧ nextLenG c s = none ∧ isCompleteG s = false := by
  refine ⟨by simp [feedG, hf], by simp [nextItemG, hf], by simp [nextLenG, nextItemG, hf], by simp [isCompleteG, hf]⟩

/-- An empty input is a no-op, on any verifier that is not failed. -/
theorem feedG_empty (w : Nat) (c : Cfg Cv) (s : GS Cv) (hf : s.failed = none) :
    feedG w c s [] = some (.ok 0 none, s) := by simp [feedG, hf]

/-- A complete stream followed by data: `TooMuchData`, the verifier unchanged. -/
theorem feedG_toomuch (w : Nat) (c : Cfg Cv) (s : GS Cv) (hf : s.failed = none) (hs : s.stack = [])
    (input : Bytes) (hne : input ≠ []) : feedG w c s input = some (.err .tooMuchData, s) := by
  simp [feedG, hf, hs, hne]

/-! ## What a reachable verifier has passed is the value -/

section
variable (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hrd : ∀ b, (c.rd b).d = b)
  (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20) (hn : c.n = groups c.len c.log) (hl : c.last ≤ c.n)
include hw hrd hlen hlog hn hl

/-- Every reachable verifier is good, and with a genuine root and a collision resistant hash every pending node holds
the genuine chaining value of its interval and every group passed is the genuine group. -/
theorem reach_genuine (cf : CollisionFree c.H) (data : Nat → Bytes) {root : Cv} (hroot : root = gcv c.H data c.n 0 c.n)
    {s : GS Cv} (h : Reach w c root s) : Good c s ∧ Genuine c.H data c.n (absR s) := by
  induction h with
  | init =>
    refine ⟨good_init w hw c hrd hlen hlog hn hl root, ?_⟩
    subst hroot
    exact init_genuine c.H data c.n c.first c.last
  | @feed s s1 input g _ hf ih =>
    obtain ⟨hg, hge⟩ := ih
    obtain ⟨hg1, hr⟩ := good_feed w hw c hrd hlen hlog hn hl input hg hf
    refine ⟨hg1, ?_⟩
    rcases hr with hr | ⟨it, hr⟩
    · rw [hr]; exact hge
    · rw [hr]
      obtain ⟨r, hrel, hwf, -⟩ := hg
      exact feed_genuine c.H cf data c.n c.first c.last (absR s) it (hrel.core ▸ hwf.1) hge
  | @skip s d _ hd ih =>
    obtain ⟨hg, hge⟩ := ih
    by_cases hok : ∃ off len, nextItemG c s = some (.group off len) ∧ atBoundaryG s = true
    · obtain ⟨off, len, hi, hb⟩ := hok
      obtain ⟨s1, hs1, hs2⟩ := skipG_eq_feedG w hw c hlen hlog hn s d off len hi hb hg.nodes hd
      rw [hs1]
      obtain ⟨hg1, hr⟩ := good_feed w hw c hrd hlen hlog hn hl d hg hs2
      refine ⟨hg1, ?_⟩
      rcases hr with hr | ⟨it, hr⟩
      · rw [hr]; exact hge
      · rw [hr]
        obtain ⟨r, hrel, hwf, -⟩ := hg
        exact feed_genuine c.H cf data c.n c.first c.last (absR s) it (hrel.core ▸ hwf.1) hge
    · have : skipG c s d = (.error .tooMuchData, s) := by
        apply skipG_err
        by_cases hb : atBoundaryG s = true
        · by_cases hf : s.failed.isSome = true
          · exact Or.inl hf
          · right; right
            intro off len hi
            exact hok ⟨off, len, hi, hb⟩
        · right; left; simpa using hb
      rw [this]; exact ⟨hg, hge⟩

/-- (Only verified bytes.) With the genuine root and a collision resistant hash, whatever bytes the adversary feeds,
in any split and with any skips under the contract, every group the verifier has passed is the genuine group of its
index, and its bytes are the genuine bytes. -/
theorem released_genuine (cf : CollisionFree c.H) (data : Nat → Bytes) {root : Cv} (hroot : root = gcv c.H data c.n 0 c.n)
    {s : GS Cv} (h : Reach w c root s) : ∀ g ∈ s.released, g.2 = data g.1 :=
  (reach_genuine w hw c hrd hlen hlog hn hl cf data hroot h).2.2

/-- Every group still to come is the genuine one: each pending node holds the genuine chaining value of its interval. -/
theorem pending_genuine (cf : CollisionFree c.H) (data : Nat → Bytes) {root : Cv} (hroot : root = gcv c.H data c.n 0 c.n)
    {s : GS Cv} (h : Reach w c root s) : ∀ nd ∈ s.stack, nd.cv = gcv c.H data c.n nd.lo nd.hi :=
  (reach_genuine w hw c hrd hlen hlog hn hl cf data hroot h).2.1

/-- (Bookkeeping.) The groups passed plus the groups the stack still covers are exactly the requested groups, in
order. -/
theorem released_bookkeeping {root : Cv} {s : GS Cv} (h : Reach w c root s) :
    s.released.map Prod.fst ++ s.stack.flatMap (clip c.first c.last) = List.range' c.first (c.last - c.first) := by
  obtain ⟨r, hrel, hwf, -⟩ := reach_good w hw c hrd hlen hlog hn hl h
  have := hwf.1.2
  rw [← hrel.stack, ← hrel.released] at this
  exact this

/-- The groups passed come in strictly ascending order of index. -/
theorem released_ascending {root : Cv} {s : GS Cv} (h : Reach w c root s) :
    (s.released.map Prod.fst).Pairwise (· < ·) := by
  have hb := released_bookkeeping w hw c hrd hlen hlog hn hl h
  have hp : (List.range' c.first (c.last - c.first)).Pairwise (· < ·) := List.pairwise_lt_range'
  rw [← hb] at hp
  exact hp.sublist (List.sublist_append_left _ _)

/-- The groups passed lie in the requested range. -/
theorem released_in_range {root : Cv} {s : GS Cv} (h : Reach w c root s) :
    ∀ g ∈ s.released, c.first ≤ g.1 ∧ g.1 < c.last := by
  intro g hg
  have hb := released_bookkeeping w hw c hrd hlen hlog hn hl h
  have : g.1 ∈ List.range' c.first (c.last - c.first) := by
    rw [← hb]; exact List.mem_append_left _ (List.mem_map_of_mem hg)
  simp [List.mem_range'_1] at this
  omega

/-- (Complete means the whole request.) When the verifier is complete it has passed exactly the groups of the request,
in order. -/
theorem complete_releases_range {root : Cv} {s : GS Cv} (h : Reach w c root s) (hc : isCompleteG s = true) :
    s.released.map Prod.fst = List.range' c.first (c.last - c.first) := by
  have hb := released_bookkeeping w hw c hrd hlen hlog hn hl h
  have hs : s.stack = [] := (by simpa [isCompleteG] using hc : s.failed = none ∧ s.stack = []).2
  simp [hs] at hb
  exact hb

/-- (The 64-node stack never overflows.) A reachable verifier holds at most 55 pending nodes, so `StackOverflow` is
unreachable: the cap of 64 is never hit by a value of up to `u64::MAX` bytes. -/
theorem reach_stack_le {root : Cv} {s : GS Cv} (h : Reach w c root s) : s.stack.length ≤ 55 ∧ s.stack.length < stackCap := by
  obtain ⟨r, hrel, hwf, hbd⟩ := reach_good w hw c hrd hlen hlog hn hl h
  have hn54 : c.n ≤ 2 ^ 54 := hn ▸ groups_le c.len c.log hlen
  have h1 := hbnd_len (hh c.n) _ hbd
  have h2 := hh_le_54 c.n hn54
  rw [← hrel.stack] at h1
  unfold stackCap
  omega

end

end

end Vinc.ValuesVerify

#audit_axioms Vinc.ValuesVerify.skipG_eq_feedG
#audit_axioms Vinc.ValuesVerify.skipG_err
#audit_axioms Vinc.ValuesVerify.reach_good
#audit_axioms Vinc.ValuesVerify.released_genuine
#audit_axioms Vinc.ValuesVerify.pending_genuine
#audit_axioms Vinc.ValuesVerify.feedG_release_verified
#audit_axioms Vinc.ValuesVerify.feedG_reject
#audit_axioms Vinc.ValuesVerify.feedG_sticky
#audit_axioms Vinc.ValuesVerify.feedG_toomuch
#audit_axioms Vinc.ValuesVerify.released_ascending
#audit_axioms Vinc.ValuesVerify.released_in_range
#audit_axioms Vinc.ValuesVerify.complete_releases_range
#audit_axioms Vinc.ValuesVerify.reach_stack_le
