import Pinc.ValuesVerifyLemmas

/-!
# `GroupVerifier` against `RangeVerifier`: one call

`Rel c s r` relates a `GroupVerifier` state `s` (`GS`) to a `RangeVerifier` state `r` (`VerifyBytes.BS`): the same
node stack, released groups and failure, and the `RangeVerifier` buffer is the pair buffer followed by the bytes the
hasher took (one of the two is empty, according to the kind of the item on top of the stack).

* `feedCode_nf`: the shape of one `RangeVerifier::feed` call (the same `min(input, still needed)` bytes taken).
* `feedG_sim`: one `GroupVerifier::feed` call and one `RangeVerifier::feed` call, on related states and the same
  input, return the same outcome (`ResMatch`: the same bytes consumed, the same group offset and length, the same
  error) and end in related states.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Pinc.ValuesVerify
open Pinc.Layout Pinc.Tree Pinc.Machine Pinc.VerifyBytes

section
variable {Cv : Type} [DecidableEq Cv]

/-- (The shape of a `RangeVerifier` call.) -/
theorem feedCode_nf (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (r : BS Cv) (hwf : Wf c r)
    (hnf : r.core.failed = false) (nd : Node Cv) (rest : List (Node Cv)) (hst : r.core.stack = nd :: rest)
    (input : Bytes) (hne : input ≠ []) (take : Nat)
    (htake : take = min input.length (needN c.len c.log nd - r.buf.length)) :
    feedCode w c r input =
      if r.buf.length + take < needN c.len c.log nd then some (.ok take none, { r with buf := r.buf ++ input.take take })
      else some (resOf take (completeItem c r nd (r.buf ++ input.take take)).2,
        (completeItem c r nd (r.buf ++ input.take take)).1) := by
  have hwf' := hwf
  obtain ⟨hI, hlen, hlog, hn, hlast, hbuf⟩ := hwf
  have hnd := hI.1 nd (by rw [hst]; exact List.mem_cons_self ..)
  have hp := needN_pos c ⟨hlen, hn⟩ nd ⟨hnd.1, hnd.2.1⟩
  have hle := needN_le c hlen hlog nd
  have hW := needW_eq w hw c hlen hlog nd
  have hg2 := groupLen_le c.log hlog
  have h30 := pow30_lt w hw
  have hfill : r.buf.length < needN c.len c.log nd := by
    by_cases hb : r.buf = []
    · simp [hb]; omega
    · obtain ⟨nd', rest', hs', hl', _⟩ := hbuf hb
      rw [hst] at hs'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hs'
      exact hl'
  have hlen1 : 1 ≤ input.length := by
    cases input with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  by_cases hfast : r.buf = [] ∧ needN c.len c.log nd ≤ input.length
  · obtain ⟨hb0, hfi⟩ := hfast
    have htk : take = needN c.len c.log nd := by rw [htake, hb0]; simp; omega
    have hnl : ¬ r.buf.length + take < needN c.len c.log nd := by rw [hb0, htk]; simp
    rw [if_neg hnl, htk, hb0]
    simp [feedCode, hnf, hne, hst, hW, hfi, hb0]
  · have hroom : Machine.sub w (needN c.len c.log nd) r.buf.length = some (needN c.len c.log nd - r.buf.length) := by
      simp [Machine.sub]; omega
    have hend : Machine.add w r.buf.length take = some (r.buf.length + take) := by
      simp only [Machine.add]
      have : r.buf.length + take ≤ needN c.len c.log nd := by omega
      rw [if_pos (by omega)]
    have hg1 : ¬ groupLen c.log < r.buf.length + take := by omega
    have htm : min input.length (needN c.len c.log nd - r.buf.length) = take := htake.symm
    by_cases hlt : r.buf.length + take < needN c.len c.log nd
    · rw [if_pos hlt]
      simp [feedCode, hnf, hne, hst, hW, hfast, hroom, htm, hend, hg1, hlt]
    · rw [if_neg hlt]
      have hg2' : ¬ groupLen c.log < needN c.len c.log nd := by omega
      simp [feedCode, hnf, hne, hst, hW, hfast, hroom, htm, hend, hg1, hlt, hg2']

/-- The outcome of a `GroupVerifier` call stands for the outcome of a `RangeVerifier` call: the same bytes consumed,
the group reported at the same call with the same offset (its length is the length of the bytes the other verifier
returns), the same error. -/
def ResMatch : Res → GR → Prop
  | .ok k v, .ok k' v' => k = k' ∧ v' = v.map (fun p => (p.1, p.2.length))
  | .err e, .err e' => e'.toE = some e
  | _, _ => False

/-- The refinement relation between a `GroupVerifier` state and a `RangeVerifier` state. -/
structure Rel (s : GS Cv) (r : BS Cv) : Prop where
  core : absR s = r.core
  fail : s.failed = if r.core.failed then some (if r.errk then Err.groupMismatch else Err.parentMismatch) else none
  buf : r.buf = s.pair ++ s.hb
  pairK : s.pair ≠ [] → ∃ nd rest, s.stack = nd :: rest ∧ nd.hi - nd.lo ≠ 1
  hbK : s.hb ≠ [] → ∃ nd rest, s.stack = nd :: rest ∧ nd.hi - nd.lo = 1

theorem Rel.stack {s : GS Cv} {r : BS Cv} (h : Rel s r) : s.stack = r.core.stack := congrArg State.stack h.core
theorem Rel.released {s : GS Cv} {r : BS Cv} (h : Rel s r) : s.released = r.core.released := congrArg State.released h.core
theorem Rel.failed {s : GS Cv} {r : BS Cv} (h : Rel s r) : s.failed.isSome = r.core.failed := congrArg State.failed h.core

theorem rel_init (c : Cfg Cv) (root : Cv) : Rel (initG c root) ⟨Tree.init root c.n c.first c.last, [], false⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [initG, absR, Tree.init]

/-- (A call on a group.) -/
theorem sim_leaf (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hrd : ∀ b, (c.rd b).d = b) (s : GS Cv) (r : BS Cv)
    (hwf : Wf c r) (hbd : HBnd (hh c.n) r.core.stack) (hrel : Rel s r) (hnf : r.core.failed = false)
    (nd : Node Cv) (rest : List (Node Cv)) (hst : r.core.stack = nd :: rest) (hleaf : nd.hi - nd.lo = 1)
    (input : Bytes) (hne : input ≠ []) :
    ∃ g s1 res r1, feedGroupG w c s nd rest input = some (g, s1) ∧ feedCode w c r input = some (res, r1) ∧
      ResMatch res g ∧ Wf c r1 ∧ HBnd (hh c.n) r1.core.stack ∧ Rel s1 r1 := by
  have hwf' := hwf
  obtain ⟨hI, hlen, hlog, hn, hlast, hbuf⟩ := hwf
  have hsf : s.failed = none := by rw [hrel.fail, hnf]; rfl
  have hss : s.stack = nd :: rest := hrel.stack.trans hst
  have hnd := hI.1 nd (by rw [hst]; exact List.mem_cons_self ..)
  have hp : s.pair = [] := by
    refine Classical.byContradiction fun h => ?_
    obtain ⟨nd', rest', h1, h2⟩ := hrel.pairK h
    rw [hss] at h1
    obtain ⟨rfl, rfl⟩ := List.cons.inj h1
    exact h2 hleaf
  have hbl : r.buf = s.hb := by rw [hrel.buf, hp]; simp
  have hneed : needN c.len c.log nd = groupSize c.len c.log nd.lo := by simp [needN, hleaf]
  have hle := needN_le c hlen hlog nd
  have hpos := needN_pos c ⟨hlen, hn⟩ nd ⟨hnd.1, hnd.2.1⟩
  have hfill : r.buf.length < needN c.len c.log nd := by
    by_cases hb : r.buf = []
    · simp [hb]; omega
    · obtain ⟨nd', rest', hs', hl', _⟩ := hbuf hb
      rw [hst] at hs'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hs'
      exact hl'
  have hG := feedGroupG_nf w hw c hlog s nd rest input (needN c.len c.log nd)
    (min input.length (needN c.len c.log nd - r.buf.length)) hneed hle (by rw [hbl]) (by rw [← hbl]; exact hfill)
  have hfill' : s.hb.length < needN c.len c.log nd := by rw [← hbl]; exact hfill
  have hR := feedCode_nf w hw c r hwf' hnf nd rest hst input hne (min input.length (needN c.len c.log nd - r.buf.length)) rfl
  rw [hbl] at hR
  rw [hbl] at hG
  by_cases hlt : s.hb.length + min input.length (needN c.len c.log nd - s.hb.length) < needN c.len c.log nd
  · -- the group is still incomplete: the bytes go to the hasher
    rw [if_pos hlt] at hG hR
    refine ⟨_, _, _, _, hG, hR, ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · refine ⟨hI, hlen, hlog, hn, hlast, ?_⟩
      intro _
      refine ⟨nd, rest, hst, ?_, hnf⟩
      simp only [List.length_append, List.length_take]
      omega
    · exact hbd
    · refine ⟨hrel.core, hrel.fail, ?_, fun h => absurd hp h, ?_⟩
      · simp [hp]
      · intro _; exact ⟨nd, rest, hss, hleaf⟩
  · -- the group completes with this call
    rw [if_neg hlt] at hG hR
    have heq : s.hb.length + min input.length (needN c.len c.log nd - s.hb.length) = needN c.len c.log nd := by omega
    have hdl : (s.hb ++ input.take (min input.length (needN c.len c.log nd - s.hb.length))).length = needN c.len c.log nd := by
      simp only [List.length_append, List.length_take]; omega
    obtain ⟨g, s1, hfin, habs, hb1, hp1, hcase⟩ := finishGroupG_eq c hlen hlog hn hrd s nd rest
      (s.hb ++ input.take (min input.length (needN c.len c.log nd - s.hb.length)))
      (min input.length (needN c.len c.log nd - s.hb.length)) (needN c.len c.log nd) hsf hss ⟨hnd.1, hnd.2.1⟩ hleaf
    rw [hfin] at hG
    have hcore : Tree.feed c.H c.n c.first c.last r.core (c.rd (s.hb ++ input.take (min input.length
        (needN c.len c.log nd - s.hb.length)))) = absR s1 := by rw [habs, hrel.core]
    have hcw := completeItem_wf c r hwf' nd (s.hb ++ input.take (min input.length (needN c.len c.log nd - s.hb.length)))
    have hbd1 := hbnd_feed c.H c.n c.first c.last (hh c.n) r.core (c.rd (s.hb ++ input.take (min input.length
        (needN c.len c.log nd - s.hb.length)))) hbd (fun nd' h => (hI.1 nd' h).1)
    rw [hcore] at hbd1
    rcases hcase with ⟨hf1, hr1, hg⟩ | ⟨hf1, hr1, hg⟩
    · have hfa : (absR s1).failed = false := by simp [absR, hf1]
      have hci : completeItem c r nd (s.hb ++ input.take (min input.length (needN c.len c.log nd - s.hb.length))) =
          ({ core := absR s1, buf := [], errk := r.errk }, some (.released (nd.lo * groupLen c.log)
            (s.hb ++ input.take (min input.length (needN c.len c.log nd - s.hb.length))))) := by
        simp [completeItem, hcore, hfa, hleaf]
      rw [hci] at hR hcw
      subst hg
      refine ⟨_, s1, _, _, hG, hR, ?_, hcw, hbd1, ?_⟩
      · simp [resOf, ResMatch, hdl]
      · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · simp [absR, hf1]
        · simp [hb1, hp1, hp]
        · simp [hp1, hp]
        · simp [hb1]
    · have hfa : (absR s1).failed = true := by simp [absR, hf1]
      have hci : completeItem c r nd (s.hb ++ input.take (min input.length (needN c.len c.log nd - s.hb.length))) =
          ({ core := absR s1, buf := [], errk := true }, some (.err .groupMismatch)) := by
        simp [completeItem, hcore, hfa, hleaf, errOf]
      rw [hci] at hR hcw
      subst hg
      refine ⟨_, s1, _, _, hG, hR, ?_, hcw, hbd1, ?_⟩
      · simp [resOf, ResMatch, Err.toE]
      · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · simp [absR, hf1]
        · simp [hb1, hp1, hp]
        · simp [hp1, hp]
        · simp [hb1]

/-- (A call on a pair.) -/
theorem sim_pair (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (s : GS Cv) (r : BS Cv)
    (hwf : Wf c r) (hbd : HBnd (hh c.n) r.core.stack) (hrel : Rel s r) (hnf : r.core.failed = false)
    (nd : Node Cv) (rest : List (Node Cv)) (hst : r.core.stack = nd :: rest) (hleaf : ¬ nd.hi - nd.lo = 1)
    (input : Bytes) (hne : input ≠ []) :
    ∃ g s1 res r1, feedPairG w c s nd rest input = some (g, s1) ∧ feedCode w c r input = some (res, r1) ∧
      ResMatch res g ∧ Wf c r1 ∧ HBnd (hh c.n) r1.core.stack ∧ Rel s1 r1 := by
  have hwf' := hwf
  obtain ⟨hI, hlen, hlog, hn, hlast, hbuf⟩ := hwf
  have hsf : s.failed = none := by rw [hrel.fail, hnf]; rfl
  have hss : s.stack = nd :: rest := hrel.stack.trans hst
  have hnd := hI.1 nd (by rw [hst]; exact List.mem_cons_self ..)
  have hh0 : s.hb = [] := by
    refine Classical.byContradiction fun h => ?_
    obtain ⟨nd', rest', h1, h2⟩ := hrel.hbK h
    rw [hss] at h1
    obtain ⟨rfl, rfl⟩ := List.cons.inj h1
    exact hleaf h2
  have hbl : r.buf = s.pair := by rw [hrel.buf, hh0]; simp
  have hneed : needN c.len c.log nd = 64 := by simp [needN, hleaf]
  have hfill : r.buf.length < needN c.len c.log nd := by
    by_cases hb : r.buf = []
    · simp [hb]; have := needN_pos c ⟨hlen, hn⟩ nd ⟨hnd.1, hnd.2.1⟩; omega
    · obtain ⟨nd', rest', hs', hl', _⟩ := hbuf hb
      rw [hst] at hs'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hs'
      exact hl'
  have hfill' : s.pair.length < 64 := by rw [← hbl, ← hneed]; exact hfill
  have hG := feedPairG_nf w hw c s nd rest input (min input.length (64 - s.pair.length)) rfl hfill'
  have hR := feedCode_nf w hw c r hwf' hnf nd rest hst input hne (min input.length (needN c.len c.log nd - r.buf.length)) rfl
  rw [hbl, hneed] at hR
  by_cases hlt : s.pair.length + min input.length (64 - s.pair.length) < 64
  · rw [if_pos hlt] at hG hR
    refine ⟨_, _, _, _, hG, hR, ⟨rfl, rfl⟩, ?_, hbd, ?_⟩
    · refine ⟨hI, hlen, hlog, hn, hlast, ?_⟩
      intro _
      refine ⟨nd, rest, hst, ?_, hnf⟩
      simp only [List.length_append, List.length_take, hneed]
      omega
    · refine ⟨hrel.core, hrel.fail, ?_, ?_, fun h => absurd hh0 h⟩
      · simp [hh0]
      · intro _; exact ⟨nd, rest, hss, hleaf⟩
  · rw [if_neg hlt] at hG hR
    obtain ⟨s1, hcp, habs, hp1, hb1, hr1, hfl⟩ := completePairG_eq c hlen hlog hn s nd rest
      (s.pair ++ input.take (min input.length (64 - s.pair.length))) hsf hss ⟨hnd.1, hnd.2.1⟩ hleaf (by rw [hss]; rw [hst] at hbd; exact hbd)
    have hfin : finishPairG c s nd rest (s.pair ++ input.take (min input.length (64 - s.pair.length)))
        (min input.length (64 - s.pair.length)) =
        some ((match s1.failed with | some e => GR.err e | none => GR.ok (min input.length (64 - s.pair.length)) none), s1) := by
      unfold finishPairG; rw [hcp]; rfl
    rw [hfin] at hG
    have hcore : Tree.feed c.H c.n c.first c.last r.core (c.rd (s.pair ++ input.take (min input.length (64 - s.pair.length)))) =
        absR s1 := by rw [habs, hrel.core]
    have hcw := completeItem_wf c r hwf' nd (s.pair ++ input.take (min input.length (64 - s.pair.length)))
    have hbd1 := hbnd_feed c.H c.n c.first c.last (hh c.n) r.core
      (c.rd (s.pair ++ input.take (min input.length (64 - s.pair.length)))) hbd (fun nd' h => (hI.1 nd' h).1)
    rw [hcore] at hbd1
    rcases hfl with hf1 | hf1
    · have hfa : (absR s1).failed = false := by simp [absR, hf1]
      have hci : completeItem c r nd (s.pair ++ input.take (min input.length (64 - s.pair.length))) =
          ({ core := absR s1, buf := [], errk := r.errk }, none) := by
        simp [completeItem, hcore, hfa, hleaf]
      rw [hci] at hR hcw
      simp only [hf1] at hG
      refine ⟨_, s1, _, _, hG, hR, ?_, hcw, hbd1, ?_⟩
      · simp [resOf, ResMatch]
      · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · simp [absR, hf1]
        · simp [hb1, hp1, hh0]
        · simp [hp1]
        · simp [hb1, hh0]
    · have hfa : (absR s1).failed = true := by simp [absR, hf1]
      have hci : completeItem c r nd (s.pair ++ input.take (min input.length (64 - s.pair.length))) =
          ({ core := absR s1, buf := [], errk := false }, some (.err .parentMismatch)) := by
        simp [completeItem, hcore, hfa, hleaf, errOf]
      rw [hci] at hR hcw
      simp only [hf1] at hG
      refine ⟨_, s1, _, _, hG, hR, ?_, hcw, hbd1, ?_⟩
      · simp [resOf, ResMatch, Err.toE]
      · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · simp [absR, hf1]
        · simp [hb1, hp1, hh0]
        · simp [hp1]
        · simp [hb1, hh0]

/-- (One call.) A `GroupVerifier::feed` call and a `RangeVerifier::feed` call on related states and the same input
return the same outcome (`ResMatch`: the same bytes consumed, the group at the same call with the same offset and
length, the same error), and end in related states. Neither call fails arithmetically. Both start from any
reachable state: the item model's invariant, a supported layout, a buffer holding a proper prefix of the item
on top, and a stack within `hh n + 1` nodes. -/
theorem feedG_sim (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hrd : ∀ b, (c.rd b).d = b) (s : GS Cv) (r : BS Cv)
    (hwf : Wf c r) (hbd : HBnd (hh c.n) r.core.stack) (hrel : Rel s r) (input : Bytes) :
    ∃ g s1 res r1, feedG w c s input = some (g, s1) ∧ feedCode w c r input = some (res, r1) ∧ ResMatch res g ∧
      Wf c r1 ∧ HBnd (hh c.n) r1.core.stack ∧ Rel s1 r1 := by
  by_cases hrf : r.core.failed = true
  · have hsf : s.failed = some (if r.errk then .groupMismatch else .parentMismatch) := by
      rw [hrel.fail]; simp [hrf]
    refine ⟨GR.err (if r.errk then .groupMismatch else .parentMismatch), s, Res.err (errOf r.errk), r, ?_, ?_, ?_, hwf, hbd, hrel⟩
    · simp [feedG, hsf]
    · simp [feedCode, hrf]
    · cases r.errk <;> simp [ResMatch, Err.toE, errOf]
  · have hnf : r.core.failed = false := by simpa using hrf
    have hsf : s.failed = none := by rw [hrel.fail]; simp [hnf]
    by_cases hin : input = []
    · subst hin
      refine ⟨GR.ok 0 none, s, Res.ok 0 none, r, ?_, ?_, ?_, hwf, hbd, hrel⟩
      · simp [feedG, hsf]
      · simp [feedCode, hnf]
      · simp [ResMatch]
    · rcases hst : r.core.stack with _ | ⟨nd, rest⟩
      · have hss : s.stack = [] := hrel.stack.trans hst
        refine ⟨GR.err .tooMuchData, s, Res.err .tooMuchData, r, ?_, ?_, ?_, hwf, hbd, hrel⟩
        · simp [feedG, hsf, hin, hss]
        · simp [feedCode, hnf, hin, hst]
        · simp [ResMatch, Err.toE]
      · have hss : s.stack = nd :: rest := hrel.stack.trans hst
        by_cases hleaf : nd.hi - nd.lo = 1
        · obtain ⟨g, s1, res, r1, h1, h2, h3, h4, h5, h6⟩ := sim_leaf w hw c hrd s r hwf hbd hrel hnf nd rest hst hleaf input hin
          exact ⟨g, s1, res, r1, by simp [feedG, hsf, hin, hss, hleaf, h1], h2, h3, h4, h5, h6⟩
        · obtain ⟨g, s1, res, r1, h1, h2, h3, h4, h5, h6⟩ := sim_pair w hw c s r hwf hbd hrel hnf nd rest hst hleaf input hin
          exact ⟨g, s1, res, r1, by simp [feedG, hsf, hin, hss, hleaf, h1], h2, h3, h4, h5, h6⟩


/-! ## Every sequence of calls, every split of the stream -/

/-- The events a `GroupVerifier` caller sees: a group matched (offset, length), or an error. -/
inductive GObs where
  | group (off len : Nat)
  | err (e : Err)

/-- The error of this verifier that stands for an error of the copying verifier. -/
def Err.ofE : E → Err
  | .parentMismatch => .parentMismatch
  | .groupMismatch => .groupMismatch
  | .tooMuchData => .tooMuchData
  | .outputTooSmall => .outputTooSmall

/-- The `GroupVerifier` event that stands for a `RangeVerifier` event. -/
def projObs : Obs → GObs
  | .released off d => .group off d.length
  | .err e => .err (Err.ofE e)

def relOfG : Option (Nat × Nat) → List GObs
  | none => []
  | some (o, l) => [.group o l]

/-- The caller's loop over one piece with `GroupVerifier` (`VerifyBytes.drivePiece`). -/
def drivePieceG (w : Nat) (c : Cfg Cv) : Nat → GS Cv → Bytes → Option (GS Cv × List GObs)
  | 0, s, p => if p = [] then some (s, []) else none
  | f + 1, s, p =>
    if p = [] then some (s, []) else
    match feedG w c s p with
    | none => none
    | some (.err e, s1) => some (s1, [.err e])
    | some (.ok k v, s1) =>
      match drivePieceG w c f s1 (p.drop k) with
      | none => none
      | some (s2, o) => some (s2, relOfG v ++ o)

def hasErrG (o : List GObs) : Bool := o.any fun x => match x with | .err _ => true | _ => false

/-- The caller feeding a list of pieces in order, stopping at the first error (`VerifyBytes.driveAll`). -/
def driveAllG (w : Nat) (c : Cfg Cv) : GS Cv → List Bytes → Option (GS Cv × List GObs)
  | s, [] => some (s, [])
  | s, p :: ps =>
    match drivePieceG w c p.length s p with
    | none => none
    | some (s1, o1) =>
      if hasErrG o1 then some (s1, o1) else
      match driveAllG w c s1 ps with
      | none => none
      | some (s2, o2) => some (s2, o1 ++ o2)

theorem hasErrG_map (o : List Obs) : hasErrG (o.map projObs) = hasErr o := by
  induction o with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [hasErrG, hasErr, projObs] at ih ⊢ <;> exact ih

/-- One piece: the caller's loop with `GroupVerifier` is the caller's loop with `RangeVerifier`, call for call. -/
theorem drivePieceG_eq (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hrd : ∀ b, (c.rd b).d = b) :
    ∀ (f : Nat) (s : GS Cv) (r : BS Cv) (p : Bytes), p.length ≤ f → Wf c r → HBnd (hh c.n) r.core.stack → Rel s r →
      r.core.failed = false →
      ∃ s1 o r1 o', drivePieceG w c f s p = some (s1, o) ∧ drivePiece w c f r p = some (r1, o') ∧ o = o'.map projObs ∧
        Wf c r1 ∧ HBnd (hh c.n) r1.core.stack ∧ Rel s1 r1 ∧ (hasErr o' = false → r1.core.failed = false) := by
  intro f
  induction f with
  | zero =>
    intro s r p hp hwf hbd hrel hnf
    have : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨s, [], r, [], by simp [drivePieceG], by simp [drivePiece], rfl, hwf, hbd, hrel, fun _ => hnf⟩
  | succ f ih =>
    intro s r p hp hwf hbd hrel hnf
    by_cases hpn : p = []
    · subst hpn
      exact ⟨s, [], r, [], by simp [drivePieceG], by simp [drivePiece], rfl, hwf, hbd, hrel, fun _ => hnf⟩
    · obtain ⟨g, s1, res, r1, hg, hr, hm, hw1, hb1, hrel1⟩ := feedG_sim w hw c hrd s r hwf hbd hrel p
      obtain ⟨r', s', hfc, hw', k, hk, hk1, hb, hok, herr⟩ := feedCode_sim w hw c r hwf hnf p hpn
      rw [hr] at hfc
      obtain ⟨rfl, rfl⟩ := Option.some.inj hfc |> Prod.mk.inj
      cases res with
      | err e =>
        cases g with
        | ok _ _ => exact absurd hm id
        | err e' =>
          have he : Err.ofE e = e' := by
            cases e <;> cases e' <;> simp [ResMatch, Err.toE, Err.ofE] at hm ⊢
          refine ⟨s1, [.err e'], r1, [.err e], by simp [drivePieceG, hpn, hg], by simp [drivePiece, hpn, hr], ?_, hw1, hb1,
            hrel1, by simp [hasErr]⟩
          simp [projObs, he]
      | ok k' v =>
        obtain ⟨hkk, hnf1⟩ := hok k' v rfl
        subst hkk
        cases g with
        | err e' => exact absurd hm id
        | ok k2 v2 =>
          obtain ⟨hk2, hv2⟩ := hm
          subst hk2
          have hlen : (p.drop k').length ≤ f := by simp; omega
          obtain ⟨s2, o2, r2, o2', hd, hd', ho, hw2, hb2, hrel2, hf2⟩ := ih s1 r1 (p.drop k') hlen hw1 hb1 hrel1 hnf1
          refine ⟨s2, relOfG v2 ++ o2, r2, relOf v ++ o2', by simp [drivePieceG, hpn, hg, hd], ?_, ?_, hw2, hb2, hrel2, ?_⟩
          · simp [drivePiece, hpn, hr, hd']
          · rw [ho, hv2]
            rcases v with _ | ⟨off, d⟩ <;> simp [relOfG, relOf, projObs]
          · intro h
            apply hf2
            rcases v with _ | ⟨off, d⟩ <;> simpa [relOf, hasErr] using h

/-- Any list of pieces. -/
theorem driveAllG_eq (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hrd : ∀ b, (c.rd b).d = b) :
    ∀ (ps : List Bytes) (s : GS Cv) (r : BS Cv), Wf c r → HBnd (hh c.n) r.core.stack → Rel s r → r.core.failed = false →
      ∃ s1 o r1 o', driveAllG w c s ps = some (s1, o) ∧ driveAll w c r ps = some (r1, o') ∧ o = o'.map projObs ∧
        Rel s1 r1 := by
  intro ps
  induction ps with
  | nil => intro s r _ _ hrel _; exact ⟨s, [], r, [], by simp [driveAllG], by simp [driveAll], rfl, hrel⟩
  | cons p ps ih =>
    intro s r hwf hbd hrel hnf
    obtain ⟨s1, o1, r1, o1', hd, hd', ho, hw1, hb1, hrel1, hf1⟩ :=
      drivePieceG_eq w hw c hrd p.length s r p (Nat.le_refl _) hwf hbd hrel hnf
    by_cases he : hasErr o1' = true
    · have heg : hasErrG o1 = true := by rw [ho, hasErrG_map]; exact he
      exact ⟨s1, o1, r1, o1', by simp [driveAllG, hd, heg], by simp [driveAll, hd', he], ho, hrel1⟩
    · have he' : hasErr o1' = false := by simpa using he
      have heg : hasErrG o1 = false := by rw [ho, hasErrG_map]; exact he'
      obtain ⟨s2, o2, r2, o2', hd2, hd2', ho2, hrel2⟩ := ih s1 r1 hw1 hb1 hrel1 (hf1 he')
      refine ⟨s2, o1 ++ o2, r2, o1' ++ o2', by simp [driveAllG, hd, heg, hd2], by simp [driveAll, hd', he', hd2'], ?_, hrel2⟩
      rw [ho, ho2, List.map_append]

/-- A fresh `GroupVerifier` and a fresh `RangeVerifier` are related, in a state the theorems apply to. -/
theorem init_ready (c : Cfg Cv) (root : Cv) (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20)
    (hn : c.n = groups c.len c.log) (hl : c.last ≤ c.n) :
    Wf c ⟨Tree.init root c.n c.first c.last, [], false⟩ ∧ HBnd (hh c.n) (Tree.init root c.n c.first c.last : State Cv Bytes).stack ∧
      Rel (initG c root) ⟨Tree.init root c.n c.first c.last, [], false⟩ ∧
      (⟨Tree.init root c.n c.first c.last, [], false⟩ : BS Cv).core.failed = false := by
  refine ⟨(wf_init c root hlen hlog hn hl).1, ?_, rel_init c root, rfl⟩
  by_cases h : c.first < c.last <;> simp [Tree.init, h, HBnd]

/-- (Equivalence for every split.) For every list of pieces of one stream, the caller feeding a fresh
`GroupVerifier` the unconsumed tail of each piece, stopping at the first error, sees exactly what the caller feeding
a fresh `RangeVerifier` the same pieces sees: the same groups (offset and length) at the same calls, the same error,
and the verifiers end in related states. Both equal the byte-at-a-time reference `VerifyBytes.bytes` over the
concatenated stream, whatever the split. -/
theorem group_equiv_range (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hrd : ∀ b, (c.rd b).d = b) (root : Cv)
    (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20) (hn : c.n = groups c.len c.log) (hl : c.last ≤ c.n)
    (ps : List Bytes) :
    ∃ s1 o r1 o', driveAllG w c (initG c root) ps = some (s1, o) ∧
      driveAll w c ⟨Tree.init root c.n c.first c.last, [], false⟩ ps = some (r1, o') ∧ o = o'.map projObs ∧
      Rel s1 r1 ∧ bytes c ⟨Tree.init root c.n c.first c.last, [], false⟩ ps.flatten = (r1, o') := by
  obtain ⟨hwf, hbd, hrel, hnf⟩ := init_ready c root hlen hlog hn hl
  obtain ⟨s1, o, r1, o', h1, h2, h3, h4⟩ := driveAllG_eq w hw c hrd ps _ _ hwf hbd hrel hnf
  obtain ⟨r2, o2, h5, h6⟩ := driveAll_eq w hw c ps _ hwf hnf
  rw [h2] at h5
  obtain ⟨rfl, rfl⟩ := Option.some.inj h5 |> Prod.mk.inj
  exact ⟨s1, o, r1, o', h1, h2, h3, h4, h6⟩

/-- A `RangeVerifier` state determines the `GroupVerifier` state related to it. -/
theorem Rel.unique {s s' : GS Cv} {r : BS Cv} (h : Rel s r) (h' : Rel s' r) : s = s' := by
  have hst : s.stack = s'.stack := h.stack.trans h'.stack.symm
  have hre : s.released = s'.released := h.released.trans h'.released.symm
  have hfa : s.failed = s'.failed := h.fail.trans h'.fail.symm
  have hb := h.buf.symm.trans h'.buf
  have hkey : s.pair = s'.pair ∧ s.hb = s'.hb := by
    rcases hs : s.stack with _ | ⟨nd, rest⟩
    · have p1 : s.pair = [] := by
        refine Classical.byContradiction fun hh => ?_
        obtain ⟨_, _, h1, _⟩ := h.pairK hh; rw [hs] at h1; cases h1
      have p2 : s'.pair = [] := by
        refine Classical.byContradiction fun hh => ?_
        obtain ⟨_, _, h1, _⟩ := h'.pairK hh; rw [← hst, hs] at h1; cases h1
      have q1 : s.hb = [] := by
        refine Classical.byContradiction fun hh => ?_
        obtain ⟨_, _, h1, _⟩ := h.hbK hh; rw [hs] at h1; cases h1
      have q2 : s'.hb = [] := by
        refine Classical.byContradiction fun hh => ?_
        obtain ⟨_, _, h1, _⟩ := h'.hbK hh; rw [← hst, hs] at h1; cases h1
      exact ⟨by rw [p1, p2], by rw [q1, q2]⟩
    · by_cases hl : nd.hi - nd.lo = 1
      · have p1 : s.pair = [] := by
          refine Classical.byContradiction fun hh => ?_
          obtain ⟨a, b, h1, h2⟩ := h.pairK hh; rw [hs] at h1; obtain ⟨rfl, rfl⟩ := List.cons.inj h1; exact h2 hl
        have p2 : s'.pair = [] := by
          refine Classical.byContradiction fun hh => ?_
          obtain ⟨a, b, h1, h2⟩ := h'.pairK hh; rw [← hst, hs] at h1; obtain ⟨rfl, rfl⟩ := List.cons.inj h1; exact h2 hl
        rw [p1, p2] at hb
        exact ⟨by rw [p1, p2], by simpa using hb⟩
      · have q1 : s.hb = [] := by
          refine Classical.byContradiction fun hh => ?_
          obtain ⟨a, b, h1, h2⟩ := h.hbK hh; rw [hs] at h1; obtain ⟨rfl, rfl⟩ := List.cons.inj h1; exact hl h2
        have q2 : s'.hb = [] := by
          refine Classical.byContradiction fun hh => ?_
          obtain ⟨a, b, h1, h2⟩ := h'.hbK hh; rw [← hst, hs] at h1; obtain ⟨rfl, rfl⟩ := List.cons.inj h1; exact hl h2
        rw [q1, q2] at hb
        exact ⟨by simpa using hb, by rw [q1, q2]⟩
  cases s; cases s'
  simp only at hst hre hfa hkey ⊢
  obtain ⟨k1, k2⟩ := hkey
  subst hst hre hfa k1 k2
  rfl

/-- Two splits of one stream give the same result with `GroupVerifier`. -/
theorem group_split_invariance (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hrd : ∀ b, (c.rd b).d = b) (root : Cv)
    (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20) (hn : c.n = groups c.len c.log) (hl : c.last ≤ c.n)
    (ps qs : List Bytes) (h : ps.flatten = qs.flatten) :
    ∃ s1 o, driveAllG w c (initG c root) ps = some (s1, o) ∧ driveAllG w c (initG c root) qs = some (s1, o) := by
  obtain ⟨s1, o, r1, o', h1, h2, h3, h4, h5⟩ := group_equiv_range w hw c hrd root hlen hlog hn hl ps
  obtain ⟨s2, o2, r2, o2', h1', h2', h3', h4', h5'⟩ := group_equiv_range w hw c hrd root hlen hlog hn hl qs
  rw [h] at h5
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (h5.symm.trans h5')
  have hs := Rel.unique h4 h4'
  subst hs
  have ho : o = o2 := h3.trans h3'.symm
  subst ho
  exact ⟨s1, o, h1, h1'⟩

end

end Pinc.ValuesVerify

#audit_axioms Pinc.ValuesVerify.feedG_sim
#audit_axioms Pinc.ValuesVerify.drivePieceG_eq
#audit_axioms Pinc.ValuesVerify.driveAllG_eq
#audit_axioms Pinc.ValuesVerify.group_equiv_range
#audit_axioms Pinc.ValuesVerify.group_split_invariance
