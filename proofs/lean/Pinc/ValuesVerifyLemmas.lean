import Pinc.ValuesVerify

/-!
# `GroupVerifier`: the stack bound, the completion of an item, the shape of a call

* `HBnd`, `hbnd_feed`: the node stack never holds more than `hh n + 1 <= 55` nodes, so the 64-node cap of
  `pushG` (and of `RangeVerifier`'s stack) is never reached.
* `completePairG_eq`, `finishGroupG_eq`: completing an item is exactly one step `Tree.feed` of the item model on the
  abstract state `absR`, with the arithmetic of the code succeeding.
* `feedGroupG_nf`, `feedPairG_nf`: a call is `min(input, still needed)` bytes taken, buffered while the item is
  incomplete and completed when it is not.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Pinc.ValuesVerify
open Pinc.Layout Pinc.Tree Pinc.Machine Pinc.VerifyBytes

theorem isIlog2_log2 : ∀ x, 0 < x → x < 2 ^ 64 → IsIlog2 x (Nat.log2 x) := fun x hx _ =>
  ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

theorem hh_le_54 (n : Nat) (h : n ≤ 2 ^ 54) : hh n ≤ 54 := by
  unfold hh
  by_cases h1 : n ≤ 1
  · simp [h1]
  · simp only [h1, ite_false]
    have : Nat.log2 (n - 1) < 54 := (Nat.log2_lt (by omega)).2 (by omega)
    omega

theorem hh_le_pow {x k : Nat} (h : x ≤ 2 ^ k) : hh x ≤ k := by
  unfold hh
  by_cases h1 : x ≤ 1
  · simp [h1]
  · simp only [h1, ite_false]
    have hk : 1 ≤ k := by
      refine Classical.byContradiction fun hk => ?_
      have : k = 0 := by omega
      subst this; simp at h; omega
    have : Nat.log2 (x - 1) < k := (Nat.log2_lt (by omega)).2 (by
      have : 2 ^ k ≥ x := h
      omega)
    omega

/-- The stack invariant: the node at height `h` (counted by `hh` of its span) sits above fewer than `H - h` nodes. -/
def HBnd {Cv : Type} (H : Nat) : List (Node Cv) → Prop
  | [] => True
  | nd :: rest => hh (nd.hi - nd.lo) + rest.length ≤ H ∧ HBnd H rest

theorem hbnd_len {Cv : Type} (H : Nat) : ∀ st : List (Node Cv), HBnd H st → st.length ≤ H + 1 := by
  intro st
  cases st with
  | nil => intro _; simp
  | cons nd rest => intro h; have := h.1; simp only [List.length_cons]; omega

theorem hbnd_expand {Cv : Type} (H first last : Nat) (nd : Node Cv) (rest : List (Node Cv)) (l r : Cv)
    (h : HBnd H (nd :: rest)) (h2 : nd.hi - nd.lo ≥ 2) :
    HBnd H ((if first < nd.lo + leftGroups (nd.hi - nd.lo) then [⟨l, nd.lo, nd.lo + leftGroups (nd.hi - nd.lo)⟩] else []) ++
      (if nd.lo + leftGroups (nd.hi - nd.lo) < last then [⟨r, nd.lo + leftGroups (nd.hi - nd.lo), nd.hi⟩] else []) ++ rest) := by
  obtain ⟨h1, hr⟩ := h
  have hlg := hh_leftGroups _ h2
  have hlt := leftGroups_lt _ h2
  have hle := le_two_leftGroups _ h2
  have hl : hh (nd.lo + leftGroups (nd.hi - nd.lo) - nd.lo) + 1 + rest.length ≤ H := by
    rw [show nd.lo + leftGroups (nd.hi - nd.lo) - nd.lo = leftGroups (nd.hi - nd.lo) by omega]
    omega
  have hrr : hh (nd.hi - (nd.lo + leftGroups (nd.hi - nd.lo))) + rest.length ≤ H := by
    have := hh_mono (a := nd.hi - (nd.lo + leftGroups (nd.hi - nd.lo))) (b := leftGroups (nd.hi - nd.lo)) (by omega)
    omega
  by_cases a : first < nd.lo + leftGroups (nd.hi - nd.lo) <;> by_cases b : nd.lo + leftGroups (nd.hi - nd.lo) < last <;>
    simp [a, b, HBnd, hr]
  · exact ⟨by omega, hrr⟩
  · omega
  · exact hrr

theorem hbnd_feed {Cv : Type} [DecidableEq Cv] (Hh : Hash Cv Bytes) (n first last H : Nat) (s : State Cv Bytes)
    (it : Raw Cv Bytes) (h : HBnd H s.stack) (hlo : ∀ nd ∈ s.stack, nd.lo < nd.hi) : HBnd H (Tree.feed Hh n first last s it).stack := by
  by_cases hf : s.failed = true
  · simp [Tree.feed, hf, h]
  · rcases hs : s.stack with _ | ⟨nd, rest⟩
    · simp [Tree.feed, hf, hs, HBnd]
    · rw [hs] at h
      unfold Tree.feed
      simp only [hf, hs, Bool.false_eq_true, ite_false]
      by_cases hl : nd.hi - nd.lo = 1
      · simp only [hl, ite_true]
        by_cases hh' : Hh.leaf (isRoot n nd.lo nd.hi) nd.lo it.d = nd.cv
        · simp only [hh', ite_true]; exact h.2
        · simp only [hh', ite_false]; exact h
      · simp only [hl, ite_false]
        by_cases hh' : Hh.parent (isRoot n nd.lo nd.hi) it.l it.r = nd.cv
        · simp only [hh', ite_true]
          have := hlo nd (by rw [hs]; exact List.mem_cons_self ..)
          exact hbnd_expand H first last nd rest it.l it.r h (by omega)
        · simp only [hh', ite_false]; exact h


section
variable {Cv : Type} [DecidableEq Cv]

/-- The item model's view of a verifier state. -/
def absR (s : GS Cv) : State Cv Bytes := ⟨s.stack, s.failed.isSome, s.released⟩

theorem pushG_ok (s : GS Cv) (n : Node Cv) (hf : s.failed = none) (hl : s.stack.length < stackCap) :
    pushG s n = { s with stack := n :: s.stack } := by
  simp [pushG, hf, hl]

/-- (`complete_pair`.) Completing a pair is one step of the item model, and none of its arithmetic fails: the
subtraction `hi - lo`, the split `lo + left_groups(hi - lo)`, and the two pushes stay below the stack cap. -/
theorem completePairG_eq (c : Cfg Cv) (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20) (hn : c.n = groups c.len c.log)
    (s : GS Cv) (nd : Node Cv) (rest : List (Node Cv)) (pair : Bytes)
    (hf : s.failed = none) (hs : s.stack = nd :: rest) (hnd : nd.lo < nd.hi ∧ nd.hi ≤ c.n)
    (hleaf : ¬ nd.hi - nd.lo = 1) (hb : HBnd (hh c.n) s.stack) :
    ∃ s1, completePairG c s nd rest pair = some s1 ∧ absR s1 = Tree.feed c.H c.n c.first c.last (absR s) (c.rd pair) ∧
      s1.pair = [] ∧ s1.hb = s.hb ∧ s1.released = s.released ∧
      (s1.failed = none ∨ s1.failed = some .parentMismatch) := by
  have hn54 : c.n ≤ 2 ^ 54 := hn ▸ groups_le c.len c.log hlen
  have hh54 := hh_le_54 c.n hn54
  rw [hs] at hb
  obtain ⟨hb1, hb2⟩ := hb
  have h2 : nd.hi - nd.lo ≥ 2 := by omega
  have hhh : 1 ≤ hh (nd.hi - nd.lo) := by
    unfold hh; simp only [show ¬ nd.hi - nd.lo ≤ 1 by omega, ite_false]; omega
  have hrest : rest.length + 2 ≤ stackCap := by unfold stackCap; omega
  obtain ⟨hsub, -, hmid⟩ := complete_arith Nat.log2 isIlog2_log2 c.len c.log c.n hn hlen hlog nd hnd
  obtain ⟨hlg, hadd⟩ := hmid hleaf
  have hlt1 : rest.length < stackCap := by omega
  have hlt2 : rest.length + 1 < stackCap := by omega
  by_cases hp : c.H.parent (isRoot c.n nd.lo nd.hi) (c.rd pair).l (c.rd pair).r = nd.cv
  · by_cases ma : c.first < nd.lo + leftGroups (nd.hi - nd.lo) <;>
      by_cases mb : nd.lo + leftGroups (nd.hi - nd.lo) < c.last <;>
      simp [completePairG, hp, hsub, hlg, hadd, ma, mb, pushG, hf, hlt1, hlt2, Tree.feed, hleaf, absR, hs]
  · simp [completePairG, hp, Tree.feed, hleaf, absR, hs, hf]

/-- (The end of `feed_group`.) A complete group is one step of the item model; a match releases it with the bytes
hashed, a mismatch fails the verifier with `GroupMismatch` and releases nothing. -/
theorem finishGroupG_eq (c : Cfg Cv) (hlen : c.len ≤ u64Max) (hlog : c.log ≤ 20) (hn : c.n = groups c.len c.log)
    (hrd : ∀ b, (c.rd b).d = b) (s : GS Cv) (nd : Node Cv) (rest : List (Node Cv)) (data : Bytes) (take size : Nat)
    (hf : s.failed = none) (hs : s.stack = nd :: rest) (hnd : nd.lo < nd.hi ∧ nd.hi ≤ c.n) (hleaf : nd.hi - nd.lo = 1) :
    ∃ g s1, finishGroupG c s nd rest data take size = some (g, s1) ∧
      absR s1 = Tree.feed c.H c.n c.first c.last (absR s) (c.rd data) ∧ s1.hb = [] ∧ s1.pair = s.pair ∧
      ((s1.failed = none ∧ s1.released = s.released ++ [(nd.lo, data)] ∧
          g = .ok take (some (nd.lo * groupLen c.log, size))) ∨
       (s1.failed = some .groupMismatch ∧ s1.released = s.released ∧ g = .err .groupMismatch)) := by
  obtain ⟨-, hmul, -⟩ := complete_arith Nat.log2 isIlog2_log2 c.len c.log c.n hn hlen hlog nd hnd
  have hm := hmul hleaf
  by_cases hp : c.H.leaf (isRoot c.n nd.lo nd.hi) nd.lo data = nd.cv
  · simp [finishGroupG, hp, hm, Tree.feed, hleaf, absR, hs, hf, hrd]
    exact ⟨_, _, ⟨rfl, rfl⟩, by simp⟩
  · simp [finishGroupG, hp, Tree.feed, hleaf, absR, hs, hf, hrd]
    exact ⟨_, _, ⟨rfl, rfl⟩, by simp⟩

theorem pow30_lt (w : Nat) (hw : w = 32 ∨ w = 64) : (2 : Nat) ^ 30 < 2 ^ w := by
  have : (2 : Nat) ^ 30 < 2 ^ 32 := by decide
  have h32 : 2 ^ 32 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- (A call on a group.) It takes `min(input, still needed)` bytes; they go to the hasher; the group is complete
when they bring `group_n` to its size. No operation of the call fails. -/
theorem feedGroupG_nf (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (hlog : c.log ≤ 20) (s : GS Cv)
    (nd : Node Cv) (rest : List (Node Cv)) (input : Bytes) (size take : Nat)
    (hsize : size = groupSize c.len c.log nd.lo) (hsz : size ≤ groupLen c.log) (htake : take = min input.length (size - s.hb.length))
    (hfill : s.hb.length < size) :
    feedGroupG w c s nd rest input =
      if s.hb.length + take < size then some (.ok take none, { s with hb := s.hb ++ input.take take })
      else finishGroupG c s nd rest (s.hb ++ input.take take) take size := by
  have h30 := pow30_lt w hw
  have hg := groupLen_le c.log hlog
  have hs64 : size < 2 ^ 64 := by
    have : (2 : Nat) ^ 30 < 2 ^ 64 := by decide
    omega
  have hsub : Machine.sub 64 size s.hb.length = some (size - s.hb.length) := by simp [Machine.sub]; omega
  have htf : tryFrom w (size - s.hb.length) = some (size - s.hb.length) := by
    simp only [tryFrom]; rw [if_pos (by omega)]
  have hb0 : (if s.hb.length = 0 then [] else s.hb) = s.hb := by
    by_cases h : s.hb.length = 0
    · simp [List.length_eq_zero_iff.1 h]
    · simp [h]
  have hadd : Machine.add 64 s.hb.length take = some (s.hb.length + take) := by
    simp only [Machine.add]; rw [if_pos (by omega)]
  have htk : min (size - s.hb.length) input.length = take := by rw [htake, Nat.min_comm]
  subst hsize
  simp only [feedGroupG, hsub, htf, hb0, htk, hadd]

/-- (A call on a pair.) It takes `min(input, still needed)` bytes into the pair buffer (or straight from the input when
the buffer is empty and the whole pair is there); the pair is complete when the buffer reaches 64 bytes. -/
theorem feedPairG_nf (w : Nat) (hw : w = 32 ∨ w = 64) (c : Cfg Cv) (s : GS Cv) (nd : Node Cv) (rest : List (Node Cv))
    (input : Bytes) (take : Nat) (htake : take = min input.length (64 - s.pair.length)) (hfill : s.pair.length < 64) :
    feedPairG w c s nd rest input =
      if s.pair.length + take < 64 then some (.ok take none, { s with pair := s.pair ++ input.take take })
      else finishPairG c s nd rest (s.pair ++ input.take take) take := by
  have h30 := pow30_lt w hw
  have hsub : Machine.sub w 64 s.pair.length = some (64 - s.pair.length) := by simp [Machine.sub]; omega
  have hadd : Machine.add w s.pair.length take = some (s.pair.length + take) := by
    simp only [Machine.add]
    have : s.pair.length + take ≤ 64 := by omega
    have : (64 : Nat) < 2 ^ 30 := by decide
    rw [if_pos (by omega)]
  have htk : min input.length (64 - s.pair.length) = take := htake.symm
  simp only [feedPairG, hsub, htk, hadd]
  by_cases hw0 : s.pair = [] ∧ take = 64
  · rw [if_pos hw0]
    obtain ⟨h1, h2⟩ := hw0
    have : ¬ s.pair.length + take < 64 := by simp [h1, h2]
    rw [if_neg this]
    simp [h1]
  · rw [if_neg hw0]
    have h64 : ¬ 64 < s.pair.length + take := by omega
    rw [if_neg h64]

end

end Pinc.ValuesVerify

#audit_axioms Pinc.ValuesVerify.hbnd_feed
#audit_axioms Pinc.ValuesVerify.completePairG_eq
#audit_axioms Pinc.ValuesVerify.finishGroupG_eq
#audit_axioms Pinc.ValuesVerify.feedGroupG_nf
#audit_axioms Pinc.ValuesVerify.feedPairG_nf
