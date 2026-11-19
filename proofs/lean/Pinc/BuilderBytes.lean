import Pinc.Builder
import Pinc.MachineEnc

/-!
# The outboard builder, piece by piece

`Builder` models `OutboardBuilder` one group at a time. This module models the real calls: `update` with
pieces of any size, the bookkeeping fields `in_group` and `consumed`, the hasher of the current group, the
errors `TooMuchData`, `Incomplete` and `OutboardSize`, and the empty value.

* `updateCode` and `finishCode` are the code of `OutboardBuilder::update` and `finish`
  (`pinc-dag/src/tree/builder.rs`), the `usize` conversions on a `w`-bit `usize` (32 or 64) and the `u64`
  arithmetic written as the code writes it. The hasher of a group is the list of the bytes fed to it: the hash
  is abstract as in `Tree`, and incremental `update` calls of the BLAKE3 hasher computing the hash of the
  concatenation is a property of that dependency, assumed.
* `builder_split_invariance`: whatever the split of the value into pieces, every call succeeds, the state after
  the last piece is the group-level state after the last group (`Builder.mainPhase`), and `finish` returns the root
  and has written the parents that the group-level model `Builder.build` gives. So everything proved about the
  group-level model (`Builder.builder_correct`: the root is the genuine root, every parent is written once at its
  pre-order slot with the genuine pair) holds for every split.
* `update_errors`, `finish_errors`: `OutboardSize` exactly when the buffer has the wrong size, checked first;
  `TooMuchData` exactly when the piece is longer than the bytes still due, and then nothing changes;
  `Incomplete` exactly when fewer bytes than declared were fed.
* `builder_empty`: a value of 0 bytes has 0 groups, `finish` writes nothing and returns the root cell the
  constructor set, the hash of the empty input.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Pinc.BuilderBytes
open Pinc.Layout Pinc.Tree Pinc.Builder Pinc.Machine

abbrev Bytes := List Nat

/-- The parameters of a builder: the abstract hash, the declared value length, the group log, the hash of the
empty input (`e0`, what `new` stores as the root of an empty value) and the filler stored otherwise (`z0`). -/
structure BCfg (Cv : Type) where
  H : Hash Cv Bytes
  len : Nat
  log : Nat
  e0 : Cv
  z0 : Cv

/-- The group count. -/
def BCfg.n {Cv : Type} (c : BCfg Cv) : Nat := groups c.len c.log

/-- The initial root cell. -/
def BCfg.c0 {Cv : Type} (c : BCfg Cv) : Cv := if c.len = 0 then c.e0 else c.z0

/-- The bytes of group `k` of a value. -/
def gb (V : Bytes) (g k : Nat) : Bytes := (V.drop (k * g)).take g

/-- `u64::div_ceil`. -/
def ceilDiv (a g : Nat) : Nat := a / g + if a % g = 0 then 0 else 1

/-- The mutable state of an `OutboardBuilder`: `in_group`, `consumed`, the offset the hasher was set to, the
bytes fed to the hasher, and the group-level state (stack, parents written, root cell). -/
structure UB (Cv : Type) where
  ing : Nat
  con : Nat
  off : Nat
  cur : Bytes
  bs : Pinc.Builder.BS Cv

/-- The errors of `update` and `finish`. -/
inductive UErr where
  | outboardSize
  | tooMuchData
  | incomplete
  deriving DecidableEq

section
variable {Cv : Type}

/-- `OutboardBuilder::new`. -/
def UB.init (c : BCfg Cv) : UB Cv := ⟨0, 0, 0, [], ⟨[], [], c.c0⟩⟩

/-- `complete_group` for the leaf at hasher offset `off`: `groupStep` with the leaf index `off / group`. -/
def groupStepAt (H : Hash Cv Bytes) (n k idx : Nat) (cur : Bytes) (s : Pinc.Builder.BS Cv) : Pinc.Builder.BS Cv :=
  let leaf := H.leaf (isRoot n (k - 1) k) idx cur
  if n = 1 then { s with root := leaf }
  else merge H n k (s.stack.length + 1) { s with stack := (leaf, 1) :: s.stack }

/-- `self.in_group = 0; self.complete_group(out)`. -/
def completeGroup (c : BCfg Cv) (st : UB Cv) : UB Cv :=
  { st with ing := 0, cur := [], bs := groupStepAt c.H c.n (ceilDiv st.con (groupLen c.log)) (st.off / groupLen c.log) st.cur st.bs }

/-- One iteration of the loop of `update` on a `w`-bit `usize`: reset the hasher at a group start, take
`min(room, data.len())` bytes, advance `in_group` and `consumed`, complete the group when it is full or the value
ends. `none` is an arithmetic failure (an overflow, an underflow). -/
def updStep (w : Nat) (c : BCfg Cv) (st : UB Cv) (data : Bytes) : Option (UB Cv × Bytes) :=
  let g := groupLen c.log
  let st0 : UB Cv := if st.ing = 0 then { st with cur := [], off := st.con / g * g } else st
  match Machine.sub 64 g st0.ing with
  | none => none
  | some room =>
    let t := min ((tryFrom w room).getD (2 ^ w - 1)) data.length
    match Machine.add 64 st0.ing t, Machine.add 64 st0.con t with
    | some ing', some con' =>
      let st1 : UB Cv := { st0 with ing := ing', con := con', cur := st0.cur ++ data.take t }
      if ing' = g ∨ con' = c.len then some (completeGroup c st1, data.drop t) else some (st1, data.drop t)
    | _, _ => none

/-- The loop of `update`; `fuel` only makes the recursion structural (`updLoop_inv` shows `data.length` is
enough). -/
def updLoop (w : Nat) (c : BCfg Cv) : Nat → UB Cv → Bytes → Option (UB Cv)
  | 0, st, d => if d = [] then some st else none
  | f + 1, st, d =>
    if d = [] then some st else
    match updStep w c st d with
    | none => none
    | some (st', d') => updLoop w c f st' d'

/-- `OutboardBuilder::update`: the state afterwards (unchanged on an error) and the error, if any. `olen` is
the length of the outboard buffer. `none` is an arithmetic failure. -/
def updateCode (w : Nat) (c : BCfg Cv) (olen : Nat) (st : UB Cv) (data : Bytes) : Option (UB Cv × Option UErr) :=
  if olen ≠ outboardSize c.len c.log then some (st, some .outboardSize)
  else match Machine.sub 64 c.len st.con with
    | none => none
    | some rem =>
      if rem < data.length then some (st, some .tooMuchData)
      else match updLoop w c data.length st data with
        | none => none
        | some st' => some (st', none)

/-- `OutboardBuilder::finish`: the root, or the error. -/
def finishCode (c : BCfg Cv) (olen : Nat) (st : UB Cv) : Except UErr Cv :=
  if olen ≠ outboardSize c.len c.log then .error .outboardSize
  else if st.con ≠ c.len then .error .incomplete
  else .ok (finish c.H c.n st.bs.stack.length st.bs).root

/-- The caller feeding a list of pieces in order, stopping at the first error. -/
def updateAll (w : Nat) (c : BCfg Cv) (olen : Nat) : UB Cv → List Bytes → Option (UB Cv × Option UErr)
  | st, [] => some (st, none)
  | st, p :: ps =>
    match updateCode w c olen st p with
    | none => none
    | some (st', some e) => some (st', some e)
    | some (st', none) => updateAll w c olen st' ps

/-! ## The invariant: the state is a function of the bytes consumed -/

/-- After `con` bytes of the value `V`: either all of them (the last group, full or partial, is complete and
the group-level state is the one after `n` groups), or inside a group (`con % g` bytes are in the hasher, which
was set to the group's offset once a byte is in it, and the group-level state is the one after `con / g` groups). -/
def BInv (c : BCfg Cv) (V : Bytes) (st : UB Cv) : Prop :=
  st.con ≤ c.len ∧
  ((st.con = c.len ∧ st.ing = 0 ∧ st.cur = [] ∧ st.bs = mainPhase c.H (gb V (groupLen c.log)) c.n c.c0 c.n) ∨
   (st.con < c.len ∧ st.ing = st.con % groupLen c.log ∧
     st.cur = (V.drop (st.con / groupLen c.log * groupLen c.log)).take (st.con % groupLen c.log) ∧
     (0 < st.con % groupLen c.log → st.off = st.con / groupLen c.log * groupLen c.log) ∧
     st.bs = mainPhase c.H (gb V (groupLen c.log)) c.n c.c0 (st.con / groupLen c.log)))

theorem BInv_init (c : BCfg Cv) (V : Bytes) (hV : V.length = c.len) : BInv c V (UB.init c) := by
  have hg := groupLen_pos c.log
  refine ⟨Nat.zero_le _, ?_⟩
  by_cases h0 : c.len = 0
  · left
    have hn : c.n = 0 := by
      unfold BCfg.n groups; rw [h0]; simp
    refine ⟨h0.symm, rfl, rfl, ?_⟩
    rw [hn]
    simp [UB.init, mainPhase]
  · right
    refine ⟨by simp [UB.init]; omega, by simp [UB.init], by simp [UB.init], by simp [UB.init], ?_⟩
    simp [UB.init, mainPhase]

theorem groupStepAt_eq (H : Hash Cv Bytes) (data : Nat → Bytes) (n k : Nat) (s : Pinc.Builder.BS Cv)
    (hk : 1 ≤ k) : groupStepAt H n k (k - 1) (data (k - 1)) s = groupStep H data n k s := rfl

theorem ceilDiv_succ (q s g : Nat) (hs : 0 < s) (hsg : s ≤ g) : ceilDiv (q * g + s) g = q + 1 := by
  have hg : 0 < g := by omega
  unfold ceilDiv
  by_cases h : s = g
  · subst h
    have e : q * s + s = (q + 1) * s := by rw [Nat.succ_mul]
    rw [e, Nat.mul_div_cancel _ hg, Nat.mul_mod_left]
    simp
  · have h1 := (Nat.div_mod_unique (b := g) (a := q * g + s) (d := q) (c := s) hg).2 ⟨by rw [Nat.mul_comm]; omega, by omega⟩
    rw [h1.1, h1.2]
    simp [show s ≠ 0 by omega]

theorem divmod_of (q s g : Nat) (hg : 0 < g) (hs : s < g) : (q * g + s) / g = q ∧ (q * g + s) % g = s :=
  (Nat.div_mod_unique (b := g) (a := q * g + s) (d := q) (c := s) hg).2 ⟨by rw [Nat.mul_comm]; omega, hs⟩

theorem take_add_drop (V : Bytes) (a r t : Nat) :
    (V.drop a).take r ++ (V.drop (a + r)).take t = (V.drop a).take (r + t) := by
  rw [List.take_add, List.drop_drop]


theorem groupStep_data_congr (H : Hash Cv Bytes) (d1 d2 : Nat → Bytes) (n k : Nat) (s : Pinc.Builder.BS Cv)
    (h : d1 (k - 1) = d2 (k - 1)) : groupStep H d1 n k s = groupStep H d2 n k s := by
  simp [groupStep, h]

/-- One iteration of the loop of `update`, from a state inside a group: it takes `t` bytes (`1 <= t <= length`),
never fails, and leaves the state of the value after `consumed + t` bytes. -/
theorem updStep_inv (w : Nat) (hw : w = 32 ∨ w = 64) (c : BCfg Cv) (V : Bytes) (hV : V.length = c.len)
    (hlog : c.log ≤ 20) (hlen : c.len < 2 ^ 64) (st : UB Cv) (hI : BInv c V st) (d : Bytes) (hd : d ≠ [])
    (hle : st.con + d.length ≤ c.len) (hpre : d = (V.drop st.con).take d.length) :
    ∃ t st1, 1 ≤ t ∧ t ≤ d.length ∧ updStep w c st d = some (st1, d.drop t) ∧ BInv c V st1 ∧
      st1.con = st.con + t := by
  obtain ⟨hcle, hcase⟩ := hI
  have hg := groupLen_pos c.log
  have hg30 := groupLen_le c.log hlog
  have h30 : (2 : Nat) ^ 30 < 2 ^ w := by
    have : (2 : Nat) ^ 30 < 2 ^ 32 := by decide
    have h32 : 2 ^ 32 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h64 : (2 : Nat) ^ 30 < 2 ^ 64 := by decide
  have hdl : 0 < d.length := by
    cases d with
    | nil => exact absurd rfl hd
    | cons _ _ => simp
  rcases hcase with ⟨hcon, _⟩ | ⟨hlt, hing, hcur, hoff, hbs⟩
  · omega
  have hn := groupLen_ge c.log
  generalize hgd : groupLen c.log = g at *
  obtain ⟨q, hq⟩ : ∃ q, q = st.con / g := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = st.con % g := ⟨_, rfl⟩
  have hm : q * g + r = st.con := by
    have := Nat.div_add_mod st.con g
    rw [← hq, ← hr] at this
    rw [Nat.mul_comm]; exact this
  have hrg : r < g := by rw [hr]; exact Nat.mod_lt _ hg
  rw [← hr] at hing
  rw [← hq, ← hr] at hcur
  rw [← hq, ← hr] at hoff
  rw [← hq] at hbs
  have hst0 : (if st.ing = 0 then ({ st with cur := [], off := st.con / g * g } : UB Cv) else st) =
      { st with cur := (V.drop (q * g)).take r, off := q * g } := by
    by_cases h0 : st.ing = 0
    · have hr0 : r = 0 := by omega
      simp [h0, hr0, hq]
    · have : 0 < r := by omega
      simp only [h0, ite_false]
      have h1 := hoff this
      cases st with
      | mk i cn o cu b =>
        simp only at h1 hcur ⊢
        subst h1
        subst hcur
        rfl
  obtain ⟨t, ht⟩ : ∃ t, t = min (g - r) d.length := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by rw [ht]; omega
  have htd : t ≤ d.length := by rw [ht]; exact Nat.min_le_right _ _
  have htg : t ≤ g - r := by rw [ht]; exact Nat.min_le_left _ _
  have hsub : Machine.sub 64 g r = some (g - r) := by simp [Machine.sub]; omega
  have hroom : (tryFrom w (g - r)).getD (2 ^ w - 1) = g - r := by
    simp only [tryFrom]; rw [if_pos (by omega)]; rfl
  have hadd1 : Machine.add 64 r t = some (r + t) := by
    simp only [Machine.add]; rw [if_pos (by omega)]
  have hadd2 : Machine.add 64 st.con t = some (st.con + t) := by
    simp only [Machine.add]; rw [if_pos (by omega)]
  have hdt : d.take t = (V.drop st.con).take t := by
    conv => lhs; rw [hpre]
    rw [List.take_take]; congr 1; omega
  have hcur' : (V.drop (q * g)).take r ++ d.take t = (V.drop (q * g)).take (r + t) := by
    rw [hdt, ← hm, ← take_add_drop V (q * g) r t]
  have hdrop : d.drop t = (V.drop (st.con + t)).take (d.length - t) := by
    conv => lhs; rw [hpre]
    rw [List.drop_take, List.drop_drop]
  -- the call
  have hcall : updStep w c st d = some (
      (if r + t = g ∨ st.con + t = c.len then
        completeGroup c { ing := r + t, con := st.con + t, off := q * g, cur := (V.drop (q * g)).take (r + t), bs := st.bs }
       else { ing := r + t, con := st.con + t, off := q * g, cur := (V.drop (q * g)).take (r + t), bs := st.bs }), d.drop t) := by
    unfold updStep
    simp only [hgd]
    rw [hst0]
    simp only [hing, hsub, hroom, ← ht, hadd1, hadd2]
    rw [hcur']
    by_cases hc : r + t = g ∨ st.con + t = c.len <;> simp [hc]
  refine ⟨t, _, ht1, htd, hcall, ?_, ?_⟩
  rotate_left
  · by_cases hc : r + t = g ∨ st.con + t = c.len <;> simp [hc, completeGroup]
  have hcon' : st.con + t = q * g + (r + t) := by omega
  have hcg : completeGroup c { ing := r + t, con := st.con + t, off := q * g, cur := (V.drop (q * g)).take (r + t), bs := st.bs } =
      { ing := 0, con := st.con + t, off := q * g, cur := [], bs := groupStepAt c.H c.n (ceilDiv (st.con + t) g) q ((V.drop (q * g)).take (r + t)) st.bs } := by
    unfold completeGroup
    simp only [hgd, Nat.mul_div_cancel q hg]
  have hnn : 0 < r + t := by omega
  -- the group of index `q` completes: the group-level state after `q + 1` groups
  have hstep : ∀ cur', cur' = gb V g q →
      groupStepAt c.H c.n (q + 1) q cur' st.bs = mainPhase c.H (gb V g) c.n c.c0 (q + 1) := by
    intro cur' hcur'
    subst hcur'
    rw [hbs]
    exact groupStepAt_eq c.H (gb V g) c.n (q + 1) _ (by omega)
  have hgroups : ∀ s, 0 < s → s ≤ g → c.len = q * g + s → c.n = q + 1 := by
    intro s hs hsg hl
    unfold BCfg.n groups
    rw [hgd, hl]
    by_cases h : s = g
    · subst h
      have e : q * s + s = (q + 1) * s := by rw [Nat.succ_mul]
      rw [e, Nat.mul_div_cancel _ hg, Nat.mul_mod_left]; simp
    · have := divmod_of q s g hg (by omega)
      rw [this.1, this.2]; simp [show s ≠ 0 by omega]
  have hmid : ∀ cur' (b : Pinc.Builder.BS Cv) (ing off : Nat), ing = 0 → cur' = [] →
      st.con + t < c.len → (st.con + t) % g = 0 → b = mainPhase c.H (gb V g) c.n c.c0 ((st.con + t) / g) →
      BInv c V { ing := ing, con := st.con + t, off := off, cur := cur', bs := b } := by
    intro cur' b ing off hi hc hl hm hb
    refine ⟨show st.con + t ≤ c.len by omega, Or.inr ⟨hl, ?_, ?_, ?_, ?_⟩⟩
    · simp only [hgd]; rw [hm]; exact hi
    · simp only [hgd]; rw [hm, hc]; simp
    · simp only [hgd]; intro h; rw [hm] at h; omega
    · simp only [hgd]; exact hb
  by_cases hA : r + t = g
  · have hce : ceilDiv (st.con + t) g = q + 1 := by
      rw [hcon', hA]; exact ceilDiv_succ q g g hg (Nat.le_refl _)
    have hcurA : (V.drop (q * g)).take (r + t) = gb V g q := by rw [hA]; rfl
    have hbsA := hstep (gb V g q) rfl
    rw [if_pos (Or.inl hA), hcg, hce, hcurA, hbsA]
    by_cases hL : st.con + t = c.len
    · refine ⟨show st.con + t ≤ c.len by omega, Or.inl ⟨hL, rfl, rfl, ?_⟩⟩
      have := hgroups g hg (Nat.le_refl _) (by omega)
      show mainPhase c.H (gb V g) c.n c.c0 (q + 1) = mainPhase c.H (gb V (groupLen c.log)) c.n c.c0 c.n
      rw [hgd, this]
    · have hd1 : (st.con + t) / g = q + 1 ∧ (st.con + t) % g = 0 := by
        have := divmod_of (q + 1) 0 g hg hg
        simp only [Nat.add_zero] at this
        rw [show st.con + t = (q + 1) * g by rw [Nat.succ_mul]; omega]
        exact this
      exact hmid [] _ 0 (q * g) rfl rfl (by omega) hd1.2 (by rw [hd1.1])
  · by_cases hL : st.con + t = c.len
    · -- the last, partial group
      have hce : ceilDiv (st.con + t) g = q + 1 := by
        rw [hcon']; exact ceilDiv_succ q (r + t) g hnn (by omega)
      have hcurB : (V.drop (q * g)).take (r + t) = gb V g q := by
        unfold gb
        have : (V.drop (q * g)).length ≤ g := by
          simp only [List.length_drop]; omega
        rw [List.take_of_length_le this, List.take_of_length_le (by simp only [List.length_drop]; omega)]
      have hbsB := hstep (gb V g q) rfl
      rw [if_pos (Or.inr hL), hcg, hce, hcurB, hbsB]
      refine ⟨show st.con + t ≤ c.len by omega, Or.inl ⟨hL, rfl, rfl, ?_⟩⟩
      have := hgroups (r + t) hnn (by omega) (by omega)
      show mainPhase c.H (gb V g) c.n c.c0 (q + 1) = mainPhase c.H (gb V (groupLen c.log)) c.n c.c0 c.n
      rw [hgd, this]
    · -- the group is still open
      rw [if_neg (show ¬ (r + t = g ∨ st.con + t = c.len) by omega)]
      have hd := divmod_of q (r + t) g hg (by omega)
      rw [← hcon'] at hd
      refine ⟨show st.con + t ≤ c.len by omega, Or.inr ⟨show st.con + t < c.len by omega, ?_, ?_, ?_, ?_⟩⟩
      · simp only [hgd]; rw [hd.2]
      · simp only [hgd]; rw [hd.1, hd.2]
      · simp only [hgd]; intro _; rw [hd.1]
      · simp only [hgd]; rw [hd.1]; exact hbs


theorem pre_drop (V d : Bytes) (m t : Nat) (hpre : d = (V.drop m).take d.length) :
    d.drop t = (V.drop (m + t)).take (d.length - t) := by
  conv => lhs; rw [hpre]
  rw [List.drop_take, List.drop_drop]

/-- The loop of `update`: from any state a stream can leave, the next `data.length` bytes of the value are
absorbed without failure, and the state is that of the value after them. -/
theorem updLoop_inv (w : Nat) (hw : w = 32 ∨ w = 64) (c : BCfg Cv) (V : Bytes) (hV : V.length = c.len)
    (hlog : c.log ≤ 20) (hlen : c.len < 2 ^ 64) :
    ∀ (f : Nat) (st : UB Cv) (d : Bytes), BInv c V st → st.con + d.length ≤ c.len →
      d = (V.drop st.con).take d.length → d.length ≤ f →
      ∃ st', updLoop w c f st d = some st' ∧ BInv c V st' ∧ st'.con = st.con + d.length := by
  intro f
  induction f with
  | zero =>
    intro st d hI _ _ hf
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨st, by simp [updLoop], hI, rfl⟩
  | succ f ih =>
    intro st d hI hle hpre hf
    by_cases hd : d = []
    · subst hd
      exact ⟨st, by simp [updLoop], hI, rfl⟩
    · obtain ⟨t, st1, ht1, htd, hs, hI1, hc1⟩ := updStep_inv w hw c V hV hlog hlen st hI d hd hle hpre
      have hpre' := pre_drop V d st.con t hpre
      have hlen' : (d.drop t).length = d.length - t := List.length_drop ..
      obtain ⟨st', hl, hI', hc'⟩ := ih st1 (d.drop t) hI1 (by rw [hlen', hc1]; omega)
        (by rw [hlen', hc1, ← hpre']) (by rw [hlen']; omega)
      refine ⟨st', ?_, hI', ?_⟩
      · simp [updLoop, hd, hs, hl]
      · rw [hc', hc1, hlen']; omega

/-- `update` on a piece that fits, with a buffer of the right size, succeeds and leaves the state of the value
after the piece. -/
theorem update_ok (w : Nat) (hw : w = 32 ∨ w = 64) (c : BCfg Cv) (V : Bytes) (hV : V.length = c.len)
    (hlog : c.log ≤ 20) (hlen : c.len < 2 ^ 64) (st : UB Cv) (hI : BInv c V st) (d : Bytes)
    (hle : st.con + d.length ≤ c.len) (hpre : d = (V.drop st.con).take d.length) :
    ∃ st', updateCode w c (outboardSize c.len c.log) st d = some (st', none) ∧ BInv c V st' ∧
      st'.con = st.con + d.length := by
  obtain ⟨st', hl, hI', hc⟩ := updLoop_inv w hw c V hV hlog hlen d.length st d hI hle hpre (Nat.le_refl _)
  refine ⟨st', ?_, hI', hc⟩
  have hs : Machine.sub 64 c.len st.con = some (c.len - st.con) := by
    simp only [Machine.sub]; rw [if_pos hI.1]
  simp [updateCode, hs, show ¬ (c.len - st.con < d.length) by omega, hl]

/-- A piece longer than the bytes still due, or a buffer of the wrong size, is refused before anything is
touched: the state is unchanged. The buffer size is checked first. -/
theorem update_errors (w : Nat) (c : BCfg Cv) (olen : Nat) (st : UB Cv) (d : Bytes) (hcon : st.con ≤ c.len)
    (hlen : c.len < 2 ^ 64) :
    (olen ≠ outboardSize c.len c.log → updateCode w c olen st d = some (st, some .outboardSize)) ∧
    (olen = outboardSize c.len c.log → c.len - st.con < d.length →
      updateCode w c olen st d = some (st, some .tooMuchData)) := by
  refine ⟨fun h => by simp [updateCode, h], fun h hl => ?_⟩
  have hs : Machine.sub 64 c.len st.con = some (c.len - st.con) := by
    simp only [Machine.sub]; rw [if_pos hcon]
  simp [updateCode, h, hs, hl]

/-- `finish`: the buffer size is checked first (`OutboardSize`), then that every declared byte was fed
(`Incomplete`); otherwise the root. -/
theorem finish_errors (c : BCfg Cv) (olen : Nat) (st : UB Cv) :
    (finishCode c olen st = .error .outboardSize ↔ olen ≠ outboardSize c.len c.log) ∧
    (finishCode c olen st = .error .incomplete ↔ olen = outboardSize c.len c.log ∧ st.con ≠ c.len) ∧
    ((∃ r, finishCode c olen st = .ok r) ↔ olen = outboardSize c.len c.log ∧ st.con = c.len) := by
  unfold finishCode
  by_cases h1 : olen ≠ outboardSize c.len c.log
  · simp [h1]
  · by_cases h2 : st.con ≠ c.len <;> simp_all

theorem updateAll_inv (w : Nat) (hw : w = 32 ∨ w = 64) (c : BCfg Cv) (V : Bytes) (hV : V.length = c.len)
    (hlog : c.log ≤ 20) (hlen : c.len < 2 ^ 64) :
    ∀ (ps : List Bytes) (st : UB Cv), BInv c V st → ps.flatten = V.drop st.con →
      ∃ st', updateAll w c (outboardSize c.len c.log) st ps = some (st', none) ∧ BInv c V st' ∧
        st'.con = c.len := by
  intro ps
  induction ps with
  | nil =>
    intro st hI hps
    simp only [List.flatten_nil] at hps
    have : st.con = c.len := by
      have h1 := congrArg List.length hps
      have h2 := hI.1
      simp [hV] at h1; omega
    exact ⟨st, by simp [updateAll], hI, this⟩
  | cons p ps ih =>
    intro st hI hps
    simp only [List.flatten_cons] at hps
    have hpl : p.length + ps.flatten.length = c.len - st.con := by
      have := congrArg List.length hps
      simpa [hV] using this
    have hpre : p = (V.drop st.con).take p.length := by
      rw [← hps, List.take_left]
    obtain ⟨st1, hu, hI1, hc1⟩ := update_ok w hw c V hV hlog hlen st hI p
      (by have := hI.1; omega) hpre
    have hps' : ps.flatten = V.drop st1.con := by
      rw [hc1]
      have : V.drop (st.con + p.length) = (V.drop st.con).drop p.length := by rw [List.drop_drop]
      rw [this, ← hps, List.drop_left]
    obtain ⟨st2, hu2, hI2, hc2⟩ := ih st1 hI1 hps'
    exact ⟨st2, by simp [updateAll, hu, hu2], hI2, hc2⟩

/-- (Split invariance.) Feed a value of `c.len` bytes in any split into pieces, with a buffer of the right size:
every call succeeds, the state after the last piece has nothing pending, and `finish` returns the root of the
group-level model `Builder.build` over the groups of the value, having written exactly the parents that model
writes. The split does not appear in the result, so it is the same for every split. -/
theorem builder_split_invariance (w : Nat) (hw : w = 32 ∨ w = 64) (c : BCfg Cv) (V : Bytes)
    (hV : V.length = c.len) (hlog : c.log ≤ 20) (hlen : c.len < 2 ^ 64) (ps : List Bytes) (hps : ps.flatten = V) :
    ∃ st, updateAll w c (outboardSize c.len c.log) (UB.init c) ps = some (st, none) ∧ st.con = c.len ∧
      st.ing = 0 ∧ st.cur = [] ∧
      finish c.H c.n st.bs.stack.length st.bs = build c.H (gb V (groupLen c.log)) c.n c.c0 ∧
      finishCode c (outboardSize c.len c.log) st = .ok (build c.H (gb V (groupLen c.log)) c.n c.c0).root := by
  obtain ⟨st, hu, hI, hc⟩ := updateAll_inv w hw c V hV hlog hlen ps (UB.init c) (BInv_init c V hV)
    (by simpa [UB.init] using hps)
  obtain ⟨_, hcase⟩ := hI
  rcases hcase with ⟨_, hing, hcur, hbs⟩ | ⟨hlt, _⟩
  · have hb : finish c.H c.n st.bs.stack.length st.bs = build c.H (gb V (groupLen c.log)) c.n c.c0 := by
      rw [hbs]; rfl
    refine ⟨st, hu, hc, hing, hcur, hb, ?_⟩
    simp [finishCode, hc, hb]
  · omega


variable [DecidableEq Cv]

/-- A value of 0 bytes: no group, no parent, an outboard of 0 bytes, and `finish` returns the root cell that
`new` stored, the hash of the empty input, without a write. -/
theorem builder_empty (c : BCfg Cv) (h0 : c.len = 0) :
    c.n = 0 ∧ outboardSize c.len c.log = 0 ∧ c.c0 = c.e0 ∧ (UB.init c).bs.w = [] ∧
      finishCode c 0 (UB.init c) = .ok c.e0 := by
  have hn : c.n = 0 := by unfold BCfg.n groups; rw [h0]; simp
  have ho : outboardSize c.len c.log = 0 := by
    unfold outboardSize
    rw [show groups c.len c.log = 0 from hn]
  have hc : c.c0 = c.e0 := by simp [BCfg.c0, h0]
  refine ⟨hn, ho, hc, rfl, ?_⟩
  unfold finishCode
  rw [if_neg (by rw [ho]; simp), if_neg (by simp [UB.init, h0])]
  simp [UB.init, finish, hc]

/-- (The root.) Whatever the split, the root `finish` returns is the genuine root of the tree over the groups
of the value, and for 0 groups the hash of the empty input. With `Builder.builder_correct` the parents written
are the genuine parents, each once, at its pre-order slot. -/
theorem builder_split_root (w : Nat) (hw : w = 32 ∨ w = 64) (c : BCfg Cv) (V : Bytes) (hV : V.length = c.len)
    (hlog : c.log ≤ 20) (hlen : c.len < 2 ^ 64) (ps : List Bytes) (hps : ps.flatten = V) :
    ∃ st, updateAll w c (outboardSize c.len c.log) (UB.init c) ps = some (st, none) ∧
      finishCode c (outboardSize c.len c.log) st =
        .ok (if c.len = 0 then c.e0 else gcv c.H (gb V (groupLen c.log)) c.n 0 c.n) := by
  obtain ⟨st, hu, hc, _, _, _, hf⟩ := builder_split_invariance w hw c V hV hlog hlen ps hps
  refine ⟨st, hu, ?_⟩
  rw [hf]
  by_cases h0 : c.len = 0
  · have hn : c.n = 0 := by unfold BCfg.n groups; rw [h0]; simp
    simp [h0, build, mainPhase, finish, hn, BCfg.c0]
  · have hn : 1 ≤ c.n := by
      unfold BCfg.n
      have := (lt_groups_iff c.len c.log 0).2 (by omega)
      omega
    rw [if_neg h0]
    by_cases h1 : c.n = 1
    · have := builder_correct_one c.H (gb V (groupLen c.log)) c.c0
      rw [h1]
      exact congrArg Except.ok (by simpa using this.2.2)
    · have := builder_correct c.H (gb V (groupLen c.log)) c.n c.c0 (by omega)
      exact congrArg Except.ok this.1

/-! ## The arithmetic of the group-level steps -/

/-- The merge step `complete_group` runs, written with the `u64` operations of the code: `2 * rs` and
`done - 2 * rs`. `none` outside is an overflow or an underflow; the inner `none` ends the loop. -/
def mergeTopM (H : Hash Cv Bytes) (n k : Nat) (s : Pinc.Builder.BS Cv) : Option (Option (Pinc.Builder.BS Cv)) :=
  match s.stack with
  | (r, rs) :: (l, ls) :: rest =>
    if rs = ls then
      match Machine.mul 64 2 rs with
      | none => none
      | some two =>
        match Machine.sub 64 k two with
        | none => none
        | some lo => some (some (s.write H n lo k l r rest two))
    else some none
  | _ => some none

/-- The merge step of the finish loop: `ls + rs` and `n - (ls + rs)`. -/
def finishTopM (H : Hash Cv Bytes) (n : Nat) (s : Pinc.Builder.BS Cv) : Option (Option (Pinc.Builder.BS Cv)) :=
  match s.stack with
  | (r, rs) :: (l, ls) :: rest =>
    match Machine.add 64 ls rs with
    | none => none
    | some size =>
      match Machine.sub 64 n size with
      | none => none
      | some lo => some (some (s.write H n lo n l r rest size))
  | _ => some none

theorem mergeTopM_eq (H : Hash Cv Bytes) (data : Nat → Bytes) (n k : Nat) (s : Pinc.Builder.BS Cv) (hk : k ≤ n)
    (hn : n ≤ 2 ^ 54) (hT : Top H data n k s.stack) : mergeTopM H n k s = some (mergeTop H n k s) := by
  obtain ⟨cv, s0, k', rest0, heq, hdec, hp2, hdvd, hle, hkk, hcv⟩ := hT
  have e54 : (2 : Nat) ^ 54 < 2 ^ 64 := by decide
  unfold mergeTopM mergeTop
  rw [heq]
  rcases rest0 with _ | ⟨⟨l, ls⟩, rest⟩
  · rfl
  · have htop := hdec.top_le
    simp only [topSize] at htop
    by_cases hq : s0 = ls
    · subst hq
      have h1 : Machine.mul 64 2 s0 = some (2 * s0) := by simp only [Machine.mul]; rw [if_pos (by omega)]
      have h2 : Machine.sub 64 k (2 * s0) = some (k - 2 * s0) := by simp only [Machine.sub]; rw [if_pos (by omega)]
      simp [h1, h2]
    · simp [hq]

theorem finishTopM_eq (H : Hash Cv Bytes) (data : Nat → Bytes) (n : Nat) (c0 : Cv) (s : Pinc.Builder.BS Cv)
    (hn : n ≤ 2 ^ 54) (hF : FinInv H data n c0 s) : finishTopM H n s = some (finishTop H n s) := by
  obtain ⟨_, cv, S, st2, hst, hdec, _, hS0, hSn, _⟩ := hF
  have e54 : (2 : Nat) ^ 54 < 2 ^ 64 := by decide
  unfold finishTopM finishTop
  rw [hst]
  rcases st2 with _ | ⟨⟨l, ls⟩, rest⟩
  · rfl
  · have htop := hdec.top_le
    simp only [topSize] at htop
    have h1 : Machine.add 64 ls S = some (ls + S) := by simp only [Machine.add]; rw [if_pos (by omega)]
    have h2 : Machine.sub 64 n (ls + S) = some (n - (ls + S)) := by simp only [Machine.sub]; rw [if_pos (by omega)]
    simp [h1, h2]

/-- Every iteration of the merge loop is free of overflow and underflow. -/
def MergeSafe (H : Hash Cv Bytes) (n k : Nat) : Nat → Pinc.Builder.BS Cv → Prop
  | 0, _ => True
  | f + 1, s => mergeTopM H n k s = some (mergeTop H n k s) ∧ ∀ s1, mergeTop H n k s = some s1 → MergeSafe H n k f s1

theorem merge_safe (H : Hash Cv Bytes) (data : Nat → Bytes) (n k : Nat) (c0 : Cv) (hk : k ≤ n) (hn : n ≤ 2 ^ 54) :
    ∀ (f : Nat) (s : Pinc.Builder.BS Cv), s.stack.length ≤ f → Top H data n k s.stack → WInv H data n k c0 s →
      MergeSafe H n k f s := by
  intro f
  induction f with
  | zero => intro _ _ _ _; trivial
  | succ f ih =>
    intro s hl hT hI
    refine ⟨mergeTopM_eq H data n k s hk hn hT, fun s1 hm => ?_⟩
    obtain ⟨h1, h2, h3⟩ := mergeTop_some H data n k c0 hk s s1 hm hT hI
    exact ih s1 (by omega) h1 h2

/-- Every iteration of the finish loop is free of overflow and underflow. -/
def FinSafe (H : Hash Cv Bytes) (n : Nat) : Nat → Pinc.Builder.BS Cv → Prop
  | 0, _ => True
  | f + 1, s => finishTopM H n s = some (finishTop H n s) ∧ ∀ s1, finishTop H n s = some s1 → FinSafe H n f s1

theorem finish_safe (H : Hash Cv Bytes) (data : Nat → Bytes) (n : Nat) (c0 : Cv) (hn : n ≤ 2 ^ 54) :
    ∀ (f : Nat) (s : Pinc.Builder.BS Cv), s.stack.length ≤ f → FinInv H data n c0 s → FinSafe H n f s := by
  intro f
  induction f with
  | zero => intro _ _ _; trivial
  | succ f ih =>
    intro s hl hF
    refine ⟨finishTopM_eq H data n c0 s hn hF, fun s1 hm => ?_⟩
    obtain ⟨h1, h2⟩ := finishTop_some H data n c0 s s1 hm hF
    exact ih s1 (by omega) h1

/-- Every `u64` operation of the group-level loops of the builder succeeds: in each of the `n` group steps,
every iteration of the merge loop (`2 * rs` and `done - 2 * rs`), and in the finish loop every iteration
(`ls + rs` and `n - (ls + rs)`), for a tree of `2 <= n <= 2^54` groups, which every value of at most
`u64::MAX` bytes has (`Layout.groups_le`). -/
theorem builder_arith (H : Hash Cv Bytes) (data : Nat → Bytes) (n : Nat) (c0 : Cv) (hn : 2 ≤ n) (hn54 : n ≤ 2 ^ 54) :
    (∀ k, 1 ≤ k → k ≤ n →
      MergeSafe H n k ((mainPhase H data n c0 (k - 1)).stack.length + 1)
        { (mainPhase H data n c0 (k - 1)) with
          stack := (H.leaf (isRoot n (k - 1) k) (k - 1) (data (k - 1)), 1) :: (mainPhase H data n c0 (k - 1)).stack }) ∧
    FinSafe H n (mainPhase H data n c0 n).stack.length (mainPhase H data n c0 n) := by
  refine ⟨?_, ?_⟩
  · intro k hk1 hk
    obtain ⟨hD, hI⟩ := mainPhase_inv H data n c0 hn (k - 1) (by omega)
    refine merge_safe H data n k c0 hk hn54 _ _ (Nat.le_refl _) ?_ ?_
    · refine ⟨_, 1, k - 1, (mainPhase H data n c0 (k - 1)).stack, rfl, hD, ⟨0, rfl⟩, Nat.one_dvd _, ?_, by omega, ?_⟩
      · intro c t ht
        cases hst : (mainPhase H data n c0 (k - 1)).stack with
        | nil => rw [hst] at ht; simp at ht
        | cons e rest =>
          obtain ⟨c', t'⟩ := e
          rw [hst] at ht hD
          simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          obtain ⟨b, hb⟩ := hD.head_pow2
          rw [hb]; exact Nat.two_pow_pos b
      · rw [gcv_leaf H data n _ _ (by omega)]
    · obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hD hI ⊢
      have hmul : (k0 + 1) * (n + 1) = k0 * (n + 1) + (n + 1) := by rw [Nat.succ_mul]
      have htop := hD.top_le
      refine ⟨?_, hI.sorted, ?_, ?_, hI.root⟩
      · intro w hw
        have := hI.good w hw
        exact ⟨this.1, by omega⟩
      · intro w hw
        have := hI.bound w hw
        simp only [topSize]
        omega
      · have := hI.count
        simp only [List.length_cons]
        omega
  · obtain ⟨hD, hI⟩ := mainPhase_inv H data n c0 hn n (Nat.le_refl _)
    refine finish_safe H data n c0 hn54 _ _ (Nat.le_refl _) ?_
    refine ⟨hI, ?_⟩
    obtain ⟨K, hK⟩ : ∃ K, K = n := ⟨n, rfl⟩
    have hD2 : Dec H data n K (mainPhase H data n c0 n).stack := by rw [hK]; exact hD
    rcases hst : (mainPhase H data n c0 n).stack with _ | ⟨⟨cv, S⟩, st2⟩
    · rw [hst] at hD2; have := hD2.nil_k; omega
    · rw [hst] at hD2
      cases hD2 with
      | @cons k' _ _ _ _ hd2 hp2 hdvd hlt hk2 hcv' =>
        refine ⟨cv, S, st2, rfl, ?_, ?_, ?_, ?_, hlt⟩
        · rw [show n - S = k' by omega]; exact hd2
        · rw [show n - S = k' by omega, hcv', hK]
        · obtain ⟨a, ha⟩ := hp2; rw [ha]; exact Nat.two_pow_pos a
        · omega

/-- `parent`'s slot: `preorder_index * 64`, narrowed to a `w`-bit `usize`, then the range `a .. a + 64` of the
buffer of `olen` bytes. For a parent node of a tree of at most `2^54` groups, with the buffer the layout
requires, this finds the slot: no overflow, no truncation, no `OutboardSize`. -/
def slotM (il : Nat → Nat) (w olen n lo hi : Nat) : Option Nat :=
  match preorderIndexM il n lo hi with
  | none => none
  | some idx =>
    match Machine.mul 64 idx 64 with
    | none => none
    | some at' =>
      match tryFrom w at' with
      | none => none
      | some a =>
        match Machine.add w a 64 with
        | none => none
        | some e => if e ≤ olen then some a else none

theorem slotM_eq (il : Nat → Nat) (hil : ∀ x, 0 < x → x < 2 ^ 64 → IsIlog2 x (il x)) (w : Nat)
    (olen n lo hi : Nat) (hn : n ≤ 2 ^ 54) (hs : Sub 0 n lo hi) (hp : hi - lo ≥ 2) (ho : olen = 64 * (n - 1))
    (hw : olen < 2 ^ w) : slotM il w olen n lo hi = some (64 * preorderIndex n lo hi) := by
  have e54 : (2 : Nat) ^ 54 < 2 ^ 64 := by decide
  obtain ⟨h1, h2⟩ := preorderOffset_lt n lo hi hn hs hp
  have h3 : preorderIndex n lo hi * 64 < 2 ^ 64 := by omega
  have h4 : 64 * preorderIndex n lo hi < 2 ^ w := by omega
  have h5 : 64 * preorderIndex n lo hi + 64 < 2 ^ w := by omega
  have h6 : 64 * preorderIndex n lo hi ≤ olen := by omega
  have h7 : 64 * preorderIndex n lo hi + 64 ≤ olen := by omega
  have e64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have h3' : 64 * preorderIndex n lo hi < 18446744073709551616 := by omega
  simp [slotM, preorderIndexM_eq il hil n lo hi hn, Machine.mul, tryFrom, Nat.mul_comm (preorderIndex n lo hi) 64,
    h4, Machine.add, h5, h6, h7, h3, h3']

end

end Pinc.BuilderBytes

#audit_axioms Pinc.BuilderBytes.builder_split_invariance
#audit_axioms Pinc.BuilderBytes.finish_errors
#audit_axioms Pinc.BuilderBytes.update_errors
#audit_axioms Pinc.BuilderBytes.builder_empty
#audit_axioms Pinc.BuilderBytes.builder_split_root
#audit_axioms Pinc.BuilderBytes.mergeTopM_eq
#audit_axioms Pinc.BuilderBytes.finishTopM_eq
#audit_axioms Pinc.BuilderBytes.slotM_eq
#audit_axioms Pinc.BuilderBytes.builder_arith
#audit_axioms Pinc.BuilderBytes.updStep_inv
#audit_axioms Pinc.BuilderBytes.updLoop_inv
#audit_axioms Pinc.BuilderBytes.update_ok
#audit_axioms Pinc.BuilderBytes.merge_safe
#audit_axioms Pinc.BuilderBytes.finish_safe
