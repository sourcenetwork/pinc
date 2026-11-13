import Vinc.Axioms

/-!
# The bundle layout (`vinc-dtn/src/layout.rs`)

`SliceLayout` on natural numbers with the machine rule of `u64`: `new` computes the sealed length with checked
operations, and every other accessor is plain arithmetic in the code, so the theorems below show that once `new`
succeeded no accessor can overflow (`all_fit`), that each equals its exact definition (`data_spec`, `blocks_spec`,
`blockK_spec`, `total_spec`), that the padding is below one slice (`padding_lt`), that `locate` is a bijection between
symbol numbers below `totalSyms` and positions (`locate_iff`, `locate_block_start`), that `dataSymbol` is the inverse
position of the data slices (`dataSymbol_locate`), and that `byteRange` refuses exactly a reversed range and a range
past the last symbol (`byteRange_spec`). The numbers are unbounded naturals, so the statements hold for every
parameter, not a checked domain. `chunk = 1024` is `vinc_dag::tree::CHUNK_LEN`.
-/

namespace Vinc.DtnLayout

/-- `2^64`: the `u64` values are the naturals below it. -/
def M : Nat := 18446744073709551616
def chunk : Nat := 1024
def tagLen : Nat := 16
def maxSymbols : Nat := 255
def maxSliceLog : Nat := 4

theorem M_def : M = 18446744073709551616 := rfl

/-- `u64::checked_mul`. -/
def cmul (a b : Nat) : Option Nat := if a * b < M then some (a * b) else none
/-- `u64::checked_add`. -/
def cadd (a b : Nat) : Option Nat := if a + b < M then some (a + b) else none
/-- `u64::saturating_mul`. -/
def smul (a b : Nat) : Nat := if a * b < M then a * b else M - 1
/-- `u64::div_ceil`, for a nonzero divisor. -/
def cdiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The parameters of a layout: `k`, `m`, `slice_log`, `payload_len`. -/
structure L where
  k : Nat
  m : Nat
  log : Nat
  p : Nat

def L.sliceLen (l : L) : Nat := chunk * 2 ^ l.log
def L.plainLen (l : L) : Nat := l.sliceLen - tagLen
def L.dataSyms (l : L) : Nat := cdiv l.p l.plainLen
def L.paddedLen (l : L) : Nat := l.dataSyms * l.plainLen
def L.blocks (l : L) : Nat := cdiv l.dataSyms l.k
def L.totalSyms (l : L) : Nat := l.dataSyms + l.blocks * l.m
def L.totalLen (l : L) : Nat := l.totalSyms * l.sliceLen

/-- `try_total_len`. -/
def L.tryTotal (l : L) : Option Nat :=
  (cmul (cdiv l.dataSyms l.k) l.m).bind fun parity =>
    (cadd l.dataSyms parity).bind fun s => cmul s l.sliceLen

/-- The validity test of `SliceLayout::new`. -/
def L.valid (l : L) : Bool :=
  decide (1 ≤ l.k ∧ l.k + l.m ≤ maxSymbols ∧ l.log ≤ maxSliceLog) && decide (l.p ≠ 0) && l.tryTotal.isSome

/-- `SliceLayout::new`. -/
def new (l : L) : Option L := if l.valid then some l else none

def L.blockK (l : L) (b : Nat) : Nat :=
  let d := l.dataSyms
  let first := smul b l.k
  if first ≥ d then 0 else if d - first < l.k then d - first else l.k
def L.blockN (l : L) (b : Nat) : Nat := if l.blockK b = 0 then 0 else l.blockK b + l.m
def L.blockStart (l : L) (b : Nat) : Nat := smul b (l.k + l.m)

structure Pos where
  block : Nat
  index : Nat
  blockK : Nat
  deriving DecidableEq

def Pos.isParity (p : Pos) : Bool := decide (p.index ≥ p.blockK)

def L.locate (l : L) (s : Nat) : Option Pos :=
  let pb := l.k + l.m
  let block := s / pb
  let index := s % pb
  let bk := l.blockK block
  if bk > 0 ∧ index < bk + l.m then some ⟨block, index, bk⟩ else none

def L.dataSymbol (l : L) (d : Nat) : Option Nat :=
  if d < l.dataSyms then some (l.blockStart (d / l.k) + d % l.k) else none

/-- `byte_range`: the byte range of symbols `[a, b)`, or `none` for the `Buffer` error. -/
def L.byteRange (l : L) (a b : Nat) : Option (Nat × Nat) :=
  if a > b ∨ b > l.totalSyms then none else some (a * l.sliceLen, b * l.sliceLen)

/-! ## Validity -/

theorem pred_mul (n k : Nat) (h : 0 < n) : n * k = (n - 1) * k + k := by
  cases n with
  | zero => omega
  | succ n => simp [Nat.succ_mul]

theorem sliceLen_pos (l : L) : 0 < l.sliceLen := by
  unfold L.sliceLen chunk; exact Nat.mul_pos (by decide) (Nat.two_pow_pos _)

theorem sliceLen_ge (l : L) : 1024 ≤ l.sliceLen := by
  unfold L.sliceLen chunk
  have : 1 ≤ 2 ^ l.log := Nat.one_le_two_pow
  omega

theorem plainLen_pos (l : L) : 0 < l.plainLen := by
  have := sliceLen_ge l; unfold L.plainLen tagLen; omega

theorem plain_lt_slice (l : L) : l.plainLen < l.sliceLen := by
  have := sliceLen_ge l; unfold L.plainLen tagLen; omega

theorem cdiv_spec (a b : Nat) (hb : 0 < b) : a ≤ cdiv a b * b ∧ (a = 0 ∨ (cdiv a b - 1) * b < a) := by
  unfold cdiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  generalize (a + b - 1) / b = q at *
  generalize (a + b - 1) % b = r at *
  have c : q * b = b * q := Nat.mul_comm _ _
  refine ⟨by omega, ?_⟩
  rcases Nat.eq_zero_or_pos a with h | h
  · exact Or.inl h
  · right
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; simp at h1; omega
    · have := pred_mul q b hq; omega

theorem cdiv_pos (a b : Nat) (hb : 0 < b) (ha : 0 < a) : 0 < cdiv a b := by
  have := (cdiv_spec a b hb).1
  rcases Nat.eq_zero_or_pos (cdiv a b) with h | h
  · rw [h] at this; omega
  · exact h

/-- The exact total of a layout, as a natural. -/
theorem tryTotal_eq (l : L) (hk : 0 < l.k) :
    l.tryTotal = if l.totalLen < M then some l.totalLen else none := by
  have hs := sliceLen_pos l
  unfold L.tryTotal cmul cadd L.totalLen L.totalSyms L.blocks
  generalize cdiv l.dataSyms l.k = B
  generalize l.dataSyms = d
  generalize l.sliceLen = S at *
  generalize l.m = m
  by_cases h3 : (d + B * m) * S < M
  · have h2 : d + B * m < M := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hs) h3
    have h1 : B * m < M := by omega
    simp [h1, h2, h3]
  · by_cases h1 : B * m < M <;> by_cases h2 : d + B * m < M <;> simp [h1, h2, h3]

theorem valid_iff (l : L) :
    l.valid = true ↔ (1 ≤ l.k ∧ l.k + l.m ≤ 255 ∧ l.log ≤ 4) ∧ l.p ≠ 0 ∧ l.totalLen < M := by
  unfold L.valid maxSymbols maxSliceLog
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨h1, h2, ?_⟩
    rw [tryTotal_eq l h1.1] at h3
    by_cases hh : l.totalLen < M
    · exact hh
    · simp [hh] at h3
  · rintro ⟨h1, h2, h3⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨h1, h2⟩, ?_⟩
    rw [tryTotal_eq l h1.1]; simp [h3]

/-! ## The counts -/

theorem data_spec (l : L) (hp : l.p ≠ 0) :
    0 < l.dataSyms ∧ (l.dataSyms - 1) * l.plainLen < l.p ∧ l.p ≤ l.dataSyms * l.plainLen := by
  have h := cdiv_spec l.p l.plainLen (plainLen_pos l)
  have hpos := cdiv_pos l.p l.plainLen (plainLen_pos l) (Nat.pos_of_ne_zero hp)
  refine ⟨hpos, ?_, h.1⟩
  rcases h.2 with h0 | h0
  · exact absurd h0 hp
  · exact h0

theorem blocks_spec (l : L) (hk : 0 < l.k) (hd : 0 < l.dataSyms) :
    0 < l.blocks ∧ (l.blocks - 1) * l.k < l.dataSyms ∧ l.dataSyms ≤ l.blocks * l.k := by
  have h := cdiv_spec l.dataSyms l.k hk
  have hpos := cdiv_pos l.dataSyms l.k hk hd
  refine ⟨hpos, ?_, h.1⟩
  rcases h.2 with h0 | h0
  · omega
  · exact h0

/-- Padding is under one slice and the padded length is exactly the data slices. -/
theorem padding_lt (l : L) (hp : l.p ≠ 0) : l.p ≤ l.paddedLen ∧ l.paddedLen - l.p < l.plainLen := by
  have ⟨hd, h1, h2⟩ := data_spec l hp
  have := pred_mul l.dataSyms l.plainLen hd
  unfold L.paddedLen
  omega

theorem total_spec (l : L) :
    l.totalSyms = l.dataSyms + l.blocks * l.m ∧ l.totalLen = l.totalSyms * l.sliceLen := ⟨rfl, rfl⟩

/-- Once `new` succeeded, no accessor overflows: the padded length, the symbol count and the total length are all
below `2^64`, and so are the data and parity counts. -/
theorem all_fit (l : L) (h : l.valid = true) :
    l.dataSyms < M ∧ l.paddedLen < M ∧ l.blocks * l.m < M ∧ l.totalSyms < M ∧ l.totalLen < M ∧
      l.dataSyms * l.sliceLen < M := by
  obtain ⟨⟨hk, _, _⟩, hp, ht⟩ := (valid_iff l).1 h
  have hM := M_def
  have hs := sliceLen_pos l
  have hd := (data_spec l hp).1
  have e1 : l.totalSyms ≤ l.totalLen := by
    unfold L.totalLen; exact Nat.le_mul_of_pos_right _ hs
  have e2 : l.dataSyms ≤ l.totalSyms := by unfold L.totalSyms; omega
  have e3 : l.blocks * l.m ≤ l.totalSyms := by unfold L.totalSyms; omega
  have e4 : l.paddedLen ≤ l.dataSyms * l.sliceLen := by
    unfold L.paddedLen; exact Nat.mul_le_mul_left _ (Nat.le_of_lt (plain_lt_slice l))
  have e5 : l.dataSyms * l.sliceLen ≤ l.totalLen := by
    unfold L.totalLen; exact Nat.mul_le_mul_right _ e2
  refine ⟨?_, ?_, ?_, ?_, ht, ?_⟩ <;> omega

theorem sliceLen_value (l : L) (h : l.valid = true) : l.sliceLen ∈ [1024, 2048, 4096, 8192, 16384] := by
  obtain ⟨⟨_, _, hl⟩, _, _⟩ := (valid_iff l).1 h
  unfold L.sliceLen chunk
  have : l.log = 0 ∨ l.log = 1 ∨ l.log = 2 ∨ l.log = 3 ∨ l.log = 4 := by omega
  rcases this with h | h | h | h | h <;> simp [h]

/-! ## Blocks -/

theorem blockK_spec (l : L) (h : l.valid = true) (b : Nat) :
    (b + 1 < l.blocks → l.blockK b = l.k) ∧
    (b + 1 = l.blocks → l.blockK b = l.dataSyms - (l.blocks - 1) * l.k) ∧
    (l.blocks ≤ b → l.blockK b = 0) := by
  obtain ⟨⟨hk, _, _⟩, hp, ht⟩ := (valid_iff l).1 h
  have hM := M_def
  have ⟨hd, _, _⟩ := data_spec l hp
  have ⟨hB, hB1, hB2⟩ := blocks_spec l (by omega) hd
  have hfit := (all_fit l h).1
  have key : ∀ b, b < l.blocks → smul b l.k = b * l.k := by
    intro b hb
    unfold smul
    have : b * l.k ≤ (l.blocks - 1) * l.k := Nat.mul_le_mul_right _ (by omega)
    have : b * l.k < M := by omega
    simp [this]
  refine ⟨?_, ?_, ?_⟩
  · intro hb
    have e : smul b l.k = b * l.k := key b (by omega)
    have h1 : (b + 1) * l.k ≤ (l.blocks - 1) * l.k := Nat.mul_le_mul_right _ (by omega)
    have h2 : (b + 1) * l.k = b * l.k + l.k := by rw [Nat.add_mul, Nat.one_mul]
    unfold L.blockK; simp only [e]
    split <;> (try split) <;> omega
  · intro hb
    have e : smul b l.k = b * l.k := key b (by omega)
    have : b = l.blocks - 1 := by omega
    subst this
    have h2 : l.blocks * l.k = (l.blocks - 1) * l.k + l.k := pred_mul _ _ hB
    unfold L.blockK; simp only [e]
    split <;> (try split) <;> omega
  · intro hb
    have h3 : l.dataSyms ≤ b * l.k := Nat.le_trans hB2 (Nat.mul_le_mul_right _ hb)
    unfold L.blockK
    by_cases hm : b * l.k < M
    · have e : smul b l.k = b * l.k := by simp [smul, hm]
      simp only [e]
      split <;> (try split) <;> omega
    · have e : smul b l.k = M - 1 := by simp [smul, hm]
      simp only [e]
      split <;> (try split) <;> omega

theorem blockK_le (l : L) (h : l.valid = true) (b : Nat) (hb : b < l.blocks) :
    0 < l.blockK b ∧ l.blockK b ≤ l.k := by
  obtain ⟨⟨hk, _, _⟩, hp, ht⟩ := (valid_iff l).1 h
  have hM := M_def
  have ⟨hd, _, _⟩ := data_spec l hp
  have ⟨hB, hB1, hB2⟩ := blocks_spec l (by omega) hd
  have s := blockK_spec l h b
  by_cases h1 : b + 1 < l.blocks
  · rw [s.1 h1]; omega
  · have := s.2.1 (by omega)
    have := pred_mul l.blocks l.k hB
    rw [‹l.blockK b = _›]; omega

theorem blockN_spec (l : L) (h : l.valid = true) (b : Nat) :
    (b < l.blocks → l.blockN b = l.blockK b + l.m) ∧ (l.blocks ≤ b → l.blockN b = 0) := by
  constructor
  · intro hb
    have := (blockK_le l h b hb).1
    unfold L.blockN; simp; omega
  · intro hb
    unfold L.blockN; simp [(blockK_spec l h b).2.2 hb]

/-- Symbols per block: the block start is `b * (k + m)` for every block of the bundle. -/
theorem blockStart_spec (l : L) (h : l.valid = true) (b : Nat) (hb : b ≤ l.blocks) :
    l.blockStart b = b * (l.k + l.m) := by
  have hfit := (all_fit l h).2.2.2.1
  obtain ⟨⟨hk, hkm, _⟩, hp, ht⟩ := (valid_iff l).1 h
  have hM := M_def
  have ⟨hd, _, _⟩ := data_spec l hp
  have ⟨hB, hB1, hB2⟩ := blocks_spec l (by omega) hd
  have : b * (l.k + l.m) ≤ l.blocks * (l.k + l.m) := Nat.mul_le_mul_right _ hb
  have : l.blocks * (l.k + l.m) = l.blocks * l.k + l.blocks * l.m := Nat.mul_add _ _ _
  have : l.totalSyms = l.dataSyms + l.blocks * l.m := rfl
  have : l.blocks * l.k < l.dataSyms + l.k := by
    have : l.blocks * l.k = (l.blocks - 1) * l.k + l.k := pred_mul _ _ hB
    omega
  have hfit2 : l.blocks * (l.k + l.m) < M + 255 := by omega
  unfold L.blockStart smul
  by_cases hh : b * (l.k + l.m) < M
  · simp [hh]
  · exfalso
    -- b <= blocks and blocks * (k + m) = blocks*k + blocks*m <= totalSyms + k, and totalSyms * 1024 < M
    have hs := sliceLen_ge l
    have : l.totalSyms * 1024 ≤ l.totalLen := Nat.mul_le_mul_left _ hs
    omega

/-- The block start plus the block size is the next block start, and the last block ends at `totalSyms`. -/
theorem blocks_cover (l : L) (h : l.valid = true) :
    ∀ b, b + 1 < l.blocks → l.blockStart b + l.blockN b = l.blockStart (b + 1) := by
  intro b hb
  rw [blockStart_spec l h b (by omega), blockStart_spec l h (b + 1) (by omega),
    (blockN_spec l h b).1 (by omega), (blockK_spec l h b).1 hb]
  rw [Nat.add_mul, Nat.one_mul]

theorem last_block_end (l : L) (h : l.valid = true) :
    l.blockStart (l.blocks - 1) + l.blockN (l.blocks - 1) = l.totalSyms := by
  obtain ⟨⟨hk, _, _⟩, hp, ht⟩ := (valid_iff l).1 h
  have hM := M_def
  have ⟨hd, _, _⟩ := data_spec l hp
  have ⟨hB, hB1, hB2⟩ := blocks_spec l (by omega) hd
  rw [blockStart_spec l h _ (by omega), (blockN_spec l h _).1 (by omega),
    (blockK_spec l h _).2.1 (by omega)]
  unfold L.totalSyms
  have : l.blocks * l.m = (l.blocks - 1) * l.m + l.m := pred_mul _ _ hB
  have : (l.blocks - 1) * (l.k + l.m) = (l.blocks - 1) * l.k + (l.blocks - 1) * l.m := Nat.mul_add _ _ _
  have : l.dataSyms - (l.blocks - 1) * l.k + (l.blocks - 1) * l.k = l.dataSyms := by omega
  omega

/-! ## locate -/

theorem locate_def (l : L) (s : Nat) :
    l.locate s = (if l.blockK (s / (l.k + l.m)) > 0 ∧ s % (l.k + l.m) < l.blockK (s / (l.k + l.m)) + l.m then
      some ⟨s / (l.k + l.m), s % (l.k + l.m), l.blockK (s / (l.k + l.m))⟩ else none) := rfl

theorem locate_iff (l : L) (h : l.valid = true) (s : Nat) :
    (l.locate s).isSome = true ↔ s < l.totalSyms := by
  obtain ⟨⟨hk, hkm, _⟩, hp, ht⟩ := (valid_iff l).1 h
  have hM := M_def
  have ⟨hd, _, _⟩ := data_spec l hp
  have ⟨hB, hB1, hB2⟩ := blocks_spec l (by omega) hd
  have hpb : 0 < l.k + l.m := by omega
  have hdm : (l.k + l.m) * (s / (l.k + l.m)) + s % (l.k + l.m) = s := Nat.div_add_mod _ _
  have hlt : s % (l.k + l.m) < l.k + l.m := Nat.mod_lt _ hpb
  have hend := last_block_end l h
  have hbs := blockStart_spec l h (l.blocks - 1) (by omega)
  have hnl := (blockN_spec l h (l.blocks - 1)).1 (by omega)
  have hkl := (blockK_spec l h (l.blocks - 1)).2.1 (by omega)
  have hkle := blockK_le l h (l.blocks - 1) (by omega)
  have hB' := pred_mul l.blocks (l.k + l.m) hB
  rw [locate_def]
  generalize s / (l.k + l.m) = q at hdm ⊢
  generalize s % (l.k + l.m) = r at hdm hlt ⊢
  have c1 : (l.k + l.m) * q = q * (l.k + l.m) := Nat.mul_comm _ _
  have A : (l.blockK q > 0 ∧ r < l.blockK q + l.m) ↔ s < l.totalSyms := by
    by_cases hq1 : q + 1 < l.blocks
    · have e := (blockK_spec l h q).1 hq1
      have hbc : (q + 1) * (l.k + l.m) ≤ (l.blocks - 1) * (l.k + l.m) := Nat.mul_le_mul_right _ (by omega)
      have c2 : (q + 1) * (l.k + l.m) = q * (l.k + l.m) + (l.k + l.m) := by rw [Nat.add_mul, Nat.one_mul]
      rw [e]
      constructor <;> intro hh <;> omega
    · by_cases hq2 : q + 1 = l.blocks
      · have e := (blockK_spec l h q).2.1 hq2
        have : q = l.blocks - 1 := by omega
        subst this
        rw [e]
        constructor <;> intro hh <;> omega
      · have e := (blockK_spec l h q).2.2 (by omega)
        have hbc : l.blocks * (l.k + l.m) ≤ q * (l.k + l.m) := Nat.mul_le_mul_right _ (by omega)
        rw [e]
        constructor <;> intro hh <;> omega
  by_cases hc : l.blockK q > 0 ∧ r < l.blockK q + l.m
  · simp only [hc, and_self, if_true, Option.isSome_some, true_iff]; exact A.1 hc
  · simp only [hc, ite_false, Option.isSome_none]
    constructor
    · intro hh; simp at hh
    · intro hh; exact absurd (A.2 hh) hc

/-- `locate` returns the block and index with `block * (k + m) + index = s`, the index inside the block, and the
parity flag of the index. -/
theorem locate_spec (l : L) (h : l.valid = true) (s : Nat) (pos : Pos) (hl : l.locate s = some pos) :
    pos.block * (l.k + l.m) + pos.index = s ∧ pos.block < l.blocks ∧ pos.blockK = l.blockK pos.block ∧
      pos.index < l.blockN pos.block ∧ (pos.isParity = true ↔ l.blockK pos.block ≤ pos.index) := by
  rw [locate_def] at hl
  split at hl
  · rename_i hc
    cases hl
    obtain ⟨⟨hk, hkm, _⟩, hp, ht⟩ := (valid_iff l).1 h
    have hM := M_def
    have ⟨hd, _, _⟩ := data_spec l hp
    have ⟨hB, hB1, hB2⟩ := blocks_spec l (by omega) hd
    have hpb : 0 < l.k + l.m := by omega
    have hdm := Nat.div_add_mod s (l.k + l.m)
    have hbk : l.blockK (s / (l.k + l.m)) > 0 := hc.1
    refine ⟨?_, ?_, rfl, ?_, ?_⟩
    · simp only; rw [Nat.mul_comm]; exact hdm
    · refine Nat.lt_of_not_le fun hn => ?_
      have := (blockK_spec l h (s / (l.k + l.m))).2.2 hn
      omega
    · simp only
      have hne : ¬ l.blockK (s / (l.k + l.m)) = 0 := by omega
      unfold L.blockN; simp only [hne, ite_false]; exact hc.2
    · simp [Pos.isParity]
  · simp at hl

/-- Distinct symbols have distinct positions. -/
theorem locate_inj (l : L) (h : l.valid = true) (s t : Nat) (pos : Pos)
    (hs : l.locate s = some pos) (ht : l.locate t = some pos) : s = t := by
  have a := (locate_spec l h s pos hs).1
  have b := (locate_spec l h t pos ht).1
  omega

theorem locate_block_start (l : L) (h : l.valid = true) (b : Nat) (hb : b < l.blocks) :
    ∃ pos, l.locate (b * (l.k + l.m)) = some pos ∧ pos.block = b ∧ pos.index = 0 ∧ pos.isParity = false := by
  obtain ⟨⟨hk, hkm, _⟩, _, _⟩ := (valid_iff l).1 h
  have hpb : 0 < l.k + l.m := by omega
  have hk := blockK_le l h b hb
  have hdiv : b * (l.k + l.m) / (l.k + l.m) = b := Nat.mul_div_cancel _ hpb
  have hmod : b * (l.k + l.m) % (l.k + l.m) = 0 := Nat.mul_mod_left _ _
  refine ⟨⟨b, 0, l.blockK b⟩, ?_, rfl, rfl, ?_⟩
  · rw [locate_def, hdiv, hmod]
    have : l.blockK b > 0 ∧ 0 < l.blockK b + l.m := ⟨hk.1, by omega⟩
    simp only [this, and_self, ite_true]
  · simp [Pos.isParity]; omega

/-- `data_symbol d` is the symbol of data slice `d`, and `locate` of it is the data position `(d / k, d % k)`. -/
theorem dataSymbol_locate (l : L) (h : l.valid = true) (d : Nat) (hd : d < l.dataSyms) :
    ∃ s, l.dataSymbol d = some s ∧ ∃ pos, l.locate s = some pos ∧ pos.block = d / l.k ∧ pos.index = d % l.k ∧
      pos.isParity = false := by
  obtain ⟨⟨hk, hkm, _⟩, hp, ht⟩ := (valid_iff l).1 h
  have hM := M_def
  have ⟨hd0, _, _⟩ := data_spec l hp
  have ⟨hB, hB1, hB2⟩ := blocks_spec l (by omega) hd0
  have hkpos : 0 < l.k := by omega
  have hq : d / l.k < l.blocks := by
    rw [Nat.div_lt_iff_lt_mul hkpos]; omega
  have hr := Nat.mod_lt d hkpos
  have hbs := blockStart_spec l h (d / l.k) (by omega)
  have hpb : 0 < l.k + l.m := by omega
  have hdm := Nat.div_add_mod d l.k
  have hbk : d % l.k < l.blockK (d / l.k) := by
    by_cases h1 : d / l.k + 1 < l.blocks
    · rw [(blockK_spec l h _).1 h1]; exact hr
    · have e := (blockK_spec l h (d / l.k)).2.1 (by omega)
      have hq' : d / l.k = l.blocks - 1 := by omega
      rw [e]
      rw [hq'] at hdm
      have c : l.k * (l.blocks - 1) = (l.blocks - 1) * l.k := Nat.mul_comm _ _
      omega
  have hbkle := (blockK_le l h _ hq)
  refine ⟨l.blockStart (d / l.k) + d % l.k, by simp [L.dataSymbol, hd], ?_⟩
  have hmod : (d / l.k * (l.k + l.m) + d % l.k) / (l.k + l.m) = d / l.k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpb, Nat.div_eq_of_lt (by omega)]; simp
  have hmod2 : (d / l.k * (l.k + l.m) + d % l.k) % (l.k + l.m) = d % l.k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨⟨d / l.k, d % l.k, l.blockK (d / l.k)⟩, ?_, rfl, rfl, ?_⟩
  · rw [locate_def, hbs, hmod, hmod2]
    have : l.blockK (d / l.k) > 0 ∧ d % l.k < l.blockK (d / l.k) + l.m := ⟨hbkle.1, by omega⟩
    simp only [this, and_self, ite_true]
  · simp [Pos.isParity]; omega

theorem dataSymbol_none (l : L) (d : Nat) (hd : l.dataSyms ≤ d) : l.dataSymbol d = none := by
  unfold L.dataSymbol; simp; omega

/-! ## byte_range -/

theorem byteRange_spec (l : L) (a b : Nat) :
    l.byteRange a b = none ↔ (a > b ∨ b > l.totalSyms) := by
  unfold L.byteRange; split <;> simp_all

theorem byteRange_fits (l : L) (h : l.valid = true) (a b : Nat) (r : Nat × Nat) (hr : l.byteRange a b = some r) :
    r = (a * l.sliceLen, b * l.sliceLen) ∧ r.1 ≤ r.2 ∧ r.2 ≤ l.totalLen ∧ r.2 < M := by
  unfold L.byteRange at hr
  split at hr
  · simp at hr
  · rename_i hc
    cases hr
    have hb : b ≤ l.totalSyms := by omega
    have hab : a ≤ b := by omega
    have := (all_fit l h).2.2.2.2.1
    refine ⟨rfl, Nat.mul_le_mul_right _ hab, Nat.mul_le_mul_right _ hb, ?_⟩
    have : b * l.sliceLen ≤ l.totalLen := Nat.mul_le_mul_right _ hb
    omega

/-- `new` accepts exactly the layouts with `k >= 1`, `k + m <= 255`, `slice_log <= 4`, a nonempty payload and a sealed
length that fits `u64`. -/
theorem new_iff (l : L) :
    (new l).isSome = true ↔ (1 ≤ l.k ∧ l.k + l.m ≤ 255 ∧ l.log ≤ 4) ∧ l.p ≠ 0 ∧ l.totalLen < M := by
  unfold new; rw [← valid_iff]; split <;> simp_all

#print axioms new_iff
#print axioms all_fit
#print axioms blockK_spec
#print axioms locate_iff
#print axioms locate_spec
#print axioms dataSymbol_locate
#print axioms padding_lt
#print axioms byteRange_fits

end Vinc.DtnLayout
