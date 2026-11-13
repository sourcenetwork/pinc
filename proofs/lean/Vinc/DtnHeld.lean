/-!
# The per-block held set of a reception

The story. A receiver records which symbols of a bundle it holds in `vinc-dtn/src/held.rs` `BlockHeld`: one bit per
symbol, and one count per erasure block, so it can tell at once whether a block holds the `k` symbols it needs to
be rebuilt. Blocks are `per = k + m` symbols each (block `b` is symbols `b * per` to `b * per + per - 1`), and the
bundle has `total` symbols. The only change is `insert_symbol s`: a symbol past the bundle is refused, a symbol
already held changes nothing, and a new one sets its bit and adds one to the count of its block, `s / per`.

What must never happen: a count that differs from the number of held symbols of its block (the receiver would ask
for too much or too little, or finish a block that cannot be rebuilt), a count past `per` (the code keeps it in a
byte, and `per <= 255`), a held symbol that stops being held, or a bit past the end of the bundle.

`inv_empty` and `inv_insert` say the invariant `Inv` holds from the empty set and after every insert;
`count_le` bounds every count by `per`; `insert_new_count` says a new symbol adds exactly one to its block, which
stays at most `per` (so the code's saturating add never saturates); `insert_mono` and `insert_holds` say a symbol
once held stays held and an inserted symbol is held; `inv_insertAll` carries the invariant over a whole run of
inserts (one fed range); `decodable_iff` says the receiver's test `k <= count b` is the test on the bits.

The set also keeps a running total, `held`, of the symbols it holds, so `covered_len` is `held * g` with no walk
over the blocks: a new symbol adds one to it. `Inv` says `held` is the number of held symbols, and
`held_of_counts` says that summing the block counts, which is how `BlockHeld::new` starts the total from an earlier
set's buffer, gives that same number.
-/

namespace Vinc.DtnHeld

-- `upd bits s` is `bits` with symbol `s` set: what setting one bit does.
def upd (bits : Nat → Bool) (s : Nat) : Nat → Bool :=
  -- the symbol `s` reads as held, every other symbol as before
  fun x => if x = s then true else bits x

-- `cnt bits base n` is how many of the `n` symbols from `base` on are held: the count a block should have.
def cnt (bits : Nat → Bool) (base : Nat) : Nat → Nat
  -- no symbols: none held
  | 0 => 0
  -- the first `n`, then symbol `base + n` if it is held
  | n + 1 => cnt bits base n + (if bits (base + n) = true then 1 else 0)

/-- A run of `n` symbols holds at most `n` of them. -/
theorem cnt_le (bits : Nat → Bool) (base : Nat) : ∀ n, cnt bits base n ≤ n
  -- the empty run holds none
  | 0 => by simp [cnt]
  -- one more symbol adds at most one
  | n + 1 => by
    simp only [cnt]
    have := cnt_le bits base n
    split <;> omega

/-- With no symbol held, every run counts zero. -/
theorem cnt_false (base : Nat) : ∀ n, cnt (fun _ => false) base n = 0
  -- the empty run
  | 0 => rfl
  -- every symbol reads as not held
  | n + 1 => by simp [cnt, cnt_false base n]

/-- Setting a symbol outside a run does not change the run's count. -/
theorem cnt_out (bits : Nat → Bool) (base s : Nat) :
    ∀ n, (s < base ∨ base + n ≤ s) → cnt (upd bits s) base n = cnt bits base n
  -- the empty run
  | 0, _ => rfl
  -- the last symbol of the run is not `s`, and the rest is outside too
  | n + 1, h => by
    simp only [cnt]
    rw [cnt_out bits base s n (by omega)]
    have hne : base + n ≠ s := by omega
    simp [upd, hne]

/-- Setting a symbol that was not held, inside a run, adds one to the run's count. -/
theorem cnt_in (bits : Nat → Bool) (base s : Nat) (hb : bits s = false) :
    ∀ n, base ≤ s → s < base + n → cnt (upd bits s) base n = cnt bits base n + 1
  -- an empty run contains no symbol
  | 0, _, h2 => by omega
  -- either `s` is the last symbol of the run or it is in the shorter run before it
  | n + 1, h1, h2 => by
    simp only [cnt]
    by_cases hs : base + n = s
    · -- `s` is the last: the run before it does not contain `s`, and `s` turns from not held to held
      rw [cnt_out bits base s n (Or.inr (by omega))]
      subst hs
      simp [upd, hb]
    · -- `s` is earlier: the shorter run gains one, the last symbol is unchanged
      rw [cnt_in bits base s hb n h1 (by omega)]
      have hne : base + n ≠ s := hs
      simp only [upd, hne, if_false]
      omega

-- The set: a bit per symbol and a count per block, as `BlockHeld` keeps them.
structure Held where
  -- whether each symbol is held
  bits : Nat → Bool
  -- the count of each block
  count : Nat → Nat
  -- the running total of held symbols
  held : Nat

-- The invariant: every block's count is the number of its held symbols, no symbol past the bundle is held, and the
-- running total is the number of held symbols.
def Inv (per total : Nat) (h : Held) : Prop :=
  -- the count of block `b` counts the `per` symbols from `b * per`
  (∀ b, h.count b = cnt h.bits (b * per) per) ∧
  -- symbols past the end of the bundle are never held
  (∀ s, total ≤ s → h.bits s = false) ∧
  -- the total counts the held symbols of the bundle, `0` to `total - 1`
  h.held = cnt h.bits 0 total

-- The empty set: nothing held, every count zero (the all-zero buffer), a total of zero.
def empty : Held := ⟨fun _ => false, fun _ => 0, 0⟩

-- `insert_symbol`: past the bundle, or already held, nothing changes; otherwise set the bit and count it in `s / per`.
def insert (per total : Nat) (h : Held) (s : Nat) : Held :=
  -- refused: past the last symbol
  if total ≤ s then h
  -- already held: nothing to do
  else if h.bits s = true then h
  -- new: its bit, one more in its block, and one more in the total
  else ⟨upd h.bits s, fun b => if b = s / per then h.count b + 1 else h.count b, h.held + 1⟩

/-- The empty set satisfies the invariant. -/
theorem inv_empty (per total : Nat) : Inv per total empty :=
  -- every count and the total are zero, and every run of the empty set counts zero; no bit is set anywhere
  ⟨fun b => (cnt_false (b * per) per).symm, fun _ _ => rfl, (cnt_false 0 total).symm⟩

/-- A symbol `s` lies in the run of its own block, `s / per`, and in no other block's run. -/
theorem in_block (per s b : Nat) (hp : 0 < per) :
    (b * per ≤ s ∧ s < b * per + per) ↔ b = s / per := by
  -- write `s` as `per * (s / per) + s % per` with `s % per < per`
  have hd := Nat.div_add_mod s per
  have hm := Nat.mod_lt s hp
  constructor
  · -- inside block `b`'s run: then `s / per` is `b`
    rintro ⟨h1, h2⟩
    have lo : b ≤ s / per := (Nat.le_div_iff_mul_le hp).2 h1
    have hi : s / per < b + 1 := (Nat.div_lt_iff_lt_mul hp).2 (by rw [Nat.add_mul, Nat.one_mul]; exact h2)
    omega
  · -- `b` is `s / per`: `s` is between `b * per` and `b * per + per`
    rintro rfl
    -- the same decomposition with the product written `s / per * per`, as in the goal
    have hd' : s / per * per + s % per = s := by rw [Nat.mul_comm]; exact hd
    constructor <;> omega

/-- Every insert keeps the invariant. -/
theorem inv_insert (per total : Nat) (hp : 0 < per) (h : Held) (s : Nat) (hi : Inv per total h) :
    Inv per total (insert per total h s) := by
  obtain ⟨hc, hz, hh⟩ := hi
  unfold insert
  -- refused or already held: the set is the same
  split
  · exact ⟨hc, hz, hh⟩
  split
  · exact ⟨hc, hz, hh⟩
  rename_i hlt hheld
  have hb : h.bits s = false := by simpa using hheld
  refine ⟨fun b => ?_, fun x hx => ?_, ?_⟩
  · -- the counts: the block of `s` gains one, as its run does; every other run does not contain `s`
    simp only
    by_cases hbs : b = s / per
    · rw [if_pos hbs, hc b, cnt_in h.bits (b * per) s hb per ((in_block per s b hp).2 hbs).1
        ((in_block per s b hp).2 hbs).2]
    · rw [if_neg hbs, hc b, cnt_out h.bits (b * per) s per (by
        -- inside block `b`'s run would make `b` the block of `s`
        have hout : ¬ (b * per ≤ s ∧ s < b * per + per) := fun hin => hbs ((in_block per s b hp).1 hin)
        omega)]
  · -- the bits past the bundle: `s` is inside the bundle, so they stay unset
    simp only [upd]
    have : x ≠ s := by omega
    simp [this, hz x hx]
  · -- the total: `s` was not held and lies inside the bundle, so the count of held symbols gains one, as the total
    show h.held + 1 = cnt (upd h.bits s) 0 total
    rw [cnt_in h.bits 0 s hb total (Nat.zero_le s) (by omega), hh]

/-- Under the invariant, no count is past `per`, so a byte holds it for `per <= 255`. -/
theorem count_le (per total : Nat) (h : Held) (hi : Inv per total h) (b : Nat) : h.count b ≤ per := by
  rw [hi.1 b]
  exact cnt_le _ _ _

/-- A new symbol inside the bundle adds exactly one to its block, and the block stays at most `per`: the code's
saturating add is a plain add. -/
theorem insert_new_count (per total : Nat) (hp : 0 < per) (h : Held) (s : Nat) (hi : Inv per total h)
    (hs : s < total) (hb : h.bits s = false) :
    (insert per total h s).count (s / per) = h.count (s / per) + 1 ∧ h.count (s / per) + 1 ≤ per := by
  have hnot : ¬ total ≤ s := by omega
  have hheld : ¬ h.bits s = true := by simp [hb]
  have hc := (inv_insert per total hp h s hi).1 (s / per)
  have hle := cnt_le (insert per total h s).bits (s / per * per) per
  refine ⟨by simp [insert, hnot, hheld], ?_⟩
  have : (insert per total h s).count (s / per) = h.count (s / per) + 1 := by simp [insert, hnot, hheld]
  omega

/-- A held symbol stays held after any insert. -/
theorem insert_mono (per total : Nat) (h : Held) (s x : Nat) (hx : h.bits x = true) :
    (insert per total h s).bits x = true := by
  unfold insert
  split
  · exact hx
  split
  · exact hx
  simp [upd, hx]

/-- An inserted symbol inside the bundle is held. -/
theorem insert_holds (per total : Nat) (h : Held) (s : Nat) (hs : s < total) :
    (insert per total h s).bits s = true := by
  unfold insert
  have hnot : ¬ total ≤ s := by omega
  simp only [hnot, if_false]
  split
  · assumption
  · simp [upd]

-- A fed range: insert every symbol of a list in turn.
def insertAll (per total : Nat) (h : Held) : List Nat → Held
  -- nothing more to insert
  | [] => h
  -- insert the first, then the rest
  | s :: rest => insertAll per total (insert per total h s) rest

/-- A whole fed range keeps the invariant. -/
theorem inv_insertAll (per total : Nat) (hp : 0 < per) :
    ∀ (l : List Nat) (h : Held), Inv per total h → Inv per total (insertAll per total h l)
  -- nothing inserted
  | [], _, hi => hi
  -- one insert keeps it, then the rest does
  | s :: rest, h, hi => inv_insertAll per total hp rest _ (inv_insert per total hp h s hi)

/-- The receiver's test that block `b` can be rebuilt, `k <= count b`, is the test on the held bits. -/
theorem decodable_iff (per total k b : Nat) (h : Held) (hi : Inv per total h) :
    k ≤ h.count b ↔ k ≤ cnt h.bits (b * per) per := by
  rw [hi.1 b]

/-- A run of `n + m` symbols holds what its first `n` hold plus what the `m` after them hold. -/
theorem cnt_add (bits : Nat → Bool) (base n : Nat) : ∀ m, cnt bits base (n + m) = cnt bits base n + cnt bits (base + n) m
  -- nothing after the first `n`
  | 0 => by simp [cnt]
  -- one more symbol at the end, counted on both sides at the same place, `base + n + m`
  | m + 1 => by
    show cnt bits base ((n + m) + 1) = _
    simp only [cnt]
    rw [cnt_add bits base n m, ← Nat.add_assoc base n m]
    omega

/-- A run that starts at or past the end of the bundle holds nothing. -/
theorem cnt_past (bits : Nat → Bool) (total base : Nat) (hz : ∀ s, total ≤ s → bits s = false) (hb : total ≤ base) :
    ∀ n, cnt bits base n = 0
  -- the empty run
  | 0 => rfl
  -- every symbol of the run is past the end, so not held
  | n + 1 => by simp [cnt, cnt_past bits total base hz hb n, hz (base + n) (by omega)]

-- `sumCounts count nb` adds up the counts of blocks `0` to `nb - 1`: what `BlockHeld::new` sums from a buffer.
def sumCounts (count : Nat → Nat) : Nat → Nat
  -- no blocks: zero
  | 0 => 0
  -- the first `nb` blocks, then block `nb`
  | nb + 1 => sumCounts count nb + count nb

/-- With every count right, the first `nb` blocks hold, in all, the sum of their counts. -/
theorem cnt_blocks (per : Nat) (h : Held) (hc : ∀ b, h.count b = cnt h.bits (b * per) per) :
    ∀ nb, cnt h.bits 0 (nb * per) = sumCounts h.count nb
  -- no blocks: an empty run
  | 0 => by simp [cnt, sumCounts]
  -- the first `nb` blocks, then the `per` symbols of block `nb`, which its count counts
  | nb + 1 => by
    rw [Nat.succ_mul, cnt_add, cnt_blocks per h hc nb]
    simp [sumCounts, hc nb]

/-- `BlockHeld::new` on an earlier set's buffer starts the running total at the sum of the block counts; when the
`nb` blocks cover the bundle (`total <= nb * per`), that sum is the total the earlier set kept. -/
theorem held_of_counts (per total nb : Nat) (h : Held) (hi : Inv per total h) (hcov : total ≤ nb * per) :
    sumCounts h.count nb = h.held := by
  obtain ⟨hc, hz, hh⟩ := hi
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hcov
  -- the blocks hold what the bundle's symbols hold, plus the `d` symbols past its end, which hold nothing
  rw [hh, ← cnt_blocks per h hc nb, hd, cnt_add, cnt_past h.bits total (0 + total) hz (by omega) d]
  simp

end Vinc.DtnHeld
