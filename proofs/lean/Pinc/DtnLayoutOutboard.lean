import Pinc.DtnLayout
import Pinc.Sizes

/-!
# The outboard of a sealed bundle (`SliceLayout::outboard_len`)

`outboard_len` is `Layout::new(total_len, log).outboard_size()` of the tree crate: the tree over the sealed bundle,
whose groups are exactly the slices (the group size `1024 << log` is the slice length), so it has one group per
symbol and one 64-byte pair per parent, `total_syms - 1` of them. `outboard_len_eq` proves that relation for every valid
layout: the number of tree groups is the number of symbols, the outboard is `64 * (total_syms - 1)` bytes, and it fits
`u64` (`Pinc.Layout.outboardSize_lt`), so the `try_from` of the buffer length in `seal` and `finish` is exact.
-/

namespace Pinc.DtnLayout
open Pinc.Layout

theorem groupLen_eq_sliceLen (l : L) : groupLen l.log = l.sliceLen := by
  unfold groupLen L.sliceLen chunk
  rw [Nat.shiftLeft_eq, Nat.mul_comm]

/-- One tree group per symbol. -/
theorem groups_eq_totalSyms (l : L) : groups l.totalLen l.log = l.totalSyms := by
  have hs := sliceLen_pos l
  unfold groups L.totalLen
  rw [groupLen_eq_sliceLen, Nat.mul_mod_left, if_pos rfl, Nat.mul_div_cancel _ hs, Nat.add_zero]

/-- `outboard_len`: 64 bytes for each parent of the tree over the symbols, and it fits `u64`. -/
theorem outboard_len_eq (l : L) (h : l.valid = true) :
    outboardSize l.totalLen l.log = 64 * (l.totalSyms - 1) ∧ outboardSize l.totalLen l.log < 2 ^ 64 := by
  have hv := (valid_iff l).1 h
  refine ⟨?_, outboardSize_lt _ _ (by have := hv.2.2; unfold M at this; unfold u64Max; omega)⟩
  unfold outboardSize
  rw [groups_eq_totalSyms]
  rcases hts : l.totalSyms with _ | n <;> simp [Nat.mul_comm]

#print axioms outboard_len_eq

end Pinc.DtnLayout
