import Vinc.Machine
import Vinc.MachineEnc
import Vinc.Varint
import Vinc.BuilderBytes

/-!
# The link to the TLA+ models

`proofs/tla/Varint.tla`, `Layout.tla`, `Encoder.tla` and `BuilderBytes.tla` check the code on bounded domains by
TLC. This module evaluates the Lean models of the same code, the functions the general theorems of the package are
about, on the same boundary sets, and the kernel checks the result (`decide +kernel`: the kernel evaluates the
boundary sets, which adds nothing to the facts the package already relies on). Each theorem names the general
theorem and the TLA+ invariant it corresponds to, so a boundary value that one tool accepts and the other rejects
cannot go unnoticed. The sets are the TLA+ ones: `EdgeVal` (for every `j` in `0..64`, `2^j - 1` for `j >= 1`, `2^j`
and `2^j + 1` for `j < 64`), the byte classes `Alpha`, the addends of `Encoder.tla`, the group buffer sizes of
`Layout.tla`, the four path shapes of `Layout.tla`, and the completed-group counts of `BuilderBytes.tla`. The values
below 16500 that `Varint.tla` also enumerates are, in Lean, below 130, and `Varint.tla` enumerates the strings of up
to 4 bytes over the class alphabet where Lean takes up to 2; the tree sizes of the path theorems are the boundary
values for the `j` of `bigJ`, the cascades being `d = 2^j`.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Vinc.Link
open Vinc.Varint Vinc.Layout Vinc.Machine

/-- The boundary values of the TLA+ models. -/
def edgeVals : List Nat :=
  (List.range 65).flatMap fun j => (if 1 ≤ j then [2 ^ j - 1] else []) ++ (if j < 64 then [2 ^ j, 2 ^ j + 1] else [])

/-- The values of the varint model: the boundary values and the small values. -/
def varintVals : List Nat := edgeVals ++ List.range 130

/-- The rests `Varint.tla` puts after an encoding. -/
def rests : List (List Nat) := [[], [0], [128], [255], [0, 0], [128, 128]]

/-- `Varint.tla` `RoundTrip`, `EncodeLength`, `Canonical`: decoding an encoding followed by a rest gives the value and
the length of the encoding, which is `encodedLen`. Lean: `Varint.decode_encode`, `encode_length`. -/
theorem varint_roundtrip_boundary :
    varintVals.all (fun v => decide (limit ≤ v) || (rests.all fun r =>
      match decode (encodeBytes v ++ r) with
      | .ok (a, n) => a == v && n == (encodeBytes v).length && n == encodedLen v && decide (n ≤ 9)
      | .error _ => false)) = true := by decide +kernel

/-- `Varint.tla` `EncodeInto`: every buffer size gives the error or the bytes. Lean: `Varint.encodeInto_ok_iff`. -/
theorem varint_encode_boundary :
    varintVals.all (fun v => (List.range 11).all fun cap =>
      match encodeInto cap v with
      | .error .overflow => decide (limit ≤ v)
      | .error (.bufferTooSmall k) => decide (v < limit) && decide (cap < encodedLen v) && k == encodedLen v - cap
      | .error _ => false
      | .ok bs => decide (v < limit) && decide (encodedLen v ≤ cap) && bs == encodeBytes v) = true := by decide +kernel

/-- The class alphabet of `Varint.tla`. -/
def alpha : List Nat := [0, 1, 2, 64, 127, 128, 129, 192, 255]

/-- The strings of exactly `n` bytes over `a`. -/
def strsOf (a : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (strsOf a n).flatMap fun s => a.map (· :: s)

/-- The strings of at most `n` bytes over the class alphabet. -/
def strs (n : Nat) : List (List Nat) := (List.range (n + 1)).flatMap fun k => strsOf alpha k

/-- `Varint.tla` `DecodeOK`, `Unique`: an accepted prefix is exactly the encoding of the value, below `2^63`, in at
most 9 bytes. Lean: `Varint.decode_canonical`, `unique_encoding`, `decode_bounds`. -/
theorem varint_decode_boundary :
    (strs 2).all (fun s =>
      match decode s with
      | .ok (v, n) => decide (v < limit) && decide (n ≤ 9) && encodeBytes v == s.take n
      | .error _ => true) = true := by decide +kernel

/-- `Layout.tla` `GroupsOK`, `DepthOK`, `OutboardOK`, `GroupSizeOK`: the machine-integer code of the layout returns
the model's values on the boundary lengths, for every group log (`hh` is the height of the tree, equal to the
recursive one by `Layout.ht_eq`). Lean: `Machine.groupsM_eq`, `depthM_eq`, `outboardSizeM_eq`, `groupSizeM_eq`. -/
theorem layout_boundary :
    edgeVals.all (fun len => (List.range 21).all fun log =>
      groupsM len log == some (groups len log)
      && depthM (fun x => 63 - Nat.log2 x) len log == some (hh (groups len log))
      && outboardSizeM len log == some (outboardSize len log)
      && [0, 1, groups len log, groups len log + 1, 2 ^ 64 - 1].all fun i =>
           groupSizeM len log i == some (groupSize len log i)) = true := by decide +kernel

/-- `Layout.tla` `GroupRangeOK`. Lean: `Machine.groupRangeM_eq`. -/
theorem group_range_boundary :
    edgeVals.all (fun len => [0, 10, 20].all fun log =>
      [0, 1, len, len / 2, len + 1, 1023, 1024, 1025].all fun s =>
      [0, 1, len, len / 2, len + 1, 1023, 1024, 1025].all fun e =>
        groupRangeM len log s e == some (if groupRange len log s e = none then none else groupRange len log s e)) = true := by
  decide +kernel

/-- `Layout.tla` `LeftOK`: `left_groups` on the counts below 300 and the boundary counts. Lean:
`Machine.leftGroupsM_eq`, `Layout.leftGroups_pos`, `leftGroups_lt`, `le_two_leftGroups`, `leftGroups_max`. -/
theorem left_groups_boundary :
    (List.range 300 ++ edgeVals).all (fun c => leftGroupsM Nat.log2 c == some (leftGroups c)) = true := by decide +kernel

/-- The node reached from the root `[a, b)` by the turns `ts` (`true`: left), stopping at a leaf. -/
def walk (a b : Nat) : List Bool → Nat × Nat
  | [] => (a, b)
  | t :: ts =>
    if b - a < 2 then (a, b)
    else
      let m := a + leftGroups (b - a)
      if t then walk a m ts else walk m b ts

/-- The nodes `Layout.tla` (`Shapes`) reaches in a tree of `n` groups: the left spine, the right spine and the two
alternating paths, 60 turns each. -/
def shapeNodes (n : Nat) : List (Nat × Nat) :=
  [List.replicate 60 true, List.replicate 60 false, (List.range 60).map (· % 2 == 0),
    (List.range 60).map (· % 2 == 1)].map (walk 0 n)

/-- The exponents of the tree sizes the path theorems take: the boundary values `2^j - 1`, `2^j`, `2^j + 1` for these
`j` (the byte widths 2, 4, 8, 16, 32, 64 bits around the powers of 7 and 10, and the top of the range) up to `2^54`
groups; `Layout.tla` takes every `j`. -/
def bigJ : List Nat := [1, 2, 3, 4, 5, 7, 8, 9, 10, 16, 17, 31, 32, 33, 53, 54]

/-- The tree sizes of `Layout.tla` (`BigN`) the Lean theorems take. -/
def bigN : List Nat := bigJ.flatMap fun j => [2 ^ j - 1, 2 ^ j, 2 ^ j + 1]

/-- `Layout.tla` `PreorderOK` on the shape paths: `preorder_index` as the code writes it on `u64` returns the model's
position, for trees of up to `2^54` groups. Lean: `Machine.preorderIndexM_eq`, `Layout.preorderIndex_correct`. -/
theorem preorder_boundary :
    bigN.all (fun n => (shapeNodes n).all fun p =>
      decide (p.2 - p.1 < 2) || (preorderIndexM Nat.log2 n p.1 p.2 == some (preorderIndex n p.1 p.2))) = true := by
  decide +kernel

/-- `BuilderBytes.tla` `ArithOK`, for the groups `d = 2^j` that complete the longest cascades: the nodes a group completes, `[d - 2^k, d)` for `1 <= k <= tz d`, in trees of `n >= d`
groups, find their slot in the outboard of `64 * (n - 1)` bytes on a 32-bit and a 64-bit `usize` without an overflow
or a truncation. Lean: `BuilderBytes.builder_arith`, `slotM_eq`. -/
theorem slot_boundary :
    (bigJ.map (2 ^ ·)).all (fun d => [d, d + 1, 2 ^ 54].all fun n => decide (n < d) || decide (2 ^ 54 < n) ||
      (List.range 55).all fun k => decide (k = 0) || decide (d % 2 ^ k ≠ 0) ||
        [32, 64].all fun w => decide (2 ^ w ≤ 64 * (n - 1)) ||
          (Vinc.BuilderBytes.slotM Nat.log2 w (64 * (n - 1)) n (d - 2 ^ k) d == some (64 * preorderIndex n (d - 2 ^ k) d))) = true := by
  decide +kernel

/-- The group buffer sizes of `Layout.tla` (`GbSet`) accepted by `Layout::for_group_bytes`. Lean:
`Machine.forGroupBytesM_iff`. -/
theorem for_group_bytes_boundary :
    ((List.range 23).flatMap fun k => [1024 <<< k, 1024 <<< k - 1, 1024 <<< k + 1, 3 <<< (10 + k)]
        ++ [0, 1, 1023, 1025, 3072, 2047, 2048, 5120, 2 ^ 40, 2 ^ 63]).all (fun gb =>
      (forGroupBytesM Nat.log2 gb).isSome == (List.range 21).any fun log => gb == groupLen log) = true := by decide +kernel

/-- `Encoder.tla` `FoldOK`: the checked fold of `encoded_len` fails exactly when the sum reaches `2^64`, for every
list of up to 3 addends from the TLA+ set. Lean: `MachineEnc.foldAdd_eq`, `encodedLen_overflows_iff`. -/
def addends : List Nat := [0, 1, 64, 2 ^ 63, 2 ^ 63 - 1, 2 ^ 64 - 1, 2 ^ 32, 2 ^ 64 - 64]

/-- The lists of at most `n` addends. -/
def lists (n : Nat) : List (List Nat) := (List.range (n + 1)).flatMap fun k => strsOf addends k

theorem fold_boundary :
    (lists 3).all (fun xs => foldAdd 0 xs == (if xs.sum < 2 ^ 64 then some xs.sum else none)) = true := by decide +kernel

end Vinc.Link

#audit_axioms Vinc.Link.varint_roundtrip_boundary
#audit_axioms Vinc.Link.varint_encode_boundary
#audit_axioms Vinc.Link.varint_decode_boundary
#audit_axioms Vinc.Link.layout_boundary
#audit_axioms Vinc.Link.group_range_boundary
#audit_axioms Vinc.Link.left_groups_boundary
#audit_axioms Vinc.Link.for_group_bytes_boundary
#audit_axioms Vinc.Link.fold_boundary
#audit_axioms Vinc.Link.preorder_boundary
#audit_axioms Vinc.Link.slot_boundary
