import Vinc.Json
import Vinc.DtnRs
import Vinc.DtnGfSlice

/-!
# Replay of the GF(2^8) and Reed-Solomon traces

The replay half of the trace validation of `gf256.rs` and `rs.rs` (the Rust test `trace_dtn_rs`; the TLA+ half is
`TraceDtnRs.tla`). Every recorded call is replayed through the Lean functions the theorems are about, and any
difference exits with an error naming the line:

* `ginv` / `gmul`: the field instance of `DtnGfField` (its `⁻¹` and `*` are the table-driven `invT` and `mulT`);
* `gkern`: the slice kernels of `DtnGfSlice` (`mulAdd`, `xorInto`, `scaleL`), on the recorded slices;
* `rsnew`: `DtnRs.validParams`;
* `rsenc` / `rsrec`: the block checks of `Rs::encode` and `Rs::reconstruct` (`len = 0`, the block length, the length of
  `present`, the count of present symbols), then the column model `encodeCol` / `reconCol` of `DtnRs` on each of the
  `len` byte columns of the block, which must give the recorded output block byte for byte.
-/

namespace Vinc.TraceDtnRs
open Vinc.Json Vinc.DtnGf Vinc.DtnRs Vinc.DtnGfSlice

/-- The replay state: the number of events replayed by each family. -/
structure W where
  field : Nat := 0
  kernels : Nat := 0
  encodes : Nat := 0
  reconstructs : Nat := 0
  deriving Inhabited

/-- The event tags of this trace. -/
def isTag (t : String) : Bool := ["ginv", "gmul", "gkern", "rsnew", "rsenc", "rsrec"].contains t

/-- Column `p` of a block of `n` symbols of `len` bytes. -/
def column (blk : List Nat) (n len p : Nat) : List GF :=
  (List.range n).map fun s => GF.ofNat (blk.getD (s * len + p) 0)

/-- The byte of column results back at `s * len + p`: the block assembled from its columns. -/
def assemble (cols : List (List GF)) (n len : Nat) : List Nat :=
  (List.range (n * len)).map fun i => ((cols.getD (i % len) []).getD (i / len) (GF.ofNat 0)).v

def bitList (j : J) : Except String (List Bool) := do
  pure ((← natList j).map fun x => x != 0)

/-- Replay one event. -/
def replayEvent (j : J) (w : W) : Except String W := do
  match (← strF j "t") with
  | "ginv" =>
    let a ← natF j "a"
    check (a < 256) "ginv: operand is not a byte"
    check ((GF.ofNat a)⁻¹.v == (← natF j "r")) s!"inv {a}: model {(GF.ofNat a)⁻¹.v}"
    pure { w with field := w.field + 1 }
  | "gmul" =>
    let a ← natF j "a"
    let b ← natF j "b"
    check (a < 256 && b < 256) "gmul: operand is not a byte"
    check ((GF.ofNat a * GF.ofNat b).v == (← natF j "r")) s!"mul {a} {b}: model {(GF.ofNat a * GF.ofNat b).v}"
    pure { w with field := w.field + 1 }
  | "gkern" =>
    let c ← natF j "c"
    let dst ← natList (← field j "dst")
    let src ← natList (← field j "src")
    let out ← natList (← field j "out")
    let model ← match (← strF j "op") with
      | "muladd" => pure (mulAdd dst src c)
      | "xor" => pure (xorInto dst src)
      | "scale" => pure (scaleL dst c)
      | op => throw s!"unknown kernel {op}"
    check (model == out) s!"kernel {← strF j "op"} c={c} on {dst} {src}: model {model}, code {out}"
    pure { w with kernels := w.kernels + 1 }
  | "rsnew" =>
    let k ← natF j "k"
    let m ← natF j "m"
    check (validParams k m == (← boolF j "ok")) s!"Rs::new {k} {m}: model {validParams k m}"
    pure w
  | "rsenc" =>
    let k ← natF j "k"
    let m ← natF j "m"
    let len ← natF j "len"
    let n := k + m
    let blk ← natList (← field j "block")
    let out ← natList (← field j "out")
    check (validParams k m) "rsenc: invalid parameters"
    if len == 0 || blk.length != n * len then
      check (!(← boolF j "ok") && (← strF j "err") == "buffer" && out == blk) s!"encode {k} {m} len {len}: model Buffer"
    else
      check (← boolF j "ok") s!"encode {k} {m} len {len}: model succeeds"
      let cols := (List.range len).map fun p => encodeCol k m (column blk n len p)
      let model := assemble cols n len
      check (model == out) s!"encode {k} {m} len {len}: model {model}, code {out}"
    pure { w with encodes := w.encodes + 1 }
  | "rsrec" =>
    let k ← natF j "k"
    let m ← natF j "m"
    let len ← natF j "len"
    let n := k + m
    let blk ← natList (← field j "block")
    let out ← natList (← field j "out")
    let present ← bitList (← field j "present")
    check (validParams k m) "rsrec: invalid parameters"
    if present.length != n || len == 0 || blk.length != n * len then
      check (!(← boolF j "ok") && (← strF j "err") == "buffer" && out == blk) s!"reconstruct {k} {m} len {len}: model Buffer"
    else if present.countP id < k then
      check (!(← boolF j "ok") && (← strF j "err") == "incomplete" && out == blk)
        s!"reconstruct {k} {m} len {len}: model Incomplete"
    else
      check (← boolF j "ok") s!"reconstruct {k} {m} len {len}: model succeeds"
      let mut cols : List (List GF) := []
      for p in List.range len do
        match reconCol k m (column blk n len p) present with
        | .ok c => cols := cols ++ [c]
        | .error _ => throw s!"reconstruct {k} {m} len {len} column {p}: the model refuses"
      let model := assemble cols n len
      check (model == out) s!"reconstruct {k} {m} len {len}: model {model}, code {out}"
    pure { w with reconstructs := w.reconstructs + 1 }
  | t => throw s!"unknown event {t}"

end Vinc.TraceDtnRs
