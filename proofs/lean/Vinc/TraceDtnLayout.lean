import Vinc.Json
import Vinc.DtnLayout
import Vinc.DtnLayoutHlc

/-!
# Replay of the layout traces

The Lean half of the trace validation of `SliceLayout` (`dtn_layout.ndjson`, written by the Rust test
`trace_dtn_layout`): every `dl` event is replayed through the functions the theorems of `Vinc.DtnLayout` are about
(`L.valid`, `dataSyms`, `blocks`, `totalSyms`, `totalLen`, `paddedLen`, `blockK`, `blockN`, `blockStart`, `locate`,
`dataSymbol`, `byteRange`). A `u64` is four 16-bit limbs; `limb` reads one. The helpers `limb` and `rows` are shared
by the other delay-tolerant replays. It is the port of `proofs/tla/TraceDtnLayout.tla`.
-/

namespace Vinc.TraceDtnLayout
open Vinc.Json Vinc.DtnLayout

/-- The value of four 16-bit limbs, least significant first. -/
def limb (j : J) : Except String Nat := do
  match ← natList j with
  | [a, b, c, d] => pure (a + 65536 * (b + 65536 * (c + 65536 * d)))
  | _ => throw "expected four limbs"

/-- The rows of an array field, each a list of values. -/
def rows (j : J) (k : String) : Except String (List (List J)) := do
  match (← field j k).arr? with
  | some a => a.toList.mapM fun r => match r.arr? with
    | some x => pure x.toList
    | none => throw s!"field {k}: a row is not an array"
  | none => throw s!"field {k} is not an array"

def isTag (t : String) : Bool := t == "dl" || t == "hc"

def at_ (r : List J) (i : Nat) : Except String J :=
  match r[i]? with
  | some v => pure v
  | none => throw s!"row too short at {i}"

def natAt (r : List J) (i : Nat) : Except String Nat := do
  match (← at_ r i).nat? with
  | some n => pure n
  | none => throw s!"entry {i} is not a number"

def boolAt (r : List J) (i : Nat) : Except String Bool := do
  match (← at_ r i).bool? with
  | some n => pure n
  | none => throw s!"entry {i} is not a bool"

def limbAt (r : List J) (i : Nat) : Except String Nat := do limb (← at_ r i)

/-- Replay one `dl` event. -/
def replayLayout (j : J) : Except String Unit := do
  let l : L := ⟨← natF j "k", ← natF j "m", ← natF j "log", ← limb (← field j "p")⟩
  let ok ← boolF j "ok"
  check (l.valid == ok) s!"new: model {l.valid}, code {ok} for {l.k} {l.m} {l.log} {l.p}"
  if !ok then return
  check (l.dataSyms == (← limb (← field j "d"))) "data_symbols"
  check (l.blocks == (← limb (← field j "bl"))) "blocks"
  check (l.totalSyms == (← limb (← field j "ts"))) "total_symbols"
  check (l.totalLen == (← limb (← field j "tl"))) "total_len"
  check (l.paddedLen == (← limb (← field j "pad"))) "padded_len"
  for r in ← rows j "bk" do
    let b ← limbAt r 0
    check (l.blockK b == (← limbAt r 1) && l.blockN b == (← limbAt r 2) && l.blockStart b == (← limbAt r 3))
      s!"block_k, block_n or block_start of block {b}"
  for r in ← rows j "lc" do
    let s ← limbAt r 0
    match l.locate s, ← boolAt r 1 with
    | some p, true =>
      check (p.block == (← limbAt r 2) && p.index == (← natAt r 3) && p.blockK == (← natAt r 4)) s!"locate {s}"
    | none, false => pure ()
    | _, _ => throw s!"locate {s}: model and code disagree on presence"
  for r in ← rows j "ds" do
    let d ← limbAt r 0
    match l.dataSymbol d, ← boolAt r 1 with
    | some s, true => check (s == (← limbAt r 2)) s!"data_symbol {d}"
    | none, false => pure ()
    | _, _ => throw s!"data_symbol {d}: model and code disagree on presence"
  for r in ← rows j "br" do
    let a ← limbAt r 0
    let b ← limbAt r 1
    match l.byteRange a b, ← boolAt r 2 with
    | some (s, e), true => check (s == (← limbAt r 3) && e == (← limbAt r 4)) s!"byte_range {a} {b}"
    | none, false => pure ()
    | _, _ => throw s!"byte_range {a} {b}: model and code disagree on presence"

/-- Replay one clock event (`hc`): `tick`, `observe`, `expires_at` and `is_expired` through the functions of
`Vinc.DtnLayoutHlc`. -/
def replayClock (j : J) : Except String Unit := do
  let op ← strF j "op"
  let w ← limb (← field j "w")
  match op with
  | "tick" =>
    let h : DtnLayoutHlc.H := ⟨w, ← limb (← field j "c")⟩
    let r := h.tick (← limb (← field j "now"))
    check (r.wall == (← limb (← field j "ow")) && r.counter == (← limb (← field j "oc"))) "tick"
  | "obs" =>
    let h : DtnLayoutHlc.H := ⟨w, ← limb (← field j "c")⟩
    let rem : DtnLayoutHlc.H := ⟨← limb (← field j "rw"), ← limb (← field j "rc")⟩
    let r := h.observe rem (← limb (← field j "now"))
    check (r.wall == (← limb (← field j "ow")) && r.counter == (← limb (← field j "oc"))) "observe"
  | "exp" =>
    let life ← limb (← field j "life")
    check (DtnLayoutHlc.expiresAt w life == (← limb (← field j "e"))) "expires_at"
    for r in ← rows j "pr" do
      let n ← limbAt r 0
      check (DtnLayoutHlc.isExpired w life n == (← boolAt r 1)) s!"is_expired at {n}"
  | _ => throw s!"unknown clock op {op}"

/-- Replay one event of the layout trace file. -/
def replayEvent (j : J) : Except String Unit := do
  match ← strF j "t" with
  | "hc" => replayClock j
  | _ => replayLayout j

end Vinc.TraceDtnLayout
