import Vinc.Json
import Vinc.BuilderBytes
import Std.Data.HashMap

/-!
# Replay of the outboard builder traces

The replay half of the trace validation of `OutboardBuilder`: it reads the events written by the Rust test
`trace_builder` and runs the byte-level model `BuilderBytes.updateCode` / `finishCode` on them.

A `bnew` event starts a run: the value length and group log must give the recorded group count; the model
builder starts empty (`UB.init`); the genuine tree is read as two tables, the hash call of each group (root flag,
group index, bytes in the group) and of each parent (root flag, left and right chaining values), and the
model's abstract hash is interpreted by them (a call that is not in a table gets the value 0, which no chaining
value has, so the model cannot accept it). The bytes of the value are represented by their offsets.

A `bupd` event is one call of `update`: the piece is the bytes `pos .. pos + ilen` and `pos` must be the model's
`consumed`, the buffer has `olen` bytes. The model's result must be the recorded one (`ok`, `outsize`, `toomuch`), and
the parents the model writes in the call, each at the slot `Layout.preorderIndex n lo hi` with the pair of the hash
values the model computed, must be exactly the slots that changed in the buffer, with the same pairs. So the
slot of every parent the code writes is checked against the proved pre-order index, and the pairs against the
genuine chaining values. A `bfin` event is a call of `finish`: the root and the parents written by the merge of
the stack are checked the same way, and the errors (`outsize`, `incomplete`) against `finishCode`. For a value of 0
bytes the root must be the recorded hash of the empty input.
-/

namespace Vinc.TraceBuilder
open Vinc.Json Vinc.Layout Vinc.Tree Vinc.Builder Vinc.BuilderBytes

/-- The model state of the current run. -/
structure BRun where
  cfg : BCfg Nat
  st : UB Nat
  pos : Nat
  osz : Nat

/-- The replay state of a file. -/
structure BState where
  run : Option BRun := none

private def mkKey (b : Bool) (x y : Nat) : List Nat := [if b then 1 else 0, x, y]

private def parseRows (j : J) : Except String (List (List J)) := do
  match j.arr? with
  | some a => a.toList.mapM fun v => match v.arr? with
    | some r => pure r.toList
    | none => throw "expected a row"
  | none => throw "expected an array"

private def asNat (j : J) : Except String Nat :=
  match j.nat? with
  | some n => pure n
  | none => throw "expected a number"

private def asBool (j : J) : Except String Bool :=
  match j.bool? with
  | some n => pure n
  | none => throw "expected a boolean"

private def insertFn (m : Std.HashMap (List Nat) Nat) (k : List Nat) (v : Nat) : Except String (Std.HashMap (List Nat) Nat) :=
  match m[k]? with
  | some v' => if v' == v then pure m else throw s!"the recorded hash is not a function at {k}"
  | none => pure (m.insert k v)

/-- Replay a `bnew` event. -/
def replayNew (bs : BState) (j : J) : Except String BState := do
  let len ← natF j "len"
  let log ← natF j "log"
  let e0 ← natF j "e0"
  check (log ≤ 20 && len ≤ u64Max) "builder run outside the supported layout"
  check (groups len log == (← natF j "n")) s!"groups {len} {log}"
  let mut leaves : Std.HashMap (List Nat) Nat := {}
  for row in ← parseRows (← field j "leaves") do
    match row with
    | [b, i, l, cv] => leaves ← insertFn leaves (mkKey (← asBool b) (← asNat i) (← asNat l)) (← asNat cv)
    | _ => throw "bad leaf row"
  let mut parents : Std.HashMap (List Nat) Nat := {}
  for row in ← parseRows (← field j "parents") do
    match row with
    | [b, l, r, cv] => parents ← insertFn parents (mkKey (← asBool b) (← asNat l) (← asNat r)) (← asNat cv)
    | _ => throw "bad parent row"
  let g := groupLen log
  let H : Hash Nat Bytes :=
    ⟨fun b i d =>
      if d == List.range' (i * g) d.length then leaves.getD (mkKey b i d.length) 0 else 0,
     fun b l r => parents.getD (mkKey b l r) 0⟩
  let cfg : BCfg Nat := { H := H, len := len, log := log, e0 := e0, z0 := 0 }
  pure { run := some ⟨cfg, UB.init cfg, 0, outboardSize len log⟩ }

/-- The slots written by the group-level state `new` that `old` had not written, as (slot, left, right), by slot. -/
private def newSlots (n : Nat) (old new : Vinc.Builder.BS Nat) : List (Nat × Nat × Nat) :=
  let ws := (new.w.drop old.w.length).map fun w => (preorderIndex n w.lo w.hi, w.l, w.r)
  (ws.toArray.qsort fun a b => a.1 < b.1).toList

private def slotsF (j : J) : Except String (List (Nat × Nat × Nat)) := do
  let rows ← parseRows (← field j "slots")
  rows.mapM fun row => match row with
    | [a, b, c] => do pure (← asNat a, ← asNat b, ← asNat c)
    | _ => throw "bad slot row"

/-- Replay a `bupd` or `bfin` event. -/
def replayCall (bs : BState) (j : J) (t : String) : Except String BState := do
  let some r := bs.run | throw "builder call before bnew"
  let olen ← natF j "olen"
  let res ← strF j "res"
  let slots ← slotsF j
  if t == "bupd" then
    let pos ← natF j "pos"
    let ilen ← natF j "ilen"
    check (pos == r.pos) s!"the piece starts at value offset {pos}, the model has consumed {r.pos}"
    let some (st', e) := updateCode 64 r.cfg olen r.st (List.range' pos ilen)
      | throw "the byte-level model of update failed arithmetically"
    let verdict := match e with | none => "ok" | some .outboardSize => "outsize" | some .tooMuchData => "toomuch" | some .incomplete => "incomplete"
    check (verdict == res) s!"update at {pos} of {ilen} bytes into {olen}: model {verdict}, code {res}"
    check (newSlots r.cfg.n r.st.bs st'.bs == slots) s!"update at {pos} of {ilen} bytes: slots written differ from the model's {newSlots r.cfg.n r.st.bs st'.bs}, code {slots}"
    if e.isNone then
      check (st'.con == pos + ilen) "consumed after the piece"
      pure { run := some { r with st := st', pos := pos + ilen } }
    else
      check (st'.con == r.st.con) "an error consumes nothing"
      pure bs
  else
    let root ← natF j "root"
    match finishCode r.cfg olen r.st with
    | .ok cv =>
      let fin := finish r.cfg.H r.cfg.n r.st.bs.stack.length r.st.bs
      check (res == "ok") s!"finish: model ok, code {res}"
      check (cv == root) s!"finish: root {cv}, code {root}"
      check (newSlots r.cfg.n r.st.bs fin == slots) "finish: slots written differ from the model's"
      if r.cfg.len == 0 then check (root == r.cfg.e0) "the empty value's root is the hash of the empty input"
      pure bs
    | .error e =>
      let verdict := match e with | .outboardSize => "outsize" | .incomplete => "incomplete" | .tooMuchData => "toomuch"
      check (verdict == res) s!"finish into {olen}: model {verdict}, code {res}"
      check (slots.isEmpty) "a failed finish writes nothing"
      pure bs

/-- Replay one builder event. -/
def replayEvent (j : J) (bs : BState) : Except String BState := do
  match (← strF j "t") with
  | "bnew" => replayNew bs j
  | "bupd" => replayCall bs j "bupd"
  | "bfin" => replayCall bs j "bfin"
  | t => throw s!"unknown builder event {t}"

end Vinc.TraceBuilder
