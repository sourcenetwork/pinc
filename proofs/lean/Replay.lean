import Vinc.Json
import Vinc.Varint
import Vinc.Ranges
import Vinc.Layout

/-!
# Trace replay

`replay <file>...` replays the ndjson traces written by the Rust test `trace_ranges` against the Lean model
functions (`Vinc.Varint.decode`, `Vinc.Varint.encodeInto`, `Vinc.Ranges.insertFixed`, `insertVec`, `find`,
`containsRange`, `coveredLen`, `Vinc.Layout.groupRange`, `groups`). Any difference between what the code
recorded and what the proved model computes exits with an error naming the line.
-/

open Vinc Vinc.Json

private def field (j : J) (k : String) : Except String J :=
  match j.get? k with
  | some v => pure v
  | none => throw s!"missing field {k}"

private def natF (j : J) (k : String) : Except String Nat := do
  match (← field j k).nat? with
  | some n => pure n
  | none => throw s!"field {k} is not a number"

private def boolF (j : J) (k : String) : Except String Bool := do
  match (← field j k).bool? with
  | some n => pure n
  | none => throw s!"field {k} is not a bool"

private def strF (j : J) (k : String) : Except String String := do
  match (← field j k).str? with
  | some n => pure n
  | none => throw s!"field {k} is not a string"

private def natList (j : J) : Except String (List Nat) := do
  match j.arr? with
  | some a => a.toList.mapM fun v => match v.nat? with
    | some n => pure n
    | none => throw "expected a number"
  | none => throw "expected an array"

private def pairList (j : J) : Except String (List (Nat × Nat)) := do
  match j.arr? with
  | some a => a.toList.mapM fun v => do
    match ← natList v with
    | [x, y] => pure (x, y)
    | _ => throw "expected a pair"
  | none => throw "expected an array"

private def check (ok : Bool) (msg : String) : Except String Unit :=
  if ok then pure () else throw msg

/-- Replay one varint or layout event. -/
private def replayPure (j : J) (t : String) : Except String Unit := do
  match t with
  | "venc" =>
    let v ← natF j "v"
    let cap ← natF j "cap"
    let res := Varint.encodeInto cap v
    match j.get? "ok", j.get? "err" with
    | some b, _ =>
      let bytes ← natList b
      check (match res with | .ok r => r == bytes | .error _ => false) s!"encode {v}: model {repr (match res with | .ok r => r | .error _ => [])}, code {bytes}"
    | _, some _ =>
      let e ← strF j "err"
      let expected : Varint.Error ← match e with
        | "overflow" => pure .overflow
        | "small" => pure (.bufferTooSmall (← natF j "needed"))
        | _ => throw s!"unknown error {e}"
      check (match res with | .error r => r == expected | .ok _ => false) s!"encode {v}: expected error {e}"
    | _, _ => throw "venc needs ok or err"
  | "vdec" =>
    let bytes ← natList (← field j "bytes")
    let res := Varint.decode bytes
    match j.get? "ok", j.get? "err" with
    | some p, _ =>
      match ← natList p with
      | [v, n] => check (match res with | .ok (a, b) => a == v && b == n | .error _ => false) s!"decode {bytes}: expected ({v}, {n})"
      | _ => throw "bad ok pair"
    | _, some _ =>
      let e ← strF j "err"
      let expected : Varint.Error ← match e with
        | "toolong" => pure .tooLong
        | "truncated" => pure .truncated
        | "nonminimal" => pure .nonMinimal
        | _ => throw s!"unknown error {e}"
      check (match res with | .error r => r == expected | .ok _ => false) s!"decode {bytes}: expected error {e}"
    | _, _ => throw "vdec needs ok or err"
  | "grange" =>
    let len ← natF j "len"
    let log ← natF j "log"
    let s ← natF j "s"
    let e ← natF j "e"
    check (Layout.groups len log == (← natF j "groups")) s!"groups {len} {log}"
    let res := Layout.groupRange len log s e
    match j.get? "ok" with
    | some p =>
      match ← natList p with
      | [a, b] => check (res == some (a, b)) s!"group_range {len} {log} {s} {e}: expected ({a}, {b})"
      | _ => throw "bad ok pair"
    | none => check res.isNone s!"group_range {len} {log} {s} {e}: expected an error"
  | _ => throw s!"unknown event {t}"

/-- Replay one verified-range event against the model state of its run; returns the new model state. -/
private def replayRanges (j : J) (items : List Ranges.Interval) : Except String (List Ranges.Interval) := do
  let kind ← strF j "kind"
  let n ← natF j "n"
  let seq ← natF j "seq"
  let s ← natF j "s"
  let e ← natF j "e"
  let ok ← boolF j "ok"
  let items := if seq == 0 then [] else items
  let (modelOk, next) ← match kind with
    | "fixed" => pure ((Ranges.insertFixed n items (s, e)).isSome, Ranges.insertState n items (s, e))
    | "vec" => pure (true, Ranges.insertVec items (s, e))
    | _ => throw s!"unknown kind {kind}"
  check (modelOk == ok) s!"insert [{s}, {e}) on {items}: model ok = {modelOk}, code ok = {ok}"
  let recorded ← pairList (← field j "items")
  check (next == recorded) s!"insert [{s}, {e}) on {items}: model {next}, code {recorded}"
  check (Ranges.coveredLen next == (← natF j "cl")) s!"covered_len of {next}"
  check (Ranges.contains next (← natF j "x") == (← boolF j "cx")) s!"contains of {next}"
  check (Ranges.containsRange next (← natF j "cs", ← natF j "ce") == (← boolF j "cr")) s!"contains_range of {next}"
  pure next

private def replayFile (path : String) : IO Nat := do
  let text ← IO.FS.readFile path
  let mut items : List Ranges.Interval := []
  let mut count := 0
  let mut lineNo := 0
  for line in text.splitOn "\n" do
    lineNo := lineNo + 1
    if line.trimAscii.isEmpty then continue
    let r : Except String (List Ranges.Interval) := do
      let j ← parse line
      match j.get? "t" with
      | some t =>
        replayPure j (← match t.str? with | some s => pure s | none => throw "t is not a string")
        pure items
      | none => replayRanges j items
    match r with
    | .ok next =>
      items := next
      count := count + 1
    | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
  pure count

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: replay <trace.ndjson>..."
    return 2
  let mut total := 0
  for path in args do
    let n ← replayFile path
    IO.println s!"replay: {path}: {n} events match the model"
    total := total + n
  IO.println s!"replay: ok, {total} events"
  return 0
