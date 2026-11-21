import Pinc.Json
import Pinc.ReconcileSession
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Replay of the reconciliation traces

The Lean half of the trace validation of `pinc-reconcile`: it reads the `rc` events written by the Rust test
`trace_reconcile` and replays every handler call through `Initiator.start`, `Initiator.handle`, `Responder.handle`
and `Responder.resume` of `Pinc.ReconcileSession`, the byte-level model of `core.rs` and `session.rs`.

A `case` event carries the two sets, the limits of both sides, the set reference, the table of ids (the 64-bit id of
every item of the two sets) and the fingerprints the real code computed: `FR`, one row `[side, a, b, bytes]` per range
fingerprint (the 32 bytes of positions `a..b` of side `side`, 0 the initiator's set `A`, 1 the responder's `B`), and
`FC`, one row `[here, there, bytes]` per final check the real initiator wrote (the 32 bytes for its arenas `here` and
`there`). They are the oracle `Oracle` of the model: `enc` is a lookup in a table keyed by the pair of a sum and a
count, where a sum is read as its coefficients on the items of the case (the items of `A`, `B` and every `FC` row, in
the order they first appear). An `FR` row is keyed by the sum and the count `b - a` of the slice it names, an `FC`
row by `sum A + sum here - sum there` and the count `|A| + |here| - |there|`, built with the very definitions
(`sumH`, `Sum`) the theorems use. So the real hash is the model's hash on every query the real code made and no
assumption on it enters the replay; a query with no row (the model asks for a fingerprint the real code never
computed) answers a value of 2^256 or more, which no 32 bytes equal, so the comparison fails at that event; two rows
with one key and different bytes are a broken trace and fail the load. An `ev` event is one handler call with the bytes
delivered to it; the replay requires the same step and the same bytes written, or the same error. A `reset` event
is `Responder::reset`, a `rep` event the report of the finished initiator. A refused message leaves the object as
`afterErr` says (the session ended).
-/

namespace Pinc.TraceReconcile
open Pinc.Json Pinc.Reconcile

/-- The replay state of a case. -/
structure Case where
  id : Nat
  o : Oracle
  a : List Item
  b : List Item
  ref : Item
  init : Initiator
  resp : Responder
  done : Bool := false

instance : Inhabited Case :=
  ⟨⟨0, ⟨fun _ _ => 0, fun _ => 0⟩, [], [], [], ⟨{ lim := ⟨0, 0, 0, 0⟩, init := true }, .idle⟩,
    ⟨{ lim := ⟨0, 0, 0, 0⟩, init := false }, .fresh⟩, false⟩⟩

/-- The replay state of a file: the current case, if any. -/
structure W where
  c : Option Case := none
  events : Nat := 0

def itemList (j : J) : Except String (List Item) := do
  match j.arr? with
  | some a => a.toList.mapM natList
  | none => throw "expected an array of items"

def tableOf (j : J) : Except String (Std.HashMap Item Nat) := do
  match j.arr? with
  | some a =>
    let mut m : Std.HashMap Item Nat := {}
    for p in a.toList do
      match p.arr? with
      | some #[k, v] => m := m.insert (← natList k) (fromBE (← natList v))
      | _ => throw "expected an [item, bytes] pair"
    pure m
  | none => throw "expected a table"

/-- The distinct items of a list, in the order they first appear. -/
def dedupe (xs : List Item) : List Item :=
  (xs.foldl (fun (acc : Std.HashSet Item × List Item) x =>
    if acc.1.contains x then acc else (acc.1.insert x, x :: acc.2)) ({}, [])).2.reverse

/-- The table key of a sum and a count: the coefficients of the sum on the items of the case. -/
def fpKey (items : List Item) (s : Sum) (c : Nat) : List Int × Nat := (items.map s, c)

/-- One recorded fingerprint: a sum, a count, and the number the 32 bytes are. -/
abbrev FpRow := Sum × Nat × Nat

def bytes32 (j : J) : Except String Nat := do
  let bs ← natList j
  check (bs.length == fpLen) s!"a fingerprint has {bs.length} bytes, not {fpLen}"
  pure (fromBE bs)

/-- The `FR` rows: the sum of positions `a..b` of a side and the count `b - a`. -/
def frRows (a b : List Item) (j : J) : Except String (List FpRow) := do
  let some rows := j.arr? | throw "FR must be an array"
  rows.toList.mapM fun p => do
    let some #[sd, x, y, bs] := p.arr? | throw "an FR row is [side, a, b, bytes]"
    let some sd := sd.nat? | throw "an FR side is 0 or 1"
    let some x := x.nat? | throw "an FR position is a number"
    let some y := y.nat? | throw "an FR position is a number"
    let s := if sd == 0 then a else b
    check (sd ≤ 1 ∧ x ≤ y ∧ y ≤ s.length) s!"an FR row [{sd}, {x}, {y}] is out of range"
    pure (sumH ((s.drop x).take (y - x)), y - x, ← bytes32 bs)

/-- The `FC` rows: the final check `sum A + sum here - sum there` with the count `|A| + |here| - |there|`. -/
def fcRows (j : J) : Except String (List (List Item × List Item × Nat)) := do
  let some rows := j.arr? | throw "FC must be an array"
  rows.toList.mapM fun p => do
    let some #[h, t, bs] := p.arr? | throw "an FC row is [here, there, bytes]"
    pure (← itemList h, ← itemList t, ← bytes32 bs)

/-- The oracle of a case: `enc` looks the pair of a sum and a count up in the recorded rows. A pair with no row gets
`2 ^ 256`, which is no 32 byte number. Two rows with one key and different bytes are an error. -/
def encOracle (items : List Item) (rows : List FpRow) (ids : Std.HashMap Item Nat) : Except String Oracle := do
  let tbl ← rows.foldlM (init := ({} : Std.HashMap (List Int × Nat) Nat)) fun m (s, c, v) => do
    let k := fpKey items s c
    match m.get? k with
    | some v' => do check (v' == v) "two fingerprint rows have one key and different bytes"; pure m
    | none => pure (m.insert k v)
  pure ⟨fun s c => (tbl.get? (fpKey items s c)).getD (2 ^ 256), fun x => (ids.get? x).getD (2 ^ 200)⟩

def errName : Err → String
  | .malformed .frame => "frame"
  | .malformed .truncated => "truncated"
  | .malformed .tag => "tag"
  | .malformed .bound => "bound"
  | .malformed .count => "count"
  | .malformed .item => "item"
  | .malformed .state => "state"
  | .index => "index"
  | .badIndex => "badIndex"
  | .messageTooLarge => "messageTooLarge"
  | .itemTooLarge => "itemTooLarge"
  | .reportTooLarge => "reportTooLarge"
  | .tooManyRounds => "tooManyRounds"
  | .mismatch => "mismatch"

def stepName : Step → String
  | .send => "send" | .chunk => "chunk" | .last => "last" | .wait => "wait" | .done => "done"

def limOf (j : J) : Except String Limits := do
  match ← natList j with
  | [a, b, c, d] => pure ⟨a, b, c, d⟩
  | _ => throw "limits need four numbers"

/-- Compare a model result with the recorded outcome of a call. -/
def compare (what : String) (j : J) (res : Except Err (Step × List Nat)) : Except String Unit := do
  if (← boolF j "ok") then
    let step ← strF j "step"
    let out ← natList (← field j "out")
    match res with
    | .error e => throw s!"{what}: the code answered {step}, the model fails with {errName e}"
    | .ok (s, m) =>
      check (stepName s == step || what.endsWith "start") s!"{what}: the code's step is {step}, the model's {stepName s}"
      -- A handler that writes nothing leaves the buffer as it was: the trace records [].
      let m := if s == .wait || s == .done then [] else m
      let k := (List.range (max m.length out.length)).find? (fun i => m[i]? != out[i]?)
      check (m == out) s!"{what}: the bytes written differ at {k}: code length {out.length} from there {(out.drop (k.getD 0)).take 24}, model length {m.length} from there {(m.drop (k.getD 0)).take 24}, code head {out.take 30}"
  else
    let err ← strF j "err"
    match res with
    | .ok (s, _) => throw s!"{what}: the code fails with {err}, the model answers {stepName s}"
    | .error e => check (errName e == err) s!"{what}: the code fails with {err}, the model with {errName e}"

def replayEvent (j : J) (w : W) : Except String W := do
  let e ← strF j "e"
  if e == "case" then
    let ids ← tableOf (← field j "ID")
    let a ← itemList (← field j "A")
    let b ← itemList (← field j "B")
    let fr ← frRows a b (← field j "FR")
    let fc ← fcRows (← field j "FC")
    let items := dedupe (a ++ b ++ fc.flatMap fun (h, t, _) => h ++ t)
    let rows := fr ++ fc.map fun (h, t, v) => (sumH a + sumH h - sumH t, a.length + h.length - t.length, v)
    let o ← encOracle items rows ids
    let li ← limOf (← field j "limI")
    let lr ← limOf (← field j "limR")
    let cs : Case := ⟨← natF j "id", o, a, b,
      ← natList (← field j "ref"), ⟨{ lim := li, init := true }, .idle⟩, ⟨{ lim := lr, init := false }, .fresh⟩, false⟩
    pure { w with c := some cs, events := w.events + 1 }
  else
    let some c := w.c | throw "event before a case"
    check ((← natF j "id") == c.id) "event of another case"
    match e with
    | "reset" => pure { w with c := some { c with resp := { c.resp with side := .fresh } }, events := w.events + 1 }
    | "rep" =>
      let here ← itemList (← field j "here")
      let there ← itemList (← field j "there")
      check (c.init.phase == .done) "rep before the initiator is done"
      check (c.init.core.here == here) s!"report: missing_here differs: code {here}, model {c.init.core.here}"
      check (c.init.core.there == there) s!"report: missing_there differs: code {there}, model {c.init.core.there}"
      pure { w with events := w.events + 1 }
    | "ev" =>
      let who ← strF j "who"
      let call ← strF j "call"
      let inp ← natList (← field j "in")
      let what := s!"{who}.{call}"
      let w' := { w with events := w.events + 1 }
      match who, call with
      | "I", "start" =>
        let r := c.init.start c.o c.a c.ref
        compare what j (r.map fun (_, m) => (.send, m))
        pure { w' with c := some { c with init := match r with | .ok (s, _) => s | .error _ => c.init } }
      | "I", "handle" =>
        let r := c.init.handle c.o c.a inp
        compare what j (r.map fun (s, m, _) => (s, m))
        pure { w' with c := some { c with init := match r with | .ok (_, _, s) => s | .error _ => c.init.afterErr } }
      | "R", "handle" =>
        let r := c.resp.handle c.o c.b inp
        compare what j (r.map fun (s, m, _) => (s, m))
        pure { w' with c := some { c with resp := match r with | .ok (_, _, s) => s | .error _ => c.resp.afterErr inp } }
      | "R", "resume" =>
        let r := c.resp.resume c.o c.b
        compare what j (r.map fun (s, m, _) => (s, m))
        pure { w' with c := some { c with resp := match r with | .ok (_, _, s) => s | .error _ => c.resp.afterResumeErr } }
      | _, _ => throw s!"unknown call {who}.{call}"
    | _ => throw s!"unknown event {e}"

end Pinc.TraceReconcile
