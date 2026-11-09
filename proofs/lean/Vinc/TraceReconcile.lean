import Vinc.Json
import Vinc.ReconcileSession
import Std.Data.HashMap

/-!
# Replay of the reconciliation traces

The Lean half of the trace validation of `vinc-reconcile`: it reads the `rc` events written by the Rust test
`trace_reconcile` and replays every handler call through `Initiator.start`, `Initiator.handle`, `Responder.handle`
and `Responder.resume` of `Vinc.ReconcileSession`, the byte-level model of `core.rs` and `session.rs`.

A `case` event carries the two sets, the limits of both sides, the set reference and the hash tables: the 128-bit
fingerprint of every item that can be hashed and the 64-bit id of every item of the two sets. They are the oracle
`Oracle` of the model (`H x` is the big endian number of the 16 bytes, `idf x` of the 8 bytes), so the real keyed
hash is the model's hash and no assumption on it enters the replay. An `ev` event is one handler call with the bytes
delivered to it; the replay requires the same step and the same bytes written, or the same error. A `reset` event
is `Responder::reset`, a `rep` event the report of the finished initiator. A refused message leaves the object as
`afterErr` says (the session ended).
-/

namespace Vinc.TraceReconcile
open Vinc.Json Vinc.Reconcile

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
  ⟨⟨0, ⟨fun _ => 0, fun _ => 0⟩, [], [], [], ⟨{ lim := ⟨0, 0, 0, 0⟩, init := true }, .idle⟩,
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
    let h ← tableOf (← field j "H")
    let ids ← tableOf (← field j "ID")
    let o : Oracle := ⟨fun x => (h.get? x).getD (2 ^ 200), fun x => (ids.get? x).getD (2 ^ 200)⟩
    let li ← limOf (← field j "limI")
    let lr ← limOf (← field j "limR")
    let cs : Case := ⟨← natF j "id", o, ← itemList (← field j "A"), ← itemList (← field j "B"),
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

end Vinc.TraceReconcile
