import Pinc.Json
import Pinc.ReconcileWireMsg

/-!
# Replay of the reconcile wire traces

The Lean half of the trace validation of the wire layer of `pinc-reconcile` (the Rust test `trace_reconcile_wire`,
the TLA+ half is `TraceReconcileWire.tla`). Every recorded call of `put_bound`, `read_bound`, `common_prefix`,
`count`, `put_parts`, `read_parts`, `frame_body` and `first_set_ref`, and the count field and head of the first part
of a message, is replayed through the Lean model (`putBound`, `readBound`, `cpl`, `count`, `putParts`, `readParts`,
`frameBody`, `readHead`, `readBytes`) that `ReconcileWireProofs.lean` and `ReconcileWireMsg.lean` are about. A varint
of 2^30 or more is recorded as 2^30 and compared after the same saturation.
-/

namespace Pinc.TraceReconcileWire
open Pinc.Json Pinc.Reconcile

def reasonStr : Reason → String
  | .frame => "frame" | .truncated => "truncated" | .tag => "tag" | .bound => "bound"
  | .count => "count" | .item => "item" | .state => "state"

def sat (v : Nat) : Nat := min v (2 ^ 30)

def hasF (j : J) (k : String) : Bool := (j.get? k).isSome

def expectErr {α : Type} (j : J) (what : String) (r : Except Reason α) : Except String Unit := do
  let want ← strF j "err"
  match r with
  | .ok _ => throw s!"{what}: the model accepts, the code refused with {want}"
  | .error e => check (reasonStr e == want) s!"{what}: model {reasonStr e}"

/-- The count field and the head of the first part of a message. -/
def parseMsg (msg : List Nat) (mx : Nat) :
    Except Reason (Nat × Bool × Option (Nat × Item × Option Item × Nat)) := do
  let body ← frameBody msg
  let ((cnt, more), rest) ← readParts body
  if cnt = 0 then return (cnt, more, none)
  let ((kind, lo, hi), _, rest') ← readHead [] rest mx
  return (cnt, more, some (kind, lo, hi, body.length - rest'.length))

def replayEvent (j : J) : Except String Unit := do
  match ← strF j "e" with
  | "pb" =>
    let last ← natList (← field j "last")
    let b ← natList (← field j "b")
    let out ← natList (← field j "out")
    check ((putBound last b).1 == out) s!"put_bound {last} {b}: model {(putBound last b).1}, code {out}"
  | "rb" =>
    let last ← natList (← field j "last")
    let inp ← natList (← field j "in")
    let mx ← natF j "mx"
    let r := readBound last inp mx
    if hasF j "ok" then
      let b ← natList (← field j "ok")
      let used ← natF j "used"
      match r with
      | .ok (b', rest) => check (b' == b && inp.length - rest.length == used) s!"read_bound {last} {inp}: model {b'}, code {b}"
      | .error e => throw s!"read_bound {last} {inp}: the model refuses ({reasonStr e}), the code accepts"
    else expectErr j s!"read_bound {last} {inp}" r
  | "cp" =>
    check (cpl (← natList (← field j "a")) (← natList (← field j "b")) == (← natF j "out")) "common_prefix"
  | "ct" =>
    let inp ← natList (← field j "in")
    let r := count inp
    if hasF j "ok" then
      match r with
      | .ok (v, rest) => check (sat v == (← natF j "ok") && inp.length - rest.length == (← natF j "used")) s!"count {inp}"
      | .error e => throw s!"count {inp}: the model refuses ({reasonStr e})"
    else expectErr j s!"count {inp}" r
  | "pp" =>
    let more ← boolF j "more"
    check (putParts (← natF j "cnt") more == (← natList (← field j "out"))) "put_parts"
  | "rp" =>
    let inp ← natList (← field j "in")
    let r := readParts inp
    if hasF j "cnt" then
      match r with
      | .ok ((cnt, more), rest) =>
        check (sat cnt == (← natF j "cnt") && more == (← boolF j "more") && inp.length - rest.length == (← natF j "used"))
          s!"read_parts {inp}"
      | .error e => throw s!"read_parts {inp}: the model refuses ({reasonStr e})"
    else expectErr j s!"read_parts {inp}" r
  | "fb" =>
    let inp ← natList (← field j "in")
    let r := frameBody inp
    if hasF j "ok" then
      match r with
      | .ok body => check (body.length == (← natF j "ok")) s!"frame_body {inp}"
      | .error e => throw s!"frame_body {inp}: the model refuses ({reasonStr e})"
    else expectErr j s!"frame_body {inp}" r
  | "fl" =>
    -- A body of `blen` bytes under a three-byte header: the check of `frameBody` without building the body.
    let hdr ← natList (← field j "hdr")
    let blen ← natF j "blen"
    match hdr with
    | [a, b, c] =>
      let good := (a * 256 + b) * 256 + c == blen
      if hasF j "ok" then check (good && blen == (← natF j "ok")) s!"frame {hdr} {blen}: the model refuses"
      else check (!good && (← strF j "err") == "frame") s!"frame {hdr} {blen}: the model accepts"
    | _ => throw "fl needs a three-byte header"
  | "msg" =>
    let inp ← natList (← field j "in")
    let mx ← natF j "mx"
    let r := parseMsg inp mx
    if hasF j "err" then expectErr j s!"message {inp}" r
    else
      match r with
      | .error e => throw s!"message {inp}: the model refuses ({reasonStr e})"
      | .ok (cnt, more, head) =>
        check (sat cnt == (← natF j "cnt") && more == (← boolF j "more")) s!"message {inp}: count field"
        match head, j.get? "head" with
        | none, none => pure ()
        | some (kind, lo, hi, used), some h =>
          check (kind == (← natF h "kind") && lo == (← natList (← field h "lo")) && used == (← natF h "used"))
            s!"message {inp}: head"
          match hi, h.get? "hi" with
          | none, none => pure ()
          | some x, some y => check (x == (← natList y)) s!"message {inp}: upper bound"
          | _, _ => throw s!"message {inp}: infinity bit"
        | _, _ => throw s!"message {inp}: head presence"
  | "fsr" =>
    let inp ← natList (← field j "in")
    let r : Except Reason (List Nat) := do
      let body ← frameBody inp
      let (n, rest) ← count body
      let (x, _) ← readBytes n rest
      return x
    if hasF j "ok" then
      match r with
      | .ok x => check (x == (← natList (← field j "ok"))) s!"first_set_ref {inp}"
      | .error e => throw s!"first_set_ref {inp}: the model refuses ({reasonStr e})"
    else expectErr j s!"first_set_ref {inp}" r
  | e => throw s!"unknown reconcile wire event {e}"

end Pinc.TraceReconcileWire
