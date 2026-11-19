import Pinc.Json
import Pinc.CoreNodeBackoff

/-!
# Replay of the failed-dial table traces

The Lean half of the trace validation of the node's table of failed dials (`pinc-node` `io.rs`), the port of
`proofs/tla/TraceNodeBackoff.tla`. It reads the `nobo` events written by the Rust test `trace_node_backoff` and
replays every call through `Pinc.NodeBackoff.backoff`, `denyBack` and `window`: the entry of the peer and the size
of the table the model computes must be the ones recorded, and so must the answer of the guard; a dump of the whole
table must be the model's. Times and waits are four 16-bit limbs, up to `u64::MAX`.

One run drives a real node whose session table is full: a `shed` (our dial of a hub came up and the table shed the
session) is replayed through `backoff`, with no entry recorded (the node's table is a private field), and each
`duty` (a duty pass: `dial_peer` of the hub, then the prune) must have dialed the hub exactly when the model's
`window` is open, and is replayed through `prune`.
-/

namespace Pinc.TraceNodeBackoff
open Pinc.Json Pinc.NodeBackoff

def isTag (t : String) : Bool := t == "nobo"

structure W where
  f : Tab := []
  hubs : List Nat := []
  max : Nat := 0

/-- A `u64` as four 16-bit limbs, least significant first. -/
def limbs (j : J) : Except String Nat := do
  match ← natList j with
  | [a, b, c, d] => pure (a + 65536 * (b + 65536 * (c + 65536 * d)))
  | _ => throw "expected four limbs"

/-- The recorded entry of the peer: `[]` for none, else `[until, wait]`. -/
def entryOf (j : J) : Except String (Option (Nat × Nat)) := do
  match j.arr? with
  | some a =>
    match a.toList with
    | [] => pure none
    | [u, b] => pure (some (← limbs u, ← limbs b))
    | _ => throw "an entry has not two parts"
  | none => throw "expected an entry"

def same (f : Tab) (p : Nat) (j : J) (what : String) : Except String Unit := do
  let e ← entryOf (← field j "e")
  check (get f p == e) s!"{what}: the model computes {repr (get f p)}, the code recorded {repr e}"
  check (f.length == (← natF j "len")) s!"{what}: the table has {f.length} entries in the model, {← natF j "len"} recorded"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    check ((← natF j "max") == 4096) "init: the bound is not 4096"
    check ((← limbs (← field j "first")) == first) "init: BACKOFF_FIRST differs"
    check ((← limbs (← field j "hubcap")) == hubCap) "init: BACKOFF_HUB_CAP differs"
    check ((← limbs (← field j "cap")) == cap) "init: BACKOFF_CAP differs"
    check ((← limbs (← field j "dfirst")) == denyFirst) "init: DENY_FIRST differs"
    check ((← limbs (← field j "dcap")) == denyCap) "init: DENY_CAP differs"
    pure { f := [], hubs := ← natList (← field j "hubs"), max := 4096 }
  | "backoff" =>
    let p ← natF j "peer"
    let f2 := (backoff w.max (w.hubs.contains p) w.f (← limbs (← field j "now")) p).2
    same f2 p j "backoff"
    pure { w with f := f2 }
  | "deny" =>
    let p ← natF j "peer"
    let f2 := (denyBack w.max w.f (← limbs (← field j "now")) p).2
    same f2 p j "deny"
    pure { w with f := f2 }
  | "gate" =>
    let p ← natF j "peer"
    check ((!window w.f (← limbs (← field j "now")) p) == (← boolF j "ok")) "gate: the answer differs"
    same w.f p j "gate"
    pure w
  | "shed" =>
    let p ← natF j "peer"
    pure { w with f := (backoff w.max (w.hubs.contains p) w.f (← limbs (← field j "now")) p).2 }
  | "duty" =>
    let p ← natF j "peer"
    let now ← limbs (← field j "now")
    check ((!window w.f now p) == (← boolF j "dialed")) "duty: the node's dial differs from the model's window"
    pure { w with f := prune w.f now }
  | "dump" =>
    let rows ← match (← field j "entries").arr? with
      | some a => a.toList.mapM fun r => do
          match ← (do match r.arr? with
                     | some x => pure x.toList
                     | none => throw "expected a row") with
          | [p, u, b] =>
            let p ← match p.nat? with
              | some n => pure n
              | none => throw "a peer is not a number"
            pure (p, ← limbs u, ← limbs b)
          | _ => throw "a row has not three parts"
      | none => throw "expected the entries"
    check (rows.length == w.f.length) "dump: the table has another size"
    for (p, u, b) in rows do
      check (get w.f p == some (u, b)) s!"dump: the entry of peer {p} differs"
    pure w
  | op => throw s!"unknown failed-dial op {op}"

end Pinc.TraceNodeBackoff
