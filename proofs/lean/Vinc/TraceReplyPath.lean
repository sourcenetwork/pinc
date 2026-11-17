import Vinc.Json
import Vinc.TransportPath

/-!
# Replay of the reply path traces

The Lean half of the trace validation of the path a dialing side's handshake reply arrives on and of its path table
(`conn/recv.rs`, `conn/drive.rs` `follow_reply`, `conn/path.rs`), the port of `proofs/tla/TraceReplyPath.tla`. It
reads the `rp` events written by the Rust test `trace_reply_path` and replays every call through the functions of
`Vinc.TransportPath`: the table recorded after it (the held paths in slot order and the active one), whether the
session is established, whether the round trip has a sample and the dropped count must be the model's, and so must
whether `add_path` took the path and what `remove_path` answered.
-/

namespace Vinc.TraceReplyPath
open Vinc.Json Vinc.TransportPath

def isTag (t : String) : Bool := t == "rp"

/-- The table's places and the dialing side the replay carries. -/
structure W where
  np : Nat := 4
  c : C := dial 1

/-- What the recorder shows of a connection: the held paths (id, validated, relay) in slot order, the active path's id
(0 for none), established, the round trip has a sample, the dropped count. -/
abbrev View := List (Nat × Bool × Bool) × Nat × Bool × Bool × Nat

def view (np : Nat) (c : C) : View :=
  ((List.range np).filterMap (fun j => (c.t j).map (fun p => (p.id, p.v, p.r))), ((c.t c.act).map P.id).getD 0,
    decide (c.hs = .done), c.smp, c.hd)

def pathsOf (j : J) : Except String (List (Nat × Bool × Bool)) := do
  match j.arr? with
  | some a => a.toList.mapM fun e => do pure (← natF e "id", ← boolF e "v", (← strF e "kind") == "relay")
  | none => throw "paths: expected an array"

def viewOf (v : J) : Except String View := do
  pure (← pathsOf (← field v "paths"), ← natF v "act", ← boolF v "est", ← boolF v "smp", ← natF v "hd")

def kindOf : String → Except String Kind
  | "none" => pure .none
  | "bad" => pure .bad
  | "other" => pure .other
  | "rej" => pure .rej
  | "pend" => pure .pend
  | "auth" => pure .auth
  | k => throw s!"unknown kind {k}"

def keyOf : String → Except String KeyR
  | "ok" => pure .ok
  | "more" => pure .more
  | "bad" => pure .bad
  | r => throw s!"unknown key answer {r}"

def removed : Nat → String
  | 0 => "ok"
  | 1 => "unknown"
  | _ => "active"

def replayEvent (j : J) (w : W) : Except String W := do
  let v ← field j "v"
  let rec' ← viewOf v
  let smp ← boolF v "smp"
  let upd (np : Nat) (c : C) (what : String) : Except String W := do
    let mine := view np c
    if mine == rec' then pure { np, c }
    else throw s!"{what}: the model computes {repr mine}, the code recorded {repr rec'}"
  match ← strF j "op" with
  | "init" => upd (← natF j "np") (dial (← natF j "id") ((← strF j "kind") == "relay")) "init"
  | "add" =>
    let (c2, ok) := addPath w.np w.c (← natF j "id")
    check (ok == ((← strF j "r") == "ok")) "add: whether the path was taken differs"
    upd w.np c2 "add"
  | "rm" =>
    let (c2, r) := removePath w.np w.c (← natF j "id")
    check (removed r == (← strF j "r")) "rm: the answer differs"
    upd w.np c2 "rm"
  | "rx" => upd w.np (rx false w.np w.c (← natF j "id") (← kindOf (← strF j "k")) (← boolF j "coal") smp) "rx"
  | "key" => upd w.np (key w.np w.c (← keyOf (← strF j "r")) smp) "key"
  | op => throw s!"unknown reply path op {op}"

end Vinc.TraceReplyPath
