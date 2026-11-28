import Pinc.Json
import Pinc.TransportPath

/-!
# Replay of the reply path traces

The Lean half of the trace validation of the path a dialing side's handshake reply arrives on and of its path table
(`conn/recv.rs`, `conn/drive.rs` `follow_reply`, `conn/path.rs`), the port of `proofs/tla/TraceReplyPath.tla`. It
reads the `rp` events written by the Rust test `trace_reply_path` and replays every call through the functions of
`Pinc.TransportPath`: the table recorded after it (the held paths in slot order and the active one), whether the
session is established, whether the round trip has a sample and the dropped count must be the model's, and so must
whether `add_path` took the path and what `remove_path` answered.

While a Reply waits for its verdict the code holds every handshake fragment and applies none, so what a held one
completes shows only when it is tried, inside the key answer that fails: the recorded kind is then `none` (or `rej`
for a reject datagram, which the test tells by its bytes). As `TraceReplyPath.tla` does, the replay then carries every
state the model may be in: the datagram held as each kind, or lost (no room in the hold); a Reply that may have come
with a second message the same fragment completed, held first; and a key answer recorded `ok`, which is the verdict
or a failed verdict whose held message authenticated. A call passes when some carried state computes what the code
recorded; the states that do not are dropped, and the replay fails when none is left. The states carried are at most
seven for each datagram held, as many as the hold had at once, and the same state is carried once.
-/

namespace Pinc.TraceReplyPath
open Pinc.Json Pinc.TransportPath

def isTag (t : String) : Bool := t == "rp"

/-- The table's places and the states of the dialing side the replay carries. -/
structure W where
  np : Nat := 4
  cs : List C := [dial 1]

/-- What the recorder shows of a connection: the held paths (id, validated) in slot order, the active path's id (0 for
none), established, the round trip has a sample, the dropped count. -/
abbrev View := List (Nat × Bool) × Nat × Bool × Bool × Nat

def view (np : Nat) (c : C) : View :=
  ((List.range np).filterMap (fun j => (c.t j).map (fun p => (p.id, p.v))), ((c.t c.act).map P.id).getD 0,
    decide (c.hs = .done), c.smp, c.hd)

def pathsOf (j : J) : Except String (List (Nat × Bool)) := do
  match j.arr? with
  | some a => a.toList.mapM fun e => do pure (← natF e "id", ← boolF e "v")
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

/-- What tells two states of the model apart, over the table's places. -/
def sig (np : Nat) (c : C) :=
  ((List.range np).map c.t, c.act, c.hs, c.rf, c.pend, c.smp, c.hd, c.rp, c.hq)

/-- Each state once, in the order found. -/
def dedup (np : Nat) (cs : List C) : List C :=
  cs.foldl (fun acc c => if acc.any (fun d => sig np d == sig np c) then acc else acc ++ [c]) []

def kinds : List Kind := [.none, .bad, .other, .rej, .pend, .auth]

/-- The states after a datagram on `pid` the code answered `k` (`rx`, see the module comment). -/
def rxNext (np : Nat) (c : C) (pid : Nat) (k : Kind) (coal s : Bool) : List C :=
  if c.hs = .key then
    if k = .none ∨ k = .rej then c :: kinds.map (fun k' => rx false np c pid k' coal s) else []
  else
    let c1 := rx false np c pid k coal s
    if k = .pend then c1 :: kinds.map (fun k' => { c1 with hq := [(pid, k')] }) else [c1]

/-- The states after a key answer the code answered `r` (`key`, see the module comment). -/
def keyNext (np : Nat) (c : C) (r : KeyR) (s : Bool) : List C :=
  (if r = .ok then [KeyR.ok, .bad] else [r]).map (fun r' => key np c r' s)

def removed : Nat → String
  | 0 => "ok"
  | 1 => "unknown"
  | _ => "active"

def replayEvent (j : J) (w : W) : Except String W := do
  let v ← field j "v"
  let rec' ← viewOf v
  let smp ← boolF v "smp"
  let upd (np : Nat) (next : List C) (what : String) : Except String W := do
    let kept := dedup np (next.filter (fun c => view np c == rec'))
    if kept.isEmpty then
      throw s!"{what}: the model computes {repr ((next.map (view np)).take 3)}, the code recorded {repr rec'}"
    else pure { np, cs := kept }
  match ← strF j "op" with
  | "init" => upd (← natF j "np") [dial (← natF j "id")] "init"
  | "add" =>
    let pid ← natF j "id"
    let took := (← strF j "r") == "ok"
    let next := w.cs.filterMap fun c => let a := addPath w.np c pid; if a.2 == took then some a.1 else none
    check (!next.isEmpty) "add: whether the path was taken differs"
    upd w.np next "add"
  | "rm" =>
    let pid ← natF j "id"
    let r ← strF j "r"
    let next := w.cs.filterMap fun c => let a := removePath w.np c pid; if removed a.2 == r then some a.1 else none
    check (!next.isEmpty) "rm: the answer differs"
    upd w.np next "rm"
  | "rx" =>
    let (pid, k, coal) := (← natF j "id", ← kindOf (← strF j "k"), ← boolF j "coal")
    upd w.np (w.cs.flatMap fun c => rxNext w.np c pid k coal smp) "rx"
  | "key" =>
    let r ← keyOf (← strF j "r")
    upd w.np (w.cs.flatMap fun c => keyNext w.np c r smp) "key"
  | op => throw s!"unknown reply path op {op}"

end Pinc.TraceReplyPath
