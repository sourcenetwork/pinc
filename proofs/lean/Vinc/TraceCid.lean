import Vinc.Json
import Vinc.TransportCid

/-!
# Replay of the connection id traces

The Lean half of the trace validation of the connection id tables (`conn/cid.rs`), the port of
`proofs/tla/TraceCid.tla`. It reads the `txcid` events written by the Rust test `trace_cid` and replays every call
through the functions of `Vinc.TransportCid`: the table the model computes must be the table recorded, slot by
slot, with the counters and the epoch, and so must the index a claim returns and the answers of a query. The code
does not show how many ids of the window it handed out again (`ru`): the model carries the count, and a wrong one
shows as a wrong index at the next claim past the window.
-/

namespace Vinc.TraceCid
open Vinc.Json Vinc.TransportCid

def isTag (t : String) : Bool := t == "txcid"

def entOf (j : J) : Except String (Option E) := do
  match j.arr? with
  | some #[i, u, s] =>
    match i.int?, u.nat?, s.bool? with
    | some i, some u, some s => pure (if i < 0 then none else some ⟨i.toNat, u, s⟩)
    | _, _, _ => throw "bad slot"
  | _ => throw "bad slot"

/-- The slots a recorded view shows. -/
def slotsOf (j : J) : Except String (List (Option E)) := do
  match (← field j "ent").arr? with
  | some a => a.toList.mapM entOf
  | none => throw "ent is not an array"

def view (c : C) : List (Option E) := (List.range slots).map c.ent

def same (c : C) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  let ents ← slotsOf v
  check (view c == ents) s!"{what}: the model holds {repr (view c)}, the code recorded {repr ents}"
  check (c.hi == (← natF v "hi") && c.tick == (← natF v "tick") && c.ns == (← natF v "ns") && c.cf == (← natF v "cf"))
    s!"{what}: the counters differ"
  check (c.sec == (← boolF v "sec") && c.fr == (← boolF v "fr")) s!"{what}: the flags differ"
  check (epoch c == (← natF v "epoch")) s!"{what}: the epoch differs"

def replayEvent (j : J) (c : C) : Except String C := do
  let op ← strF j "op"
  match op with
  | "init" => let c2 : C := {}; same c2 j "init"; pure c2
  | "frem" => let c2 := setFirstRemote c; same c2 j "frem"; pure c2
  | "install" => let c2 := (install c).1; same c2 j "install"; pure c2
  | "auth" => let c2 := (auth c (← natF j "k")).1; same c2 j "auth"; pure c2
  | "claim" =>
    let (c2, r) := claim c
    check ((r.map (fun k => (k : Int))).getD (-1) == (← intF j "k")) "claim: the index differs"
    same c2 j "claim"
    pure c2
  | "conf" => let c2 := confirm c (← natF j "k"); same c2 j "conf"; pure c2
  | "query" =>
    same c j "query"
    check ((held c).length + 1 == (← natF j "lc")) "query: the number of ids accepted differs"
    match (← field j "has").arr? with
    | some a =>
      for e in a do
        match e.arr? with
        | some #[p, b] =>
          match p.nat?, b.bool? with
          | some p, some b => check (isLocal c p == b) s!"query: is_local {p} differs"
          | _, _ => throw "bad probe"
        | _ => throw "bad probe"
    | none => throw "has is not an array"
    match (← field j "usable").arr? with
    | some a =>
      for e in a do
        match e.arr? with
        | some #[p, b] =>
          match p.nat?, b.bool? with
          | some p, some b => check (remoteUsable c p == b) s!"query: remote_usable {p} differs"
          | _, _ => throw "bad probe"
        | _ => throw "bad probe"
    | none => throw "usable is not an array"
    pure c
  | _ => throw s!"unknown connection id op {op}"

end Vinc.TraceCid
