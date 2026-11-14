import Vinc.Json
import Vinc.TransportCidCode

/-!
# Replay of the connection id traces

The Lean half of the trace validation of the connection id tables (`conn/cid.rs`), the port of
`proofs/tla/TraceCid.tla`. It reads the `txcid` events written by the Rust test `trace_cid` and replays every call
through the code's calls of `Vinc.TransportCidCode` (`installCode`, `authCode`, with the refill loop that passes over
an index whose id the table holds and makes the entry stand for it) and the model's `claim` and `confirm`: the table
computed must be the table recorded, slot by slot, with the counters and the epoch, and so must the index a claim
returns and the answers of a query; after every call the ids of the indices from one below the highest seen to two
above it must be accepted. The first event of a run records, for each index the run reaches, the least index whose id
is the same (0 for the first id): that is `idOf` for the run, and an index past the recorded ones fails the replay.
Where no two indices share an id the code's calls are the model's (`installCode_eq`, `authCode_eq`). The code does not
show how many ids of the window it handed out again (`ru`): the model carries the count, and a wrong one shows as a
wrong index at the next claim past the window.
-/

namespace Vinc.TraceCid
open Vinc.Json Vinc.TransportCid

def isTag (t : String) : Bool := t == "txcid"

/-- The table, and the id of each index of the run being replayed. -/
structure W where
  c : C := {}
  ids : Array Nat := #[0]

/-- The id of index `j` in the run (an index past the recorded ones is refused by `reached` before it matters). -/
def W.idOf (w : W) (j : Nat) : Nat := w.ids.getD j j

/-- Every index the calls can have touched has its id recorded: a refill reaches `hi + 2 * look` at most. -/
def reached (w : W) (c : C) (k : Nat) (what : String) : Except String Unit :=
  check (k < w.ids.size && c.hi + 2 * look < w.ids.size) s!"{what}: index {k} or the refill is past the recorded ids"

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

/-- The trace's probe of index `p`: index 0 is the first id; a derived id exists once the secret is installed. -/
def probe (w : W) (c : C) (p : Nat) : Bool := decide (p = 0) || (c.sec && idLocal w.idOf c (w.idOf p))

/-- The ids of the indices from `hi - look + 1` to `hi + look` (from 1 on) are accepted once the secret is installed. -/
def window (w : W) (c : C) (what : String) : Except String Unit :=
  check (!c.sec || (List.range (2 * look)).all (fun d =>
      let j := c.hi + 1 + d - look
      decide (j = 0) || idLocal w.idOf c (w.idOf j)))
    s!"{what}: an id of the window of the highest index {c.hi} is not accepted"

def step (j : J) (w : W) : Except String W := do
  let op ← strF j "op"
  match op with
  | "init" =>
    let ids ← natList (← field j "ids")
    let w2 : W := { c := {}, ids := ids.toArray }
    check (w2.ids[0]? == some 0) "init: the recorded ids do not start with the first id"
    same w2.c j "init"
    pure w2
  | "frem" => let c2 := setFirstRemote w.c; same c2 j "frem"; pure { w with c := c2 }
  | "install" =>
    let c2 := (installCode w.idOf w.c).1
    reached w c2 0 "install"
    same c2 j "install"
    pure { w with c := c2 }
  | "auth" =>
    let k ← natF j "k"
    let c2 := (authCode w.idOf w.c k).1
    reached w c2 k "auth"
    same c2 j "auth"
    pure { w with c := c2 }
  | "claim" =>
    let (c2, r) := claim w.c
    check ((r.map (fun k => (k : Int))).getD (-1) == (← intF j "k")) "claim: the index differs"
    same c2 j "claim"
    pure { w with c := c2 }
  | "conf" => let c2 := confirm w.c (← natF j "k"); same c2 j "conf"; pure { w with c := c2 }
  | "query" =>
    let c := w.c
    same c j "query"
    check ((held c).length + 1 == (← natF j "lc")) "query: the number of ids accepted differs"
    match (← field j "has").arr? with
    | some a =>
      for e in a do
        match e.arr? with
        | some #[p, b] =>
          match p.nat?, b.bool? with
          | some p, some b =>
            reached w c p "query"
            check (probe w c p == b) s!"query: is_local {p} differs"
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
    pure w
  | _ => throw s!"unknown connection id op {op}"

def replayEvent (j : J) (w : W) : Except String W := do
  let w2 ← step j w
  window w2 w2.c (← strF j "op")
  pure w2

end Vinc.TraceCid
