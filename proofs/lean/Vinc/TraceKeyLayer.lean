import Vinc.Json
import Vinc.TraceKeyRoll
import Vinc.KeyRollSysStep

/-!
# Replay of the key layer traces

The Lean half of the trace validation of the flip and hold layer of the key roll (`conn/keys.rs`, the sending and
receiving paths that call it, and `Roll` under it), the port of `proofs/tla/TraceKeyLayer.tla`. It reads the `kl`
events written by the Rust test `trace_keylayer` and replays every one through the functions the theorems of
`Vinc.KeyRollSys` are about: `beginNode` (`roll_tick`), `Node.poll` and the packet number (a packet sealed),
`Node.afterRecv`, `acts` and `rekeyRx` (a packet received), `requeueUpd` and `reqLostUpd` (loss detection).

A run (`init`) starts the two nodes of the model at the packet numbers the connections showed. Keys, shares and
echoes are ids; the replay keeps one bijection between ids and the symbolic terms of the model (`Vinc.KeyRoll.T`).
After every step the state the model computes must be the state recorded: the phase bits, the sending, staged,
current, previous and next keys, the floor and the hold deadline, the packet numbers, the roll machine and the
REKEY message waiting.
-/

namespace Vinc.TraceKeyLayer
open Vinc.Json Vinc.KeyRoll Vinc.KeyRollSys Vinc.TraceKeyRoll

instance : Inhabited Node := ⟨Node.init false⟩

/-- The replay state of a run: its number, the two nodes (empty outside a run) and the oracle. -/
structure KL where
  run : Nat := 0
  nd : Array Node := #[]
  om : List (T × Int) := []

/-- The message of a packet from the recorded ids (the ghost field is not recorded). -/
def msgOf (om : List (T × Int)) (k : Nat) (sh to : Int) (spn : Nat) : Except String (Option Msg) := do
  let term (id : Int) : Except String T :=
    match om.find? (·.2 == id) with
    | some p => pure p.1
    | none => throw s!"id {id} was never produced"
  match k with
  | 0 => pure none
  | 1 => pure (some (Msg.req (← term sh)))
  | _ => pure (some ⟨true, ← term sh, spn, ← term to, .junk⟩)

def msgPairs (m : Option Msg) (k : Nat) (sh to : Int) : List (T × Int) :=
  match m with
  | none => []
  | some m => (m.share, sh) :: (if k == 2 then [(m.to, to)] else [])

def msgShape (m : Option Msg) (k : Nat) (spn : Nat) : Bool :=
  match m with
  | none => k == 0
  | some m => k != 0 && (m.answer == (k == 2)) && (k != 2 || m.spn == spn)

def opt (t : Option T) (id : Int) : List (T × Int) :=
  match t with | some t => [(t, id)] | none => []

/-- The terms of a node that its recorded view names. -/
def viewPairs (s : Node) (v : J) : Except String (List (T × Int)) := do
  let stg := s.stg.map (·.sec)
  let prev := s.prev.map (·.k.sec)
  let nxt := s.nxt.map (·.k.sec)
  let pend := s.roll.pending.map (·.share)
  let last := s.roll.last
  let lastId ← intF v "last"
  let lastSh ← intF v "lastsh"
  pure ([(s.sk.sec, ← intF v "sk"), (s.cur.sec, ← intF v "cur")] ++ opt stg (← intF v "stg") ++ opt prev (← intF v "prev")
    ++ opt nxt (← intF v "next") ++ opt pend (← intF v "pend")
    ++ (match last with
        | some (sh, a) => [(sh, lastId), (a.share, lastSh)]
        | none => [])
    ++ msgPairs s.out (← natF v "ok") (← intF v "osh") (← intF v "oto")
    ++ msgPairs s.lastAns (← natF v "lk") (← intF v "lsh") (← intF v "lto"))

/-- The state recorded is the state the model computed. -/
def viewShape (s : Node) (v : J) : Except String Unit := do
  check (s.sph == (← boolF v "sph") && s.rph == (← boolF v "rph") && s.first == (← natF v "first") &&
    s.npn == (← natF v "npn")) "view: phase bits or numbers"
  check (s.roll.isIdle == (← boolF v "idle") && s.roll.rolls == (← natF v "rolls")) "view: roll machine"
  check (s.stg.isNone == ((← intF v "stg") == -1)) "view: staged sending key"
  check (s.prev.isNone == ((← intF v "prev") == -1)) "view: previous key"
  match s.prev with
  | some pv => check (pv.dl == (← natF v "prevdl")) "view: hold deadline"
  | none => pure ()
  check (s.nxt.isNone == ((← intF v "next") == -1)) "view: next key"
  match s.nxt with
  | some x => check (x.floor == (← natF v "floor")) "view: floor"
  | none => pure ()
  check (s.roll.pending.isNone == ((← intF v "pend") == -1)) "view: pending request"
  check (s.roll.last.isNone == ((← intF v "last") == -1)) "view: last answered"
  check (s.reqAt.isNone == ((← intF v "reqat") == -1)) "view: request time"
  match s.reqAt with
  | some t => check (t == (← natF v "reqat")) "view: request time value"
  | none => pure ()
  check (msgShape s.out (← natF v "ok") (← natF v "ospn")) "view: waiting message"
  check (msgShape s.lastAns (← natF v "lk") (← natF v "lspn")) "view: last answer"

/-- Add pairs to the oracle one by one: each must agree with what is there (equal terms, equal ids). -/
def bindAll (om : List (T × Int)) (ps : List (T × Int)) : Except String (List (T × Int)) :=
  ps.foldlM (fun om p => bind om p.1 p.2) om

/-- The node `s` is the node recorded in `v`; returns the oracle with its terms added. -/
def viewOK (om : List (T × Int)) (s : Node) (v : J) (extra : List (T × Int)) : Except String (List (T × Int)) := do
  viewShape s v
  bindAll om ((← viewPairs s v) ++ extra)

def selCode : Sel → Nat
  | .cur => 0 | .prev => 1 | .next => 2 | .err => 3

/-- Parameters for the functions of the model: only the probe timeout is read. -/
def params (pto : Nat) : Params := ⟨pto, fun _ => 0, 0, false⟩

def nodeOf (st : KL) (n : Nat) : Node := st.nd[n]!

def setNodeAt (st : KL) (n : Nat) (s : Node) : KL := { st with nd := st.nd.set! n s }

/-- One event, against the model state; returns the new state. -/
def replayEvent (j : J) (st : KL) : Except String KL := do
  let op ← strF j "op"
  let inRun : Except String Unit := do check (st.run == (← natF j "run")) s!"event of run {← natF j "run"} outside run {st.run}"
  match op with
  | "init" =>
    check (st.run == 0) "init inside a run"
    let va ← field j "a"
    let vb ← field j "b"
    let n0 := { Node.init false with npn := ← natF va "npn", first := ← natF va "first" }
    let n1 := { Node.init true with npn := ← natF vb "npn", first := ← natF vb "first" }
    let om ← viewOK [] n0 va []
    let om ← viewOK om n1 vb []
    pure ⟨← natF j "run", #[n0, n1], om⟩
  | "begin" =>
    inRun
    let n ← natF j "n"
    let s := nodeOf st n
    check (s.stg.isNone && s.nxt.isNone && s.roll.isIdle) "begin: a roll cannot start now"
    let s2 := beginNode s (n == 1)
    let om ← viewOK st.om s2 (← field j "v") []
    pure { setNodeAt st n s2 with om := om }
  | "send" =>
    inRun
    let n ← natF j "n"
    let s0 := nodeOf st n
    let k ← natF j "mk"
    let now ← natF j "now"
    let pto ← natF j "pto"
    let q := if k != 0 then s0.poll now pto else (none, s0)
    check (k == 0 || q.1.isSome) "send: no message to carry"
    check (q.2.sph == (← boolF j "ph") && q.2.npn == (← natF j "pn")) "send: header"
    check (msgShape q.1 k (← natF j "mspn")) "send: message"
    let s2 := { q.2 with npn := q.2.npn + 1 }
    let extra := (q.2.sk.sec, ← intF j "key") :: msgPairs q.1 k (← intF j "msh") (← intF j "mto")
    let om ← viewOK st.om s2 (← field j "v") extra
    pure { setNodeAt st n s2 with om := om }
  | "recv" =>
    inRun
    let n ← natF j "n"
    let s0 := nodeOf st n
    let k ← natF j "mk"
    let msh ← intF j "msh"
    let mto ← intF j "mto"
    let m ← msgOf st.om k msh mto (← natF j "mspn")
    let key ← intF j "key"
    let sec ← match st.om.find? (·.2 == key) with
      | some p => pure p.1
      | none => throw s!"recv: key {key} was never produced"
    let p : Pkt := ⟨n == 0, ← boolF j "ph", ← natF j "pn", sec, m⟩
    let forged ← boolF j "forged"
    let now ← natF j "now"
    let P := params (← natF j "pto")
    let rx := s0.recvKeys p forged now P.pto
    let (s1, proc) := s0.afterRecv P p forged now
    check ((← natF j "slot") == selCode rx.sel) "recv: key chosen"
    check ((← boolF j "opened") == rx.acc) "recv: opened"
    check ((← boolF j "dup") == (rx.acc && !proc)) "recv: repeat"
    check ((← boolF j "promoted") == (rx.acc && rx.sel == .next)) "recv: promotion"
    let s2 :=
      match m with
      | some msg => if proc && acts msg (s0.rxSel P p forged now) then (rekeyRx s1 msg (n == 1) p.sec.depth).s else s1
      | none => s1
    let om ← viewOK st.om s2 (← field j "v") []
    pure { setNodeAt st n s2 with om := om }
  | "requeue" =>
    inRun
    let n ← natF j "n"
    let s := nodeOf st n
    pure (setNodeAt st n (if s.out.isNone then { s with out := s.lastAns } else s))
  | "rlost" =>
    inRun
    let n ← natF j "n"
    pure (setNodeAt st n { nodeOf st n with reqAt := none })
  | "end" =>
    inRun
    pure {}
  | _ => throw s!"unknown key layer op {op}"

end Vinc.TraceKeyLayer
