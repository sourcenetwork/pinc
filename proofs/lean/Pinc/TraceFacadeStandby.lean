import Pinc.Json
import Pinc.FacadeStandby

/-!
# Replay of the standby slab traces

The Lean half of the trace validation of the facade's standby slab (`crates/pinc/src/standby.rs`), the port of
`proofs/tla/TraceFacadeStandby.tla`. It reads the `fsb` events written by the Rust test `trace_standby` and replays
every call through `Pinc.FacadeStandby.alloc`, `arm`, `notify`, `baton`, `notifyAll` and `release`: the ticket
handed out, the wakers woken in order, and the slots, the free stack and the queue of tickets the model computes must
be the ones recorded. The free stack is recorded as the code's `Vec` holds it (the top last); the model keeps the top
first. Beside the slab it keeps the documented order (`Op.order`): every alloc must hand out a ticket no entry of the
queue names, the live entries of the queue must be that order after every call, and every baton must wake what the
order says (`orderWoken`), its oldest armed ticket.
-/

namespace Pinc.TraceFacadeStandby
open Pinc.Json Pinc.FacadeStandby

def isTag (t : String) : Bool := t == "fsb"

structure W where
  s : S := {}
  /-- The documented order: the tickets waiting for the driving role, in the order they were queued. -/
  o : List Ticket := []

def ticketOf (j : J) : Except String Ticket := do
  match ← natList j with
  | [i, g] => pure ⟨i, g⟩
  | _ => throw "expected a ticket of two numbers"

/-- A recorded slot: `[generation, waker (0 for none), queued, live]`. -/
def slotOfJ (j : J) : Except String Slot := do
  match j.arr? with
  | some a =>
    match a.toList with
    | [g, w, q, l] =>
      match g.nat?, w.nat?, q.bool?, l.bool? with
      | some g, some w, some q, some l => pure ⟨g, if w = 0 then none else some w, q, l⟩
      | _, _, _, _ => throw "a slot is not two numbers and two booleans"
    | _ => throw "a slot has not four parts"
  | none => throw "expected a slot"

def same (m : S) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  let slots ← match (← field v "slots").arr? with
    | some a => a.toList.mapM slotOfJ
    | none => throw "expected the slots"
  let queue ← match (← field v "queue").arr? with
    | some a => a.toList.mapM ticketOf
    | none => throw "expected the queue"
  let rec' : S := { slots, free := (← natList (← field v "free")).reverse, queue }
  if decide (m = rec') then pure ()
  else throw s!"{what}: the model computes {repr m}, the code recorded {repr rec'}"

/-- The live entries of the queue are the documented order. -/
def inOrder (s : S) (o : List Ticket) (what : String) : Except String Unit :=
  check (s.queue.filter (valid s.slots) == o) s!"{what}: the live entries of the queue are not the documented order"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let s : S := {}
    same s j "init"
    pure { s, o := [] }
  | "alloc" =>
    let (t, s) := alloc w.s
    check (t == (← ticketOf (← field j "out"))) "alloc: another ticket is handed out"
    check (!w.s.queue.contains t) "alloc: a stale entry of the queue names the ticket handed out"
    same s j "alloc"
    inOrder s w.o "alloc"
    pure { s, o := w.o }
  | "arm" =>
    check ((← natList (← field j "woke")).isEmpty) "arm: something was woken"
    let op := Op.arm (← ticketOf (← field j "tk")) (← natF j "w")
    let s := op.run w.s
    same s j "arm"
    let o := op.order w.s w.o
    inOrder s o "arm"
    pure { s, o }
  | "notify" =>
    let (ws, s) := notify (← ticketOf (← field j "tk")) w.s
    check (ws == (← natList (← field j "woke"))) "notify: other wakers are woken"
    same s j "notify"
    inOrder s w.o "notify"
    pure { s, o := w.o }
  | "baton" =>
    let (ws, s) := baton w.s
    check (ws == (← natList (← field j "woke"))) "baton: other wakers are woken"
    check (ws == orderWoken w.s.slots w.o) "baton: not the oldest armed ticket is woken"
    same s j "baton"
    let o := Op.baton.order w.s w.o
    inOrder s o "baton"
    pure { s, o }
  | "all" =>
    let (ws, s) := notifyAll w.s
    check (ws == (← natList (← field j "woke"))) "notify_all: other wakers are woken"
    same s j "notify_all"
    inOrder s w.o "notify_all"
    pure { s, o := w.o }
  | "release" =>
    check ((← natList (← field j "woke")).isEmpty) "release: something was woken"
    let op := Op.release (← ticketOf (← field j "tk"))
    let s := op.run w.s
    same s j "release"
    let o := op.order w.s w.o
    inOrder s o "release"
    pure { s, o }
  | op => throw s!"unknown standby op {op}"

end Pinc.TraceFacadeStandby
