import Vinc.Json
import Vinc.FacadeStandby

/-!
# Replay of the standby slab traces

The Lean half of the trace validation of the facade's standby slab (`crates/vinc/src/standby.rs`), the port of
`proofs/tla/TraceFacadeStandby.tla`. It reads the `fsb` events written by the Rust test `trace_standby` and replays
every call through `Vinc.FacadeStandby.alloc`, `arm`, `notify`, `baton`, `notifyAll` and `release`: the ticket
handed out, the wakers woken in order, and the slots, the free stack and the queue the model computes must be the
ones recorded. The free stack is recorded as the code's `Vec` holds it (the top last); the model keeps the top first.
-/

namespace Vinc.TraceFacadeStandby
open Vinc.Json Vinc.FacadeStandby

def isTag (t : String) : Bool := t == "fsb"

structure W where
  s : S := {}

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
  let rec' : S := { slots, free := (← natList (← field v "free")).reverse, queue := ← natList (← field v "queue") }
  if decide (m = rec') then pure ()
  else throw s!"{what}: the model computes {repr m}, the code recorded {repr rec'}"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let s : S := {}
    same s j "init"
    pure { s }
  | "alloc" =>
    let (t, s) := alloc w.s
    check (t == (← ticketOf (← field j "out"))) "alloc: another ticket is handed out"
    same s j "alloc"
    pure { s }
  | "arm" =>
    check ((← natList (← field j "woke")).isEmpty) "arm: something was woken"
    let s := arm (← ticketOf (← field j "tk")) (← natF j "w") w.s
    same s j "arm"
    pure { s }
  | "notify" =>
    let (ws, s) := notify (← ticketOf (← field j "tk")) w.s
    check (ws == (← natList (← field j "woke"))) "notify: other wakers are woken"
    same s j "notify"
    pure { s }
  | "baton" =>
    let (ws, s) := baton w.s
    check (ws == (← natList (← field j "woke"))) "baton: other wakers are woken"
    same s j "baton"
    pure { s }
  | "all" =>
    let (ws, s) := notifyAll w.s
    check (ws == (← natList (← field j "woke"))) "notify_all: other wakers are woken"
    same s j "notify_all"
    pure { s }
  | "release" =>
    check ((← natList (← field j "woke")).isEmpty) "release: something was woken"
    let s := release (← ticketOf (← field j "tk")) w.s
    same s j "release"
    pure { s }
  | op => throw s!"unknown standby op {op}"

end Vinc.TraceFacadeStandby
