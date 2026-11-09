import Vinc.Json
import Vinc.ConnectMailbox

/-!
# Replay of the mailbox trace

The replay half of the trace validation of `Mailbox` (the Rust test `trace_connect_mailbox`, the TLA+ half is
`TraceConnectMailbox.tla`). Every recorded call is replayed through the Lean functions the theorems of
`ConnectMailbox.lean` are about (`push`, `pop`, `sweep`, `clear`) and any difference exits with an error naming the line:
the answer, the sequence number, the number dropped, the first flag, the messages and bytes held for the member, and
every counter.
-/

namespace Vinc.TraceConnectMailbox
open Vinc.Json Vinc.ConnectMailbox

structure W where
  c : Cfg := ⟨0, 1, 0, 0, 0⟩
  mb : MB := MB.empty

instance : Inhabited W := ⟨{}⟩

def statsOf (s : Stats) : List Nat :=
  [s.stored, s.delivered, s.dropped, s.droppedBytes, s.expired, s.oversize, s.members]

def pending (mb : MB) (k : Nat) : Nat × Nat :=
  match lookup k mb.held with
  | some h => (h.count, h.used)
  | none => (0, 0)

def seen (j : J) (mb : MB) : Except String Unit := do
  check (statsOf mb.st == (← natList (← field j "st"))) s!"counters: model {statsOf mb.st}, code {← natList (← field j "st")}"

def seenNode (j : J) (mb : MB) : Except String Unit := do
  let (cnt, used) := pending mb (← natF j "node")
  check (cnt == (← natF j "pc") && used == (← natF j "pu")) s!"held: model ({cnt}, {used}), code ({← natF j "pc"}, {← natF j "pu"})"
  seen j mb

def replayEvent (j : J) (w : W) : Except String W := do
  match (← strF j "t") with
  | "mbnew" =>
    pure { c := ⟨← natF j "h", ← natF j "b", ← natF j "n", ← natF j "age", ← natF j "maxpkt"⟩, mb := MB.empty }
  | "mpush" =>
    let (mb, r) := push w.c (← natF j "now") w.mb (← natF j "node") (← natF j "src") (← natF j "flag") (← natF j "len")
    match ← strF j "res", r with
    | "stored", .stored s d f =>
      check (s == (← natF j "seq") && d == (← natF j "dropped") && f == (← boolF j "first")) s!"push: model seq {s} dropped {d} first {f}"
    | "toolarge", .tooLarge => pure ()
    | "noslot", .noSlot => pure ()
    | e, _ => throw s!"push: the code answered {e}, the model differs"
    seenNode j mb
    pure { w with mb := mb }
  | "mpop" =>
    let (mb, r) := pop w.c (← natF j "now") w.mb (← natF j "node") (← natF j "max")
    match ← boolF j "got", r with
    | true, some m =>
      check (m.src == (← natF j "src") && m.flag == (← natF j "flag") && m.len == (← natF j "len") &&
        m.seq == (← natF j "seq") && m.t == (← natF j "mt")) "pop: a different message than the model's"
    | false, none => pure ()
    | _, _ => throw "pop: the code and the model disagree on whether a message came out"
    seenNode j mb
    pure { w with mb := mb }
  | "msweep" =>
    let mb := sweep w.c (← natF j "now") w.mb
    seen j mb
    pure { w with mb := mb }
  | "mclear" =>
    let mb := clear w.mb (← natF j "node")
    seen j mb
    pure { w with mb := mb }
  | t => throw s!"unknown mailbox event {t}"

/-- The tags this module replays. -/
def isTag (t : String) : Bool := ["mbnew", "mpush", "mpop", "msweep", "mclear"].contains t

end Vinc.TraceConnectMailbox
