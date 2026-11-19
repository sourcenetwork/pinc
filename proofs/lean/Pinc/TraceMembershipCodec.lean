import Pinc.Json
import Pinc.MembershipCodecBuf

/-!
# Replay of the hub stream codec traces

The replay half of the trace validation of `pinc-membership/src/codec.rs` (the Rust test `trace_membership`, part
`codec`; the TLA+ half is `TraceHubCodec.tla`). Every recorded call of `Frame::parse`, `Frame::read` and
`Frame::encode` is replayed through the Lean functions the codec theorems are about (`Pinc.MemCodec.parse`, `read`,
`encode`): the model must return the frame the code returned, or the refusal of the same class, and the bytes the
code wrote. Any difference exits with an error naming the line.
-/

namespace Pinc.TraceMembershipCodec
open Pinc.Json Pinc.MemCodec

/-- Equality of results, decided. -/
instance exceptDecEq {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .ok _, .error _ => isFalse (by intro e; cases e)
  | .error _, .ok _ => isFalse (by intro e; cases e)

/-- Whether an event belongs to this replay. -/
def isTag (t : String) : Bool := t == "mc"

/-- A u64 recorded as four 16-bit limbs. -/
def limbsN (j : J) : Except String Nat := do
  match ← natList j with
  | [a, b, c, d] => pure (a + b * 65536 + c * 4294967296 + d * 281474976710656)
  | _ => throw "expected four limbs"

def limbsF (j : J) (k : String) : Except String Nat := do limbsN (← field j k)

def aliveOfNat : Nat → Except String Alive
  | 0 => pure .down
  | 1 => pure .alive
  | 2 => pure .left
  | n => throw s!"alive {n}"

def pathOfNat : Nat → Except String Path
  | 0 => pure .session
  | 1 => pure .direct
  | 2 => pure .relay
  | n => throw s!"path {n}"

def errOfStr : String → Except String Err
  | "short" => pure .short
  | "tooLarge" => pure .tooLarge
  | "topic" => pure .topicOnMembership
  | "helloFlag" => pure .helloFlag
  | "helloLen" => pure .helloLen
  | "ackLen" => pure .ackLen
  | "probeLen" => pure .probeLen
  | "deltaLen" => pure .deltaLen
  | "snapFlag" => pure .snapFlag
  | "snapSize" => pure .snapSize
  | "snapNotAlive" => pure .snapNotAlive
  | "aliveByte" => pure .aliveByte
  | "probeCount" => pure .probeCount
  | "probePath" => pure .probePath
  | "downLen" => pure .downLen
  | "bufferSmall" => pure .bufferSmall
  | "topicLong" => pure .topicLong
  | s => throw s!"unknown refusal {s}"

def entryJ (j : J) : Except String Entry := do
  pure ⟨← natList (← field j "m"), ⟨← limbsF j "inc", ← natF j "ver", ← natList (← field j "th")⟩,
    ← aliveOfNat (← natF j "a")⟩

def arrF (j : J) (k : String) : Except String (List J) := do
  match (← field j k).arr? with
  | some a => pure a.toList
  | none => throw s!"field {k} is not an array"

/-- A frame in the trace schema. -/
def frameJ (j : J) : Except String Frame := do
  match ← strF j "k" with
  | "hello" =>
    pure (.hello ⟨← limbsF j "inc", ← natF j "ver", ← natList (← field j "th")⟩ (← boolF j "snap") (← boolF j "homed"))
  | "ack" => pure .ack
  | "probe" => pure .probe
  | "delta" => pure (.delta (← entryJ (← field j "e")))
  | "snap" => pure (.snap (← boolF j "part") (← boolF j "more") (← (← arrF j "es").mapM entryJ))
  | "down" =>
    let prs ← (← arrF j "pr").mapM fun p => do
      pure (Probe.mk (← limbsF p "age") (← pathOfNat (← natF p "path")))
    pure (.down (← natList (← field j "m")) (← limbsF j "inc") ⟨← limbsF j "sil", prs⟩)
  | "other" => pure (.other (← natF j "ty") (← natList (← field j "topic")) (← natList (← field j "rest")))
  | s => throw s!"unknown frame {s}"

def replayEvent (j : J) : Except String Unit := do
  match ← strF j "op" with
  | "parse" =>
    let bytes ← natList (← field j "b")
    match j.get? "ok", j.get? "err" with
    | some f, _ =>
      let f ← frameJ f
      check (decide (parse bytes = .ok f)) s!"parse {bytes}: the model does not return the frame the code returned"
    | _, some _ =>
      let e ← errOfStr (← strF j "err")
      check (decide (parse bytes = .error e)) s!"parse {bytes}: the code refused with {repr e}, the model does not"
    | _, _ => throw "parse needs ok or err"
  | "read" =>
    let bytes ← natList (← field j "b")
    match j.get? "ok", j.get? "more", j.get? "err" with
    | some f, _, _ =>
      let f ← frameJ f
      let n ← natF j "n"
      check (decide (read bytes = .ok (some (f, n)))) s!"read {bytes}: the model does not return the frame and {n} bytes"
    | _, some _, _ => check (decide (read bytes = .ok none)) s!"read {bytes}: the model does not ask for more bytes"
    | _, _, some _ =>
      let e ← errOfStr (← strF j "err")
      check (decide (read bytes = .error e)) s!"read {bytes}: the code refused with {repr e}, the model does not"
    | _, _, _ => throw "read needs ok, more or err"
  | "enc" =>
    let f ← frameJ (← field j "f")
    let cap ← natF j "cap"
    match j.get? "err" with
    | none =>
      let bytes ← natList (← field j "b")
      check (decide (encode cap f = .ok bytes)) s!"encode into {cap} bytes: the model writes other bytes"
    | some _ =>
      let e ← errOfStr (← strF j "err")
      check (decide (encode cap f = .error e)) s!"encode into {cap} bytes: the code refused with {repr e}, the model does not"
  | op => throw s!"unknown codec event {op}"

end Pinc.TraceMembershipCodec
