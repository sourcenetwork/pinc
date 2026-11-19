import Pinc.Json
import Pinc.CoreKeepalive

/-!
# Replay of the keepalive traces

The Lean half of the trace validation of the keepalive schedule (`pinc-core` `keepalive.rs`), the port of
`proofs/tla/TraceKeepalive.tla`. It reads the `cka` events written by the Rust test `trace_keepalive` (every `u64` is
four 16-bit limbs, an absent time is `[]`) and replays every call through `Pinc.CoreKeepalive.plan` and
`standbyDue`: the ping and the review moment the model computes must be the recorded ones. The times run up to
`u64::MAX`, so every saturating addition is exercised.
-/

namespace Pinc.TraceKeepalive
open Pinc.Json Pinc.CoreKeepalive

def isTag (t : String) : Bool := t == "cka"

def limbsOf (j : J) : Except String Nat := do
  match ← natList j with
  | [a, b, c, d] =>
    check (a < 65536 && b < 65536 && c < 65536 && d < 65536) "a limb is out of range"
    pure (a + 65536 * (b + 65536 * (c + 65536 * d)))
  | _ => throw "expected four limbs"

def time (j : J) (k : String) : Except String Nat := do limbsOf (← field j k)

/-- A recorded optional time: `[]` for none. -/
def optTime (j : J) (k : String) : Except String (Option Nat) := do
  let v ← field j k
  match v.arr? with
  | some a => if a.size == 0 then pure none else pure (some (← limbsOf v))
  | none => throw s!"field {k} is not a time"

def roleOf : String → Except String Role
  | "hub" => pure .hub
  | "member" => pure .member
  | "other" => pure .other
  | r => throw s!"unknown role {r}"

def replayEvent (j : J) : Except String Unit := do
  match ← strF j "op" with
  | "plan" =>
    let x : Inputs := {
      role := ← roleOf (← strF j "role"), dialer := ← boolF j "dialer", direct := ← boolF j "direct",
      now := ← time j "now", lastTx := ← time j "tx", lastRx := ← time j "rx", lastApp := ← time j "app",
      quietUntil := ← time j "qu", inFlight := ← boolF j "flight" }
    let p := plan x
    check (p.ping == (← optTime j "ping")) s!"ping: the model computes {repr p.ping}"
    check (p.review == (← optTime j "review")) s!"review: the model computes {repr p.review}"
  | "standby" =>
    let d := standbyDue (← time j "now") (← time j "tx") (← time j "app")
    check (d == (← optTime j "due")) s!"standby_due: the model computes {repr d}"
  | op => throw s!"unknown keepalive op {op}"

end Pinc.TraceKeepalive
