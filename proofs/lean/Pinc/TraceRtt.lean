import Pinc.Json
import Pinc.CoreRtt

/-!
# Replay of the node round trip traces

The Lean half of the trace validation of the node's round trips (`pinc-core` `rtt.rs`), the port of
`proofs/tla/TraceRtt.tla`. It reads the `corr` events written by the Rust test `trace_rtt` (every `u64` is four
16-bit limbs, an absent value is `[]`) and replays every call through `Pinc.CoreRtt.handshake`, `restore`, `peak`
and `timeout`: the peers (in order, with their values while the table holds at most 8), the average, the peak and
the floor the model computes must be the recorded ones, and so must the answer of `restore_peer`, the readers for
four peers (`krtt`, `first_resend`, `remembered_for`, `hub_resend`), `thin_node` and `thin`. The times run up to
`u64::MAX`, so every saturating step is exercised.
-/

namespace Pinc.TraceRtt
open Pinc.Json Pinc.CoreRtt

def isTag (t : String) : Bool := t == "corr"

def limbsOf (j : J) : Except String Nat := do
  match ← natList j with
  | [a, b, c, d] =>
    check (a < 65536 && b < 65536 && c < 65536 && d < 65536) "a limb is out of range"
    pure (a + 65536 * (b + 65536 * (c + 65536 * d)))
  | _ => throw "expected four limbs"

def optLimbs (j : J) : Except String (Option Nat) := do
  match j.arr? with
  | some a => if a.size == 0 then pure none else pure (some (← limbsOf j))
  | none => throw "expected a value or []"

def lm (j : J) (k : String) : Except String Nat := do limbsOf (← field j k)

structure W where
  r : R := {}
  cap : Nat := 0

def arrOf (j : J) : Except String (List J) :=
  match j.arr? with
  | some a => pure a.toList
  | none => throw "expected an array"

/-- The recorded state and readers against the model's. -/
def same (m : R) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  let len ← natF v "len"
  let peers ← natList (← field v "peers")
  check (m.tab.length == len && keys m.tab == peers) s!"{what}: the model's peers are {repr (keys m.tab)}, the code's {repr peers}"
  if len ≤ 8 then
    let tab ← (← arrOf (← field v "tab")).mapM fun e => do
      match ← arrOf e with
      | [p, x] => pure ((← natN p), ← limbsOf x)
      | _ => throw "an entry has not two parts"
    check (m.tab == tab) s!"{what}: the model's table is {repr m.tab}, the code's {repr tab}"
  check (m.lrtt == (← lm v "lrtt")) s!"{what}: the model's average is {m.lrtt}"
  check (m.tgr == (← lm v "tgr")) s!"{what}: the model's peak is {m.tgr}"
  check (m.floor == (← lm v "floor")) s!"{what}: the model's floor is {m.floor}"
  check (thinNode m == (← boolF v "tn")) s!"{what}: thin_node differs"
  for e in (← arrOf (← field v "q")) do
    match ← arrOf e with
    | [p, k, f, rm, h] =>
      let p ← natN p
      check (krtt m p == (← optLimbs k)) s!"{what}: krtt of {p}"
      check (firstResend m p == (← limbsOf f)) s!"{what}: first_resend of {p}: the model computes {firstResend m p}"
      check (remembered m p == (← optLimbs rm)) s!"{what}: remembered_for of {p}"
      check (hub m p == (← optLimbs h)) s!"{what}: hub_resend of {p}"
    | _ => throw "a reader entry has not five parts"
  match ← arrOf (← field v "th") with
  | [s, mn, b] =>
    let b ← match b.bool? with
      | some b => pure b
      | none => throw "thin is not a boolean"
    check (thin m (← limbsOf s) (← limbsOf mn) == b) s!"{what}: thin differs"
  | _ => throw "thin has not three parts"
where
  natN (j : J) : Except String Nat :=
    match j.nat? with
    | some n => pure n
    | none => throw "expected a number"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let w := { w with r := {}, cap := ← natF j "cap" }
    same w.r j "init"
    pure w
  | "hs" =>
    let r2 := handshake w.cap (← natF j "p") (← lm j "x") w.r
    same r2 j "hs"
    pure { w with r := r2 }
  | "restore" =>
    let (ok, r2) := restore w.cap (← natF j "p") (← lm j "x") w.r
    check (ok == (← boolF j "ok")) "restore: the answer differs"
    same r2 j "restore"
    pure { w with r := r2 }
  | "peak" =>
    let r2 := peak (← lm j "x") w.r
    same r2 j "peak"
    pure { w with r := r2 }
  | "timeout" =>
    let r2 := timeout w.r
    same r2 j "timeout"
    pure { w with r := r2 }
  | op => throw s!"unknown round trip op {op}"

end Pinc.TraceRtt
