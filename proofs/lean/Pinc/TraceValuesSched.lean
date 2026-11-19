import Pinc.Json
import Pinc.ValuesSchedSteal
import Pinc.ValuesSchedHoles

/-!
# Replay of the scheduler traces

The Lean half of the trace validation of the work scheduler of the value fetch (`TraceValuesSched.tla` is the TLA+
half). It reads the `vs` events written by the Rust test `trace_values_sched` and replays each one on the model of
`ValuesSchedSteal` and `ValuesSchedHoles`: the wanted groups are `align` of the ranges asked, a top-up's target is
`target`, the choice of the victim of a steal is `etaOf` over the candidates with `idle` and `prate`, its cut is
`keepOf`, a verified group moves the clocks and counters, an eviction returns the share to the queue. The bytes of the
queue, of the providers' lists and the verified wanted bytes are checked to add up at every event.

The replay is exact on `Nat` (the times are `ms * 10^6 + ns`), unlike the TLA+ half which evaluates the same arithmetic
in 32 bits by division with remainder.
-/

namespace Pinc.TraceValuesSched
open Pinc.Json Pinc.ValuesSched

/-- One provider slot. -/
structure PV where
  inA : Bool := false
  a : Nat := 0
  pb : Nat := 0
  pt : Option Nat := none
  lp : Option Nat := none
  deriving Inhabited

/-- The state of a run. `ph`: 0 before a run line or after an end, 1 after `run`, 2 after `start`. -/
structure RS where
  ph : Nat := 0
  run : Nat := 0
  len : Nat := 0
  wanted : Array Bool := #[]
  done : Array Bool := #[]
  vb : Nat := 0
  striped : Bool := false
  q : Nat := 0
  pv : Array PV := #[{}, {}, {}, {}]
  t0 : Nat := 0
  pend : Option (Nat × Nat) := none
  evicted : List Nat := []
  np : Nat := 0
  badroot : Bool := false

def nGroups (len : Nat) : Nat := (len + G - 1) / G

def gsize (g len : Nat) : Nat := min ((g + 1) * G) len - g * G

/-- The bytes of the flagged groups. -/
def bytesOf (flags : Array Bool) (len : Nat) : Nat :=
  (List.range flags.size).foldl (fun acc g => if flags[g]! then acc + gsize g len else acc) 0

/-- The groups of the asked ranges after `align`, or the whole value when none was asked. -/
def wantedFlags (len : Nat) (ranges : List (Nat × Nat)) : Array Bool := Id.run do
  let mut f := Array.replicate (nGroups len) false
  let rs := if ranges.isEmpty then [(0, len)] else ranges
  for (off, l) in rs do
    match align ⟨off, l⟩ len with
    | some a =>
      for g in List.range ((a.off + a.len - 1) / G + 1 - a.off / G) do
        f := f.set! (a.off / G + g) true
    | none => pure ()
  return f

/-- The groups lying wholly inside a verified interval `[s, e)`. -/
def verifiedFlags (len : Nat) (ivs : List (Nat × Nat)) : Array Bool :=
  Array.ofFn (n := nGroups len) fun g =>
    ivs.any fun (s, e) => decide (s ≤ g.val * G ∧ min ((g.val + 1) * G) len ≤ e)

def now (j : J) : Except String Nat := do
  pure ((← natF j "ms") * 1000000 + (← natF j "ns"))

def pairOf (j : J) (k : String) : Except String (List (Nat × Nat)) := do pairList (← field j k)

def sumA (r : RS) : Nat := r.pv.foldl (fun s p => s + p.a) 0

def pend' (r : RS) : Nat := match r.pend with | some (_, b) => b | none => 0

/-- Queue, lists, in-flight tail and verified wanted bytes add up to the wanted bytes (a striped run). -/
def conserved (r : RS) : Bool :=
  !r.striped || r.q + sumA r + pend' r + r.vb == bytesOf r.wanted r.len

def getPV (r : RS) (p : Nat) : Except String PV :=
  match r.pv[p]? with
  | some v => pure v
  | none => throw s!"provider slot {p} is out of range"

def setPV (r : RS) (p : Nat) (v : PV) : RS := { r with pv := r.pv.set! p v }

/-- The eta of slot `s` as a steal candidate at `t` (the thief is `to`); `NOETA` as `none`. -/
def etaAt (r : RS) (s t : Nat) : Option Nat :=
  let p := r.pv[s]!
  etaOf (idle p.lp r.t0 t) p.a (prate p.pt p.pb t)

def isCand (r : RS) (s to t : Nat) : Bool :=
  s != to && r.pv[s]!.inA && match etaAt r s t with | some e => decide (STEAL_ETA_MS ≤ e) | none => false

/-- The victim: the candidate with the greatest eta, the lowest slot among equals (strictly greater replaces). -/
def best (r : RS) (to t : Nat) : Option Nat :=
  (List.range 4).foldl (fun b s =>
    if isCand r s to t then
      match b with
      | none => some s
      | some b' => if (etaAt r s t).getD 0 > (etaAt r b' t).getD 0 then some s else b
    else b) none

def replayEvent (j : J) (r : RS) : Except String RS := do
  let op ← strF j "op"
  match op with
  | "run" =>
    check (r.ph != 1 && r.ph != 2) "run: the previous run did not end"
    let len ← natF j "len"
    let wf := wantedFlags len (← pairOf j "want")
    let vf := verifiedFlags len (← pairOf j "ver")
    let both := Array.ofFn (n := nGroups len) fun g => wf[g.val]! && vf[g.val]!
    pure { run := ← natF j "run", len, wanted := wf, done := vf, vb := bytesOf both len, ph := 1,
           np := (← natList (← field j "provs")).length, badroot := (← natF j "badroot") == 1 }
  | "start" =>
    check (r.ph == 1 && (← natF j "run") == r.run) "start: out of place"
    let missing := Array.ofFn (n := r.wanted.size) fun g => r.wanted[g.val]! && !r.done[g.val]!
    let w ← natF j "wanted"
    check (w == bytesOf missing r.len && 0 < w) s!"start: wanted {w}, model {bytesOf missing r.len}"
    let n ← natF j "prov"
    check (n == min r.np 4 && 1 ≤ n) "start: the providers used"
    let striped := (← natF j "striped") == 1
    check (striped == decide (1 < n)) "start: striped iff more than one provider"
    pure { r with ph := 2, striped, t0 := ← now j, q := if striped then w else 0,
                  pv := (List.range 4).toArray.map fun s =>
                    { inA := decide (s < n), a := if !striped && s == 0 then w else 0 } }
  | "topup" =>
    check (r.ph == 2 && r.striped && (← natF j "run") == r.run) "topup: out of place"
    let p ← natF j "p"
    let v ← getPV r p
    let t ← now j
    let bytes ← natF j "bytes"
    check v.inA "topup: a provider that holds no share"
    let tgt := target v.pt v.pb t
    check ((← natF j "tgt") == tgt) s!"topup: target {← natF j "tgt"}, model {tgt}"
    check (v.a < tgt / 2) "topup: the provider already holds half its target"
    match r.pend with
    | some (to, b) =>
      check (to == p && b == bytes) "topup: the tail of a steal goes to the thief"
      check (r.q == 0 && v.a == 0) "topup: a steal needs an empty queue and an empty thief"
      pure (setPV { r with pend := none } p { v with a := v.a + bytes, lp := some t })
    | none =>
      let k := (r.pv.toList.filter (·.inA)).length
      let want := if 4 * STRIPE_CHUNK * k ≤ r.q then tgt - v.a
        else tailWant (tgt - v.a) k r.q
      check (0 < r.q) "topup: from an empty queue"
      check (min want r.q ≤ bytes && bytes ≤ r.q && bytes < want + G) s!"topup: {bytes} bytes for {want} wanted of {r.q}"
      pure (setPV { r with q := r.q - bytes } p { v with a := v.a + bytes, lp := if v.a == 0 then some t else v.lp })
  | "steal" =>
    check (r.ph == 2 && r.striped && (← natF j "run") == r.run && r.pend.isNone) "steal: out of place"
    let from_ ← natF j "from"
    let to ← natF j "to"
    let t ← now j
    check (from_ != to) "steal: from itself"
    let f ← getPV r from_
    let th ← getPV r to
    check (r.q == 0 && th.inA && th.a == 0) "steal: the queue is not empty or the thief holds work"
    check (best r to t == some from_) s!"steal: the victim is {from_}, model {best r to t}"
    let m := f.a
    let rq := if (etaAt r from_ t).getD 0 ≥ STEAL_ETA_STALLED_MS then 0 else prate f.pt f.pb t
    let rp := prate th.pt th.pb t
    let keep := keepOf m rq rp
    let moved := m - min keep m
    check ((← natF j "bytes") == moved) s!"steal: {← natF j "bytes"} moved, model {moved}"
    pure (setPV { r with pend := if moved > 0 then some (to, moved) else none } from_ { f with a := m - moved })
  | "ver" =>
    check (r.ph == 2 && (← natF j "run") == r.run && r.pend.isNone) "ver: out of place"
    let p ← natF j "p"
    let v ← getPV r p
    let off ← natF j "off"
    let len ← natF j "len"
    let t ← now j
    check (off % G == 0) "ver: not on a group boundary"
    let g := off / G
    check (r.wanted[g]? == some true && r.done[g]? == some false) s!"ver: group {g} was verified or not wanted"
    check (len == gsize g r.len) "ver: not a whole group"
    let r1 := { r with done := r.done.set! g true, vb := r.vb + len }
    if r.striped then
      check (len ≤ v.a) "ver: bytes the provider was not assigned"
      pure (setPV r1 p { v with a := v.a - len, pb := v.pb + len, lp := some t, pt := v.pt <|> some t })
    else pure r1
  | "liar" =>
    check (r.ph == 2 && (← natF j "run") == r.run && r.pend.isNone) "liar: out of place"
    let p ← natF j "p"
    let v ← getPV r p
    check (v.inA && !r.evicted.contains p) "liar: a provider that holds no share"
    pure (setPV { r with q := r.q + v.a, evicted := p :: r.evicted } p {})
  | "end" =>
    check ((← natF j "run") == r.run && r.pend.isNone) "end: out of place"
    let res ← strF j "res"
    let allVer := (List.range r.wanted.size).all fun g => !r.wanted[g]! || r.done[g]!
    let noHolder := !r.pv.any (·.inA)
    match res with
    | "complete" =>
      check (allVer && (r.ph == 1 || (r.ph == 2 && (!r.striped || (r.q == 0 && sumA r == 0))))) "end: complete with a wanted group missing"
    | "noprov" => check (r.ph == 1 && !allVer && r.np == 0 && !(r.len == 0 && r.badroot)) "end: noprov"
    | "badroot" => check (r.ph == 1 && r.len == 0 && r.badroot) "end: badroot"
    | "liar" => check (r.ph == 2 && noHolder && !allVer) "end: every provider lied, but one still holds a share"
    | _ => throw s!"end: unknown result {res}"
    pure { r with ph := 0 }
  | _ => throw s!"unknown scheduler event {op}"

/-- Replay one event and check the conservation of the bytes afterwards. -/
def replayChecked (j : J) (r : RS) : Except String RS := do
  let r' ← replayEvent j r
  check (conserved r') "the bytes of the queue, the lists and the verified groups no longer add up"
  check (r'.evicted.all fun p => !(r'.pv[p]!.inA) && r'.pv[p]!.a == 0) "an evicted provider holds work"
  pure r'

end Pinc.TraceValuesSched
