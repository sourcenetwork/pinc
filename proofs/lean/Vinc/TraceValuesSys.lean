import Vinc.Json
import Vinc.ValuesSysSafe

/-!
# Replay of the value fetch traces

The Lean half of the trace validation of `vinc-values` `Fetch`: it reads the `vs` lines written by the Rust test
`trace_values_sys` (a `start` line, one `rec` line per event and per trace record of a run, an `end` line) and checks
that every run is a behaviour of the model `Vinc.ValuesSys`. It is the port of `proofs/tla/TraceValuesSys.tla`, and it
computes with the functions of the model itself: the commit of a verified group is `commitSt`, the announcement of the
held first granule is `releaseHd`, the final event is `finish`, and the store content of a group is the content of a
frame that verifies (`Kind.content`), so a group recorded as not genuine is rejected by the same collision-freedom
step the safety theorems use.

The checks: the start (BadRoot, then Complete when nothing is missing, then NoProvider, else the fetch starts); every
request asks only for wanted groups the store had not verified and never goes to an evicted provider; a group verifies
once, from a candidate, with the store snapshot of the model after it; the first granule is held and announced by its
release; every `Readable` event was announced by the model; the final events have their reasons; only a liar is
evicted and it is never named again; one final event and no record after it.
-/

namespace Vinc.TraceValuesSys
open Vinc.Json Vinc.ValuesSys

/-- The replay state of a file: the run in progress, if any. -/
structure W where
  /-- A run is in progress. -/
  live : Bool := false
  c : Cfg := { g := 0, want := emp, head0 := 0, initVer := emp, listed := emp, empty := false, rootOk := true,
               liars := emp, storeFail := false, deadline := none }
  s : St := init { g := 0, want := emp, head0 := 0, initVer := emp, listed := emp, empty := false, rootOk := true,
                   liars := emp, storeFail := false, deadline := none } 0
  np : Nat := 0
  relp : Option Nat := none
  seen : Nat → Nat := fun _ => 0

def setOf (l : List Nat) : GSet := fun x => l.contains x

def snapSet (ps : List (Nat × Nat)) : GSet := fun x => ps.any fun (a, b) => decide (a ≤ x) && decide (x < b)

def sameSet (n : Nat) (a b : GSet) : Bool := (List.range n).all fun x => a x == b x

def provs (np : Nat) : List Nat := (List.range np).map (· + 1)

def finalOf : String → Except String Final
  | "Complete" => pure .complete
  | "Deadline" => pure .deadline
  | "EveryProviderLied" => pure .everyProviderLied
  | "NoProvider" => pure .noProvider
  | "Store" => pure .store
  | "BadRoot" => pure .badRoot
  | s => throw s!"unknown final event {s}"

/-- The reason of a final event (`ValuesSysCore.ReasonOk`). -/
def reasonOk (c : Cfg) (np : Nat) (s : St) : Final → Bool
  | .everyProviderLied =>
      (provs np).any c.listed && (provs np).all fun p => !c.listed p || (!s.inP p && s.lied p)
  | .deadline => match c.deadline with
      | some d => decide (d < s.now)
      | none => false
  | .noProvider => (provs np).all fun p => !c.listed p
  | .store => true
  | .badRoot => c.empty && !c.rootOk
  | .complete =>
      (List.range c.g).all (fun x => !c.want x || s.ver x) && s.hd.isNone &&
        (List.range c.g).all fun x => !c.want x || s.ver0 x || decide (0 < s.ann x)

/-- What a start produces at once, in the order of `Fetch::start`: the final event, if any. -/
def startFinal (c : Cfg) (np : Nat) (s : St) : Option Final :=
  if c.empty && !c.rootOk then some .badRoot
  else if (List.range c.g).all (fun x => !c.want x || s.ver x) then some .complete
  else if (provs np).all (fun p => !c.listed p) then some .noProvider
  else none

def startEv (j : J) : Except String W := do
  let g ← natF j "g"
  let want ← natList (← field j "want")
  let ver0 ← natList (← field j "ver0")
  let listed ← natList (← field j "listed")
  let liars ← natList (← field j "liars")
  let dl ← intF j "dl"
  let c : Cfg := { g := g, want := setOf want, head0 := ← natF j "first", initVer := setOf ver0,
                   listed := setOf listed, empty := (← natF j "empty") == 1,
                   rootOk := (← natF j "badroot") == 0, liars := setOf liars, storeFail := true,
                   deadline := if dl < 0 then none else some dl.toNat }
  pure { live := true, c := c, s := init c 0, np := ← natF j "np" }

/-- The first requested group announced: before its release it is held. -/
def recEv (j : J) (w : W) : Except String W := do
  check w.live "a record outside a run"
  check (w.s.run != .done) "a record after the final event"
  let k ← strF j "k"
  let now := (← natF j "now")
  check (w.s.now ≤ now) "time went back"
  let w := { w with s := { w.s with now := now } }
  let s := w.s
  let c := w.c
  let cand (p : Nat) : Bool := s.inP p
  match k with
  | "fstart" =>
    check (s.run == .idle && startFinal c w.np s == none) "a fetch started that should have ended at once"
    pure { w with s := { s with run := .running, ver0 := s.ver, reqd := emp, inP := c.listed, inA := c.listed,
                                queue := dif c.want s.ver, asg := fun _ => emp } }
  | "req" =>
    let p ← natF j "p"
    let gs ← natList (← field j "groups")
    check (s.run == .running && cand p) "a request to a provider that is not a candidate"
    check (gs.all fun x => c.want x && !s.ver x) "a request for a group that is not wanted or is verified"
    pure { w with s := { s with reqd := fun x => s.reqd x || gs.contains x } }
  | "ver" =>
    let p ← natF j "p"
    let g ← natF j "g"
    let genuine ← natF j "genuine"
    check (s.run == .running && cand p) "a group verified from a provider that is not a candidate"
    check (c.want g && s.reqd g) "a verified group that was not asked for"
    check (!s.ver g) "a group verified twice"
    let kind : Kind := if genuine == 1 then .good else .junk
    check kind.verifies "bytes that fail their hash reached the store"
    let s1 : St := { s with wr := fun x => if x = g then kind.content else s.wr x }
    let s2 := commitSt c s1 g
    check (sameSet c.g s2.ver (snapSet (← pairList (← field j "snap")))) "the store snapshot differs from the model"
    check (s2.wr g == .good) "the store holds other bytes than the true ones"
    pure { w with s := s2 }
  | "held" =>
    let g ← natF j "g"
    check (s.hd == some g && !s.rel) "the first granule is not held"
    pure w
  | "rel" =>
    let g ← natF j "g"
    check (s.hd == some g) "a release of a granule that is not held"
    pure { w with relp := some g }
  | "ev" =>
    match ← strF j "e" with
    | "R" =>
      let g ← natF j "g"
      check (s.run == .running) "a Readable event outside a running fetch"
      if s.hd == some g then
        check (w.relp == some g) "the held granule announced without its release"
        pure { w with s := releaseHd s, relp := none, seen := fun x => if x = g then w.seen g + 1 else w.seen x }
      else
        check (w.relp == none && (g != c.head0 || s.rel)) "the first granule announced before its release"
        check (s.ver g && decide (w.seen g < s.ann g)) "a Readable event the model did not announce"
        pure { w with seen := fun x => if x = g then w.seen g + 1 else w.seen x }
    | e =>
      let f ← if e == "C" then pure Final.complete else finalOf (← strF j "why")
      if s.run == .idle then
        check (startFinal c w.np s == some f) "the final event of a start is not the one the model gives"
        pure { w with s := finish { s with run := .running, ver0 := s.ver, reqd := emp, inP := c.listed } f }
      else
        check (w.relp == none && s.run == .running) "a final event in the middle of a release"
        let s' := finish s f
        check (reasonOk c w.np s' f) "a final event without its reason"
        pure { w with s := s' }
  | "liar" =>
    let p ← natF j "p"
    check (s.run == .running && cand p && c.liars p) "an eviction of a provider that is not a lying candidate"
    pure { w with s := { s with inP := fun q => if q = p then false else s.inP q,
                                inA := fun q => if q = p then false else s.inA q,
                                lied := fun q => if q = p then true else s.lied q } }
  | "dial" | "retry" | "topup" =>
    check (s.run == .running && cand (← natF j "p")) "work for a provider that is not a candidate"
    pure w
  | "steal" =>
    check (s.run == .running && cand (← natF j "from") && cand (← natF j "to")) "a steal between non-candidates"
    pure w
  | "stall" | "proofrej" => check (s.run == .running) "a record of a fetch that is not running"; pure w
  | k => throw s!"unknown record {k}"

def endEv (j : J) (w : W) : Except String W := do
  check w.live "an end outside a run"
  check ((w.s.run == .done) == ((← natF j "done") == 1)) "the end of the run disagrees with the final event"
  check (sameSet w.c.g w.s.ver (snapSet (← pairList (← field j "snap")))) "the final store differs from the model"
  pure {}

/-- Replay one `vs` line. -/
def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "start" =>
    check (!w.live) "a start inside a run"
    startEv j
  | "rec" => recEv j w
  | "end" => endEv j w
  | o => throw s!"unknown op {o}"

end Vinc.TraceValuesSys
