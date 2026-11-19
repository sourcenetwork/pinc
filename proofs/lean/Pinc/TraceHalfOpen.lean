import Pinc.Json
import Pinc.CoreHalfOpen

/-!
# Replay of the half-open cap traces

The Lean half of the trace validation of the endpoint's half-open cap and the lifetime of an unauthenticated session
(`pinc-core` `rx.rs`, `events.rs`, `endpoint.rs`, `timers.rs`), the port of `proofs/tla/TraceHalfOpen.tla`. It reads
the `coho` events written by the Rust test `trace_halfopen` and replays every call: each decision the endpoint
recorded (an admission with the count, the room the host left and the sessions owed, and the ticket's verdict it used,
a session made, established, expired or freed) must be the one `Pinc.CoreHalfOpen` makes, in that order, and the slots
and the count the model computes must be the recorded ones; the deadlines a session's connection asks for are the
endpoint's own. The cap a first flight meets is the smaller of the code's and half the room, rounded up, and none starts
a session while the owed sessions fill the room. A first packet the responder would only reject or not answer is
recorded as decided without a session, answered with a reject because its prekey or ticket is not held (admitted 2)
or dropped without an answer (admitted 3): a short Initial or a Hello of its floor's size or more, no resumption,
that finds room to be decided on, and never one the test sent as a genuine dialer does while no session holds its id. A reject is counted once at
most in the call (a refusal by the ledger or a full queue); one that is queued is counted when it is sent. An admission happens only
while the id has fewer holders than `holders` (`room`), and a datagram whose first flight went to the admission frees
no session that was in use before it (only one it made itself): an arrival never frees the session that holds its id.
After every call the count is at most the cap and the number of counted sessions, every slot is good (`good`),
`poll_timeout` is the earliest deadline (none while stalled), a timer call the queue did not stop left no session at
or past its end, and a first flight that made no session changed no slot. The file `halfopen_ns.ndjson`, with times
in nanoseconds, is replayed here only.
-/

namespace Pinc.TraceHalfOpen
open Pinc.Json Pinc.CoreHalfOpen

def isTag (t : String) : Bool := t == "coho"

structure W where
  e : E := {}
  p : P := { max := 0, life := 0, hold := 0, full := 0, short := 0, hello := 0, holders := 0 }

/-- A recorded slot: `[slot, in use, created, unauthenticated, counted, has a deadline, the deadline, its life]`. -/
def slotOf (r : List Nat) : Except String (Nat × Option Sl) :=
  match r with
  | [j, use, created, unauth, counted, hasDl, dl, life] =>
    if use == 0 then pure (j, none)
    else pure (j, some { created, unauth := unauth == 1, counted := counted == 1, life,
                         dl := if hasDl == 1 then some dl else none })
  | _ => throw "a slot has not eight numbers"

def listOf (j : J) (k : String) : Except String (List J) := do
  match (← field j k).arr? with
  | some a => pure a.toList
  | none => throw s!"expected the list {k}"

/-- A slot without what is the endpoint's own: the deadline, and the life (it rises to the hold when the session
answers). -/
def bare : Option Sl → Option Sl
  | some s => some { s with dl := none, life := 0 }
  | none => none

/-- `good` as a test. -/
def goodB (p : P) : Option Sl → Bool
  | some s => (!s.counted || s.unauth) && (!s.unauth || s.dl.any (· ≤ s.created + s.life + 1))
              && (s.life == p.life || s.life == p.hold)
  | none => true

structure St where
  e : E
  adm : Option (Bool × Bool)

/-- One decision of a call: `[0, admitted, count, resume, room, owed]` an admission (admitted 1 made a session, 0 was
refused, 2 was answered with a reject without a session, 3 was dropped), `[1, slot, dial, 0, 0, 0]` a session made, `[2, slot, 0, 0, 0,
0]` established, `[3, slot, 0, 0, 0, 0]` expired (the next decision frees it), `[4, slot, 0, 0, 0, 0]` freed; `n` is
how many sessions held the datagram's id. -/
def stepOf (p : P) (op : String) (now kind len n genuine : Nat) (st : St) (s : List Nat) (next : Option (List Nat)) :
    Except String St := do
  match s with
  | [0, a, c, r, rm, ow] =>
    check (op == "dgram") "an admission outside a datagram"
    check (isFirst kind) "an admission of a type that starts nothing"
    check (room p n) s!"a first flight went to the admission for an id that {n} sessions hold"
    check (c == st.e.count) s!"the admission used the count {c}, the model holds {st.e.count}"
    check (r == 0 || kind == 6) "a resumption that is no Hello"
    check (a ≤ 3) "an admission that is neither made, refused, answered with a reject nor dropped"
    if a ≥ 2 then
      check (r == 0 && forged kind && decide (ow < rm) && decide (floor p kind ≤ len) && (genuine == 0 || n > 0))
        "a first packet answered without a session that is not a short Initial or a Hello of its floor's size, or no room, or a genuine one with no session under its id"
    else
      check ((a == 1) == (decide (ow < rm) && admits { p with max := halfCap p.max rm } st.e.count kind len (r == 1)))
        "the admission differs from the rule"
    pure { st with adm := some (a == 1, r == 1) }
  | [1, j, 1, _, _, _] =>
    check (j < st.e.slots.length && at? st.e.slots j == none) "a dial took a slot in use"
    pure { st with e := dial st.e j now p.life }
  | [1, j, _, _, _, _] =>
    check (j < st.e.slots.length && at? st.e.slots j == none) "a session took a slot in use"
    match st.adm with
    | some (true, r) => pure { e := make st.e j now r p.life, adm := none }
    | _ => throw "a session made without an admission"
  | [2, j, _, _, _, _] =>
    check (at? st.e.slots j).isSome "a free slot was established"
    pure { st with e := establish st.e j }
  | [3, j, _, _, _, _] =>
    check (op == "timer") "an expiry outside a timer call"
    check (expired p now (at? st.e.slots j)) "a session expired before its end"
    check (next == some [4, j, 0, 0, 0, 0]) "an expired session was not freed"
    pure st
  | [4, j, _, _, _, _] => pure { st with e := release st.e j }
  | _ => throw s!"unknown decision {s}"

def foldSteps (p : P) (op : String) (now kind len n genuine : Nat) : St → List (List Nat) → Except String St
  | st, [] => pure st
  | st, s :: rest => do
    let st' ← stepOf p op now kind len n genuine st s rest.head?
    foldSteps p op now kind len n genuine st' rest

/-- Every session the decisions free was not in use before the call (`before`), or was made earlier in the call
(`made`). -/
def freesOnlyMade (before : List (Option Sl)) : List Nat → List (List Nat) → Bool
  | _, [] => true
  | made, [1, j, _, _, _, _] :: rest => freesOnlyMade before (j :: made) rest
  | made, [4, j, _, _, _, _] :: rest => ((at? before j).isNone || made.contains j) && freesOnlyMade before made rest
  | made, _ :: rest => freesOnlyMade before made rest

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let k ← natF j "k"
    pure { e := init k, p := { max := ← natF j "max", life := ← natF j "life", hold := ← natF j "hold",
                               full := ← natF j "full", short := ← natF j "short", hello := ← natF j "hello",
                               holders := ← natF j "holders" } }
  | op =>
    check (op == "dgram" || op == "timer" || op == "other") s!"unknown half-open op {op}"
    let p := w.p
    let now ← natF j "now"
    let kind ← natF j "kind"
    let len ← natF j "len"
    let n ← natF j "n"
    let genuine ← natF j "genuine"
    let stalled0 := (← natF j "stalled0") == 1
    let stalled := (← natF j "stalled") == 1
    let count ← natF j "count"
    let dropped ← natF j "dropped"
    let stalledIn ← natF j "stalledIn"
    let otherwise ← natF j "otherwise"
    let steps ← (← listOf j "steps").mapM natList
    let diff ← (← (← listOf j "diff").mapM natList).mapM slotOf
    let timeout : Option Nat := match ← natList (← field j "timeout") with
      | [t] => some t
      | _ => none
    let st ← foldSteps p op now kind len n genuine { e := w.e, adm := none } steps
    -- the slots and the count the model computes are the endpoint's; the deadlines are the endpoint's own
    let sl := diff.foldl (fun acc (x : Nat × Option Sl) => put acc x.1 x.2) w.e.slots
    check (sl.map bare == st.e.slots.map bare)
      s!"the slots differ: the model computes {repr (st.e.slots.map bare)}, the code recorded {repr (sl.map bare)}"
    check (st.e.count == count) s!"the count differs: the model computes {st.e.count}, the code recorded {count}"
    let e' : E := { slots := sl, count }
    -- the count is at most the cap and the number of counted sessions; every slot is good
    check (count ≤ p.max && count == countOf sl) "the count passed the cap or differs from the counted sessions"
    check (sl.all (goodB p)) "a counted session is authenticated, or an unauthenticated one's deadline is past its end"
    -- poll_timeout is the earliest deadline, none while stalled
    check (timeout == poll sl stalled) s!"poll_timeout {timeout} is not the earliest deadline {poll sl stalled}"
    -- a timer call the queue did not stop leaves no session at or past its end; a stalled one runs nothing
    check (op != "timer" || stalled || sl.all (fun o => !expired p now o)) "a session outlived its end"
    check (op != "timer" || !stalled0 || (steps.isEmpty && diff.isEmpty)) "a timer ran while the queue was stalled"
    -- an arrival never frees a session: a datagram whose first flight went to the admission frees only a session it
    -- made itself (the id table full, or a session that ended at once)
    check (op != "dgram" || !steps.any (fun s => s.head? == some 0) || freesOnlyMade w.e.slots [] steps)
      "a first flight freed a session that was in use before it"
    -- a datagram for an id no session holds
    if op == "dgram" && n == 0 then
      let made := steps.any (fun s => s.head? == some 1)
      let decided := steps.head?.bind List.head? == some 0
      check (!stalled0 || (steps.isEmpty && stalledIn == 1 && dropped == 0)) "a stalled endpoint decided"
      check (stalled0 || isFirst kind || (steps.isEmpty && (kind == 0 || dropped == 1)))
        "a type that starts no session decided"
      check (stalled0 || !isFirst kind || decided) "a first message type was not decided"
      check (made || diff.isEmpty) "a first flight that made no session changed a slot"
      -- a reject that is queued is counted when it is sent, not in this call
      let answered := steps.head?.bind (fun s => s[1]?) == some 2
      check (!decided || made || (if answered then dropped + otherwise ≤ 1 else dropped + otherwise == 1))
        "a first flight that made no session was not counted once"
    pure { w with e := e' }

end Pinc.TraceHalfOpen
