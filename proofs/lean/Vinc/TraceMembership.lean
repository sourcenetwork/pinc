import Vinc.Json
import Vinc.TraceMembershipInc
import Vinc.MembershipModelNode

/-!
# Replay of the node traces

The Lean half of the trace validation of the hub and member state machines (`vinc-membership`): the Rust test
`trace_membership` (part `node`) records every call into a machine of the membership test world as one `mem` line:
the call, the host as the call found it, what the machine asked of the host and reported, and the public state after.
The replay applies the same call to the model of the node (`Vinc.Membership`, `MembershipModel*.lean`) with the same
host and requires the same frames sent (route, whether a session took them, and the frame bytes through the codec
model `Vinc.MemCodec`), the same broadcast-layer calls, closes, events and trace records, the same store afterwards and
the same public state (members, view epoch, primary, incarnation, roster leases).

The frames received are tied to the codec: each `fs` entry carries the bytes, and `MemCodec.read` of them must be the
frame the line records. A `start` re-initialises its slot; a start that fails leaves the slot's machine untouched.
-/

namespace Vinc.TraceMembership
open Vinc.Json Vinc.MemInc Vinc.Membership Vinc.TraceMembershipInc

def isTag (t : String) : Bool := t == "mem"

/-- The replay state: the machine of each slot. -/
structure W where
  slots : List (Nat × N) := []

instance : Inhabited W := ⟨{}⟩

def hexVal (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
  else throw s!"bad hex digit {c}"

def hexBytes (s : String) : Except String (List Nat) := do
  let rec go : List Char → Except String (List Nat)
    | [] => pure []
    | [_] => throw "odd hex length"
    | a :: b :: r => do
      let v := (← hexVal a) * 16 + (← hexVal b)
      pure (v :: (← go r))
  go s.toList

def listJ (j : J) : Except String (List J) :=
  match j.arr? with
  | some a => pure a.toList
  | none => throw "expected an array"

def optNat (j : J) : Except String (Option Nat) := do
  match ← listJ j with
  | [] => pure none
  | [x] => match x.nat? with | some n => pure (some n) | none => throw "expected a number"
  | _ => throw "not an option"

/-! ## The codec bridge -/

def idBytes (m : Nat) : List Nat := List.replicate 32 m

def pathOf : Nat → Vinc.MemCodec.Path
  | 0 => .session
  | 1 => .direct
  | _ => .relay

def recOf (r : Rec) : Vinc.MemCodec.Rec := ⟨r.inc, r.ver, r.th⟩

/-- The codec frame of a node frame (ids are 32 equal bytes in the traces). -/
def toCodec : NFrame → Vinc.MemCodec.Frame
  | .hello rc s h => .hello (recOf rc) s h
  | .ack => .ack
  | .probe => .probe
  | .delta m rc a => .delta ⟨idBytes m, recOf rc, a⟩
  | .snap p mo es => .snap p mo (es.map fun (m, rc) => ⟨idBytes m, recOf rc, .alive⟩)
  | .down m inc pf => .down (idBytes m) inc ⟨pf.sil, pf.probes.map fun (a, p) => ⟨a, pathOf p⟩⟩
  | .other t tp r => .other t tp r

/-- `MemCodec.read` returned this frame and used this many bytes. -/
def readIs (r : Except Vinc.MemCodec.Err (Option (Vinc.MemCodec.Frame × Nat))) (v : Option (Vinc.MemCodec.Frame × Nat)) : Bool :=
  match r with | .ok x => decide (x = v) | .error _ => false

/-! ## Reading the line -/

def recF (j : J) : Except String Rec := do pure ⟨← u64F j "inc", ← natF j "ver", ← natList (← field j "th")⟩

def frameOf (j : J) : Except String NFrame := do
  match ← strF j "k" with
  | "hello" => pure (.hello (← recF j) (← boolF j "snap") (← boolF j "homed"))
  | "ack" => pure .ack
  | "probe" => pure .probe
  | "delta" =>
    let a ← natF j "a"
    pure (.delta (← natF j "m") (← recF j) (match a with | 0 => .down | 1 => .alive | _ => .left))
  | "snap" =>
    let es ← (← listJ (← field j "es")).mapM fun x => do pure ((← natF x "m"), (← recF x))
    pure (.snap (← boolF j "partial") (← boolF j "more") es)
  | "down" =>
    let pr ← (← listJ (← field j "pr")).mapM fun x => do
      match ← natList x with
      | [a, p] => pure (a, p)
      | _ => throw "bad probe"
    pure (.down (← natF j "m") (← u64F j "inc") ⟨← natF j "sil", pr⟩)
  | "other" => pure (.other (← natF j "ty") (← natList (← field j "topic")) (← natList (← field j "rest")))
  | k => throw s!"unknown frame kind {k}"

def evidOf (j : J) : Except String Evid := do
  pure ⟨← u64F j "rx", ← u64F j "srtt", ← natF j "pto", ← natF j "inf", ← boolF j "direct"⟩

def pairs (j : J) : Except String (List (Nat × J)) := do
  (← listJ j).mapM fun x => do
    match ← listJ x with
    | [a, b] => match a.nat? with | some n => pure (n, b) | none => throw "bad pair key"
    | _ => throw "expected a pair"

def sortedByKey {α : Type} (l : List (Nat × α)) : AMap α := l.foldl (fun m p => AMap.insert m p.1 p.2) []

def envOf (j : J) : Except String Env := do
  let ev ← (← pairs (← field j "ev")).mapM fun (p, x) => do pure (p, ← evidOf x)
  let car ← (← pairs (← field j "car")).mapM fun (m, x) => do
    match ← strF x "k" with
    | "open" => pure (m, Car.open_)
    | "gone" => pure (m, Car.gone (← u64F x "since") (← optF x "sleep"))
    | k => throw s!"unknown carrier {k}"
  let gu ← (← pairs (← field j "gu")).mapM fun (p, x) => do pure (p, ← limbsOf x)
  let acc ← natList (← field j "acc")
  check ((← natF j "floor") == 9) "the floor body is 9 bytes in the harness"
  pure { ev := sortedByKey ev, car := sortedByKey car, acc := sortedByKey (acc.map fun p => (p, ())),
         ver := ← natF j "ver", tk := ← natF j "tk", refl := ← boolF j "refl",
         loc := ⟨← boolF j "pers", ← optF j "sealed", ← boolF j "failunseal", ← boolF j "failseal"⟩,
         floorBody := fun p => [0xF1, p, 0, 0, 0, 0, 0, 0, 1], gu := sortedByKey gu }

def routeOf (j : J) : Except String Route := do
  match ← strF j "r" with
  | "s" => pure .session
  | "d" => pure .direct
  | "v" => pure (.via (← natF j "via"))
  | r => throw s!"unknown route {r}"

def sentOf (j : J) : Except String Sent := do
  let f ← frameOf (← field j "f")
  let hex ← hexBytes (← strF j "hex")
  check (Vinc.MemCodec.enc (toCodec f) == hex) s!"codec: the model encoding of {repr f} differs from the code's bytes"
  pure (← natF j "to", ← routeOf j, f, ← boolF j "ok")

def bcOf (j : J) : Except String Bc := do
  match ← strF j "k" with
  | "frame" => pure (.frame (← natF j "from") (← natF j "ty") (← natList (← field j "topic")) (← natList (← field j "rest")))
  | "hold" => pure (.hold (← natF j "m"))
  | "restore" => pure (.restore (← natF j "m"))
  | "release" => pure (.release (← natF j "m"))
  | "resub" => pure (.resub (← natF j "hub"))
  | "primary" => pure (.primary (← optNat (← field j "old")) (← natF j "new"))
  | k => throw s!"unknown broadcast call {k}"

def evOf (j : J) : Except String Ev := do
  match ← strF j "k" with
  | "joined" => pure (.joined (← natF j "m"))
  | "suspected" => pure (.suspected (← natF j "m"))
  | "down" => pure (.down (← natF j "m"))
  | "left" => pure (.left (← natF j "m"))
  | "revoked" => pure (.revoked (← natF j "m"))
  | "addr" => pure (.addr (← natF j "m"))
  | "stack" => pure (.stack (← natF j "m") (← natF j "v"))
  | "view" => pure (.view (← u64F j "epoch") (← natF j "n"))
  | "lost" => pure (.lost (← natF j "n"))
  | k => throw s!"unknown event {k}"

def trOf (j : J) : Except String Tr := do
  let m := fun (k : String) => natF j k
  match ← strF j "k" with
  | "started" => pure (.started (← u64F j "inc"))
  | "incarnation" => pure (.incarnation (← u64F j "inc"))
  | "frame_in" => pure (.frameIn (← m "peer") (← m "ty"))
  | "frame_out" => pure (.frameOut (← m "peer") (← m "ty"))
  | "bad_frame" => pure (.badFrame (← m "peer"))
  | "attached" => pure (.attached (← m "member"))
  | "pulse" => pure (.pulse (← m "member"))
  | "lease_expired" => pure (.leaseExpired (← m "member"))
  | "carrier_gone" => pure (.carrierGone (← m "member"))
  | "probe_sent" => pure (.probeSent (← m "member") (← m "path"))
  | "no_independent_path" => pure (.noIndependentPath (← m "member"))
  | "confirmed" => pure (.confirmed (← m "member"))
  | "leave_seen" => pure (.leaveSeen (← m "member"))
  | "down_sent" => pure (.downSent (← m "member"))
  | "down_accepted" => pure (.downAccepted (← m "member"))
  | "down_refused" => pure (.downRefused (← m "member") (← m "why"))
  | "carrier_returned" => pure (.carrierReturned (← m "member") (← boolF j "restored"))
  | "self_delta" => pure (.selfDelta (← m "hub"))
  | "snap_applied" => pure (.snapApplied (← m "hub") (← m "entries") (← boolF j "more"))
  | "absent" => pure (.absent (← m "member"))
  | "removed" => pure (.removed (← m "member") (← m "why"))
  | "deferred" => pure (.deferred (← m "member"))
  | "quiet" => pure (.quiet (← m "cause"))
  | "hub_stale" => pure (.hubStale (← m "hub"))
  | "primary" => pure (.primary (← m "hub"))
  | "hello_suppressed" => pure (.helloSuppressed (← m "hub"))
  | "seal_failed" => pure .sealFailed
  | "lost" => pure (.lost (← m "n"))
  | k => throw s!"unknown trace record {k}"

def closeOf (j : J) : Except String (Nat × CloseR) := do
  match ← listJ j with
  | [p, r] =>
    let p ← match p.nat? with | some n => pure n | none => throw "bad close peer"
    match r.str? with
    | some "noack" => pure (p, .noack)
    | some "stale" => pure (p, .stale)
    | some "leave" => pure (p, .leave)
    | some "revoked" => pure (p, .revoked)
    | _ => throw "bad close reason"
  | _ => throw "bad close"

/-- Compare two lists of the line, naming the field. -/
def same {α : Type} [BEq α] [Repr α] (what : String) (model code : List α) : Except String Unit :=
  check (model == code) s!"{what}: model {repr model}, code {repr code}"

instance : BEq Tr := ⟨fun a b => decide (a = b)⟩
instance : BEq Ev := ⟨fun a b => decide (a = b)⟩
instance : BEq Bc := ⟨fun a b => decide (a = b)⟩
instance : BEq CloseR := ⟨fun a b => decide (a = b)⟩
instance : BEq NFrame := ⟨fun a b => decide (a = b)⟩
instance : BEq Route := ⟨fun a b => decide (a = b)⟩

/-- Check what the machine produced against the line. -/
def checkOut (j : J) (n : N) (now : Nat) : Except String Unit := do
  let o ← field j "out"
  same "sent" n.outSent (← (← listJ (← field o "sent")).mapM sentOf)
  same "broadcast calls" n.outBc (← (← listJ (← field o "bc")).mapM bcOf)
  same "closes" n.outClose (← (← listJ (← field o "cl")).mapM closeOf)
  same "events" n.drainEvents (← (← listJ (← field o "ev")).mapM evOf)
  same "traces" n.drainTraces (← (← listJ (← field o "tr")).mapM trOf)
  check ((← optF o "sealed") == n.loc.sealed) s!"store after: model {repr n.loc.sealed}"
  let st ← field j "st"
  let ms ← (← listJ (← field st "members")).mapM fun x => do
    match ← listJ x with
    | [i, inc, ver, th] =>
      let i ← match i.nat? with | some v => pure v | none => throw "bad member id"
      let ver ← match ver.nat? with | some v => pure v | none => throw "bad version"
      pure (i, (⟨← limbsOf inc, ver, ← natList th⟩ : Rec))
    | _ => throw "bad member"
  same "members" (n.members.map fun p => (p.1, p.2.rc)) ms
  check ((← u64F st "epoch") == n.epoch) s!"view epoch: model {n.epoch}"
  check ((← optNat (← field st "primary")) == n.primary) s!"primary: model {repr n.primary}"
  check ((← u64F st "inc") == n.inc.word) s!"incarnation: model {n.inc.word}"
  let ro ← (← listJ (← field st "roster")).mapM fun x => do
    match ← listJ x with
    | [i, t] =>
      let i ← match i.nat? with | some v => pure v | none => throw "bad roster id"
      pure (i, ← limbsOf t)
    | _ => throw "bad roster entry"
  same "roster" (n.roster.map fun p => (p.1, p.2.renewed)) ro
  check ((← boolF st "sealfailed") == n.sealFailed) "seal_failed"
  check ((← u64F st "maxframe") == n.maxFrame) s!"max frame: model {n.maxFrame}"
  same "hubs up" (sortedByKey ((n.me :: n.up.keys).filter (fun h => n.hubUp now h) |>.map fun h => (h, ())) |>.keys) (← natList (← field st "hu"))

def slotGet (w : W) (k : Nat) : Except String N :=
  match w.slots.lookup k with
  | some n => pure n
  | none => throw s!"no machine in slot {k}"

def slotSet (w : W) (k : Nat) (n : N) : W :=
  { slots := (k, n) :: w.slots.filter (fun p => p.1 != k) }

/-- The frames of a `by` line, tied to their bytes through the codec model at the limit `mf` in force. -/
def framesOf (j : J) (mf : Nat) : Except String (List NFrame) := do
  let fs ← (← listJ (← field j "fs")).mapM fun x => do
    let f ← frameOf (← field x "f")
    let hex ← hexBytes (← strF x "hex")
    check (readIs (Vinc.MemCodec.readWith mf hex) (some (toCodec f, hex.length))) s!"codec: reading the bytes of {repr f} gives another frame"
    pure f
  let rest ← hexBytes (← strF j "rest")
  let bad ← boolF j "bad"
  if bad then
    check (match Vinc.MemCodec.readWith mf rest with | .error _ => true | _ => false) "codec: the bytes the code refused are accepted"
  else
    check (rest.isEmpty || readIs (Vinc.MemCodec.readWith mf rest) none) "codec: the partial tail is not a partial frame"
  pure fs

def replayEvent (j : J) (w : W) : Except String W := do
  let k ← natF j "n"
  let op ← strF j "op"
  let e ← envOf (← field j "env")
  if op == "start" then
    let now ← u64F j "now"
    let hubs ← natList (← field j "hubs")
    let r := N.start e (k + 1) (← boolF j "hub") hubs true now (← u64F j "wall") (← u64F j "floor")
    let ret ← strF j "ret"
    match r with
    | .ok n =>
      check (ret == "ok") s!"start: the model succeeds, the code said {ret}"
      checkOut j n now
      pure (slotSet w k n.drained.clearOut)
    | .error err =>
      let want := match err with
        | .tooManyHubs => "toomany" | .store => "store" | .exhausted => "exhausted"
      check (ret == want) s!"start: model {want}, code {ret}"
      pure w
  else
    let n0 ← slotGet w k
    let n0 := { n0 with loc := e.loc }
    let now ← match j.get? "now" with | some _ => u64F j "now" | none => pure 0
    let n : N ← match op with
      | "up" => pure (N.sessionUp e n0 now (← natF j "peer") (← boolF j "inc"))
      | "dn" => pure (N.sessionDown e n0 now (← natF j "peer") (← u64F j "code"))
      | "by" =>
        check ((← u64F j "mf") == n0.maxFrame) s!"max frame: model {n0.maxFrame}"
        let fs ← framesOf j n0.maxFrame
        pure (N.onBytes e n0 now (← natF j "peer") fs (← boolF j "bad"))
      | "to" => pure (N.onTimeout e n0 now)
      | "cg" => pure (N.carrierGone e n0 now (← natF j "member"))
      | "cr" => pure (N.carrierReturn e n0 now (← natF j "member"))
      | "lv" => pure (N.leave n0)
      | "rv" =>
        let ret ← strF j "ret"
        match N.revoke e n0 now (← natF j "member") with
        | some n => do check (ret == "ok") "revoke: the model accepts, the code said full"; pure n
        | none => do check (ret == "full") "revoke: the model says full, the code accepted"; pure n0
      | "mv" => pure (N.addressChanged n0 now)
      | "sn" => pure (N.snapshotTo e n0 now (← natF j "peer"))
      | "sm" => pure (N.setMaxFrame n0 (← u64F j "mf"))
      | _ => throw s!"unknown node op {op}"
    checkOut j n now
    pure (slotSet w k n.drained.clearOut)

end Vinc.TraceMembership
