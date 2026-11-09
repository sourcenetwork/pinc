import Vinc.Json
import Vinc.ValuesTimeDeadline

/-!
# Replay of the time-rule traces

The replay half of the trace validation of the time rules of `Fetch` (the Rust test `trace_values_time`, the TLA+
half is `TraceValuesTime.tla`). Every run of the real fetch is replayed through the functions of `Vinc/ValuesTime.lean`
that the theorems of `ValuesTimeHold`, `-Inv`, `-Bound`, `-Stall` and `-Deadline` are about, and any difference exits
with an error naming the line:

* `vtrun`: `startFetch` must report what `Fetch::start` reported (bad root, nothing missing, no provider, or running),
  and the fields right after `start` are those of `Fs.init`;
* `vt` of kind `ev` (an event of the simulation): `byteLive` (the stream bytes arrived), `arrival` (a frame completed),
  then for every recorded record in order `verifyStep` (a group verified), `step .evict` (a provider evicted) or
  `step .aheadStoreFail` (the store refused a write), and optionally `checkDone` (a stream ended);
* `vt` of kind `bs` (a run of steps in which only stream bytes arrived): `byteLive` at the first time and then the largest gap and the last time (`byteLive_run`);
* `vt` of kind `to` (an `on_timeout` call): `onTimeout` with the sessions recorded, where `stallRtt` and
  `stallLive` of the sessions must be the waits the test computed.

The model state after the step must be the recorded one (the wait, the last frame and byte times, the held granule,
the release flag and the count of later granules, whether the fetch runs), the records and events must be exactly the
model's in order, `poll_timeout` must be the model's minimum or a retry time below it. The time of the first request
and the steal timer are armed by code outside these rules and are taken from the record, allowing only the values the
code can arm.
-/

namespace Vinc.ValuesTimeTrace
open Vinc.Json Vinc.ValuesTime Vinc.Ranges

/-- A u64 recorded as four 16-bit limbs, least significant first. -/
def limbsOf (j : J) : Except String Nat := do
  match ← natList j with
  | [a, b, c, d] => pure (a + 65536 * b + 65536 * 65536 * c + 65536 * 65536 * 65536 * d)
  | _ => throw "bad limbs"

def limbsF (j : J) (k : String) : Except String Nat := do limbsOf (← field j k)

/-- The time state of a fetch as recorded. -/
structure St where
  run : Bool
  sw : Nat
  lastp : Nat
  lastb : Nat
  treq : Nat
  tw : Nat
  head : Option (Nat × Nat × Nat)
  rel : Bool
  nv : Nat
  poll : Option Nat

def parseSt (j : J) : Except String St := do
  let h ← field j "head"
  let head ← if (← boolF h "h") then pure (some (← natF h "off", ← natF h "len", ← limbsF h "t0")) else pure none
  let p ← field j "poll"
  let poll ← if (← boolF p "p") then pure (some (← limbsF p "v")) else pure none
  pure { run := ← boolF j "run", sw := ← limbsF j "sw", lastp := ← limbsF j "lastp", lastb := ← limbsF j "lastb"
         treq := ← limbsF j "treq", tw := ← limbsF j "tw", head, rel := ← boolF j "rel", nv := ← natF j "nv", poll }

/-- The model state of a run and where it is. -/
structure W where
  fs : Fs
  inRun : Bool
  run : Nat

instance : Inhabited W := ⟨⟨Fs.init 0 [] [] none false 0, false, 0⟩⟩

def cmpSt (s : Fs) (st : St) : Bool :=
  s.running == st.run && s.sw == st.sw && s.lastp == st.lastp && s.lastb == st.lastb && s.rel == st.rel &&
    s.nv == st.nv && (s.head.map (fun h => (h.off, h.len, h.t0))) == st.head

def showSt (s : Fs) : String :=
  s!"run {s.running} sw {s.sw} lastp {s.lastp} lastb {s.lastb} head {s.head.map (fun h => (h.off, h.len, h.t0))} rel {s.rel} nv {s.nv}"

def showRec (st : St) : String :=
  s!"run {st.run} sw {st.sw} lastp {st.lastp} lastb {st.lastb} head {st.head} rel {st.rel} nv {st.nv}"

def causeOf : String → Except String Cause
  | "buffered" => pure .buffered
  | "tail" => pure .tail
  | "granules" => pure .granules
  | "timeout" => pure .timeout
  | "done" => pure .done
  | c => throw s!"unknown cause {c}"

def failOf : String → Except String Fail
  | "NoProvider" => pure .noProvider
  | "Lied" => pure .lied
  | "Deadline" => pure .deadline
  | "Store" => pure .store
  | "BadRoot" => pure .badRoot
  | r => throw s!"unknown failure {r}"

/-- A recorded record or event: `none` for the eviction record, which the model does not log. -/
def atomOf (a : J) : Except String (Option Ev) := do
  let arr ← match a.arr? with | some x => pure x | none => throw "atom is not an array"
  let tag ← match arr[0]? >>= (·.str?) with | some t => pure t | none => throw "atom has no tag"
  let n (k : Nat) : Except String Nat := match arr[k]? >>= J.nat? with | some v => pure v | none => throw s!"atom {tag}: field {k}"
  match tag with
  | "ver" => pure (some (.verified (← n 1) (← n 2)))
  | "held" => pure (some (.held (← n 1)))
  | "rel" =>
    let c ← match arr[2]? >>= (·.str?) with | some c => pure c | none => throw "rel cause"
    pure (some (.released (← n 1) (← causeOf c)))
  | "rd" => pure (some (.readable (← n 1) (← n 2)))
  | "done" => pure (some .complete)
  | "fail" =>
    let r ← match arr[1]? >>= (·.str?) with | some c => pure c | none => throw "fail reason"
    pure (some (.failed (← failOf r)))
  | "redial" =>
    let l (k : Nat) : Except String Nat := match arr[k]? with | some x => limbsOf x | none => throw "redial limbs"
    pure (some (.redial (← l 1) (← l 2)))
  | "liar" => pure none
  | t => throw s!"unknown atom {t}"

def atomsOf (j : J) : Except String (List J) :=
  match j.arr? with | some a => pure a.toList | none => throw "tr is not an array"

def eventsOf (as : List J) : Except String (List Ev) := do
  let mut out := []
  for a in as do
    if let some e ← atomOf a then out := out ++ [e]
  pure out

def tagOf (a : J) : Except String String := do
  match a.arr? >>= (·[0]?) >>= (·.str?) with | some t => pure t | none => throw "atom has no tag"

/-- The consumed records of an event step, in order. -/
def foldAtoms (now : Nat) (s : Fs) (as : List J) : Except String Fs := do
  let mut s := s
  for a in as do
    match ← tagOf a with
    | "ver" =>
      let arr := (a.arr?).getD #[]
      let o ← match arr[1]? >>= J.nat? with | some v => pure v | none => throw "ver off"
      let l ← match arr[2]? >>= J.nat? with | some v => pure v | none => throw "ver len"
      s := step s (.ahead now o l)
    | "liar" => s := step s (.evict now false)
    | "fail" =>
      let arr := (a.arr?).getD #[]
      if (arr[1]? >>= (·.str?)) == some "Store" then s := step s (.aheadStoreFail now)
    | _ => pure ()
  pure s

def pollOk (s : Fs) (st : St) : Bool :=
  match st.poll, pollTimeout s with
  | none, none => true
  | none, some _ => false
  | some _, none => true
  | some v, some m => decide (v ≤ m)

/-- The arming rules for the first request time and the steal timer. -/
def armOk (pre post : St) (now : Nat) (stealRule : Bool) : Bool :=
  (post.treq == pre.treq || (pre.treq == 0 && post.treq == now)) &&
    (!stealRule || post.tw == pre.tw || (decide (pre.tw ≤ now) && post.tw == now + STEAL_IDLE / 2))

def parseSess (j : J) : Except String Sess := do
  let up ← boolF j "c"
  let r ← intF j "r"
  let info := if up then some { rtt := if r < 0 then none else some r.toNat, pto := false, lastRx := 0 : PeerInfo } else none
  let pto ← boolF j "p"
  let lastRx ← limbsF j "x"
  pure { conn := up, info := info.map fun i => { i with pto, lastRx } }

def replayStart (j : J) (w : W) : Except String W := do
  let o0 ← natF j "o0"
  let len ← natF j "len"
  let er ← boolF j "er"
  let want ← pairList (← field j "want")
  let sto ← pairList (← field j "stoi")
  check ((← natF j "hb") == HOLD_B && (← natF j "nvl") == HOLD_NV) "HOLD_B or HOLD_NV differ from the constants of the model"
  let hasdl ← boolF j "hasdl"
  let dl ← limbsF j "dl"
  let striped ← boolF j "striped"
  let np ← natF j "np"
  let post ← parseSt (← field j "post")
  let evs ← eventsOf (← atomsOf (← field j "tr"))
  let out := startFetch len er np want sto
  check (evs == out.toList) s!"start reported {repr evs}, the model says {repr out.toList}"
  check (post.run == out.isNone && post.sw == STALL_WAIT && post.lastp == 0 && post.lastb == 0 && post.tw == 0 &&
    post.head.isNone && !post.rel && post.nv == 0) "state right after start"
  let fs := { Fs.init o0 want sto (if hasdl then some dl else none) striped np with running := out.isNone, treq := post.treq }
  pure { fs, inRun := true, run := ← natF j "run" }

def replayEv (j : J) (w : W) : Except String W := do
  let now ← limbsF j "now"
  let pre ← parseSt (← field j "pre")
  let post ← parseSt (← field j "post")
  check (cmpSt w.fs pre) s!"before the step: model {showSt w.fs}, recorded {showRec pre}"
  let as ← atomsOf (← field j "tr")
  let evs ← eventsOf as
  let s0 := { w.fs with log := [] }
  let s1 := if post.lastb == now then byteLive s0 now else s0
  let s2 := if post.lastp == now then arrival s1 now else s1
  let s3 ← foldAtoms now s2 as
  let c0 := s3
  let c1 := if s3.running then checkDone s3 now else s3
  let ok (c : Fs) : Bool := cmpSt c post && c.log == evs
  let c ← if ok c0 then pure c0 else if ok c1 then pure c1
    else throw s!"event step at {now}: model {showSt c0} events {repr c0.log} / {showSt c1} events {repr c1.log}, recorded {showRec post} events {repr evs}"
  check (armOk pre post now true) s!"arming of treq/tw: pre {pre.treq} {pre.tw} post {post.treq} {post.tw} at {now}"
  let c := { c with treq := post.treq, tw := post.tw, log := [], rt := none }
  check (pollOk c post) s!"poll_timeout {post.poll}, the model offers {pollTimeout c}"
  pure { w with fs := c }

def replayTo (j : J) (w : W) : Except String W := do
  let now ← limbsF j "now"
  let pre ← parseSt (← field j "pre")
  let post ← parseSt (← field j "post")
  check (cmpSt w.fs pre) s!"before the step: model {showSt w.fs}, recorded {showRec pre}"
  let as ← atomsOf (← field j "tr")
  let evs ← eventsOf as
  let ss ← match (← field j "ss").arr? with
    | some a => a.toList.mapM parseSess
    | none => throw "ss is not an array"
  let wr ← limbsF j "w"
  let lv ← limbsF j "lv"
  check (stallRtt ss == wr) s!"stall_rtt: model {stallRtt ss}, test {wr}"
  check (stallLive now pre.lastp ss == lv) s!"stall_live: model {stallLive now pre.lastp ss}, test {lv}"
  let s0 := { w.fs with log := [] }
  let ok (c : Fs) : Bool := cmpSt c post && c.log == evs && c.tw == post.tw
  let c0 := onTimeout s0 now ss false none
  let c1 := onTimeout s0 now ss true none
  let c ← if ok c0 then pure c0 else if ok c1 then pure c1
    else throw s!"timer step at {now}: model {showSt c0} events {repr c0.log} / {showSt c1} events {repr c1.log}, recorded {showRec post} events {repr evs}"
  check (armOk pre post now false) s!"arming of treq: pre {pre.treq} post {post.treq} at {now}"
  let c := { c with treq := post.treq, log := [], rt := none }
  check (pollOk c post) s!"poll_timeout {post.poll}, the model offers {pollTimeout c}"
  pure { w with fs := c }

/-- A run of steps in which only stream bytes arrived: `byteLive` at the first time, then, by `byteLive_run`, the
largest gap and the last time. -/
def replayBs (j : J) (w : W) : Except String W := do
  let pre ← parseSt (← field j "pre")
  let post ← parseSt (← field j "post")
  check (cmpSt w.fs pre) s!"before the bytes: model {showSt w.fs}, recorded {showRec pre}"
  let t1 ← limbsF j "t1"
  let tn ← limbsF j "tn"
  let n ← natF j "n"
  let mg ← limbsF j "mg"
  check (t1 != 0) "bytes at time 0"
  let s1 := byteLive { w.fs with log := [] } t1
  let c := if n > 1 then byteRun s1 tn mg else s1
  check (cmpSt c post) s!"after the bytes: model {showSt c}, recorded {showRec post}"
  check (pollOk c post) s!"poll_timeout {post.poll}, the model offers {pollTimeout c}"
  pure { w with fs := c }

def replayEvent (j : J) (w : W) : Except String W := do
  match (← strF j "t") with
  | "vtrun" => replayStart j w
  | "vt" =>
    check (w.inRun && (← natF j "run") == w.run) "step outside its run"
    match (← strF j "k") with
    | "ev" => replayEv j w
    | "bs" => replayBs j w
    | _ => replayTo j w
  | t => throw s!"unknown time event {t}"

/-- The tags this module replays. -/
def isTag (t : String) : Bool := t == "vtrun" || t == "vt"

end Vinc.ValuesTimeTrace
