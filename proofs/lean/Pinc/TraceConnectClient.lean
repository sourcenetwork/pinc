import Pinc.Json
import Pinc.ConnectClient
import Pinc.TraceConnectCodec

/-!
# Replay of the client rules trace

The replay half of the trace validation of the client rules (the Rust test `trace_connect_client`; the TLA+ half is
`TraceConnectClient.tla`). Every recorded call of the real punch timer, tunnel rules, first-flight selection, pending
dials, lookup table, verification, classification and probe state is replayed through the Lean functions of
`ConnectClient.lean`; the answer and the state read back after the call must be the model's. Times are recorded in
microseconds and are nanoseconds here; a deadline one nanosecond past a whole microsecond is recorded rounded up.
-/

namespace Pinc.TraceConnectClient
open Pinc.Json Pinc.ConnectClient
open Pinc.ConnectLink (satSub)

structure W where
  p : Puncher := {}
  sp : Splices := Splices.new 3 2
  pend : Pending := Pending.new 3 2
  lk : Lookups := Lookups.new 3
  nc : Netcheck := Netcheck.new 3

instance : Inhabited W := ⟨{}⟩

def isTag (t : String) : Bool := t == "cl"

def ns (j : J) (k : String) : Except String Nat := do pure ((← natF j k) * 1000)

/-- A recorded optional time: `-1` is none. -/
def optI (j : J) (k : String) : Except String (Option Nat) := do
  let v ← intF j k
  pure (if v < 0 then none else some v.toNat)

def ceilUs (d : Nat) : Nat := (d + 999) / 1000

def sameInt (what : String) (j : J) (k : String) (v : Option Nat) : Except String Unit := do
  let want ← intF j k
  let got : Int := match v with | some x => x | none => -1
  check (want == got) s!"{what}: the code says {want}, the model {got}"

def sameStr (what : String) (j : J) (v : String) : Except String Unit := do
  check ((← field j "res").str? == some v) s!"{what}: different answer, the model says {v}"

def boolList (j : J) (k : String) : Except String (List Bool) := do
  match (← field j k).arr? with
  | some a => a.toList.mapM fun x => match x.bool? with | some b => pure b | none => throw "expected a bool"
  | none => throw "expected an array"

def intListF (j : J) (k : String) : Except String (List Int) := do intList (← field j k)

def candOf' (j : J) : Except String Cand := do
  match j.arr? with
  | some a =>
    match a.toList with
    | [t, v] =>
      match t.str?, v.nat? with
      | some "u", some p => pure (.udp p)
      | some "r", some r => pure (.relay r)
      | _, _ => throw "bad candidate"
    | _ => throw "bad candidate"
  | none => throw "bad candidate"

def candsOf (j : J) : Except String (List Cand) := do
  match j.arr? with
  | some a => a.toList.mapM candOf'
  | none => throw "expected candidates"

def viewOf (j : J) : Except String (Option RelayView) := do
  if ← boolF j "some" then pure (some ⟨← boolF j "live", ← natF j "gen"⟩) else pure none

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "m" with
  | "gaps" =>
    let g := (probeGaps (← ns j "srtt")).map ceilUs
    check (g == (← natList (← field j "out"))) "probe gaps"
    pure w
  | "pnew" => pure { w with p := {} }
  | "puncher" =>
    let now ← ns j "now"
    match ← strF j "c" with
    | "est" =>
      let p := w.p.established now
      sameInt "est" j "at" (if p.at_ = 0 then none else some (ceilUs p.at_))
      pure { w with p := p }
    | "arm" =>
      let p := w.p.arm (← ns j "arg")
      sameInt "arm" j "at" (if p.at_ = 0 then none else some (ceilUs p.at_))
      pure { w with p := p }
    | "due" =>
      let v ← field j "view"
      let (s, p) := w.p.due now ⟨← ns v "idle", ← boolF v "direct", ← ns v "rtt", ← ns v "quiet"⟩
      sameStr "due" j (match s with | .punch => "punch" | .wait => "wait")
      sameInt "due" j "at" (if p.at_ = 0 then none else some (ceilUs p.at_))
      pure { w with p := p }
    | c => throw s!"unknown puncher call {c}"
  | "decide" =>
    let sj ← field j "session"
    let sess ← if ← boolF sj "has" then pure (some (⟨← natF sj "pto", ← boolF sj "hs", ← natF sj "tries", ← boolF sj "thin"⟩ : Rides))
      else pure none
    let v := decide' (← boolF j "open") (← ns j "silent") sess (← boolF j "tunnel")
    sameStr "decide" j (match v with | .carrier => "carrier" | .tunnel => "tunnel" | .both => "both")
    pure w
  | "thin" =>
    let age ← optI j "age"
    let t : Thin := ⟨← boolF j "thin", ← boolF j "est", age.map (· * 1000), ← ns j "rtt", ← boolF j "fresh",
      ← boolF j "took", ← natF j "pto"⟩
    check ((← field j "res").bool? == some (thinSplice t)) "thin_splice"
    pure w
  | "hubok" =>
    check ((← field j "res").bool? == some (hubOk (← boolF j "valid") (← ns j "heard") (← ns j "now"))) "hub_ok"
    pure w
  | "snew" => pure { w with sp := Splices.new (← natF j "p") (← natF j "r") }
  | "seen" => pure { w with sp := w.sp.seen (← ns j "now") (← natF j "relay") (← natF j "peer") (← natF j "from") }
  | "sview" =>
    let now ← ns j "now"
    let rtt ← ns j "rtt"
    let ages := (List.range 5).flatMap fun p => (List.range 2).map fun r =>
      match w.sp.age now r (p + 1) with | some a => (a / 1000 : Int) | none => -1
    check (ages == (← intListF j "ages")) "splice ages"
    let lives := (List.range 2).map fun r => match w.sp.liveAt now r rtt with | some a => (a : Int) | none => -1
    check (lives == (← intListF j "lives")) "splice live"
    pure w
  | "direct" =>
    check ((← field j "res").bool? == some (directFirst (← boolF j "first") (← boolF j "hub") (← boolF j "restarted") (← ns j "fd") (← ns j "started")))
      "direct_first"
    pure w
  | "select" =>
    let cands ← candsOf (← field j "cands")
    let views ← match (← field j "views").arr? with
      | some a => a.toList.mapM viewOf
      | none => throw "views"
    let tj ← field j "try"
    let last ← if ← boolF tj "haslast" then
        (match ← natList (← field tj "last") with
          | [r, g, a] => pure (some (r, g, a * 1000))
          | _ => throw "last relay")
      else pure none
    let t : Try := ⟨← ns tj "now", ← boolF tj "dialer", ← natF tj "tries", ← ns tj "rtt", ← boolF tj "nortt",
      ← boolF tj "hs0", last⟩
    let relay := fun r => (views.getD r none)
    let (outc, carried) := select cands t relay (← natF j "cap")
    check (outc == (← candsOf (← field j "out"))) "select: different candidates"
    let want ← match ← natList (← field j "carried") with
      | [] => pure none
      | [r, g] => pure (some (r, g))
      | _ => throw "carried"
    check (carried == want) "select: different carried relay"
    pure w
  | "pnew3" => pure { w with pend := Pending.new (← natF j "n") (← natF j "h") }
  | "padd" =>
    let (ok, p) := w.pend.add (← natF j "peer") (← natF j "s")
    check ((← field j "res").bool? == some ok) "pending add"
    pendView j w p
  | "ptake" =>
    let (ws, p) := w.pend.take (← natF j "peer")
    let got : List Int := ws.map fun x => match x with | some v => (v : Int) | none => -1
    check (got == (← intListF j "res")) "pending take"
    pendView j w p
  | "pprune" =>
    let keep ← natF j "keep"
    let (dropped, p) := w.pend.prune fun s => s % 4 != keep
    check (dropped == (← natList (← field j "res"))) "pending prune"
    pendView j w p
  | "lnew" => pure { w with lk := Lookups.new (← natF j "n") }
  | "ask" =>
    let (a, l) := w.lk.ask (← ns j "now") (← natF j "peer") (← boolF j "udp") (← boolF j "car") (← ns j "thin")
    sameStr "ask" j (match a with | .skip => "skip" | .udp false => "udp" | .udp true => "udpall" | .carrier => "carrier" | .later => "later")
    lkView j w l
  | "answered" =>
    if (j.get? "relay").isSome then ncAnswered j w else lkView j w (w.lk.answered (← natF j "peer"))
  | "toolarge" => lkView j w (w.lk.tooLarge (← natF j "peer"))
  | "lclear" => lkView j w w.lk.clear
  | "lview" => lkView j w w.lk
  | "verify" =>
    let peer ← natList (← field j "peer")
    let sig ← boolF j "sig"
    let kind ← strF j "k"
    let rb ← natList (← field j "b")
    let ans : Answer := if kind == "abs" then .absent else if kind == "big" then .tooLarge else .record rb
    let v := verify peer ans sig (fun e => "rec:" ++ Pinc.TraceConnectCodec.Et e)
    let res ← field j "res"
    match v with
    | .none => check (res.str? == some "none") "verify: absent"
    | .refused t => check (res.str? == some t) s!"verify: refused {t}"
    | .found home reach seq addrs =>
      let f ← field res "found"
      check (home == (← natList (← field f "home"))) "verify: home"
      check (reach == (← natF f "reach")) "verify: reach"
      check (seq == (← natF f "seq")) "verify: seq"
      let want ← match (← field f "addrs").arr? with
        | some a => a.toList.mapM fun x => do
          match x.arr? with
          | some l => match l.toList with
            | [ip, p] =>
              let ipb ← natList ip
              let pn := p.nat?.getD 0
              pure ((if ipb.length == 4 then 4 else 6) :: (ipb ++ [pn / 256, pn % 256]))
            | _ => throw "address"
          | none => throw "address"
        | none => throw "addresses"
      check (addrs == want) "verify: addresses"
    pure w
  | "classify" =>
    let addrs := fun (k : String) => do
      match (← field j k).arr? with
      | some a => a.toList.mapM fun x => do
        match x.arr? with
        | some l => match l.toList with
          | [ip, p] => pure ((← natList ip, p.nat?.getD 0) : Addr)
          | _ => throw "address"
        | none => throw "address"
      | none => throw "addresses"
    let o : Observed := ⟨← addrs "local", ← addrs "refl", ← addrs "mapped", ← boolF j "heard", ← ns j "since", ← ns j "wd"⟩
    check ((← natF j "res") == (classify o).getD 0) "classify"
    pure w
  | "nnew" =>
    -- the pinned relay of the run: `-1` is none
    let nc := Netcheck.new (← natF j "r")
    pure { w with nc := match ← optI j "pin" with | some p => nc.setPin p | none => nc }
  | "psent" =>
    ncView j w (w.nc.probeSent (← ns j "now") (← natF j "relay") (← natList (← field j "nonce")) (← boolF j "works")) "none"
  | "failed" => ncView j w (w.nc.failed (← natF j "relay")) "none"
  | "healthy" => ncView j w (w.nc.healthy (← natF j "relay")) "none"
  | "restart" => ncView j w w.nc.restart "none"
  | "failover" =>
    let usable ← boolList j "usable"
    let isOpen ← boolList j "open"
    let (r, n) := w.nc.failover (fun i => usable.getD i false) fun i => isOpen.getD i false
    sameInt "failover" j "res" r
    ncView j w n "ok"
  | "missing" =>
    let first ← optI j "fr"
    let (s, n) := w.nc.homeMissing first
    sameStr "missing" j (match s with | .done => "done" | .again => "again" | .fallback f => s!"fb{f}")
    ncView j w n "ok"
  | m => throw s!"unknown client call {m}"
where
  pendView (j : J) (w : W) (p : Pending) : Except String W := do
    check (p.peers == (← natList (← field j "peers"))) "pending peers"
    check ((List.range 5).map (fun k => p.contains (k + 1)) == (← boolList j "has")) "pending contains"
    pure { w with pend := p }
  lkView (j : J) (w : W) (l : Lookups) : Except String W := do
    let now ← ns j "now"
    check (l.len == (← natF j "len")) "lookup len"
    check (l.due now == (← natList (← field j "due"))) "lookup due"
    sameInt "lookup next" j "next" (l.nextDeadline.map ceilUs)
    check ((List.range 5).map (fun k => l.contains (k + 1)) == (← boolList j "has")) "lookup contains"
    pure { w with lk := l }
  ncAnswered (j : J) (w : W) : Except String W := do
    let (r, n) := w.nc.answered (← ns j "now") (← natF j "relay") (← natList (← field j "nonce")) (← natF j "addr")
    sameInt "answered" j "res" (r.map (· / 1000))
    ncView j w n "ok"
  ncView (j : J) (w : W) (n : Netcheck) (_k : String) : Except String W := do
    sameInt "home" j "home" n.home
    let rtts : List Int := (List.range 3).map fun i => match n.rttOf i with | some r => (r / 1000 : Int) | none => -1
    check (rtts == (← intListF j "rtts")) "netcheck rtts"
    let refl : List Int := (List.range 3).map fun i => match n.refl.getD i none with | some a => (a : Int) | none => -1
    check (refl == (← intListF j "refl")) "netcheck reflexive"
    check ((List.range 3).map n.unhealthy == (← boolList j "unh")) "netcheck unhealthy"
    check (n.bestRtt / 1000 == (← natF j "best")) "netcheck best rtt"
    sameInt "first" j "first" (n.firstProbe.map ceilUs)
    pure { w with nc := n }

end Pinc.TraceConnectClient
