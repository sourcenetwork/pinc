import Pinc.MembershipModelView

/-!
# The membership machine: the hub roster (`hub.rs`)

`send_snapshot`, `send_floor`, `on_hello`, `hub_down`, `on_down`, `hub_tick`, `carrier_return`, `carrier_gone`,
`independent_route`, `schedule_confirm`, `carrier_watch`, `confirm`, step for step. `push_delta` is in
`MembershipModelView.lean` (it shares the recursion of `apply_delta`).
-/

set_option linter.unusedVariables false

namespace Pinc.Membership
open Pinc.MemInc

/-- `ms`: a duration in whole milliseconds, saturating at `u32::MAX`. -/
def ms (d : Nat) : Nat := min (d / 1000000) U32MAX

/-- The frames of a snapshot: chunks of `SNAP_CHUNK`, a chunk is sent when the next entry arrives, so the last one
is never empty unless the snapshot is. -/
def snapChunks (es : List (Nat × Rec)) : List (List (Nat × Rec) × Bool) :=
  if es.length ≤ SNAP_CHUNK then [(es, false)] else (es.take SNAP_CHUNK, true) :: snapChunks (es.drop SNAP_CHUNK)
termination_by es.length
decreasing_by simp_wf; unfold SNAP_CHUNK at *; omega

/-- `send_snapshot`: the combined view for a member, the roster for a hub, plus this hub itself. -/
def N.sendSnapshot (e : Env) (n : N) (now peer : Nat) : N :=
  let partial_ := decide (now - n.born < LEASE)
  let toHub := n.isBoot peer
  let base : List (Nat × Rec) := if toHub then n.roster.map (fun p => (p.1, p.2.rc)) else n.members.map (fun p => (p.1, p.2.rc))
  let es := (base.filter (fun p => p.1 != peer)) ++ (if n.me != peer then [(n.me, n.own)] else [])
  (snapChunks es).foldl (fun n c => (N.tx e n peer .session (.snap partial_ c.2 c.1)).1) n

/-- `send_floor`: the replay floor the broadcast layer writes for a member that has just attached. -/
def N.sendFloor (e : Env) (n : N) (peer : Nat) : N :=
  let body := (e.floorBody peer).take FLOOR_MAX
  if body.isEmpty then n else (N.tx e n peer .session (.other 14 [] body)).1

/-- The later life of `peer` the view holds, in an epoch above the one its HELLO announces (a clock that went back
while the hub that held its last life went away): `on_hello` tells the node of it and waits for its HELLO from above. -/
def N.viewAhead (n : N) (peer : Nat) (rc : Rec) : Option Rec :=
  match n.members.get? peer with
  | some s => if rc.inc / 65536 < s.rc.inc / 65536 then some s.rc else none
  | none => none

/-- A HELLO from `peer`. -/
def N.onHello (e : Env) (n : N) (now peer : Nat) (rc : Rec) (snap homed : Bool) : N :=
  let n := if homed && !n.isBoot peer then
      (if n.homed.len < MAX_TABLE then { n with homed := n.homed.ins peer } else n)
    else { n with homed := n.homed.del peer }
  let n := if n.downed.has peer then (N.bc { n with downed := n.downed.erase peer } (.restore peer)) else n
  let newAttach := !n.attached.has peer
  let n := if newAttach && n.attached.len < MAX_TABLE then { n with attached := n.attached.ins peer } else n
  let n := if newAttach then N.sendFloor e (n.trace (.attached peer)) peer else n
  let n := if snap || newAttach then N.sendSnapshot e n now peer else (N.tx e n peer .session .ack).1
  match n.roster.get? peer with
  | some held =>
    if rc.inc < held.rc.inc then
      let n := { n with roster := n.roster.modify peer (fun l => { l with renewed := now }) }
      N.deltaTo e n peer peer held.rc .alive
    else if (n.viewAhead peer rc).isSome then
      let s := (n.viewAhead peer rc).getD rc
      let n := { n with roster := n.roster.modify peer (fun l => { l with renewed := now }) }
      N.deltaTo e n peer peer s .alive
    else if held.rc == rc then
      { n with roster := n.roster.modify peer (fun l => { l with renewed := now }) }
    else if MAX_TABLE ≤ n.roster.len && !n.roster.has peer then n
    else
      let n := { n with roster := n.roster.insert peer ⟨rc, now⟩ }
      N.pushDelta e n now peer rc .alive
  | none =>
    if (n.viewAhead peer rc).isSome then N.deltaTo e n peer peer ((n.viewAhead peer rc).getD rc) .alive
    else if MAX_TABLE ≤ n.roster.len then n
    else
      let n := { n with roster := n.roster.insert peer ⟨rc, now⟩ }
      N.pushDelta e n now peer rc .alive

/-- Why a hub drops a member from its roster. -/
inductive Cause where
  | confirmed (pf : Proof)
  | remote
  | left

/-- `hub_down`: drop `member`'s lease now. -/
def N.hubDown (e : Env) (n : N) (now member : Nat) (cause : Cause) : N :=
  match n.roster.get? member with
  | none => n
  | some lease =>
    let n := { n with roster := n.roster.erase member, susp := n.susp.erase member, attached := n.attached.del member }
    let isLeft := match cause with | .left => true | _ => false
    let n := if isLeft then n.bc (.release member) else n.bc (.hold member)
    let n := N.pushDelta e n now member lease.rc (if isLeft then .left else .down)
    let n := if !isLeft && (n.downed.len < MAX_TABLE || n.downed.has member) then
        { n with downed := n.downed.insert member (lease, now) } else n
    match cause with
    | .confirmed proof =>
      let n := n.trace (.confirmed member)
      n.boot.foldl
        (fun n hub =>
          if hub != n.me then
            let (n, ok) := N.tx e n hub .session (.down member lease.rc.inc proof)
            if ok then n.trace (.downSent member) else n
          else n) n
    | _ => n

/-- `on_down`: another hub's DOWN. Accepted only on a stale lease of our own. -/
def N.onDown (e : Env) (n : N) (now m inc : Nat) (pf : Proof) : N :=
  let refuse := fun (n : N) (why : Refusal) => n.trace (.downRefused m why.toNat)
  if n.isBoot m then refuse n .notApplicable
  else match n.roster.get? m with
  | none => refuse n .unknown
  | some l =>
    if l.rc.inc / 65536 != inc / 65536 then refuse n .unknown
    else
      let oldest := pf.oldest
      if !pf.independent then refuse n .notIndependent
      else if pf.sil < oldest then refuse n .badProof
      else if e.carrier m == .open_ then refuse n .carrierOpen
      else
        let renewed := match e.evidence m with | some ev => max l.renewed ev.rx | none => l.renewed
        let n := { n with roster := n.roster.modify m (fun x => { x with renewed := renewed }) }
        let window := max (oldest * 1000000) RENEW
        if now - renewed ≤ window then refuse n .leaseFresh
        else N.hubDown e (n.trace (.downAccepted m)) now m .remote

/-- `carrier_return`: `member`'s carrier is open again. Restore the entry and the subscriptions and tell the member. -/
def N.carrierReturn (e : Env) (n : N) (now member : Nat) : N :=
  match n.downed.get? member with
  | none => n.trace (.carrierReturned member false)
  | some (l, _) =>
    let n := { n with downed := n.downed.erase member }
    if n.roster.has member || n.revoked.has member then n
    else if MAX_TABLE ≤ n.roster.len then (n.bc (.release member)).trace (.carrierReturned member false)
    else
      let l := { l with renewed := now }
      let n := { n with roster := n.roster.insert member l }
      let n := if n.up.has member && n.attached.len < MAX_TABLE then { n with attached := n.attached.ins member } else n
      let n := n.bc (.restore member)
      let n := N.pushDelta e n now member l.rc .alive
      let n := N.deltaTo e n member member l.rc .alive
      n.trace (.carrierReturned member true)

/-- `probe_second`: the second probe never takes the path of the first, the session: it goes through the relay of the
first live hub (not this node, not the member) whose relay the host takes it for: `(route, path)`. A probe the host
refuses is not a sent probe, so the member needs a session (`acc`) and a hub whose relay the host refuses
(`rv`) is passed over. (The code tries each hub in turn and a refused try leaves its frame-out trace and a not-taken
entry in the sent list; this model selects the hub that takes it and leaves the refused tries out, as the
refused tries change no table. `Membership.tla` models them.) -/
def N.independentRoute (e : Env) (n : N) (now m : Nat) (_ev : Option Evid) : Option (Route × Nat) :=
  (n.boot.find? (fun x => x != n.me && x != m && n.hubUp now x && !e.rv.has x &&
    !(n.revoked.has m || m == n.me) && e.acc.has m)).map (fun x => (.via x, 2))

/-- `on_left`: another hub's delta says `m` left. A member this hub holds for the same life, with no carrier to this
hub, is dropped as left at once. -/
def N.onLeft (e : Env) (n : N) (now m : Nat) (rc : Rec) : N :=
  if n.isBoot m || e.carrier m == .open_ ||
      (match n.roster.get? m with | none => true | some l => l.rc.inc / 65536 != rc.inc / 65536) then n
  else N.hubDown e (n.trace (.leaveSeen m)) now m .left

/-- The smoothed round trip the host holds for the hub whose relay `route` goes through (0 when it has none, or the
route is no relay): `probe_second`'s second value. -/
def N.relaySrtt (e : Env) (route : Route) : Nat :=
  match route with
  | .via x => match e.evidence x with | some ev => ev.srtt | none => 0
  | _ => 0

/-- The relay's round trip of the second probe `independentRoute` gives (0 when there is none). -/
def N.srttFor (e : Env) (n : N) (now m : Nat) (ev : Option Evid) : Nat :=
  match n.independentRoute e now m ev with
  | some (route, _) => N.relaySrtt e route
  | none => 0

/-- `wait_b`: the second probe waits the first's wait and three round trips of the hub whose relay carries it. -/
def waitB (wait srtt : Nat) : Nat := satAdd wait (min (srtt * 3) U64MAX)

def N.scheduleConfirm (n : N) (now at_ : Nat) : N :=
  let at_ := max at_ (now + 1)
  { n with nextConf := some (match n.nextConf with | some c => min c at_ | none => at_) }

/-- `confirm`. -/
def N.confirm (e : Env) (n : N) (now m : Nat) (sp : Susp) (l : Lease) : N :=
  let probes : List (Nat × Nat) :=
    (ms (now - sp.probeA), 0) :: (match sp.probeB with | some (tb, path) => [(ms (now - tb), path)] | none => [])
  N.hubDown e n now m (.confirmed ⟨ms (now - l.renewed), probes⟩)

/-- The watch runs again when the first probe's wait ends: an independent route may be up by then. A suspicion is not
reported (c26385e): only the confirmation is an event. -/
def N.rewatch (n : N) (now : Nat) (sp : Susp) : N :=
  if now < sp.probeA + sp.wait then n.scheduleConfirm now (sp.probeA + sp.wait) else n

theorem rewatch_susp (n : N) (now : Nat) (sp : Susp) : (N.rewatch n now sp).susp = n.susp := by
  unfold N.rewatch N.scheduleConfirm
  repeat' split
  all_goals rfl

/-- The `_` arm of the match on the suspicion in `carrier_watch`: a new drop to confirm. -/
def N.newSusp (e : Env) (n : N) (now m since : Nat) (ev : Option Evid) : N :=
  if MAX_TABLE ≤ n.susp.len then n
  else
    let wait := max PROBE_WAIT_MIN (match ev with | some x => min (x.srtt * 3) U64MAX | none => 0)
    let n := (N.tx e n m .session .probe).1
    let n := n.trace (.probeSent m 0)
    let srttB := N.srttFor e n now m ev
    let (n, probeB) : N × Option (Nat × Nat) :=
      match n.independentRoute e now m ev with
      | some (route, path) =>
        let n := (N.tx e n m route .probe).1
        (n.trace (.probeSent m path), some (now, path))
      | none => (n, none)
    let sp : Susp := ⟨since, now, probeB, wait, srttB⟩
    let n := { n with susp := n.susp.insert m sp }
    let n := n.scheduleConfirm now (now + wait)
    match probeB with
    | some (tb, _) => n.scheduleConfirm now (max (max (since + CONFIRM) (now + wait)) (tb + waitB wait srttB))
    | none => n.trace (.noIndependentPath m)


/-- `carrier_watch`: confirm or clear a dropped carrier. -/
def N.carrierWatch (e : Env) (n : N) (now m : Nat) : N :=
  match n.roster.get? m with
  | none => { n with susp := n.susp.erase m }
  | some l =>
    match e.carrier m with
    | .gone since sleep =>
      let ev := e.evidence m
      let heard := match ev with | some x => decide (since ≤ x.rx) | none => false
      if decide (since ≤ l.renewed) || heard || (match sleep with | some s => decide (since ≤ satAdd s SLEEP_WIN) | none => false) then
        let n := if heard then
            (match ev with
             | some x => { n with roster := n.roster.modify m (fun y => { y with renewed := max y.renewed x.rx }) }
             | none => n)
          else n
        { n with susp := n.susp.erase m }
      else
        match n.susp.get? m with
        | some sp0 =>
          if sp0.since == since then
            let n := N.rewatch n now sp0
            let (n, sp) : N × Susp :=
              if sp0.probeB.isNone then
                match n.independentRoute e now m ev with
                | some (route, path) =>
                  let n := (N.tx e n m route .probe).1
                  let n := n.trace (.probeSent m path)
                  let sp := { sp0 with probeB := some (now, path), srttB := N.relaySrtt e route }
                  ({ n with susp := n.susp.insert m sp }, sp)
                | none => (n, sp0)
              else (n, sp0)
            match sp.probeB with
            | some (tb, _) =>
              let dl := max (max (sp.since + CONFIRM) (sp.probeA + sp.wait)) (tb + waitB sp.wait sp.srttB)
              if dl ≤ now then N.confirm e n now m sp l else n.scheduleConfirm now dl
            | none => n
          else N.newSusp e n now m since ev
        | none => N.newSusp e n now m since ev
    | _ => { n with susp := n.susp.erase m }

/-- `carrier_gone`: `member`'s relay carrier closed. Start confirming it now rather than at the next tick. -/
def N.carrierGone (e : Env) (n : N) (now member : Nat) : N :=
  if n.isHub && !n.isBoot member then N.carrierWatch e (n.trace (.carrierGone member)) now member else n

/-- `hub_tick`: expire leases, refresh them from transport evidence, watch dropped carriers, restore returned
carriers. -/
def N.hubTick (e : Env) (n : N) (now : Nat) : N :=
  let n := forKeys n.roster.keys
    (fun m n =>
      match n.roster.get? m with
      | none => n
      | some l0 =>
        let (n, l) : N × Lease :=
          match e.evidence m with
          | some ev =>
            if RENEW < now - l0.renewed && l0.renewed < ev.rx then
              (({ n with roster := n.roster.modify m (fun x => { x with renewed := ev.rx }) }).trace (.pulse m), { l0 with renewed := ev.rx })
            else (n, l0)
          | none => (n, l0)
        if LEASE < now - l.renewed then
          let n := { n with roster := n.roster.erase m, susp := n.susp.erase m }
          let n := n.trace (.leaseExpired m)
          let n := N.pushDelta e n now m l.rc .down
          n.bc (.release m)
        else if !n.isBoot m then N.carrierWatch e n now m
        else n) n
  forKeys n.downed.keys
    (fun m n =>
      match n.downed.get? m with
      | none => n
      | some (_, t0) =>
        if LEASE < now - t0 || n.roster.has m || n.revoked.has m then (N.bc { n with downed := n.downed.erase m } (.release m))
        else if e.carrier m == .open_ then N.carrierReturn e n now m
        else n) n

end Pinc.Membership
