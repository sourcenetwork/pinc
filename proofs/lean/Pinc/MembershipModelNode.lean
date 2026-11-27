import Pinc.MembershipModelHub

/-!
# The membership machine: timers, frame dispatch, sessions (`timers.rs`, `input.rs`, `node.rs`)

`poll_timeout`, `on_timeout`, `tick`, `slow_tick`, `sample_session_rtts`, `drop_stale_hubs`, `pulse_refresh`,
`on_bytes`, `on_frame`, `start`, `session_up`, `session_down`, `drop_peer`, `leave`, `revoke`, `address_changed`,
step for step. A call takes the host (`Env`) as it finds it; the node's store is read from it at the start of the call.
-/

set_option linter.unusedVariables false

namespace Pinc.Membership
open Pinc.MemInc

/-- `stream_reset`: a snapshot of `peer` cut short will not be finished, so its copy is closed and the next snapshot
starts a new round. -/
def N.streamReset (n : N) (peer : Nat) : N :=
  match n.hv.get? peer with
  | some c => { n with hv := n.hv.insert peer { c with open_ := false } }
  | none => n

/-- `stream_reset` changes only the copies. -/
@[simp] theorem N.streamReset_eq (n : N) (peer : Nat) :
    n.streamReset peer =
      { n with hv := match n.hv.get? peer with | some c => n.hv.insert peer { c with open_ := false } | none => n.hv } := by
  unfold N.streamReset; split <;> rfl

/-- `drop_peer`. -/
def N.dropPeer (e : Env) (n : N) (now peer : Nat) : N :=
  let n := ({ n with up := n.up.erase peer, attached := n.attached.del peer, homed := n.homed.del peer,
                     helloAt := n.helloAt.unset peer, hsent := n.hsent.unset peer }).streamReset peer
  let n := if !n.isHub && n.homeOk == some peer then { n with homeOk := none } else n
  let n := if !n.downed.has peer then n.bc (.release peer) else n
  if n.isBoot peer && n.primary == some peer then N.reselect e n now else n

/-- `poll_timeout`: when the host should next call `on_timeout`. -/
def N.pollTimeout (n : N) : Nat :=
  let t := min n.nextRenew (n.nextTick.getD n.born)
  match n.nextConf with | some c => min t c | none => t

/-- `pulse_refresh`: refresh our hearing of each hub from the transport. -/
def N.pulseRefresh (e : Env) (n : N) (now : Nat) : N :=
  n.boot.foldl
    (fun n hub =>
      if hub == n.me || !n.up.has hub then n
      else
        let t := n.heard.get? hub
        match e.evidence hub with
        | some ev =>
          if (match t with | none => true | some t => decide (RENEW ≤ now - t)) && (match t with | none => true | some t => decide (t < ev.rx)) then
            let n := if !n.isHub && (match t with | some t => decide (e.giveUp hub < ev.rx - t) | none => false) then
                n.beginQuiet now 1 else n
            { n with heard := n.heard.insert hub ev.rx }
          else n
        | none => n) n

/-- `sample_session_rtts`: the hub sessions' transport round trips feed the nearest-hub choice. -/
def N.sampleSessionRtts (e : Env) (n : N) (now : Nat) : N :=
  let n := n.boot.foldl
    (fun n hub =>
      if hub == n.me then n
      else match e.evidence hub with
        | some ev =>
          if n.up.has hub && 0 < ev.srtt && now - ev.rx < PULSE_FRESH && ev.inf ≤ RTT_QUIET then n.rttSample hub ev.srtt else n
        | none => n) n
  let cur := n.primary.bind (fun p => n.hrtt.get? p)
  let better := n.boot.any (fun x =>
    x != n.me && n.primary != some x && n.hubUp now x &&
      (match n.hrtt.get? x with
       | some r => (match cur with | none => true | some c => decide (min (r + HYST_ABS) U64MAX < c * 2 / 3))
       | none => false))
  if better then N.reselect e n now else n

/-- `drop_stale_hubs`: a stale hub's copy is dropped while another hub is fresh, and its session is closed. -/
def N.dropStaleHubs (e : Env) (n : N) (now : Nat) : N :=
  let stale := (n.hv.keys.filter (fun k => !n.hubUp now k)).length
  if stale == 0 || n.hv.len ≤ stale then n
  else
    let (n, changed) := n.hv.keys.foldl
      (fun (a : N × Bool) hub =>
        let (n, changed) := a
        if n.hubUp now hub then a
        else match n.hv.get? hub with
          | none => a
          | some copy =>
            let n := { n with hv := n.hv.erase hub }
            let n := n.trace (.hubStale hub)
            let n := if n.up.has hub && HUB_STALE ≤ now - (n.heard.get? hub).getD 0 then n.close hub .stale else n
            copy.entries.keys.foldl (fun (b : N × Bool) m => let (n', c) := N.recomputeOne e b.1 now m; (n', b.2 || c)) (n, changed))
      (n, false)
    if changed then n.bump else n

/-- `slow_tick`. -/
def N.slowTick (e : Env) (n : N) (now : Nat) : N :=
  let n := forKeys n.helloAt.keys
    (fun hub n =>
      match n.helloAt.timeAt hub with
      | none => n
      | some t0 =>
        let opened := (n.up.get? hub).getD now
        if ACK_WAIT < now - t0 && HS_GRACE < now - opened then
          let skip := match e.evidence hub with
            | some ev =>
              let wt := max ACK_WAIT (min (ev.srtt * 4) U64MAX)
              decide (now - t0 ≤ wt) || decide (now - ev.rx < wt / 2)
            | none => false
          if skip then n
          else
            let n := { n with helloAt := n.helloAt.unset hub }
            if n.up.has hub then N.dropPeer e (n.close hub .noack) now hub else n
        else n) n
  let n := if !n.isHub then N.sampleSessionRtts e n now else n
  let n := N.dropStaleHubs e n now
  let n := N.sweepAbsent e n now
  let primaryDown := match n.primary with | none => true | some p => !n.hubUp now p
  if primaryDown then N.reselect e n now else n

/-- Whether an omission clock has run out by `now` (`next_absent` is due): the tick sweeps then. -/
def N.absentDue (n : N) (now : Nat) : Bool :=
  match n.nextAbsent with | some t => decide (t ≤ now) | none => false

/-- `tick`. -/
def N.tick (e : Env) (n : N) (now : Nat) : N :=
  let n := N.recheckDue e n now
  let n := if n.absentDue now then N.sweepAbsent e n now else n
  let n := if n.sent != some (n.ver, n.th) then N.renew e n now false false else n
  let n := if n.isHub || n.nextSlow ≤ now then
      N.slowTick e (if !n.isHub then { n with nextSlow := satAdd now SLOW_TICK } else n) now
    else n
  if n.isHub then N.hubTick e n now else n

/-- `on_timeout`: run whatever is due at `now`. -/
def N.onTimeout (e : Env) (n : N) (now : Nat) : N :=
  if n.leaving then n
  else
    let n := N.pulseRefresh e n now
    let n := N.refreshLocal e n now
    let n := if n.nextRenew ≤ now then N.renew e n now false true else n
    let n := if (match n.nextConf with | some c => decide (c ≤ now) | none => false) then
        let n := { n with nextConf := none }
        if n.isHub then forKeys n.susp.keys (fun m n => N.carrierWatch e n now m) n else n
      else n
    if (n.nextTick.getD 0) ≤ now then
      -- The first tick is due at the start (`poll_timeout` gives `born`), so a late first tick is late too.
      let n := if !n.isHub && WAKE_GAP < now - n.nextTick.getD n.born then
          N.renew e (n.beginQuiet now 0) now true false
        else n
      let n := { n with nextTick := some (satAdd now (if n.isHub then HUB_TICK else NODE_TICK)) }
      N.tick e n now
    else n

/-- A DELTA from a hub: a hub that is told a member left drops it (`on_left`), then the copy of the sender takes the
entry. -/
def N.ofDelta (e : Env) (n : N) (now peer m : Nat) (rc : Rec) (a : Alive) : N :=
  let n := if n.isHub && a == .left then N.onLeft e n now m rc else n
  N.applyDelta e n now peer m rc a

/-- `on_frame`: handle one frame from `peer`. -/
def N.onFrame (e : Env) (n : N) (now peer : Nat) (f : NFrame) : N :=
  if n.revoked.has peer || n.leaving then n
  else
    let n := n.trace (.frameIn peer f.ty)
    let n := N.pulseRefresh e n now
    let fromHub := n.isBoot peer
    let n := if fromHub then
        let silent := match n.heard.get? peer with | some t => decide (e.giveUp peer < now - t) | none => false
        let n := if !n.isHub && silent then n.beginQuiet now 1 else n
        let n := { n with heard := n.heard.insert peer now, helloAt := n.helloAt.unset peer }
        let isAckSnap := match f with | .ack => true | .snap .. => true | _ => false
        let t0 := n.hsent.timeAt peer
        let n := if isAckSnap then { n with hsent := n.hsent.unset peer } else n
        let n := match t0 with
          | some t0 =>
            if isAckSnap && now - t0 < RTT_SAMPLE_MAX then
              let n := n.rttSample peer (now - t0)
              match n.primary with
              | some p =>
                if !n.isHub && p != peer then
                  let cur := n.hrtt.get? p
                  let new := (n.hrtt.get? peer).getD U64MAX
                  if n.hubUp now peer && (match cur with | none => true | some c => decide (min (new + HYST_ABS) U64MAX < c * 3 / 4)) then
                    N.reselect e n now
                  else n
                else n
              | none => n
            else n
          | none => n
        if n.primary.isNone then N.reselect e n now else n
      else n
    let isHello := match f with | .hello .. => true | _ => false
    let n := if n.isHub && !isHello && n.roster.has peer then
        { n with roster := n.roster.modify peer (fun l => { l with renewed := now }) } else n
    match f with
    | .hello rc snap homed => if n.isHub then N.onHello e n now peer rc snap homed else n
    | .probe => if fromHub && !n.isHub then N.helloTo e n peer false else n
    | .down m inc pf =>
      if n.isHub && fromHub then N.onDown e n now m inc pf
      else if fromHub then N.applyDown e n now peer m inc
      else n
    | .delta m rc a => if fromHub then N.ofDelta e n now peer m rc a else n
    | .snap part more es => if fromHub then N.applySnap e n now peer part more es else n
    | .ack => n
    | .other ty topic rest => n.bc (.frame peer ty topic rest)

/-- `on_bytes`: the complete frames at the start of the buffer, in order (at most `MAX_FRAMES_PER_CALL`), then, if the
next frame did not parse, the bad-frame trace. -/
def N.onBytes (e : Env) (n : N) (now peer : Nat) (fs : List NFrame) (bad : Bool) : N :=
  let n := (fs.take MAX_FRAMES_PER_CALL).foldl (fun n f => N.onFrame e n now peer f) n
  if bad then n.trace (.badFrame peer) else n

/-! ## Sessions, leave, revoke, move -/

/-- `session_up`: a hub stream to `peer` is up; `incoming` is true when `peer` dialed this node. -/
def N.sessionUp (e : Env) (n : N) (now peer : Nat) (incoming : Bool) : N :=
  if peer == n.me then n
  else if n.revoked.has peer then n.close peer .revoked
  else
    let silent := match n.heard.get? peer with | some t => decide (e.giveUp peer < now - t) | none => false
    let n := if !n.isHub && n.isBoot peer && silent then n.beginQuiet now 1 else n
    if MAX_TABLE ≤ n.up.len && !n.up.has peer then n.close peer .stale
    else
      let n := ({ n with up := n.up.insert peer now }).streamReset peer
      let n := if incoming then { n with attached := n.attached.del peer } else n
      if n.isBoot peer && (!incoming || n.isHub) then
        let n := if !n.isHub && n.primary == some peer then n.bc (.resub peer) else n
        N.helloTo e n peer true
      else n

/-- `session_down`: the session with `peer` ended with `code`. -/
def N.sessionDown (e : Env) (n : N) (now peer code : Nat) : N :=
  if !n.up.has peer then n
  else
    let n := { n with up := n.up.erase peer }
    let n := if n.isHub && code == LEAVE_CODE && !n.isBoot peer then
        N.hubDown e (n.trace (.leaveSeen peer)) now peer .left else n
    N.dropPeer e n now peer

/-- `leave`: close every session with the leave code, and stop renewing. -/
def N.leave (n : N) : N :=
  forKeys n.up.keys (fun p n => n.close p .leave) { n with leaving := true }

/-- `revoke`: drop the member from the view and the roster, forget its subscriptions and close every session with
it. `none` is `TableFull`. -/
def N.revoke (e : Env) (n : N) (now member : Nat) : Option N :=
  if !n.revoked.has member && MAX_TABLE ≤ n.revoked.len then none
  else
    let n := { n with revoked := n.revoked.ins member }
    let n := { n with hv := n.hv.map (fun (p : Nat × HubCopy) => (p.1, { p.2 with entries := p.2.entries.erase member })) }
    let n := { n with recheck := n.recheck.erase member, left := n.left.del member, susp := n.susp.erase member,
                      downed := n.downed.erase member, attached := n.attached.del member, homed := n.homed.del member }
    let n := match n.members.get? member with
      | some x =>
        let n := (({ n with members := n.members.erase member }).trace (.removed member Removal.revoked.toNat))
        let n := { n with goneVer := n.goneVer.erase member }
        let n := if n.isHub then N.homeDelta e n member x.rc .down else n
        n.bump
      | none => n
    let n := match n.roster.get? member with
      | some l => N.pushDelta e { n with roster := n.roster.erase member } now member l.rc .down
      | none => n
    let n := n.bc (.release member)
    let n := if n.up.has member then n.close member .revoked else n
    some (n.emit (.revoked member))

/-- `snapshot_to`: a hub sends an attached `peer` its snapshot again, without a new attachment. -/
def N.snapshotTo (e : Env) (n : N) (now peer : Nat) : N :=
  if n.isHub && n.attached.has peer then N.sendSnapshot e n now peer else n

/-- `set_max_frame`: the limit never goes below the default. -/
def N.setMaxFrame (n : N) (mb : Nat) : N := { n with maxFrame := max mb Pinc.MemCodec.maxBody }

/-- `address_changed`. -/
def N.addressChanged (n : N) (now : Nat) : N := { n with tag := n.tag.moved now }

/-! ## Start -/

inductive StartErr where
  | tooManyHubs | store | exhausted
  deriving DecidableEq, Repr

/-- `Membership::start`: `hubs` in the host's preference order. -/
def N.start (e : Env) (me : Nat) (isHub : Bool) (hubs : List Nat) (tracing : Bool) (now wall floor : Nat) :
    Except StartErr N :=
  let boot0 := hubs.foldl (fun acc h => if acc.contains h then acc else acc ++ [h]) []
  let boot := if isHub && !boot0.contains me then boot0 ++ [me] else boot0
  if MAX_HUBS < boot.length then .error .tooManyHubs
  else
    match Pinc.MemInc.start e.loc wall floor with
    | .error .store => .error .store
    | .error .exhausted => .error .exhausted
    | .ok (inc, loc) =>
      let (th, tag) := Tag.init.tag now e.refl e.hash
      let n : N := {
        me := me, isHub := isHub, boot := boot, born := now, leaving := false, inc := inc, tag := tag, ver := e.ver,
        th := th, sent := none, sealFailed := false, maxFrame := Pinc.MemCodec.maxBody, up := [], heard := [], revoked := [],
        hv := if isHub then [(me, ⟨[], 0, false⟩)] else [], members := [], epoch := 0, hrtt := [], hsent := [],
        helloAt := [], primary := if isHub then some me else none, homeOk := none, homeSeen := false, recheck := [],
        quietUntil := 0, regrace := false, held := [], nextAbsent := none, goneVer := [], left := [], nextRenew := now, nextTick := none,
        nextSlow := now, own := ⟨inc.word, e.ver, th⟩, roster := [], attached := [], homed := [], susp := [],
        downed := [], nextConf := none, events := [], lostEvents := 0, tracing := tracing, traces := [],
        lostTraces := 0, loc := loc, outSent := [], outBc := [], outClose := [] }
      .ok (n.trace (.started inc.word))

end Pinc.Membership
