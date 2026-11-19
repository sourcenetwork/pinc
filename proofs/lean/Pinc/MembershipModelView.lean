import Pinc.MembershipModelTypes

/-!
# The membership machine: the member view (`view.rs`)

`refresh_local`, `hello_to`, `renew`, `reselect`, `apply_delta`, `apply_snap`, `mark_absent`, `sweep_absent`,
`recompute_one`, `remove_from_view`, `recheck_due`, `home_delta`, step for step. `push_delta` (`hub.rs`) lives here too:
it calls `apply_delta`, whose first test (`member == me`) is false for the hub's own deltas to itself only through
`on_self_entry`'s first line (`hub == me` returns), so `pushDelta` uses `applyDeltaCore`, the code after that test,
and `applyDelta` is the test followed by the same core: the recursion of the code (`renew` -> `push_delta` ->
`apply_delta` -> `on_self_entry` -> `renew`) is cut at the one call that returns at once.
-/

set_option linter.unusedVariables false

namespace Pinc.Membership
open Pinc.MemInc

def N.refreshLocal (e : Env) (n : N) (now : Nat) : N :=
  let (t, tag') := n.tag.tag now e.refl e.hash
  { n with ver := e.ver, th := t, tag := tag' }

def N.helloTo (e : Env) (n : N) (peer : Nat) (snap : Bool) : N :=
  if n.leaving then n
  else
    let homed := !n.isHub && n.primary == some peer
    (N.tx e n peer .session (.hello ⟨n.inc.word, n.ver, n.th⟩ snap homed)).1

/-- The bookkeeping of a HELLO to `hub` in `renew`: `hello_at` keeps an armed time, else takes `now`; `hsent` takes
`now`. -/
def N.markHello (n : N) (hub now : Nat) : N :=
  let at_ := match n.helloAt.timeAt hub with | some t => some t | none => some now
  { n with helloAt := n.helloAt.insert hub at_, hsent := n.hsent.insert hub (some now) }

/-- `bump_record`: the next record of this life, or the seal failure. -/
def N.bumpRecord (n : N) : N :=
  match nextRecord n.loc n.inc with
  | .ok (w, i', l') => ({ n with inc := i', loc := l' }).trace (.incarnation w)
  | .error _ => ({ n with sealFailed := true }).trace .sealFailed

def N.pulseFresh (e : Env) (now hub : Nat) : Bool :=
  match e.evidence hub with
  | some ev => ev.pto == 0 && decide (now - ev.rx < PULSE_FRESH)
  | none => false

/-- `home_delta`: tell the members whose home this hub is. -/
def N.homeDelta (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : N :=
  forKeys n.homed.keys (fun p n => if p != m then N.deltaTo e n p m rc a else n) n

/-- Which hub copies feed the view right now. -/
structure Source where
  only : Option Nat
  hold : Bool
  anyFresh : Bool

def N.source (n : N) (now : Nat) : Source :=
  let home := n.primary.filter (fun p => !n.isHub && n.homeOk == some p && n.hv.has p && n.hubUp now p)
  match home with
  | some p => ⟨some p, false, true⟩
  | none => ⟨none, !n.isHub, n.hv.keys.any (fun k => n.hubUp now k)⟩

/-- The best candidate for `m` over the eligible copies: `(record, absent)`, and whether a copy's omission expired. -/
def N.candidates (n : N) (now : Nat) (src : Source) (m : Nat) : Option (Rec × Bool) × Bool :=
  n.hv.foldl
    (fun (acc : Option (Rec × Bool) × Bool) (p : Nat × HubCopy) =>
      let (best, expired) := acc
      let hub := p.1
      let eligible := match src.only with
        | some o => o == hub
        | none => !src.anyFresh || n.hubUp now hub
      if !eligible then acc
      else match p.2.entries.get? m with
        | none => acc
        | some ce =>
          let absent := ce.absentSince.isSome
          if (match ce.absentSince with | some t => decide (LEASE ≤ now - t) | none => false) then (best, true)
          else
            let better := match best with
              | none => true
              | some (b, babs) => decide (b.inc < ce.rc.inc) || (ce.rc.inc == b.inc && babs && !absent)
            if better then (some (ce.rc, absent), expired) else acc)
    (none, false)

/-- `remove_from_view`. Returns whether the view changed. -/
def N.removeFromView (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (expired : Bool) : N × Bool :=
  match cur with
  | none => (n, false)
  | some c =>
    if src.hold then
      ((if n.recheck.len < MAX_TABLE then { n with recheck := n.recheck.orIns m (n.quietUntil, n.regrace) } else n), false)
    else if now < n.quietUntil && n.recheck.len < MAX_TABLE then
      ((({ n with recheck := n.recheck.orIns m (n.quietUntil, n.regrace) }).trace (.deferred m)), false)
    else
      let n := { n with members := n.members.erase m }
      let n := if n.goneVer.len < MAX_TABLE || n.goneVer.has m then
          { n with goneVer := n.goneVer.insert m (c.rc.ver, c.rc.th) } else n
      let wasLeft := n.left.has m
      let n := { n with left := n.left.del m }
      let (why, a) : Removal × Alive := if wasLeft then (.left, .left) else if expired then (.leaseExpired, .down) else (.reported, .down)
      let n := n.trace (.removed m why.toNat)
      let n := n.emit (if wasLeft then .left m else .down m)
      let n := if n.isHub then N.homeDelta e n m c.rc a else n
      (n, true)

/-- `recompute_one`: decide `m`'s place in the view from the hub copies. Returns whether the view changed. -/
def N.recomputeOne (e : Env) (n : N) (now m : Nat) : N × Bool :=
  let src := n.source now
  let (best, expired) := n.candidates now src m
  let cur := n.members.get? m
  match best with
  | none => N.removeFromView e n now m cur src expired
  | some (best, absent) =>
    let n := if n.isHub && (match cur with | none => true | some c => decide (c.rc ≠ best)) then
        N.homeDelta e n m best .alive else n
    let (n, changed, early) : N × Bool × Bool :=
      match cur with
      | some c =>
        if best.inc / 65536 ≤ c.rc.inc / 65536 then
          if best.inc / 65536 == c.rc.inc / 65536 && c.rc.inc ≤ best.inc then
            let n := { n with members := n.members.modify m (fun x => { x with rc := { x.rc with inc := best.inc } }) }
            let (n, ch1) := if best.ver != c.rc.ver then
                (({ n with members := n.members.modify m (fun x => { x with rc := { x.rc with ver := best.ver } }) }).emit (.stack m best.ver), true)
              else (n, false)
            let (n, ch2) := if best.th != c.rc.th then
                (({ n with members := n.members.modify m (fun x => { x with rc := { x.rc with th := best.th } }) }).emit (.addr m), true)
              else (n, false)
            (n, ch1 || ch2, false)
          else (n, false, false)
        else
          let n := { n with members := n.members.insert m ⟨best⟩ }
          let n := n.emit (.joined m)
          let old := (some (c.rc.ver, c.rc.th)).orElse (fun _ => n.goneVer.get? m)
          let n := { n with goneVer := n.goneVer.erase m }
          let n := match old with
            | some (ver, th) => if ver != best.ver then n.emit (.stack m best.ver) else n
            | none => n
          (n, true, false)
      | none =>
        if n.members.len ≥ MAX_TABLE then (n, false, true)
        else
          let n := { n with members := n.members.insert m ⟨best⟩ }
          let n := n.emit (.joined m)
          let old := n.goneVer.get? m
          let n := { n with goneVer := n.goneVer.erase m }
          let n := match old with
            | some (ver, th) =>
              let n := if ver != best.ver then n.emit (.stack m best.ver) else n
              if th != best.th then n.emit (.addr m) else n
            | none => n
          (n, true, false)
    -- the view keeps no suspicion flag and reports no suspicion: an absent best record changes nothing here
    if early then (n, false) else (n, changed)

def N.bump (n : N) : N :=
  let n := { n with epoch := n.epoch + 1 }
  n.emit (.view n.epoch (min n.members.len U32MAX))

/-- A waiting removal due at `now` whose extra look has run: it is recomputed. -/
def recheckReady (now : Nat) (p : Nat × (Nat × Bool)) : Bool := decide (p.2.1 ≤ now) && p.2.2
/-- A waiting removal due at `now` whose extra look has not begun: it gets the look. -/
def recheckLook (now : Nat) (p : Nat × (Nat × Bool)) : Bool := decide (p.2.1 ≤ now) && !p.2.2
/-- A waiting removal after the first loop of `recheck_due`. -/
def recheckStep (now : Nat) (p : Nat × (Nat × Bool)) : Nat × (Nat × Bool) :=
  if recheckLook now p then (p.1, (satAdd now RECHECK_GAP, true)) else p

/-- The first part of `recheck_due`: the removals whose extra look ran leave the table, a due removal whose look has not
begun gets it (`RECHECK_GAP` from now) and the window lasts at least as long. -/
def N.recheckArm (n : N) (now : Nat) : N :=
  let n' := { n with recheck := (n.recheck.filter (fun p => !recheckReady now p)).map (recheckStep now) }
  if n.recheck.any (recheckLook now) then
    { n' with regrace := true, quietUntil := max n.quietUntil (satAdd now RECHECK_GAP) }
  else n'

/-- Recompute the members `ks` in order; whether the view changed. -/
def N.recheckFold (e : Env) (n : N) (now : Nat) (ks : List Nat) : N × Bool :=
  ks.foldl (fun (a : N × Bool) m => let (n', c) := N.recomputeOne e a.1 now m; (n', a.2 || c)) (n, false)

/-- The recompute of `recheck_due`: the members `ready`, in key order, with no window open (`quiet_until` is taken for
the loop and put back after it), then one bump if the view changed. -/
def N.recheckRun (e : Env) (n : N) (now : Nat) (ready : List Nat) : N :=
  let r := N.recheckFold e { n with quietUntil := 0 } now ready
  let n' := { r.1 with quietUntil := n.quietUntil }
  if r.2 then n'.bump else n'

/-- `recheck_due`: recompute the members whose deferral is due. A member gets one more look at the end of its window,
then is recomputed without a further deferral, whatever window a heal has opened since (#284). -/
def N.recheckDue (e : Env) (n : N) (now : Nat) : N :=
  let ready := AMap.keys (n.recheck.filter (recheckReady now))
  let n := N.recheckArm n now
  if ready.isEmpty then n else N.recheckRun e { n with regrace := false } now ready

/-- `apply_delta` after the test `member == me`. -/
def N.applyDeltaCore (e : Env) (n : N) (now hub : Nat) (m : Nat) (rc : Rec) (a : Alive) : N :=
  if n.revoked.has m then n
  else
    let (n, ok) : N × Bool :=
      if !n.hv.has hub then
        if MAX_HUBS ≤ n.hv.len then (n, false)
        else ({ n with hv := n.hv.insert hub ⟨[], 0, false⟩ }, true)
      else (n, true)
    if !ok then n
    else
      let n := match n.hv.get? hub with
        | none => n
        | some c =>
          match a with
          | .alive =>
            if c.entries.len < MAX_TABLE || c.entries.has m then
              { n with hv := n.hv.insert hub { c with entries := c.entries.insert m ⟨rc, c.round, none⟩ }, left := n.left.del m }
            else n
          | .down | .left =>
            match c.entries.get? m with
            | some x =>
              if x.rc.inc / 65536 ≤ rc.inc / 65536 then
                let n := { n with hv := n.hv.insert hub { c with entries := c.entries.erase m } }
                if a == .left && n.left.len < MAX_TABLE then { n with left := n.left.ins m } else n
              else n
            | none => n
      let (n, ch) := N.recomputeOne e n now m
      if ch then n.bump else n

/-- `push_delta`: one roster change at this hub: tell the attached hubs (and the homed members, for the hub's own
record) and fold it into this hub's own copy. -/
def N.pushDelta (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) : N :=
  let n := forKeys n.attached.keys
    (fun p n => if p != m && (n.isBoot p || (m == n.me && n.homed.has p)) then N.deltaTo e n p m rc a else n) n
  -- `apply_delta` with `hub == me`: for the node itself it returns at once (`on_self_entry`).
  if m == n.me then n else N.applyDeltaCore e n now n.me m rc a

/-- `renew`: renew the lease on every hub with a session. -/
def N.renew (e : Env) (n : N) (now : Nat) (forceSnap periodic : Bool) : N :=
  let n := if (match n.sent with | some s => decide (s ≠ (n.ver, n.th)) | none => false) then n.bumpRecord else n
  let periodic := if n.sent != some (n.ver, n.th) then false else periodic
  let n := { n with sent := some (n.ver, n.th) }
  let cur : Rec := ⟨n.inc.word, n.ver, n.th⟩
  let n := if n.isHub && decide (n.own ≠ cur) then N.pushDelta e { n with own := cur } now n.me cur .alive else n
  let n := n.boot.foldl
    (fun n hub =>
      if hub == n.me || !n.up.has hub then n
      else
        let snap := forceSnap || !n.hv.has hub
        if periodic && !snap && (n.primary != some hub || n.homeOk == some hub) && N.pulseFresh e now hub then
          n.trace (.helloSuppressed hub)
        else
          N.helloTo e (n.markHello hub now) hub snap) n
  { n with nextRenew := satAdd now RENEW }

/-- `on_self_entry`: a hub told us about ourselves. -/
def N.onSelfEntry (e : Env) (n : N) (now hub : Nat) (rc : Rec) (a : Alive) : N :=
  if hub == n.me then n
  else
    let n := n.trace (.selfDelta hub)
    if a == .alive && n.inc.word < rc.inc then
      match observe n.loc n.inc rc.inc with
      | .ok (true, i', l') => N.renew e (({ n with inc := i', loc := l' }).trace (.incarnation i'.word)) now false false
      | .ok (false, _, _) => n
      | .error _ => ({ n with sealFailed := true }).trace .sealFailed
    else if a != .alive || rc.inc < n.inc.word then N.helloTo e n hub false
    else n.bc (.resub hub)

/-- `apply_delta`. -/
def N.applyDelta (e : Env) (n : N) (now hub : Nat) (m : Nat) (rc : Rec) (a : Alive) : N :=
  if m == n.me then N.onSelfEntry e n now hub rc a else N.applyDeltaCore e n now hub m rc a

/-- `apply_down`: a hub reported `member` down with proof. -/
def N.applyDown (e : Env) (n : N) (now hub member inc : Nat) : N :=
  N.applyDelta e n now hub member ⟨inc, 0, [0, 0, 0, 0, 0, 0, 0, 0]⟩ .down

/-- `drop_gone`: a complete snapshot of `hub` listed round `round`; an earlier entry of a member the view does not list
is dropped from the copy (the code's `retain`). -/
def N.dropGone (n : N) (hub round : Nat) : N :=
  match n.hv.get? hub with
  | some c => { n with hv := n.hv.insert hub { c with entries := c.entries.filter (fun p => p.2.round == round || n.members.has p.1) } }
  | none => n

/-- `mark_absent`: a complete snapshot of `hub` listed round `round`; everything else in its copy is omitted. -/
def N.markAbsent (e : Env) (n : N) (now hub round : Nat) : N × Bool :=
  let ks := match n.hv.get? hub with | some c => c.entries.keys | none => []
  ks.foldl
    (fun (a : N × Bool) m =>
      let (n, changed) := a
      match (n.hv.get? hub).bind (fun c => c.entries.get? m) with
      | some ce =>
        if ce.round != round && ce.absentSince.isNone then
          let n := match n.hv.get? hub with
            | some c => { n with hv := n.hv.insert hub { c with entries := c.entries.modify m (fun x => { x with absentSince := some now }) } }
            | none => n
          let n := n.trace (.absent m)
          let (n, ch) := N.recomputeOne e n now m
          (n, changed || ch)
        else a
      | none => a)
    (n, false)

/-- `mark_view_absent`: a complete snapshot of the confirmed home listed round `round`. It is the whole view, so a
view member the home's copy does not hold, whichever hub's copy listed it, gets an entry there carrying the view's
record, one round before `round` (`round - 1`: a snapshot's round is at least 1 here), with the omission clock started;
with the copy full there is no room and the member is recomputed at once. The members are walked in key order, each
recomputed by itself, so the keys taken at the start are the ones the code's cursor visits. -/
def N.markViewAbsent (e : Env) (n : N) (now hub round : Nat) : N × Bool :=
  n.members.keys.foldl
    (fun (a : N × Bool) m =>
      let (n, changed) := a
      match n.members.get? m with
      | some v =>
        match n.hv.get? hub with
        | some c =>
          if c.entries.has m then a
          else if MAX_TABLE ≤ c.entries.len && !c.entries.has m then
            let (n, ch) := N.recomputeOne e n now m
            (n, changed || ch)
          else
            let n := { n with hv := n.hv.insert hub { c with entries := c.entries.insert m ⟨v.rc, round - 1, some now⟩ } }
            let n := n.trace (.absent m)
            let (n, ch) := N.recomputeOne e n now m
            (n, changed || ch)
        | none => a
      | none => a)
    (n, false)

/-- The omissions of a complete snapshot of `hub`: `mark_absent`, then, at a member whose confirmed home `hub` is,
`mark_view_absent`. -/
def N.snapAbsent (e : Env) (n : N) (now hub round : Nat) : N × Bool :=
  let a := N.markAbsent e n now hub round
  if !a.1.isHub && a.1.primary == some hub then
    let b := N.markViewAbsent e a.1 now hub round
    (b.1, a.2 || b.2)
  else a

/-- `apply_snap`: a snapshot frame from `hub`. -/
def N.applySnap (e : Env) (n : N) (now hub : Nat) (partial_ more : Bool) (es : List (Nat × Rec)) : N :=
  let (n, ok) : N × Bool :=
    if !n.hv.has hub then
      if MAX_HUBS ≤ n.hv.len then (n, false) else ({ n with hv := n.hv.insert hub ⟨[], 0, false⟩ }, true)
    else (n, true)
  if !ok then n
  else
    let (n, round) : N × Nat := match n.hv.get? hub with
      | some c =>
        let c := if !c.open_ then { c with round := c.round + 1, open_ := true } else c
        ({ n with hv := n.hv.insert hub c }, c.round)
      | none => (n, 0)
    let n := if !n.isHub && n.primary == some hub then { n with homeOk := some hub, homeSeen := true } else n
    let (n, changed, cnt) := es.foldl
      (fun (a : N × Bool × Nat) (p : Nat × Rec) =>
        let (n, changed, cnt) := a
        let cnt := cnt + 1
        let (m, rc) := p
        if m == n.me then (N.onSelfEntry e n now hub rc .alive, changed, cnt)
        else if n.revoked.has m then (n, changed, cnt)
        else
          match n.hv.get? hub with
          | some c =>
            if MAX_TABLE ≤ c.entries.len && !c.entries.has m then (n, changed, cnt)
            else
              let n := { n with hv := n.hv.insert hub { c with entries := c.entries.insert m ⟨rc, round, none⟩ } }
              let n := { n with left := n.left.del m }
              let (n, ch) := N.recomputeOne e n now m
              (n, changed || ch, cnt)
          | none =>
            let n := { n with left := n.left.del m }
            let (n, ch) := N.recomputeOne e n now m
            (n, changed || ch, cnt))
      (n, false, 0)
    let n := n.trace (.snapApplied hub cnt more)
    let (n, changed) : N × Bool :=
      if !more then
        let n := match n.hv.get? hub with
          | some c => { n with hv := n.hv.insert hub { c with open_ := false } }
          | none => n
        let (n, changed) := if !partial_ then
            let (n', ch) := N.snapAbsent e (n.dropGone hub round) now hub round
            (n', changed || ch)
          else (n, changed)
        let n := if n.primary == some hub then n.bc (.resub hub) else n
        (n, changed)
      else (n, changed)
    if changed then n.bump else n

/-- `sweep_absent`: drop copy entries whose omission has lasted a full lease. -/
def N.sweepAbsent (e : Env) (n : N) (now : Nat) : N :=
  let (n, changed) := n.hv.keys.foldl
    (fun (a : N × Bool) hub =>
      let ks := match a.1.hv.get? hub with | some c => c.entries.keys | none => []
      ks.foldl
        (fun (a : N × Bool) m =>
          let (n, changed) := a
          let expired := match (n.hv.get? hub).bind (fun c => c.entries.get? m) with
            | some ce => (match ce.absentSince with | some t => decide (LEASE ≤ now - t) | none => false)
            | none => false
          if expired then
            let (n, ch) := N.recomputeOne e n now m
            let n := match n.hv.get? hub with
              | some c => { n with hv := n.hv.insert hub { c with entries := c.entries.erase m } }
              | none => n
            (n, changed || ch)
          else a)
        a)
    (n, false)
  if changed then n.bump else n

/-- `rtt_sample`: fold a transport round trip sample into the hub's smoothed round trip. -/
def N.rttSample (n : N) (hub r : Nat) : N :=
  let v := match n.hrtt.get? hub with
    | some old => min r ((3 * old + r) / 4)
    | none => r
  { n with hrtt := n.hrtt.insert hub v }

/-- The best hub by round trip, then by position among the other hubs. -/
def N.bestHub (n : N) (now : Nat) : Option Nat :=
  let others := n.boot.filter (fun x => x != n.me)
  let r := (others.zipIdx.foldl
    (fun (best : Option ((Nat × Nat) × Nat)) (p : Nat × Nat) =>
      let (hub, i) := p
      if n.hubUp now hub then
        let k := ((n.hrtt.get? hub).getD RTT_UNKNOWN, i)
        match best with
        | none => some (k, hub)
        | some (bk, _) => if k.1 < bk.1 || (k.1 == bk.1 && k.2 < bk.2) then some (k, hub) else best
      else best) none)
  r.map (·.2)

/-- `reselect`: pick the primary hub: the lowest round trip, keeping the current one unless the new one beats it by
20 ms and a quarter. -/
def N.reselect (e : Env) (n : N) (now : Nat) : N :=
  let p : Option Nat :=
    if n.isHub then some n.me
    else
      let p := n.bestHub now
      match p, n.primary with
      | some np, some cur =>
        if np != cur && n.hubUp now cur then
          let rc := (n.hrtt.get? cur).getD RTT_UNKNOWN
          let rn := (n.hrtt.get? np).getD RTT_UNKNOWN
          if min (rc * 3) U64MAX / 4 ≤ min (rn + HYST_ABS) U64MAX then some cur else p
        else p
      | _, _ => p
  match p with
  | none => n
  | some p =>
    if n.primary == some p then n
    else
      let old := n.primary
      let n := ({ n with primary := some p }).trace (.primary p)
      let n := if !n.isHub then
          let n := { n with homeOk := none }
          let n := N.helloTo e n p true
          match old with
          | some o => if n.up.has o then N.helloTo e n o false else n
          | none => n
        else n
      n.bc (.primary old p)

end Pinc.Membership
