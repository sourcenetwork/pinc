import Pinc.Axioms

/-!
# The receive path of one broadcast node, and the system around it

The executable counterpart of `proofs/tla/BroadcastNodeOps.tla` (the operators), `BroadcastNode.tla` (the harness)
and `BroadcastLogOps.tla` (the hub log): the functions of `msg.rs` (`on_msg`, `hub_store`, `offer`, `offer_held`,
`acp_answer`), `floors.rs` (`is_old`, `hold_for_floor`, `floor_check`), `timers.rs` (`sweep`, `poll_timeout`) and
`table.rs` (`Seen`) over one topic, ported operator by operator with the TLA names and the TLA case order.

Every operator returns a `Res`: the new node `n`, the trace records `outs` in order, the ids delivered to the
application `dl` in order, the `ack` frames sent and the ids `acc`ounted for. All functions are total and
executable (structural recursion, or a fuel that the shrinking list always covers), so a replay tool runs them on
recorded traces. All constants of the TLA model are fields of `Params`; the TLC configs are instances.

Differences from the TLA text, each exact for what is stated:
* Ids, origins and stamps are `Nat` without a finite universe. The access-verdict table is an association list
  `acp` (its length is the TLA cardinality of the defined entries), the set `req` and the accounting `acc` are
  lists (membership is the set).
* The hub log keeps the entries and the byte accounting (`used`, `wpos`) of `BroadcastLogOps`; the index is
  membership of the id in `entries` (a push refuses an id that is present, so entries never repeat an id, which
  is what makes the TLA index exact); the byte cells, which only the log model itself reads, are not repeated.
* `SInsert` returns the new set (the TLA record also has `ok`, which no caller reads), and `Head` of an empty
  order is the empty-order no-op; the TLA run stops there with an error, and the theorems assume `0 < seenCap`,
  which is what keeps that case away.
* The TLA assertion in `SPush` ("the map refused an id the set had room for") is not repeated: it cannot
  fire, because every map entry is an order entry (`SeenInv.map` in `BroadcastNodeLemmas1`).
* `store` (the print of each stored message, the content here) is not tidied: the TLA `Tidy` drops the entry of an
  id that neither the log nor the dedupe map holds, and a duplicate reads it only for an id one of them holds, where
  the two agree. `AckById` (the old rule) is a TLA witness only.
* The environment is unbounded: `MaxNow` and `MaxLife` (bounds for the model checker) are dropped, `Stamps`,
  `Sizes`, `Paths` are all values.
-/

namespace Pinc.BroadcastNode

/-! ## Parameters and messages -/

/-- The constants of the TLA model. -/
structure Params where
  ttl : Nat
  seenCap : Nat
  logRing : Nat
  logCap : Nat
  logWin : Nat
  fholdMax : Nat
  heldMax : Nat
  checksMax : Nat
  acpCap : Nat
  acpMax : Nat
  floorWait : Nat
  oldSlack : Nat
  me : Nat
  isHub : Bool
  revoked : List Nat
  heldDedup : Bool
  heldFullKeepsUnseen : Bool
  topicFull : Bool
  ackAfterStore : Bool
  gather : Bool
  evictGuard : Bool
  /-- A hub keeps the print of a message it stored after the log let it go (the dedupe map carries it); `false`
  compares only while the log holds the id. -/
  keepPrint : Bool
  /-- Only a copy due an acknowledgement is compared with the stored print; `false` compares every copy. -/
  dueOnly : Bool

/-- What the checks before the signature find (`graft`: the id and signature of a stored message under another body,
which never verifies as a new message). -/
inductive MsgKind where
  | good | badhead | big | badsig | graft
  deriving DecidableEq, Repr

/-- A message: id, origin, hybrid timestamp as one number, what the checks find, size of head and body, and the
body (an opaque value: the hash of the body and the flag the signature covers). -/
structure Msg where
  mid : Nat
  origin : Nat
  ts : Nat
  kind : MsgKind
  n : Nat
  body : Nat × Bool
  deriving DecidableEq, Repr

/-- What a hub's log holds for an id besides the id: origin, timestamp, body (`Content` of the TLA text). -/
abbrev Content := Nat × Nat × (Nat × Bool)

/-- The content of a message. -/
def Msg.content (m : Msg) : Content := (m.origin, m.ts, m.body)

/-- A message that no step uses: the ghost of a step that is not a message. -/
def Msg.zero : Msg := ⟨0, 0, 0, .good, 0, (0, false)⟩

/-- The part of a message that is held and offered again (`mid`, `origin`, `ts`). -/
structure Ent where
  mid : Nat
  origin : Nat
  ts : Nat
  deriving DecidableEq, Repr

/-- The entry of a message. -/
def Msg.ent (m : Msg) : Ent := ⟨m.mid, m.origin, m.ts⟩

/-- The frame type a message arrives by. -/
inductive Frame where
  | pub | fan | fanp | msg | other
  deriving DecidableEq, Repr

/-! ## `table.rs` Seen: ids to the time they were recorded, in insertion order -/

/-- The dedupe set: the association, the insertion order and the newest time. -/
structure Seen where
  map : Nat → Option Nat
  order : List (Nat × Nat)
  last : Nat

/-- The empty set. -/
def SeenEmpty : Seen := ⟨fun _ => none, [], 0⟩

/-- `map` with one key set. -/
def mapSet (f : Nat → Option Nat) (k : Nat) (v : Option Nat) : Nat → Option Nat :=
  fun x => if x = k then v else f x

/-- `Seen::contains`: recorded and not older than the ttl. -/
def SContains (p : Params) (S : Seen) (mid now : Nat) : Bool :=
  match S.map mid with
  | some t => decide (now - t ≤ p.ttl)
  | none => false

/-- The newest recorded time, if any. -/
def SNewest (S : Seen) : Option Nat := match S.order with | [] => none | _ => some S.last

/-- The instant the oldest record expires. -/
def SNextExpiry (p : Params) (S : Seen) : Option Nat :=
  match S.order with | [] => none | e :: _ => some (e.2 + p.ttl + 1)

/-- The oldest record leaves; its id is forgotten unless a newer record replaced it in the map. -/
def SPopFront (S : Seen) : Seen :=
  match S.order with
  | [] => S
  | e :: rest => ⟨if S.map e.1 = some e.2 then mapSet S.map e.1 none else S.map, rest, S.last⟩

/-- Pop the expired records, at most `f` of them (the fuel is the order length, which covers all). -/
def SExpireAux (p : Params) (now : Nat) : Nat → Seen → Seen
  | 0, S => S
  | f + 1, S =>
    match S.order with
    | [] => S
    | e :: _ => if p.ttl < now - e.2 then SExpireAux p now f (SPopFront S) else S

/-- `Seen::expire`. -/
def SExpire (p : Params) (S : Seen) (now : Nat) : Seen := SExpireAux p now S.order.length S

/-- Record an id at `now`. -/
def SPush (S : Seen) (mid now : Nat) : Seen :=
  ⟨mapSet S.map mid (some now), S.order ++ [(mid, now)], now⟩

/-- `Seen::insert`: a full set refuses unless forced, which drops the oldest record first. -/
def SInsert (p : Params) (S : Seen) (mid now : Nat) (force : Bool) : Seen :=
  if p.seenCap ≤ S.order.length then (if force then SPush (SPopFront S) mid now else S) else SPush S mid now

/-- Record the evicted ids, each unless the set still holds it (the guard is the code after the fix). -/
def SInsertAll (p : Params) (S : Seen) (now : Nat) : List Nat → Seen
  | [] => S
  | i :: ids =>
    SInsertAll p (if p.evictGuard && SContains p S i now then S else SInsert p S i now true) now ids

/-- Re-record the ids that left the log in a sweep, each unless the set holds it. -/
def SweepIds (p : Params) (S : Seen) (now : Nat) : List Nat → Seen
  | [] => S
  | i :: ids => SweepIds p (if SContains p S i now then S else SInsert p S i now true) now ids

/-! ## The hub log (`BroadcastLogOps`) -/

/-- A logged message: id, arrival time, wall clock, ring offset and length, ring cost (padding included). -/
structure LEntry where
  mid : Nat
  at_ : Nat
  wall : Nat
  off : Nat
  len : Nat
  cost : Nat
  deriving DecidableEq, Repr

/-- The hub log: entries oldest first, the write position and the bytes in use. -/
structure Log where
  entries : List LEntry
  wpos : Nat
  used : Nat
  deriving DecidableEq, Repr

/-- The empty log. -/
def LEmpty : Log := ⟨[], 0, 0⟩

/-- `Contains`: the id is logged. -/
def LContains (L : Log) (mid : Nat) : Bool := L.entries.any (fun e => e.mid == mid)

/-- `Pop`: the oldest entry leaves; the ring restarts when the log empties. -/
def LPop (L : Log) : Log :=
  match L.entries with
  | [] => L
  | e :: rest => ⟨rest, if rest.isEmpty then 0 else L.wpos, if rest.isEmpty then 0 else L.used - e.cost⟩

/-- The padding a write of `n` bytes needs at the write position. -/
def LPad (p : Params) (L : Log) (n : Nat) : Nat := if p.logRing < L.wpos + n then p.logRing - L.wpos else 0

/-- `Write`: append the entry at the write position (or at 0 after padding). -/
def LWrite (p : Params) (L : Log) (mid at_ wall n : Nat) : Log :=
  let pad := LPad p L n
  let off := if 0 < pad then 0 else L.wpos
  ⟨L.entries ++ [⟨mid, at_, wall, off, n, pad + n⟩], (off + n) % p.logRing, L.used + pad + n⟩

/-- The result of `Push`: the new log, whether it was stored, the evicted ids in order. -/
structure PushRes where
  log : Log
  ok : Bool
  ev : List Nat

/-- `Loop` with a fuel (the entries shrink by one per round, so `entries.length + 1` covers it). -/
def LLoop (p : Params) (mid at_ wall n : Nat) : Nat → Log → List Nat → PushRes
  | 0, L, ev => ⟨L, false, ev⟩
  | f + 1, L, ev =>
    if L.entries.length < p.logCap ∧ L.used + LPad p L n + n ≤ p.logRing then ⟨LWrite p L mid at_ wall n, true, ev⟩
    else match L.entries with
      | [] => ⟨L, false, ev⟩
      | e :: _ => LLoop p mid at_ wall n f (LPop L) (ev ++ [e.mid])

/-- `Push`: the new log, whether it was stored, and the evicted ids in order. -/
def LPush (p : Params) (L : Log) (mid at_ wall n : Nat) : PushRes :=
  if p.logRing < n ∨ LContains L mid = true then ⟨L, false, []⟩
  else LLoop p mid at_ wall n (L.entries.length + 1) L []

/-- The result of `Expire`. -/
structure ExpRes where
  log : Log
  ev : List Nat

/-- `ExpireLoop` with a fuel. -/
def LExpireAux (p : Params) (now : Nat) : Nat → Log → List Nat → ExpRes
  | 0, L, ev => ⟨L, ev⟩
  | f + 1, L, ev =>
    match L.entries with
    | [] => ⟨L, ev⟩
    | e :: _ => if p.logWin < now - e.at_ then LExpireAux p now f (LPop L) (ev ++ [e.mid]) else ⟨L, ev⟩

/-- `Expire`: drop the messages older than the window. -/
def LExpire (p : Params) (L : Log) (now : Nat) : ExpRes := LExpireAux p now L.entries.length L []

/-! ## The node, the results and the trace records -/

/-- The phase of the floor gathering. -/
inductive Phase where
  | never | gathering | done
  deriving DecidableEq, Repr

/-- A cached access verdict. -/
structure AcpE where
  allow : Bool
  exp : Nat
  deriving DecidableEq, Repr

/-- An outstanding access check. -/
structure Check where
  id : Nat
  origin : Nat
  deriving DecidableEq, Repr

/-- The state of one node (`NodeInit`). `ofloor = none` is `NoOf`, a missing `rfloor` is `NoT`. -/
structure Node where
  seen : Seen
  lg : Log
  sub : Bool
  req : List Nat
  phase : Phase
  rfloor : Option Nat
  ofloor : Option (Nat → Option Nat)
  nohist : Bool
  fhold : List Ent
  acp : List (Nat × AcpE)
  checks : List Check
  nextCheck : Nat
  held : List Ent
  born : Nat
  /-- What the log holds for each id it holds (the entry of an id that left the log means nothing). -/
  store : Nat → Option Content

/-- Why a message was refused. -/
inductive Why where
  | topicsFull | seenFull | old | heldFull | badHead | duplicate | idTaken | revoked | badSignature | logFull
  deriving DecidableEq, Repr

/-- Why a message is held. -/
inductive HoldWhy where
  | floor | acp
  deriving DecidableEq, Repr

/-- How a message reached the application. -/
inductive Via where
  | cache | answer
  deriving DecidableEq, Repr

/-- The trace records of the receive path. -/
inductive TraceRec where
  | stored (mid : Nat) (fanned : Bool)
  | rejected (mid : Nat) (why : Why)
  | delivered (mid origin ts : Nat) (via : Via)
  | held (mid : Nat) (why : HoldWhy)
  | acpAsked (id origin : Nat)
  | acpAnswered (id : Nat) (allow : Bool) (origin : Nat)
  | repaired (mid : Nat)
  | floorDone (used : Bool)
  deriving DecidableEq, Repr

/-- An operator's result. -/
structure Res where
  n : Node
  outs : List TraceRec
  dl : List Nat
  ack : Nat
  acc : List Nat

/-- A result with no delivery, ack or accounting. -/
def Plain (n : Node) (outs : List TraceRec) : Res := ⟨n, outs, [], 0, []⟩

/-- Run `F` on the node of `r` and append what it emitted. -/
def Bind (r : Res) (F : Node → Res) : Res :=
  let r2 := F r.n
  ⟨r2.n, r.outs ++ r2.outs, r.dl ++ r2.dl, r.ack + r2.ack, r.acc ++ r2.acc⟩

/-- `NodeInit`. -/
def NodeInit (p : Params) (born : Nat) : Node :=
  ⟨SeenEmpty, LEmpty, true, [], if p.isHub then .never else if p.gather then .gathering else .done,
   none, none, false, [], [], [], 1, [], born, fun _ => none⟩

/-! ## `floors.rs` -/

/-- `IsOld`: the message is at or below a floor. -/
def IsOld (p : Params) (N : Node) (origin ts : Nat) : Bool :=
  match N.ofloor with
  | some f => match f origin with | some x => decide (ts ≤ x) | none => false
  | none =>
    if (match N.rfloor with | some r => decide (ts ≤ r) | none => false) then true
    else N.rfloor.isNone && !N.nohist && decide (ts + p.oldSlack < N.born)

/-- `HoldFloor`: hold a message offered while the floors are gathered. -/
def HoldFloor (p : Params) (N : Node) (m : Ent) : Res :=
  if p.fholdMax ≤ N.fhold.length ∨ N.fhold.any (fun e => e.mid == m.mid) = true then Plain N []
  else Plain {N with fhold := N.fhold ++ [m]} [.held m.mid .floor]

/-! ## `msg.rs` offer -/

/-- A check for the origin is outstanding. -/
def AskedFor (N : Node) (o : Nat) : Bool := N.checks.any (fun c => c.origin == o)

/-- The id is already held for a verdict. -/
def HeldHas (N : Node) (mid : Nat) : Bool := N.held.any (fun e => e.mid == mid)

/-- The part of `offer` after the verdict cache missed: hold the message and ask. -/
def HoldAndAsk (p : Params) (N : Node) (m : Ent) : Res :=
  let dupHeld := p.heldDedup && HeldHas N m.mid
  let heldOK := decide (N.held.length < p.heldMax) && !dupHeld
  let N2 := if heldOK then {N with held := N.held ++ [m]} else N
  let ask := !AskedFor N2 m.origin && decide (N2.checks.length < p.checksMax)
  let N3 := if ask then {N2 with checks := N2.checks ++ [⟨N2.nextCheck, m.origin⟩], nextCheck := N2.nextCheck + 1} else N2
  ⟨N3, (if heldOK then [.held m.mid .acp] else []) ++ (if ask then [.acpAsked N2.nextCheck m.origin] else []),
   [], 0, if heldOK || dupHeld || p.heldFullKeepsUnseen then [m.mid] else []⟩

/-- `offer`: record the id, then deliver, hold and ask, or refuse. -/
def Offer (p : Params) (N : Node) (now : Nat) (m : Ent) : Res :=
  if p.topicFull then ⟨N, [.rejected m.mid .topicsFull], [], 0, [m.mid]⟩
  else if p.seenCap ≤ N.seen.order.length then ⟨N, [.rejected m.mid .seenFull], [], 0, [m.mid]⟩
  else
    let old := IsOld p N m.origin m.ts
    let a := N.acp.lookup m.origin
    let cached := match a with | some e => decide (now ≤ e.exp) | none => false
    let allow := match a with | some e => e.allow | none => false
    let needsHold := N.sub && !old && m.origin != p.me && !cached
    let full := needsHold && p.heldFullKeepsUnseen && decide (p.heldMax ≤ N.held.length) && !(p.heldDedup && HeldHas N m.mid)
    if N.phase = .gathering ∧ p.isHub = false then HoldFloor p N m
    else if full then
      let r := HoldAndAsk p N m
      ⟨r.n, r.outs ++ [.rejected m.mid .heldFull], [], 0, [m.mid]⟩
    else
      let N1 := {N with seen := SInsert p N.seen m.mid now false}
      if !N.sub || old || m.origin == p.me then ⟨N1, if old then [.rejected m.mid .old] else [], [], 0, [m.mid]⟩
      else if cached then
        if allow then ⟨N1, [.delivered m.mid m.origin m.ts .cache], [m.mid], 0, [m.mid]⟩
        else ⟨N1, [], [], 0, [m.mid]⟩
      else HoldAndAsk p N1 m

/-- The id is a duplicate: recorded and unexpired, or in the log. -/
def IsDup (p : Params) (N : Node) (mid now : Nat) : Bool := SContains p N.seen mid now || LContains N.lg mid

/-- The print a frame carries: a good message's is its content; a graft (the id and signature of a stored message
under another body) carries the print stored under its id. The other kinds carry none that is compared. -/
def Print (N : Node) (m : Msg) : Option Content := if m.kind = .graft then N.store m.mid else some m.content

/-- The print held for the id is the frame's: a message whose signature verifies, with the origin, timestamp and body
the node stored under the id (the signature binds them, so another message has another print), or a graft of the
stored message, whose signature is the stored one (a graft for an id the node holds no print for is another message's:
the code answers that the id is taken). A frame that fails the signature check otherwise never has the stored print. -/
def SameStored (N : Node) (m : Msg) : Bool :=
  (decide (m.kind = .good) && decide (N.store m.mid = some m.content)) ||
    (decide (m.kind = .graft) && (N.store m.mid).isSome)

/-- A known id: a copy due an acknowledgement (`0 < ack`) is compared with the print held for the id, while the log
holds the id and, with `keepPrint`, after the log let it go. The same print is a duplicate that is acknowledged, a
different one is refused with `idTaken` and no acknowledgement. A copy due none is a plain duplicate and compares
nothing (`dueOnly`; `false` compares every copy). -/
def DupRes (p : Params) (N : Node) (m : Msg) (ack : Nat) : Res :=
  let look := (p.keepPrint || LContains N.lg m.mid) && (decide (0 < ack) || !p.dueOnly)
  ⟨N, [.rejected m.mid (if look && !SameStored N m then .idTaken else .duplicate)], [],
    if look && SameStored N m then ack else 0, []⟩

/-- `offer_held`: offered again unless it arrived another way meanwhile. -/
def OfferHeld (p : Params) (N : Node) (now : Nat) (e : Ent) : Res :=
  if IsDup p N e.mid now then Plain N [] else Offer p N now e

/-- Offer each held entry in turn. -/
def OfferAll (p : Params) (now : Nat) (r : Res) : List Ent → Res
  | [] => r
  | e :: es => OfferAll p now (Bind r (fun x => OfferHeld p x now e)) es

/-- `floor_check`: the floors are settled (or the wait ran out): offer what was held. -/
def FloorsSettled (p : Params) (N : Node) (now : Nat) (used : Bool) (rf : Option Nat)
    (of_ : Option (Nat → Option Nat)) (nh : Bool) : Res :=
  let N1 := {N with phase := .done, rfloor := rf, ofloor := of_, nohist := nh, fhold := []}
  OfferAll p now (Plain N1 [.floorDone used]) N.fhold

/-! ## `msg.rs` hub_store and on_msg -/

/-- `hub_store`: log the message, record the evicted ids, then offer or record it. -/
def HubStore (p : Params) (N : Node) (now wall : Nat) (fanned : Bool) (m : Msg) : Res :=
  if p.topicFull then Plain N [.rejected m.mid .topicsFull]
  else
    let r := LPush p N.lg m.mid now wall m.n
    let N1 := {N with seen := SInsertAll p N.seen now r.ev, lg := r.log}
    if !r.ok then Plain N1 [.rejected m.mid .logFull]
    else
      let st : List TraceRec := [.stored m.mid fanned]
      if N1.sub && m.origin != p.me then Bind (Plain N1 st) (fun x => Offer p x now m.ent)
      else ⟨{N1 with seen := SInsert p N1.seen m.mid now true}, st, [], 0, [m.mid]⟩

/-- Which frame types this node accepts. -/
def Allowed (p : Params) (t : Frame) (fromBoot : Bool) : Bool :=
  match t with
  | .pub | .fan | .fanp => p.isHub
  | .msg => fromBoot
  | .other => true

/-- Whether a record is `Stored`. -/
def IsStored : TraceRec → Bool
  | .stored .. => true
  | _ => false

/-- Once a message is stored the log holds it: its content is the entry of its id. -/
def NoteStored (m : Msg) (r : Res) : Res :=
  if r.outs.any IsStored then
    {r with n := {r.n with store := fun x => if x = m.mid then some m.content else r.n.store x}}
  else r

/-- `on_msg`. -/
def OnMsg (p : Params) (N : Node) (now wall : Nat) (t : Frame) (fromBoot : Bool) (m : Msg) : Res :=
  if !Allowed p t fromBoot then Plain N []
  else if m.kind = .badhead then Plain N [.rejected 0 .badHead]
  else if m.kind = .big then Plain N [.rejected m.mid .badHead]
  else
    let ack := if p.isHub && (t = .pub || t = .fanp) then 1 else 0
    if IsDup p N m.mid now then DupRes p N m ack
    else if p.revoked.contains m.origin then Plain N [.rejected m.mid .revoked]
    else if m.kind = .badsig ∨ m.kind = .graft then Plain N [.rejected m.mid .badSignature]
    else
      let rep := N.req.contains m.mid
      let N1 := {N with req := N.req.filter (fun x => x != m.mid)}
      let o1 : List TraceRec := if rep then [.repaired m.mid] else []
      let early := if p.ackAfterStore then 0 else ack
      let r0 : Res := ⟨N1, o1, [], early, []⟩
      if p.isHub then
        let rh := Bind r0 (fun x => HubStore p x now wall (t = .fan || t = .fanp) m)
        NoteStored m {rh with ack := rh.ack + (if p.ackAfterStore && rh.outs.any IsStored then ack else 0)}
      else Bind r0 (fun x => Offer p x now m.ent)

/-- `acp_answer`: a verdict arrives for an outstanding check. -/
def AcpAnswer (p : Params) (N : Node) (now id : Nat) (allow : Bool) : Res :=
  match N.checks.find? (fun c => c.id == id) with
  | none => Plain N []
  | some c =>
    let origin := c.origin
    let cached := decide (N.acp.length < p.acpMax)
    let acp1 := if (N.acp.lookup origin).isSome || cached then
        (if (N.acp.lookup origin).isSome then N.acp.map (fun e => if e.1 == origin then (origin, ⟨allow, now + p.acpCap⟩) else e)
         else N.acp ++ [(origin, ⟨allow, now + p.acpCap⟩)])
      else N.acp
    let mine := N.held.filter (fun e => e.origin == origin)
    let N1 := {N with checks := N.checks.eraseP (fun c => c.id == id), acp := acp1,
                      held := N.held.filter (fun e => e.origin != origin)}
    let dels := if allow then mine else []
    ⟨N1, .acpAnswered id allow origin :: dels.map (fun e => .delivered e.mid origin e.ts .answer), dels.map (·.mid), 0, []⟩

/-- `on_have` (`gap.rs`): the ids this node lacks are asked for and remembered as requested. -/
def OnHave (p : Params) (N : Node) (now : Nat) (fromBoot : Bool) (ids : List Nat) : Res :=
  if !fromBoot then Plain N []
  else Plain {N with req := N.req ++ ids.filter (fun i => !SContains p N.seen i now && !LContains N.lg i && !N.req.contains i)} []

/-! ## `timers.rs` -/

/-- `Sweep`: expire the set and the log, re-record the ids that left the log. -/
def Sweep (p : Params) (N : Node) (now : Nat) : Node :=
  let S1 := SExpire p N.seen now
  let e := LExpire p N.lg now
  {N with seen := SweepIds p S1 now e.ev, lg := e.log}

/-- `on_timer`: sweep, and end the floor wait when it ran out. -/
def OnTimer (p : Params) (N : Node) (now : Nat) : Res :=
  let N1 := Sweep p N now
  if N1.phase = .gathering ∧ p.floorWait < now - N1.born then FloorsSettled p N1 now false none none false
  else Plain N1 []

/-- The minimum of a list, `none` for the empty list. -/
def MinOf : List Nat → Option Nat
  | [] => none
  | x :: xs => match MinOf xs with | none => some x | some y => some (min x y)

/-- `poll_timeout`: the next deadline the host calls `on_timer` at. -/
def PollTimeout (p : Params) (N : Node) : Option Nat :=
  MinOf ([SNextExpiry p N.seen,
          match N.lg.entries with | [] => none | e :: _ => some (e.at_ + p.logWin + 1),
          if N.phase = .gathering then some (N.born + p.floorWait + 1) else none].filterMap id)

/-! ## The system: `BroadcastNode.tla` -/

/-- Which step produced the current record. -/
inductive Last where
  | init | msg | timer | answer | floors | tick | restart
  deriving DecidableEq, Repr

/-- The harness state: the node, the clock, the life, and the ghosts `cnt` (deliveries in the life), `recd` (when
an id was last recorded), `capd` (the set dropped it early), `ep` (epochs), the accounted ids, the last step's
records, deliveries, acks and the acknowledged message. -/
structure Sys where
  node : Node
  now : Nat
  life : Nat
  cnt : Nat → Nat
  recd : Nat → Nat
  capd : Nat → Bool
  ep : Nat → Nat
  acct : List Nat
  outs : List TraceRec
  dls : List Nat
  last : Last
  ackd : Nat
  lm : Msg

/-- `Init`. -/
def SInit (p : Params) : Sys :=
  ⟨NodeInit p 0, 0, 0, fun _ => 0, fun _ => 0, fun _ => false, fun _ => 0, [], [], [], .init, 0, Msg.zero⟩

/-- `NewRec`: a new record of the id, not a refresh of a live one. -/
def NewRec (p : Params) (now : Nat) (old new : Node) (m : Nat) : Bool :=
  (new.seen.map m).isSome && new.seen.map m != old.seen.map m &&
    ((old.seen.map m).isNone || p.ttl < now - (old.seen.map m).getD 0)

/-- `Rec`. -/
def RecG (old new : Node) (rec : Nat → Nat) : Nat → Nat :=
  fun m => if (new.seen.map m).isSome ∧ new.seen.map m ≠ old.seen.map m then (new.seen.map m).getD 0 else rec m

/-- `Cap`. -/
def CapG (p : Params) (now : Nat) (old new : Node) (capd : Nat → Bool) : Nat → Bool :=
  fun m => if (new.seen.map m).isSome ∧ new.seen.map m ≠ old.seen.map m then false
    else if (old.seen.map m).isSome ∧ (new.seen.map m).isNone ∧ now - (old.seen.map m).getD 0 ≤ p.ttl then true
    else capd m

/-- `Ep`. -/
def EpG (p : Params) (now : Nat) (old new : Node) (ep : Nat → Nat) : Nat → Nat :=
  fun m => if NewRec p now old new m then ep m + 1 else ep m

/-- `Apply`: take the result of an operator as one step of the system. The ghost `lm` is the message only when the
step acknowledged one (`NoMsg` otherwise, `lm' = IF r.ack > 0 THEN msg ELSE NoMsg` of the TLA text). -/
def Apply (p : Params) (s : Sys) (r : Res) (what : Last) (m : Msg) : Sys :=
  ⟨r.n, s.now, s.life, fun m => s.cnt m + r.dl.count m, RecG s.node r.n s.recd, CapG p s.now s.node r.n s.capd,
   EpG p s.now s.node r.n s.ep, s.acct ++ r.acc, r.outs, r.dl, what, r.ack, if 0 < r.ack then m else Msg.zero⟩

/-- The tick guard: time passes only up to the next deadline `PollTimeout` names. -/
def TickOk (p : Params) (N : Node) (now : Nat) : Bool :=
  match PollTimeout p N with | none => true | some t => decide (now < t)

/-- The restart of the node. -/
def Restarted (p : Params) (s : Sys) : Sys :=
  ⟨NodeInit p s.now, s.now, s.life + 1, fun _ => 0, fun _ => 0, fun _ => false, fun _ => 0, [], [], [], .restart, 0, Msg.zero⟩

/-- Time passes by one: the step records are cleared. -/
def Ticked (s : Sys) : Sys := {s with now := s.now + 1, outs := [], dls := [], last := .tick, ackd := 0, lm := Msg.zero}

/-- `Next`: a message by any frame, the timer, an answer to an outstanding check, the floors settled in any way
(`rf`, `of_`, `nh` are any values), time passing, a restart. -/
inductive Step (p : Params) : Sys → Sys → Prop where
  | msg (s : Sys) (t : Frame) (b : Bool) (m : Msg) :
      Step p s (Apply p s (OnMsg p s.node s.now s.now t b m) .msg m)
  | timer (s : Sys) : Step p s (Apply p s (OnTimer p s.node s.now) .timer Msg.zero)
  | answer (s : Sys) (c : Check) (hc : c ∈ s.node.checks) (allow : Bool) :
      Step p s (Apply p s (AcpAnswer p s.node s.now c.id allow) .answer Msg.zero)
  | floors (s : Sys) (rf : Option Nat) (of_ : Option (Nat → Option Nat)) (nh : Bool)
      (h : s.node.phase = .gathering) :
      Step p s (Apply p s (FloorsSettled p s.node s.now true rf of_ nh) .floors Msg.zero)
  | tick (s : Sys) (h : TickOk p s.node s.now = true) :
      Step p s (Ticked s)
  | restart (s : Sys) : Step p s (Restarted p s)

/-- The reachable states. -/
inductive Reach (p : Params) : Sys → Prop where
  | init : Reach p (SInit p)
  | step {s s' : Sys} : Reach p s → Step p s s' → Reach p s'

end Pinc.BroadcastNode
