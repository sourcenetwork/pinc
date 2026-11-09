/-!
# Connection ids: the model

A model of `vinc-transport` `conn/cid.rs` (`Cids`), operation for operation as `proofs/tla/CidOps.tla` has them,
over unbounded indices. A connection id is known by its derived index (the code derives it from the session secret
and the index; index 0 is the id the handshake carried and is not in the table). The slots are a function from
the slot number to the entry; slots from `slots` up are empty. `Vinc.TraceCid` replays the recorded calls of the
real code through these functions; the theorems are in `Vinc.TransportCidThm`.

The eviction rule is the one of the code now: a stale entry (below the highest index seen, never used by a packet)
may make room as well as a used one. The earlier rule (`seen` only) lost the lookahead after enough skipped
indices; `proofs/tla/Cid_stale.cfg` keeps that behaviour as a witness.
-/

namespace Vinc.TransportCid

/-- A derived id held: its index, the tick of its last use and whether an authenticated packet used it. -/
structure E where
  idx : Nat
  used : Nat
  seen : Bool
  deriving BEq, Repr, DecidableEq

/-- The table. -/
structure C where
  ent : Nat → Option E := fun _ => none
  hi : Nat := 0
  tick : Nat := 0
  ns : Nat := 0
  sec : Bool := false
  fr : Bool := false

/-- `LOCAL_SLOTS`. -/
def slots : Nat := 8
/-- `LOOKAHEAD`. -/
def look : Nat := 2

/-- Whether the table holds the id of index `k`. -/
def has (c : C) (k : Nat) : Bool := (List.range slots).any (fun s => (c.ent s).any (fun e => e.idx == k))

/-- An entry that may make room: used by a packet, or stale (below the highest index seen). -/
def evictable (c : C) (e : E) : Bool := e.seen || decide (e.idx ≤ c.hi)

def lexLt (a b : Nat × Nat) : Bool := decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 < b.2))

def pick (acc : Option (Nat × Nat)) (p : Nat × Nat) : Option (Nat × Nat) :=
  match acc with
  | none => some p
  | some q => if lexLt p q then some p else some q

/-- The (use tick, slot) of every entry that may make room. -/
def cands (c : C) : List (Nat × Nat) :=
  (List.range slots).filterMap (fun s => (c.ent s).bind (fun e => if evictable c e then some (e.used, s) else none))

/-- The slot of the entry least recently used among those that may make room (ties: the lower slot). -/
def victim (c : C) : Option Nat := ((cands c).foldl pick none).map (·.2)

def freeSlot (c : C) : Option Nat := (List.range slots).find? (fun s => (c.ent s).isNone)

def put (c : C) (s : Nat) (e : E) : C := { c with ent := fun t => if t = s then some e else c.ent t }

/-- The id of index `k` into the table; the index evicted, if any. -/
def refill1 (c : C) (k : Nat) : C × Option Nat :=
  if has c k then (c, none)
  else match freeSlot c with
    | some s => (put c s ⟨k, c.tick, false⟩, none)
    | none =>
      match victim c with
      | some s => (put c s ⟨k, c.tick, false⟩, (c.ent s).map (·.idx))
      | none => (c, none)

/-- `refill`: the indices `hi + 1` and `hi + 2`; the indices evicted. -/
def refill (c : C) : C × List Nat :=
  if c.sec then
    let r1 := refill1 c (c.hi + 1)
    let r2 := refill1 r1.1 (c.hi + 2)
    (r2.1, r1.2.toList ++ r2.2.toList)
  else (c, [])

def install (c : C) : C × List Nat := refill { c with sec := true }

/-- The slot holding index `k`, if any. -/
def slotOf (c : C) (k : Nat) : Option Nat := (List.range slots).find? (fun s => (c.ent s).any (fun e => e.idx == k))

/-- The packet to the id of index `k` in slot `s` authenticated: the entry is used and seen; the highest index moves up
and the lookahead is filled when `k` is above it. -/
def authAt (c1 : C) (k s : Nat) : C × List Nat :=
  let c2 := put c1 s ⟨k, c1.tick, true⟩
  if c1.hi < k then refill { c2 with hi := k } else (c2, [])

/-- `on_authenticated` for the id of index `k` (0 is the first id, which is not in the table). -/
def auth (c : C) (k : Nat) : C × List Nat :=
  let c1 := { c with tick := c.tick + 1 }
  match (if k < 1 then none else slotOf c1 k) with
  | none => (c1, [])
  | some s => authAt c1 k s

def setFirstRemote (c : C) : C := { c with fr := true }

/-- `claim_remote`: the index of the id for a path of its own. -/
def claim (c : C) : C × Option Nat :=
  if !c.fr || (decide (0 < c.ns) && !c.sec) then (c, none) else ({ c with ns := c.ns + 1 }, some c.ns)

def isLocal (c : C) (k : Nat) : Bool := decide (k = 0) || has c k

/-- The indices held. -/
def held (c : C) : List Nat := (List.range slots).filterMap (fun s => (c.ent s).map (·.idx))

def epoch (c : C) : Nat := 2 * c.hi + (if c.sec then 1 else 0)

end Vinc.TransportCid
