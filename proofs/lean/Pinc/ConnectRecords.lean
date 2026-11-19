import Pinc.ConnectRelay

/-!
# The record store of the relay

`relay/records.rs` of `pinc-connect` as total functions over unbounded `Nat`, step for step the operators of
`proofs/tla/ConnectRecordsOps.tla`: `RecordStore::accept` and `sweep`, `Relay::store`, `publish`, `replica`,
`restore_record`, `set_own_record`, `republish_due`, `sync_record`, `lookup` and `answer`, and the part of
`handle_timeout` that touches records. The theorems are in `ConnectRecordsThm.lean`; the trace replay is
`TraceConnectRecords.lean`.

Seams, stated: a record is the bytes the node signed reduced to what the store sees (`node`, `seq`, `home`, the length,
and `tag`, which stands for every other byte: equal records are equal bytes), and `ok` says that
`Record::parse_verified` succeeds on them (the signature verifies and the key belongs to the node id, an ideal
primitive: a predicate of the bytes, as in `ConnectSigned.lean`). The table of the store is a list of entries with
distinct nodes, at most `R` of them (`ConnectTable.lean` proves the real `Table` is that map). Time is in nanoseconds,
as in the code; the peers are the slots of the relay.
-/

namespace Pinc.ConnectRecords
open Pinc.ConnectRelay (V Ef)

/-- `RECORD_REPUBLISH_NS`, `RECORD_TTL_NS`, `SWEEP_NS` and `MAX_DNS_DATAGRAM - 35`. -/
def sec : Nat := 1000000000
def repub : Nat := 1800 * sec
def recTtl : Nat := 3 * repub
def sweepNs : Nat := sec
def maxDns : Nat := 1452 - 28 - 35

structure Rec where
  node : Nat
  seq : Nat
  home : Nat
  tag : Nat
  len : Nat
  ok : Bool
  deriving DecidableEq, Repr

structure Ent where
  r : Rec
  rcv : Nat
  deriving DecidableEq, Repr

structure Cf where
  R : Nat
  P : Nat
  me : Nat

structure St where
  ents : List Ent := []
  pr : List Nat := []
  np : Nat := 0
  ls : Nat := 0
  records : Nat := 0
  lookups : Nat := 0
  rejected : Nat := 0

def St.new (cf : Cf) : St := { pr := List.replicate cf.P 0 }

structure Out where
  st : St
  res : String
  ef : Ef

def find (l : List Ent) (n : Nat) : Option Ent := l.find? (fun e => e.r.node == n)

/-- Replace the entry of the node, or add it (the table is a map: its order is not observed). -/
def put (l : List Ent) (e : Ent) : List Ent := e :: l.filter (fun x => x.r.node != e.r.node)

/-- `Relay::reject`: the counter and the trace transition. -/
def fail (st : St) (why : String) (node : Nat) : Out :=
  ⟨{ st with rejected := st.rejected + 1 }, why, [[.s "t", .s "rej", .s why, .n node]]⟩

inductive Kind | stale | refreshed | full | stored
  deriving DecidableEq

/-- `RecordStore::accept`: how the store treats a verified record. -/
def accept (cf : Cf) (st : St) (now : Nat) (r : Rec) : Kind × St :=
  match find st.ents r.node with
  | some s =>
    if r.seq < s.r.seq || (r.seq == s.r.seq && decide (r ≠ s.r)) then (.stale, st)
    else if r.seq == s.r.seq then (.refreshed, { st with ents := put st.ents { s with rcv := now } })
    else (.stored, { st with ents := put st.ents ⟨r, now⟩ })
  | none =>
    if cf.R ≤ st.ents.length then (.full, st)
    else (.stored, { st with ents := put st.ents ⟨r, now⟩ })

/-- `Relay::store`; the owner is 0 for none. -/
def store (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String) : Out :=
  if !r.ok then fail st "badrecord" owner
  else if owner != 0 && owner != r.node then fail st "wrongowner" owner
  else match accept cf st now r with
    | (.stale, _) => fail st "stalerec" r.node
    | (.full, _) => fail st "storefull" r.node
    | (.refreshed, s) => ⟨s, "ok", []⟩
    | (.stored, s) => ⟨{ s with records := s.records + 1 }, "ok", [[.s "t", .s "rstored", .n r.node, .n r.seq, .s origin]]⟩

/-- The frame to every peer, in slot order. -/
def sync (st : St) (len : Nat) : Ef :=
  (st.pr.filter (· != 0)).map fun p => [.s "peer", .n p, .s "sync", .n len]

def publish (cf : Cf) (st : St) (now node : Nat) (r : Rec) : Out :=
  let s := store cf st now r node "publish"
  if s.res != "ok" then s else { s with ef := s.ef ++ sync s.st r.len }

def replica (cf : Cf) (st : St) (now : Nat) (r : Rec) : Out := store cf st now r 0 "replica"

/-- `restore_record` is a replica at the time the record was received. -/
def restore (cf : Cf) (st : St) (received : Nat) (r : Rec) : Out := replica cf st received r

def setOwn (cf : Cf) (st : St) (now : Nat) (r : Rec) : Out :=
  let s := store cf st now r cf.me "own"
  if s.res != "ok" then s
  else ⟨{ s.st with np := now + repub }, "ok", s.ef ++ sync s.st r.len⟩

def peerCount (st : St) : Nat := (st.pr.filter (· != 0)).length

/-- `republish_due`. -/
def republishDue (cf : Cf) (st : St) (now : Nat) : St × Ef :=
  if st.np == 0 || now < st.np then (st, [])
  else
    let s1 := { st with np := now + repub }
    match find s1.ents cf.me with
    | none => (s1, [])
    | some e =>
      let s2 := { s1 with ents := put s1.ents { e with rcv := now } }
      (s2, sync s2 e.r.len ++ [[.s "t", .s "repub", .n (peerCount s2)]])

/-- `RecordStore::sweep`. -/
def sweepRecs (st : St) (now : Nat) : St := { st with ents := st.ents.filter fun e => now - e.rcv < recTtl }

/-- `handle_timeout`, the part that touches records. -/
def timeout (cf : Cf) (st : St) (now : Nat) : Out :=
  let d := republishDue cf st now
  if now - d.1.ls < sweepNs then ⟨d.1, "ok", d.2⟩
  else ⟨{ sweepRecs d.1 now with ls := now }, "ok", d.2⟩

/-- `Relay::lookup`: the stored record of the node if it is fresh. -/
def lookup (st : St) (now peer : Nat) : Option Rec :=
  match find st.ents peer with
  | some e => if now - e.rcv < recTtl then some e.r else none
  | none => none

/-- `Relay::answer`: the counter, the trace transition and the answer. -/
def answer (st : St) (now peer : Nat) : St × Ef × String :=
  let l := lookup st now peer
  ({ st with lookups := st.lookups + 1 }, [[.s "t", .s "lookup", .n peer, .n (if l.isSome then 1 else 0)]],
   match l with
   | none => "absent"
   | some r => if maxDns < r.len then "toolarge" else "record")

def isPeer (st : St) (n : Nat) : Bool := st.pr.any (· == n)

/-- `sync_record`. -/
def syncRecord (cf : Cf) (st : St) (to node : Nat) : Bool × Ef :=
  match find st.ents node with
  | some e => if e.r.home == cf.me && isPeer st to then (true, [[.s "peer", .n to, .s "sync", .n e.r.len]]) else (false, [])
  | none => (false, [])

def setSlot : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | _ :: t, 0, p => p :: t
  | x :: t, i + 1, p => x :: setSlot t i p

def firstFree : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: t, i => if x == 0 then some i else firstFree t (i + 1)

/-- `add_peer`. -/
def addPeer (st : St) (p : Nat) : St × Bool :=
  if isPeer st p then (st, true)
  else match firstFree st.pr 0 with
    | none => (st, false)
    | some i => ({ st with pr := setSlot st.pr i p }, true)

/-- `remove_peer`. -/
def removePeer (st : St) (p : Nat) : St := { st with pr := st.pr.map fun x => if x == p then 0 else x }

end Pinc.ConnectRecords
