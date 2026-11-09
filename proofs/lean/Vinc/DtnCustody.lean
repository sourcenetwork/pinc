import Vinc.DtnStoreProps

/-!
# Custody

A model of `vinc-dtn/src/custody.rs`: the `CustodyBook<N>` and its operations on the shared `Ledger`. The book is `N`
optional records (`bundle`, `previous` custodian to whom an ack is owed, the node custody was `offered` to and the id of
that offer). The book also has a counter `next_offer`: every `offer` takes the counter as its id and increments it.
In this model the counter is the separate component `nx` of the callers (`offer B nx b to` returns the new one; no other
operation reads or changes it). A
bundle is the key `⟨1, id⟩` of the ledger (`Space::DTN` is `1`); nodes are numbers (equal bytes, equal number).

The signature check of an acknowledgement is the one abstraction: `CustodyAck::verify` is the boolean `valid` of the
ack (it succeeds exactly when the signature verifies under the custodian's node id; the signature scheme itself is
assumed, as everywhere in this package, and is not re-proved). Everything else is the code's own logic. The offer id an
ack names is a number the model compares (it is part of the signed body, so it cannot be changed without invalidating
the signature).

Two behaviours are pinned: `onAck` for a bundle whose item the ledger no longer holds drops the record and returns
the store's `Unknown` (`CErr.storeUnknown`); `accept` answers the `previous` and offer id of the INCOMING offer
(`acceptDue`), not the record's, and a bundle already held keeps its record (its `previous` too) and cancels the
outstanding offer (`cancelRec`).

Environment of the book: the host admits and releases items of the ledger directly (the mailbox layer, transit bundles,
`Ledger::expire`), but never admits, releases or reclasses a key the book holds a record of (`Allowed`): custody of a
bundle enters through `accept` and leaves through `delivered`, expiry or relief.

This module holds the definitions and the single-operation theorems; `Vinc.DtnCustodySys` the system steps and the
invariants over all runs.
-/

namespace Vinc.DtnStore

/-- A custody record: the bundle, the previous custodian (to whom an ack is owed), the node custody was `offered` to
(none: no offer outstanding) and the id `oid` of that offer (`0` when none: the code's `Option<{to, id}>` is the pair
`(offered, oid)` with `oid = 0` for none). -/
structure Record where
  bundle : Nat
  previous : Nat
  offered : Option Nat
  oid : Nat
  deriving DecidableEq, Repr

/-- The bundle's ledger key. -/
def bkey (b : Nat) : Key := ⟨1, b⟩

/-- Why custody bookkeeping refused something. -/
inductive CErr where
  | store (e : AErr)
  | storeUnknown
  | ack
  | capacity
  | unknown
  | notOffered
  deriving DecidableEq, Repr

abbrev Recs := List (Option Record)

def recs (B : Recs) : List Record := B.filterMap id

def holds (B : Recs) (b : Nat) : Bool := (recs B).any fun r => decide (r.bundle = b)

/-- `sync`: the records of items the ledger no longer holds are dropped. -/
def sync (B : Recs) (L : Ledger) : Recs := B.map fun s => s.filter fun r => L.contains (bkey r.bundle)

/-- The slot of the first record of `b`. -/
def slotOf (B : Recs) (b : Nat) : Option Nat := B.findIdx? fun s => s.any fun r => decide (r.bundle = b)

/-- The result of an operation: the error, the book, the ledger and the evictions (in the order the callback saw). -/
structure COut where
  err : Option CErr
  B : Recs
  L : Ledger
  ev : List Entry

/-- Change the first record of `b` by `f` (`none` when the book has no record of `b`). -/
def modFirst (b : Nat) (f : Record → Record) : Recs → Option Recs
  | [] => none
  | s :: r =>
    match s with
    | some x => if x.bundle = b then some (some (f x) :: r) else (modFirst b f r).map (s :: ·)
    | none => (modFirst b f r).map (s :: ·)

/-- The change an offer makes to a record: node and id are set. -/
def offerRec (to id : Nat) (x : Record) : Record := { x with offered := some to, oid := id }

/-- The change a hand-back makes to a record: the outstanding offer is cancelled (the previous custodian stays). -/
def cancelRec (x : Record) : Record := { x with offered := none, oid := 0 }

/-- `CustodyBook::accept`. The counter `next_offer` is not touched by `accept`. -/
def accept (B : Recs) (L : Ledger) (bundle bytes expires previous now : Nat) : COut :=
  let L1 := (expire L now).1
  let ev1 := (expire L now).2
  let B1 := sync B L1
  if holds B1 bundle then ⟨none, ((modFirst bundle cancelRec B1).getD B1), L1, ev1⟩ else
  match B1.findIdx? Option.isNone with
  | none => ⟨some .capacity, B1, L1, ev1⟩
  | some slot =>
    if L1.contains (bkey bundle) then
      let L2 := (reclass L1 (bkey bundle) .custody).1
      ⟨none, (sync B1 L2).set slot (some ⟨bundle, previous, none, 0⟩), L2, ev1⟩
    else
      let r := admitItem L1 (bkey bundle) bytes .custody expires now
      match r.err with
      | some e => ⟨some (.store e), B1, r.L, ev1 ++ r.ev⟩
      | none => ⟨none, (sync B1 r.L).set slot (some ⟨bundle, previous, none, 0⟩), r.L, ev1 ++ r.ev⟩

/-- The `AckDue` an `accept` returns: for every successful acceptance (fresh, promoted from transit, or a bundle
already held) it is the `previous` and the offer id of the INCOMING offer, never the record's. -/
def acceptDue (previous offer : Nat) (o : COut) : Option (Nat × Nat) :=
  if o.err = none then some (previous, offer) else none

/-- The result of `CustodyBook::offer`: the error, the book, the counter after the call and the id handed out (`0`
and meaningless when the call failed). -/
structure OOut where
  err : Option CErr
  B : Recs
  nx : Nat
  id : Nat

/-- `CustodyBook::offer` with the book's counter `nx` (`next_offer`): the offer gets the id `nx`, the counter becomes
`nx + 1` (it saturates at `u64::MAX` in the code, which `2^64` offers cannot reach; here it counts in the naturals),
and the record's outstanding offer is replaced by `(to, nx)`. -/
def offer (B : Recs) (nx b to : Nat) : OOut :=
  match modFirst b (offerRec to nx) B with
  | none => ⟨some .unknown, B, nx, 0⟩
  | some B' => ⟨none, B', nx + 1, nx⟩

/-- `CustodyBook::on_ack` for an ack for `b` signed by `custodian`, naming offer `offer`, whose signature check gave
`valid`. Relief needs the record's node AND its offer id to match; a stale ack is `notOffered` and moves nothing. An ack
of an offered, current offer for an item the ledger no longer holds clears the record and reports `storeUnknown`
(the store's `Unknown`). -/
def onAck (B : Recs) (L : Ledger) (b custodian offer : Nat) (valid : Bool) : COut :=
  if valid then
    match slotOf B b with
    | none => ⟨some .unknown, B, L, []⟩
    | some i =>
      match B[i]? with
      | some (some r) =>
        if r.offered = some custodian ∧ r.oid = offer then
          let r := reclass L (bkey b) .transit
          ⟨if r.2 then none else some .storeUnknown, B.set i none, r.1, []⟩
        else ⟨some .notOffered, B, L, []⟩
      | _ => ⟨some .notOffered, B, L, []⟩
  else ⟨some .ack, B, L, []⟩

/-- `CustodyBook::delivered`. -/
def delivered (B : Recs) (L : Ledger) (b : Nat) : COut :=
  match slotOf B b with
  | none => ⟨some .unknown, B, L, []⟩
  | some i => ⟨none, B.set i none, (release L (bkey b)).1, []⟩

/-- `CustodyBook::expire`. -/
def bexpire (B : Recs) (L : Ledger) (now : Nat) : COut :=
  ⟨none, sync B (expire L now).1, (expire L now).1, (expire L now).2⟩

/-- Every ledger item of a held bundle is custody (the class of a held bundle is never changed behind the book). -/
def Linked (B : Recs) (L : Ledger) : Prop :=
  ∀ r ∈ recs B, ∀ e ∈ L.entries, e.key = bkey r.bundle → e.cls = .custody

/-- No bundle is held twice. -/
def NodupB (B : Recs) : Prop := ((recs B).map (·.bundle)).Nodup

/-! ## Records -/

theorem filterSlots_recs (l : Recs) (p : Record → Bool) :
    (l.map fun s => s.filter p).filterMap id = (l.filterMap id).filter p := by
  induction l with
  | nil => simp
  | cons s l ih =>
    cases s with
    | none => simp only [List.map_cons, List.filterMap_cons, Option.filter_none, id]; simpa using ih
    | some v =>
      by_cases h : p v
      · simp only [List.map_cons, List.filterMap_cons, Option.filter_some, h, ite_true, id, List.filter_cons]; rw [ih]
      · simp only [List.map_cons, List.filterMap_cons, Option.filter_some, h, id, List.filter_cons]
        simp; simpa using ih

theorem recs_sync (B : Recs) (L : Ledger) :
    recs (sync B L) = (recs B).filter fun r => L.contains (bkey r.bundle) := by
  simp only [recs, sync, filterSlots_recs]

theorem mem_recs_sync {B : Recs} {L : Ledger} {r : Record} :
    r ∈ recs (sync B L) ↔ r ∈ recs B ∧ L.contains (bkey r.bundle) = true := by
  rw [recs_sync]; simp

theorem recs_set_none (B : Recs) (i : Nat) : ∀ r ∈ recs (B.set i none), r ∈ recs B := by
  intro r hr
  simp only [recs, List.mem_filterMap, id] at hr ⊢
  obtain ⟨s, hs, hse⟩ := hr
  rcases List.mem_or_eq_of_mem_set hs with h | h
  · exact ⟨s, h, hse⟩
  · subst h; simp at hse

end Vinc.DtnStore
