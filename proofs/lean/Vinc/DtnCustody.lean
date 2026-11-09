import Vinc.DtnStoreProps

/-!
# Custody

A model of `vinc-dtn/src/custody.rs`: the `CustodyBook<N>` and its operations on the shared `Ledger`. The book is `N`
optional records (`bundle`, `previous` custodian to whom an ack is owed, and the node custody was `offered` to). A
bundle is the key `⟨1, id⟩` of the ledger (`Space::DTN` is `1`); nodes are numbers (equal bytes, equal number).

The signature check of an acknowledgement is the one abstraction: `CustodyAck::verify` is the boolean `valid` of the
ack (it succeeds exactly when the signature verifies under the custodian's node id; the signature scheme itself is
assumed, as everywhere in this package, and is not re-proved). Everything else is the code's own logic.

Environment of the book: the host admits and releases items of the ledger directly (the mailbox layer, transit bundles,
`Ledger::expire`), but never admits, releases or reclasses a key the book holds a record of (`Allowed`): custody of a
bundle enters through `accept` and leaves through `delivered`, expiry or relief.

This module holds the definitions and the single-operation theorems; `Vinc.DtnCustodySys` the system steps and the
invariants over all runs.
-/

namespace Vinc.DtnStore

/-- A custody record. -/
structure Record where
  bundle : Nat
  previous : Nat
  offered : Option Nat
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

/-- `CustodyBook::accept`. -/
def accept (B : Recs) (L : Ledger) (bundle bytes expires previous now : Nat) : COut :=
  let L1 := (expire L now).1
  let ev1 := (expire L now).2
  let B1 := sync B L1
  if holds B1 bundle then ⟨none, B1, L1, ev1⟩ else
  match B1.findIdx? Option.isNone with
  | none => ⟨some .capacity, B1, L1, ev1⟩
  | some slot =>
    if L1.contains (bkey bundle) then
      let L2 := (reclass L1 (bkey bundle) .custody).1
      ⟨none, (sync B1 L2).set slot (some ⟨bundle, previous, none⟩), L2, ev1⟩
    else
      let r := admitItem L1 (bkey bundle) bytes .custody expires now
      match r.err with
      | some e => ⟨some (.store e), B1, r.L, ev1 ++ r.ev⟩
      | none => ⟨none, (sync B1 r.L).set slot (some ⟨bundle, previous, none⟩), r.L, ev1 ++ r.ev⟩

/-- `CustodyBook::offer`: set the node custody was offered to (the first record of the bundle). -/
def setOffered (b to : Nat) : Recs → Option Recs
  | [] => none
  | s :: r =>
    match s with
    | some x => if x.bundle = b then some (some { x with offered := some to } :: r) else (setOffered b to r).map (s :: ·)
    | none => (setOffered b to r).map (s :: ·)

def offer (B : Recs) (b to : Nat) : Option CErr × Recs :=
  match setOffered b to B with
  | none => (some .unknown, B)
  | some B' => (none, B')

/-- `CustodyBook::on_ack` for an ack for `b` signed by `custodian` whose signature check gave `valid`. -/
def onAck (B : Recs) (L : Ledger) (b custodian : Nat) (valid : Bool) : COut :=
  if valid then
    match slotOf B b with
    | none => ⟨some .unknown, B, L, []⟩
    | some i =>
      if (B[i]?.bind id).bind (·.offered) ≠ some custodian then ⟨some .notOffered, B, L, []⟩
      else
        let r := reclass L (bkey b) .transit
        ⟨if r.2 then none else some .storeUnknown, B.set i none, r.1, []⟩
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

theorem contains_iff {L : Ledger} {k : Key} : L.contains k = true ↔ ∃ e ∈ L.entries, e.key = k := by
  unfold Ledger.contains; simp

theorem recs_set_none (B : Recs) (i : Nat) : ∀ r ∈ recs (B.set i none), r ∈ recs B := by
  intro r hr
  simp only [recs, List.mem_filterMap, id] at hr ⊢
  obtain ⟨s, hs, hse⟩ := hr
  rcases List.mem_or_eq_of_mem_set hs with h | h
  · exact ⟨s, h, hse⟩
  · subst h; simp at hse

end Vinc.DtnStore
