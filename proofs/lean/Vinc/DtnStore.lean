import Vinc.Axioms

/-!
# The charged store (definitions and slot arithmetic)

A model of `vinc-dtn/src/store.rs`: the `Ledger<N>` that charges every kept item, delay-tolerant bundles and mailbox
items alike (told apart only by `Key.space`), against one byte budget.

The ledger is `N` optional slots (`slots.length = N`), the budget, the bytes charged (`used`) and the next admission
sequence number. Times, sizes and sequence numbers are `Nat`s; the `u64` operations the code uses are modelled
exactly: `saturating_sub` is the truncated subtraction and `saturating_add` is `satAdd` (capped at `2^64 - 1`).
`used -= bytes` and `used += bytes` cannot leave the `u64` range because `used` is the sum of the kept sizes and at most
the budget (the invariant `Inv`); `next_seq += 1` would need 2^64 admissions (a documented ceiling, not an assumption of
any theorem here: the sequence number is a `Nat`).

`expire` is the code's loop over the slot indices `0..N`: every slot is visited once and the removal of one slot does
not change another, so it is the map of "empty the slot if its entry is expired" and the evictions are reported in slot
order. `oldestIdx` is `oldest_transit`: the minimum of `(seq, slot index)` over the transit entries.

The theorems about admission are in `Vinc.DtnStoreAdmit`, about custody in `Vinc.DtnCustody`.
-/

namespace Vinc.DtnStore

/-- The largest `u64`. -/
def MAX : Nat := 2 ^ 64 - 1

/-- `u64::saturating_add`. -/
def satAdd (a b : Nat) : Nat := min (a + b) MAX

/-- How an item may be evicted. -/
inductive Class where
  | custody
  | transit
  deriving DecidableEq, Repr

/-- A key: the owning layer (`1` bundles, `2` mailbox items, any other number is another layer) and the 32-byte id,
standing for the byte string (equal bytes, equal id). -/
structure Key where
  space : Nat
  id : Nat
  deriving DecidableEq, Repr

/-- One kept item. -/
structure Entry where
  key : Key
  bytes : Nat
  cls : Class
  expires : Nat
  seq : Nat
  deriving DecidableEq, Repr

/-- The ledger: the byte budget, the bytes charged, the next admission number and the slots. -/
structure Ledger where
  budget : Nat
  used : Nat
  nextSeq : Nat
  slots : List (Option Entry)

/-- An empty ledger of `n` slots (`Ledger::new`). -/
def Ledger.empty (budget n : Nat) : Ledger := ⟨budget, 0, 0, List.replicate n none⟩

/-- The kept items, in slot order (`iter`). -/
def Ledger.entries (L : Ledger) : List Entry := L.slots.filterMap id

/-- The sum of the sizes. -/
def sumB (es : List Entry) : Nat := (es.map (·.bytes)).sum

/-- Whether `key` is kept. -/
def Ledger.contains (L : Ledger) (k : Key) : Bool := L.entries.any fun e => decide (e.key = k)

/-- The entry for `key`. -/
def Ledger.get (L : Ledger) (k : Key) : Option Entry := L.entries.find? fun e => decide (e.key = k)

/-- Expired at `now`: `expires <= now`. -/
def expiredAt (now : Nat) (e : Entry) : Bool := decide (e.expires ≤ now)

/-- `expire`: every item expired at `now` leaves, reported in slot order. -/
def expire (L : Ledger) (now : Nat) : Ledger × List Entry :=
  let ev := L.entries.filter (expiredAt now)
  ({ L with used := L.used - sumB ev, slots := L.slots.map fun s => s.filter fun e => !expiredAt now e }, ev)

/-- `take`: empty slot `i`, returning the entry. -/
def takeAt (L : Ledger) (i : Nat) : Option (Ledger × Entry) :=
  match L.slots[i]? with
  | some (some e) => some ({ L with used := L.used - e.bytes, slots := L.slots.set i none }, e)
  | _ => none

/-- `(seq, slot index)` of the oldest transit item at or after slot `i` (the minimum over pairs). -/
def minT : List (Option Entry) → Nat → Option (Nat × Nat)
  | [], _ => none
  | s :: r, i =>
    let rest := minT r (i + 1)
    match s with
    | some e =>
      if e.cls = .transit then
        match rest with
        | none => some (e.seq, i)
        | some (q, j) => if e.seq < q ∨ (e.seq = q ∧ i ≤ j) then some (e.seq, i) else some (q, j)
      else rest
    | none => rest

/-- `oldest_transit`. -/
def oldestIdx (L : Ledger) : Option Nat := (minT L.slots 0).map (·.2)

/-- The first empty slot takes the entry. -/
def put : List (Option Entry) → Entry → Option (List (Option Entry))
  | [], _ => none
  | none :: r, e => some (some e :: r)
  | some x :: r, e => (put r e).map (some x :: ·)

/-- `release`: remove `key` on purpose. -/
def release (L : Ledger) (k : Key) : Ledger × Option Entry :=
  match L.slots.findIdx? fun s => s.any fun e => decide (e.key = k) with
  | none => (L, none)
  | some i =>
    match takeAt L i with
    | some (L', e) => (L', some e)
    | none => (L, none)

/-- `reclass`: change the class of a kept item (`false` when the key is not kept: `StoreError::Unknown`). -/
def reclass (L : Ledger) (k : Key) (c : Class) : Ledger × Bool :=
  if L.contains k then
    ({ L with slots := L.slots.map fun s => s.map fun e => if e.key = k then { e with cls := c } else e }, true)
  else (L, false)

/-! ## The invariant -/

/-- What every reachable ledger satisfies: the charge is the sum of the sizes and within the budget, keys and
sequence numbers are pairwise distinct, and every sequence number was handed out. -/
structure Inv (L : Ledger) : Prop where
  used_eq : L.used = sumB L.entries
  used_le : L.used ≤ L.budget
  budget_le : L.budget ≤ MAX
  keys : (L.entries.map (·.key)).Nodup
  seqs : (L.entries.map (·.seq)).Nodup
  seq_lt : ∀ e ∈ L.entries, e.seq < L.nextSeq

theorem Inv.empty (budget n : Nat) (h : budget ≤ MAX) : Inv (Ledger.empty budget n) := by
  refine ⟨?_, by simp [Ledger.empty], h, ?_, ?_, ?_⟩ <;>
    simp [Ledger.empty, Ledger.entries, sumB]

/-! ## Slot lemmas -/

theorem sumB_cons (e : Entry) (es : List Entry) : sumB (e :: es) = e.bytes + sumB es := by simp [sumB]

theorem sumB_append (a b : List Entry) : sumB (a ++ b) = sumB a + sumB b := by simp [sumB]

theorem sumB_perm {a b : List Entry} (h : a.Perm b) : sumB a = sumB b := by
  unfold sumB; exact List.Perm.sum_nat (h.map _)

theorem sumB_filter (p : Entry → Bool) (es : List Entry) :
    sumB (es.filter p) + sumB (es.filter fun e => !p e) = sumB es := by
  induction es with
  | nil => simp [sumB]
  | cons e es ih =>
    by_cases h : p e <;> simp [h, sumB_cons] <;> omega

theorem satAdd_foldl (acc : Nat) (hacc : acc ≤ MAX) (es : List Entry) :
    es.foldl (fun b e => satAdd b e.bytes) acc = min (acc + sumB es) MAX := by
  induction es generalizing acc with
  | nil => simp [sumB]; omega
  | cons e es ih =>
    simp only [List.foldl_cons, sumB_cons]
    rw [ih _ (by unfold satAdd; omega)]
    unfold satAdd
    omega

theorem filterSlots_entries (l : List (Option Entry)) (p : Entry → Bool) :
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

theorem entries_expire (L : Ledger) (now : Nat) :
    (expire L now).1.entries = L.entries.filter fun e => !expiredAt now e := by
  simp only [expire, Ledger.entries, filterSlots_entries]

theorem takeAt_perm {L L' : Ledger} {i : Nat} {e : Entry} (h : takeAt L i = some (L', e)) :
    L.entries.Perm (e :: L'.entries) := by
  unfold takeAt at h
  split at h
  · rename_i e' hs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hi : i < L.slots.length := by
      by_cases hc : i < L.slots.length
      · exact hc
      · simp [List.getElem?_eq_none (by omega : L.slots.length ≤ i)] at hs
    have hg : L.slots[i] = some e' := by
      have := List.getElem?_eq_getElem hi
      rw [hs] at this
      simpa using this.symm
    have hsplit : L.slots = L.slots.take i ++ some e' :: L.slots.drop (i + 1) := by
      calc L.slots = L.slots.take i ++ L.slots.drop i := (List.take_append_drop i _).symm
        _ = _ := by rw [List.drop_eq_getElem_cons hi, hg]
    have hset : L.slots.set i none = L.slots.take i ++ none :: L.slots.drop (i + 1) := by
      simp [List.set_eq_take_append_cons_drop, hi]
    obtain ⟨A, B, hA, hB⟩ : ∃ A B, L.slots = A ++ some e' :: B ∧ L.slots.set i none = A ++ none :: B :=
      ⟨_, _, hsplit, hset⟩
    have hl : L.entries = A.filterMap id ++ e' :: B.filterMap id := by
      simp only [Ledger.entries]; rw [hA]; simp [List.filterMap_append]
    have hr : (e' :: ({ L with used := L.used - e'.bytes, slots := L.slots.set i none } : Ledger).entries) =
        e' :: (A.filterMap id ++ B.filterMap id) := by
      simp only [Ledger.entries]; rw [hB]; simp [List.filterMap_append]
    rw [hr, hl]
    exact List.perm_middle
  · simp at h

end Vinc.DtnStore
