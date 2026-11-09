import Vinc.Json

/-!
# The bounded tables

`Table` and `Cache` of `vinc-connect/src/relay/table.rs`, step for step (the model of
`proofs/tla/ConnectTableOps.tla`, which TLC checks against a plain bounded map for every bucket function on small
capacities, and which the trace test `trace_connect_table` replays against the real code, wrap-around and all).

A table of capacity `n` is a list of `n` slots, a slot is a key and a value, and key `0` marks the empty slot (node ids
are keys from 1). `bk` is the bucket function: the code's hash reduced modulo `n`, an arbitrary function here, so every
theorem holds for every hash.

Theorems (all `n`, all `bk`):
* `cache_put_get`, `cache_put_evicts`, `cache_put_other`, `cache_get_iff`: the direct-mapped collision rule. A put
  replaces exactly the occupant of the key's bucket and no other slot; a get hits exactly when the bucket holds the key.
* `insert_len`, `remove_len`: the length bookkeeping of a table that reports `len` of the slots it holds, and the
  capacity bound of `insert`.
* `find_probes`: a lookup visits at most `n` slots (the loops are bounded by `n`).

The probe invariant of the open-addressing table (every key reachable from its bucket without crossing an empty slot)
and the refinement of insert, remove and retain to a map are model checked, not proved here: `ConnectTable.tla`
(`Reachable`, `Refines`, `Visited`) for capacities up to 4 and every bucket function of a 4-key set.
-/

namespace Vinc.ConnectTable

structure Slot where
  k : Nat
  v : Nat
  deriving DecidableEq, Repr

def free : Slot := ⟨0, 0⟩

structure T where
  s : List Slot
  len : Nat

def T.new (n : Nat) : T := ⟨List.replicate n free, 0⟩

def getS (s : List Slot) (i : Nat) : Slot := s.getD i free

/-- `Table::find`: the slot of `k`, probing at most `left` slots from `i`. -/
def findFrom (n : Nat) (s : List Slot) (k : Nat) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, left + 1 =>
    if (getS s i).k = 0 then none
    else if (getS s i).k = k then some i
    else findFrom n s k ((i + 1) % n) left

def find (n : Nat) (bk : Nat → Nat) (t : T) (k : Nat) : Option Nat := findFrom n t.s k (bk k) n

/-- The first empty slot from `i` within `left` probes. -/
def firstFree (n : Nat) (s : List Slot) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, left + 1 => if (getS s i).k = 0 then some i else firstFree n s ((i + 1) % n) left

inductive Ins where
  | ok (old : Nat)
  | full

/-- `Table::insert` (`old` is 0 when the key was new). -/
def insert (n : Nat) (bk : Nat → Nat) (t : T) (k v : Nat) : T × Ins :=
  match find n bk t k with
  | some f => (⟨t.s.set f ⟨k, v⟩, t.len⟩, .ok (getS t.s f).v)
  | none =>
    if t.len ≥ n then (t, .full)
    else
      match firstFree n t.s (bk k) n with
      | none => (t, .full)
      | some p => (⟨t.s.set p ⟨k, v⟩, t.len + 1⟩, .ok 0)

/-- The cyclic test of `remove_at`: the entry at `j` stays unless its ideal slot lies outside `(hole, j]`. -/
def stays (hole j ideal : Nat) : Bool :=
  if hole ≤ j then decide (hole < ideal ∧ ideal ≤ j) else decide (hole < ideal ∨ ideal ≤ j)

/-- The backward shift loop of `remove_at`. -/
def shift (n : Nat) (bk : Nat → Nat) (s : List Slot) (hole j : Nat) : Nat → List Slot
  | 0 => s
  | left + 1 =>
    let j2 := (j + 1) % n
    if (getS s j2).k = 0 then s
    else if stays hole j2 (bk (getS s j2).k) then shift n bk s hole j2 left
    else shift n bk ((s.set hole (getS s j2)).set j2 free) j2 j2 left

def removeAt (n : Nat) (bk : Nat → Nat) (t : T) (i : Nat) : T :=
  ⟨shift n bk (t.s.set i free) i i n, t.len - 1⟩

def remove (n : Nat) (bk : Nat → Nat) (t : T) (k : Nat) : T × Option Nat :=
  match find n bk t k with
  | none => (t, none)
  | some f => (removeAt n bk t f, some (getS t.s f).v)

/-- `Table::retain` with the predicate "the value is odd"; the keys the predicate was called on. The loop runs at
most `2n` rounds (each advances the index or removes an entry), which is the fuel. -/
def retainFrom (n : Nat) (bk : Nat → Nat) : Nat → T → Nat → List Nat → T × List Nat
  | 0, t, _, vis => (t, vis)
  | fuel + 1, t, i, vis =>
    if i ≥ n then (t, vis)
    else if (getS t.s i).k = 0 then retainFrom n bk fuel t (i + 1) vis
    else if (getS t.s i).v % 2 = 1 then retainFrom n bk fuel t (i + 1) ((getS t.s i).k :: vis)
    else retainFrom n bk fuel (removeAt n bk t i) i ((getS t.s i).k :: vis)

def retainOdd (n : Nat) (bk : Nat → Nat) (t : T) : T × List Nat := retainFrom n bk (2 * n + 2) t 0 []

/-- The entries in slot order, as `Table::iter`. -/
def entries (t : T) : List Slot := t.s.filter fun x => x.k ≠ 0

/-! ### Cache -/

def Cache.new (n : Nat) : List Slot := List.replicate n free

def cachePut (c : List Slot) (bk : Nat → Nat) (k v : Nat) : List Slot := c.set (bk k) ⟨k, v⟩
def cacheGet (c : List Slot) (bk : Nat → Nat) (k : Nat) : Option Nat :=
  if (getS c (bk k)).k = k then some (getS c (bk k)).v else none

theorem getS_set_self (s : List Slot) (i : Nat) (x : Slot) (h : i < s.length) : getS (s.set i x) i = x := by
  simp [getS, h]

theorem getS_set_other (s : List Slot) (i j : Nat) (x : Slot) (h : i ≠ j) : getS (s.set i x) j = getS s j := by
  simp [getS, List.getD_eq_getElem?_getD, List.getElem?_set, h]

/-- A put followed by a get of the same key hits with the value (the bucket is inside the cache). -/
theorem cache_put_get (c : List Slot) (bk : Nat → Nat) (k v : Nat) (hb : bk k < c.length) :
    cacheGet (cachePut c bk k v) bk k = some v := by
  simp [cacheGet, cachePut, getS_set_self _ _ _ hb]

/-- A put replaces exactly the occupant of the key's bucket. -/
theorem cache_put_evicts (c : List Slot) (bk : Nat → Nat) (k v : Nat) (hb : bk k < c.length) :
    getS (cachePut c bk k v) (bk k) = ⟨k, v⟩ ∧ (cachePut c bk k v).length = c.length := by
  simp [cachePut, getS_set_self _ _ _ hb]

/-- No other slot changes. -/
theorem cache_put_other (c : List Slot) (bk : Nat → Nat) (k v j : Nat) (hj : j ≠ bk k) :
    getS (cachePut c bk k v) j = getS c j := getS_set_other _ _ _ _ (Ne.symm hj)

/-- A get hits exactly when the bucket holds the key, and answers the value stored with it. -/
theorem cache_get_iff (c : List Slot) (bk : Nat → Nat) (k v : Nat) :
    cacheGet c bk k = some v ↔ (getS c (bk k)).k = k ∧ (getS c (bk k)).v = v := by
  unfold cacheGet; split <;> simp_all

/-! ### Table bookkeeping -/

theorem findFrom_some_lt (n : Nat) (s : List Slot) (k : Nat) (hn : 0 < n) :
    ∀ (left i p : Nat), i < n → findFrom n s k i left = some p → p < n := by
  intro left; induction left with
  | zero => intro i p _ h; simp [findFrom] at h
  | succ l ih =>
    intro i p hi h
    unfold findFrom at h
    split at h
    · simp at h
    · split at h
      · simp at h; omega
      · exact ih _ p (Nat.mod_lt _ hn) h

/-- A lookup visits at most `n` slots: it is a loop of `n` rounds, and a hit is a slot of the array. -/
theorem find_probes (n : Nat) (bk : Nat → Nat) (t : T) (k p : Nat) (hn : 0 < n) (hb : bk k < n)
    (h : find n bk t k = some p) : p < n := findFrom_some_lt n t.s k hn n _ p hb h

/-- A successful insert keeps the length at most `n`: an existing key keeps it, a new key is added only below `n`. -/
theorem insert_len (n : Nat) (bk : Nat → Nat) (t : T) (k v : Nat) (h : t.len ≤ n) :
    (insert n bk t k v).1.len ≤ n := by
  unfold insert
  split
  · simpa using h
  · split
    · simpa using h
    · split
      · simpa using h
      · simp; omega

/-- `remove` lowers the length by one when it removes an entry, and changes nothing otherwise. -/
theorem remove_len (n : Nat) (bk : Nat → Nat) (t : T) (k : Nat) :
    (remove n bk t k).1.len = t.len - (if (remove n bk t k).2.isSome then 1 else 0) := by
  unfold remove
  split <;> simp [removeAt]

end Vinc.ConnectTable
