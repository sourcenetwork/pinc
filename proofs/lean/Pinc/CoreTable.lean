/-!
# The connection-id table: the model

A model of `pinc-core` `table.rs` (`Table`), as `proofs/tla/CoreTableOps.tla` has it, over unbounded `Nat`: a hash
table of at most `n` entries with chaining and a list of the entries in insertion order. The code keeps the entries in
an array, a chain per bucket and the order list as links between array indexes, and a free list of the unused ones;
here an entry is a record `E` (the key, the value and `s`, the number of pushes before it, which tells the order in
which entries were pushed) and the chain of a bucket and the order list hold the same records, so an operation that
changes or removes an entry does so in every list at once, as it does in the code, where the lists link one entry.
The free list and the array positions are not here: that the free list is empty exactly when the table holds `n`
entries (so that a push is refused exactly then), that the links of the three lists stay well formed and that an
entry keeps its array position until it is removed are checked by TLC (`CoreTable.tla`, `WellFormed`, `StableRight`)
for every bucket function at small sizes. `bk` is the bucket function, the code's keyed hash reduced modulo `n`: an
arbitrary function here, so every theorem holds for every hash.

The chain of a bucket lists its entries newest push first (a push puts the entry at the head); `find`, `matches` and
`remove_pair` walk the chain, `remove` and `touch` go through `find`. `Pinc.TraceCoreTable` replays the recorded calls
of the real table through these functions; the theorems are in `Pinc.CoreTableThm`.
-/

namespace Pinc.CoreTable

/-- An entry: the key, the value, and the number of pushes before this entry's push. -/
structure E where
  k : Nat
  v : Nat
  s : Nat
  deriving BEq, DecidableEq, Repr

/-- The table: the chain of each bucket (newest push first), the order list (oldest first), the number of pushes so
far and `len`. -/
structure T where
  chain : Nat → List E
  order : List E
  ctr : Nat
  len : Nat

/-- `Table::new` and `clear`. -/
def T.new : T := ⟨fun _ => [], [], 0, 0⟩

/-- `Table::find`: the first entry of the key along the chain of its bucket. -/
def find (bk : Nat → Nat) (t : T) (k : Nat) : Option E := (t.chain (bk k)).find? fun e => e.k == k

/-- The entries of `k` along its chain, newest push first: what `matches` walks. -/
def holders (bk : Nat → Nat) (t : T) (k : Nat) : List E := (t.chain (bk k)).filter fun e => e.k == k

/-- `Table::push`: refused (nothing changes) when the table holds `n` entries, which is when the free list is empty. -/
def push (bk : Nat → Nat) (n : Nat) (t : T) (k v : Nat) : T × Bool :=
  if t.len < n then
    let e : E := ⟨k, v, t.ctr⟩
    (⟨fun b => if b = bk k then e :: t.chain b else t.chain b, t.order ++ [e], t.ctr + 1, t.len + 1⟩, true)
  else (t, false)

/-- `Table::pop` of the entry `e`, which must be held: it leaves its chain and the order list. -/
def pop (t : T) (e : E) : T :=
  ⟨fun b => (t.chain b).filter fun x => x.s != e.s, t.order.filter fun x => x.s != e.s, t.ctr, t.len - 1⟩

/-- A new value for the entry `s`, in every list. -/
def setV (t : T) (s v : Nat) : T :=
  let f : E → E := fun x => if x.s = s then { x with v := v } else x
  ⟨fun b => (t.chain b).map f, t.order.map f, t.ctr, t.len⟩

/-- `Table::insert`: an existing key takes the value (the entry keeps its place in the order); a new key is pushed
and, when the table is full, the oldest entry (the head of the order list) is popped first and returned. -/
def insert (bk : Nat → Nat) (n : Nat) (t : T) (k v : Nat) : T × Option (Nat × Nat) :=
  match find bk t k with
  | some e => (setV t e.s v, none)
  | none =>
    if t.len = n then
      match t.order with
      | o :: _ => ((push bk n (pop t o) k v).1, some (o.k, o.v))
      | [] => ((push bk n t k v).1, none)
    else ((push bk n t k v).1, none)

/-- `Table::insert_room`. -/
def insertRoom (bk : Nat → Nat) (n : Nat) (t : T) (k v : Nat) : T × Bool :=
  match find bk t k with
  | some e => (setV t e.s v, true)
  | none => push bk n t k v

/-- `Table::insert_dup`. -/
def insertDup (bk : Nat → Nat) (n : Nat) (t : T) (k v : Nat) : T × Bool := push bk n t k v

/-- `Table::remove`: the entry `find` gives, and its value. -/
def remove (bk : Nat → Nat) (t : T) (k : Nat) : T × Option Nat :=
  match find bk t k with
  | some e => (pop t e, some e.v)
  | none => (t, none)

/-- `Table::remove_pair`: the first entry along the chain that holds exactly `k` and `v`. -/
def removePair (bk : Nat → Nat) (t : T) (k v : Nat) : T × Bool :=
  match (t.chain (bk k)).find? fun e => e.k == k && e.v == v with
  | some e => (pop t e, true)
  | none => (t, false)

/-- `Table::touch`: the entry `find` gives moves to the newest place of the order list; the chains are untouched. -/
def touch (bk : Nat → Nat) (t : T) (k : Nat) : T :=
  match find bk t k with
  | some e =>
    if t.order.getLast? = some e then t
    else { t with order := (t.order.filter fun x => x.s != e.s) ++ [e] }
  | none => t

/-- `Table::matches::<M>`: the values of the first `M` entries along the chain, newest push first, and how many. -/
def matchesOf (bk : Nat → Nat) (t : T) (k : Nat) (m : Nat) : List Nat × Nat :=
  let es := (holders bk t k).take m
  (es.map (·.v), es.length)

/-- `Table::iter`: the pairs, oldest first. -/
def iter (t : T) : List (Nat × Nat) := t.order.map fun e => (e.k, e.v)

end Pinc.CoreTable
