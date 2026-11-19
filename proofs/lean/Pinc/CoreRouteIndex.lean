/-!
# The table of sessions by address: the model

A model of the endpoint's table of sessions by address (`pinc-core` `endpoint.rs`: the field `by_route`, the methods
`sync_route`, `free_slot` and `session_from`, and `Meta::route` in `slot.rs`). The story: a hub holds sessions in `k`
slots. Each slot's session may have an active path that is validated and direct, from some remote address; a datagram
from that address is the session's. The endpoint keeps a table from that address to the slot, so it can say who sent
a datagram without looking at every session. After every input that touches a session, the endpoint settles it, and
settling brings the session's entry in line with its path (`sync`); a freed slot loses its entry (`free`). What must
never happen: the table names a session at an address its path is not from and the lookup answers it, or a session
whose path is from an address is missing from the table, or the table grows past `k` entries.

Addresses and slots are numbers here. The table is the list of its entries, `(address, slot)`: what
`Pinc.CoreTable` proves the code's `Table` to be (its order list, the entries a key's chain holds and
`remove_pair` taking exactly the entry it names when the pair is held once), so `insert_dup` is a `cons`,
`remove_pair` is an `erase` and the holders of an address are the entries with that address. `route i` is
`Meta::route` of slot `i`: the address the slot holds an entry under, if any. `cur i` is the truth the code reads at
the moment of a lookup (`direct_remote`): the address of slot `i`'s validated direct path, or none.

The theorems are in `Pinc.CoreRouteIndexThm`.
-/

namespace Pinc.CoreRouteIndex

-- The state: each slot's `Meta::route`, and the table's entries (address, slot).
structure S where
  -- `Meta::route` of every slot.
  route : Nat → Option Nat
  -- The entries of `by_route`, newest first.
  idx : List (Nat × Nat)

-- A new endpoint: no slot holds an entry and the table is empty (`Table::new`, `Meta::EMPTY`).
def S.empty : S := ⟨fun _ => none, []⟩

-- `f` with slot `i` set to `v`.
def upd (f : Nat → Option Nat) (i : Nat) (v : Option Nat) : Nat → Option Nat := fun j => if j = i then v else f j

-- The table without the entry of slot `i`, if `route` gives it one: `remove_pair(old, i)`.
def drop (s : S) (i : Nat) : List (Nat × Nat) :=
  match s.route i with
  | some a => s.idx.erase (a, i)
  | none => s.idx

-- `sync_route(i)`, with `want` what `direct_remote(i)` reads now and `k` the table's capacity: nothing when the
-- slot's entry already says `want`; otherwise the old entry leaves, and a new one is added (`insert_dup`) when `want`
-- names an address and the table has room. A refused entry leaves the slot without one.
def sync (k : Nat) (s : S) (i : Nat) (want : Option Nat) : S :=
  if s.route i = want then s
  else
    match want with
    | some a =>
      if (drop s i).length < k then ⟨upd s.route i (some a), (a, i) :: drop s i⟩
      else ⟨upd s.route i none, drop s i⟩
    | none => ⟨upd s.route i none, drop s i⟩

-- `free_slot(i)`: the slot's entry leaves and the slot holds none.
def free (s : S) (i : Nat) : S := ⟨upd s.route i none, drop s i⟩

-- The slots the table holds under address `a` (`Table::holders`).
def holders (s : S) (a : Nat) : List Nat := (s.idx.filter fun e => e.1 == a).map (·.2)

-- `session_from(a, keep)` before its `min`: the holders of `a` whose path is from `a` now and that `keep` accepts.
-- The code answers the least session id of these.
def candidates (s : S) (cur : Nat → Option Nat) (keep : Nat → Bool) (a : Nat) : List Nat :=
  (holders s a).filter fun i => cur i == some a && keep i

-- The walk the table replaces: every slot below `k` whose path is from `a` now and that `keep` accepts.
def walk (k : Nat) (cur : Nat → Option Nat) (keep : Nat → Bool) (a : Nat) : List Nat :=
  (List.range k).filter fun i => cur i == some a && keep i

end Pinc.CoreRouteIndex
