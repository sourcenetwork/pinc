---------------------------- MODULE TableSlabOps ----------------------------
(***************************************************************************)
(* The operators of the sorted slab, pinc-table slab.rs (`SortedSlab`),    *)
(* step for step, shared by TableSlab.tla (the model check) and            *)
(* TraceTableSlab.tla (the trace check).                                   *)
(*                                                                         *)
(* A state is the slab as the code holds it: `recs` the records of slots   *)
(* 0..len-1 (<<key, value>>; keys compare as the integers the fixed-length *)
(* big-endian key bytes encode, which is the bytewise order slab.rs        *)
(* uses), `idx` the index entries 0..len-1 (slot numbers in key order),    *)
(* `len`, `cap`. The bytes past `len` in the record area and the index are *)
(* left out: the code reads none of them (every operator below reads only  *)
(* below the length it had when the call began, and TLC stops with an      *)
(* error on a read outside a function's domain, so this is checked, not    *)
(* assumed). The width of an index entry is TableBytes.tla's. A key or a   *)
(* value of the wrong length is the argument `kg` or `vg` FALSE. A result  *)
(* is <<call, outcome, number>>; `mv` says whether a record moved into a   *)
(* hole, for the witness.                                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

Empty == [k \in 0..(-1) |-> 0]

(* SortedSlab::new(mem, c, ...) once accepted (TableBytes.tla has the refusals) *)
Slab0(c) == [cap |-> c, len |-> 0, recs |-> Empty, idx |-> Empty]

(* SortedSlab::search: the binary search over the index, Ok(position) or Err(insertion point) *)
RECURSIVE SearchAt(_, _, _, _)
SearchAt(s, lo, hi, key) ==
    IF lo >= hi THEN [found |-> FALSE, p |-> lo]
    ELSE LET mid == lo + (hi - lo) \div 2
             km == s.recs[s.idx[mid]][1]
         IN IF km < key THEN SearchAt(s, mid + 1, hi, key)
            ELSE IF km > key THEN SearchAt(s, lo, mid, key)
            ELSE [found |-> TRUE, p |-> mid]
Search(s, key) == SearchAt(s, 0, s.len, key)

(* SortedSlab::insert: Length before anything; a key held gets the value; a new key on a full slab is Full;
   otherwise the record goes to slot len, the index entries from the insertion point move up one, and the point
   names the new slot *)
Insert(s, kg, vg, k, v) ==
    IF ~kg \/ ~vg THEN [s |-> s, r |-> <<"insert", "length", 0>>, mv |-> "none"]
    ELSE LET f == Search(s, k)
         IN IF f.found
            THEN [s |-> [s EXCEPT !.recs[s.idx[f.p]] = <<@[1], v>>], r |-> <<"insert", "true", 0>>, mv |-> "none"]
            ELSE IF s.len = s.cap THEN [s |-> s, r |-> <<"insert", "full", 0>>, mv |-> "none"]
            ELSE LET n == s.len
                     p == f.p
                 IN [s |-> [s EXCEPT !.len = n + 1,
                                     !.recs = [j \in 0..n |-> IF j < n THEN s.recs[j] ELSE <<k, v>>],
                                     !.idx = [j \in 0..n |-> IF j < p THEN s.idx[j]
                                                            ELSE IF j = p THEN n ELSE s.idx[j - 1]]],
                     r |-> <<"insert", "false", 0>>, mv |-> "none"]

(* SortedSlab::remove: the index entries above the position move down one, len = last; when the removed slot is
   not the last, the index entry that named the last slot (found by searching its key in the shortened index)
   names the hole, and the last record is copied into it *)
Remove(s, k) ==
    LET f == Search(s, k)
    IN IF ~f.found THEN [s |-> s, r |-> <<"remove", "false", 0>>, mv |-> "none"]
       ELSE LET p == f.p
                slot == s.idx[p]
                last == s.len - 1
                x1 == [j \in 0..(last - 1) |-> IF j < p THEN s.idx[j] ELSE s.idx[j + 1]]
                s1 == [s EXCEPT !.len = last, !.idx = x1]
            IN IF slot = last
               THEN [s |-> [s1 EXCEPT !.recs = [j \in 0..(last - 1) |-> s.recs[j]]],
                     r |-> <<"remove", "true", 0>>, mv |-> "none"]
               ELSE LET q == Search(s1, s.recs[last][1])
                        x2 == IF q.found THEN [x1 EXCEPT ![q.p] = slot] ELSE x1
                    IN [s |-> [s1 EXCEPT !.idx = x2,
                                         !.recs = [j \in 0..(last - 1) |->
                                                     IF j = slot THEN s.recs[last] ELSE s.recs[j]]],
                        r |-> <<"remove", "true", 0>>, mv |-> "remove"]

(* the value change of the closure `keep` of the model: values 1..vm, each kept one moves to the next *)
Bump(v, vm) == (v % vm) + 1

(* SortedSlab::retain, pass 1: in index order, each kept entry swaps down to position `kept`; `seen` is the keys in
   the order the closure is called *)
RECURSIVE Pass1(_, _, _, _, _, _, _, _, _)
Pass1(r, x, p, n, keep, mut, vm, kept, seen) ==
    IF p >= n THEN [r |-> r, x |-> x, kept |-> kept, seen |-> seen]
    ELSE LET sl == x[p]
             rc == r[sl]
         IN IF rc[1] \in keep
            THEN Pass1(IF mut THEN [r EXCEPT ![sl] = <<rc[1], Bump(rc[2], vm)>>] ELSE r,
                       [x EXCEPT ![kept] = sl, ![p] = x[kept]], p + 1, n, keep, mut, vm, kept + 1,
                       Append(seen, rc[1]))
            ELSE Pass1(r, x, p + 1, n, keep, mut, vm, kept, Append(seen, rc[1]))

(* pass 2, the scan for the next removed slot below `kept`: while j < len and idx[j] >= kept *)
RECURSIVE Skip(_, _, _, _)
Skip(x, j, kept, n) == IF j < n /\ x[j] >= kept THEN Skip(x, j + 1, kept, n) ELSE j

(* pass 2: a kept record in a slot at or above `kept` moves into the next removed slot below it; the `break` the
   code marks unreachable stops TLC with an error *)
RECURSIVE Pass2(_, _, _, _, _, _, _)
Pass2(r, x, q, j, kept, n, mvd) ==
    IF q >= kept THEN [r |-> r, x |-> x, mvd |-> mvd]
    ELSE LET sl == x[q]
         IN IF sl < kept THEN Pass2(r, x, q + 1, j, kept, n, mvd)
            ELSE LET j2 == Skip(x, j, kept, n)
                 IN IF j2 = n
                    THEN IF Assert(FALSE, "retain finds no removed slot for a kept record")
                         THEN [r |-> r, x |-> x, mvd |-> mvd] ELSE [r |-> r, x |-> x, mvd |-> mvd]
                    ELSE LET hole == x[j2]
                         IN Pass2([r EXCEPT ![hole] = r[sl]], [x EXCEPT ![q] = hole], q + 1, j2 + 1, kept, n, TRUE)

(* SortedSlab::retain with the closure "keep the keys in `keep`, and when `mut`, bump the value of each kept
   record"; the result is the number removed, `calls` the keys the closure saw in order *)
Retain(s, keep, mut, vm) ==
    LET a == Pass1(s.recs, s.idx, 0, s.len, keep, mut, vm, 0, <<>>)
        b == Pass2(a.r, a.x, 0, a.kept, a.kept, s.len, FALSE)
    IN [s |-> [s EXCEPT !.len = a.kept,
                        !.recs = [j \in 0..(a.kept - 1) |-> b.r[j]],
                        !.idx = [j \in 0..(a.kept - 1) |-> b.x[j]]],
        r |-> <<"retain", "ok", s.len - a.kept>>,
        mv |-> IF b.mvd THEN "retain" ELSE "none",
        calls |-> a.seen]

(* SortedSlab::clear *)
Clear(s) == [s |-> [s EXCEPT !.len = 0, !.recs = Empty, !.idx = Empty], r |-> <<"clear", "ok", 0>>, mv |-> "none"]

(* the queries: entry, get, contains, first, last, first_at_or_after, next_after, iter *)
Entry(s, p) == IF p < s.len THEN s.recs[s.idx[p]] ELSE <<>>
GetV(s, k) == LET f == Search(s, k) IN IF f.found THEN <<s.recs[s.idx[f.p]][2]>> ELSE <<>>
Contains(s, k) == Search(s, k).found
First(s) == Entry(s, 0)
Last(s) == IF s.len = 0 THEN <<>> ELSE Entry(s, s.len - 1)
AtOrAfter(s, k) == Entry(s, Search(s, k).p)
NextAfter(s, k) == LET f == Search(s, k) IN Entry(s, IF f.found THEN f.p + 1 ELSE f.p)
Iter(s) == [k \in 1..s.len |-> s.recs[s.idx[k - 1]]]

(* two sequences are equal, element by element *)
SeqEq(a, b) == Len(a) = Len(b) /\ \A k \in 1..Len(a) : a[k] = b[k]
=============================================================================
