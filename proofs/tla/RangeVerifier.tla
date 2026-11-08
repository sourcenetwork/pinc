------------------------------- MODULE RangeVerifier -------------------------------
(***************************************************************************)
(* Model of vinc-dag RangeVerifier (tree/verify.rs): the stack of pending  *)
(* nodes (cv, lo, hi), the sticky failure flag and the log of released     *)
(* groups, for a tree of n groups and a requested group range              *)
(* [first, last). An adversary feeds, at each step, either the genuine     *)
(* item or any forged one drawn from a universe that holds every genuine   *)
(* chaining value, a forged one and every group payload. The buffer and    *)
(* partial feeds are not modelled: one Feed is one completed item.         *)
(*                                                                         *)
(* Hashes are symbolic terms, so a hash matches a chaining value only if   *)
(* the inputs are the genuine ones: this is collision resistance, as an    *)
(* explicit modelling assumption. The genuine payload of group g is g.     *)
(*                                                                         *)
(* Checked by TLC for every n in 0..MaxGroups and every range [first,last)*)
(* with first <= last <= n: released groups are genuine, ascending and in  *)
(* range, a rejected item releases nothing, a failure is permanent, and a  *)
(* complete verifier has released exactly the requested groups.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT MaxGroups

IsPow2(p) == \E k \in 0..MaxGroups : p = 2 ^ k

(* left_groups: the largest power of two strictly below c, for c >= 2 *)
Left(c) == CHOOSE p \in 1..c : IsPow2(p) /\ p < c /\ \A q \in 1..c : (IsPow2(q) /\ q < c) => q <= p

(* symbolic hashes: a leaf hash of (is-root, group index, payload), a parent hash of (is-root, left, right) *)
HL(root, g, d) == <<"L", root, g, d>>
HP(root, l, r) == <<"P", root, l, r>>

RECURSIVE GenCv(_, _, _)
GenCv(n, lo, hi) ==
    LET root == (lo = 0 /\ hi = n)
    IN IF hi - lo >= 2
       THEN LET mid == lo + Left(hi - lo) IN HP(root, GenCv(n, lo, mid), GenCv(n, mid, hi))
       ELSE HL(root, lo, lo)

RECURSIVE NodeSet(_, _)
NodeSet(lo, hi) ==
    IF hi - lo >= 2
    THEN LET mid == lo + Left(hi - lo) IN {<<lo, hi>>} \cup NodeSet(lo, mid) \cup NodeSet(mid, hi)
    ELSE {<<lo, hi>>}

(* what the adversary can put in a parent pair, and as group payload *)
CvU(n) == {GenCv(n, nd[1], nd[2]) : nd \in NodeSet(0, n)} \cup {<<"forged">>}
DataU == 0..MaxGroups

VARIABLES n, first, last, stack, failed, released
vars == <<n, first, last, stack, failed, released>>

Init ==
    /\ n \in 0..MaxGroups
    /\ first \in 0..n
    /\ last \in first..n
    /\ stack = IF first < last THEN <<[cv |-> GenCv(n, 0, n), lo |-> 0, hi |-> n]>> ELSE <<>>
    /\ failed = FALSE
    /\ released = <<>>

(* one completed stream item, read according to the kind of the node on top of the stack *)
Feed ==
    /\ ~failed
    /\ stack # <<>>
    /\ LET nd == Head(stack)
           rest == Tail(stack)
           root == (nd.lo = 0 /\ nd.hi = n)
       IN IF nd.hi - nd.lo = 1
          THEN \E d \in DataU :
                 IF HL(root, nd.lo, d) = nd.cv
                 THEN /\ stack' = rest
                      /\ released' = Append(released, <<nd.lo, d>>)
                      /\ UNCHANGED failed
                 ELSE /\ failed' = TRUE
                      /\ UNCHANGED <<stack, released>>
          ELSE \E l \in CvU(n), r \in CvU(n) :
                 IF HP(root, l, r) = nd.cv
                 THEN LET mid == nd.lo + Left(nd.hi - nd.lo)
                      IN /\ stack' = (IF first < mid THEN <<[cv |-> l, lo |-> nd.lo, hi |-> mid]>> ELSE <<>>)
                                     \o (IF mid < last THEN <<[cv |-> r, lo |-> mid, hi |-> nd.hi]>> ELSE <<>>)
                                     \o rest
                         /\ UNCHANGED <<failed, released>>
                 ELSE /\ failed' = TRUE
                      /\ UNCHANGED <<stack, released>>
    /\ UNCHANGED <<n, first, last>>

(* a failed or finished verifier takes no further step *)
Done == (failed \/ stack = <<>>) /\ UNCHANGED vars

Next == Feed \/ Done

Spec == Init /\ [][Next]_vars

Complete == ~failed /\ stack = <<>>

Range(a, b) == IF a >= b THEN <<>> ELSE [i \in 1..(b - a) |-> a + i - 1]
Clip(nd) == Range(IF nd.lo > first THEN nd.lo ELSE first, IF nd.hi < last THEN nd.hi ELSE last)
RECURSIVE FlatClip(_)
FlatClip(i) == IF i > Len(stack) THEN <<>> ELSE Clip(stack[i]) \o FlatClip(i + 1)

TypeOK ==
    /\ n \in 0..MaxGroups /\ first \in 0..n /\ last \in first..n
    /\ failed \in BOOLEAN
    /\ \A i \in 1..Len(stack) : stack[i].lo < stack[i].hi /\ stack[i].hi <= n

(* every released group is the genuine group at its index *)
ReleasedGenuine == \A i \in 1..Len(released) : released[i][2] = released[i][1]

(* releases come in strictly ascending order of index, inside the requested range *)
Ascending == \A i \in 1..(Len(released) - 1) : released[i][1] < released[i + 1][1]
InRange == \A i \in 1..Len(released) : first <= released[i][1] /\ released[i][1] < last

(* every pending node holds the genuine chaining value of its interval *)
StackGenuine == \A i \in 1..Len(stack) : stack[i].cv = GenCv(n, stack[i].lo, stack[i].hi)

(* released groups plus what the stack still covers is exactly the requested range, in order *)
Bookkeeping == [i \in 1..Len(released) |-> released[i][1]] \o FlatClip(1) = Range(first, last)

(* completion means every requested group was released *)
CompleteReleasedAll ==
    Complete => /\ Len(released) = last - first
                /\ {released[i][1] : i \in 1..Len(released)} = first..(last - 1)

(* a failure is permanent, and the step that fails releases nothing *)
FailureSticky == [][failed => failed']_vars
RejectReleasesNothing == [][(failed' /\ ~failed) => released' = released]_vars
=================================================================================
