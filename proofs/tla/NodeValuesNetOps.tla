--------------------------- MODULE NodeValuesNetOps ---------------------------
(***************************************************************************)
(* The operators of the values layer's tables (pinc-node values_net.rs,   *)
(* Net and next_fetch_id), shared by NodeValuesNet.tla and                *)
(* TraceNodeValuesNet.tla.                                                 *)
(*                                                                         *)
(* A net is a record:                                                      *)
(*   provs    the provider table, a sequence: number k is provs[k + 1], a  *)
(*            slot [peer |-> p, uses |-> u] with p > 0, or Free (peer 0);  *)
(*   streams  the stream table, a set of [lid, prov, owner]: the layer's   *)
(*            number, the provider number the stream holds a use of, and   *)
(*            its owner (a fetch id, or 0 for the server, Owner::Serve);   *)
(*   next     the last stream number handed out (Net::next);               *)
(*   held     the providers each running fetch holds, a set of [f, ps]     *)
(*            with ps a sequence of numbers (Net::held);                   *)
(*   refused  the fetches the provider table refused (Net::refused).       *)
(* cap bounds the provider table and scap the stream table (both          *)
(* TABLE_MAX in the code). A use count is never near u32::MAX: the        *)
(* holders of a number are at most the streams and the running fetches'   *)
(* lists, so the saturating add is a plain add here.                       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

Free == [peer |-> 0, uses |-> 0]
Net0 == [provs |-> <<>>, streams |-> {}, next |-> 0, held |-> {}, refused |-> 0]
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* the free slots at the end leave the table (Net::release, the loop after the give-back)
RECURSIVE Trim(_)
Trim(ps) == IF ps # <<>> /\ ps[Len(ps)].peer = 0 THEN Trim(SubSeq(ps, 1, Len(ps) - 1)) ELSE ps

\* Net::acquire: the number the peer has, else the first free slot, else a new slot while the table has room; one more
\* use. ok is FALSE (None) when the table is full and the peer is not in it; nothing changes then.
Acquire(ps, p, cap) ==
    LET f == {i \in 1..Len(ps) : ps[i].peer = p}
        fr == {i \in 1..Len(ps) : ps[i].peer = 0}
        i == IF f # {} THEN Min(f) ELSE IF fr # {} THEN Min(fr) ELSE Len(ps) + 1
        base == IF i > Len(ps) THEN Append(ps, Free) ELSE ps
    IN IF f = {} /\ fr = {} /\ Len(ps) >= cap
       THEN [ok |-> FALSE, ps |-> ps, num |-> 0]
       ELSE [ok |-> TRUE, ps |-> [base EXCEPT ![i] = [peer |-> p, uses |-> @.uses + 1]], num |-> i - 1]

\* Net::hold: one more use of a number in use; ok is FALSE (None) for a free number
Hold(ps, num) ==
    IF num + 1 \in 1..Len(ps) /\ ps[num + 1].peer # 0
    THEN [ok |-> TRUE, ps |-> [ps EXCEPT ![num + 1].uses = @ + 1]]
    ELSE [ok |-> FALSE, ps |-> ps]

\* Net::release: one use given back; the last frees the slot; the free tail leaves. A give-back of a free number is a
\* debug assertion in the code and changes nothing here (the tail is already trimmed).
Release(ps, num) ==
    IF num + 1 \in 1..Len(ps) /\ ps[num + 1].peer # 0
    THEN Trim([ps EXCEPT ![num + 1] = IF @.uses <= 1 THEN Free ELSE [peer |-> @.peer, uses |-> @.uses - 1]])
    ELSE Trim(ps)

RECURSIVE ReleaseAll(_, _)
ReleaseAll(ps, nums) == IF nums = <<>> THEN ps ELSE ReleaseAll(Release(ps, Head(nums)), Tail(nums))

\* Net::acquire_all: a use of every peer, in order, or of none: at the first refusal the uses taken are given back
RECURSIVE AcqAll(_, _, _, _)
AcqAll(ps, peers, got, cap) ==
    IF peers = <<>> THEN [ok |-> TRUE, ps |-> ps, nums |-> got]
    ELSE LET a == Acquire(ps, Head(peers), cap)
         IN IF ~a.ok THEN [ok |-> FALSE, ps |-> ReleaseAll(ps, got), nums |-> <<>>]
            ELSE AcqAll(a.ps, Tail(peers), Append(got, a.num), cap)

\* Net::add: the stream takes over the use of num; with the stream table full the use is given back and lid is 0 (None)
AddR(n, num, owner, scap) ==
    IF Cardinality(n.streams) >= scap
    THEN [n |-> [n EXCEPT !.provs = Release(n.provs, num)], lid |-> 0]
    ELSE [n |-> [n EXCEPT !.next = @ + 1,
                          !.streams = @ \cup {[lid |-> n.next + 1, prov |-> num, owner |-> owner]}],
          lid |-> n.next + 1]

Running(n) == {x.f : x \in n.held}
HeldOf(n, f) == (CHOOSE x \in n.held : x.f = f).ps

\* values.rs start_fetch over the table: acquire_all, then begin_fetch; a refusal counts and changes nothing else
Start(n, f, peers, cap) ==
    LET a == AcqAll(n.provs, peers, <<>>, cap)
    IN IF a.ok THEN [ok |-> TRUE, n |-> [n EXCEPT !.provs = a.ps, !.held = @ \cup {[f |-> f, ps |-> a.nums]}]]
       ELSE [ok |-> FALSE, n |-> [n EXCEPT !.provs = a.ps, !.refused = @ + 1]]

\* start_fetch for a fetch done as it starts (or refused by the value layer): acquire_all, then release_all
StartDone(n, peers, cap) ==
    LET a == AcqAll(n.provs, peers, <<>>, cap)
    IN IF a.ok THEN [ok |-> TRUE, n |-> [n EXCEPT !.provs = ReleaseAll(a.ps, a.nums)]]
       ELSE [ok |-> FALSE, n |-> [n EXCEPT !.provs = a.ps, !.refused = @ + 1]]

\* Net::end_fetch: what the fetch holds is given back; an id not running changes nothing
EndFetch(n, f) ==
    IF f \notin Running(n) THEN n
    ELSE LET x == CHOOSE y \in n.held : y.f = f
         IN [n EXCEPT !.provs = ReleaseAll(n.provs, x.ps), !.held = @ \ {x}]

\* values_stream_opened over the table: acquire the peer, then add a served stream (a refused acquire adds nothing)
Serve(n, p, cap, scap) ==
    LET a == Acquire(n.provs, p, cap)
    IN IF ~a.ok THEN [n |-> n, lid |-> 0] ELSE AddR([n EXCEPT !.provs = a.ps], a.num, 0, scap)

\* Net::add_for, as open_stream calls it: a stream of fetch f for the k-th provider it holds
OpenFor(n, f, k, scap) ==
    LET num == HeldOf(n, f)[k]
        h == Hold(n.provs, num)
    IN IF ~h.ok THEN [n |-> n, lid |-> 0] ELSE AddR([n EXCEPT !.provs = h.ps], num, f, scap)

\* Net::drop_stream: the stream leaves and gives its use back; an unknown number changes nothing
Drop(n, lid) ==
    LET d == {x \in n.streams : x.lid = lid}
    IN IF d = {} THEN n
       ELSE LET x == CHOOSE y \in d : TRUE IN [n EXCEPT !.streams = @ \ d, !.provs = Release(n.provs, x.prov)]

\* next_fetch_id over a u32 written as two limbs of L values each (65536 in the code): the next id after x that is
\* not 0 and not running, with the number of steps the loop took
Succ(x, L) == IF x[2] = L - 1 THEN (IF x[1] = L - 1 THEN <<0, 0>> ELSE <<x[1] + 1, 0>>) ELSE <<x[1], x[2] + 1>>
RECURSIVE NextIdFrom(_, _, _, _)
NextIdFrom(x, running, L, k) ==
    LET y == Succ(x, L)
    IN IF y # <<0, 0>> /\ y \notin running THEN [id |-> y, steps |-> k + 1] ELSE NextIdFrom(y, running, L, k + 1)

\* values_provide.rs, Node::values_provide and values_unprovide over a set of roots bounded by pcap (PROVIDED_MAX)
Provide(pv, r, pcap) == IF r \in pv \/ Cardinality(pv) < pcap THEN [ok |-> TRUE, pv |-> pv \cup {r}] ELSE [ok |-> FALSE, pv |-> pv]
Unprovide(pv, r) == [ok |-> r \in pv, pv |-> pv \ {r}]

\* how many holders hold a use of num: the streams of it and its places in the running fetches' lists
RECURSIVE SumOcc(_, _)
SumOcc(H, num) ==
    IF H = {} THEN 0
    ELSE LET x == CHOOSE y \in H : TRUE
         IN Cardinality({k \in 1..Len(x.ps) : x.ps[k] = num}) + SumOcc(H \ {x}, num)
Holders(n, num) == Cardinality({x \in n.streams : x.prov = num}) + SumOcc(n.held, num)
HeldNums(n) == {x.prov : x \in n.streams} \cup UNION {{x.ps[k] : k \in 1..Len(x.ps)} : x \in n.held}

\* the use count of every slot is its holders, a free slot has none, and every number held is a slot of the table
Exact(n) == /\ \A i \in 1..Len(n.provs) : n.provs[i].uses = Holders(n, i - 1)
            /\ \A num \in HeldNums(n) : num < Len(n.provs)
=============================================================================
