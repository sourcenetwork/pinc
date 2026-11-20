---------------------------- MODULE NodeValuesNet ----------------------------
(***************************************************************************)
(* The values layer's tables (pinc-node values_net.rs: Net, its provider  *)
(* table and stream table; next_fetch_id) over every sequence of the      *)
(* calls the node makes on them, at small sizes (NodeValuesNetOps.tla has  *)
(* the operators):                                                         *)
(*   StartA     values.rs start_fetch: acquire_all then begin_fetch;       *)
(*   StartDoneA start_fetch of a fetch done (or refused by the value       *)
(*              layer) as it starts: acquire_all then release_all;         *)
(*   EndA       end_fetch of a running fetch (values_drain, cancel_fetch); *)
(*   ServeA     values_stream_opened: acquire then add as Serve;           *)
(*   OpenA      open_stream: add_for one of the fetch's providers;         *)
(*   DropA      drop_stream (every way a stream leaves).                   *)
(* A fetch id is begun only when it is not running (next_fetch_id skips   *)
(* running ids; NextIdOK below checks that over a small wrap).             *)
(*                                                                         *)
(* Checked, from the module documentation of values_net.rs:               *)
(*  - Bounded: each table holds at most its bound (TABLE_MAX);            *)
(*  - Exact: a number's use count is its holders (the running fetches'    *)
(*    lists and the streams), so the last use given back frees the slot;  *)
(*    every number held is in the table; Trimmed: no free slot at the end; *)
(*    OnePeer: a peer has one number;                                      *)
(*  - ByPeak: the table is never longer than the most providers in use at *)
(*    once so far ("bounded by the providers in use, not by the node's    *)
(*    history"; the witness NodeValuesNet_hole shows it can be longer than *)
(*    the providers in use now: a hole below a slot in use stays);        *)
(* and in every step:                                                      *)
(*  - KeepsPeer: a number keeps its peer for every holder that holds it   *)
(*    before and after the step;                                           *)
(*  - FirstFree: a peer new to the table takes the first free slot, and   *)
(*    GrowsOnlyFull: the table grows only when no slot is free;           *)
(*  - RefusedWhole: a fetch the provider table refuses changes nothing but *)
(*    the refusal count;                                                   *)
(*  - GivesBack: a stream refused (provider table or stream table full)   *)
(*    changes nothing, its use is given back; a fetch done at start leaves *)
(*    the tables as they were;                                             *)
(* and once (ASSUME): next_fetch_id is never 0, never a running id, and   *)
(* takes at most as many steps as running ids plus two, for every last id *)
(* and every set of running ids that leaves one id free, over a u32 of     *)
(* two limbs of LIMB values.                                               *)
(* Witnesses: NodeValuesNet_refused (a fetch is refused whole),           *)
(* NodeValuesNet_sfull (a stream is refused for a full stream table),     *)
(* NodeValuesNet_hole (the table is longer than the providers in use).    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS CAP, SCAP, PEERS, FIDS, LISTMAX, NMAX, LIMB
VARIABLES n, op, peak
vars == <<n, op, peak>>

INSTANCE NodeValuesNetOps

Lists == UNION {[1..k -> PEERS] : k \in 1..LISTMAX}
InUse(m) == Cardinality({i \in 1..Len(m.provs) : m.provs[i].peer # 0})
Max2(a, b) == IF a >= b THEN a ELSE b

Init == n = Net0 /\ op = [k |-> "init", ok |-> TRUE, p |-> 0] /\ peak = 0
Upd(m, o) == n' = m /\ op' = o /\ peak' = Max2(peak, InUse(m))

StartA(f, ps) == f \notin Running(n) /\ LET r == Start(n, f, ps, CAP) IN Upd(r.n, [k |-> "start", ok |-> r.ok, p |-> 0])
StartDoneA(ps) == LET r == StartDone(n, ps, CAP) IN Upd(r.n, [k |-> "startdone", ok |-> r.ok, p |-> 0])
EndA(f) == f \in Running(n) /\ Upd(EndFetch(n, f), [k |-> "end", ok |-> TRUE, p |-> 0])
ServeA(q) == LET r == Serve(n, q, CAP, SCAP) IN Upd(r.n, [k |-> "serve", ok |-> r.lid # 0, p |-> q])
OpenA(f, j) == /\ f \in Running(n) /\ j \in 1..Len(HeldOf(n, f))
               /\ LET r == OpenFor(n, f, j, SCAP) IN Upd(r.n, [k |-> "open", ok |-> r.lid # 0, p |-> 0])
DropA(l) == Upd(Drop(n, l), [k |-> "drop", ok |-> TRUE, p |-> 0])

Next == \/ \E f \in FIDS, ps \in Lists : StartA(f, ps)
        \/ \E ps \in Lists : StartDoneA(ps)
        \/ \E f \in FIDS : EndA(f)
        \/ \E q \in PEERS : ServeA(q)
        \/ \E f \in FIDS, j \in 1..LISTMAX : OpenA(f, j)
        \/ \E x \in n.streams : DropA(x.lid)
Spec == Init /\ [][Next]_vars

\* the state space is finite only with a bound on the streams ever added and on the refusals counted: a refusal changes
\* nothing but the count and op (RefusedWhole), and no step reads either, so a state reached after more refusals is
\* reached after its last one alone; without the bound the same refusal repeats forever and the run never ends
Bound == n.next <= NMAX /\ n.refused <= 1

Bounded == Len(n.provs) <= CAP /\ Cardinality(n.streams) <= SCAP
Trimmed == n.provs = Trim(n.provs)
OnePeer == \A i, j \in 1..Len(n.provs) : (i # j /\ n.provs[i].peer # 0) => n.provs[i].peer # n.provs[j].peer
ByPeak == Len(n.provs) <= peak
Inv == Bounded /\ Trimmed /\ OnePeer /\ Exact(n) /\ ByPeak

PeerOf(m, num) == m.provs[num + 1].peer
KeepsPeer == /\ \A x \in n.streams \cap n'.streams : PeerOf(n', x.prov) = PeerOf(n, x.prov)
             /\ \A x \in n.held \cap n'.held : \A j \in 1..Len(x.ps) : PeerOf(n', x.ps[j]) = PeerOf(n, x.ps[j])
FirstFree == (op'.k = "serve" /\ op'.ok /\ \A i \in 1..Len(n.provs) : n.provs[i].peer # op'.p) =>
                 LET fr == {i \in 1..Len(n.provs) : n.provs[i].peer = 0}
                 IN n'.provs[IF fr = {} THEN Len(n.provs) + 1 ELSE Min(fr)].peer = op'.p
GrowsOnlyFull == Len(n'.provs) > Len(n.provs) => \A i \in 1..Len(n.provs) : n.provs[i].peer # 0
RefusedWhole == (op'.k \in {"start", "startdone"} /\ ~op'.ok) => n' = [n EXCEPT !.refused = @ + 1]
GivesBack == /\ (op'.k \in {"serve", "open"} /\ ~op'.ok) => n' = n
             /\ (op'.k = "startdone" /\ op'.ok) => n' = n
Steps == KeepsPeer /\ FirstFree /\ GrowsOnlyFull /\ RefusedWhole /\ GivesBack
StepProps == [][Steps]_vars

Ids == {<<a, b>> : a \in 0..(LIMB - 1), b \in 0..(LIMB - 1)}
NZ == Ids \ {<<0, 0>>}
NextIdOK == \A last \in Ids, R \in SUBSET NZ :
                Cardinality(R) < Cardinality(NZ) =>
                    LET r == NextIdFrom(last, R, LIMB, 0)
                    IN r.id # <<0, 0>> /\ r.id \notin R /\ r.steps <= Cardinality(R) + 2
ASSUME NextIdOK

\* witnesses: each is violated in a reachable state
NeverRefused == n.refused = 0
\* add_for on a held number is refused only by a full stream table
NeverStreamFull == ~(op.k = "open" /\ ~op.ok)
NoHole == Len(n.provs) <= InUse(n)
=============================================================================
