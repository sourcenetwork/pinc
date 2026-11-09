--------------------------- MODULE ValuesPlanServer ---------------------------
(***************************************************************************)
(* The request slots of the value server (server.rs): S slots, each free,  *)
(* collecting a request, or serving a response for a root over rounded    *)
(* ranges. The events are the code's: a stream opened (the first free slot*)
(* or a BUSY reset, never a queue), a request answered (a value the store *)
(* does not hold whole, or a plan the value cannot give, resets with      *)
(* UNAVAILABLE and frees only its slot; otherwise the supersession pass    *)
(* frees every serving slot of the same peer, the same root and an         *)
(* overlapping range of another stream and resets it with SUPERSEDED,     *)
(* then the source is installed, which can be refused: UNAVAILABLE), a     *)
(* stream reset or finished, a closed session.                             *)
(*                                                                         *)
(* Checked: at most S requests are held and never two on one stream; a     *)
(* stream is reset SUPERSEDED exactly when it was another stream of the   *)
(* peer serving the root over a range the new request overlaps (and every *)
(* such stream is, whether or not the new request is then installed);     *)
(* every refusal frees the slot of the refused request and no other; a    *)
(* BUSY reset happens only with all slots held.                           *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/ValuesPlanServer.lean (held_le,      *)
(* opened_busy, opened_free, supersede_iff, supersedes_iff, refuse_spec,  *)
(* closed_iff), for every S.                                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS S, Streams, Peers, Roots, G

Free == [free |-> TRUE]
Collecting(st, p) == [stream |-> st, peer |-> p, root |-> 0, ranges |-> {}]
Serving(st, p, r, rg) == [stream |-> st, peer |-> p, root |-> r, ranges |-> rg]

Spans == {<<0, 1>>, <<1, 2>>, <<3, 1>>}
Reqs == {sp \in SUBSET Spans : Cardinality(sp) <= 2}

\* the rounded range of a span (whole groups of G)
Round(sp) == <<(sp[1] \div G) * G, (((sp[1] + sp[2] + G - 1) \div G) * G) - (sp[1] \div G) * G>>
Overlaps(rg, spans) == \E r \in rg, sp \in spans : sp[1] < r[1] + r[2] /\ r[1] < sp[1] + sp[2]

VARIABLES slots, ghost, held
vars == <<slots, ghost, held>>

IsFree(x) == "free" \in DOMAIN x
Used == {i \in 1 .. S : ~IsFree(slots[i])}
UsedStreams == {slots[i].stream : i \in Used}

\* ghost: what the last action did, for the invariants
NoGhost == [kind |-> "none"]

Init == slots = [i \in 1 .. S |-> Free] /\ ghost = NoGhost /\ held = 0

Open == \E st \in Streams \ UsedStreams, p \in Peers :
    IF Used = 1 .. S
    THEN /\ ghost' = [kind |-> "busy"] /\ UNCHANGED <<slots, held>>
    ELSE LET i == CHOOSE i \in 1 .. S : IsFree(slots[i]) /\ \A j \in 1 .. S : IsFree(slots[j]) => i <= j
         IN /\ slots' = [slots EXCEPT ![i] = Collecting(st, p)]
            /\ ghost' = [kind |-> "open", slot |-> i] /\ held' = held + 1

\* the answer to the request collected in slot i, for a root and spans; the store holds the value or not, and the
\* source is installed or refused
Answer == \E i \in Used, root \in Roots, req \in Reqs, holds \in BOOLEAN, installs \in BOOLEAN :
    /\ slots[i].root = 0
    /\ LET me == slots[i]
           mine == {Round(sp) : sp \in req}
           sup == {j \in Used \ {i} : slots[j].peer = me.peer /\ slots[j].root = root /\ slots[j].root # 0
                                       /\ Overlaps(slots[j].ranges, req)}
       IN IF ~holds
          THEN /\ slots' = [slots EXCEPT ![i] = Free]
               /\ held' = held - 1
               /\ ghost' = [kind |-> "unavailable", slot |-> i]
          ELSE LET freed == [j \in 1 .. S |-> IF j \in sup THEN Free ELSE slots[j]]
               IN IF installs
                  THEN /\ slots' = [freed EXCEPT ![i] = Serving(me.stream, me.peer, root, mine)]
                       /\ held' = held - Cardinality(sup)
                       /\ ghost' = [kind |-> "served", slot |-> i, peer |-> me.peer, root |-> root, req |-> req]
                  ELSE /\ slots' = [freed EXCEPT ![i] = Free]
                       /\ held' = held - Cardinality(sup) - 1
                       /\ ghost' = [kind |-> "refused", slot |-> i, peer |-> me.peer, root |-> root, req |-> req]

Done == \E i \in Used :
    /\ slots' = [slots EXCEPT ![i] = Free] /\ held' = held - 1
    /\ ghost' = [kind |-> "done", slot |-> i]

Closed == \E p \in Peers :
    LET gone == {i \in Used : slots[i].peer = p}
    IN /\ slots' = [i \in 1 .. S |-> IF i \in gone THEN Free ELSE slots[i]]
       /\ held' = held - Cardinality(gone)
       /\ ghost' = [kind |-> "closed", peer |-> p, gone |-> gone]

Next == Open \/ Answer \/ Done \/ Closed
Spec == Init /\ [][Next]_vars

(* ---- invariants ---- *)
HeldOK == /\ held = Cardinality(Used) /\ held <= S
UniqueStreams == \A i, j \in Used : i # j => slots[i].stream # slots[j].stream
BusyOnlyFull == ghost.kind = "busy" => Used = 1 .. S

\* the other slots after an answer: freed exactly when they were another stream of the peer serving the root over
\* a range the request overlaps (the pass runs for a request that is then installed or refused, not for an
\* unavailable value), untouched otherwise; the request's own slot is its own
AnswerOK ==
    /\ ghost'.kind \in {"served", "refused"} =>
         \A j \in 1 .. S : j # ghost'.slot =>
            IF ~IsFree(slots[j]) /\ slots[j].peer = ghost'.peer /\ slots[j].root = ghost'.root /\ slots[j].root # 0
               /\ Overlaps(slots[j].ranges, ghost'.req)
            THEN IsFree(slots'[j])
            ELSE slots'[j] = slots[j]
    /\ ghost'.kind = "unavailable" => \A j \in 1 .. S : j # ghost'.slot => slots'[j] = slots[j]
    /\ ghost'.kind = "served" => ~IsFree(slots'[ghost'.slot])
    /\ ghost'.kind \in {"refused", "unavailable"} => IsFree(slots'[ghost'.slot])
    /\ ghost'.kind = "closed" => \A j \in 1 .. S : IF j \in ghost'.gone THEN IsFree(slots'[j]) ELSE slots'[j] = slots[j]
    /\ ghost'.kind = "busy" => slots' = slots
Actions == [][AnswerOK]_vars
=============================================================================
