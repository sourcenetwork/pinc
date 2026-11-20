---------------------------- MODULE FacadeRecords ---------------------------
(***************************************************************************)
(* Discovery by signed records in the facade: what a lookup may believe.    *)
(*                                                                         *)
(* Who acts. Nodes publish records with rising sequence numbers to a store  *)
(* nobody trusts. The store may hold the newest record, an older one of the *)
(* same node (a replay), a record of another node filed under this one, or  *)
(* bytes that do not verify (a forgery). A looking-up endpoint fetches what *)
(* the store holds, keeps it only if it verifies and names the node asked   *)
(* about, and keeps the newer of that and what it already knew.            *)
(*                                                                         *)
(* What must never happen. The endpoint believes a record its node did not  *)
(* sign (KnownGenuine); what it believes about a node goes back to an older *)
(* record (NoRollback); a lookup answers with something other than the      *)
(* newest genuine record it has seen of that node (LookupNewest).          *)
(*                                                                         *)
(* Rust: crates/pinc/src/records.rs `PeerRecord::verified` (signature, key  *)
(* to node id binding and the node asked about), `newest`, `Records::find`; *)
(* crates/pinc/src/endpoint.rs `Endpoint::{signed_record, lookup}` (the     *)
(* rising sequence number). Lean counterpart: Pinc/FacadeRecords.lean       *)
(* (`inv_reach`, `noSeqCheck_bad`).                                         *)
(*                                                                         *)
(* Witness (scripts/proofs.sh witness_tlc): SeqCheck = FALSE keeps whatever *)
(* verified record was fetched last; a replayed older record then rolls the *)
(* endpoint back and NoRollback fails.                                      *)
(*                                                                         *)
(* The known table is bounded as the code has it: at most KMAX nodes       *)
(* (records.rs `KNOWN_MAX`, 4096); `remember` forgets one other node's      *)
(* record (whichever the map yields first: any) to take a new node when it *)
(* is full. A forgotten node's next lookup takes whatever verifies, so a    *)
(* replay older than what was once believed is believed again: NoRollback  *)
(* holds only while no node is forgotten (HeldNoRollback: a held record   *)
(* never goes back, checked with forgetting in FacadeRecords_bounded.cfg), *)
(* and FacadeRecords_evict.cfg                                             *)
(* (KMAX 1) shows NoReplayBelieved failing (finding a).                    *)
(*                                                                         *)
(* RELAYS: the endpoint knows relays (a node that carries the relay role, *)
(* ordinary or deployed from the relay binary). When the store yields      *)
(* nothing that verifies and nothing is known, `Endpoint::lookup`          *)
(* (endpoint/records.rs 105-114) answers with the record the relays found  *)
(* (`relay_record`), which the connectivity client verified, but neither   *)
(* weighs it against nor keeps it in the known table (RelayLookup).        *)
(* FacadeRecords_relay.cfg shows LookupNewest failing (finding b); the      *)
(* answers stay genuine (AnswerGenuine, FacadeRecords_bounded.cfg).         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Nodes,     \* the nodes that publish
    MaxSeq,    \* the most records a node publishes
    SeqCheck,  \* FALSE: the fetched record always replaces the known one (a witness config)
    KMAX,      \* the most nodes the known table holds (KNOWN_MAX)
    RELAYS     \* the endpoint knows relays, which answer a lookup the store misses

\* A record: who signed it, its sequence number, and whether its signature verifies. Seq 0 stands for "none".
Recs == [signer : Nodes, seq : 0..MaxSeq, sound : BOOLEAN]
NoRec == [signer |-> CHOOSE n \in Nodes : TRUE, seq |-> 0, sound |-> FALSE]

VARIABLES
    published,  \* per node: the highest sequence number it has published
    store,      \* per node: the record the store hands out for it
    known,      \* per node: the record the endpoint believes, or NoRec
    peak,       \* per node: the highest sequence number the endpoint has believed (history, for NoRollback)
    answer      \* the last lookup: [node, rec]

vars == <<published, store, known, peak, answer>>

\* The endpoint's check: the signature verifies and the record names the node asked about.
Verified(n, r) == r.sound /\ r.signer = n /\ r.seq > 0

\* `newest` in records.rs: the fetched record only if it is newer than the known one.
Newest(k, f) == IF ~SeqCheck THEN f ELSE IF f.seq > k.seq THEN f ELSE k

Init ==
    /\ published = [n \in Nodes |-> 0]
    /\ store = [n \in Nodes |-> NoRec]
    /\ known = [n \in Nodes |-> NoRec]
    /\ peak = [n \in Nodes |-> 0]
    /\ answer = [node |-> CHOOSE n \in Nodes : TRUE, rec |-> NoRec]

\* A node publishes a record with a sequence number above every earlier one; the store takes it.
Publish(n) ==
    /\ published[n] < MaxSeq
    /\ published' = [published EXCEPT ![n] = @ + 1]
    /\ store' = [store EXCEPT ![n] = [signer |-> n, seq |-> published[n] + 1, sound |-> TRUE]]
    /\ UNCHANGED <<known, peak, answer>>

\* The store misbehaves for `n`: an older genuine record of `n`, any record of another node, or bytes that do not
\* verify with any sequence number.
Tamper(n) ==
    /\ \E r \in Recs :
        /\ \/ r.signer = n /\ r.sound /\ r.seq <= published[n] /\ r.seq > 0
           \/ r.signer # n
           \/ ~r.sound
        /\ store' = [store EXCEPT ![n] = r]
    /\ UNCHANGED <<published, known, peak, answer>>

Held(k) == {m \in Nodes : k[m] # NoRec}
\* `remember`: a node not held, at a full table, first forgets one other node's record (any)
Remember(n, best) ==
    IF n \notin Held(known) /\ Cardinality(Held(known)) >= KMAX
    THEN \E m \in Held(known) : known' = [known EXCEPT ![m] = NoRec, ![n] = best]
    ELSE known' = [known EXCEPT ![n] = best]

\* The endpoint looks `n` up: what verifies is weighed against what it knew; the answer is what it now believes.
\* Nothing verified and nothing known: `find` returns None before `remember`, the table is unchanged.
Lookup(n) ==
    LET f == store[n]
        best == IF Verified(n, f) THEN Newest(known[n], f) ELSE known[n]
    IN /\ ~(RELAYS /\ best = NoRec)
       /\ IF best = NoRec THEN UNCHANGED known ELSE Remember(n, best)
       /\ peak' = [peak EXCEPT ![n] = IF best.seq > @ THEN best.seq ELSE @]
       /\ answer' = [node |-> n, rec |-> best]
       /\ UNCHANGED <<published, store>>

\* The store yields nothing for `n` and the endpoint has relays: the answer is a genuine record of `n` the relays
\* found (any published one, possibly older than one answered before) or none; the known table is not touched.
RelayLookup(n) ==
    /\ RELAYS
    /\ ~Verified(n, store[n]) /\ known[n] = NoRec
    /\ \E r \in {NoRec} \cup {[signer |-> n, seq |-> q, sound |-> TRUE] : q \in 1..published[n]} :
          answer' = [node |-> n, rec |-> r]
    /\ UNCHANGED <<published, store, known, peak>>

Next == \E n \in Nodes : Publish(n) \/ Tamper(n) \/ Lookup(n) \/ RelayLookup(n)

Spec == Init /\ [][Next]_vars

\* Every believed record was signed by its node and was really published by it.
KnownGenuine ==
    \A n \in Nodes : known[n].seq > 0 => known[n].signer = n /\ known[n].sound /\ known[n].seq <= published[n]
\* What the endpoint believes about a node is never older than something it believed before.
NoRollback == \A n \in Nodes : known[n].seq = peak[n]
\* A lookup answers with the newest genuine record seen of that node, or nothing if none was.
LookupNewest == answer.rec = known[answer.node]
\* A lookup answers with a record its node signed and published, or nothing.
AnswerGenuine == answer.rec.seq > 0 => answer.rec.signer = answer.node /\ answer.rec.sound
                                       /\ answer.rec.seq <= published[answer.node]
\* The known table holds at most KMAX nodes.
Bounded == Cardinality(Held(known)) <= KMAX
\* While a node's record is held it is never replaced by an older one: what is held only rises or is forgotten (a full
\* table forgets one node; its next lookup takes what the store holds, NoReplayBelieved's finding). This is the
\* documented rule of records.rs: no rollback for a node whose record is held.
HeldNoRollback == [][\A n \in Nodes : known[n].seq > 0 => known'[n].seq = 0 \/ known'[n].seq >= known[n].seq]_vars
\* What the endpoint believes about a node is never older than something it believed before (unlike NoRollback, a
\* node forgotten by a full table is allowed to hold nothing).
NoReplayBelieved == \A n \in Nodes : known[n].seq > 0 => known[n].seq >= peak[n]
=============================================================================
