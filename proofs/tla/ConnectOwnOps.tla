--------------------------- MODULE ConnectOwnOps ---------------------------
(***************************************************************************)
(* The node's own record and address discovery, as pure operators:         *)
(* relay/discovery.rs (the QAD answer), client/conn.rs (set_local,         *)
(* probe_all, handle_udp for a QADR, candidates, set_hints),               *)
(* client/netcheck.rs (probe_sent, answered, reflexive_into) and           *)
(* client/signing.rs (record_job, start_jobs) and restore_record_seq.      *)
(* ConnectOwn.tla (the model check) and TraceConnectOwn.tla (the trace     *)
(* validation) use them.                                                   *)
(*                                                                         *)
(* An address is a small natural, 0 meaning none; a relay is its position  *)
(* 1..n in the node's configuration, cf.udp[k] its configured UDP address  *)
(* (0: none); nonces are naturals above 0. The node state S is             *)
(*   probe[k]  the nonce of the outstanding probe to relay k, 0 if none    *)
(*   refl[k]   the reflexive address relay k reported, 0 if none           *)
(*   local     the node's own addresses, at most cf.cap (MAX_ADDRS = 8)    *)
(*   wall      the wall clock of the last tick, in ms (0: none, after a    *)
(*             tick without one too: fix K8)                               *)
(*   last      the sequence number of the last record built (0: none yet)  *)
(* cf.cap is MAX_ADDRS; the real value is 8, TLC checks small ones and the *)
(* Lean theorems (ConnectOwn.lean) hold for all. The home relay, the       *)
(* reachability class and the hints are inputs of the record: the home and *)
(* the class are chosen by the rules of ConnectClientOps.tla.              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

Min(a, b) == IF a < b THEN a ELSE b

NewNode(cf) == [probe |-> [k \in 1..Len(cf.udp) |-> 0], refl |-> [k \in 1..Len(cf.udp) |-> 0], local |-> <<>>, wall |-> 0,
                last |-> 0]

(* relay/discovery.rs: a QAD query is answered with its own nonce and the address it came from *)
QadReply(nonce, src) == [nonce |-> nonce, addr |-> src]

(* set_local: the first cap addresses *)
SetLocal(cf, S, addrs) == [S EXCEPT !.local = SubSeq(addrs, 1, Min(Len(addrs), cf.cap))]

(* probe_all: a probe with a fresh nonce to every relay that takes UDP (nonces[k] is the nonce drawn for relay k) *)
ProbeAll(cf, S, nonces) == [S EXCEPT !.probe = [k \in 1..Len(cf.udp) |-> IF cf.udp[k] # 0 THEN nonces[k] ELSE S.probe[k]]]

(* handle_udp for a QADR from address from, with the nonce and the address the relay reports: it is the relay whose
   configured address is from (the first such), and Netcheck::answered takes it only for the outstanding nonce *)
RelayAt(cf, from) == IF from # 0 /\ \E k \in 1..Len(cf.udp) : cf.udp[k] = from
                     THEN CHOOSE k \in 1..Len(cf.udp) : cf.udp[k] = from /\ \A j \in 1..(k - 1) : cf.udp[j] # from
                     ELSE 0
Observe(cf, S, from, nonce, addr) ==
    LET k == RelayAt(cf, from) IN
    IF k = 0 \/ S.probe[k] = 0 \/ S.probe[k] # nonce THEN [S |-> S, took |-> FALSE]
    ELSE [S |-> [S EXCEPT !.probe[k] = 0, !.refl[k] = addr], took |-> TRUE]

(* Netcheck::restart *)
Restart(S) == [S EXCEPT !.probe = [k \in 1..Len(S.probe) |-> 0], !.refl = [k \in 1..Len(S.refl) |-> 0]]

InSeq(s, a) == \E i \in 1..Len(s) : s[i] = a

(* Netcheck::reflexive_into: the distinct reflexive addresses in relay order (an address that several relays report is
   listed once, at its first relay), as many as fit in cap *)
ReflList(cf, S) == LET F[k \in 0..Len(S.refl)] == IF k = 0 THEN <<>> ELSE IF S.refl[k] # 0 /\ ~InSeq(F[k - 1], S.refl[k]) THEN Append(F[k - 1], S.refl[k]) ELSE F[k - 1]
                   IN SubSeq(F[Len(S.refl)], 1, Min(Len(F[Len(S.refl)]), cf.cap))

(* Connectivity::candidates: reflexive first, then the local ones not yet there, up to cap *)
Cands(cf, S) == LET r0 == ReflList(cf, S)
                    F[i \in 0..Len(S.local)] == IF i = 0 THEN r0
                        ELSE IF Len(F[i - 1]) < cf.cap /\ ~InSeq(F[i - 1], S.local[i]) THEN Append(F[i - 1], S.local[i]) ELSE F[i - 1]
                IN F[Len(S.local)]

(* tick takes the wall clock it is given; without one (0) the layer has none (fix K8: the clock of an earlier tick
   is not kept) *)
Tick(S, wall) == [S EXCEPT !.wall = wall]

(* the number of a record built at wall clock wall after the one numbered last: the clock, or one above the last when
   the clock did not move past it (the code's addition saturates at 2^64 - 1, which the small numbers here never reach;
   the Lean model has it) *)
NextSeq(wall, last) == IF wall > last THEN wall ELSE last + 1

(* record_job, called by start_jobs with the wall clock of the last tick: the fields of the record that is signed *)
RecordJob(cf, S, home, class, hints) == [seq |-> NextSeq(S.wall, S.last), home |-> home, reach |-> class, addrs |-> Cands(cf, S), hints |-> hints]

(* record_job keeps the number of the record it built as the last one *)
Built(S, j) == [S EXCEPT !.last = j.seq]

(* restore_record_seq: the last number is raised to n, never lowered *)
RestoreSeq(S, n) == IF n > S.last THEN [S EXCEPT !.last = n] ELSE S
=============================================================================
