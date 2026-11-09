------------------------------ MODULE DtnCustody ------------------------------
(***************************************************************************)
(* Model check of custody, vinc-dtn/src/custody.rs: the book and the shared *)
(* ledger under every sequence of calls (DtnCustodyOps.tla, the same        *)
(* definitions the trace check uses). The environment calls accept (with   *)
(* any incoming offer id), offer, on_ack (a valid or an invalid ack, from   *)
(* any node, naming any offer id), delivered and the book's expire, and the *)
(* host calls the ledger directly: admit of a key the book holds no record  *)
(* of (transit bundles, mailbox items), expire, and release of a key the    *)
(* book holds no record of. The clock of every call is an input and may go  *)
(* back. The book's counter nx (next_offer) and the log `handed` of the ids *)
(* handed out are variables.                                                *)
(*                                                                          *)
(* Pinned behaviours: on_ack for a bundle whose item the ledger no longer   *)
(* holds drops the record and returns the store's Unknown ("storeunknown"); *)
(* accept answers the previous node and offer id of the INCOMING offer (the *)
(* result fields prev and offer), not the record's.                         *)
(*                                                                          *)
(* Properties (asserted on every step, plus invariants):                    *)
(*   CustodyExit      a custody item that has not expired leaves the ledger *)
(*                    or stops being custody only through delivered, a      *)
(*                    release of its key, or an ack of its bundle           *)
(*   ReliefOnlyByAck  the item becomes transit and the record clears exactly*)
(*                    when the ack is valid, the bundle is held, custody was*)
(*                    offered to exactly the acknowledging node under       *)
(*                    exactly the ack's offer id, and the ledger holds the  *)
(*                    item; every other ack moves nothing (a current offered*)
(*                    ack for an item the ledger already dropped clears the *)
(*                    record: storeunknown)                                 *)
(*   StaleAckMovesNothing  a valid ack of a held bundle that is not the     *)
(*                    outstanding offer (right node but another id, another *)
(*                    node, or an offer cancelled by a hand-back) is        *)
(*                    "notoffered" and changes nothing                      *)
(*   CustodyToTransit only an ack relieves                                  *)
(*   AcceptRefused    a refused accept (full book, custody refused, or an   *)
(*                    incoming bundle already expired) changes nothing but  *)
(*                    the expired items and their records; capacity exactly *)
(*                    when no record is free                                *)
(*   AcceptOk         the bundle is held and its item is custody; the answer*)
(*                    owed is the incoming previous node and offer id       *)
(*   HandBackCancels  accepting a bundle already held keeps the record and  *)
(*                    its previous custodian and cancels the outstanding    *)
(*                    offer of this node                                    *)
(*   Promote          a held item is promoted without new room              *)
(*   OfferIds         an offer returns the counter and increments it; the   *)
(*                    ids handed out are pairwise distinct (HandedExact:    *)
(*                    exactly 0 .. nx - 1, strictly increasing); every      *)
(*                    outstanding offer id was handed out (OfferIdsBelow)   *)
(*   Linked, Distinct every held bundle's item is custody (or already gone  *)
(*                    before the next sync); a bundle is held once          *)
(* The Lean counterpart is proofs/lean/Vinc/DtnCustody*.lean.               *)
(***************************************************************************)
EXTENDS DtnCustodyOps

CONSTANTS N, R, Budget, Bundles, HostKeys, Nodes, ByteVals, ExpVals, NowVals, MaxSeq, MaxNx

VARIABLES B, L, nx, handed
vars == <<B, L, nx, handed>>

\* the offer ids an ack may name: every id up to the counter bound, handed out or not
OffVals == 0..MaxNx

Classes == {"custody", "transit"}
\* host keys: a mailbox item, a bundle item the book never holds, and bundle 2 (also acceptable through the book)
HostKeysDef == {<<2, 1>>, <<1, 2>>, <<1, 3>>}

Held(key) == \E i \in RIdx(B) : key = BKey(B[i].bundle)

Init == B = [i \in 1..R |-> BNone] /\ L = New(Budget, N) /\ nx = 0 /\ handed = {}

LiveKept(pre, post, now, key) ==
    \A e \in Ents(pre) : (e.cls = "custody" /\ e.exp > now /\ e.key # key) => e \in Ents(post)

AcceptStep == \E b \in Bundles, bytes \in ByteVals, exp \in ExpVals, prev \in Nodes, o \in OffVals, now \in NowVals :
    LET r == Accept(B, L, b, bytes, exp, prev, o, now)
        x == Expire(L, now)
        B1 == Sync(B, x.L)
        key == BKey(b)
        sl == SlotOf(B1, b)
    IN /\ Assert(LiveKept(L, r.L, now, <<0, 0>>), "accept evicted live custody")
       /\ Assert((r.err # "ok") => (r.L = WithoutExpired(L, now) /\ r.B = Sync(B, WithoutExpired(L, now)) /\ r.ev = ExpiredSeq(L, now)),
                 "a refused accept moved something")
       /\ Assert((r.err = "capacity") = (~Holds(B1, b) /\ \A i \in 1..R : B1[i].full), "capacity is not exactly a full book")
       /\ Assert((r.err = "ok") => (Holds(r.B, b) /\ \E e \in Ents(r.L) : e.key = key /\ e.cls = "custody"),
                 "an accepted bundle is not held in custody")
       \* a held item is promoted without new room
       /\ Assert((r.err = "ok" /\ ~Holds(B1, b) /\ Contains(x.L, key)) => r.L.used = x.L.used, "promotion needed room")
       \* the answer owed is the incoming previous node and offer id, never the record's
       /\ Assert((r.err = "ok") => (r.prev = prev /\ r.offer = o), "the answer owed is not the incoming one")
       \* an incoming bundle already expired, not kept and with a free record, is refused as expired
       /\ Assert((~Holds(B1, b) /\ FirstEmpty(B1) # 0 /\ ~Contains(x.L, key) /\ exp <= now) => r.err = "expired",
                 "an expired incoming bundle was not refused")
       \* a hand-back (the bundle is already held) keeps the record and its previous node and cancels the offer
       /\ Assert(Holds(B1, b) =>
                    /\ r.err = "ok" /\ r.L = x.L /\ r.ev = x.ev
                    /\ r.B[sl].bundle = b /\ r.B[sl].prev = B1[sl].prev /\ r.B[sl].off = 0 /\ r.B[sl].oid = 0
                    /\ \A j \in RIdx(B1) : j # sl => r.B[j] = B1[j],
                 "a hand-back did not cancel the offer or changed more than it")
       /\ B' = r.B /\ L' = r.L /\ UNCHANGED <<nx, handed>>

OfferStep == \E b \in Bundles, to \in Nodes :
    LET r == Offer(B, nx, b, to)
        i == SlotOf(B, b)
    IN /\ Assert((r.err = "ok") = Holds(B, b), "offer ok exactly for a held bundle")
       \* the counter is handed out and incremented; a failed offer leaves it
       /\ Assert((r.err = "ok") => (r.id = nx /\ r.nx = nx + 1 /\ r.id \notin handed), "an offer did not hand out a fresh counter value")
       /\ Assert((r.err # "ok") => (r.nx = nx /\ r.B = B), "a failed offer changed the book")
       \* a new offer replaces the outstanding one
       /\ Assert((r.err = "ok") => (r.B[i].off = to /\ r.B[i].oid = r.id /\ r.B[i].prev = B[i].prev), "the offer is not recorded")
       /\ B' = r.B /\ nx' = r.nx /\ handed' = (IF r.err = "ok" THEN handed \cup {r.id} ELSE handed) /\ UNCHANGED L

AckStep == \E b \in Bundles, c \in Nodes, o \in OffVals, v \in BOOLEAN :
    LET r == OnAck(B, L, b, c, o, v)
        i == SlotOf(B, b)
        offered == Holds(B, b) /\ B[i].off = c /\ B[i].oid = o
        relief == v /\ offered /\ Contains(L, BKey(b))
    IN /\ Assert((r.err = "ok") = relief, "relief is not exactly valid, held, offered to this node under this id, in the ledger")
       /\ Assert((r.err \notin {"ok", "storeunknown"}) => (r.B = B /\ r.L = L), "a refused ack moved something")
       \* a stale ack never relieves and changes nothing
       /\ Assert((v /\ Holds(B, b) /\ ~offered) => (r.err = "notoffered" /\ r.B = B /\ r.L = L), "a stale ack moved something")
       /\ Assert((r.err = "storeunknown") => (v /\ offered /\ ~Contains(L, BKey(b)) /\ r.L = L /\ ~Holds(r.B, b)),
                 "storeunknown is not the offered ack of a dropped item")
       /\ Assert(relief =>
                    /\ ~Holds(r.B, b)
                    /\ \A e \in Ents(L) : e.key = BKey(b) => [e EXCEPT !.cls = "transit"] \in Ents(r.L)
                    /\ \A e \in Ents(L) : e.key # BKey(b) => e \in Ents(r.L)
                    /\ r.L.used = L.used,
                 "a relief changed more than the class of the item")
       /\ Assert(\A j \in RIdx(B) : B[j].bundle # b => (\E q \in RIdx(r.B) : r.B[q] = B[j]), "an ack cleared another record")
       /\ B' = r.B /\ L' = r.L /\ UNCHANGED <<nx, handed>>

DeliveredStep == \E b \in Bundles :
    LET r == Delivered(B, L, b) IN
    /\ Assert((r.err = "ok") = Holds(B, b), "delivered ok exactly for a held bundle")
    /\ Assert((r.err = "ok") => (~Holds(r.B, b) /\ ~Contains(r.L, BKey(b)) /\ LiveKept(L, r.L, 0, BKey(b)) /\ \A i \in RIdx(B) : B[i].bundle # b => Holds(r.B, B[i].bundle)),
              "delivery removed more than the bundle")
    /\ B' = r.B /\ L' = r.L /\ UNCHANGED <<nx, handed>>

BExpireStep == \E now \in NowVals :
    LET r == BExpire(B, L, now) IN
    /\ Assert(r.ev = ExpiredSeq(L, now) /\ r.L = WithoutExpired(L, now), "book expiry removed more than the expired items")
    /\ Assert(\A i \in RIdx(r.B) : Contains(r.L, BKey(r.B[i].bundle)), "a record survived the loss of its item")
    /\ Assert(LiveKept(L, r.L, now, <<0, 0>>), "book expiry evicted live custody")
    /\ B' = r.B /\ L' = r.L /\ UNCHANGED <<nx, handed>>

HostAdmitStep == \E key \in HostKeys, bytes \in ByteVals, cls \in Classes, exp \in ExpVals, now \in NowVals :
    /\ ~Held(key)
    /\ LET r == Admit(L, key, bytes, cls, exp, now) IN
       /\ Assert(LiveKept(L, r.L, now, <<0, 0>>), "a host admission evicted live custody")
       /\ L' = r.L /\ UNCHANGED <<B, nx, handed>>

HostExpireStep == \E now \in NowVals :
    /\ Assert(LiveKept(L, Expire(L, now).L, now, <<0, 0>>), "a host expiry removed live custody")
    /\ L' = Expire(L, now).L /\ UNCHANGED <<B, nx, handed>>

HostReleaseStep == \E key \in HostKeys :
    /\ ~Held(key)
    /\ L' = Release(L, key).L /\ UNCHANGED <<B, nx, handed>>

Next == AcceptStep \/ OfferStep \/ AckStep \/ DeliveredStep \/ BExpireStep \/ HostAdmitStep \/ HostExpireStep \/ HostReleaseStep

Spec == Init /\ [][Next]_vars

Bounded == L.seq <= MaxSeq /\ nx <= MaxNx

(* ---- invariants ---- *)

LedgerInv ==
    /\ Len(L.slots) = N
    /\ L.used = Total(L)
    /\ L.used <= L.budget
    /\ \A i, j \in Occ(L.slots) : i # j => L.slots[i].key # L.slots[j].key /\ L.slots[i].seq # L.slots[j].seq
    /\ \A i \in Occ(L.slots) : L.slots[i].seq < L.seq

Distinct == \A i, j \in RIdx(B) : i # j => B[i].bundle # B[j].bundle

\* every ledger item of a held bundle is custody
Linked == \A i \in RIdx(B), e \in Ents(L) : e.key = BKey(B[i].bundle) => e.cls = "custody"

\* the offered node of a record is a node or none, and a record without an offer carries no id
OfferedOk == \A i \in RIdx(B) : B[i].off \in Nodes \cup {0} /\ (B[i].off = 0 => B[i].oid = 0)

\* every outstanding offer id was handed out (is below the counter)
OfferIdsBelow == \A i \in RIdx(B) : B[i].off # 0 => B[i].oid < nx

\* the ids handed out so far are exactly 0 .. nx - 1: pairwise distinct, from a strictly increasing counter
HandedExact == handed = 0..(nx - 1)

\* the only way custody turns to transit is relief: no state has a record and the item class changed
\* behind its back (Linked), and a relief clears the record (AckStep)
=============================================================================
