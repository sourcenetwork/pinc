------------------------------ MODULE DtnCustody ------------------------------
(***************************************************************************)
(* Model check of custody, vinc-dtn/src/custody.rs: the book and the shared *)
(* ledger under every sequence of calls (DtnCustodyOps.tla, the same        *)
(* definitions the trace check uses). The environment calls accept, offer,  *)
(* on_ack (a valid or an invalid ack, from any node), delivered and the     *)
(* book's expire, and the host calls the ledger directly: admit of a key the*)
(* book holds no record of (transit bundles, mailbox items), expire, and    *)
(* release of a key the book holds no record of. The clock of every call is *)
(* an input and may go back.                                                *)
(*                                                                          *)
(* Properties (asserted on every step, plus invariants):                    *)
(*   CustodyExit      a custody item that has not expired leaves the ledger *)
(*                    or stops being custody only through delivered, a      *)
(*                    release of its key, or an ack of its bundle           *)
(*   ReliefOnlyByAck  the item becomes transit and the record clears exactly*)
(*                    when the ack is valid, the bundle is held, custody was*)
(*                    offered to exactly the acknowledging node and the     *)
(*                    ledger holds the item; every other ack moves nothing  *)
(*                    (a valid, offered ack for an item the ledger already  *)
(*                    dropped clears the record: storeunknown)              *)
(*   CustodyToTransit only an ack relieves                                  *)
(*   AcceptRefused    a refused accept changes nothing but the expired items*)
(*                    and their records; capacity exactly when no record is *)
(*                    free                                                  *)
(*   AcceptOk         the bundle is held and its item is custody            *)
(*   Promote          a held item is promoted without new room              *)
(*   Linked, Distinct every held bundle's item is custody (or already gone  *)
(*                    before the next sync); a bundle is held once          *)
(* The Lean counterpart is proofs/lean/Vinc/DtnCustody*.lean.               *)
(***************************************************************************)
EXTENDS DtnCustodyOps

CONSTANTS N, R, Budget, Bundles, HostKeys, Nodes, ByteVals, ExpVals, NowVals, MaxSeq

VARIABLES B, L
vars == <<B, L>>

Classes == {"custody", "transit"}
\* host keys: a mailbox item, a bundle item the book never holds, and bundle 2 (also acceptable through the book)
HostKeysDef == {<<2, 1>>, <<1, 2>>, <<1, 3>>}

Held(key) == \E i \in RIdx(B) : key = BKey(B[i].bundle)

Init == B = [i \in 1..R |-> BNone] /\ L = New(Budget, N)

LiveKept(pre, post, now, key) ==
    \A e \in Ents(pre) : (e.cls = "custody" /\ e.exp > now /\ e.key # key) => e \in Ents(post)

AcceptStep == \E b \in Bundles, bytes \in ByteVals, exp \in ExpVals, prev \in Nodes, now \in NowVals :
    LET r == Accept(B, L, b, bytes, exp, prev, now)
        x == Expire(L, now)
        B1 == Sync(B, x.L)
        key == BKey(b)
    IN /\ Assert(LiveKept(L, r.L, now, <<0, 0>>), "accept evicted live custody")
       /\ Assert((r.err # "ok") => (r.L = WithoutExpired(L, now) /\ r.B = Sync(B, WithoutExpired(L, now)) /\ r.ev = ExpiredSeq(L, now)),
                 "a refused accept moved something")
       /\ Assert((r.err = "capacity") = (~Holds(B1, b) /\ \A i \in 1..R : B1[i].full), "capacity is not exactly a full book")
       /\ Assert((r.err = "ok") => (Holds(r.B, b) /\ \E e \in Ents(r.L) : e.key = key /\ e.cls = "custody"),
                 "an accepted bundle is not held in custody")
       \* a held item is promoted without new room
       /\ Assert((r.err = "ok" /\ ~Holds(B1, b) /\ Contains(x.L, key)) => r.L.used = x.L.used, "promotion needed room")
       /\ B' = r.B /\ L' = r.L

OfferStep == \E b \in Bundles, to \in Nodes :
    LET r == Offer(B, b, to) IN
    /\ Assert((r.err = "ok") = Holds(B, b), "offer ok exactly for a held bundle")
    /\ B' = r.B /\ UNCHANGED L

AckStep == \E b \in Bundles, c \in Nodes, v \in BOOLEAN :
    LET r == OnAck(B, L, b, c, v)
        i == SlotOf(B, b)
        offered == Holds(B, b) /\ B[i].off = c
        relief == v /\ offered /\ Contains(L, BKey(b))
    IN /\ Assert((r.err = "ok") = relief, "relief is not exactly valid, held, offered to this node, in the ledger")
       /\ Assert((r.err \notin {"ok", "storeunknown"}) => (r.B = B /\ r.L = L), "a refused ack moved something")
       /\ Assert((r.err = "storeunknown") => (v /\ offered /\ ~Contains(L, BKey(b)) /\ r.L = L /\ ~Holds(r.B, b)),
                 "storeunknown is not the offered ack of a dropped item")
       /\ Assert(relief =>
                    /\ ~Holds(r.B, b)
                    /\ \A e \in Ents(L) : e.key = BKey(b) => [e EXCEPT !.cls = "transit"] \in Ents(r.L)
                    /\ \A e \in Ents(L) : e.key # BKey(b) => e \in Ents(r.L)
                    /\ r.L.used = L.used,
                 "a relief changed more than the class of the item")
       /\ Assert(\A j \in RIdx(B) : B[j].bundle # b => (\E q \in RIdx(r.B) : r.B[q] = B[j]), "an ack cleared another record")
       /\ B' = r.B /\ L' = r.L

DeliveredStep == \E b \in Bundles :
    LET r == Delivered(B, L, b) IN
    /\ Assert((r.err = "ok") = Holds(B, b), "delivered ok exactly for a held bundle")
    /\ Assert((r.err = "ok") => (~Holds(r.B, b) /\ ~Contains(r.L, BKey(b)) /\ LiveKept(L, r.L, 0, BKey(b)) /\ \A i \in RIdx(B) : B[i].bundle # b => Holds(r.B, B[i].bundle)),
              "delivery removed more than the bundle")
    /\ B' = r.B /\ L' = r.L

BExpireStep == \E now \in NowVals :
    LET r == BExpire(B, L, now) IN
    /\ Assert(r.ev = ExpiredSeq(L, now) /\ r.L = WithoutExpired(L, now), "book expiry removed more than the expired items")
    /\ Assert(\A i \in RIdx(r.B) : Contains(r.L, BKey(r.B[i].bundle)), "a record survived the loss of its item")
    /\ Assert(LiveKept(L, r.L, now, <<0, 0>>), "book expiry evicted live custody")
    /\ B' = r.B /\ L' = r.L

HostAdmitStep == \E key \in HostKeys, bytes \in ByteVals, cls \in Classes, exp \in ExpVals, now \in NowVals :
    /\ ~Held(key)
    /\ LET r == Admit(L, key, bytes, cls, exp, now) IN
       /\ Assert(LiveKept(L, r.L, now, <<0, 0>>), "a host admission evicted live custody")
       /\ L' = r.L /\ UNCHANGED B

HostExpireStep == \E now \in NowVals :
    /\ Assert(LiveKept(L, Expire(L, now).L, now, <<0, 0>>), "a host expiry removed live custody")
    /\ L' = Expire(L, now).L /\ UNCHANGED B

HostReleaseStep == \E key \in HostKeys :
    /\ ~Held(key)
    /\ L' = Release(L, key).L /\ UNCHANGED B

Next == AcceptStep \/ OfferStep \/ AckStep \/ DeliveredStep \/ BExpireStep \/ HostAdmitStep \/ HostExpireStep \/ HostReleaseStep

Spec == Init /\ [][Next]_vars

Bounded == L.seq <= MaxSeq

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

\* the offered node of a record is a node or none
OfferedOk == \A i \in RIdx(B) : B[i].off \in Nodes \cup {0}

\* the only way custody turns to transit is relief: no state has a record and the item class changed
\* behind its back (Linked), and a relief clears the record (AckStep)
=============================================================================
