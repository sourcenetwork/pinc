---------------------------- MODULE DtnCustodyOps ----------------------------
(***************************************************************************)
(* The operations of vinc-dtn/src/custody.rs (CustodyBook<N>) on the shared *)
(* ledger of DtnStoreOps.tla, step for step. The book is a sequence of      *)
(* records [bundle, prev, off] (off = the node custody was offered to, 0    *)
(* for none) or BNone; a bundle is the ledger key <<1, bundle>>; nodes are  *)
(* numbers (equal bytes, equal number).                                     *)
(*                                                                          *)
(*  Sync       the records of items the ledger no longer holds are dropped  *)
(*  Accept     expire; sync; held -> ok; no free record -> capacity; a held *)
(*             item (transit) is promoted to custody without new room;      *)
(*             otherwise admit as custody; sync; the first free record      *)
(*  Offer      set the node custody was offered to, on the first record     *)
(*  OnAck      the ack's signature check is the boolean `valid` (the        *)
(*             signature scheme is assumed, not modelled); relief clears the*)
(*             record and reclasses the item to transit                     *)
(*  Delivered  clear the record, release the item                           *)
(*  BExpire    expire, then sync                                            *)
(*                                                                          *)
(* The Lean counterpart is proofs/lean/Vinc/DtnCustody*.lean.               *)
(***************************************************************************)
EXTENDS DtnStoreOps

BNone == [full |-> FALSE]
Rec(b, prev, off) == [full |-> TRUE, bundle |-> b, prev |-> prev, off |-> off]
BKey(b) == <<1, b>>

RIdx(B) == {i \in 1..Len(B) : B[i].full}
Holds(B, b) == \E i \in RIdx(B) : B[i].bundle = b
Recs(B) == {B[i] : i \in RIdx(B)}

Sync(B, L) == [i \in 1..Len(B) |-> IF B[i].full /\ ~Contains(L, BKey(B[i].bundle)) THEN BNone ELSE B[i]]

SlotOf(B, b) ==
    IF Holds(B, b) THEN CHOOSE i \in RIdx(B) : B[i].bundle = b /\ \A j \in 1..(i - 1) : ~(B[j].full /\ B[j].bundle = b) ELSE 0
FirstEmpty(B) ==
    IF \E i \in 1..Len(B) : ~B[i].full THEN CHOOSE i \in 1..Len(B) : ~B[i].full /\ \A j \in 1..(i - 1) : B[j].full ELSE 0

\* accept: [err, B, L, ev], err one of "ok", "capacity", "custody" (the store refused custody), "full"
Accept(B, L, b, bytes, exp, prev, now) ==
    LET x == Expire(L, now)
        B1 == Sync(B, x.L)
        slot == FirstEmpty(B1)
        key == BKey(b)
        rc == Reclass(x.L, key, "custody")
        ad == Admit(x.L, key, bytes, "custody", exp, now)
        new == Rec(b, prev, 0)
    IN IF Holds(B1, b) THEN [err |-> "ok", B |-> B1, L |-> x.L, ev |-> x.ev]
       ELSE IF slot = 0 THEN [err |-> "capacity", B |-> B1, L |-> x.L, ev |-> x.ev]
       ELSE IF Contains(x.L, key)
            THEN [err |-> "ok", B |-> [Sync(B1, rc.L) EXCEPT ![slot] = new], L |-> rc.L, ev |-> x.ev]
       ELSE IF ad.err # "ok" THEN [err |-> ad.err, B |-> B1, L |-> ad.L, ev |-> x.ev \o ad.ev]
       ELSE [err |-> "ok", B |-> [Sync(B1, ad.L) EXCEPT ![slot] = new], L |-> ad.L, ev |-> x.ev \o ad.ev]

\* offer: [err, B], err "ok" or "unknown"
Offer(B, b, to) ==
    IF Holds(B, b) THEN [err |-> "ok", B |-> [B EXCEPT ![SlotOf(B, b)].off = to]] ELSE [err |-> "unknown", B |-> B]

\* on_ack: [err, B, L], err one of "ok", "ack", "unknown", "notoffered", "storeunknown"
OnAck(B, L, b, custodian, valid) ==
    LET i == SlotOf(B, b)
        rc == Reclass(L, BKey(b), "transit")
    IN IF ~valid THEN [err |-> "ack", B |-> B, L |-> L]
       ELSE IF i = 0 THEN [err |-> "unknown", B |-> B, L |-> L]
       ELSE IF B[i].off # custodian THEN [err |-> "notoffered", B |-> B, L |-> L]
       ELSE [err |-> IF rc.ok THEN "ok" ELSE "storeunknown", B |-> [B EXCEPT ![i] = BNone], L |-> rc.L]

\* delivered: [err, B, L], err "ok" or "unknown"
Delivered(B, L, b) ==
    LET i == SlotOf(B, b) IN
    IF i = 0 THEN [err |-> "unknown", B |-> B, L |-> L]
    ELSE [err |-> "ok", B |-> [B EXCEPT ![i] = BNone], L |-> Release(L, BKey(b)).L]

BExpire(B, L, now) == LET x == Expire(L, now) IN [B |-> Sync(B, x.L), L |-> x.L, ev |-> x.ev]
=============================================================================
