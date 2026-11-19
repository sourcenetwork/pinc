---------------------------- MODULE DtnCustodyOps ----------------------------
(***************************************************************************)
(* The operations of pinc-dtn/src/custody.rs (CustodyBook<N>) on the shared *)
(* ledger of DtnStoreOps.tla, step for step. The book is a sequence of      *)
(* records [bundle, prev, off, oid] or BNone: off is the node custody was   *)
(* offered to (0 for none), oid the id of that offer (0 when none: the     *)
(* code's Option<{to, id}> is the pair (off, oid)); a bundle is the ledger  *)
(* key <<1, bundle>>; nodes are numbers (equal bytes, equal number).        *)
(*                                                                          *)
(* The book also has a counter next_offer. It is the separate value nx that *)
(* the callers carry: Offer takes it and returns the new one, no other      *)
(* operation reads or changes it (the code's u64 counter saturates at       *)
(* 2^64 - 1, which 2^64 offers cannot reach; here it counts in the          *)
(* naturals). A book is therefore the pair (sequence, nx).                  *)
(*                                                                          *)
(*  Sync       the records of items the ledger no longer holds are dropped  *)
(*  Accept(B, L, b, bytes, exp, prev, offer, now)                           *)
(*             expire; sync; held -> ok: the record stays (its prev too) and*)
(*             the outstanding offer is cancelled (off, oid := 0); no free  *)
(*             record -> capacity; a kept item (transit) is promoted to     *)
(*             custody without new room; otherwise admit as custody, whose  *)
(*             error is the ledger's ("custody", "full", "dup", "expired":  *)
(*             an incoming bundle already expired is "expired"); sync; the  *)
(*             first free record. The answer owed (the AckDue) is the result*)
(*             fields prev and offer: ALWAYS the previous node and offer id *)
(*             of the INCOMING offer, not the record's (pinned behaviour)   *)
(*  Offer(B, nx, b, to)                                                     *)
(*             [err, B, nx, id]: the offer gets the id nx, the counter      *)
(*             becomes nx + 1, the record's outstanding offer is replaced by*)
(*             (to, nx); "unknown" for a bundle not held (nx unchanged)     *)
(*  OnAck(B, L, b, custodian, offer, valid)                                 *)
(*             the ack's signature check is the boolean `valid` (the        *)
(*             signature scheme is assumed, not modelled); relief needs the *)
(*             record's off to be the custodian AND its oid to be the ack's *)
(*             offer, else "notoffered" and nothing changes; relief clears  *)
(*             the record and reclasses the item to transit; if the ledger  *)
(*             no longer holds the item the record is dropped and the error *)
(*             is "storeunknown" (the store's Unknown: pinned behaviour)    *)
(*  Delivered  clear the record, release the item                           *)
(*  BExpire    expire, then sync                                            *)
(*                                                                          *)
(* The Lean counterpart is proofs/lean/Pinc/DtnCustody*.lean.               *)
(***************************************************************************)
EXTENDS DtnStoreOps

BNone == [full |-> FALSE]
Rec(b, prev, off, oid) == [full |-> TRUE, bundle |-> b, prev |-> prev, off |-> off, oid |-> oid]
BKey(b) == <<1, b>>

RIdx(B) == {i \in 1..Len(B) : B[i].full}
Holds(B, b) == \E i \in RIdx(B) : B[i].bundle = b
Recs(B) == {B[i] : i \in RIdx(B)}

Sync(B, L) == [i \in 1..Len(B) |-> IF B[i].full /\ ~Contains(L, BKey(B[i].bundle)) THEN BNone ELSE B[i]]

SlotOf(B, b) ==
    IF Holds(B, b) THEN CHOOSE i \in RIdx(B) : B[i].bundle = b /\ \A j \in 1..(i - 1) : ~(B[j].full /\ B[j].bundle = b) ELSE 0
FirstEmpty(B) ==
    IF \E i \in 1..Len(B) : ~B[i].full THEN CHOOSE i \in 1..Len(B) : ~B[i].full /\ \A j \in 1..(i - 1) : B[j].full ELSE 0

\* the record of b loses its outstanding offer
Cancel(B, b) == LET i == SlotOf(B, b) IN [B EXCEPT ![i].off = 0, ![i].oid = 0]

\* accept: [err, B, L, ev, prev, offer], err one of "ok", "capacity", "custody", "full", "dup", "expired" (the
\* store's verdicts); prev and offer are the answer owed when err = "ok"
Accept(B, L, b, bytes, exp, prev, offer, now) ==
    LET x == Expire(L, now)
        B1 == Sync(B, x.L)
        slot == FirstEmpty(B1)
        key == BKey(b)
        rc == Reclass(x.L, key, "custody")
        ad == Admit(x.L, key, bytes, "custody", exp, now)
        new == Rec(b, prev, 0, 0)
    IN IF Holds(B1, b) THEN [err |-> "ok", B |-> Cancel(B1, b), L |-> x.L, ev |-> x.ev, prev |-> prev, offer |-> offer]
       ELSE IF slot = 0 THEN [err |-> "capacity", B |-> B1, L |-> x.L, ev |-> x.ev, prev |-> prev, offer |-> offer]
       ELSE IF Contains(x.L, key)
            THEN [err |-> "ok", B |-> [Sync(B1, rc.L) EXCEPT ![slot] = new], L |-> rc.L, ev |-> x.ev, prev |-> prev, offer |-> offer]
       ELSE IF ad.err # "ok" THEN [err |-> ad.err, B |-> B1, L |-> ad.L, ev |-> x.ev \o ad.ev, prev |-> prev, offer |-> offer]
       ELSE [err |-> "ok", B |-> [Sync(B1, ad.L) EXCEPT ![slot] = new], L |-> ad.L, ev |-> x.ev \o ad.ev, prev |-> prev, offer |-> offer]

\* offer: [err, B, nx, id], err "ok" or "unknown"
Offer(B, nx, b, to) ==
    IF Holds(B, b) THEN [err |-> "ok", B |-> [B EXCEPT ![SlotOf(B, b)].off = to, ![SlotOf(B, b)].oid = nx], nx |-> nx + 1, id |-> nx]
    ELSE [err |-> "unknown", B |-> B, nx |-> nx, id |-> 0]

\* the record offers custody to the node under the offer id
OfferedTo(r, node, id) == r.off # 0 /\ r.off = node /\ r.oid = id

\* on_ack: [err, B, L], err one of "ok", "ack", "unknown", "notoffered", "storeunknown"
OnAck(B, L, b, custodian, offer, valid) ==
    LET i == SlotOf(B, b)
        rc == Reclass(L, BKey(b), "transit")
    IN IF ~valid THEN [err |-> "ack", B |-> B, L |-> L]
       ELSE IF i = 0 THEN [err |-> "unknown", B |-> B, L |-> L]
       ELSE IF ~OfferedTo(B[i], custodian, offer) THEN [err |-> "notoffered", B |-> B, L |-> L]
       ELSE [err |-> IF rc.ok THEN "ok" ELSE "storeunknown", B |-> [B EXCEPT ![i] = BNone], L |-> rc.L]

\* delivered: [err, B, L], err "ok" or "unknown"
Delivered(B, L, b) ==
    LET i == SlotOf(B, b) IN
    IF i = 0 THEN [err |-> "unknown", B |-> B, L |-> L]
    ELSE [err |-> "ok", B |-> [B EXCEPT ![i] = BNone], L |-> Release(L, BKey(b)).L]

BExpire(B, L, now) == LET x == Expire(L, now) IN [B |-> Sync(B, x.L), L |-> x.L, ev |-> x.ev]
=============================================================================
