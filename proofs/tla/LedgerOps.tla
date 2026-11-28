------------------------------ MODULE LedgerOps ------------------------------
(***************************************************************************)
(* The operations of pinc-core ledger.rs (Ledger: on_receive, open,        *)
(* validate, allow_send) over an abstract number type, so that one         *)
(* definition serves the model check (Ledger.tla: TLC integers, a small    *)
(* saturation maximum)                                                     *)
(* and the trace check (TraceLedger.tla: the 80-bit words of U64.tla and   *)
(* the real u64::MAX).                                                     *)
(*                                                                         *)
(* An entry is the budget record of AmpOps.tla, [rx, tx, valid]; its       *)
(* SatAdd, Recv, Send and Validate are the saturating counters of the      *)
(* entry. The ledger's gate is CanSend of AmpOps with the overhead 0: the  *)
(* ledger adds the 28 header bytes to the size first (Charge, a            *)
(* saturating add) and then compares tx + charge with rx * 3 exactly (the  *)
(* code compares in 128 bits), which is not AmpOps' tx + n + 48.           *)
(*                                                                         *)
(* The table (pinc-core table.rs, Table::insert) is a sequence in          *)
(* insertion order of [addr, ent]: the ledger inserts only a key it did    *)
(* not find, appended at the end, and when CAP entries are held the first  *)
(* one, the oldest, is evicted; an update keeps the entry's place.         *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS Zero, Top, Plus(_, _), Leq(_, _), Times3(_), OVH, CAP

A == INSTANCE AmpOps WITH Zero <- Zero, Top <- Top, Ovh <- Zero, Plus <- Plus, Leq <- Leq, Times3 <- Times3

(* the index of address x in table tb, 0 when it is not there *)
Find(tb, x) == LET ks == {k \in 1..Len(tb) : tb[k].addr = x}
               IN IF ks = {} THEN 0 ELSE CHOOSE k \in ks : TRUE

(* Table::insert of a key not held: appended, the oldest evicted when full *)
Ins(tb, x, e) == IF Len(tb) >= CAP THEN Append(Tail(tb), [addr |-> x, ent |-> e])
                 ELSE Append(tb, [addr |-> x, ent |-> e])

Upd(tb, k, e) == [tb EXCEPT ![k] = [addr |-> tb[k].addr, ent |-> e]]

(* the bytes charged for a datagram of n bytes: n.saturating_add(DATAGRAM_OVERHEAD) *)
Charge(n) == A!SatAdd(n, OVH)

(* Ledger::on_receive(addr, n): the table after it and the answer (held: not validated). Receiving counts bytes *)
(* and never validates: a datagram proves nothing about its source address.                                   *)
OnReceive(tb, x, n) ==
    LET k == Find(tb, x)
    IN IF k = 0
       THEN [tab |-> Ins(tb, x, [rx |-> n, tx |-> Zero, valid |-> FALSE]), held |-> TRUE]
       ELSE LET e1 == A!Recv(tb[k].ent, n)
            IN [tab |-> Upd(tb, k, e1), held |-> ~e1.valid]

(* Ledger::validate(addr): the address proved that it receives what was sent to it (an authenticated packet on a *)
(* path the transport validated); an address not held is left alone.                                             *)
Validate(tb, x) ==
    LET k == Find(tb, x)
    IN IF k = 0 THEN tb ELSE Upd(tb, k, A!Validate(tb[k].ent))

(* Ledger::open(addr): the host dials the address *)
Open(tb, x) ==
    LET k == Find(tb, x)
    IN IF k = 0 THEN Ins(tb, x, [rx |-> Zero, tx |-> Zero, valid |-> TRUE])
       ELSE Upd(tb, k, A!Validate(tb[k].ent))

(* Ledger::allow_send(addr, n): the table after it and the answer (ok: charged, not ok: held, nothing changes). *)
(* fit: an entry not validated is charged only while tx + charge fits the counter; without it (the code before *)
(* the fix) tx saturates at Top, stops counting, and the gate then lets every later datagram through           *)
AllowSendBy(tb, x, n, fit) ==
    LET c == Charge(n)
        k == Find(tb, x)
    IN IF k = 0
       THEN [tab |-> Ins(tb, x, [rx |-> Zero, tx |-> c, valid |-> TRUE]), ok |-> TRUE]
       ELSE IF tb[k].ent.valid
       THEN [tab |-> Upd(tb, k, A!Send(tb[k].ent, c)), ok |-> TRUE]
       ELSE IF A!CanSend(FALSE, tb[k].ent.tx, tb[k].ent.rx, c) /\ (fit => Leq(Plus(tb[k].ent.tx, c), Top))
       THEN [tab |-> Upd(tb, k, A!Send(tb[k].ent, c)), ok |-> TRUE]
       ELSE [tab |-> tb, ok |-> FALSE]
(* the code: allow_send refuses a charge that would pass the counter's top (TraceLedger replays it) *)
AllowSend(tb, x, n) == AllowSendBy(tb, x, n, TRUE)
=============================================================================
