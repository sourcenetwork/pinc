-------------------------------- MODULE Ledger --------------------------------
(***************************************************************************)
(* The amplification ledger of pinc-core ledger.rs (Ledger) over every     *)
(* sequence of on_receive, open and allow_send calls on NA addresses, with *)
(* a table of CAP entries (LEDGER_ENTRIES, 1024 in the code), counters     *)
(* that saturate at U (u64::MAX in the code, small here so that TLC        *)
(* reaches it) and an overhead OVH (DATAGRAM_OVERHEAD, 28 in the code).   *)
(* FACTOR is 3, as in the code. LedgerOps.tla has the operators.           *)
(*                                                                         *)
(* The state is the table alone; what a call does is checked in every      *)
(* state for every call that could come next (every address, every size   *)
(* of NS), so no history variable multiplies the states.                   *)
(*                                                                         *)
(* Checked, in every state reached:                                        *)
(*  - TypeOK, Bounded, Distinct: at most CAP entries, each address once;   *)
(*  - AmpBound: for an address that is not validated the bytes charged     *)
(*    never exceed three times the bytes received (module invariant);      *)
(*  - SendExact: allow_send charges exactly when the address is not held,  *)
(*    or is validated, or tx + min(n + OVH, U) <= 3 * rx; a held datagram  *)
(*    changes nothing; a charge adds min(n + OVH, U) to tx, saturating;    *)
(*    an address not in the table counts as one we wrote to first, so its *)
(*    new entry is validated (the eviction trade of the module doc);       *)
(*  - OpenExact: open validates the address and keeps its counters, and an *)
(*    address not held gets a validated entry with nothing counted;        *)
(*  - ReceiveExact: on_receive adds n to rx, saturating; a first datagram  *)
(*    leaves the address held; a later one validates it if we sent to it   *)
(*    meanwhile (it answered); the answer is whether it is still held;     *)
(* and in every step:                                                      *)
(*  - TableStep: the order of the table is kept, or one address it did not *)
(*    hold is appended and, when CAP were held, the first inserted goes;   *)
(*    at most one held entry changes;                                      *)
(*  - Monotone: an entry held before and after does not lose bytes and     *)
(*    stays validated.                                                     *)
(* Ledger.cfg: 3 addresses, 2 entries, U = 3 (the factor overtakes the     *)
(* saturation); Ledger_sat.cfg: 2 addresses, 1 entry, U = 30, sizes up to  *)
(* U so that the charge and both counters saturate.                        *)
(* Witnesses: Ledger_w_evict (a full table meets an address it does not    *)
(* hold), Ledger_w_held (an address we sent to is still held and a         *)
(* datagram to it is refused), Ledger_w_sat (a counter saturates).         *)
(* TraceLedger.tla checks the real Ledger against LedgerOps.tla.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NA, CAP, U, OVH, NS

ASSUME CAP >= 1 /\ NS \subseteq 0..U /\ OVH \in 0..U

VARIABLE t

IPlus(a, c) == a + c
ILeq(a, c) == a <= c
ITimes3(a) == 3 * a

L == INSTANCE LedgerOps WITH Zero <- 0, Top <- U, Plus <- IPlus, Leq <- ILeq, Times3 <- ITimes3, OVH <- OVH,
                             CAP <- CAP

Addr == 1..NA
Min(a, c) == IF a <= c THEN a ELSE c

Init == t = <<>>

Receive == \E x \in Addr, n \in NS : t' = L!OnReceive(t, x, n).tab
Dial == \E x \in Addr : t' = L!Open(t, x)
Send == \E x \in Addr, n \in NS : t' = L!AllowSend(t, x, n).tab

Next == Receive \/ Dial \/ Send
Spec == Init /\ [][Next]_t

(* the entry of x in table tb, as a sequence of zero or one entry *)
Entry(tb, x) == LET k == L!Find(tb, x) IN IF k = 0 THEN <<>> ELSE <<tb[k].ent>>

TypeOK == t \in Seq([addr : Addr, ent : [rx : 0..U, tx : 0..U, valid : BOOLEAN]])
Bounded == Len(t) <= CAP
Distinct == \A j, k \in 1..Len(t) : t[j].addr = t[k].addr => j = k

AmpBound == \A k \in 1..Len(t) : ~t[k].ent.valid => t[k].ent.tx <= 3 * t[k].ent.rx

SendExact ==
    \A x \in Addr, n \in NS :
        LET r == L!AllowSend(t, x, n)
            e == Entry(t, x)
            e2 == Entry(r.tab, x)
            c == Min(n + OVH, U)
        IN /\ r.ok = (e = <<>> \/ e[1].valid \/ e[1].tx + c <= 3 * e[1].rx)
           /\ ~r.ok => r.tab = t
           /\ r.ok => /\ e2 # <<>>
                      /\ e2[1].tx = (IF e = <<>> THEN c ELSE Min(e[1].tx + c, U))
                      /\ e2[1].rx = (IF e = <<>> THEN 0 ELSE e[1].rx)
                      /\ e2[1].valid = (e = <<>> \/ e[1].valid)

OpenExact ==
    \A x \in Addr :
        LET e == Entry(t, x)
            e2 == Entry(L!Open(t, x), x)
        IN /\ e2 # <<>>
           /\ e2[1].valid
           /\ e2[1].rx = (IF e = <<>> THEN 0 ELSE e[1].rx)
           /\ e2[1].tx = (IF e = <<>> THEN 0 ELSE e[1].tx)

ReceiveExact ==
    \A x \in Addr, n \in NS :
        LET r == L!OnReceive(t, x, n)
            e == Entry(t, x)
            e2 == Entry(r.tab, x)
        IN /\ e2 # <<>>
           /\ e2[1].rx = (IF e = <<>> THEN n ELSE Min(e[1].rx + n, U))
           /\ e2[1].tx = (IF e = <<>> THEN 0 ELSE e[1].tx)
           /\ e2[1].valid = (e # <<>> /\ (e[1].valid \/ e[1].tx > 0))
           /\ r.held = ~e2[1].valid

Order(tb) == [k \in 1..Len(tb) |-> tb[k].addr]
Held(tb) == {tb[k].addr : k \in 1..Len(tb)}

TableStep ==
    [][/\ \/ Order(t') = Order(t)
          \/ \E x \in Addr \ Held(t) :
                Order(t') = (IF Len(t) = CAP THEN Tail(Order(t)) ELSE Order(t)) \o <<x>>
       /\ Cardinality({x \in Held(t) \cap Held(t') : Entry(t, x) # Entry(t', x)}) <= 1]_t

Monotone ==
    [][\A x \in Held(t) \cap Held(t') :
          LET e == Entry(t, x)[1]
              e2 == Entry(t', x)[1]
          IN e2.rx >= e.rx /\ e2.tx >= e.tx /\ (e.valid => e2.valid)]_t

(* reachability witnesses *)
NoEvictReady == ~(Len(t) = CAP /\ Addr \ Held(t) # {})
NotHeldAfterSending ==
    ~\E k \in 1..Len(t) :
        /\ ~t[k].ent.valid
        /\ t[k].ent.tx > 0
        /\ \E n \in NS : ~L!AllowSend(t, t[k].addr, n).ok
NotSaturated == \A k \in 1..Len(t) : t[k].ent.rx < U /\ t[k].ent.tx < U
=============================================================================
