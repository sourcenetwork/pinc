----------------------------- MODULE TraceLedger -----------------------------
(***************************************************************************)
(* Trace validation of the amplification ledger: pinc-core ledger.rs.      *)
(*                                                                         *)
(* The Rust test tests/trace_ledger.rs drives real Ledgers (the public     *)
(* API, no probe) with seeded calls and records one event per call in      *)
(* ledger.ndjson: "new" starts a fresh ledger; "rx", "open" and "tx" are   *)
(* on_receive, open and allow_send with the address (a small number the    *)
(* test maps to a socket address), the size as four 16-bit limbs, the      *)
(* answer, the table's length after the call, the entry of the address     *)
(* after it and the entry of a second address q the test picks (one it     *)
(* used before, evicted or not). Every call must be the step of            *)
(* LedgerOps.tla at the code's sizes: 1024 entries, the counters as the    *)
(* 80-bit words of U64.tla saturating at u64::MAX, the overhead 28.        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds ledger.ndjson.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

CONSTANT CAP

VARIABLES i, t
vars == <<i, t>>

U == INSTANCE U64
Times3(a) == U!Add(a, U!Shl(a, 1))
L == INSTANCE LedgerOps WITH Zero <- U!Zero, Top <- U!Max64, Plus <- U!Add, Leq <- U!Le, Times3 <- Times3,
                             OVH <- U!W(28), CAP <- CAP

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/ledger.ndjson")
Ev0 == Trace[i]

(* the recorded entry v of address x is the one in table tb *)
Same(tb, x, v) ==
    LET k == L!Find(tb, x)
    IN IF k = 0 THEN ~v.has
       ELSE /\ v.has
            /\ tb[k].ent.rx = U!FromLimbs(v.rx)
            /\ tb[k].ent.tx = U!FromLimbs(v.tx)
            /\ tb[k].ent.valid = v.valid

After(ev) ==
    LET n == U!FromLimbs(ev.n)
    IN IF ev.op = "new" THEN [tab |-> <<>>, res |-> FALSE]
       ELSE IF ev.op = "rx" THEN LET r == L!OnReceive(t, ev.a, n) IN [tab |-> r.tab, res |-> r.held]
       ELSE IF ev.op = "open" THEN [tab |-> L!Open(t, ev.a), res |-> FALSE]
       ELSE LET r == L!AllowSend(t, ev.a, n) IN [tab |-> r.tab, res |-> r.ok]

Init == i = 1 /\ t = <<>>
Step == /\ i <= Len(Trace)
        /\ Ev0.t = "ledger"
        /\ Ev0.op \in {"new", "rx", "open", "tx"}
        /\ LET r == After(Ev0)
           IN /\ t' = r.tab
              /\ Ev0.res = r.res
              /\ Ev0.len = Len(r.tab)
              /\ Ev0.op = "new" \/ (Same(r.tab, Ev0.a, Ev0.e) /\ Same(r.tab, Ev0.q, Ev0.qe))
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

(* the table never holds more than CAP entries, and a held address got at most three times what it sent *)
Inv == /\ Len(t) <= CAP
       /\ \A k \in 1..Len(t) : ~t[k].ent.valid => U!Le(t[k].ent.tx, Times3(t[k].ent.rx))
=============================================================================
