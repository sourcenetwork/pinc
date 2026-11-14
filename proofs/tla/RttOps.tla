------------------------------- MODULE RttOps -------------------------------
(***************************************************************************)
(* The operations of vinc-core rtt.rs (NodeRtt), step for step: what the   *)
(* endpoint remembers about round trips. Rtt.tla checks them over every    *)
(* interleaving at small sizes; TraceRtt.tla replays the recorded calls of *)
(* the real code. Times are u64 nanosecond words (five 16-bit limbs) of    *)
(* Nanos.tla, so that the saturating arithmetic of the code is exact.      *)
(*                                                                         *)
(* The state r: tab (the table of peer round trips, a sequence of          *)
(* <<peer, word>> in insertion order, oldest first), lrtt (the node        *)
(* average), tgr (the node peak) and floor (the handshake floor). cap is   *)
(* the size of the table (256 in the code). A peer is a natural number.    *)
(* The table (table.rs, insert_room) is a bounded insertion-ordered map:   *)
(* a known peer takes the new value and keeps its place; a new peer is     *)
(* appended while there is room and refused when the table is full; no     *)
(* entry is removed. An optional word is [some, v].                        *)
(***************************************************************************)
EXTENDS Integers, Sequences

N == INSTANCE Nanos
U == INSTANCE U64

Zero == N!Zero
Ms(n) == N!Millis(n)
SlowRtt == Ms(250)
FirstResend == Ms(500)
FloorMax == N!Sec(8)
HubResend == Ms(300)

None == [some |-> FALSE, v |-> Zero]
Some(v) == [some |-> TRUE, v |-> v]

\* a.saturating_mul(k) for a small constant k
SatMul(a, k) == LET p == N!MulAt(a, k, 1, 0) IN IF U!Fits(p) THEN p ELSE U!Max64
SatAdd(a, b) == N!SatAdd(a, b)

Rtt0 == [tab |-> <<>>, lrtt |-> Zero, tgr |-> Zero, floor |-> Zero]

Find(tab, p) == IF \E i \in 1..Len(tab) : tab[i][1] = p THEN CHOOSE i \in 1..Len(tab) : tab[i][1] = p ELSE 0
Krtt(r, p) == LET i == Find(r.tab, p) IN IF i = 0 THEN None ELSE Some(r.tab[i][2])

\* Table::insert_room
InsertRoom(tab, cap, p, v) ==
    LET i == Find(tab, p)
    IN IF i # 0 THEN [ok |-> TRUE, tab |-> [tab EXCEPT ![i] = <<p, v>>]]
       ELSE IF Len(tab) < cap THEN [ok |-> TRUE, tab |-> Append(tab, <<p, v>>)]
       ELSE [ok |-> FALSE, tab |-> tab]

\* note_handshake: zero is ignored; else the peer's entry (room permitting), the floor to zero, the average moves
Handshake(r, cap, p, v) ==
    IF v = Zero THEN r
    ELSE [tab |-> InsertRoom(r.tab, cap, p, v).tab,
          lrtt |-> IF r.lrtt = Zero THEN v ELSE N!Div(SatAdd(SatMul(r.lrtt, 7), v), 8),
          tgr |-> r.tgr, floor |-> Zero]

\* restore_peer: the table only; the answer says whether it was stored
Restore(r, cap, p, v) ==
    LET t == InsertRoom(r.tab, cap, p, v)
    IN [ok |-> t.ok, r |-> [r EXCEPT !.tab = t.tab]]

\* note_peak: tgr = peak.max(tgr - (tgr >> 5))
Peak(r, pk) == [r EXCEPT !.tgr = N!Max(pk, N!Sub(r.tgr, N!Div(r.tgr, 32)))]

\* note_timeout: floor = FLOOR_MAX.min(FIRST_RESEND.max(floor.saturating_mul(2)))
TimeoutWith(r, fm) == [r EXCEPT !.floor = N!Min(fm, N!Max(FirstResend, SatMul(r.floor, 2)))]
Timeout(r) == TimeoutWith(r, FloorMax)

\* the readers
Base(r, p) == LET k == Krtt(r, p) IN IF k.some /\ k.v # Zero THEN k.v ELSE r.lrtt
FirstResendOf(r, p) == N!Max(N!Max(FirstResend, SatMul(Base(r, p), 2)), r.floor)
HalfUp(a) == IF a[1] % 2 = 1 THEN U!Add(N!Div(a, 2), U!One) ELSE N!Div(a, 2)
Remembered(r, p) == LET x == N!Max(Base(r, p), HalfUp(r.floor)) IN IF x # Zero THEN Some(x) ELSE None
\* hub_resend: max(300 ms, 3 * r0 / 2 + 20 ms), the product first, as r0 + r0 / 2 (the same value, which cannot overflow
\* before the sum saturates); half selects the rule of the code before cede7b48, (r0 / 2) * 3, the half first, which is
\* one nanosecond short for an odd r0 (the witness config Rtt_hubhalf)
HubOfB(r, p, half) ==
    LET k == Krtt(r, p)
        t == IF half THEN SatMul(N!Div(k.v, 2), 3) ELSE SatAdd(k.v, N!Div(k.v, 2))
    IN IF k.some /\ k.v # Zero THEN Some(N!Max(HubResend, SatAdd(t, Ms(20)))) ELSE None
HubOf(r, p) == HubOfB(r, p, FALSE)
ThinNode(r) == N!Le(SlowRtt, N!Max(r.tgr, r.lrtt))
Thin(r, srtt, minrtt) ==
    srtt = Zero \/ N!Le(SlowRtt, N!Max(N!Max(N!Max(r.tgr, r.lrtt), minrtt), N!Div(srtt, 2)))

\* timers.rs conn_config: the node values a new connection gets (zero is no value)
Opt(v) == IF v = Zero THEN None ELSE Some(v)
ConnConfig(r, p) == [thin |-> ThinNode(r), rtt |-> Opt(r.lrtt), peak |-> Opt(r.tgr), rem |-> Remembered(r, p)]

\* Connection::set_node_rtt: a zero value leaves the input as it was
PushOf(cv, r) ==
    [thin |-> ThinNode(r),
     rtt |-> IF r.lrtt # Zero THEN Some(r.lrtt) ELSE cv.rtt,
     peak |-> IF r.tgr # Zero THEN Some(r.tgr) ELSE cv.peak]
OptV(o) == IF o.some THEN o.v ELSE Zero
\* the handshake of a connection is thin if the flag or the larger of its two node round trips is at least 250 ms
\* (handshake.rs Timing::is_thin, THIN_RTT)
ConnThin(cv) == cv.thin \/ N!Le(SlowRtt, N!Max(OptV(cv.rtt), OptV(cv.peak)))
\* Timing::first: the connection's first resend delay from what it was given
ConnFirst(rem, rtt) == N!Max(FirstResend, SatMul(IF rem.some THEN rem.v ELSE OptV(rtt), 2))
=============================================================================
