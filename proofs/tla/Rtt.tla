-------------------------------- MODULE Rtt ---------------------------------
(***************************************************************************)
(* The node's round trips (vinc-core rtt.rs, NodeRtt), over every          *)
(* interleaving of a handshake sample, a restored peer, a connection's     *)
(* round trip peak, a dial that times out, a new connection and a push of  *)
(* the node values to a running one, at small sizes (RttOps.tla has the    *)
(* operators, on u64 nanosecond words, so saturation is exact).            *)
(*                                                                         *)
(* Checked (module doc of rtt.rs in quotes):                               *)
(*  - "at most PEER_RTTS peers, none replaced once the table is full":     *)
(*    the table never holds more than CAP peers, each once (Bounded); no   *)
(*    entry is ever removed or moved: the peers after a step begin with    *)
(*    the peers before it (TableOnlyGrows); a known peer takes the new     *)
(*    value in place, a new peer is stored exactly when there is room and  *)
(*    otherwise refused with the table unchanged, and no other peer's      *)
(*    value moves (HandshakeStep, RestoreStepOK);                                             *)
(*  - lrtt, "an exponentially weighted mean with weight 7/8 on the old     *)
(*    value": the first sample is taken as it is; then 8 * new lies in     *)
(*    (7 * old + sample - 8, 7 * old + sample] when that fits a u64, and   *)
(*    is the floor of u64::MAX / 8 when the sum saturates; it never        *)
(*    exceeds the larger of the old average and the sample, is positive    *)
(*    after a sample, is 0 only before the first sample, and moves only    *)
(*    on a handshake sample (HandshakeStep, AvgZeroOnlyBefore, AvgOnlyHandshake);          *)
(*  - tgr, "after every sample it becomes max(sample, tgr - tgr / 32)":    *)
(*    never below the sample, never below 31/32 of the old peak, one of    *)
(*    the two, never above the larger of the old peak and the sample,      *)
(*    never above the largest sample ever given, and zero only before the  *)
(*    first non-zero one (PeakStepOK, PeakAtMost, PeakZeroIff); the   *)
(*    peak is not related to the average (the module doc promises no order,*)
(*    and tgr = 0 with lrtt > 0 is reachable);                             *)
(*  - the floor "rises after a dial times out, min(8 s, max(500 ms, 2 x    *)
(*    floor)), and falls to zero only when a handshake answered at its     *)
(*    first flight gives a sample: a new round trip peak of a session does *)
(*    not reset it": a timeout takes it to 500 ms from zero and doubles it *)
(*    up to 8 s; it is always 0, 500 ms, 1 s, 2 s, 4 s or 8 s; every       *)
(*    handshake with a sample sets it to zero, a handshake with no sample  *)
(*    (0) changes nothing, and no other step (a restored peer, a peak)     *)
(*    changes it (FloorShape, TimeoutStepOK, HandshakeStep, HandshakeZero,*)
(*    FloorOnlyHandshake). That the endpoint calls note_handshake only for *)
(*    a handshake with no resend is read off events.rs, not modelled;      *)
(*  - the readers: the first resend of a dial is at least 500 ms, at least *)
(*    twice the peer's round trip (else the node average) and at least the *)
(*    floor, and one of the three (FirstResendRight); a connection built   *)
(*    from conn_config computes the same first resend from the remembered  *)
(*    round trip it is given as the node computes it, because the floor is *)
(*    even (ConnFirstSame); the hub resend exists exactly for a peer with  *)
(*    a positive round trip of its own (HubRight); a node is thin exactly  *)
(*    when its peak or its average is at least 250 ms, and a session is    *)
(*    thin when it has no sample, when the node is, or when its smallest   *)
(*    round trip or half its smoothed one is (ThinRight);                  *)
(*  - what the connection reads: a new connection gets the average and the *)
(*    peak (None for 0), the thin flag and the remembered round trip; a    *)
(*    running one that is pushed the node values holds them afterwards,    *)
(*    and a connection's handshake is thin, so its connect limit is 60 s,  *)
(*    exactly when the node is thin (PushRight, ConnectRight). The zero    *)
(*    "leaves the input as it was" rule of the push never hides a fall: an *)
(*    average or a peak that is positive stays positive                    *)
(*    (AvgNeverZeroAgain, PeakNeverZeroAgain).                             *)
(* Witness configs: Rtt_peakfloor (a peak resets the floor, the code of    *)
(* before 2dd1682: FloorOnlyHandshake fails), Rtt_zeroreset (a handshake   *)
(* with no sample resets the floor: HandshakeZero fails), Rtt_evict (a     *)
(* full table replaces its oldest peer: TableOnlyGrows fails), Rtt_floor9  *)
(* (a ceiling of 9 s: FloorShape fails); Rtt_sat (a saturated average),    *)
(* Rtt_full (a refused peer), Rtt_thin (a thin node) and Rtt_peakzero (a   *)
(* zero peak beside a positive average) are reachability witnesses.        *)
(* Lean counterpart: proofs/lean/Vinc/CoreRtt*.lean.                       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS CAP, PEERS, VALSMS, TOPV, EDGE, DEPTH, PEAK_RESETS, ZERO_RESETS, EVICT, FLOOR_TOP
VARIABLES r, cv, last, n, sampled, maxpeak, maxhs
vars == <<r, cv, last, n, sampled, maxpeak, maxhs>>

INSTANCE RttOps

\* the samples tried: whole milliseconds, 250 ms less one nanosecond, and u64::MAX (so the average saturates)
Vals == {Ms(k) : k \in VALSMS} \cup (IF EDGE THEN {N!SatSub(SlowRtt, U!One)} ELSE {}) \cup (IF TOPV THEN {U!Max64} ELSE {})

Cv0 == [thin |-> FALSE, rtt |-> None, peak |-> None]
Init == /\ r = Rtt0 /\ cv = Cv0 /\ last = [k |-> "init", p |-> 0, v |-> Zero, ok |-> TRUE] /\ n = 0
        /\ sampled = FALSE /\ maxpeak = Zero /\ maxhs = Zero

Mx(a, b) == N!Max(a, b)
Step(rp, nv, k, p, v, ok) == /\ r' = rp /\ last' = [k |-> k, p |-> p, v |-> v, ok |-> ok] /\ n' = n + 1

HsStep == \E p \in PEERS, v \in Vals :
    LET x == Handshake(r, CAP, p, v)
        evict == EVICT /\ v # Zero /\ Find(r.tab, p) = 0 /\ Len(r.tab) = CAP
        y == [x EXCEPT !.tab = IF evict THEN Append(Tail(r.tab), <<p, v>>) ELSE @,
                       !.floor = IF v = Zero /\ ZERO_RESETS THEN Zero ELSE @]
    IN /\ Step(y, 0, "hs", p, v, TRUE) /\ cv' = cv
       /\ sampled' = (sampled \/ v # Zero) /\ maxhs' = Mx(maxhs, v) /\ maxpeak' = maxpeak

RestoreStep == \E p \in PEERS, v \in Vals :
    LET x == Restore(r, CAP, p, v)
    IN /\ Step(x.r, 0, "restore", p, v, x.ok) /\ cv' = cv /\ UNCHANGED <<sampled, maxpeak, maxhs>>

PeakStep == \E v \in Vals :
    LET x == Peak(r, v)
    IN /\ Step([x EXCEPT !.floor = IF PEAK_RESETS THEN Zero ELSE @], 0, "peak", 0, v, TRUE) /\ cv' = cv
       /\ maxpeak' = Mx(maxpeak, v) /\ UNCHANGED <<sampled, maxhs>>

TimeoutStep == /\ Step(TimeoutWith(r, N!Sec(FLOOR_TOP)), 0, "timeout", 0, Zero, TRUE) /\ cv' = cv
               /\ UNCHANGED <<sampled, maxpeak, maxhs>>

ConnectStep == \E p \in PEERS :
    LET c == ConnConfig(r, p)
    IN /\ Step(r, 0, "connect", p, Zero, TRUE) /\ cv' = [thin |-> c.thin, rtt |-> c.rtt, peak |-> c.peak]
       /\ UNCHANGED <<sampled, maxpeak, maxhs>>

PushStep == /\ Step(r, 0, "push", 0, Zero, TRUE) /\ cv' = PushOf(cv, r) /\ UNCHANGED <<sampled, maxpeak, maxhs>>

Next == n < DEPTH /\ (HsStep \/ RestoreStep \/ PeakStep \/ TimeoutStep \/ ConnectStep \/ PushStep)
Spec == Init /\ [][Next]_vars

Probe == PEERS \cup {Cardinality(PEERS) + 1}   \* a peer the table never saw

Fits(a) == a[5] = 0
Keys(t) == [i \in 1..Len(t) |-> t[i][1]]
Floors == {Zero, Ms(500), N!Sec(1), N!Sec(2), N!Sec(4), N!Sec(8)}
Exact(a, k) == N!MulAt(a, k, 1, 0)       \* a * k on 80 bits, no overflow for a u64 and k < 2^15
Le(a, b) == N!Le(a, b)
Lt(a, b) == N!Lt(a, b)

-------------------------------------------------------------------------------
\* State invariants

Bounded == /\ Len(r.tab) <= CAP
           /\ \A i, j \in 1..Len(r.tab) : r.tab[i][1] = r.tab[j][1] => i = j
           /\ \A i \in 1..Len(r.tab) : Fits(r.tab[i][2])
           /\ Fits(r.lrtt) /\ Fits(r.tgr) /\ Fits(r.floor)
FloorShape == r.floor \in Floors
AvgZeroOnlyBefore == (r.lrtt = Zero) <=> ~sampled
PeakAtMost == Le(r.tgr, maxpeak)
AvgAtMost == Le(r.lrtt, maxhs)

FirstResendRight(p) ==
    LET f == FirstResendOf(r, p)
        two == SatMul(Base(r, p), 2)
    IN /\ Le(FirstResend, f) /\ Le(r.floor, f) /\ Le(two, f)
       /\ (f = FirstResend \/ f = r.floor \/ f = two)
ConnFirstSame(p) == ConnFirst(Remembered(r, p), Opt(r.lrtt)) = FirstResendOf(r, p)
RememberedRight(p) ==
    LET m == Remembered(r, p)
    IN /\ (~m.some) <=> (Base(r, p) = Zero /\ r.floor = Zero)
       /\ (m.some => /\ Le(Base(r, p), m.v) /\ Le(r.floor, Exact(m.v, 2))
                     /\ (m.v = Base(r, p) \/ Le(Exact(m.v, 2), U!Add(r.floor, U!One))))
HubRight(p) ==
    LET h == HubOf(r, p)
        k == Krtt(r, p)
        exact == U!Add(Exact(N!Div(k.v, 2), 3), Ms(20))
    IN /\ h.some <=> (k.some /\ k.v # Zero)
       /\ (h.some => Le(HubResend, h.v) /\ (U!Fits(exact) => Le(exact, h.v)))
ThinRight ==
    /\ ThinNode(r) <=> (Le(SlowRtt, r.tgr) \/ Le(SlowRtt, r.lrtt))
    /\ \A s, m \in Vals :
        Thin(r, s, m) <=> (s = Zero \/ ThinNode(r) \/ Le(SlowRtt, m) \/ Le(SlowRtt, N!Div(s, 2)))

Inv == /\ Bounded /\ FloorShape /\ AvgZeroOnlyBefore /\ PeakAtMost /\ AvgAtMost
       /\ \A p \in Probe : FirstResendRight(p) /\ ConnFirstSame(p) /\ RememberedRight(p) /\ HubRight(p)
       /\ ThinRight

-------------------------------------------------------------------------------
\* Action properties

KnownBefore(p) == Find(r.tab, p) # 0
KrttAfter(p) == LET i == Find(r'.tab, p) IN IF i = 0 THEN None ELSE Some(r'.tab[i][2])
Stored(p, v, ok) ==
    /\ ok <=> (KnownBefore(p) \/ Len(r.tab) < CAP)
    /\ IF ok THEN KrttAfter(p) = Some(v) ELSE r'.tab = r.tab
    /\ \A q \in Probe \ {p} : KrttAfter(q) = Krtt(r, q)
    /\ Len(r'.tab) = (IF KnownBefore(p) \/ ~ok THEN Len(r.tab) ELSE Len(r.tab) + 1)

TableOnlyGrows == /\ Len(r'.tab) >= Len(r.tab)
                  /\ \A i \in 1..Len(r.tab) : r'.tab[i][1] = r.tab[i][1]

HandshakeStep ==
    LET p == last'.p
        v == last'.v
        s == U!Add(Exact(r.lrtt, 7), v)
    IN last'.k = "hs" /\ v # Zero =>
        /\ r'.floor = Zero /\ r'.tgr = r.tgr
        /\ Stored(p, v, KnownBefore(p) \/ Len(r.tab) < CAP)
        /\ r'.lrtt # Zero /\ Le(r'.lrtt, Mx(r.lrtt, v))
        /\ IF r.lrtt = Zero THEN r'.lrtt = v
           ELSE IF U!Fits(s) THEN Le(Exact(r'.lrtt, 8), s) /\ Lt(s, U!Add(Exact(r'.lrtt, 8), N!W(8)))
                ELSE r'.lrtt = N!Div(U!Max64, 8)
HandshakeZero == last'.k = "hs" /\ last'.v = Zero => r' = r
RestoreStepOK == last'.k = "restore" =>
    /\ r'.lrtt = r.lrtt /\ r'.tgr = r.tgr /\ r'.floor = r.floor /\ Stored(last'.p, last'.v, last'.ok)
PeakStepOK == last'.k = "peak" =>
    /\ r'.tab = r.tab /\ r'.lrtt = r.lrtt /\ r'.floor = r.floor
    /\ Le(last'.v, r'.tgr) /\ Le(Exact(r.tgr, 31), Exact(r'.tgr, 32))
    /\ (r'.tgr = last'.v \/ r'.tgr = N!Sub(r.tgr, N!Div(r.tgr, 32)))
    /\ Le(r'.tgr, Mx(r.tgr, last'.v))
TimeoutStepOK == last'.k = "timeout" =>
    /\ r'.tab = r.tab /\ r'.lrtt = r.lrtt /\ r'.tgr = r.tgr
    /\ Le(FirstResend, r'.floor) /\ Le(r'.floor, FloorMax)
    /\ (Lt(r.floor, FloorMax) => Lt(r.floor, r'.floor))
    /\ (Le(FirstResend, r.floor) => Exact(r'.floor, 1) = U!Min(Exact(FloorMax, 1), Exact(r.floor, 2)))
    /\ (r.floor = Zero => r'.floor = FirstResend)
FloorOnlyHandshake == Lt(r'.floor, r.floor) => (last'.k = "hs" /\ last'.v # Zero /\ r'.floor = Zero)
FloorMoves == r'.floor # r.floor => last'.k \in {"hs", "timeout"}
AvgOnlyHandshake == r'.lrtt # r.lrtt => (last'.k = "hs" /\ last'.v # Zero)
PeakOnlyPeak == r'.tgr # r.tgr => last'.k = "peak"
AvgNeverZeroAgain == r.lrtt # Zero => r'.lrtt # Zero
PeakZeroIff == last'.k = "peak" => ((r'.tgr = Zero) <=> (r.tgr = Zero /\ last'.v = Zero))
PeakNeverZeroAgain == r.tgr # Zero => r'.tgr # Zero
PushRight == last'.k = "push" =>
    /\ cv'.thin = ThinNode(r) /\ ConnThin(cv') = ThinNode(r)
    /\ cv'.rtt = Opt(r.lrtt) /\ cv'.peak = Opt(r.tgr)
ConnectRight == last'.k = "connect" =>
    /\ cv'.thin = ThinNode(r) /\ ConnThin(cv') = ThinNode(r)
    /\ cv'.rtt = Opt(r.lrtt) /\ cv'.peak = Opt(r.tgr)

ActionProp == /\ TableOnlyGrows /\ HandshakeStep /\ HandshakeZero /\ RestoreStepOK /\ PeakStepOK /\ TimeoutStepOK
              /\ FloorOnlyHandshake /\ FloorMoves /\ AvgOnlyHandshake /\ PeakOnlyPeak /\ AvgNeverZeroAgain
              /\ PeakNeverZeroAgain /\ PeakZeroIff /\ PushRight /\ ConnectRight
Props == [][ActionProp]_vars

\* reachability witnesses
NoSat == r.lrtt # N!Div(U!Max64, 8)
NoRefuse == ~(last.k = "restore" /\ ~last.ok)
NoThin == ~ThinNode(r)
NoPeakZero == ~(r.tgr = Zero /\ r.lrtt # Zero)
=============================================================================
