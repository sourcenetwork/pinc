--------------------------------- MODULE Cc ---------------------------------
(***************************************************************************)
(* Congestion control and pacing of vinc-transport recovery/cubic.rs,      *)
(* round_exit.rs, delivery.rs and pacer.rs over every interleaving of the   *)
(* calls the recovery engine makes on them, at small sizes (CcOps.tla has  *)
(* the operators and the scaling).                                         *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the window is never below MINC and never above MAXC, the filter      *)
(*    streak never exceeds 4, the Reno estimate never exceeds the cap      *)
(*    (Bounds);                                                            *)
(*  - slow start adds every acknowledged byte up to the cap (SlowStart);   *)
(*    an acknowledgement does not lower the window unless the rate gate    *)
(*    is in play (NoLowering);                                             *)
(*  - a loss reduces the window by the rule and ends slow start, a         *)
(*    filtered loss keeps it, a loss of a packet sent before the last      *)
(*    reduction changes nothing, a reduction never raises the window       *)
(*    (LossRules);                                                         *)
(*  - a restore never lowers the window (RestoreRaises);                   *)
(*  - the pacer charges each packet its size. The bursts are cut here     *)
(*    independently of the pacer's state, greedily at the budget of BURST *)
(*    datagrams (AccAfter); the pacer's count of bytes is that cut's and   *)
(*    stays below the budget (PacerShape); no packet inside a burst moves *)
(*    the release (NoEarlyPause); the release a burst sets is never later *)
(*    than the time its bytes take at the paced rate (NoOvercharge); a     *)
(*    sender that waits for the release and that the window limits at     *)
(*    every packet starts each burst at least that time after the last     *)
(*    packet of the burst before (PacerRate); for any waiting sender the  *)
(*    first packets of two bursts in a row are at least that time apart    *)
(*    (BurstStarts); the release never moves back (NextMono), also for a   *)
(*    sender that does not wait (EAGERS).                                  *)
(*    PacerSpec is the pacer alone, several bursts deep, with waits long  *)
(*    enough for a burst to be slow (Cc_pacer*.cfg). RULE picks the rule:  *)
(*    "bytes" is the code; "count", the rule before (a packet is a token  *)
(*    whatever it weighs), is kept as the witness of what the byte budget *)
(*    changes (Cc_pacer_count: small packets pause before their budget,    *)
(*    Cc_pacer_countbig: packets larger than the datagram are paced too    *)
(*    fast); each other rule removes one guard and has its RED config.     *)
(*    A sender the window does not limit breaks the packet-by-packet rate  *)
(*    (Cc_pacer_strict.cfg is the witness).                                *)
(* Lean counterpart: proofs/lean/Vinc/TransportCc*.lean.                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS MS, SEC, TOP, MAXC, MINC, INITC, BETALIM, MINMSS, MAXMSS, MINSAMP, EXITCW, GFAST, GMID, U32MAX, IRTT, BURST,
          KMAX, PMTU, PSRTT, PCW, LIMS, DELAYS, SIZES, EAGERS, RULE
VARIABLES x, p, t, k, sends, lims, sizes, last
vars == <<x, p, t, k, sends, lims, sizes, last>>

INSTANCE CcOps

Init == x = Cc0 /\ p = Pc0 /\ t = 0 /\ k = 0 /\ sends = <<>> /\ lims = <<>> /\ sizes = <<>>
        /\ last = [kind |-> "none", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0]

RttA == \E s \in {1, 3} : x' = OnSample(x, s) /\ last' = [kind |-> "rtt", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<p, t, sends, lims, sizes>>

AckA == \E d \in {0, 1}, ac \in {1, 5}, la \in 0..1, np \in 1..2, sr \in {-1, 4}, mn \in {-1, 300}, mss \in {2} :
          LET a == [now |-> t + d, acked |-> ac, la |-> la, np |-> np, srtt |-> sr, mn |-> mn, mss |-> mss]
              x1 == Decay(FeedProbe(x, a), a)
              ws0 == IF x1.epoch < 0 THEN x1.cwnd ELSE x1.west
          IN /\ t' = t + d
             /\ IF InSlowStart(x1)
                THEN x' = IF GateInPlay(a) THEN ApplyGate(GrowSS(x1, a), a.mn) ELSE GrowSS(x1, a)
                ELSE /\ ~GateInPlay(a)
                     /\ \E cw \in {x1.cwnd, x1.cwnd + 1, x1.cwnd + 3, MAXC}, we \in {ws0, ws0 + 1, ws0 + 2, ws0 + 5, MAXC}, kk \in {0, 2} :
                          LET y == [x1 EXCEPT !.cwnd = cw, !.west = we, !.k = kk, !.epoch = IF x1.epoch < 0 THEN a.now ELSE x1.epoch]
                          IN CaRel(x1, a, y) /\ x' = y
             /\ last' = [kind |-> "ack", r |-> FALSE, filt |-> FALSE, gate |-> GateInPlay(a), ac |-> ac]
             /\ UNCHANGED <<p, sends, lims, sizes>>
LossA == \E d \in {0, 1}, nw \in 0..3, lt \in {-1, 2, 9}, mn \in {-1, 2} :
           LET r == Loss(x, t + d, nw, lt, mn)
           IN /\ t' = t + d /\ x' = r.x
              /\ last' = [kind |-> "loss", r |-> r.r, filt |-> Filtered(x, lt, mn) /\ ~InEpisode(x, nw), gate |-> FALSE, ac |-> 0]
              /\ UNCHANGED <<p, sends, lims, sizes>>
NewPathA == \E np \in 0..3 : x' = NewPath(x, t, np) /\ last' = [kind |-> "newpath", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<p, t, sends, lims, sizes>>
RestoreA == \E cw \in {6, 20}, ss \in {15, TOP} :
              x' = Restore(x, cw, ss) /\ last' = [kind |-> "restore", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<p, t, sends, lims, sizes>>
ResumeA == \E mn \in {-1, 1, 300} : x' = Resume(x, mn) /\ last' = [kind |-> "resume", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<p, t, sends, lims, sizes>>
SlackA == \E b \in {2, 50} : x' = SetSlack(x, b) /\ last' = [kind |-> "slack", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<p, t, sends, lims, sizes>>

\* a packet of sz bytes leaves, never before the last packet; a waiting sender sends it at the release time or later,
\* an eager one (an ack-eliciting packet that does not consult the pacer) whenever it likes
SendA == \E d \in DELAYS, lim \in LIMS, sz \in SIZES, eager \in EAGERS :
           LET prev == IF sends = <<>> THEN 0 ELSE sends[Len(sends)]
               at == Mx(IF eager THEN t + d ELSE NextRelease(p, t + d), prev)
           IN /\ at <= 3000 /\ Len(sends) < 2 * BURST + 2
              /\ p' = OnSentR(RULE, p, at, sz, PMTU, PSRTT, PCW, lim)
              /\ sends' = Append(sends, at) /\ lims' = Append(lims, lim) /\ sizes' = Append(sizes, sz)
              /\ t' = Mx(t, at)
              /\ last' = [kind |-> "send", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<x>>

Next == (RttA \/ AckA \/ LossA \/ NewPathA \/ RestoreA \/ ResumeA \/ SlackA \/ SendA) /\ k' = k + 1
Spec == Init /\ [][Next]_vars
Bound == k <= KMAX

Bounds == /\ x.cwnd >= MINC /\ x.cwnd <= MAXC /\ x.streak <= 4 /\ x.west <= MAXC

\* the bursts, cut from the sizes alone: packet i is charged at least one byte; AccAfter is the bytes charged to the
\* burst after packet j (0 once a packet brought it to the budget); a burst starts where the one before ended
Ch(sz, i) == Mx(sz[i], 1)
RECURSIVE AccAfter(_, _)
AccAfter(sz, j) == IF j = 0 THEN 0
                   ELSE LET a == AccAfter(sz, j - 1) + Ch(sz, j) IN IF a >= Budget(PMTU) THEN 0 ELSE a
IsStart(sz, j) == AccAfter(sz, j - 1) = 0
EndsAt(sz, j) == AccAfter(sz, j - 1) + Ch(sz, j) >= Budget(PMTU)
RECURSIVE BytesIn(_, _, _)
BytesIn(sz, i, j) == IF i >= j THEN 0 ELSE Ch(sz, i) + BytesIn(sz, i + 1, j)
\* the first packet of the burst packet j belongs to
LastStart(sz, j) == CHOOSE i \in 1..j : IsStart(sz, i) /\ \A m \in (i + 1)..j : ~IsStart(sz, m)
SpanOf(b) == SpanB(b, PMTU, PSRTT, PCW)

PacerShape == p.spent >= 0 /\ p.spent < Budget(PMTU) /\ p.spent = AccAfter(sizes, Len(sizes))
\* a sender the window limits at every packet: a burst starts at least its predecessor's time after that one's last
PacerRateStrict == \A j \in 2..Len(sends) :
                     IsStart(sizes, j) => sends[j] >= sends[j - 1] + SpanOf(BytesIn(sizes, LastStart(sizes, j - 1), j))
PacerRate == (\A j \in DOMAIN lims : lims[j]) => PacerRateStrict
\* any waiting sender: the first packets of two bursts in a row are at least the first burst's time apart
BurstStarts == \A j \in 2..Len(sends) :
                 IsStart(sizes, j) => LET i == LastStart(sizes, j - 1) IN sends[j] >= sends[i] + SpanOf(BytesIn(sizes, i, j))
PacerInv == PacerShape /\ PacerRate /\ BurstStarts
Inv == Bounds /\ PacerInv

\* the pacer alone, deep enough for several bursts
PacerNext == SendA /\ k' = k + 1
PacerSpec == Init /\ [][PacerNext]_vars
NextMono == [][p'.next >= p.next]_vars
\* a packet that does not bring its burst to the budget leaves the release where it was
NoEarlyPause == [][(last'.kind = "send" /\ ~EndsAt(sizes', Len(sizes'))) => p'.next = p.next]_vars
\* the release a burst sets is at most its last packet's time plus the time its bytes take
NoOvercharge == [][(last'.kind = "send" /\ EndsAt(sizes', Len(sizes'))) =>
                    p'.next <= Mx(p.next, sends'[Len(sends')]
                                          + SpanOf(BytesIn(sizes', LastStart(sizes', Len(sizes')), Len(sizes') + 1)))]_vars

\* the step properties
NoLowering == [][(last'.kind = "ack" /\ ~last'.gate) => x'.cwnd >= x.cwnd]_vars
SlowStartAdds == [][(last'.kind = "ack" /\ ~last'.gate /\ x.cwnd < x.ss)
                      => x'.cwnd = Mn(SAdd(x.cwnd, last'.ac), MAXC)]_vars
LossRules == [][last'.kind = "loss" =>
                  /\ ~last'.r => x' = x
                  /\ last'.r => x'.cwnd <= x.cwnd
                  /\ (last'.r /\ ~last'.filt) => (x'.ss = x'.cwnd /\ ~InSlowStart(x') /\ x'.wmax = x.cwnd /\ x'.streak = 0)
                  /\ (last'.r /\ last'.filt) => x'.streak = x.streak + 1]_vars
RestoreRaises == [][last'.kind = "restore" => x'.cwnd >= x.cwnd]_vars
=============================================================================
