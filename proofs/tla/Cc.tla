--------------------------------- MODULE Cc ---------------------------------
(***************************************************************************)
(* Congestion control and pacing of pinc-transport recovery/cubic.rs,      *)
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
(*  - the pacer holds one to BURST tokens (PacerShape); a sender that    *)
(*    waits for the release and that the window limits at every packet   *)
(*    sends no more than BURST packets in any BURST gaps (PacerRate); for *)
(*    any sender the first packets of two bursts in a row are at least    *)
(*    BURST gaps apart (BurstStarts) and the release never moves back     *)
(*    (NextMono). PacerSpec is the pacer alone, several bursts deep, with *)
(*    waits long enough for a burst to be slow (Cc_pacer*.cfg); a sender  *)
(*    the window does not limit breaks the packet-by-packet rate          *)
(*    (Cc_pacer_strict.cfg is the witness).                                *)
(* Lean counterpart: proofs/lean/Pinc/TransportCc*.lean.                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS MS, SEC, TOP, MAXC, MINC, INITC, BETALIM, MINMSS, MAXMSS, MINSAMP, EXITCW, GFAST, GMID, U32MAX, IRTT, BURST,
          KMAX, PMTU, PSRTT, PCW, LIMS, DELAYS
VARIABLES x, p, t, k, sends, lims, last
vars == <<x, p, t, k, sends, lims, last>>

INSTANCE CcOps

Init == x = Cc0 /\ p = Pc0 /\ t = 0 /\ k = 0 /\ sends = <<>> /\ lims = <<>> /\ last = [kind |-> "none", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0]

RttA == \E s \in {1, 3} : x' = OnSample(x, s) /\ last' = [kind |-> "rtt", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<p, t, sends, lims>>

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
             /\ UNCHANGED <<p, sends, lims>>
LossA == \E d \in {0, 1}, nw \in 0..3, lt \in {-1, 2, 9}, mn \in {-1, 2} :
           LET r == Loss(x, t + d, nw, lt, mn)
           IN /\ t' = t + d /\ x' = r.x
              /\ last' = [kind |-> "loss", r |-> r.r, filt |-> Filtered(x, lt, mn) /\ ~InEpisode(x, nw), gate |-> FALSE, ac |-> 0]
              /\ UNCHANGED <<p, sends, lims>>
NewPathA == \E np \in 0..3 : x' = NewPath(x, t, np) /\ last' = [kind |-> "newpath", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<p, t, sends, lims>>
RestoreA == \E cw \in {6, 20}, ss \in {15, TOP} :
              x' = Restore(x, cw, ss) /\ last' = [kind |-> "restore", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<p, t, sends, lims>>
ResumeA == \E mn \in {-1, 1, 300} : x' = Resume(x, mn) /\ last' = [kind |-> "resume", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<p, t, sends, lims>>
SlackA == \E b \in {2, 50} : x' = SetSlack(x, b) /\ last' = [kind |-> "slack", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<p, t, sends, lims>>

\* a sender that waits for the release: a packet leaves at the release time or later, never before the last packet
SendA == \E d \in DELAYS, lim \in LIMS :
           LET at == Mx(NextRelease(p, t + d), IF sends = <<>> THEN 0 ELSE sends[Len(sends)])
           IN /\ at <= 3000 /\ Len(sends) < 2 * BURST + 2
              /\ p' = OnSent(p, at, PMTU, PSRTT, PCW, lim) /\ sends' = Append(sends, at) /\ lims' = Append(lims, lim)
              /\ t' = Mx(t, at)
              /\ last' = [kind |-> "send", r |-> FALSE, filt |-> FALSE, gate |-> FALSE, ac |-> 0] /\ UNCHANGED <<x>>

Next == (RttA \/ AckA \/ LossA \/ NewPathA \/ RestoreA \/ ResumeA \/ SlackA \/ SendA) /\ k' = k + 1
Spec == Init /\ [][Next]_vars
Bound == k <= KMAX

Bounds == /\ x.cwnd >= MINC /\ x.cwnd <= MAXC /\ x.streak <= 4 /\ x.west <= MAXC
G == Gap(PMTU, PSRTT, PCW)
PacerShape == p.tokens >= 1 /\ p.tokens <= BURST
\* a sender the window limits at every packet: packets i and i + BURST are at least BURST gaps apart
PacerRateStrict == \A i \in 1..(Len(sends) - BURST) : sends[i + BURST] >= sends[i] + BURST * G
PacerRate == (\A j \in DOMAIN lims : lims[j]) => PacerRateStrict
\* any sender: the first packets of two bursts in a row are at least BURST gaps apart, and the release never moves back
BurstStarts == \A i \in 1..(Len(sends) - BURST) : (i - 1) % BURST = 0 => sends[i + BURST] >= sends[i] + BURST * G
PacerInv == PacerShape /\ PacerRate /\ BurstStarts
Inv == Bounds /\ PacerInv

\* the pacer alone, deep enough for several bursts
PacerNext == SendA /\ k' = k + 1
PacerSpec == Init /\ [][PacerNext]_vars
NextMono == [][p'.next >= p.next]_vars

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
