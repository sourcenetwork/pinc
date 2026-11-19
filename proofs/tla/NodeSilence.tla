----------------------------- MODULE NodeSilence -----------------------------
(***************************************************************************)
(* How long a path may stay silent before the transport gives it up        *)
(* (pinc-node bound.rs, `give_up` and `heal_after`; NodeSilenceOps.tla has  *)
(* the operators, on exact u64 words with the code's saturation), at every *)
(* boundary value of the smoothed round trip: 0 (unsampled), 2^j - 1, 2^j  *)
(* and 2^j + 1 for every width up to u64::MAX, and each constant of the    *)
(* code with its two neighbours (the point where (srtt / 2) * 4 reaches    *)
(* MS, the seeded round trip, SLOW_SRTT and PTO_CAP, and 2.5 s where eight *)
(* round trips are SLOW_SILENCE), both values of `thin`, and keepalives 0, *)
(* QUIET_KEEP_DIALER (60 s), QUIET_KEEP_ACCEPTOR (70 s), u64::MAX - 1 and  *)
(* u64::MAX.                                                               *)
(*                                                                         *)
(* The cases are the states of a machine whose root has one successor per  *)
(* (srtt, thin); G is the table of give_up over every case, computed once. *)
(*                                                                         *)
(* Checked (the invariants of bound.rs):                                   *)
(*  - Seed: an unsampled path is the transport's seeded round trip         *)
(*    (give_up(0) = give_up(333 ms));                                      *)
(*  - Floor: the bound never drops below the transport's silence rule:     *)
(*    eight round trips, and 20 s on a slow (srtt >= 1 s) or thin path     *)
(*    (saturating at u64::MAX);                                            *)
(*  - Grows: the bound grows with the smoothed round trip: for every       *)
(*    sampled srtt and every larger point of the domain, not smaller       *)
(*    (checked between the points of the domain, not for every u64);      *)
(*  - HealAbove, HealSum: heal_after is one keepalive interval plus the    *)
(*    give-up time (saturating), so a silence of one keepalive interval is *)
(*    never a heal (below u64::MAX).                                       *)
(* Witnesses: NodeSilence_w_need (the silence rule is above the sum of the *)
(* timeouts for some case, so Floor is not vacuous) and NodeSilence_w_sat  *)
(* (the bound saturates at u64::MAX for some case).                        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Nanos
VARIABLE c

INSTANCE NodeSilenceOps

Edge(w) == {U!Sub(w, One), w, U!Add(w, One)}
Pts == {U!Sub(U!Pw(j), One) : j \in 0..64} \cup {U!Pw(j) : j \in 0..63} \cup {U!Add(U!Pw(j), One) : j \in 0..63}
       \cup Edge(Of(500000)) \cup Edge(SEED) \cup Edge(SLOWSRTT) \cup Edge(PTOCAP) \cup Edge(Millis(2500))
       \cup {Millis(10), Millis(50), Millis(200), Sec(3)}
Keeps == {Zero, Sec(60), Sec(70), U!Sub(U!Max64, One), U!Max64}

\* give_up over every case, computed once
G == [p \in Pts \X BOOLEAN |-> GiveUp(p[1], p[2])]

Init == c = [t |-> "root"]
Next == c.t = "root" /\ \E x \in Pts, th \in BOOLEAN : c' = [t |-> "case", x |-> x, th |-> th]
Spec == Init /\ [][Next]_c

Seed == c.t = "case" => G[<<Zero, c.th>>] = G[<<SEED, c.th>>]

Floor == c.t = "case" =>
    LET s == IF c.x = Zero THEN SEED ELSE c.x
        g == G[<<c.x, c.th>>]
    IN /\ Le(U!SatMul64(s, W(8)), g)
       /\ (Le(Sec(1), s) \/ c.th) => Le(Sec(20), g)

Grows == c.t = "case" /\ c.x # Zero =>
    \A y \in Pts : Lt(c.x, y) => Le(G[<<c.x, c.th>>], G[<<y, c.th>>])

HealAbove == c.t = "case" =>
    \A k \in Keeps :
        LET h == HealAfter(k, c.x, c.th)
        IN /\ Le(G[<<c.x, c.th>>], h)
           /\ Lt(k, U!Max64) => Lt(k, h)

HealSum == c.t = "case" =>
    \A k \in Keeps :
        LET s == U!Add(k, G[<<c.x, c.th>>])
        IN HealAfter(k, c.x, c.th) = IF U!Fits(s) THEN s ELSE U!Max64

\* reachability witnesses
NeedNeverBinds == c.t = "case" => LET s == Seeded(c.x) IN Le(Need(s, c.th), Sum(s))
NeverMax == c.t = "case" => G[<<c.x, c.th>>] # U!Max64
=============================================================================
