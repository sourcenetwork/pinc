--------------------------------- MODULE Pn ---------------------------------
(***************************************************************************)
(* Packet-number truncation and expansion of vinc-transport                *)
(* packet/number.rs, checked exhaustively at a small byte size (PnOps.tla  *)
(* has the operators).                                                     *)
(*                                                                         *)
(* Checked, for every packet number n below P62, every width 1 to 3 and    *)
(* every largest received (or none):                                       *)
(*  - the expansion of the truncated number is congruent to it modulo the  *)
(*    window of the width, whatever the input (Congruent);                 *)
(*  - it gives n back whenever n lies within half a window of the next    *)
(*    number expected: expected - window / 2 < n <= expected + window / 2  *)
(*    (Exact), and the number it gives is in that window unless no number *)
(*    of the window is a packet number, below 0 or past the end of the     *)
(*    space (Closest);                                                     *)
(*  - encoding writes the low bytes of n, big-endian, and the expansion of *)
(*    what it wrote gives n back within the window (RoundTrip);            *)
(*  - an error is exact: a number above MAXPN is PacketNumber before the   *)
(*    width is looked at, a width other than 2 or 3 is PnLength            *)
(*    (Errors).                                                            *)
(* Lean counterpart: proofs/lean/Vinc/TransportPn.lean (any byte size, the *)
(* real one).                                                              *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS BYTE, P62, MAXPN, TOP, WIDEWIN, EMAX
VARIABLE s
INSTANCE PnOps

Init == s = 0
Next == s' = s

Exp(lg) == IF lg < 0 THEN 0 ELSE SAdd(lg, 1)
InWin(n, e, l) == LET h == Pow(BYTE, l) \div 2 IN e < n + h /\ n <= e + h

Congruent == \A lg \in -1..40, t \in 0..70, l \in 1..3 : DecodePn(t, l, lg) % Pow(BYTE, l) = t % Pow(BYTE, l)
Exact == \A lg \in -1..40, n \in 0..(P62 - 1), l \in 1..3 :
           InWin(n, Exp(lg), l) => DecodePn(n % Pow(BYTE, l), l, lg) = n
\* the result is in the window, or no number of the window is a packet number (below 0, or past the end of the space)
Closest == \A lg \in -1..40, t \in 0..70, l \in 1..3 :
             LET r == DecodePn(t, l, lg) w == Pow(BYTE, l)
             IN InWin(r, Exp(lg), l) \/ (r < w /\ Exp(lg) + (w \div 2) < r) \/ (r >= P62 - w /\ r + (w \div 2) <= Exp(lg))
RoundTrip == \A lg \in -1..40, n \in 0..(P62 - 1), l \in 2..3 :
               LET r == EncodePn(n, l)
                   v == IF l = 2 THEN r.b[1] * BYTE + r.b[2] ELSE (r.b[1] * BYTE + r.b[2]) * BYTE + r.b[3]
               IN r.err = "ok" /\ v = n % Pow(BYTE, l) /\ (InWin(n, Exp(lg), l) => DecodePn(v, l, lg) = n)
Errors == /\ EncodePn(MAXPN + 1, 2).err = "PacketNumber" /\ EncodePn(MAXPN + 1, 7).err = "PacketNumber"
          /\ EncodePn(3, 1).err = "PnLength" /\ EncodePn(3, 4).err = "PnLength" /\ EncodePn(3, 0).err = "PnLength"
          /\ EncodePn(MAXPN, 2).err = "ok"
Inv == Congruent /\ Exact /\ Closest /\ RoundTrip /\ Errors
Spec == Init /\ [][Next]_s
=============================================================================
