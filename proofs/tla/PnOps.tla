------------------------------- MODULE PnOps --------------------------------
(***************************************************************************)
(* The operations of pinc-transport packet/number.rs, step for step: the   *)
(* packet-number truncation and expansion over 62 bits at a width fixed per *)
(* connection. Pn.tla checks them exhaustively at a small byte size;        *)
(* TracePn.tla replays the recorded calls of the real code.                *)
(*                                                                         *)
(* BYTE is 256 in the code; Pn.tla runs a small BYTE so that every packet   *)
(* number, width and largest received is visited. P62 stands for 2^62 and   *)
(* MAXPN for 2^62 - 1: TLC integers are 32 bits, so the trace check runs   *)
(* them at the largest 32-bit integer and keeps every number below it; the *)
(* Lean replay runs the real values (the wide file). TOP stands for        *)
(* u64::MAX in the saturating sums.                                        *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS BYTE, P62, MAXPN, TOP, WIDEWIN

SAdd(a, b) == IF a > TOP - b THEN TOP ELSE a + b
RECURSIVE Pow(_, _)
Pow(b, n) == IF n = 0 THEN 1 ELSE b * Pow(b, n - 1)
Clamp14(n) == IF n < 1 THEN 1 ELSE IF n > 4 THEN 4 ELSE n

\* decode_pn: lg is -1 for none
DecodePn(t, len, lg) ==
    LET l == Clamp14(len)
        e == IF lg < 0 THEN 0 ELSE SAdd(lg, 1)
        w == Pow(BYTE, l)
        h == w \div 2
        c == (e - (e % w)) + (t % w)
    IN IF SAdd(c, h) <= e /\ c < P62 - w THEN c + w
       ELSE IF c > SAdd(e, h) /\ c >= w THEN c - w
       ELSE c

\* encode_pn: the error, or "ok" with the three bytes (the unused ones are 0)
EncodePn(full, len) ==
    IF full > MAXPN THEN [err |-> "PacketNumber", b |-> <<0, 0, 0>>]
    ELSE IF len < 2 \/ len > 3 THEN [err |-> "PnLength", b |-> <<0, 0, 0>>]
    ELSE [err |-> "ok", b |-> [i \in 1..3 |-> IF i <= len THEN (full \div Pow(BYTE, len - i)) % BYTE ELSE 0]]

\* pn_len_for
PnLenFor(w) == IF w > WIDEWIN THEN 3 ELSE 2
=============================================================================
