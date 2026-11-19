--------------------------- MODULE NodeSilenceOps ---------------------------
(***************************************************************************)
(* The silence bound of pinc-node bound.rs, step for step: `give_up`       *)
(* (GiveUp) and `heal_after` (HealAfter), with the constants of bound.rs,  *)
(* on the Nanos words of Nanos.tla (the u64 of the code on 16-bit limbs:   *)
(* every `saturating_add` and `saturating_mul` of the code saturates at    *)
(* u64::MAX here as well). NodeSilence.tla checks them over the boundary   *)
(* values of the u64 range; TraceNodeSilence.tla replays the recorded      *)
(* calls of the real code.                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, Nanos

\* bound.rs
MSW == Millis(1)          \* MS
SEED == Millis(333)       \* SEED_RTT
PTOS == 10                \* GIVE_UP_PTOS
SLOWSILENCE == Sec(20)    \* SLOW_SILENCE
RTTS == 8                 \* SILENCE_RTTS
PTOCAP == Sec(2)          \* PTO_CAP
MAXSHIFT == 6             \* PTO_MAX_SHIFT
SLOWSRTT == Sec(1)        \* SLOW_SRTT
ACKDELAY == Millis(25)    \* MAX_ACK_DELAY

\* a.saturating_mul(g) for a power of two g (a native integer): every multiplier of give_up is one
SatMulBy(a, g) == U!SatMul64(a, U!W(g))

\* an unsampled path (srtt 0) is the transport's seeded round trip
Seeded(srtt) == IF srtt = Zero THEN SEED ELSE srtt

\* srtt + max((srtt / 2) * 4, MS) + MAX_ACK_DELAY, saturating
Base(s) == SatAdd(SatAdd(s, Max(SatMulBy(Div(s, 2), 4), MSW)), ACKDELAY)
\* max(PTO_CAP, srtt * 2)
Wide(s) == Max(PTOCAP, SatMulBy(s, 2))
Slow(s) == Le(SLOWSRTT, s)
CapOf(s) == IF Slow(s) THEN Wide(s) ELSE PTOCAP
Shift(k) == IF k < MAXSHIFT THEN k ELSE MAXSHIFT

\* the loop over the GIVE_UP_PTOS timeouts: base * 2^min(k, 6), at most 4 * wide, at most the cap, summed saturating
RECURSIVE SumFrom(_, _, _, _, _)
SumFrom(base, wide, cap, k, acc) ==
    IF k = PTOS THEN acc
    ELSE SumFrom(base, wide, cap, k + 1,
                 SatAdd(acc, Min(Min(SatMulBy(base, 2 ^ Shift(k)), SatMulBy(wide, 4)), cap)))
Sum(s) == SumFrom(Base(s), Wide(s), CapOf(s), 0, Zero)

\* the transport's silence rule: SLOW_SILENCE on a slow or thin path, at least SILENCE_RTTS round trips
Need(s, thin) == Max(IF Slow(s) \/ thin THEN SLOWSILENCE ELSE Zero, SatMulBy(s, RTTS))

\* give_up(srtt, thin)
GiveUp(srtt, thin) == LET s == Seeded(srtt) IN Max(Sum(s), Need(s, thin))

\* heal_after(keepalive, srtt, thin)
HealAfter(keep, srtt, thin) == SatAdd(keep, GiveUp(srtt, thin))
=============================================================================
