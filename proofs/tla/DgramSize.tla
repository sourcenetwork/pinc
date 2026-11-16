------------------------------ MODULE DgramSize ------------------------------
(***************************************************************************)
(* How big a datagram build_datagram (vinc-transport conn/send.rs) writes  *)
(* for one path, for every input it reads, with the real sizes.            *)
(*                                                                         *)
(* The story: a connection writes one datagram for a path. The path is     *)
(* believed to carry pathMtu bytes. The datagram may start with a          *)
(* fragment of the handshake, then holds one application packet (1-RTT or  *)
(* 0-RTT), or zero padding the handshake still owes. Two datagrams are     *)
(* built larger than pathMtu on purpose: a first flight sent whole (up to  *)
(* 1452 bytes, or the interface size when smaller), and a path MTU probe   *)
(* of the probed size.                                                     *)
(*                                                                         *)
(* What must never happen: an application packet that is not a probe ends  *)
(* past pathMtu (AppFits), or a datagram is larger than pathMtu for any    *)
(* other reason than those two (SizeOK). A router drops such a packet, or  *)
(* black-holes it with no ICMP back.                                       *)
(*                                                                         *)
(* GUARD is the code since #554: the application packet's room ends at     *)
(* pathMtu (at the probe's size for a probe). With GUARD = FALSE it ends   *)
(* where the datagram's room ends, which a whole flight widens to 1452,    *)
(* so the packet behind a whole flight ran past pathMtu (DgramSize_noguard *)
(* must find AppFits violated).                                            *)
(*                                                                         *)
(* What the model leaves out: the handshake fragment and the application   *)
(* packet are given by how many bytes each would take (HsWant, AppWant)    *)
(* and take at most the room they are given; their content is the          *)
(* FramePack and HdrBody rows. Lean counterpart:                           *)
(* proofs/lean/Vinc/TransportDgramSize.lean.                               *)
(***************************************************************************)
EXTENDS Integers

\* GUARD: TRUE is the code (the packet behind the handshake ends at the path's size), FALSE the rule before #554.
CONSTANT GUARD

\* The input of one call of build_datagram. Every valid input is an initial state, and nothing changes after it: each
\* invariant is checked on every input.
VARIABLE x

\* MIN_MTU, PROBE_MTU and MIN_ROOM of the code: the floor of a path, the first probe size, the smallest room worth a
\* datagram.
MinMtu == 1200
ProbeMtu == 1452
MinRoom == 24

\* The sizes a path is believed to carry: the floor, after the first probe, after a jumbo probe.
PathSizes == {MinMtu, ProbeMtu, 8952}
\* The interface sizes the host reports, below and above the first probe size.
Ifaces == {MinMtu, 1280, 1500, 9000}
\* The caller's buffer: below a datagram, around the sizes that matter, a GSO buffer.
Outs == {MinRoom - 1, MinRoom, MinMtu, 1300, ProbeMtu, 9216, 65536}
\* What the amplification budget still allows on the path (a validated path is unlimited, standing as 10^6).
Amps == {0, MinRoom, 1250, 4000, 1000000}
\* The probe size probe_size returns, 0 for none: a probe is above the path's size and fits the buffer.
Probes == {0, ProbeMtu, 8952}
\* The handshake bytes write_handshake would write: none, a short Reply, a resumed Hello, flights around the sizes.
HsWants == {0, 112, 149, 1188, 1269, 1388, ProbeMtu}
\* The bytes the application packet would take: none, tiny, around the room behind a short fragment, a lot.
AppWants == {0, 1, 30, 1088, 1303, 9000}
\* The zero padding the handshake still owes.
PadOweds == {0, MinMtu}

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

\* One input of build_datagram: the path's size p, the interface size f, the buffer o, the amplification room a, the
\* probe size q (0: none), whether the first flight goes whole w, and what each part would take.
Inputs == [p : PathSizes, f : Ifaces, o : Outs, a : Amps, q : Probes, w : BOOLEAN,
           hs : HsWants, app : AppWants, pad : PadOweds]
\* probe_size returns a probe only above the path's size (Mtu::target) and only when the buffer holds it.
Valid(i) == i.q = 0 \/ (i.q > i.p /\ i.q <= i.o)

\* `base`: a whole flight may take the larger of the path's size and 1452 (or the interface size when smaller).
Base(i) == IF i.w THEN Max(i.p, Min(ProbeMtu, i.f)) ELSE i.p
\* `max_len`: the probe's size or the base, cut to the buffer and to the amplification room.
MaxLen(i) == Min(Min(IF i.q > 0 THEN i.q ELSE Base(i), i.o), i.a)
\* The handshake fragment takes at most the datagram's room.
Hs(i) == Min(i.hs, MaxLen(i))
\* `app_end`: where the application packet's room ends. With the guard: the path's size, or the probe's size.
AppEnd(g, i) == IF g THEN Min(IF i.q > 0 THEN i.q ELSE i.p, MaxLen(i)) ELSE MaxLen(i)
\* The application packet takes at most the room behind the fragment (none when the fragment reaches the end).
App(g, i) == Min(i.app, Max(AppEnd(g, i) - Hs(i), 0))
\* The handshake pads into the datagram's room only when no application packet rode in it.
Pad(g, i) == IF App(g, i) = 0 THEN Min(i.pad, MaxLen(i) - Hs(i)) ELSE 0
\* The datagram's length: nothing when the room is under MIN_ROOM, the owed padding alone when no fragment is left,
\* else the fragment, the packet and the padding.
Len(g, i) ==
    IF MaxLen(i) < MinRoom THEN 0
    ELSE IF Hs(i) = 0 /\ i.pad > 0 THEN Min(i.pad, MaxLen(i))
    ELSE Hs(i) + App(g, i) + Pad(g, i)
\* The application packet the datagram carries: none when there is no datagram or it is the owed padding alone.
Pkt(g, i) == IF MaxLen(i) < MinRoom \/ (Hs(i) = 0 /\ i.pad > 0) THEN 0 ELSE App(g, i)

\* Every valid input is a state of its own; nothing changes after it.
Init == x \in {i \in Inputs : Valid(i)}
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

\* An application packet that is not a probe ends at or before the path's size.
AppFits == x.q = 0 /\ Pkt(GUARD, x) > 0 => Hs(x) + Pkt(GUARD, x) <= x.p
\* A datagram is larger than the path's size only as a probe of the probed size, or as a whole flight with no
\* application packet behind it, at most the size the whole flight was given.
SizeOK == \/ Len(GUARD, x) <= x.p
          \/ x.q > 0 /\ Len(GUARD, x) <= x.q
          \/ x.w /\ Pkt(GUARD, x) = 0 /\ Len(GUARD, x) <= Base(x)
\* Never past the buffer or the amplification room.
Bounded == Len(GUARD, x) <= Min(x.o, x.a)
\* The guard changes nothing but a whole flight's datagram: every other datagram is the one of the rule before #554.
Unchanged == ~x.w => Len(GUARD, x) = Len(FALSE, x) /\ Pkt(GUARD, x) = Pkt(FALSE, x)
\* Negated for a witness: with the guard a packet still rides behind a whole flight's fragment, so AppFits is not
\* vacuous. DgramSize_reach must find it violated.
Coalesced == ~(x.w /\ Hs(x) > 0 /\ Pkt(GUARD, x) > 0)
=============================================================================
