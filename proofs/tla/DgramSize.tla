------------------------------ MODULE DgramSize ------------------------------
(***************************************************************************)
(* How big a datagram build_datagram (pinc-transport conn/send.rs) writes  *)
(* for one path, for every input it reads, with the real sizes.            *)
(*                                                                         *)
(* The story: a connection writes one datagram for a path. The path is     *)
(* believed to carry pathMtu bytes. The datagram may start with a          *)
(* fragment of the handshake, then holds one application packet (1-RTT or  *)
(* 0-RTT), or zero padding the handshake still owes. Two datagrams are     *)
(* built larger than pathMtu on purpose: a first flight sent whole (up to  *)
(* 1452 bytes, and no more than the interface carries on the path's        *)
(* address family: its MTU less the IP and UDP headers), and a path MTU    *)
(* probe of the probed size. A first flight longer than that is cut at the *)
(* path's size from the start.                                             *)
(*                                                                         *)
(* What must never happen: an application packet that is not a probe ends  *)
(* past pathMtu (AppFits), or a datagram is larger than pathMtu for any    *)
(* other reason than those two (SizeOK). A router drops such a packet, or  *)
(* black-holes it with no ICMP back.                                       *)
(*                                                                         *)
(* IFACE is the code since #584: the room of a whole flight is the        *)
(* interface's payload. With IFACE = FALSE it is the interface's MTU, which *)
(* includes the headers, so a 1280-byte interface got a 1280-byte datagram *)
(* on a link that carries 1252 (DgramSize_noiface must find IfaceOK        *)
(* violated).                                                              *)
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
(* proofs/lean/Pinc/TransportDgramSize.lean.                               *)
(***************************************************************************)
EXTENDS Integers

\* GUARD: TRUE is the code (the packet behind the handshake ends at the path's size), FALSE the rule before #554.
CONSTANT GUARD

\* IFACE: TRUE is the code (a whole flight's room is the interface's payload), FALSE the rule before #584 (the
\* interface's MTU, headers included).
CONSTANT IFACE

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
\* The interface MTUs the host reports (IP and UDP headers included), below and above the first probe size.
Ifaces == {MinMtu, 1280, 1420, 1500, 9000}
\* The first flight with its framing (whole_len + FLIGHT_OVERHEAD): none, a resumed Hello, flights around the room of
\* a 1280-byte interface, the largest that goes whole, one byte above it.
Flights == {0, 149, 1269, 1388, ProbeMtu, ProbeMtu + 1}
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

\* One input of build_datagram: the path's size p, the interface MTU f, whether the path is IPv6 v6, the buffer o, the
\* amplification room a, the probe size q (0: none), the first flight with its framing fl (0: none, or whole flights
\* are off), and what each part would take.
Inputs == [p : PathSizes, f : Ifaces, v6 : BOOLEAN, o : Outs, a : Amps, q : Probes, fl : Flights,
           hs : HsWants, app : AppWants, pad : PadOweds]
\* The quick profile (quick/DgramSize*.cfg substitute it for Inputs): the same fields over fewer values, keeping the
\* floor and first probe paths, a 1280-byte and a 1500-byte interface, the buffer and amplification edges, both probes,
\* no flight, a resumed Hello, a flight around the 1280-byte room and one too large to go whole.
InputsQuick == [p : {MinMtu, ProbeMtu}, f : {1280, 1500}, v6 : BOOLEAN, o : {MinRoom - 1, 1300, 65536},
                a : {MinRoom, 1250, 1000000}, q : Probes, fl : {0, 149, 1269, ProbeMtu + 1},
                hs : {0, 149, 1269, ProbeMtu}, app : {0, 30, 9000}, pad : PadOweds]
\* probe_size returns a probe only above the path's size (Mtu::target) and only when the buffer holds it.
Valid(i) == i.q = 0 \/ (i.q > i.p /\ i.q <= i.o)

\* `interface_payload`: the largest UDP payload the interface carries on the path's family (IPv4 headers 28, IPv6 48).
Room(i) == Max(i.f - (IF i.v6 THEN 48 ELSE 28), 0)
\* The room a whole flight is given: the interface's payload (the code), or its MTU (the rule before #584).
IfaceRoom(i) == IF IFACE THEN Room(i) ELSE i.f
\* `whole`: the first flight goes whole when it fits 1452 bytes and the interface's room.
W(i) == i.fl > 0 /\ i.fl <= Min(ProbeMtu, IfaceRoom(i))
\* `base`: a whole flight may take the larger of the path's size and 1452 (or the interface's room when smaller).
Base(i) == IF W(i) THEN Max(i.p, Min(ProbeMtu, IfaceRoom(i))) ELSE i.p
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
          \/ W(x) /\ Pkt(GUARD, x) = 0 /\ Len(GUARD, x) <= Base(x)
\* A datagram above the path's size that is not a probe (a whole flight) is no larger than the interface carries on the
\* path's family, so the link does not drop it. DgramSize_noiface must find it violated.
IfaceOK == (x.q = 0 /\ Len(GUARD, x) > x.p) => Len(GUARD, x) <= Room(x)
\* Never past the buffer or the amplification room.
Bounded == Len(GUARD, x) <= Min(x.o, x.a)
\* The guard changes nothing but a whole flight's datagram: every other datagram is the one of the rule before #554.
Unchanged == ~W(x) => Len(GUARD, x) = Len(FALSE, x) /\ Pkt(GUARD, x) = Pkt(FALSE, x)
\* Negated for a witness: with the guard a packet still rides behind a whole flight's fragment, so AppFits is not
\* vacuous. DgramSize_reach must find it violated.
Coalesced == ~(W(x) /\ Hs(x) > 0 /\ Pkt(GUARD, x) > 0)
=============================================================================
