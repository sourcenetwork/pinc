---------------------------- MODULE ConnectMappedOps ----------------------------
(***************************************************************************)
(* The port mappings the connectivity layer holds (pinc-connect            *)
(* client/mapped.rs: set_mapped, refresh_mapped, candidates, with the      *)
(* parts of conn.rs update_class and timers.rs link_changed and resume     *)
(* that drive them) as pure operators. ConnectMapped.tla (the model check) *)
(* and TraceConnectMapped.tla (the trace validation) use them.             *)
(*                                                                         *)
(* An address is <<ip, port>> with ip the four octets of an IPv4 address;  *)
(* NOA (the empty sequence) is no address. The classification is          *)
(* netcheck::classify as ConnectClientOps.tla has it (0 none, 1 Public, 2  *)
(* PortMapped, 3 Nat, 4 Cgnat, 5 UdpBlocked), with `quiet` standing for    *)
(* "no UDP heard and the watchdog has run out since the first probe". The  *)
(* node state S is                                                         *)
(*   mapped    self.mapped, the two mapping slots                          *)
(*   refl      the reflexive address each relay reported (Netcheck)        *)
(*   live      self.live, the mapped addresses a relay vouched for at the  *)
(*             last refresh                                                *)
(*   cls       self.class; unmapped  self.unmapped                         *)
(*   local     the node's own addresses (set_local)                        *)
(* Each operation returns the new state with what it did: want (the record *)
(* was asked for again, sign.want_record), fb (the class fell back from    *)
(* PortMapped) and pub (next_publish was set to now).                      *)
(* Not modelled: IPv6 and to_canonical (the addresses here are IPv4, where *)
(* to_canonical is the identity); the notices themselves.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CC == INSTANCE ConnectClientOps

NOA == <<>>
MAXADDRS == 8

Some1(a) == a # NOA
Flat(s) == SelectSeq(s, Some1)
InSeqA(s, v) == \E i \in 1..Len(s) : s[i] = v

(* append the elements not yet listed, while fewer than cap are *)
RECURSIVE DedupCap(_, _, _)
DedupCap(s, acc, cap) == IF s = <<>> THEN acc
                         ELSE DedupCap(Tail(s), IF Len(acc) < cap /\ ~InSeqA(acc, Head(s)) THEN Append(acc, Head(s)) ELSE acc, cap)

New(local, r) == [mapped |-> <<NOA, NOA>>, refl |-> [i \in 1..r |-> NOA], live |-> <<NOA, NOA>>, cls |-> 0, unmapped |-> 0,
                  local |-> SubSeq(local, 1, IF Len(local) < MAXADDRS THEN Len(local) ELSE MAXADDRS)]

(* Netcheck::reflexive_into into a buffer of MAX_ADDRS: the distinct reflexive addresses in relay order *)
ReflList(S) == DedupCap(Flat(S.refl), <<>>, MAXADDRS)

(* netcheck::mapped_seen: a relay saw the node at the mapping's IP *)
Seen(rl, m) == \E i \in 1..Len(rl) : rl[i][1] = m[1]

(* Connectivity::live_of *)
LiveOf(S, rl) == [j \in 1..2 |-> IF S.mapped[j] # NOA /\ Seen(rl, S.mapped[j]) THEN S.mapped[j] ELSE NOA]
AnyLive(l) == l[1] # NOA \/ l[2] # NOA

Did(S, w, f, p) == [s |-> S, want |-> w, fb |-> f, pub |-> p]

(* Connectivity::refresh_mapped *)
Refresh(S) ==
    LET live == LiveOf(S, ReflList(S))
    IN IF live = S.live THEN Did(S, FALSE, FALSE, FALSE)
       ELSE LET fb == AnyLive(S.live) /\ S.cls = 2 /\ ~AnyLive(live)
            IN Did([S EXCEPT !.live = live, !.cls = IF fb THEN S.unmapped ELSE S.cls], TRUE, fb, fb)

Classify(S, mapped, quiet) == CC!Classify(Flat(S.local), ReflList(S), mapped, ~quiet, 1, 1)

(* Connectivity::update_class *)
UpdateClass(S, quiet) ==
    LET r == Refresh(S)
        S1 == r.s
        cls == Classify(S1, Flat(S1.mapped), quiet)
        um == IF cls = 2 THEN Classify(S1, <<>>, quiet) ELSE S1.unmapped
        chg == cls # S1.cls /\ cls # 0
    IN Did([S1 EXCEPT !.unmapped = um, !.cls = IF chg THEN cls ELSE S1.cls], r.want, r.fb, r.pub \/ chg)

(* Connectivity::set_mapped: the first two addresses; the same pair changes nothing *)
SetMapped(S, addrs, quiet) ==
    LET m == <<IF Len(addrs) >= 1 THEN addrs[1] ELSE NOA, IF Len(addrs) >= 2 THEN addrs[2] ELSE NOA>>
    IN IF m = S.mapped THEN Did(S, FALSE, FALSE, FALSE) ELSE UpdateClass([S EXCEPT !.mapped = m], quiet)

(* a QADR answer from relay i (Netcheck::answered), then after_answer's update_class *)
Answer(S, i, a) == UpdateClass([S EXCEPT !.refl[i] = a], FALSE)

(* link_changed and resume: Netcheck::restart forgets every reflexive address, then refresh_mapped *)
Restart(S) == Refresh([S EXCEPT !.refl = [k \in DOMAIN S.refl |-> NOA]])

(* tick's update_class *)
Tick(S, quiet) == UpdateClass(S, quiet)

(* Connectivity::candidates: the vouched mapped addresses, the reflexive ones, the local ones, distinct, at most 8 *)
Cands(S) == LET rl == ReflList(S) IN DedupCap(Flat(LiveOf(S, rl)) \o rl \o Flat(S.local), <<>>, MAXADDRS)
=============================================================================
