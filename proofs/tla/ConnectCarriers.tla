---------------------------- MODULE ConnectCarriers ----------------------------
(***************************************************************************)
(* Model check of the life of a relay slot's carrier (ConnectCarriersOps,  *)
(* pinc-connect src/client/carriers.rs) under a host that keeps the       *)
(* contract the layer documents and the hosts in the tree keep             *)
(* (tests/support/connect_client.rs, pinc-sim suite/node/carrier.rs): it   *)
(* takes the stream requests after every call, in order; it opens a stream *)
(* for Io::Open and reports it opened (stream_opened) or closed            *)
(* (stream_closed) once; on Io::Close it forgets the stream and reports    *)
(* nothing more of it.                                                      *)
(*                                                                         *)
(* What goes wrong underneath: a stream kind that never opens (Broken: its *)
(* connect fails or its handshake never completes), both kinds broken (the *)
(* only node carrying the relay role at that slot is gone), a relay with  *)
(* no stream address (addr "udp"), a stream the network ends at any time,  *)
(* a carrier that ends mid-message (a record cut or altered), a handshake  *)
(* that answers with another identity, a lease reset before a send, a held *)
(* queue that overflows, a close for a suspension at any time.            *)
(*                                                                         *)
(* Properties (the module documentation of client/conn.rs and the doc     *)
(* comments of carriers.rs):                                                *)
(*  StreamOnLiveLink  a stream is open only for a relay whose link is not *)
(*                    Down (conn.rs invariant)                             *)
(*  OpenMatches       the link is open exactly while the carrier is open  *)
(*                    ("a link is open only after the carrier opened")     *)
(*  OneStream         a stream is asked for only when the host holds none *)
(*                    for the slot                                         *)
(*  DialKind          "a failed dial changes the stream kind for the next *)
(*                    one": a dial that never opened is followed by one of *)
(*                    the other kind, one that opened by the same kind,    *)
(*                    whichever of the three paths ended it                *)
(*  FailsCounted      every dial that never opened is reported to the      *)
(*                    relay's health once ("A relay whose carrier dials   *)
(*                    never opened ... three times in a row is unhealthy") *)
(*  NoticesAlternate  CarrierUp and CarrierDown alternate, Up first, and   *)
(*                    the last one says whether the link is open           *)
(*  SameCarrier       sealed bytes leave only on the carrier that sealed  *)
(*                    them (a close drops what it had not handed over)     *)
(*  HeldBound         the held queue never exceeds its capacity           *)
(*  HeldFirst         "What waited for the carrier goes out first, in     *)
(*                    order" (carrier_open): no packet routed after the   *)
(*                    carrier opened leaves before one held when it opened *)
(*  NoCarrierDown     the link of a relay with no carrier stays Down and   *)
(*                    holds nothing: no dial site moves it to Dialing     *)
(* Witnesses (TLC must violate): ConnectCarriers_w_open (NoFallbackOpen: a *)
(* carrier opens after a failed dial of the other kind). _w_slow checks   *)
(* HeldFirst on a very slow node (with fix K4 a packet sent while the      *)
(* drain is due is held behind the others; before it, TLC found HeldFirst  *)
(* violated there). _slow checks every property on a very slow node and on *)
(* a slot with no stream address.                                          *)
(***************************************************************************)
EXTENDS ConnectCarriersOps, TLC

CONSTANTS Addrs, Brokens, Slow, Cap, MaxPkts, MaxGen

VARIABLES c, hs, np, addr, broken, up, ups, badN, lastDial, lastUp, badK, badS, first, early
vars == <<c, hs, np, addr, broken, up, ups, badN, lastDial, lastUp, badK, badS, first, early>>

cf == [addr |-> addr, cap |-> Cap, slow |-> Slow]
NoStream == [st |-> "none", kind |-> "none"]

Init == /\ c = NewC /\ hs = NoStream /\ np = 0 /\ addr \in Addrs /\ broken \in Brokens
        /\ up = FALSE /\ ups = 0 /\ badN = FALSE /\ lastDial = "none" /\ lastUp = FALSE /\ badK = FALSE
        /\ badS = FALSE /\ first = {} /\ early = FALSE

(* the host takes the requests in order *)
RECURSIVE TakeIo(_, _, _)
TakeIo(h, io, bad) ==
    IF io = <<>> THEN [h |-> h, bad |-> bad]
    ELSE LET r == Head(io) IN
         IF r.op = "open" THEN TakeIo([st |-> "conn", kind |-> r.kind], Tail(io), bad \/ h.st # "none")
         ELSE TakeIo(NoStream, Tail(io), bad)

RECURSIVE Notes(_, _, _, _)
Notes(u, n, bad, nt) ==
    IF nt = <<>> THEN [u |-> u, n |-> n, bad |-> bad]
    ELSE IF Head(nt) = "up" THEN Notes(TRUE, n + 1, bad \/ u, Tail(nt))
    ELSE Notes(FALSE, n, bad \/ ~u, Tail(nt))

(* the dial kind the documented rule wants after the last dial *)
Want(ld, lu) == IF ld = "none" THEN "tcp" ELSE IF lu THEN ld ELSE Other(ld)

(* apply the result W of a layer call made while the host held h *)
Step(W, h) ==
    LET t == TakeIo(h, W.io, badS)
        n == Notes(up, ups, badN, W.nt)
        opens == SelectSeq(W.io, LAMBDA r : r.op = "open")
        upNow == \E k \in 1..Len(W.nt) : W.nt[k] = "up"
        f == IF upNow THEN SetOf(c.held) ELSE first \cap SetOf(W.c.held)
        newOut == Ids(W.c.out) \ Ids(c.out)
    IN /\ c' = W.c /\ hs' = t.h /\ badS' = t.bad
       /\ up' = n.u /\ ups' = n.n /\ badN' = n.bad
       \* at most one open per call (a close comes between two); the rule is checked on it
       /\ IF opens = <<>> THEN /\ lastDial' = lastDial /\ lastUp' = (lastUp \/ upNow) /\ badK' = badK
          ELSE /\ lastDial' = opens[1].kind /\ lastUp' = upNow
               /\ badK' = (badK \/ Len(opens) > 1 \/ opens[1].kind # Pick(Want(lastDial, lastUp), addr))
       /\ first' = f
       /\ early' = (early \/ ((\E q \in newOut : q \notin f) /\ f \cap SetOf(W.c.held) # {}))
       /\ UNCHANGED <<addr, broken>>

Route == /\ np < MaxPkts
         /\ \E bs \in BOOLEAN, wd \in BOOLEAN :
              /\ (bs => c.link = "open") /\ (wd => c.link # "open")
              /\ Step(SendPacket(W0(c), np + 1, bs, wd, cf), hs)
         /\ np' = np + 1

Tick == \E d \in TickChoices(c.link) : Step(TickStep(W0(c), d, cf), hs) /\ UNCHANGED np

Drive == /\ c.due
         /\ \E d \in TickChoices(c.link), wd \in BOOLEAN : Step(DriveStep(W0(c), d, wd, cf), hs) /\ UNCHANGED np

Opened == /\ hs.st = "conn" /\ c.car = "none"
          /\ \E ok \in BOOLEAN : Step(StreamOpened(W0(c), ok), [hs EXCEPT !.st = "up"]) /\ UNCHANGED np

Gone == /\ hs.st # "none" /\ Step(StreamClosed(W0(c)), NoStream) /\ UNCHANGED np

Handshake == /\ c.car = "hs" /\ hs.st = "up"
             /\ \E right \in BOOLEAN : /\ (right => hs.kind \notin broken)
                                       /\ Step(HsDone(W0(c), right, cf), hs)
             /\ UNCHANGED np

Fatal == /\ c.car # "none" /\ Step(Dead(W0(c)), hs) /\ UNCHANGED np

Poll == /\ c.out # <<>> /\ Step(PollStream(W0(c), cf).w, hs) /\ UNCHANGED np

Suspend == /\ c.link # "down" /\ Step(ClosePub(W0(c)), hs) /\ UNCHANGED np

Next == Route \/ Tick \/ Drive \/ Opened \/ Gone \/ Handshake \/ Fatal \/ Poll \/ Suspend

Spec == Init /\ [][Next]_vars

Bound == c.gen <= MaxGen

StreamOnLiveLink == c.car # "none" => c.link # "down"
OpenMatches == (c.link = "open") <=> (c.car = "open")
OneStream == ~badS
DialKind == ~badK
FailsCounted == c.fails = c.gen - ups - (IF c.link = "dialing" THEN 1 ELSE 0)
NoCarrierDown == ~HasCarrier(cf) => c.link = "down" /\ c.held = <<>> /\ c.gen = 0
NoticesAlternate == ~badN /\ (up <=> c.link = "open")
SameCarrier == \A k \in 1..Len(c.out) : c.out[k].g = c.gen
HeldBound == Len(c.held) <= Cap
HeldFirst == ~early

\* reachability
NoFallbackOpen == ~(c.link = "open" /\ c.fails >= 1)

\* the constant sets of the configs
AddrsFallback == {"both", "tcp"}
AddrsAll == {"both", "tcp", "ws", "udp"}
AddrsBoth == {"both"}
BrokensAll == {{}, {"tcp"}, {"tcp", "ws"}}
BrokensTcp == {{"tcp"}}
BrokensNone == {{}}
=============================================================================
