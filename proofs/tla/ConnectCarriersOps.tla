-------------------------- MODULE ConnectCarriersOps --------------------------
(***************************************************************************)
(* The life of one relay slot's carrier in pinc-connect                     *)
(* src/client/carriers.rs, as pure operators: start_dial, act (the Dial and *)
(* Close answers of the link), close_stream, close_stream_quiet,           *)
(* send_packet, drain_held, carrier_open, stream_opened, stream_closed,    *)
(* poll_stream, the follow-up of a very slow node (drive.rs               *)
(* carrier_follow_up) and the close of a suspension (signing.rs           *)
(* close_for_suspend through close_pub). ConnectCarriers.tla (the model   *)
(* check) and TraceConnectCarriers.tla (the trace validation) use them.     *)
(*                                                                         *)
(* The slot is the node that carries the relay role at that position of   *)
(* the node's configuration: an ordinary node or one deployed from the     *)
(* relay binary, the code does not tell them apart.                         *)
(*                                                                         *)
(* A call is a function of W = [c, io, nt]: c the slot, io the stream      *)
(* requests the call queued for the host (Io::Open with its kind,         *)
(* Io::Close), nt the carrier notices it raised ("up" CarrierUp, "down"    *)
(* CarrierDown). The slot c is                                              *)
(*   link    the state of client/link.rs: "down", "dialing", "open"        *)
(*   car     the ProtectedCarrier: "none", "hs" (handshaking), "open"      *)
(*   kind    the stream kind of the next dial: "tcp" or "ws" (Kind)        *)
(*   gen     Rly::generation, one per Io::Open                              *)
(*   held    the packets held while the carrier is not open (ids, oldest   *)
(*           first); a push onto a full queue drops the oldest (queue.rs,   *)
(*           its own model; cap here is a count)                            *)
(*   out     the sealed packets not yet handed to the host, each with the  *)
(*           generation of the carrier that sealed it                       *)
(*   due     Rly::drain_due (the held packets wait for the endpoint's view) *)
(*   fails   the calls of dial_failed (the relay's health, netcheck.rs)    *)
(*   dropped the packets dropped: held ones as the oldest, or with no     *)
(*           carrier to send on                                            *)
(*                                                                         *)
(* The link's timing is ConnectLink.tla's (proved there); here each answer *)
(* the link can give in its state is a parameter of the call: the tick's   *)
(* acts (d), before_send's reset (bs) and want_dial's dial (wd). The       *)
(* carrier's own byte handling is ConnectCarrier.tla's; here the handshake *)
(* ends with the configured relay's identity, another one, or a fatal      *)
(* error, as a parameter. Frames other than packets (PING, PONG, PUBLISH,  *)
(* DNS) are not tracked. The write buffer (OUT_LEN, 24 KiB) always has     *)
(* room: the path where a full buffer refuses a frame is not modelled.     *)
(* cf = [addr, cap, slow]: addr the stream addresses the relay is          *)
(* configured with ("both", "tcp", "ws", or "udp" for neither), cap the    *)
(* held queue's capacity, slow the very slow node of carrier_open          *)
(* (node_rtt >= TG_SLOW and node_tgr >= DEDUPE_PEAK_RTT). The thinning of   *)
(* a slow node (trim_held, KEPT_SHORT = 8) never drops a packet at the     *)
(* sizes checked here (at most 8 short packets held) and is left out.     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

Other(k) == IF k = "tcp" THEN "ws" ELSE "tcp"

(* start_dial: the kind for the slot's kind and the configured addresses, "none" when neither address is there *)
Pick(k, addr) ==
    CASE k = "tcp" /\ addr \in {"tcp", "both"} -> "tcp"
      [] (k = "ws" /\ addr \in {"ws", "both"}) \/ addr = "ws" -> "ws"
      [] addr = "tcp" -> "tcp"
      [] OTHER -> "none"

NewC == [link |-> "down", car |-> "none", kind |-> "tcp", gen |-> 0, held |-> <<>>, out |-> <<>>, due |-> FALSE,
         fails |-> 0, dropped |-> 0]
W0(c) == [c |-> c, io |-> <<>>, nt |-> <<>>]

OpenIo(k) == [op |-> "open", kind |-> k]
CloseIo == [op |-> "close", kind |-> "none"]

StartDial(W, cf) ==
    LET k == Pick(W.c.kind, cf.addr) IN
    IF k = "none" THEN W
    ELSE [W EXCEPT !.c.kind = k, !.c.gen = @ + 1, !.io = Append(@, OpenIo(k))]

(* has_carrier: a stream address is configured; a relay reached over UDP only has none *)
HasCarrier(cf) == cf.addr # "udp"

(* want_dial answered Dial: the link is dialing, then act(Dial); the link of a relay with no carrier is never asked
   (Connectivity::want_dial, and tick skips the relay), so it stays as it is *)
LinkDial(W, cf) == IF HasCarrier(cf) THEN StartDial([W EXCEPT !.c.link = "dialing"], cf) ELSE W

(* dial_failed: net.failed; the failover it may start moves the home to another slot (ConnectClient.tla) *)
DialFailed(W) == [W EXCEPT !.c.fails = @ + 1]

(* close_stream: the carrier is dropped, a dial that had not opened changes the kind and counts as failed, an open
   link or carrier raises CarrierDown, and the host is asked to close the stream *)
CloseStream(W) ==
    LET was == W.c.link
        down == was = "open" \/ W.c.car = "open"
        df == was = "dialing"
        W1 == [W EXCEPT !.c.kind = IF df THEN Other(@) ELSE @, !.c.link = "down", !.c.car = "none", !.c.out = <<>>,
                        !.nt = IF down THEN Append(@, "down") ELSE @]
        W2 == IF df THEN DialFailed(W1) ELSE W1
    IN [W2 EXCEPT !.io = Append(@, CloseIo)]

(* act(Close): the link already set itself down (the dial watchdog, a failed check, a lease reset); a carrier that is
   not open is a dial that never opened *)
ActClose(W) ==
    IF W.c.car # "open" THEN CloseStream(DialFailed([W EXCEPT !.c.kind = Other(@)])) ELSE CloseStream(W)

(* tick: the acts the link can answer in each state, as the up to four rounds of the tick loop combine them *)
TickChoices(l) ==
    CASE l = "down" -> {"none", "dial"}
      [] l = "dialing" -> {"none", "watchdog", "watchdog_dial"}
      [] l = "open" -> {"none", "check", "reset", "reset_dial"}

TickStep(W, d, cf) ==
    CASE d = "dial" -> LinkDial(W, cf)
      [] d \in {"watchdog", "reset"} -> ActClose([W EXCEPT !.c.link = "down"])
      [] d \in {"watchdog_dial", "reset_dial"} -> LinkDial(ActClose([W EXCEPT !.c.link = "down"]), cf)
      [] OTHER -> W

Hold(c, p, cap) ==
    IF Len(c.held) < cap THEN [c EXCEPT !.held = Append(@, p)]
    ELSE [c EXCEPT !.held = Append(Tail(@), p), !.dropped = @ + 1]

Sealed(c, ps) == [k \in 1..Len(ps) |-> [p |-> ps[k], g |-> c.gen]]

(* send_packet: a relay with no carrier drops the packet (counted) and holds nothing; before_send may reset an open
   link (bs), an open link takes the packet unless a drain is due (fix K4: then it is held behind the others),
   otherwise it is held and the link may dial (wd) *)
SendPacket(W, p, bs, wd, cf) ==
    IF ~HasCarrier(cf) THEN [W EXCEPT !.c.dropped = @ + 1] ELSE
    LET W1 == IF bs /\ W.c.link = "open" THEN ActClose([W EXCEPT !.c.link = "down"]) ELSE W IN
    IF W1.c.link = "open" /\ ~W1.c.due THEN [W1 EXCEPT !.c.out = Append(@, [p |-> p, g |-> W1.c.gen])]
    ELSE LET W2 == [W1 EXCEPT !.c = Hold(@, p, cf.cap)] IN
         IF wd /\ W2.c.link = "down" THEN LinkDial(W2, cf) ELSE W2

(* drain_held: every held packet through send_packet, oldest first; on an open link all leave, otherwise each goes
   back behind the others (the order is kept) and the link may dial *)
DrainHeld(W, wd, cf) ==
    IF W.c.link = "open" THEN [W EXCEPT !.c.out = @ \o Sealed(W.c, W.c.held), !.c.held = <<>>]
    ELSE IF wd /\ W.c.link = "down" /\ W.c.held # <<>> THEN LinkDial(W, cf)
    ELSE W

(* carrier_open: the link opens, CarrierUp, and what waited goes out, unless the node is very slow: then the drain
   waits for the next drive *)
CarrierOpen(W, cf) ==
    LET W1 == [W EXCEPT !.c.link = "open", !.c.car = "open", !.nt = Append(@, "up")] IN
    IF cf.slow THEN [W1 EXCEPT !.c.due = TRUE] ELSE DrainHeld(W1, FALSE, cf)

(* stream_opened: ProtectedCarrier::dial succeeded (ok) or failed *)
StreamOpened(W, ok) == IF ok THEN [W EXCEPT !.c.car = "hs", !.c.out = <<>>] ELSE CloseStream(W)

(* drive_carrier or after_poll_state saw the handshake open: with the configured relay's identity (right) or another *)
HsDone(W, right, cf) == IF right THEN CarrierOpen(W, cf) ELSE CloseStream(W)

(* a fatal error of the carrier (a record cut or altered, a failed key answer, a fatal seal): Got::Dead *)
Dead(W) == CloseStream(W)

(* close_stream_quiet: the network ended the stream; no close request goes back *)
CloseQuiet(W) ==
    LET was == W.c.link
        W1 == [W EXCEPT !.c.car = "none", !.c.out = <<>>, !.c.kind = IF was # "open" THEN Other(@) ELSE @,
                        !.c.link = "down"]
    IN IF was = "open" THEN [W1 EXCEPT !.nt = Append(@, "down")] ELSE DialFailed(W1)

(* stream_closed *)
StreamClosed(W) == IF W.c.link = "down" THEN [W EXCEPT !.c.car = "none"] ELSE CloseQuiet(W)

(* poll_stream: the host takes what was sealed; room was made, so packets held while the carrier was open go in *)
PollStream(W, cf) ==
    LET sent == W.c.out
        W1 == [W EXCEPT !.c.out = <<>>]
        W2 == IF Len(sent) > 0 /\ W1.c.held # <<>> /\ W1.c.link = "open" /\ ~W1.c.due THEN DrainHeld(W1, FALSE, cf) ELSE W1
    IN [w |-> W2, sent |-> [k \in 1..Len(sent) |-> sent[k].p]]

(* carrier_follow_up of drive: the drain a very slow node deferred (the thinning is left out, see the header) *)
FollowUp(W, wd, cf) == IF W.c.due THEN DrainHeld([W EXCEPT !.c.due = FALSE], wd, cf) ELSE W

(* drive: tick first, then the follow-up *)
DriveStep(W, d, wd, cf) == FollowUp(TickStep(W, d, cf), wd, cf)

(* close_for_suspend through close_pub: every slot whose link is not down *)
ClosePub(W) == IF W.c.link # "down" THEN CloseStream(W) ELSE W

Ids(s) == {s[k].p : k \in 1..Len(s)}
SetOf(s) == {s[k] : k \in 1..Len(s)}
=============================================================================
