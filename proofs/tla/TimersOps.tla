------------------------------ MODULE TimersOps ------------------------------
(***************************************************************************)
(* The timers and the closing state of the PINCER connection, step for     *)
(* step: pinc-transport conn/timer.rs (poll_timeout, handle_timeout),      *)
(* conn/life.rs (close, sleep, wake, the link outage, the idle deadline,   *)
(* the three ends) and the parts of conn/send.rs and conn/recv.rs that     *)
(* touch them (the CLOSE packet, the last send, SLEEP leaving, a packet    *)
(* heard, SLEEP and CLOSE applied). Timers.tla checks them over every      *)
(* interleaving at small sizes; TraceTimers.tla replays the recorded calls *)
(* of a scripted pair of real connections.                                 *)
(*                                                                         *)
(* The state s: ph (the phase: "hs" handshaking, "conn" connected,         *)
(* "closing" with its CLOSE still to leave, "closed"), close (the code of  *)
(* the CLOSE to send, None for none), co (the host asked for a datagram    *)
(* since the close began, so the CLOSE was offered to it, whether or not   *)
(* it could be written), keys (the 1-RTT sending keys are                  *)
(* installed), act (when the peer was last heard or the connection last    *)
(* resumed), sent (when a datagram last left), ka (the keepalive interval),*)
(* pa (since when the peer announced its sleep), la (this endpoint         *)
(* sleeps), stx (SLEEP frames still to send), wd (when an unanswered WAKE  *)
(* is reported) and ld (since when the link is down). None is -1.          *)
(*                                                                         *)
(* The deadlines of the other components are inputs, c: conf (the         *)
(* handshake is confirmed), hs (its retransmit deadline), rekey (the REKEY *)
(* request resent), rec (loss recovery: the loss time or the probe         *)
(* timeout), ack (the acknowledgement due), amp (the active path may still *)
(* be sent 64 bytes), rr and kr (a REKEY request, a PING, can be written: *)
(* the send ring and the active path have room for the smallest datagram   *)
(* that carries it; the REKEY request and the keepalive deadlines are each *)
(* offered only under its own gate, so a deadline that cannot be acted on  *)
(* never keeps the host polling), paced (the pacer's release),             *)
(* path (path probes and idle-out) and mtu (the MTU retry and black-hole   *)
(* suspicion). Their own                                                   *)
(* rules are proved in their own models (TransportRecovery*, TransportCc*, *)
(* TransportRx*, TransportMtu); here they are opaque. So are the decisions *)
(* the components take inside a call: a close a component decides in      *)
(* handle_timeout (cc: "dead" when recovery gives up, "hs" when the        *)
(* handshake runs out of time, "unconf" when a dialing side that           *)
(* established heard no 1-RTT packet from its peer within the connect      *)
(* limit after that, conn/drive.rs pump), whether poll_transmit wrote a    *)
(* datagram and how many SLEEP frames are left after it.                   *)
(*                                                                         *)
(* A probe timeout may also close the session behind a live carrier       *)
(* (dead_behind_live_carrier, conn/timer.rs). Its inputs are pr: ping (a   *)
(* probe timeout fired in this call), relay (the active path is a relay    *)
(* path), ch (when the relay's carrier last heard anything, None for none),*)
(* pto (probe timeouts in a row), lh (when the peer was last heard), smp   *)
(* (the round trip has a sample), sr (its smoothed value) and nd (the      *)
(* node's longest round trip, 0 for none). The recovery component's own    *)
(* rules are proved in TransportRecovery*; here pr is read as given.       *)
(*                                                                         *)
(* k holds the constants: idle (IDLE_TIMEOUT, 75 s), hold (SLEEP_HOLD,     *)
(* 120 s), wake (WAKE_WAIT, 800 ms), ldm (LINK_DOWN_MAX, 30 s), cf         *)
(* (CARRIER_FRESH, 6 s) and ir (INITIAL_RTT, 333 ms).                      *)
(* Every operation returns the new state and the events it reports, a     *)
(* sequence of "local", "peer", "viol", "idle", "dead", "hs", "unconf"     *)
(* (the reasons of Event::Closed), "asleep", "awake" and "unanswered".     *)
(***************************************************************************)
EXTENDS Integers, Sequences

None == -1
Mn(a, b) == IF a < b THEN a ELSE b
Mx(a, b) == IF a > b THEN a ELSE b
\* `add` of poll_timeout: fold a deadline into the minimum
AddD(t, x) == IF x = None THEN t ELSE Mn(t, x)
Plus(x, d) == IF x = None THEN None ELSE x + d

Open(s) == s.ph \in {"hs", "conn"}

\* idle_deadline: 75 s after the peer was last heard, or 120 s after it announced its sleep
Idle(s, k) == IF s.pa = None THEN s.act + k.idle ELSE Mx(s.act + k.idle, s.pa + k.hold)
\* nothing can leave: the link is down, or this endpoint sleeps and its SLEEP frames left
Suspended(s) == s.ld # None \/ (s.la /\ s.stx = 0)
LinkEnd(s, k) == Plus(s.ld, k.ldm)
KeepDue(s) == IF s.ka = None THEN None ELSE s.sent + s.ka

\* poll_timeout, step for step (bug: a deliberately wrong rule for the witness configs, "none" for the code)
PollB(s, c, k, bug) ==
    IF s.ph = "closed" THEN None
    ELSE IF s.ph = "closing" THEN 0
    ELSE IF Suspended(s)
         THEN LET t1 == AddD(Idle(s, k), LinkEnd(s, k))
                  t2 == IF bug = "nowake" THEN t1 ELSE AddD(t1, s.wd)
              IN IF s.ld # None THEN AddD(t2, c.rec) ELSE t2
         ELSE LET t1 == IF ~c.conf THEN AddD(Idle(s, k), c.hs) ELSE Idle(s, k)
                  t2 == AddD(AddD(t1, IF c.rr THEN c.rekey ELSE None), c.rec)
                  t3 == IF c.amp THEN AddD(t2, c.ack) ELSE t2
                  t4 == AddD(AddD(AddD(AddD(t3, c.paced), c.path), s.wd), LinkEnd(s, k))
              IN IF s.ph = "conn" THEN AddD(AddD(t4, IF c.kr THEN KeepDue(s) ELSE None), c.mtu) ELSE t4
Poll(s, c, k) == PollB(s, c, k, "none")

Silent(s) == [s EXCEPT !.ph = "closed", !.close = None]

\* begin_close: one CLOSE is to leave if the connection was established with sending keys; otherwise it is over at once.
\* The CLOSE has not been offered to the host yet.
BeginClose(s, err, why) ==
    IF ~Open(s) THEN [s |-> s, ev |-> <<>>]
    ELSE [s |-> [s EXCEPT !.close = err, !.co = FALSE, !.ph = IF s.ph = "conn" /\ s.keys THEN "closing" ELSE "closed"],
          ev |-> <<why>>]

\* the round trip dead_behind_live_carrier reads: the smoothed one, or before a sample the larger of INITIAL_RTT and
\* twice the node's longest round trip
Rtt(pr, k) == IF pr.smp THEN pr.sr ELSE Mx(k.ir, 2 * pr.nd)
\* dead_behind_live_carrier (bug: a deliberately wrong rule for the witness configs, "none" for the code): the active
\* path is a relay path, its carrier was heard within CARRIER_FRESH, 4 probe timeouts fired in a row and nothing was
\* heard for 4 round trips (saturating differences)
CarrierB(now, pr, k, bug) ==
    /\ (bug = "norelay" \/ pr.relay)
    /\ (bug = "nofresh" \/ (pr.ch # None /\ Mx(now - pr.ch, 0) < k.cf))
    /\ pr.pto >= 4
    /\ Mx(now - pr.lh, 0) >= 4 * Rtt(pr, k)
Carrier(now, pr, k) == CarrierB(now, pr, k, "none")

\* handle_timeout: a closing connection ends once its CLOSE was offered to the host or it has none to send, and until
\* then waits (the grace of the endpoint, CLOSE_GRACE in pinc-core, only decides when the timer runs; bug = "grace" is
\* the rule before the fix: it ends at its next timer, so a host held up past the grace before it asked for a datagram
\* never sends the CLOSE); past the idle deadline the connection ends silently and nothing else
\* runs; otherwise the handshake timer (it may end a handshaking connection whose handshake ran out of time, and a
\* connected one whose peer never confirmed the session, each silently), the end of a link outage, the recovery timer
\* and the wake wait, in this order. The recovery timer ends the connection silently when the path is dead
\* (cc = "dead"); otherwise, at a probe timeout behind a live carrier, it begins a close with a CLOSE (reason
\* PathDead, error 0), which is a no-op on a connection that already ended. bug = "nounconf" is the rule before
\* #390: the handshake timer ends only a handshaking connection
TimeoutB(s, now, cc, pr, k, bug) ==
    IF s.ph = "closed" THEN [s |-> s, ev |-> <<>>]
    ELSE IF s.ph = "closing"
         THEN [s |-> IF bug = "grace" \/ s.close = None \/ s.co THEN [s EXCEPT !.ph = "closed"] ELSE s, ev |-> <<>>]
    ELSE IF now >= Idle(s, k) THEN [s |-> Silent(s), ev |-> <<"idle">>]
    ELSE LET h == IF cc = "hs" /\ s.ph = "hs" THEN [s |-> Silent(s), ev |-> <<"hs">>]
                  ELSE IF cc = "unconf" /\ s.ph = "conn" /\ bug # "nounconf" THEN [s |-> Silent(s), ev |-> <<"unconf">>]
                  ELSE [s |-> s, ev |-> <<>>]
             l == IF h.s.ld # None /\ h.s.ld + k.ldm <= now THEN [h.s EXCEPT !.ld = None] ELSE h.s
             b == BeginClose(l, 0, "dead")
             d == IF cc = "dead" THEN (IF l.ph # "closed" THEN [s |-> Silent(l), ev |-> h.ev \o <<"dead">>]
                                       ELSE [s |-> l, ev |-> h.ev])
                  ELSE IF pr.ping /\ CarrierB(now, pr, k, bug) THEN [s |-> b.s, ev |-> h.ev \o b.ev]
                  ELSE [s |-> l, ev |-> h.ev]
         IN IF d.s.wd # None /\ d.s.wd <= now THEN [s |-> [d.s EXCEPT !.wd = None], ev |-> d.ev \o <<"unanswered">>]
            ELSE d
Timeout(s, now, cc, pr, k) == TimeoutB(s, now, cc, pr, k, "none")

\* a datagram reached handle_datagram: heard (a packet authenticated and was new), and of its frames a SLEEP and
\* a CLOSE were applied. A closed or closing connection refuses it.
RecvB(s, now, heard, sleep, close, bug) ==
    IF ~Open(s) \/ ~heard THEN [s |-> s, ev |-> <<>>]
    ELSE LET s1 == [s EXCEPT !.act = IF bug = "noheard" THEN s.act ELSE now, !.wd = None,
                             !.pa = IF sleep THEN now ELSE None]
             e1 == IF sleep THEN <<"asleep">> ELSE <<>>
         IN IF close THEN [s |-> Silent(s1), ev |-> e1 \o <<"peer">>]
            ELSE [s |-> s1, ev |-> e1 \o (IF s.pa # None /\ ~sleep THEN <<"awake">> ELSE <<>>)]
Recv(s, now, heard, sleep, close) == RecvB(s, now, heard, sleep, close, "none")

\* frames that do not decode: a violation before anything is heard
Bad(s, err) == BeginClose(s, err, "viol")
\* a frame that breaks a rule: the packet was heard, the peer's sleep ended, then the violation (a closed or closing
\* connection refuses the datagram before its frames are read)
Viol(s, now, err) == IF ~Open(s) THEN [s |-> s, ev |-> <<>>]
                     ELSE BeginClose([s EXCEPT !.act = now, !.wd = None, !.pa = None], err, "viol")

Close(s, err) == BeginClose(s, err, "local")

\* What poll_transmit may write: nothing once closed, only the CLOSE while closing, nothing while suspended
CanSend(s) == IF s.ph = "closed" THEN FALSE ELSE IF s.ph = "closing" THEN s.close # None ELSE ~Suspended(s)
\* One poll_transmit call: sent says whether it wrote a datagram, stx is the SLEEP count after it. While closing with
\* a CLOSE to send, the call offers it (build_close), whether or not it could be written.
Tx(s, now, sent, stx) ==
    IF s.ph = "closed" THEN s
    ELSE IF s.ph = "closing"
         THEN IF s.close = None THEN [s EXCEPT !.ph = "closed"]
              ELSE IF sent THEN [s EXCEPT !.ph = "closed", !.close = None, !.sent = now, !.co = TRUE]
              ELSE [s EXCEPT !.co = TRUE]
    ELSE IF Suspended(s) THEN s
    ELSE [s EXCEPT !.sent = IF sent THEN now ELSE s.sent, !.stx = stx]
\* whether the call wrote the CLOSE
TxClose(s, sent) == s.ph = "closing" /\ s.close # None /\ sent

Resume(s, now, susp, k) == [s EXCEPT !.wd = IF susp THEN now + k.wake ELSE s.wd, !.act = now]
Sleep(s) == IF s.ph = "conn" /\ ~s.la THEN [s EXCEPT !.la = TRUE, !.stx = 2] ELSE s
Wake(s, now, k) == IF s.ph = "conn" /\ s.la THEN Resume([s EXCEPT !.la = FALSE], now, TRUE, k) ELSE s
\* set_link_down; a handshaking connection only tells its handshake about a return
Link(s, now, down, k) ==
    IF s.ph # "conn" THEN s
    ELSE IF down THEN [s EXCEPT !.ld = IF s.ld = None THEN now ELSE s.ld]
    ELSE IF s.ld # None THEN Resume([s EXCEPT !.ld = None], now, FALSE, k)
    ELSE s
Keepalive(s, ka) == [s EXCEPT !.ka = ka]
Pulse(s, now, sent) == [s EXCEPT !.act = now, !.sent = IF sent THEN now ELSE s.sent]
\* the handshake established the session: Event::Connected
Est(s, now) == IF s.ph = "hs" THEN [s EXCEPT !.ph = "conn", !.keys = TRUE, !.act = now] ELSE s
\* the application calls that take data (open, write, datagrams) are refused once the connection is closing
AppOpen(s) == Open(s)
=============================================================================
