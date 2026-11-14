------------------------------ MODULE FramePack ------------------------------
(***************************************************************************)
(* The VINCER packet builder (FramePackOps.tla, the operators that follow  *)
(* fill_frames, put_stream_header, implicit_stream_len and the tail of     *)
(* build_packet) checked on every combination of what the sources hold:    *)
(* each case is a state. A case gives the mode of the fill (an ordinary    *)
(* fill, the probe timeout's PING, a path MTU probe, a tail repair), the   *)
(* room of the payload, the least payload, the ACK pending, the control    *)
(* frames and path frames pending, the chunks the stream layer holds, the  *)
(* datagrams queued, the credit given back after an answer, and the        *)
(* switches (the sent ring has room, the window and the pacer allow data,  *)
(* a packet is forced, an ACK is due). A case of the other modes gives     *)
(* what build_app sees (the probe timeout owes packets, a path MTU probe   *)
(* is due, a tail repair is pending, the packet goes on the active path)   *)
(* and its mode is the one Pick gives; an ordinary fill is built with no   *)
(* repair pending.                                                         *)
(*                                                                         *)
(* The choice before the fill:                                             *)
(*   RepairKept the pending tail repair is taken exactly by a packet built *)
(*              as a repair (on the active path, no path MTU probe due,    *)
(*              no probe timeout's packet owed) and is otherwise left      *)
(*              pending: a repair due together with a path MTU probe or    *)
(*              the probe timeout's PING goes with the next packet.        *)
(*                                                                         *)
(* Properties of every packet the builder seals:                           *)
(*   HintRight  the place kept is the last frame, a STREAM frame with its  *)
(*              length whose data runs to the end of the fill, so          *)
(*              implicit_stream_len never refuses it and the ? of          *)
(*              build_packet never gives up a packet whose frames were     *)
(*              already taken from their owners;                           *)
(*   RoundTrip  the fill is the frames' encodings one after the other      *)
(*              (put_stream_header writes the header write gives), and the *)
(*              payload sealed is read by FrameIter, with no error, as the *)
(*              frames written in order, the last without its length when  *)
(*              it was dropped, then one PADDING frame for the padding;    *)
(*   LastOnly   a frame without a length is only the last one, a STREAM    *)
(*              frame, and never in a padded payload: the fill writes      *)
(*              every frame with its length;                               *)
(*   Order      the frames come in the order of fill_frames (Slots):       *)
(*              ACK, SLEEP, WAKE, MTU echo, READY, tickets, REKEY,         *)
(*              extension frames, credit and resets, PATH_RESPONSE, PING,  *)
(*              PATH_CHALLENGE, stream data, datagrams, then the credit an *)
(*              answered stream gives back and a forced PING; no PADDING   *)
(*              or CLOSE is written by a fill;                             *)
(*   Sizes      the payload sealed is the fill, the fill padded to the     *)
(*              least payload, or the fill less the bytes of the length    *)
(*              dropped, and never more than the room.                     *)
(*                                                                         *)
(* Witnesses (each must be violated): HintRight when a datagram or a       *)
(* credit frame after the STREAM frame does not forget the place           *)
(* (FramePack_stale.cfg, CLEAR = FALSE: the packet would be given up);     *)
(* RoundTrip when, besides, the length is dropped without the check        *)
(* (FramePack_nocheck.cfg: the STREAM frame swallows what follows it);     *)
(* NoImplicit, an implicit length is reached (FramePack_reach.cfg);        *)
(* RepairKept under the rule before #293 (FramePack_taken.cfg, KEEP =      *)
(* FALSE: the probe packet takes the pending repair and carries none of    *)
(* it, so the repair is gone).                                             *)
(*                                                                         *)
(* Lean counterpart: TransportFramePackThm.lean (fill_hint, finish_ok,     *)
(* finish_frames, finish_lastOnly, fill_ordered, fill_bytes,               *)
(* implicit_spec, implicit_refuses, header_eq, pick_took, pick_keeps,      *)
(* pick_probe_then_repair, pickOld_loses).                                 *)
(***************************************************************************)
EXTENDS FramePackOps, FiniteSets

CONSTANT MODES
\* the case, and what the builder makes of it: the fill, its tail, and what FrameIter reads in each
VARIABLES c, r, f, iw, ip
vars == <<c, r, f, iw, ip>>

(* ---- what the sources hold ---- *)
A1 == [k |-> "Ack", largest |-> 9, first |-> 2, extra |-> 0, tail |-> <<>>]
A2 == [k |-> "Ack", largest |-> 9, first |-> 0, extra |-> 1, tail |-> <<1, 2>>]
E1 == [k |-> "Extension", ty |-> 65, body |-> <<1, 2, 3>>]
EBig == [k |-> "Extension", ty |-> 66, body |-> [i \in 1..30 |-> i]]
MSD == [k |-> "MaxStreamData", id |-> 4, max |-> 900]
MS == [k |-> "MaxStreams", limit |-> 20]
RS == [k |-> "ResetStream", id |-> 8, error |-> 1, fs |-> 300]
SS == [k |-> "StopSending", id |-> 8, error |-> 2]
RK == [k |-> "Rekey", ans |-> FALSE, sh |-> Zeros(32), echo |-> Zeros(8), spn |-> 0]

\* the control frames pending: none; some; the others, with an extension frame that may not fit
Ctls ==
    { [sleep |-> FALSE, wake |-> FALSE, echo |-> FALSE, ready |-> FALSE, tickets |-> FALSE, rekey |-> FALSE,
       ext |-> <<>>, sc |-> <<>>],
      [sleep |-> TRUE, wake |-> FALSE, echo |-> FALSE, ready |-> TRUE, tickets |-> FALSE, rekey |-> FALSE,
       ext |-> <<E1>>, sc |-> <<MSD>>],
      [sleep |-> FALSE, wake |-> TRUE, echo |-> TRUE, ready |-> FALSE, tickets |-> TRUE, rekey |-> TRUE,
       ext |-> <<EBig, E1>>, sc |-> <<MS, RS, SS>>] }
Paths == { [resp |-> FALSE, pping |-> FALSE, chal |-> FALSE], [resp |-> TRUE, pping |-> TRUE, chal |-> TRUE],
           [resp |-> FALSE, pping |-> FALSE, chal |-> TRUE] }
S1 == [id |-> 0, off |-> 0, fin |-> FALSE, data |-> <<5, 6, 7>>]
S2 == [id |-> 4, off |-> 100, fin |-> TRUE, data |-> <<8, 9>>]
SL == [id |-> 8, off |-> 0, fin |-> TRUE, data |-> [i \in 1..40 |-> i]]
Streams == {<<>>, <<S1>>, <<S1, S2>>, <<SL>>}
Dgrams == {<<>>, <<<<1, 2>>>>, <<<<1, 2>>, [i \in 1..30 |-> i]>>}
Caps == {30, 64}

\* full: the least payload is the whole room (a path MTU probe, or a packet GSO batches), else the 2 bytes the
\* header-protection sample needs
Normal ==
    [mode : {"normal"}, cap : Caps, full : BOOLEAN, ack : {<<>>, <<A1>>, <<A2>>}, ctl : Ctls, path : Paths,
     ring : BOOLEAN, cc : BOOLEAN, streams : Streams, dgrams : Dgrams, sc2 : {<<>>, <<MS>>}, force : BOOLEAN,
     ackDue : BOOLEAN]
\* what build_app sees: the probe timeout owes packets, a path MTU probe is due, a tail repair is pending, the packet
\* goes on the active path; an ordinary fill of Normal is built with nothing owed or due and no repair pending
Sels == [probes : BOOLEAN, mtu : BOOLEAN, pending : BOOLEAN, active : BOOLEAN]
NoSel == [probes |-> FALSE, mtu |-> FALSE, pending |-> FALSE, active |-> TRUE]
PickOf(s) == Pick(s.probes, s.mtu, s.pending, s.active)
\* the other modes, each as build_app picks it
Other ==
    {y \in [sel : Sels, cap : {24, 40, 64}, full : BOOLEAN, ack : {<<>>, <<A1>>, <<A2>>}, wakeUntil : BOOLEAN,
            streams : Streams, rroom : {30, 600}, ackDue : BOOLEAN] : PickOf(y.sel).mode # "normal"}

\* a case as the operators read it (the fields a mode does not use are fixed)
Flat(x) ==
    IF "sel" \notin DOMAIN x
    THEN [mode |-> x.mode, cap |-> x.cap, minp |-> IF x.full THEN x.cap ELSE 2, ack |-> x.ack, ring |-> x.ring, cc |-> x.cc,
          sleep |-> x.ctl.sleep, wake |-> x.ctl.wake, echo |-> x.ctl.echo, ready |-> x.ctl.ready,
          tickets |-> x.ctl.tickets, rekey |-> x.ctl.rekey, rk |-> RK, ext |-> x.ctl.ext, sc |-> x.ctl.sc,
          resp |-> x.path.resp, pping |-> x.path.pping, chal |-> x.path.chal, streams |-> x.streams,
          dgrams |-> x.dgrams, released |-> Len(x.sc2) > 0, sc2 |-> x.sc2, force |-> x.force, ackDue |-> x.ackDue,
          wakeUntil |-> FALSE, rroom |-> 0, sel |-> NoSel, took |-> PickOf(NoSel).took, left |-> PickOf(NoSel).left]
    ELSE LET p == PickOf(x.sel) IN
         [mode |-> p.mode, cap |-> x.cap, minp |-> IF p.mode = "probe" \/ x.full THEN x.cap ELSE 2, ack |-> x.ack,
          ring |-> TRUE, cc |-> TRUE, sleep |-> FALSE, wake |-> FALSE, echo |-> FALSE, ready |-> FALSE,
          tickets |-> FALSE, rekey |-> FALSE, rk |-> RK, ext |-> <<>>, sc |-> <<>>, resp |-> FALSE,
          pping |-> FALSE, chal |-> FALSE, streams |-> x.streams, dgrams |-> <<>>, released |-> FALSE, sc2 |-> <<>>,
          force |-> p.mode = "pingonly", ackDue |-> x.ackDue, wakeUntil |-> x.wakeUntil, rroom |-> x.rroom,
          sel |-> x.sel, took |-> p.took, left |-> p.left]

Init ==
    /\ c \in {Flat(x) : x \in (IF "normal" \in MODES THEN Normal ELSE {})
                                \cup {y \in Other : PickOf(y.sel).mode \in MODES}}
    /\ r = Fill(c)
    /\ f = Finish(r.w, r.hint, c.minp)
    /\ iw = Iter(r.w)
    /\ ip = IF f.ok THEN Iter(f.pay) ELSE iw
Spec == Init /\ [][UNCHANGED vars]_vars

(* ---- the properties ---- *)
R == r
F == f

\* the frame of the fill that starts at byte p (0-based) and the bytes up to it
Last(fs) == fs[Len(fs)]
HintRight ==
    Built(c, R) =>
        /\ F.ok
        /\ Len(R.hint) = 2 =>
             /\ Last(R.fs).k = "Stream" /\ ~Last(R.fs).imp
             /\ R.hint[1] = Len(Bytes(SubSeq(R.fs, 1, Len(R.fs) - 1)))
             /\ R.hint[2] = StreamOverhead(Last(R.fs).id, Last(R.fs).off, Len(Last(R.fs).data), FALSE)
                              - VLen(Len(Last(R.fs).data))

RoundTrip ==
    Built(c, R) =>
        /\ R.w = Bytes(R.fs)
        /\ iw = [fs |-> R.fs, e |-> "none", n |-> 0]
        /\ F.ok => ip = [fs |-> Expected(R.fs, F), e |-> "none", n |-> 0]

LastOnly ==
    Built(c, R) /\ F.ok =>
        LET fs == ip.fs IN
        /\ \A i \in 1..Len(fs) : fs[i].k \in {"Stream", "Datagram"} /\ fs[i].imp => i = Len(fs) /\ fs[i].k = "Stream"
        /\ F.pad > 0 => F.n = 0
        /\ \A i \in 1..Len(R.fs) : ~(R.fs[i].k \in {"Stream", "Datagram"} /\ R.fs[i].imp)

Order ==
    Built(c, R) =>
        /\ Ordered(c.mode, R.fs)
        /\ \A i \in 1..Len(R.fs) : R.fs[i].k \notin {"Padding", "Close"}

Sizes ==
    Built(c, R) /\ F.ok =>
        /\ Len(R.w) <= c.cap
        /\ c.minp <= c.cap => Len(F.pay) <= c.cap
        /\ Len(F.pay) = IF F.pad > 0 THEN c.minp ELSE Len(R.w) - F.n
        /\ F.n > 0 => F.n = VLen(Len(Last(R.fs).data))

\* the reachability witness: an implicit length is reached
NoImplicit == ~(Built(c, R) /\ F.ok /\ F.n > 0)

\* build_app takes the pending repair exactly for a packet it builds as a repair, and leaves it pending otherwise
RepairKept ==
    /\ c.took = (c.mode = "repair")
    /\ c.left = (c.sel.pending /\ c.mode # "repair")
    /\ c.mode = "repair" => c.sel.pending /\ c.sel.active /\ ~c.sel.probes /\ ~c.sel.mtu
=============================================================================
