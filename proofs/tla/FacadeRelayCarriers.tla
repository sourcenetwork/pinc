------------------------- MODULE FacadeRelayCarriers -------------------------
(***************************************************************************)
(* The carriers of a node that carries the relay role: the streams its    *)
(* host accepts, reads, writes and closes for it through the Carriers      *)
(* trait, and what the role keeps of each (relay/part.rs Part::poll,       *)
(* Part::stop, Part::end; relay/state.rs; relay/conn.rs; relay/carriers.rs *)
(* the Carriers contract). drive/role_io.rs role_carries drives the same   *)
(* poll for an Endpoint that carries the role. The operators are in        *)
(* FacadeRelayCarriersOps.tla.                                             *)
(*                                                                         *)
(* The networks. The poll is the same code on every node that carries the *)
(* role: an ordinary node in a network with no relay binary, a node        *)
(* deployed from the relay binary where those are the only relays, and     *)
(* both in a mixed network. A member's carrier is TCP or WebSocket (kind;  *)
(* the only difference here is that a WebSocket write takes one frame,     *)
(* TCP all that is queued). A node of the relay binary may be the only     *)
(* relay and hub of its network, so the full tables (handshakes, carriers) *)
(* and the slow-reader close are what protects every member; it is         *)
(* restarted with the same identity, which here is a new part with no      *)
(* conns (Sys0); members of an older library speak the same carrier        *)
(* protocol, whose bytes are abstracted to outcomes. No rule here is one   *)
(* an ordinary node with the role lacks.                                   *)
(*                                                                         *)
(* Environment: the host hands back at most one completion per poll (the   *)
(* code takes up to BUDGET; one at a time is one of its schedules); with   *)
(* LATE it may hand back an operation of a stream after the role closed   *)
(* that stream (Carriers::close abandons them, a queued one may still     *)
(* come); a member's frames for another member arrive as Forward; the      *)
(* clock moves on one unit at a time and the host runs the timers at       *)
(* least once per unit (the role asks for them every CHECK_NS). The        *)
(* machine's sessions do not end on their own here (session time is not    *)
(* modelled), and the first timer pings every open member (next_ping is 0); *)
(* the next ping is CLIENT_PING_NS later, past TMAX.                       *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - OwnedOps: a read or a write is out on a live conn exactly when the   *)
(*    conn says so (one of each at most, conn.rs);                        *)
(*  - AcceptMatch: accept_out is set exactly when an accept is out;        *)
(*  - ClosedOnce, LiveOpen (carriers.rs: a stream is closed once, or       *)
(*    dropped at the end of a run without a close; a live conn's stream    *)
(*    is neither);                                                         *)
(*  - HsCount (handshaking counts the conns in their handshake, at most    *)
(*    Limits.handshaking), CapBound (sessions at most Limits.carriers),    *)
(*    BacklogBound (limits.rs write_backlog: at most BL units queued; the  *)
(*    write buffer holds at most BL more), ByNode;                         *)
(*  - HandshakeBound (limits.rs: a handshake ends by handshake_ns, a       *)
(*    silent carrier is closed after idle_ns, to the CHECK_NS).            *)
(***************************************************************************)
EXTENDS FacadeRelayCarriersOps

CONSTANTS KINDS,  \* carrier kinds of the accepted streams
          MAXH,   \* the most streams accepted
          TMAX,   \* the largest clock
          MAXEND, \* the most ends of a run (Part::end) before the same part is polled again
          LATE,   \* whether the host may hand back an operation of a stream after its close
          STOP    \* whether Part::stop is called

VARIABLES m, now, ticked, ends
vars == <<m, now, ticked, ends>>

Init == m = Sys0(0) /\ now = 0 /\ ticked = FALSE /\ ends = 0

ReadX == {"hello", "open", "frame", "junk", "zero"}
SlowOf(op) == op.k = "rd" /\ op.slot \in Slots(m) /\ m.c.cs[op.slot].on /\ SlowAt(m, op.slot)

PollA ==
    /\ \/ m' = Poll(m, now, NoDone, LATE)
       \/ \E op \in m.o :
            \/ op.k = "acc" /\ m' = Poll(m, now, [NoDone EXCEPT !.op = op, !.x = "err"], LATE)
            \/ op.k = "acc" /\ Len(m.ends) < MAXH /\ \E kind \in KINDS :
                 m' = Poll(m, now, [NoDone EXCEPT !.op = op, !.x = "ok", !.kind = kind], LATE)
            \/ op.k = "rd" /\ \E x \in ReadX, reply \in BOOLEAN, n \in NODES :
                 /\ x = "open" \/ n = (CHOOSE j \in NODES : TRUE)
                 /\ reply => x \in {"hello", "open", "frame"}
                 /\ m' = Poll(m, now, [NoDone EXCEPT !.op = op, !.x = x, !.n = n, !.reply = reply,
                                                     !.slow = SlowOf(op)], LATE)
            \/ op.k = "wr" /\ \E x \in {"all", "part", "zero"} :
                 m' = Poll(m, now, [NoDone EXCEPT !.op = op, !.x = x], LATE)
    /\ UNCHANGED <<now, ticked, ends>>

\* a frame of another member for node n is queued on its conn
Forward(n) ==
    /\ m.c.by[n] # 0
    /\ m' = Push(m, m.c.by[n], SlowAt(m, m.c.by[n]))
    /\ UNCHANGED <<now, ticked, ends>>

TimeoutA ==
    /\ m' = Timeout(m, now, [k \in Slots(m) |-> SlowAt(m, k)])
    /\ ticked' = TRUE
    /\ UNCHANGED <<now, ends>>

Advance ==
    /\ ticked /\ now < TMAX
    /\ now' = now + 1 /\ ticked' = FALSE
    /\ UNCHANGED <<m, ends>>

\* Part::close_carrier (state/tunnel.rs revoke)
Revoke(n) ==
    /\ m.c.by[n] # 0
    /\ m' = Dying(m, m.c.by[n], "revoked")
    /\ UNCHANGED <<now, ticked, ends>>

StopA ==
    /\ STOP /\ ~m.c.stop
    /\ m' = Stop(m)
    /\ UNCHANGED <<now, ticked, ends>>

\* the run ends without waiting for the stop (Part::end, or the part dropped); with MAXEND > 0 the same part is
\* polled again by a later run (Relay::run again, or Endpoint::run again with the role)
EndA ==
    /\ ends < MAXEND
    /\ m' = End(m)
    /\ ends' = ends + 1
    /\ UNCHANGED <<now, ticked>>

Next == PollA \/ TimeoutA \/ Advance \/ StopA \/ EndA \/ \E n \in NODES : Forward(n) \/ Revoke(n)

Spec == Init /\ [][Next]_vars

RdOp(k) == [k |-> "rd", id |-> m.c.cs[k].id, slot |-> k, h |-> m.c.cs[k].h]
WrOp(k) == [k |-> "wr", id |-> m.c.cs[k].id, slot |-> k, h |-> m.c.cs[k].h]

TypeOK == /\ now \in 0..TMAX
          /\ Len(m.ends) <= MAXH
          /\ \A x \in m.o : x.k \in {"acc", "rd", "wr"}
          /\ m.c.hs >= 0

OwnedOps == \A k \in Live(m) : (m.c.cs[k].rd <=> RdOp(k) \in m.o) /\ (m.c.cs[k].wr <=> WrOp(k) \in m.o)

AcceptMatch == m.c.acc <=> AccOp \in m.o

ClosedOnce == \A h \in 1..Len(m.ends) : m.ends[h] <= 1 /\ ~(h \in m.drop /\ m.ends[h] > 0)

LiveOpen == \A k \in Live(m) : m.ends[m.c.cs[k].h] = 0 /\ m.c.cs[k].h \notin m.drop

HsCount == m.c.hs = Cardinality({k \in Live(m) : m.c.cs[k].node = 0}) /\ m.c.hs <= HS

CapBound == Sessions(m) <= CAP

BacklogBound == \A k \in Slots(m) : m.c.cs[k].q <= BL /\ m.c.cs[k].wb <= BL

ByNode == \A n \in NODES :
              /\ m.c.by[n] # 0 => m.c.by[n] \in Live(m) /\ m.c.cs[m.c.by[n]].node = n
                                  /\ m.c.cs[m.c.by[n]].sid = m.c.cur[n]
              /\ m.c.cur[n] # 0 => m.c.by[n] # 0

HandshakeBound == ticked => \A k \in Live(m) :
                      m.c.cs[k].dy = "" => /\ m.c.cs[k].node = 0 => now < m.c.cs[k].dl
                                           /\ now - m.c.cs[k].rx < IDL

\* the stats count a refusal as a full handshake table only when it was full (stats.rs refused_handshakes_full)
HsFullHonest == ~m.mis

\* witnesses: each must be violated
NoFull == m.c.cnt.full = 0
NoHsFull == m.c.cnt.hsfull = 0
NoSlow == m.c.cnt.slow = 0
NoTimeout == m.c.cnt.tout = 0
NoLate == ~m.late
=============================================================================
