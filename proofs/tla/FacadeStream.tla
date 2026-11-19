----------------------------- MODULE FacadeStream -----------------------------
(***************************************************************************)
(* The handles of one stream and the datagrams of one connection, every    *)
(* interleaving of the application's calls, the peer's actions and the     *)
(* connection's end, on the operations of FacadeStreamOps.tla (the Rust     *)
(* items are named there). One call is one step: whether and when a call    *)
(* that waits is woken is FacadeWaits.tla's; here a waiting call changes    *)
(* nothing.                                                                *)
(*                                                                         *)
(* Parts chooses the side checked (send, recv, dgram): the three are        *)
(* independent but for the session's end, so each config checks one and    *)
(* stays small. The properties are the module and item docs of stream.rs   *)
(* and conn.rs: reads in order, each chunk once, the end only after every   *)
(* chunk and then again on every read; nothing written after the FIN; a     *)
(* dropped SendStream ends its stream; a dropped or stopped RecvStream      *)
(* holds nothing; after a reset the writer sees the reset; datagrams in     *)
(* arrival order, each once, a full queue dropping only its oldest, the     *)
(* reason only once the datagrams that arrived before are read; and a      *)
(* refused or waiting call changes nothing.                                 *)
(***************************************************************************)
EXTENDS FacadeStreamOps, TLC

CONSTANTS
    Parts,    \* a subset of {"send", "recv", "dgram"}
    MAXW,     \* chunks the application writes
    MAXR,     \* chunks the peer sends
    MAXD      \* datagrams each way

ASSUME Parts \subseteq {"send", "recv", "dgram"} /\ MAXW >= 0 /\ MAXR >= 0 /\ MAXD >= 0 /\ DQ >= 1

VARIABLES s, last
vars == <<s, last>>

Init == s = S0(0) /\ last = [op |-> "none", o |-> Ok(0)]

Do(op, x) == s' = x.s /\ last' = [op |-> op, o |-> x.o]
Env(op, t) == s' = t /\ last' = [op |-> op, o |-> Ok(0)]

Next ==
    \/ "send" \in Parts /\ ~s.dropS /\ s.tw < MAXW /\ Do("write", Write(s))
    \/ "send" \in Parts /\ ~s.dropS /\ Do("finish", Finish(s))
    \/ "send" \in Parts /\ ~s.dropS /\ ~s.hreset /\ Do("reset", Reset(s))
    \/ "send" \in Parts /\ ~s.dropS /\ Do("dsend", DropSend(s))
    \/ "send" \in Parts /\ s.live /\ ~s.pstop /\ Env("pstop", PeerStop(s))
    \/ "send" \in Parts /\ s.live /\ ~s.room /\ Env("room", [s EXCEPT !.room = TRUE])
    \/ "send" \in Parts /\ s.room /\ Env("full", [s EXCEPT !.room = FALSE])
    \/ "recv" \in Parts /\ ~s.dropR /\ Do("read", Read(s))
    \/ "recv" \in Parts /\ ~s.dropR /\ ~s.hstop /\ Do("stop", Stop(s))
    \/ "recv" \in Parts /\ ~s.dropR /\ Do("drecv", DropRecv(s))
    \/ "recv" \in Parts /\ s.live /\ ~s.pfin /\ ~s.preset /\ s.pw < MAXR /\ Env("psend", PeerSend(s))
    \/ "recv" \in Parts /\ s.live /\ ~s.pfin /\ ~s.preset /\ Env("pfin", PeerFin(s))
    \/ "recv" \in Parts /\ s.live /\ ~s.pfin /\ ~s.preset /\ Env("preset", PeerReset(s))
    \/ "dgram" \in Parts /\ \E fit \in BOOLEAN : Do("rdg", RecvDgram(s, fit))
    \/ "dgram" \in Parts /\ s.dsent < MAXD /\ \E big \in BOOLEAN : Do("sdg", SendDgram(s, big))
    \/ "dgram" \in Parts /\ s.live /\ s.dn < MAXD /\ Env("pdg", PeerDgram(s))
    \/ s.live /\ \E who \in {"peer", "local"} : Env(who, Close(s, who))

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties.                                                              *)

TypeOK ==
    /\ s.tw \in 0..MAXW /\ s.pw \in 0..MAXR /\ s.rpos \in 0..s.pw /\ s.dn \in 0..MAXD
    /\ s.hend \in {"none", "fin", "reset"} /\ s.why \in {"none", "peer", "local"}
    /\ last.o.r \in 0..3

\* reads return the chunks in the order sent, each once, none skipped
ReadOrder == s.got = [j \in 1..Len(s.got) |-> j]
\* the end is seen only after every chunk
EndExact == s.hend = "fin" => s.pfin /\ s.rpos = s.pw /\ Len(s.got) = s.pw
\* the end once seen is the answer of every later read (unless the stream was stopped)
EndRepeat == (last.op = "read" /\ s.hend = "fin" /\ ~s.hstop) => last.o = EndR \/ (last.o.r = 0 /\ last.o.v = s.pw)
EndSticky == [][s.hend # "none" => s'.hend = s.hend]_vars
\* nothing is written after the FIN; a write after finish is refused
NoWriteAfterFin == [][s.tfin => s'.tw = s.tw]_vars
WriteAfterFinish == (last.op = "write" /\ s.hfin) => last.o.r = 2
\* finish is idempotent: a second finish (no reset) is Ok and changes nothing
FinishIdem == [][(s.hfin /\ ~s.hreset /\ last'.op = "finish") => (last'.o = Ok(0) /\ s'.tfin = s.tfin)]_vars
\* a SendStream dropped on a live session ends its stream: FIN, reset, or stopped by the peer
DropEnds == s.dropS /\ s.dropLive => s.tfin \/ s.treset \/ s.pstop
\* documented: after reset(code) the writer and finish see the reset (findings at DOC = FALSE)
ResetSeen == (last.op \in {"write", "finish"} /\ s.hreset) => last.o = Err(STOPPED, RC)
\* documented: a dropped or stopped RecvStream holds nothing the peer sent (finding at DOC = FALSE, DFULL)
NoHeld == ((s.dropR \/ s.hstop) /\ s.live) => s.rpos = s.pw \/ s.preset
\* documented: no stop entry outlives the SendStream (finding at DOC = FALSE)
FailClean == s.dropS => ~s.failed

\* datagrams: in arrival order, each read once, every one read, held or dropped, only the oldest dropped
DgramFifo == \A j \in 1..(Len(s.dgot) - 1) : s.dgot[j] < s.dgot[j + 1]
DgramKept ==
    /\ Range(s.dgot) \cup Range(s.dq) \cup s.ddrop = 1..s.dn
    /\ Len(s.dgot) + Len(s.dq) + Cardinality(s.ddrop) = s.dn
DropOldest == \A x \in s.ddrop, y \in Range(s.dq) : x < y
DgramBound == Len(s.dq) <= DQ
\* documented: the reason only once the datagrams that arrived before are read (finding at DOC = FALSE)
LateDgram == (last.op = "rdg" /\ last.o.r = 2 /\ last.o.k \in {PEERCLOSED, LOCALCLOSED}) => s.dq = <<>>

\* a refused or waiting call changes nothing but the handle's own cached end
Facts(t) == <<t.live, t.tw, t.tfin, t.treset, t.failed, t.fcode, t.rpos, t.got, t.dq, t.dgot, t.ddrop, t.dsent>>
ErrKeeps ==
    [][(last'.op \in {"write", "finish", "read", "rdg", "sdg"} /\ last'.o.r \in {2, 3}) => Facts(s') = Facts(s)]_vars

\* witness: a full datagram queue drops one
NoDrop == s.ddrop = {}
=============================================================================
