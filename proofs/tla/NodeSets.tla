------------------------------- MODULE NodeSets -------------------------------
(***************************************************************************)
(* The reconcile layer over real sessions (pinc-node reconcile.rs: rounds  *)
(* and answered streams) with the layer tables it rides on (layer.rs:      *)
(* lsess, lout, lconn, ldials, dial_layer, layer_up, layer_failed,         *)
(* layer_closed, layer_session) and the node calls that touch them         *)
(* (node.rs: sets_start, sets_cancel, revoke, leave, handle_timeout, the   *)
(* service loop of settle). The endpoint is abstract: sessions it dials,   *)
(* reports up, fails, and ends, and a stream credit it gives or not.       *)
(*                                                                         *)
(* One step is one call of the node, run to its end as the code does: a   *)
(* host call, a timer call (handle_timeout: sets_timeout, then settle), or *)
(* one endpoint event handed over (then settle). settle drains the queued  *)
(* layer dials (Settle, the service loop) until none is left; the code's   *)
(* bound of 64 rounds is never reached at these sizes.                     *)
(*                                                                         *)
(* State st:                                                               *)
(*   eps      the endpoint's sessions [sid, peer, out (we dialed), up      *)
(*            (reported), closing (a Close was issued, or Shutdown)];      *)
(*   lsess    the layer sessions [sid, peer, inc] (Io::lsess);            *)
(*   lout     [peer, sid]: the session we dialed per peer (Io::lout);     *)
(*   lconn    peers with a layer dial in flight (Io::lconn, bound LCONN); *)
(*   ldials   peers queued for a layer dial (Io::ldials, drained by       *)
(*            Settle, so empty between steps);                             *)
(*   revoked, leaving   Io::revoked and Node::leaving;                     *)
(*   rounds   [id, peer, att (attempts spent), act (the session of the    *)
(*            round's stream, 0 for none), oa (open_at, NONE for none)];   *)
(*   resps    the answered streams [s, k] (Reconciler::resps);             *)
(*   next     the last round id handed out; ends: [id, why, att, gone] one *)
(*            per round event the node emitted (gone: the peer was revoked *)
(*            or the node was leaving when it ended); cancelled: ids       *)
(*            sets_cancel stopped; now: the time; credit: whether the      *)
(*            endpoint gives a stream now; fl: the ids of the rounds a full *)
(*            table touched in this step, in order (a ghost).              *)
(*                                                                         *)
(* The other layers (values, delay-tolerant) are not in the state: FILLERS *)
(* are peers whose incoming sessions take room in lsess as another layer's *)
(* would. Not modelled: the host's set changing under a round (the         *)
(* documented contract forbids it), the protocol messages (a reply is one  *)
(* of: the exchange ends, a malformed head, an early end of stream, a      *)
(* reset with UNKNOWN_SET, another reset), a write the stream table        *)
(* refuses (the first message is far below the cap), the round id's u32   *)
(* wrap (2^32 starts), a Close the endpoint refuses (left to the transport *)
(* timeout). Assumed of the endpoint: a dial ends in exactly one Connected *)
(* or ConnectFailed (a Close during the handshake gives ConnectFailed), a  *)
(* reported session ends in exactly one Closed, and a closing session      *)
(* reports nothing else and gives no stream.                               *)
(*                                                                         *)
(* Checked (Inv), from the module documentation of layer.rs, reconcile.rs  *)
(* and node.rs:                                                            *)
(*  - Bounds: lsess at most LCAP (TABLE_MAX), lconn at most LCONN, at most *)
(*    ROUNDS rounds and RESPONDERS answered streams, at most ATTEMPTS      *)
(*    attempts spent by a round;                                           *)
(*  - OneLayer: a session belongs to one layer entry; LoutSound: lout      *)
(*    holds, per peer, one outgoing session of lsess;                      *)
(*  - LiveRefs: every layer session is a reported endpoint session, and    *)
(*    every answered stream and every round's stream is on one: a closed   *)
(*    session leaves nothing of the layers behind;                         *)
(*  - GoneClosing: a layer session of a revoked peer, or of a leaving      *)
(*    node, is being closed;                                               *)
(*  - Accounted: a round that left the table ended with one event, or was  *)
(*    cancelled and has none; Exhausted only after ATTEMPTS;               *)
(*  - Waiting: a round waiting for stream credit has no stream and a time  *)
(*    within the clock;                                                    *)
(* and in every step (StepProps):                                          *)
(*  - NoNewForGone: no layer session comes up for a revoked peer or on a   *)
(*    leaving node;                                                        *)
(*  - OpenAtSat: a round that waits for credit retries at now + OPEN_RETRY *)
(*    saturating at the clock's maximum.                                   *)
(* Documented properties the code meets with fix N1 (layer_lost):         *)
(* NodeSets_way (RoundHasWay: "a round ends with exactly one event"; a    *)
(* shed dial into a full layer table is not left without a way on),       *)
(* NodeSets_cancel (CancelledDoc: a round of a revoked peer or a leaving  *)
(* node ends Cancelled). Before N1, TLC found both violated (the          *)
(* findings). CancelledDoc holds since the code decides it by one         *)
(* function, Node::peer_gone (layer.rs, PeerGone here), on both paths     *)
(* that ended such a round Exhausted: a round waiting on a dial of ours   *)
(* that fails after the revoke or the leave (ConnectFailed, layer_lost    *)
(* with cancel) and a round active on a session that closes after it      *)
(* (sets_down ends it Cancelled instead of round_retry).                  *)
(* A dial that finds a table full (lconn in dial_layer, lsess in          *)
(* layer_up: layer_unrecorded, Unrecorded here) counts an attempt of     *)
(* every round waiting for the peer, and the round tries again after      *)
(* OPEN_RETRY (round_retry with wait: open_at), not in the same call; a   *)
(* round on a table that stays full ends Exhausted, its first attempt     *)
(* spent in the start call. The ghost fl lists, per call, the rounds a    *)
(* full table touched (reset at every step): FullOnce (Inv) says no round *)
(* is touched twice in one call, FullSpends (StepProps) that each one     *)
(* spent an attempt and waits OPEN_RETRY or ended Exhausted after its    *)
(* ATTEMPTS. UnrecordedOld is the rule before the fix (a failed dial,     *)
(* retried at once, layer_failed); NodeSets_w_samecall substitutes it and *)
(* TLC must violate FullOnce.                                              *)
(* Witnesses: NodeSets_busy, NodeSets_exhausted, NodeSets_respfull,        *)
(* NodeSets_sat, NodeSets_w_full (a full table touches a round),          *)
(* NodeSets_w_samecall (the old rule touches one twice in a call).        *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences
CONSTANTS PEERS, FILLERS, SIDS, LCAP, LCONN, ROUNDS, RESPONDERS, ATTEMPTS, NSTARTS, TMAX, OR
VARIABLES st
vars == <<st>>

NONE == -1
\* the reply kinds of the peer to a round's stream
KINDS == {"end", "bad", "fin", "unknown", "reset"}
Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Sat(t) == IF t > TMAX THEN TMAX ELSE t

Used(s) == {e.sid : e \in s.eps}
FreeSid(s) == IF SIDS \ Used(s) = {} THEN 0 ELSE Min(SIDS \ Used(s))
EpOf(s, sid) == CHOOSE e \in s.eps : e.sid = sid
LIds(s) == {x.sid : x \in s.lsess}
HasOut(s, p) == \E o \in s.lout : o.peer = p
\* layer_session: the session we dialed, else the lowest incoming one
SessOf(s, p) ==
    LET o == {x.sid : x \in {y \in s.lout : y.peer = p}}
        a == {x.sid : x \in {y \in s.lsess : y.peer = p}}
    IN IF o # {} THEN Min(o) ELSE IF a # {} THEN Min(a) ELSE 0
\* open_stream_at: the endpoint gives a stream when it has credit and the session is not closing
CanOpen(s, sid) == s.credit /\ ~EpOf(s, sid).closing
Close(s, sid) == [s EXCEPT !.eps = {IF e.sid = sid THEN [e EXCEPT !.closing = TRUE] ELSE e : e \in @}]

\* Node::peer_gone: the node leaves or the peer is revoked
PeerGone(s, p) == s.leaving \/ p \in s.revoked
Has(s, id) == \E r \in s.rounds : r.id = id
RoundOf(s, id) == CHOOSE r \in s.rounds : r.id = id
Put(s, r) == [s EXCEPT !.rounds = {x \in @ : x.id # r.id} \cup {r}]
\* round_fail and round_finish: the round's one event
End(s, id, why) ==
    LET r == RoundOf(s, id)
    IN [s EXCEPT !.rounds = {x \in @ : x.id # id},
                 !.ends = @ \cup {[id |-> id, why |-> why, att |-> r.att,
                                   gone |-> PeerGone(s, r.peer)]}]

\* round_begin: on the peer's session if there is one, else after a dial; with no credit it waits OPEN_RETRY
\* (not counted); a stream opened spends an attempt
RoundBegin(s, id) ==
    IF ~Has(s, id) THEN s
    ELSE LET r == [RoundOf(s, id) EXCEPT !.oa = NONE]
             sid == SessOf(s, r.peer)
         IN IF sid = 0
            THEN LET s2 == Put(s, r)
                 IN IF r.peer \in s.lconn \/ r.peer \in s.ldials THEN s2 ELSE [s2 EXCEPT !.ldials = @ \cup {r.peer}]
            ELSE IF ~CanOpen(s, sid) THEN Put(s, [r EXCEPT !.oa = Sat(s.now + OR)])
            ELSE Put(s, [r EXCEPT !.att = @ + 1, !.act = sid])

\* round_retry: exhausted at ATTEMPTS, else the stream is abandoned and the round begins again, at once or (wait: a
\* table was full) after OPEN_RETRY
RoundRetry(s, id, wait) ==
    IF ~Has(s, id) THEN s
    ELSE LET r == RoundOf(s, id)
         IN IF r.att >= ATTEMPTS THEN End(s, id, "exhausted")
            ELSE IF wait THEN Put(s, [r EXCEPT !.act = 0, !.oa = Sat(s.now + OR)])
            ELSE RoundBegin(Put(s, [r EXCEPT !.act = 0]), id)

Waiting(s, p) == {r.id : r \in {x \in s.rounds : x.peer = p /\ x.act = 0}}
RECURSIVE FailEach(_, _, _)
FailEach(s, ids, wait) ==
    IF ids = {} THEN s
    ELSE LET id == Min(ids)
             s1 == IF Has(s, id) THEN RoundRetry(Put(s, [RoundOf(s, id) EXCEPT !.att = @ + 1]), id, wait) ELSE s
         IN FailEach(s1, ids \ {id}, wait)
RECURSIVE BeginEach(_, _)
BeginEach(s, ids) == IF ids = {} THEN s ELSE LET id == Min(ids) IN BeginEach(RoundBegin(s, id), ids \ {id})
\* a round whose session closed: Cancelled when the peer is gone (fix A1b), else it retries at once
RECURSIVE DownEach(_, _)
DownEach(s, ids) ==
    IF ids = {} THEN s
    ELSE LET id == Min(ids)
             s0 == IF Has(s, id) THEN Put(s, [RoundOf(s, id) EXCEPT !.act = 0]) ELSE s
             s1 == IF ~Has(s, id) THEN s
                   ELSE IF PeerGone(s, RoundOf(s, id).peer) THEN End(s0, id, "cancelled")
                   ELSE RoundRetry(s0, id, FALSE)
         IN DownEach(s1, ids \ {id})

\* sets_failed: a failed dial spends an attempt of each round waiting for the peer, and retries it (after OPEN_RETRY
\* when wait)
SetsFailed(s, p, wait) == FailEach(s, Waiting(s, p), wait)
\* sets_up: the rounds waiting for the peer begin
SetsUp(s, p) == BeginEach(s, Waiting(s, p))
\* sets_timeout: the rounds whose open_at came begin
SetsTimeout(s) == BeginEach(s, {r.id : r \in {x \in s.rounds : x.oa # NONE /\ x.oa <= s.now}})
\* sets_down: the session's answered streams go and its rounds retry
SetsDown(s, sid) == DownEach([s EXCEPT !.resps = {x \in @ : x.s # sid}], {r.id : r \in {x \in s.rounds : x.act = sid}})

\* layer_failed for the reconcile layer
LayerFailed(s, p) == SetsFailed([s EXCEPT !.lconn = @ \ {p}], p, FALSE)

RECURSIVE CancelEach(_, _)
CancelEach(s, ids) == IF ids = {} THEN s ELSE LET id == Min(ids) IN CancelEach(End(s, id, "cancelled"), ids \ {id})
\* layer_lost (fix N1): a dial of ours ends with no session; refused for good (cancel: the peer revoked or the node
\* leaving) the rounds waiting for the peer end Cancelled (sets_cancelled), a round active on a session of the peer
\* ends through that session's close (SetsDown, fix A1b); otherwise it is layer_failed (retry, backoff)
LayerLost(s, p, cancel) ==
    IF cancel THEN CancelEach([s EXCEPT !.lconn = @ \ {p}], Waiting(s, p))
    ELSE LayerFailed(s, p)

\* layer_unrecorded (fix A2): a dial that finds a table full counts an attempt of each round waiting for the peer, which
\* tries again after OPEN_RETRY; UnrecordedOld, the rule before it (layer_lost without cancel: a failed dial, retried
\* at once), is for the witness NodeSets_w_samecall only
Unrecorded(s, p) == SetsFailed([s EXCEPT !.lconn = @ \ {p}], p, TRUE)
UnrecordedOld(s, p) == LayerFailed(s, p)
\* the ghost: the rounds waiting for p are touched by a full table
RECURSIVE Asc(_)
Asc(S) == IF S = {} THEN <<>> ELSE <<Min(S)>> \o Asc(S \ {Min(S)})
Hit(s, p) == [s EXCEPT !.fl = @ \o Asc(Waiting(s, p))]

\* dial_layer: nothing with a session we dialed or a dial in flight; refused (reported to the layer) for a revoked
\* peer or a leaving node; unrecorded with lconn full; failed when the endpoint has no room for a session; else the
\* dial is made and recorded in lconn
DialLayer(s, p) ==
    IF HasOut(s, p) \/ p \in s.lconn THEN s
    ELSE IF PeerGone(s, p) THEN LayerLost(s, p, TRUE)
    ELSE IF Cardinality(s.lconn) >= LCONN THEN Unrecorded(Hit(s, p), p)
    ELSE IF FreeSid(s) = 0 THEN LayerFailed(s, p)
    ELSE [s EXCEPT !.eps = @ \cup {[sid |-> FreeSid(s), peer |-> p, out |-> TRUE, up |-> FALSE, closing |-> FALSE]},
                   !.lconn = @ \cup {p}]

\* the service loop of settle: every queued layer dial is made
RECURSIVE Settle(_)
Settle(s) == IF s.ldials = {} THEN s ELSE LET p == Min(s.ldials) IN Settle(DialLayer([s EXCEPT !.ldials = @ \ {p}], p))

\* layer_up: shed (Close) for a revoked peer or a leaving node, a full table, or a second session we dialed; a shed
\* dial of ours (not the duplicate) is layer_lost with cancel when revoked or leaving (fix N1), and unrecorded when
\* the table is full (fix A2)
LayerUp(s, sid, p, inc) ==
    LET s0 == [s EXCEPT !.lconn = @ \ {p}]
    IN IF PeerGone(s, p)
       THEN IF inc THEN Close(s0, sid) ELSE LayerLost(Close(s0, sid), p, TRUE)
       ELSE IF Cardinality(s.lsess) >= LCAP
       THEN IF inc THEN Close(s0, sid) ELSE Unrecorded(Hit(Close(s0, sid), p), p)
       ELSE IF ~inc /\ HasOut(s, p) THEN Close(s0, sid)
       ELSE SetsUp([s0 EXCEPT !.lsess = @ \cup {[sid |-> sid, peer |-> p, inc |-> inc]},
                              !.lout = IF inc THEN @ ELSE @ \cup {[peer |-> p, sid |-> sid]}], p)

\* layer_closed: a session not in the table (a shed one) changes nothing
LayerClosed(s, sid) ==
    IF sid \notin LIds(s) THEN s
    ELSE SetsDown([s EXCEPT !.lsess = {x \in @ : x.sid # sid}, !.lout = {o \in @ : o.sid # sid}], sid)

Init == st = [eps |-> {}, lsess |-> {}, lout |-> {}, lconn |-> {}, ldials |-> {}, revoked |-> {}, leaving |-> FALSE,
              rounds |-> {}, resps |-> {}, next |-> 0, ends |-> {}, cancelled |-> {}, now |-> 0, credit |-> TRUE,
              fl |-> <<>>]
\* every step starts with no round touched by a full table
B == [st EXCEPT !.fl = <<>>]

\* ---- host calls; a result is a parameter so the state graph has one node per state (MbtNodeSets)
\* sets_start: res is the round id, or 0 for SetsError::Busy (nothing changes)
CallStart(p, res) ==
    /\ st.next < NSTARTS
    /\ IF Cardinality(st.rounds) >= ROUNDS
       THEN res = 0 /\ st' = B
       ELSE LET id == st.next + 1
            IN /\ res = id
               /\ st' = Settle(RoundBegin([B EXCEPT !.next = id,
                                   !.rounds = @ \cup {[id |-> id, peer |-> p, att |-> 0, act |-> 0, oa |-> NONE]}], id))
\* sets_cancel: the round goes with no event; false and nothing for a round that does not run
CallCancel(id, res) ==
    /\ res = Has(st, id)
    /\ st' = IF res THEN [B EXCEPT !.rounds = {x \in @ : x.id # id}, !.cancelled = @ \cup {id}] ELSE B
\* revoke: Close for every endpoint session of the peer (a dial in flight included)
CallRevoke(p) ==
    st' = Settle([B EXCEPT !.revoked = @ \cup {p},
                            !.eps = {IF e.peer = p THEN [e EXCEPT !.closing = TRUE] ELSE e : e \in @}])
\* leave: Shutdown, the endpoint ends every session
CallLeave == ~st.leaving /\ st' = Settle([B EXCEPT !.leaving = TRUE, !.eps = {[e EXCEPT !.closing = TRUE] : e \in @}])
\* handle_timeout at t (not before now)
CallTick(t) == t >= st.now /\ st' = Settle(SetsTimeout([B EXCEPT !.now = t]))

\* ---- the endpoint
EnvCredit == st' = [B EXCEPT !.credit = ~@]
EvConnected(sid) ==
    /\ \E e \in st.eps : e.sid = sid /\ e.out /\ ~e.up /\ ~e.closing
    /\ st' = Settle(LayerUp([B EXCEPT !.eps = {IF e.sid = sid THEN [e EXCEPT !.up = TRUE] ELSE e : e \in @}],
                            sid, EpOf(st, sid).peer, FALSE))
\* ConnectFailed: layer_lost, with cancel when the peer is gone (fix A1)
EvFailed(sid) ==
    /\ \E e \in st.eps : e.sid = sid /\ e.out /\ ~e.up
    /\ LET p == EpOf(st, sid).peer
       IN st' = Settle(LayerLost([B EXCEPT !.eps = {e \in @ : e.sid # sid}], p, PeerGone(st, p)))
EvIncoming(p) ==
    /\ FreeSid(st) # 0
    /\ LET sid == FreeSid(st)
       IN st' = Settle(LayerUp([B EXCEPT !.eps = @ \cup {[sid |-> sid, peer |-> p, out |-> FALSE, up |-> TRUE,
                                                           closing |-> FALSE]}], sid, p, TRUE))
EvClosed(sid) ==
    /\ \E e \in st.eps : e.sid = sid /\ e.up
    /\ st' = Settle(LayerClosed([B EXCEPT !.eps = {e \in @ : e.sid # sid}], sid))
\* the peer answers on a round's stream: the exchange ends (ReconcileDone), a head over the limit or an early end of
\* stream (Protocol), a reset with UNKNOWN_SET (UnknownSet), another reset (the round retries)
EvReply(id, kind) ==
    /\ Has(st, id) /\ RoundOf(st, id).act # 0 /\ ~EpOf(st, RoundOf(st, id).act).closing
    /\ st' = Settle(CASE kind = "end" -> End(B, id, "done")
                      [] kind \in {"bad", "fin"} -> End(B, id, "protocol")
                      [] kind = "unknown" -> End(B, id, "unknownset")
                      [] kind = "reset" -> RoundRetry(B, id, FALSE))
\* the peer opens a stream on a layer session: answered, or reset BUSY with RESPONDERS answered
EvPeerStream(sid) ==
    /\ sid \in LIds(st) /\ ~EpOf(st, sid).closing
    /\ st' = IF Cardinality(st.resps) >= RESPONDERS THEN B
             ELSE [B EXCEPT !.resps = @ \cup {[s |-> sid, k |-> Min({k \in 1..RESPONDERS : [s |-> sid, k |-> k] \notin @})]}]
\* an answered stream ends (the exchange ended, it broke the protocol, or the peer reset it)
EvRespEnd(sid, k) == [s |-> sid, k |-> k] \in st.resps /\ st' = [B EXCEPT !.resps = @ \ {[s |-> sid, k |-> k]}]

Next == \/ \E p \in PEERS, res \in 0..NSTARTS : CallStart(p, res)
        \/ \E id \in 1..NSTARTS, res \in BOOLEAN : CallCancel(id, res)
        \/ \E p \in PEERS : CallRevoke(p)
        \/ CallLeave
        \/ \E t \in 0..TMAX : CallTick(t)
        \/ EnvCredit
        \/ \E sid \in SIDS : EvConnected(sid)
        \/ \E sid \in SIDS : EvFailed(sid)
        \/ \E p \in PEERS \cup FILLERS : EvIncoming(p)
        \/ \E sid \in SIDS : EvClosed(sid)
        \/ \E id \in 1..NSTARTS, kind \in KINDS : EvReply(id, kind)
        \/ \E sid \in SIDS : EvPeerStream(sid)
        \/ \E sid \in SIDS, k \in 1..RESPONDERS : EvRespEnd(sid, k)
Spec == Init /\ [][Next]_vars

Bounds == /\ Cardinality(st.lsess) <= LCAP /\ Cardinality(st.lconn) <= LCONN
          /\ Cardinality(st.rounds) <= ROUNDS /\ Cardinality(st.resps) <= RESPONDERS
          /\ \A r \in st.rounds : r.att <= ATTEMPTS
          /\ st.ldials = {}
OneLayer == \A x, y \in st.lsess : x.sid = y.sid => x = y
LoutSound == /\ \A o \in st.lout : \E x \in st.lsess : x.sid = o.sid /\ x.peer = o.peer /\ ~x.inc
             /\ \A o1, o2 \in st.lout : o1.peer = o2.peer => o1 = o2
             /\ \A x \in st.lsess : ~x.inc => \E o \in st.lout : o.sid = x.sid
LiveRefs == /\ \A x \in st.lsess : \E e \in st.eps : e.sid = x.sid /\ e.up
            /\ \A x \in st.resps : x.s \in LIds(st)
            /\ \A r \in st.rounds : r.act # 0 => r.act \in LIds(st)
GoneClosing == \A x \in st.lsess : (x.peer \in st.revoked \/ st.leaving) => EpOf(st, x.sid).closing
Accounted == /\ \A id \in 1..st.next : Has(st, id) \/ id \in st.cancelled \/ \E e \in st.ends : e.id = id
             /\ \A e1, e2 \in st.ends : e1.id = e2.id => e1 = e2
             /\ \A e \in st.ends : ~Has(st, e.id) /\ e.id \notin st.cancelled
             /\ \A e \in st.ends : e.why = "exhausted" => e.att = ATTEMPTS
WaitingOK == \A r \in st.rounds : r.oa # NONE => (r.act = 0 /\ r.oa <= TMAX)
\* a round's dial finds a full table at most once in one call (fix A2; before it, the round dialed again in the same
\* call and found the table full again until its attempts were spent)
FullOnce == \A i, j \in 1..Len(st.fl) : st.fl[i] = st.fl[j] => i = j
Inv == Bounds /\ OneLayer /\ LoutSound /\ LiveRefs /\ GoneClosing /\ Accounted /\ WaitingOK /\ FullOnce

NoNewForGone == \A x \in st'.lsess \ st.lsess : x.peer \notin st'.revoked /\ ~st'.leaving
OpenAtSat == \A r \in st'.rounds : (r.oa # NONE /\ (~Has(st, r.id) \/ RoundOf(st, r.id).oa # r.oa))
                 => r.oa = Sat(st'.now + OR)
\* a round a full table touched in the step spent an attempt and waits OPEN_RETRY with no stream, or ended Exhausted
\* with its ATTEMPTS spent: a full table holds no round longer than ATTEMPTS - 1 retry periods
AttBefore(id) == IF Has(st, id) THEN RoundOf(st, id).att ELSE 0
FullSpends == \A i \in 1..Len(st'.fl) :
                  LET id == st'.fl[i]
                  IN \/ /\ Has(st', id)
                        /\ RoundOf(st', id).act = 0 /\ RoundOf(st', id).oa = Sat(st'.now + OR)
                        /\ RoundOf(st', id).att > AttBefore(id)
                     \/ \E e \in st'.ends \ st.ends : e.id = id /\ e.why = "exhausted" /\ e.att = ATTEMPTS
StepProps == [][NoNewForGone /\ OpenAtSat /\ FullSpends]_vars

\* finding F1 (reconcile.rs module doc, "a round ends with exactly one event"), as safety: a round that runs has
\* something that will move it: its stream, its retry time, a queued dial, a session, or a dial of ours in flight
InFlight(s, p) == \E e \in s.eps : e.peer = p /\ e.out /\ ~e.up
RoundHasWay == \A r \in st.rounds : r.act # 0 \/ r.oa # NONE \/ r.peer \in st.ldials \/ SessOf(st, r.peer) # 0
                                    \/ InFlight(st, r.peer)
\* F2 (event.rs, ReconcileFailure::Cancelled: "The node left the group or the peer was revoked"), holds since A1, A1b
CancelledDoc == \A e \in st.ends : e.gone => e.why = "cancelled"

\* witnesses: each is violated in a reachable state
RoundsNotFull == Cardinality(st.rounds) < ROUNDS
NeverExhausted == \A e \in st.ends : e.why # "exhausted"
RespNotFull == Cardinality(st.resps) < RESPONDERS
\* a round waits for credit with its retry time at the clock's maximum, set at the maximum
NeverSat == ~\E r \in st.rounds : r.oa = TMAX /\ st.now = TMAX
\* a full table touches a round (NodeSets_w_full)
NeverFull == st.fl = <<>>
=============================================================================
