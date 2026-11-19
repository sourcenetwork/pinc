------------------------------ MODULE NodeValues ------------------------------
(***************************************************************************)
(* The values layer joined to the node's sessions (pinc-node values.rs:    *)
(* start_fetch, cancel_fetch, values_drain, values_up and supersede,       *)
(* values_down, values_stream_opened, values_pacing, VSess::open_stream    *)
(* and hangup; layer.rs layer_up and layer_closed for the values layer)    *)
(* over the tables of values_net.rs (NodeValuesNetOps.tla).                *)
(*                                                                         *)
(* State: n the net (provider and stream tables, the running fetches'      *)
(* lists); sof the session of each stream [lid, ses]; lsess the values     *)
(* sessions [sid, peer, inc]; lout [peer, sid] the session we dialed per   *)
(* peer; closing the sessions the node closed (a superseded or hung up     *)
(* one) that the endpoint has not ended yet.                               *)
(*                                                                         *)
(* What pinc-values decides is a choice of the environment here: when a    *)
(* fetch opens a stream to one of its providers, drops one (a reset, an    *)
(* eviction), hangs up a provider, finishes; when a served response ends.  *)
(* Assumed of pinc-values (its own models): a fetch that turns Done drops  *)
(* every stream it owns (drop_all_streams) before the node drains it, and  *)
(* the server refuses a request with BUSY when its SERVERS slots are full. *)
(* Assumed of the endpoint: a closing session opens no new stream.         *)
(*                                                                         *)
(* Checked (Inv), from the module documentation of values.rs and           *)
(* values_net.rs:                                                          *)
(*  - Bounded and Exact of the net (every table bounded, the use counts    *)
(*    exactly the holders), at most FETCHES running fetches and SERVERS    *)
(*    served streams;                                                      *)
(*  - OnLive: every stream is on a values session of the table that was   *)
(*    not superseded (a closed or superseded session leaves none; a hung  *)
(*    up one keeps its streams until the endpoint ends it, as the code    *)
(*    does); supd is the set of superseded sessions not yet ended;         *)
(*  - NoOrphan: every stream a fetch owns belongs to a running fetch (a    *)
(*    fetch that finished or was cancelled leaves no stream behind);       *)
(*  - LoutSound: lout names an outgoing values session of the table.       *)
(* Witnesses: NodeValues_busy (a request is refused for full server       *)
(* slots), NodeValues_super (a peer's new incoming session supersedes an   *)
(* older one that held a stream).                                          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS PEERS, SIDS, CAP, SCAP, FIDS, FETCHES, SERVERS, NMAX
VARIABLES n, sof, lsess, lout, closing, supd, sup, busy
vars == <<n, sof, lsess, lout, closing, supd, sup, busy>>

INSTANCE NodeValuesNetOps

LIds == {x.sid : x \in lsess}
SesOf(lid) == (CHOOSE x \in sof : x.lid = lid).ses
OfSession(sid) == {x.lid : x \in {y \in sof : y.ses = sid}}
Serves == {x \in n.streams : x.owner = 0}
\* the stream table and the session map after a drop of every stream in L
RECURSIVE DropAll(_, _)
DropAll(m, L) == IF L = {} THEN m ELSE LET l == Min(L) IN DropAll(Drop(m, l), L \ {l})
Gone(L) == {x \in sof : x.lid \notin L}
NewLid(r) == r.lid # 0

Init == /\ n = Net0 /\ sof = {} /\ lsess = {} /\ lout = {} /\ closing = {} /\ supd = {} /\ sup = FALSE
        /\ busy = FALSE

\* start_fetch: Busy at FETCHES; the providers are taken whole or the fetch is refused
StartF(f, p) ==
    /\ f \notin Running(n) /\ Cardinality(Running(n)) < FETCHES
    /\ n' = Start(n, f, <<p>>, CAP).n
    /\ UNCHANGED <<sof, lsess, lout, closing, supd, sup, busy>>
\* open_stream: on the session we dialed to the provider; none, NotConnected and nothing changes
OpenF(f) ==
    /\ f \in Running(n)
    /\ LET num == HeldOf(n, f)[1]
           p == n.provs[num + 1].peer
           o == {x \in lout : x.peer = p}
       IN /\ o # {} /\ (CHOOSE x \in o : TRUE).sid \notin closing
          /\ LET r == OpenFor(n, f, 1, SCAP)
             IN /\ n' = r.n
                /\ sof' = IF NewLid(r) THEN sof \cup {[lid |-> r.lid, ses |-> (CHOOSE x \in o : TRUE).sid]} ELSE sof
    /\ UNCHANGED <<lsess, lout, closing, supd, sup, busy>>
\* the fetch drops one of its streams (a reset, an eviction)
DropF(l) ==
    /\ \E x \in n.streams : x.lid = l /\ x.owner # 0
    /\ n' = Drop(n, l) /\ sof' = Gone({l})
    /\ UNCHANGED <<lsess, lout, closing, supd, sup, busy>>
\* the fetch turns Done or is cancelled: its streams go (drop_all_streams, cancel_fetch), then end_fetch
EndF(f) ==
    /\ f \in Running(n)
    /\ LET L == {x.lid : x \in {y \in n.streams : y.owner = f}}
       IN n' = EndFetch(DropAll(n, L), f) /\ sof' = Gone(L)
    /\ UNCHANGED <<lsess, lout, closing, supd, sup, busy>>
\* VSess::hangup: lout forgets the session and it is closed; the table keeps it until the endpoint ends it
Hangup(p) ==
    /\ \E x \in lout : x.peer = p
    /\ closing' = closing \cup {x.sid : x \in {y \in lout : y.peer = p}}
    /\ lout' = {x \in lout : x.peer # p}
    /\ UNCHANGED <<n, sof, lsess, supd, sup, busy>>
\* layer_up of a values session (room in the layer table, and a second outgoing session for a peer we hold, are
\* the layer table's, modelled in NodeSets.tla; here an outgoing session comes up only for a peer with none);
\* an incoming one supersedes the peer's older incoming sessions: their streams go and they are closed
Up(sid, p, inc) ==
    /\ sid \in SIDS \ (LIds \cup closing)
    /\ inc \/ ~\E x \in lout : x.peer = p
    /\ LET old == IF inc THEN {x.sid : x \in {y \in lsess : y.peer = p /\ y.inc /\ y.sid \notin closing}} ELSE {}
                L == UNION {OfSession(s) : s \in old}
            IN /\ lsess' = lsess \cup {[sid |-> sid, peer |-> p, inc |-> inc]}
               /\ lout' = IF inc THEN lout ELSE lout \cup {[peer |-> p, sid |-> sid]}
               /\ n' = DropAll(n, L) /\ sof' = Gone(L)
               /\ closing' = closing \cup old
               /\ supd' = supd \cup old
               /\ sup' = (sup \/ L # {})
               /\ busy' = busy
\* layer_closed and values_down: the session leaves the table, and every stream on it goes
Closed(sid) ==
    /\ sid \in LIds
    /\ LET L == OfSession(sid)
       IN /\ n' = DropAll(n, L) /\ sof' = Gone(L)
          /\ lsess' = {x \in lsess : x.sid # sid}
          /\ lout' = {x \in lout : x.sid # sid}
          /\ closing' = closing \ {sid}
          /\ supd' = supd \ {sid}
    /\ UNCHANGED <<sup, busy>>
\* values_stream_opened: the request takes the peer's provider number and a stream, else it is abandoned with
\* BUSY; then the server takes it, or resets it with BUSY when its SERVERS slots are full
Request(sid) ==
    /\ sid \in LIds \ closing
    /\ LET p == (CHOOSE x \in lsess : x.sid = sid).peer
           r == Serve(n, p, CAP, SCAP)
       IN IF ~NewLid(r) THEN UNCHANGED <<n, sof, busy>>
          ELSE IF Cardinality(Serves) >= SERVERS THEN n' = Drop(r.n, r.lid) /\ sof' = sof /\ busy' = TRUE
          ELSE n' = r.n /\ sof' = sof \cup {[lid |-> r.lid, ses |-> sid]} /\ busy' = busy
    /\ UNCHANGED <<lsess, lout, closing, supd, sup>>
\* values_pacing: a served response is done (acknowledged) and its stream goes
ServeDone(l) ==
    /\ \E x \in Serves : x.lid = l
    /\ n' = Drop(n, l) /\ sof' = Gone({l})
    /\ UNCHANGED <<lsess, lout, closing, supd, sup, busy>>

Next == \/ \E f \in FIDS, p \in PEERS : StartF(f, p)
        \/ \E f \in FIDS : OpenF(f) \/ EndF(f)
        \/ \E x \in n.streams : DropF(x.lid) \/ ServeDone(x.lid)
        \/ \E p \in PEERS : Hangup(p)
        \/ \E sid \in SIDS, p \in PEERS, inc \in BOOLEAN : Up(sid, p, inc)
        \/ \E sid \in SIDS : Closed(sid) \/ Request(sid)
Spec == Init /\ [][Next]_vars
Bound == n.next <= NMAX

OnLive == /\ {x.lid : x \in sof} = {x.lid : x \in n.streams}
          /\ \A x \in sof : x.ses \in LIds /\ x.ses \notin supd
NoOrphan == \A x \in n.streams : x.owner # 0 => x.owner \in Running(n)
LoutSound == \A o \in lout : \E x \in lsess : x.sid = o.sid /\ x.peer = o.peer /\ ~x.inc
Inv == /\ Len(n.provs) <= CAP /\ Cardinality(n.streams) <= SCAP /\ Exact(n)
       /\ Cardinality(Running(n)) <= FETCHES /\ Cardinality(Serves) <= SERVERS
       /\ OnLive /\ NoOrphan /\ LoutSound

\* witnesses
NeverBusy == ~busy
NeverSuper == ~sup
=============================================================================
