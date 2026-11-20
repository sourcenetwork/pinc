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
(*  - LoutSound: lout names an outgoing values session of the table;       *)
(*  - NoLost (2d85e67e): the fetches hear of every stream of theirs a      *)
(*    closed session takes: one In::Reset (CANCELLED) per stream when a     *)
(*    session we dialed to the peer is still in lout (a stall redial hung  *)
(*    the closed one up and dialed anew), else one In::Closed of the        *)
(*    provider when the closed session was one we dialed; fk, the streams   *)
(*    the fetches still hold, is never a stream the table dropped;          *)
(*  - NoDownLive: a provider with a session in lout is never reported      *)
(*    closed.                                                              *)
(* A fetch that hangs a provider up (its stall redial) forgets its own     *)
(* streams of that provider; the table keeps them until the endpoint ends  *)
(* the session. TellOnce (no stream is told by a reset after the           *)
(* provider's Closed told it) is a documented finding, NodeValues_twice:   *)
(* the Closed of the redial's session covers the streams the fetch still   *)
(* held on the older hung-up one, and when that one ends after a third     *)
(* session came up, each is told again as a reset (the fetch ignores a     *)
(* reset of a stream it does not hold).                                    *)
(* Witnesses: NodeValues_busy (a request is refused for full server       *)
(* slots), NodeValues_super (a peer's new incoming session supersedes an   *)
(* older one that held a stream), NodeValues_lost (NoLost fails under the  *)
(* rule before 2d85e67e, TellOld: only the close of lout's own session was *)
(* told, as a Closed, so a fetch's streams on a session another fetch's    *)
(* redial hung up were dropped unheard).                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS PEERS, SIDS, CAP, SCAP, FIDS, FETCHES, SERVERS, NMAX
VARIABLES n, sof, lsess, lout, closing, supd, sup, busy, fk, tset, twice, downLive
vars == <<n, sof, lsess, lout, closing, supd, sup, busy, fk, tset, twice, downLive>>
ghost == <<fk, tset, twice, downLive>>

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
\* the peer of a provider number of the table
PeerOfNum(num) == IF num + 1 \in 1 .. Len(n.provs) THEN n.provs[num + 1].peer ELSE 0

Init == /\ n = Net0 /\ sof = {} /\ lsess = {} /\ lout = {} /\ closing = {} /\ supd = {} /\ sup = FALSE
        /\ busy = FALSE /\ fk = {} /\ tset = {} /\ twice = FALSE /\ downLive = FALSE

\* start_fetch: Busy at FETCHES; the providers are taken whole or the fetch is refused
StartF(f, p) ==
    /\ f \notin Running(n) /\ Cardinality(Running(n)) < FETCHES
    /\ n' = Start(n, f, <<p>>, CAP).n
    /\ UNCHANGED <<sof, lsess, lout, closing, supd, sup, busy>> /\ UNCHANGED ghost
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
                /\ fk' = IF NewLid(r) THEN fk \cup {r.lid} ELSE fk
    /\ UNCHANGED <<lsess, lout, closing, supd, sup, busy, tset, twice, downLive>>
\* the fetch drops one of its streams (a reset, an eviction)
DropF(l) ==
    /\ \E x \in n.streams : x.lid = l /\ x.owner # 0
    /\ n' = Drop(n, l) /\ sof' = Gone({l}) /\ fk' = fk \ {l}
    /\ UNCHANGED <<lsess, lout, closing, supd, sup, busy, tset, twice, downLive>>
\* the fetch turns Done or is cancelled: its streams go (drop_all_streams, cancel_fetch), then end_fetch
EndF(f) ==
    /\ f \in Running(n)
    /\ LET L == {x.lid : x \in {y \in n.streams : y.owner = f}}
       IN n' = EndFetch(DropAll(n, L), f) /\ sof' = Gone(L) /\ fk' = fk \ L
    /\ UNCHANGED <<lsess, lout, closing, supd, sup, busy, tset, twice, downLive>>
\* VSess::hangup by fetch f's stall redial: lout forgets the session and it is closed; the table keeps it until the
\* endpoint ends it; f forgets its own streams of the provider (drop_streams), the other fetches keep theirs
Hangup(f, p) ==
    /\ f \in Running(n) /\ \E k \in 1 .. Len(HeldOf(n, f)) : PeerOfNum(HeldOf(n, f)[k]) = p
    /\ \E x \in lout : x.peer = p
    /\ closing' = closing \cup {x.sid : x \in {y \in lout : y.peer = p}}
    /\ lout' = {x \in lout : x.peer # p}
    /\ fk' = fk \ {x.lid : x \in {y \in n.streams : y.owner = f /\ PeerOfNum(y.prov) = p}}
    /\ UNCHANGED <<n, sof, lsess, supd, sup, busy, tset, twice, downLive>>
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
               \* an incoming session carries no fetch stream (they open on lout's)
               /\ UNCHANGED ghost
\* what values_down tells the fetches of session s (ses) closing, lout1 being lout without it: closed, one In::Closed of
\* the provider to every fetch (a session we dialed and none of ours left to the peer); resets, one In::Reset per fetch
\* stream on it (else)
Tell(s, ses, lout1) ==
    LET down == ~s.inc /\ ~\E x \in lout1 : x.peer = s.peer
    IN [closed |-> down, resets |-> ~down]
\* before 2d85e67e: In::Closed only when the session was lout's own, nothing else
TellOld(s, ses, lout1) == [closed |-> \E x \in lout : x.sid = ses, resets |-> FALSE]
\* layer_closed and values_down: the session leaves the table, and every stream on it goes; the fetches are told
Closed(sid) ==
    /\ sid \in LIds
    /\ LET L == OfSession(sid)
           s == CHOOSE x \in lsess : x.sid = sid
           lout1 == {x \in lout : x.sid # sid}
           t == Tell(s, sid, lout1)
           FL == {x.lid : x \in {y \in n.streams : y.lid \in L /\ y.owner # 0}}
           n1 == DropAll(n, L)
           \* the provider is still in the table (lookup): some fetch holds it
           known == \E i \in 1 .. Len(n1.provs) : n1.provs[i].peer = s.peer
           \* In::Closed: every fetch drops every stream it holds of the provider, on any session
           CL == IF t.closed /\ known THEN {x.lid : x \in {y \in n.streams : y.owner # 0 /\ PeerOfNum(y.prov) = s.peer}}
                 ELSE {}
           RL == IF t.resets THEN FL ELSE {}
       IN /\ n' = n1 /\ sof' = Gone(L)
          /\ lsess' = {x \in lsess : x.sid # sid}
          /\ lout' = lout1
          /\ closing' = closing \ {sid}
          /\ supd' = supd \ {sid}
          /\ fk' = fk \ (CL \cup RL)
          /\ tset' = tset \cup (fk \cap (CL \cup RL))
          /\ twice' = (twice \/ RL \cap tset # {})
          /\ downLive' = (downLive \/ (t.closed /\ known /\ \E x \in lout1 : x.peer = s.peer))
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
    /\ UNCHANGED <<lsess, lout, closing, supd, sup>> /\ UNCHANGED ghost
\* values_pacing: a served response is done (acknowledged) and its stream goes
ServeDone(l) ==
    /\ \E x \in Serves : x.lid = l
    /\ n' = Drop(n, l) /\ sof' = Gone({l})
    /\ UNCHANGED <<lsess, lout, closing, supd, sup, busy>> /\ UNCHANGED ghost

Next == \/ \E f \in FIDS, p \in PEERS : StartF(f, p)
        \/ \E f \in FIDS : OpenF(f) \/ EndF(f)
        \/ \E x \in n.streams : DropF(x.lid) \/ ServeDone(x.lid)
        \/ \E f \in FIDS, p \in PEERS : Hangup(f, p)
        \/ \E sid \in SIDS, p \in PEERS, inc \in BOOLEAN : Up(sid, p, inc)
        \/ \E sid \in SIDS : Closed(sid) \/ Request(sid)
Spec == Init /\ [][Next]_vars
Bound == n.next <= NMAX

OnLive == /\ {x.lid : x \in sof} = {x.lid : x \in n.streams}
          /\ \A x \in sof : x.ses \in LIds /\ x.ses \notin supd
NoOrphan == \A x \in n.streams : x.owner # 0 => x.owner \in Running(n)
LoutSound == \A o \in lout : \E x \in lsess : x.sid = o.sid /\ x.peer = o.peer /\ ~x.inc
\* every stream a fetch still holds is a stream of the table: none was dropped unheard
NoLost == fk \subseteq {x.lid : x \in n.streams}
NoDownLive == ~downLive
TellOnce == ~twice
Inv == /\ Len(n.provs) <= CAP /\ Cardinality(n.streams) <= SCAP /\ Exact(n)
       /\ Cardinality(Running(n)) <= FETCHES /\ Cardinality(Serves) <= SERVERS
       /\ OnLive /\ NoOrphan /\ LoutSound /\ NoLost /\ NoDownLive

\* witnesses
NeverBusy == ~busy
NeverSuper == ~sup
=============================================================================
