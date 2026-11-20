------------------------------ MODULE BroadcastReach ------------------------------
(***************************************************************************)
(* Delivery scoped to the publisher's connected component (pinc#86):       *)
(* pinc-broadcast reach.rs (Topics::set_adjacent, Topics::on_adj,          *)
(* Topics::reach_timer) and reach/table.rs (Reach::take, Reach::class,     *)
(* Reach::rebuild, Reach::expire, Reach::leave, Reach::drop_gone,           *)
(* Reach::reopen, Scope::to), log.rs (HubLog::holds), the checks in msg.rs *)
(* (Topics::hub_store), gap.rs (Topics::on_sub, Topics::on_get,            *)
(* Topics::have_to) and behind.rs (Topics::peer_writable), and the facade's *)
(* report of its sessions: pinc engine.rs (Core::on_event, Core::service)  *)
(* and engine/topics.rs (Core::adjacent_changed, Core::report_adjacent).  *)
(*                                                                         *)
(* The story. Members open and close sessions with each other. The facade *)
(* runs in turns: it handles a turn's session events first, and only then *)
(* tells its primary hub, in one signed record with a growing sequence     *)
(* number, which peers it holds sessions with; the frame may be lost, and  *)
(* the member sends its newest record again from time to time (the         *)
(* refresh). A hub keeps the newest record of every member, charged in     *)
(* bytes (a fixed share, and a unit per peer while it is live) up to       *)
(* TableBytes, mirrors each record a member hands it to the other hubs,    *)
(* keeps an edge only where both ends list each other, and labels each     *)
(* component of those edges by its least member. A hub that has not heard  *)
(* a record for a while expires it: the member stays scoped, alone, until  *)
(* it is heard again. A hub refuses a record that does not fit: a newer    *)
(* one of a member it holds leaves that member a tombstone, alone, and the *)
(* table stays open; a newcomer's is refused and the table closes, and     *)
(* says so (an event for each refusal and one for the closing): while it  *)
(* is closed a member it holds no record of is                             *)
(* alone. It opens again, and says so, once no refused member waits: each *)
(* one got a record, or left with nothing of it in the log. A member may   *)
(* leave for good: its subscriptions are forgotten,                        *)
(* its messages drain out of the hub's log, and only then may the hub drop *)
(* its expired record. Members subscribe at their primary hub after their  *)
(* record (the same stream carries both, record first) and publish; a hub  *)
(* hands a logged message to a subscriber when their classes are equal, at *)
(* once (the push) or at any later time (a replay, a HAVE offer, a GET     *)
(* answer, a catch-up: repair). Some members may lie: they name any peers  *)
(* they like.                                                              *)
(*                                                                         *)
(* What must never happen (DeliverySound): a hub hands a message from o to *)
(* s while o and s are not linked by sessions that are up, or by edges the *)
(* hub holds only because an honest end's newer word has not reached it    *)
(* yet. And what must happen (Converges): once the sessions stop changing, *)
(* every hub's components become the sessions' components. Also: a member *)
(* signs at most one record a turn however many sessions came and went    *)
(* (BoundedReports), a hub's events say whether its table is closed and   *)
(* name every member it refused (ClosedTold), and a hub's record of a      *)
(* member goes back to an older one only over a tombstone and only from    *)
(* the member's own frame, never from a hub's mirror (NoRollback).        *)
(*                                                                         *)
(* Mutual = Rebuild = Tomb = ScopedRepair = Closed = Batch = Told = Waits  *)
(* = Charge = TRUE and EvictAny = FALSE is the code.                       *)
(* BroadcastReach_bytes.cfg sets Charge = FALSE: only a newcomer's record  *)
(* is checked against the bytes, as when the bound was a count of records, *)
(* so a member whose newer record names more peers is taken whatever it   *)
(* costs; TLC finds Bounds (the table within TableBytes) violated.         *)
(* BroadcastReach_perevent.cfg sets Batch = FALSE: a member names its      *)
(* sessions on every session event, as before the review of #137, so a     *)
(* member in two session changes of one turn signs two records; TLC finds  *)
(* BoundedReports violated.                                                *)
(* BroadcastReach_silent.cfg sets Told = FALSE: the table refuses and      *)
(* closes without an event, so whoever runs the hub cannot tell that every *)
(* member without a record is now alone; TLC finds ClosedTold violated.    *)
(* BroadcastReach_reopen.cfg sets Waits = FALSE: the table opens again     *)
(* while a refused member still has no record, so it counts as unscoped    *)
(* and hears another member without a record; TLC finds DeliverySound     *)
(* violated.                                                               *)
(* BroadcastReach_onesided.cfg sets Mutual = FALSE: an edge is kept on one *)
(* end's word, so a liar that names an honest member it has no session     *)
(* with hears that member; TLC finds DeliverySound violated.               *)
(* BroadcastReach_stale.cfg sets Rebuild = FALSE: the labels are worked    *)
(* out when a member is first heard and kept after its records change, so *)
(* after a split the hub still uses the joined component; TLC finds        *)
(* DeliverySound violated.                                                 *)
(* BroadcastReach_forget.cfg sets Tomb = FALSE: an expired record is       *)
(* forgotten, so its member counts as one that never named its peers, and *)
(* two such members hear each other; TLC finds DeliverySound violated.     *)
(* BroadcastReach_repair.cfg sets ScopedRepair = FALSE: the push is        *)
(* scoped and the repair answers are not, so a gap repair carries a        *)
(* message across groups; TLC finds DeliverySound violated.                *)
(* BroadcastReach_full.cfg sets Closed = FALSE: a full table refuses two   *)
(* newcomers and does not close, so both count as members that never      *)
(* named their peers and hear each other (the unscoped fallback); TLC     *)
(* finds DeliverySound violated.                                           *)
(* BroadcastReach_evict.cfg sets EvictAny = TRUE: a full table makes room  *)
(* by dropping any expired record, of a member still subscribed and still *)
(* logged, which then counts as unscoped; two such members hear each      *)
(* other; TLC finds DeliverySound violated.                                *)
(*                                                                         *)
(* Not modelled: the signature (a hub takes a record only from its member  *)
(* or from a hub, and only with the member's signature, before its table   *)
(* changes; a liar can sign only its own); the timing of expiry, refresh   *)
(* and the log's drain (each may happen at any time, which covers every    *)
(* timing the code allows); when the labels are worked out (the code works *)
(* them out lazily, before the first check after a change, so every check  *)
(* reads the labels of the current records, as Recv does here at once);    *)
(* unscoped members (they form one more class of their own, which no       *)
(* scoped member shares); hubs as origins or subscribers (never scoped);   *)
(* the incarnation (a sequence number stands for the pair (inc, seq); an   *)
(* older record a member sends itself, after its incarnation went back, is *)
(* any older frame of its own still in flight, which a tombstone takes);   *)
(* the 250 ms gap between two reports (an abstraction: a gap only moves a  *)
(* report to a later turn); a revoked member (forgotten, and no longer     *)
(* waiting); a hub that refused more members than it can remember (it     *)
(* stays closed, which DeliverySound allows).                              *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/BroadcastReach.lean (labels_iff,     *)
(* edge_symm, reach_mono, split_narrows, closed_unknown_alone,             *)
(* reopened_refused_iff, log_push_inv, log_pop_inv, log_holds_iff,        *)
(* running_charge, take_within, shrink_le).                                *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences, TLC

\* N: the members are 1..N; HubCount: how many hubs there are; Liars: the members that may lie about their peers;
\* MaxChanges: how many times sessions open or close; MaxLoss: how many record frames may be lost; MaxExpire: how
\* many times a hub may expire a record; MaxLeave: how many members may leave for good; TableBytes: the bytes one hub's
\* records may be charged (Limits::reach_bytes); RecBase: a live record's fixed share with its signature
\* (REACH_RECORD_BASE plus the signature), in the unit of one peer (32 bytes in the code); SigUnits: the signature's
\* part of RecBase, which a tombstone (record_cost(0, 0)) is not charged; Mutual, Rebuild, Tomb, ScopedRepair, Closed,
\* EvictAny, Batch, Told, Waits, Charge: the guards
CONSTANTS N, HubCount, Liars, MaxChanges, MaxLoss, MaxExpire, MaxLeave, TableBytes, RecBase, SigUnits,
          Mutual, Rebuild, Tomb, ScopedRepair, Closed, EvictAny, Batch, Told, Waits, Charge

ASSUME SigUnits \in 0..RecBase

\* the members, numbered from 1 so that 0 can mean "unscoped" and -n "n alone, with no record"
Nodes == 1..N
\* the hubs, numbered from 101 in order (a member's primary is picked from them), and as a set
HubList == [i \in 1..HubCount |-> 100 + i]
Hubs == {HubList[i] : i \in 1..Len(HubList)}
\* a member's primary hub: the members are spread over the hubs in turn
Prim(n) == HubList[1 + (n % Len(HubList))]
\* the most records one member may send: one per change of its sessions, its first one and a margin for a liar
MaxSeq == MaxChanges + 2

\* sess: the sessions that are up, each a set of two members; changes: how many opened or closed so far; cur: each
\* member's newest record (its sequence number and the peers it names); tab: each hub's record of each member
\* (sequence 0: none held; live FALSE: expired); lab: each hub's label of each member, worked out from its records;
\* net: the record frames in flight (to a hub; a mirrored copy is marked); lost, expired: how many frames were lost
\* and records expired; subd: the subscribers each hub holds; bad: a hub handed a message to a subscriber it must
\* not reach; closed: each hub's table refused a newcomer; refd: the members whose record each hub refused; left:
\* the members that left for good; logged: the origins each hub's log still holds a message of (HubLog::holds);
\* phase: whether the facade is handling a turn's session events or naming its peers after them; sent: how many
\* records each member signed this turn; said: whether each hub's last close or open event said closed; heard: the
\* members each hub reported refusing; bytes: the running charge of each hub's table (Reach::bytes)
VARIABLES sess, changes, cur, tab, lab, net, lost, expired, subd, bad, closed, refd, left, logged, phase, sent, said,
          heard, bytes
\* the variables of the turns and of the hub's events, which most actions leave alone
turnsAndEvents == <<phase, sent, said, heard>>
vars == <<sess, changes, cur, tab, lab, net, lost, expired, subd, bad, closed, refd, left, logged, phase, sent, said,
          heard, bytes>>

\* the peers member n holds sessions with, now
Nbrs(n) == {v \in Nodes : {n, v} \in sess}
\* the members reachable from the set S over the edges E, S included (a breadth-first walk to a fixed point)
\* TLC evaluates an operator's argument and a LET value again at each use inside a step, so the edges and each round of
\* the walk are bound once, as the one element of a set (UNION of a one-set set is that set)
RECURSIVE Walk(_, _)
Walk(E, S) == UNION {IF nxt = S THEN S ELSE Walk(E, nxt) : nxt \in {S \union {v \in Nodes : \E u \in S : {u, v} \in E}}}
Closure(E, S) == UNION {Walk(e, S) : e \in {E}}
\* whether u and v are in one component of the edges E
Linked(E, u, v) == v \in Closure(E, {u})
\* the least member of a non-empty set of members
Least(S) == CHOOSE x \in S : \A y \in S : x <= y

\* the peers a hub's record of n names: none when there is no record or it expired
HeldPeers(t, n) == IF t[n].seq > 0 /\ t[n].live THEN t[n].peers ELSE {}
\* the edges a hub's table t makes (Reach::rebuild): both ends name each other, or with Mutual off, either does
Edges(t) == {e \in SUBSET Nodes : Cardinality(e) = 2 /\
                \E u, v \in e : u /= v /\ u \in HeldPeers(t, v) /\ (~Mutual \/ v \in HeldPeers(t, u))}
\* the label of every member under the table t: the least member of its component
Labels(t) == CHOOSE l \in {[n \in Nodes |-> Least(Closure(e, {n}))] : e \in {Edges(t)}} : TRUE
\* one record's charge (reach/table.rs record_cost(peers, sig)): a live record its share with its signature and one unit
\* for every peer; a tombstone (expired or refused) names no peer and carries no signature, record_cost(0, 0); nothing
\* for no record
Cost(r) == IF r.seq = 0 THEN 0 ELSE IF r.live THEN RecBase + Cardinality(r.peers) ELSE RecBase - SigUnits
\* the bytes the table t is charged (Reach::bytes): the sum of its records' charges
RECURSIVE SumCost(_, _)
SumCost(t, S) == IF S = {} THEN 0 ELSE LET n == CHOOSE x \in S : TRUE IN Cost(t[n]) + SumCost(t, S \ {n})
Size(t) == SumCost(t, Nodes)
\* whether a table can be charged more than TableBytes at all: every member with a live record naming every other
\* member. A constant, so TLC works it out once; where it is FALSE no record is ever refused, and the step skips the
\* charge (TLC checks the fairness of a frame's arrival at every step, so the charge is the bulk of the run)
CanOverflow == TableBytes < N * (RecBase + N - 1)
\* a member's class at hub h (Reach::class): its label with a record (an expired record still counts: its label is
\* the member itself, alone); with none, alone (-n) once the table closed, otherwise unscoped (0)
Class(h, n) == IF tab[h][n].seq > 0 THEN lab[h][n] ELSE IF closed[h] THEN -n ELSE 0
\* whether hub h may hand a message from o to s (Scope::to)
Allowed(h, o, s) == Class(h, o) = Class(h, s)

\* an honest member whose word at hub h is behind the truth: the hub holds no live record of it, or one that names
\* other peers than the sessions it holds now (its newer word is still to arrive, in flight, lost or not yet sent)
Behind(h, n) == n \notin Liars /\ (tab[h][n].seq = 0 \/ ~tab[h][n].live \/ tab[h][n].peers /= Nbrs(n))
\* the edges a hub may rightly use: sessions that are up, an edge between two liars (they could open one), and an
\* edge it holds only because an honest end's newer word has not reached it
Good(h) == sess \union {e \in SUBSET Liars : Cardinality(e) = 2}
               \union {e \in Edges(tab[h]) : \E n \in e : Behind(h, n)}

\* the record a hub holds of nobody
None == [seq |-> 0, peers |-> {}, live |-> FALSE]

\* every member starts with a first record naming no peer (the facade names its peers from its start), the hubs
\* know nothing yet, and every member has a message in every hub's log
Init == /\ sess = {} /\ changes = 0
        /\ cur = [n \in Nodes |-> [seq |-> 1, peers |-> {}]]
        /\ tab = [h \in Hubs |-> [n \in Nodes |-> None]] /\ bytes = [h \in Hubs |-> 0]
        /\ lab = [h \in Hubs |-> [n \in Nodes |-> n]]
        /\ net = {[to |-> Prim(n), n |-> n, seq |-> 1, peers |-> {}, mir |-> FALSE] : n \in Nodes}
        /\ lost = 0 /\ expired = 0
        /\ subd = [h \in Hubs |-> {}] /\ bad = FALSE
        /\ closed = [h \in Hubs |-> FALSE] /\ refd = [h \in Hubs |-> {}] /\ left = {}
        /\ logged = [h \in Hubs |-> Nodes]
        /\ phase = "events" /\ sent = [n \in Nodes |-> 0]
        /\ said = [h \in Hubs |-> FALSE] /\ heard = [h \in Hubs |-> {}]

\* a session between u and v opens or closes in the turn's events (Event::Connected, Event::Incoming, Event::Closed
\* in Core::on_event, which only marks the peers to be named: Core::adjacent_changed); a member that left opens none.
\* Without Batch each end names its peers at once, on the event, as the code did before (the RED configuration)
Toggle(u, v) ==
    /\ phase = "events" /\ u < v /\ changes < MaxChanges /\ u \notin left /\ v \notin left
    /\ LET \* the sessions after this change
           s2 == IF {u, v} \in sess THEN sess \ {{u, v}} ELSE sess \union {{u, v}}
           \* the peers of x after it
           nb(x) == {w \in Nodes : {x, w} \in s2}
           \* the ends that name their peers on the event: none with Batch; else the honest ends with records to spare
           now == IF Batch THEN {} ELSE {x \in {u, v} : x \notin Liars /\ cur[x].seq < MaxSeq}
       IN /\ sess' = s2
          /\ cur' = [x \in Nodes |-> IF x \in now THEN [seq |-> cur[x].seq + 1, peers |-> nb(x)] ELSE cur[x]]
          /\ net' = net \union {[to |-> Prim(x), n |-> x, seq |-> cur[x].seq + 1, peers |-> nb(x), mir |-> FALSE] :
                                 x \in now}
          /\ sent' = [x \in Nodes |-> IF x \in now THEN sent[x] + 1 ELSE sent[x]]
    /\ changes' = changes + 1
    /\ UNCHANGED <<tab, bytes, lab, lost, expired, subd, bad, closed, refd, left, logged, phase, said, heard>>

\* some honest member's sessions changed since its last record, and it has a record to spare
Pending == \E n \in Nodes : n \notin Liars /\ n \notin left /\ cur[n].peers /= Nbrs(n) /\ cur[n].seq < MaxSeq

\* the turn's session events are all handled (Core::service once Core::drain found no more): the members name
\* their peers now. A turn that changed nothing names nothing, so it is not a step of its own here
EndTurn ==
    /\ phase = "events" /\ Pending /\ phase' = "report"
    /\ UNCHANGED <<sess, changes, cur, tab, bytes, lab, net, lost, expired, subd, bad, closed, refd, left, logged, sent, said,
                   heard>>

\* member n would name its peers in this turn: honest, still here, its sessions changed since its last record, a
\* record to spare, and none signed yet this turn
ReportReady(n) ==
    n \notin Liars /\ n \notin left /\ cur[n].peers /= Nbrs(n) /\ cur[n].seq < MaxSeq /\ sent[n] = 0

\* every member that had to name its peers did: the next turn starts, with no record signed in it yet
NextTurn ==
    /\ phase = "report" /\ \A n \in Nodes : ~ReportReady(n)
    /\ phase' = "events" /\ sent' = [n \in Nodes |-> 0]
    /\ UNCHANGED <<sess, changes, cur, tab, bytes, lab, net, lost, expired, subd, bad, closed, refd, left, logged, said,
                   heard>>

\* the frame that carries member n's newest record to its primary hub
Frame(n) == [to |-> Prim(n), n |-> n, seq |-> cur[n].seq, peers |-> cur[n].peers, mir |-> FALSE]

\* once the turn's events are handled, an honest member names its sessions anew when they changed: one signed record
\* for all of the turn's changes (Core::report_adjacent, Topics::set_adjacent)
Report(n) ==
    /\ phase = "report" /\ ReportReady(n)
    /\ cur' = [cur EXCEPT ![n] = [seq |-> @.seq + 1, peers |-> Nbrs(n)]]
    /\ net' = net \union {[to |-> Prim(n), n |-> n, seq |-> cur[n].seq + 1, peers |-> Nbrs(n), mir |-> FALSE]}
    /\ sent' = [sent EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<sess, changes, tab, bytes, lab, lost, expired, subd, bad, closed, refd, left, logged, phase, said, heard>>

\* a liar names any peers it likes, signed with its own key
Lie(n, P) ==
    /\ n \in Liars /\ n \notin left /\ n \notin P /\ P /= cur[n].peers /\ cur[n].seq < MaxSeq
    /\ cur' = [cur EXCEPT ![n] = [seq |-> @.seq + 1, peers |-> P]]
    /\ net' = net \union {[to |-> Prim(n), n |-> n, seq |-> cur[n].seq + 1, peers |-> P, mir |-> FALSE]}
    /\ UNCHANGED <<sess, changes, tab, bytes, lab, lost, expired, subd, bad, closed, refd, left, logged>> /\ UNCHANGED turnsAndEvents

\* the refresh (Topics::reach_timer): the member sends its newest record again
Refresh(n) ==
    /\ n \notin left /\ Frame(n) \notin net
    /\ net' = net \union {Frame(n)}
    /\ UNCHANGED <<sess, changes, cur, tab, bytes, lab, lost, expired, subd, bad, closed, refd, left, logged>> /\ UNCHANGED turnsAndEvents

\* a record frame is lost on the way
Lose(f) ==
    /\ f \in net /\ lost < MaxLoss
    /\ net' = net \ {f} /\ lost' = lost + 1
    /\ UNCHANGED <<sess, changes, cur, tab, bytes, lab, expired, subd, bad, closed, refd, left, logged>> /\ UNCHANGED turnsAndEvents

\* hub f.to takes a record frame (Topics::on_adj, Reach::take): a newer record, or the same one again over an expired
\* one, or over a tombstone an older one from the member itself (never from a hub's mirror), replaces what it holds and the labels are worked out again (with Rebuild; without it only for a member heard
\* for the first time); a record from a member, not from a hub, new or the same again (a refresh), is mirrored to the
\* other hubs, as is an older one a tombstone took; any other older one is ignored. A record whose charge does not fit TableBytes is refused: a newcomer's, and
\* with Closed the table closes; a newer one of a member the hub holds, which leaves that member a tombstone (alone,
\* the table stays open). With EvictAny the hub instead drops an expired record, whatever its member, to make room.
\* Without Charge only a newcomer's record is checked, as when the bound counted records.
Recv(f) ==
    /\ f \in net
    /\ LET h == f.to
           \* the record the hub holds of the frame's member
           old == tab[h][f.n]
           \* the frame is newer; or the held record is a tombstone (or none) and the frame is the same, or older and
           \* from the member itself (table.rs: an older one is refused only over a live record or from a mirror)
           takes == f.seq > old.seq \/ (~old.live /\ (f.seq = old.seq \/ ~f.mir))
           \* the frame's record, and the table with it in place of the one held
           new == [seq |-> f.seq, peers |-> f.peers, live |-> TRUE]
           t0 == [tab[h] EXCEPT ![f.n] = new]
           \* the running charge with it: the held record's charge out, the new one's in (Reach::take)
           b0 == bytes[h] - Cost(old) + Cost(new)
           \* the record does not fit: the charge with it exceeds the bytes (without Charge, only for a newcomer)
           full == CanOverflow /\ b0 > TableBytes /\ (Charge \/ old.seq = 0)
           \* the expired records of other members an EvictAny hub could drop
           tombs == {v \in Nodes \ {f.n} : tab[h][v].seq > 0 /\ ~tab[h][v].live}
           \* the member whose record EvictAny drops, or 0 for none
           gone == IF full /\ EvictAny /\ tombs /= {} THEN Least(tombs) ELSE 0
           b2 == IF gone > 0 THEN b0 - Cost(tab[h][gone]) ELSE b0
           \* the record fits, or fits once EvictAny made room
           room == ~full \/ (gone > 0 /\ b2 <= TableBytes)
           \* the refusal closes the table: a newcomer's, with Closed
           closes == takes /\ ~room /\ Closed /\ old.seq = 0
           \* the copies a member's own record is mirrored as
           mirrors == {[to |-> o, n |-> f.n, seq |-> f.seq, peers |-> f.peers, mir |-> TRUE] : o \in Hubs \ {h}}
       IN \* t2: the table after the drop, with the frame's record; tomb: a refused member the hub holds a record of is
          \* left a tombstone that names no peer and carries the refused record's number, so the record it replaced is
          \* older and a late mirror of it is not taken again (each bound once, as the one element of a set)
          \E t2 \in {IF gone > 0 THEN [t0 EXCEPT ![gone] = None] ELSE t0},
             tomb \in {[tab[h] EXCEPT ![f.n] = [@ EXCEPT !.live = FALSE, !.seq = f.seq]]} :
          /\ tab' = IF takes /\ room THEN [tab EXCEPT ![h] = t2]
                    ELSE IF takes /\ old.seq > 0 THEN [tab EXCEPT ![h] = tomb] ELSE tab
          /\ bytes' = IF takes /\ room THEN [bytes EXCEPT ![h] = b2]
                      ELSE IF takes /\ old.seq > 0 THEN [bytes EXCEPT ![h] = @ - Cost(old) + Cost(tomb[f.n])] ELSE bytes
          /\ lab' = IF takes /\ room /\ (Rebuild \/ old.seq = 0) THEN [lab EXCEPT ![h] = Labels(t2)]
                    ELSE IF takes /\ ~room /\ old.seq > 0 /\ Rebuild THEN [lab EXCEPT ![h] = Labels(tomb)] ELSE lab
          /\ closed' = IF closes THEN [closed EXCEPT ![h] = TRUE] ELSE closed
          /\ refd' = IF takes /\ ~room THEN [refd EXCEPT ![h] = @ \union {f.n}] ELSE refd
          \* with Told the hub reports the refusal (Event::ReachRefused) and the closing (Event::ReachClosed)
          /\ heard' = IF takes /\ ~room /\ Told THEN [heard EXCEPT ![h] = @ \union {f.n}] ELSE heard
          /\ said' = IF closes /\ Told THEN [said EXCEPT ![h] = TRUE] ELSE said
          /\ net' = (net \ {f}) \union (IF (f.seq >= old.seq \/ takes) /\ ~f.mir /\ room THEN mirrors ELSE {})
    /\ UNCHANGED <<sess, changes, cur, lost, expired, subd, bad, left, logged, phase, sent>>

\* hub h expires its record of n (Reach::expire): with Tomb the record stays, naming no peer, so n is alone in its
\* component; without it the record is forgotten (sequence back to 0)
Expire(h, n) ==
    /\ tab[h][n].seq > 0 /\ tab[h][n].live /\ expired < MaxExpire
    /\ \E t2 \in {[tab[h] EXCEPT ![n] = IF Tomb THEN [@ EXCEPT !.live = FALSE] ELSE None]} :
          /\ tab' = [tab EXCEPT ![h] = t2]
          /\ bytes' = [bytes EXCEPT ![h] = @ - Cost(tab[h][n]) + Cost(t2[n])]
          /\ lab' = IF Rebuild THEN [lab EXCEPT ![h] = Labels(t2)] ELSE lab
    /\ expired' = expired + 1
    /\ UNCHANGED <<sess, changes, cur, net, lost, subd, bad, closed, refd, left, logged>> /\ UNCHANGED turnsAndEvents

\* member n leaves for good with no session up (Topics::release on every hub, Reach::leave): the hubs forget its
\* subscriptions, and it sends and publishes nothing more
Leave(n) ==
    /\ n \notin left /\ Cardinality(left) < MaxLeave /\ Nbrs(n) = {}
    /\ left' = left \union {n}
    /\ subd' = [h \in Hubs |-> subd[h] \ {n}]
    /\ UNCHANGED <<sess, changes, cur, tab, bytes, lab, net, lost, expired, bad, closed, refd, logged>> /\ UNCHANGED turnsAndEvents

\* hub h's log lets the last message of a member that left go (the log window passes)
Drain(h, n) ==
    /\ n \in left /\ n \in logged[h]
    /\ logged' = [logged EXCEPT ![h] = @ \ {n}]
    /\ UNCHANGED <<sess, changes, cur, tab, bytes, lab, net, lost, expired, subd, bad, closed, refd, left>> /\ UNCHANGED turnsAndEvents

\* hub h drops the expired record of a member that left once its log holds nothing of it (Reach::drop_gone)
Drop(h, n) ==
    /\ n \in left /\ n \notin logged[h] /\ tab[h][n].seq > 0 /\ ~tab[h][n].live
    /\ \E t2 \in {[tab[h] EXCEPT ![n] = None]} :
          /\ tab' = [tab EXCEPT ![h] = t2]
          /\ bytes' = [bytes EXCEPT ![h] = @ - Cost(tab[h][n])]
          /\ lab' = IF Rebuild THEN [lab EXCEPT ![h] = Labels(t2)] ELSE lab
    /\ UNCHANGED <<sess, changes, cur, net, lost, expired, subd, bad, closed, refd, left, logged>> /\ UNCHANGED turnsAndEvents

\* the members hub h refused that still wait for a record: no record now, and not gone for good with nothing of
\* theirs left in its log (Reach::waiting)
Waiting(h) == {n \in refd[h] : tab[h][n].seq = 0 /\ ~(n \in left /\ n \notin logged[h])}

\* hub h's closed table opens again on its sweep (Reach::reopen, Topics::reach_timer) once no refused member waits,
\* or with Waits off whenever it likes; with Told it reports it (Event::ReachOpened)
Reopen(h) ==
    /\ closed[h] /\ (~Waits \/ Waiting(h) = {})
    /\ closed' = [closed EXCEPT ![h] = FALSE]
    /\ said' = IF Told THEN [said EXCEPT ![h] = FALSE] ELSE said
    /\ UNCHANGED <<sess, changes, cur, tab, bytes, lab, net, lost, expired, subd, bad, refd, left, logged, phase, sent, heard>>

\* member s subscribes at its primary hub; its record went first on the same stream, so the hub took it or its full
\* table refused it
Sub(s) ==
    /\ s \notin left /\ s \notin subd[Prim(s)]
    /\ tab[Prim(s)][s].seq > 0 \/ s \in refd[Prim(s)]
    /\ subd' = [subd EXCEPT ![Prim(s)] = @ \union {s}]
    /\ UNCHANGED <<sess, changes, cur, tab, bytes, lab, net, lost, expired, bad, closed, refd, left, logged>> /\ UNCHANGED turnsAndEvents

\* hub h hands o's logged message to subscriber s, checking reach (the push, Topics::hub_store) or, for a repair
\* answer (on_sub, on_get, have_to, peer_writable), checking it only with ScopedRepair; bad records a hand-over the
\* sessions do not justify. The publish and the mirror of messages are BroadcastPublish.tla's, so a hand-over is a
\* check at the current state, not a state of its own.
Hand(h, o, s, repair) ==
    /\ s \in subd[h] /\ o \in logged[h] /\ s /= o
    /\ (repair /\ ~ScopedRepair) \/ Allowed(h, o, s)
    /\ bad' = (bad \/ ~Linked(Good(h), o, s))
    /\ UNCHANGED <<sess, changes, cur, tab, bytes, lab, net, lost, expired, subd, closed, refd, left, logged>> /\ UNCHANGED turnsAndEvents

Next == \/ \E u, v \in Nodes : Toggle(u, v)
        \/ EndTurn \/ NextTurn
        \/ \E n \in Nodes : Report(n) \/ Refresh(n) \/ Sub(n) \/ Leave(n)
        \/ \E n \in Liars : \E P \in SUBSET (Nodes \ {n}) : Lie(n, P)
        \/ \E f \in net : Lose(f) \/ Recv(f)
        \/ \E h \in Hubs : Reopen(h)
        \/ \E h \in Hubs, n \in Nodes : Expire(h, n) \/ Drain(h, n) \/ Drop(h, n)
        \/ \E h \in Hubs, o, s \in Nodes, r \in BOOLEAN : Hand(h, o, s, r)

\* turns end and start again, honest members report their changes, frames in flight arrive, and members refresh;
\* losses and expiries are bounded, so in the end every hub hears every member's newest record. Each is weak fairness,
\* WF_vars(EndTurn) /\ WF_vars(NextTurn) /\ WF_vars(Report(n)) /\ WF_vars(Refresh(n)) and, per hub h and member n,
\* WF_vars(\E f \in net : f.to = h /\ f.n = n /\ Recv(f)), written out so that TLC does not try every successor of
\* every state to work out ENABLED. WF_vars(A) is []<>~(ENABLED <<A>>_vars) \/ []<><<A>>_vars, and ENABLED is the
\* guard of each (each step of these changes a variable). EndTurn sets phase, NextTurn sets phase, Report(n) counts
\* sent[n] and Refresh(n) puts Frame(n) in net, so each of them is followed by a state where it is disabled: []<><<A>>
\* implies []<>~ENABLED, and the fairness is []<>~ENABLED alone. A frame in net can always be received and leaves net
\* (its mirrors go to the other hubs), and only Recv and Lose take a frame out of net, Lose counting it in lost: so a
\* step of Next that takes a frame of n to h out of net with lost unchanged is a receipt of one (RecvOf)
InFlight(h, n) == \E f \in net : f.to = h /\ f.n = n
RecvOf(h, n) == \E f \in net : f.to = h /\ f.n = n /\ f \notin net' /\ lost' = lost
Spec == /\ Init /\ [][Next]_vars
        /\ []<>~(phase = "events" /\ Pending)
        /\ []<>~(phase = "report" /\ \A m \in Nodes : ~ReportReady(m))
        /\ \A n \in Nodes : []<>~(phase = "report" /\ ReportReady(n)) /\ []<>~(n \notin left /\ Frame(n) \notin net)
        /\ \A h \in Hubs : \A n \in Nodes : []<>~InFlight(h, n) \/ []<><<RecvOf(h, n)>>_vars

(* ---------------------------- the checked properties ---------------------------- *)
\* a hub never hands a message to a subscriber that sessions, or a word still on its way, do not link to the origin
DeliverySound == ~bad
\* an edge a hub uses is one it may rightly use (the lemma DeliverySound rests on)
EdgesGood == \A h \in Hubs : Edges(tab[h]) \subseteq Good(h)
\* the labels a hub uses are those of its records (with Rebuild)
LabelsFresh == \A h \in Hubs : lab[h] = Labels(tab[h])
\* the tables stay within their bounds: sequence numbers, and at most TableBytes charged a hub, where the running charge
\* a hub keeps is the charge of its records worked out again
Bounds == /\ \A n \in Nodes : cur[n].seq <= MaxSeq
          /\ \A h \in Hubs : \A n \in Nodes : tab[h][n].seq <= cur[n].seq
          /\ \A h \in Hubs : bytes[h] = Size(tab[h]) /\ Size(tab[h]) <= TableBytes
\* an honest member signs at most one record a turn, however many of its sessions came and went in it
BoundedReports == \A n \in Nodes \ Liars : sent[n] <= 1
\* a hub's events tell the truth about its table: the last of them says closed exactly while it is, and every member
\* it refused was reported
ClosedTold == \A h \in Hubs : (said[h] <=> closed[h]) /\ refd[h] \subseteq heard[h]
\* a witness, not a promise: a table that refused a member stays closed. BroadcastReach_reopened.cfg must find it
\* violated, which shows the guarded Reopen is reachable (a slot freed and the refused member's record took it)
StaysClosed == \A h \in Hubs : refd[h] /= {} => closed[h]
\* table.rs Reach::take: no rollback over a live record, and none from a mirror: a hub's record of a member is replaced
\* by one with a lower sequence number only over a tombstone and only by the member's own frame (a drop to no record,
\* sequence 0, is Reach::drop_gone or a forget without Tomb)
NoRollback == [][\A h \in Hubs, n \in Nodes :
                   (tab'[h][n].seq > 0 /\ tab'[h][n].seq < tab[h][n].seq) =>
                       /\ ~tab[h][n].live
                       /\ \E f \in net \ net' : f.to = h /\ f.n = n /\ ~f.mir /\ f.seq = tab'[h][n].seq]_vars
\* once the sessions stop changing, every hub's components are the sessions' components (honest members only)
Converges == <>[](\A h \in Hubs : \A u, v \in Nodes : (lab[h][u] = lab[h][v]) <=> Linked(sess, u, v))
\* the quick profiles of BroadcastReach_table and BroadcastReach_hubs3 (proofs/tla/quick): runs of at most 8 steps
BroadcastReach_tableQuickBound == TLCGet("level") <= 8
BroadcastReach_hubs3QuickBound == TLCGet("level") <= 8
=============================================================================
