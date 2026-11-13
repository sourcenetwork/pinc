------------------------------ MODULE BroadcastReach ------------------------------
(***************************************************************************)
(* Delivery scoped to the publisher's connected component (vinc#86):       *)
(* vinc-broadcast reach.rs (Topics::set_adjacent, Topics::on_adj,          *)
(* Topics::reach_timer) and reach/table.rs (Reach::take, Reach::class,     *)
(* Reach::rebuild, Reach::expire, Reach::leave, Reach::drop_gone,           *)
(* Scope::to), and the checks in msg.rs (Topics::hub_store), gap.rs       *)
(* (Topics::on_sub, Topics::on_get, Topics::have_to) and behind.rs        *)
(* (Topics::peer_writable).                                                *)
(*                                                                         *)
(* The story. Members open and close sessions with each other. Each member *)
(* tells its primary hub, in a signed record with a growing sequence       *)
(* number, which peers it holds sessions with; the frame may be lost, and  *)
(* the member sends its newest record again from time to time (the         *)
(* refresh). A hub keeps the newest record of every member, at most        *)
(* TableMax of them, mirrors each record a member hands it to the other    *)
(* hubs, keeps an edge only where both ends list each other, and labels    *)
(* each component of those edges by its least member. A hub that has not   *)
(* heard a record for a while expires it: the member stays scoped, alone,  *)
(* until it is heard again. A hub whose table is full refuses a newcomer's *)
(* record and closes: from then on a member it holds no record of is       *)
(* alone. A member may leave for good: its subscriptions are forgotten,    *)
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
(* every hub's components become the sessions' components.                 *)
(*                                                                         *)
(* Mutual = Rebuild = Tomb = ScopedRepair = Closed = TRUE and              *)
(* EvictAny = FALSE is the code.                                           *)
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
(* an older record a member sends itself after its incarnation went back.  *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/BroadcastReach.lean (labels_iff,     *)
(* edge_symm, reach_mono, split_narrows, closed_unknown_alone).            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences, TLC

\* N: the members are 1..N; HubCount: how many hubs there are; Liars: the members that may lie about their peers;
\* MaxChanges: how many times sessions open or close; MaxLoss: how many record frames may be lost; MaxExpire: how
\* many times a hub may expire a record; MaxLeave: how many members may leave for good; TableMax: the most records
\* one hub keeps (Limits::max_reach); Mutual, Rebuild, Tomb, ScopedRepair, Closed, EvictAny: the guards
CONSTANTS N, HubCount, Liars, MaxChanges, MaxLoss, MaxExpire, MaxLeave, TableMax,
          Mutual, Rebuild, Tomb, ScopedRepair, Closed, EvictAny

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
\* the members that left for good; logged: the origins each hub's log still holds a message of
VARIABLES sess, changes, cur, tab, lab, net, lost, expired, subd, bad, closed, refd, left, logged
vars == <<sess, changes, cur, tab, lab, net, lost, expired, subd, bad, closed, refd, left, logged>>

\* the peers member n holds sessions with, now
Nbrs(n) == {v \in Nodes : {n, v} \in sess}
\* the members reachable from the set S over the edges E, S included (a breadth-first walk to a fixed point)
RECURSIVE Closure(_, _)
Closure(E, S) == LET nxt == S \union {v \in Nodes : \E u \in S : {u, v} \in E}
                 IN IF nxt = S THEN S ELSE Closure(E, nxt)
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
Labels(t) == [n \in Nodes |-> Least(Closure(Edges(t), {n}))]
\* how many records the table t holds, expired ones included
Count(t) == Cardinality({n \in Nodes : t[n].seq > 0})
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
        /\ tab = [h \in Hubs |-> [n \in Nodes |-> None]]
        /\ lab = [h \in Hubs |-> [n \in Nodes |-> n]]
        /\ net = {[to |-> Prim(n), n |-> n, seq |-> 1, peers |-> {}, mir |-> FALSE] : n \in Nodes}
        /\ lost = 0 /\ expired = 0
        /\ subd = [h \in Hubs |-> {}] /\ bad = FALSE
        /\ closed = [h \in Hubs |-> FALSE] /\ refd = [h \in Hubs |-> {}] /\ left = {}
        /\ logged = [h \in Hubs |-> Nodes]

\* a session between u and v opens or closes (Event::Connected, Event::Closed in the facade); a member that left
\* opens none
Toggle(u, v) ==
    /\ u < v /\ changes < MaxChanges /\ u \notin left /\ v \notin left
    /\ sess' = IF {u, v} \in sess THEN sess \ {{u, v}} ELSE sess \union {{u, v}}
    /\ changes' = changes + 1
    /\ UNCHANGED <<cur, tab, lab, net, lost, expired, subd, bad, closed, refd, left, logged>>

\* the frame that carries member n's newest record to its primary hub
Frame(n) == [to |-> Prim(n), n |-> n, seq |-> cur[n].seq, peers |-> cur[n].peers, mir |-> FALSE]

\* an honest member names its sessions anew when they changed (Core::report_adjacent, Topics::set_adjacent)
Report(n) ==
    /\ n \notin Liars /\ n \notin left /\ cur[n].peers /= Nbrs(n) /\ cur[n].seq < MaxSeq
    /\ cur' = [cur EXCEPT ![n] = [seq |-> @.seq + 1, peers |-> Nbrs(n)]]
    /\ net' = net \union {[to |-> Prim(n), n |-> n, seq |-> cur[n].seq + 1, peers |-> Nbrs(n), mir |-> FALSE]}
    /\ UNCHANGED <<sess, changes, tab, lab, lost, expired, subd, bad, closed, refd, left, logged>>

\* a liar names any peers it likes, signed with its own key
Lie(n, P) ==
    /\ n \in Liars /\ n \notin left /\ n \notin P /\ P /= cur[n].peers /\ cur[n].seq < MaxSeq
    /\ cur' = [cur EXCEPT ![n] = [seq |-> @.seq + 1, peers |-> P]]
    /\ net' = net \union {[to |-> Prim(n), n |-> n, seq |-> cur[n].seq + 1, peers |-> P, mir |-> FALSE]}
    /\ UNCHANGED <<sess, changes, tab, lab, lost, expired, subd, bad, closed, refd, left, logged>>

\* the refresh (Topics::reach_timer): the member sends its newest record again
Refresh(n) ==
    /\ n \notin left /\ Frame(n) \notin net
    /\ net' = net \union {Frame(n)}
    /\ UNCHANGED <<sess, changes, cur, tab, lab, lost, expired, subd, bad, closed, refd, left, logged>>

\* a record frame is lost on the way
Lose(f) ==
    /\ f \in net /\ lost < MaxLoss
    /\ net' = net \ {f} /\ lost' = lost + 1
    /\ UNCHANGED <<sess, changes, cur, tab, lab, expired, subd, bad, closed, refd, left, logged>>

\* hub f.to takes a record frame (Topics::on_adj, Reach::take): a newer record, or the same one again over an expired
\* one, replaces what it holds and the labels are worked out again (with Rebuild; without it only for a member heard
\* for the first time); a record from a member, not from a hub, new or the same again (a refresh), is mirrored to the
\* other hubs; an older one is ignored. A newcomer that finds the table full is refused, and with Closed the table
\* closes; with EvictAny the hub instead drops an expired record, whatever its member, to make room.
Recv(f) ==
    /\ f \in net
    /\ LET h == f.to
           \* the record the hub holds of the frame's member
           old == tab[h][f.n]
           \* the frame is newer, or the same as an expired record
           takes == f.seq > old.seq \/ (f.seq = old.seq /\ ~old.live)
           \* a newcomer and no slot left
           full == old.seq = 0 /\ Count(tab[h]) >= TableMax
           \* the expired records an EvictAny hub could drop
           tombs == {v \in Nodes : tab[h][v].seq > 0 /\ ~tab[h][v].live}
           \* the record fits: a slot, or one made by EvictAny
           room == ~full \/ (EvictAny /\ tombs /= {})
           \* the member whose record EvictAny drops, or 0 for none
           gone == IF full /\ EvictAny /\ tombs /= {} THEN Least(tombs) ELSE 0
           \* the table after the drop and with the frame's record
           t1 == IF gone > 0 THEN [tab[h] EXCEPT ![gone] = None] ELSE tab[h]
           t2 == [t1 EXCEPT ![f.n] = [seq |-> f.seq, peers |-> f.peers, live |-> TRUE]]
           \* the copies a member's own record is mirrored as
           mirrors == {[to |-> o, n |-> f.n, seq |-> f.seq, peers |-> f.peers, mir |-> TRUE] : o \in Hubs \ {h}}
       IN /\ tab' = IF takes /\ room THEN [tab EXCEPT ![h] = t2] ELSE tab
          /\ lab' = IF takes /\ room /\ (Rebuild \/ old.seq = 0) THEN [lab EXCEPT ![h] = Labels(t2)] ELSE lab
          /\ closed' = IF takes /\ ~room /\ Closed THEN [closed EXCEPT ![h] = TRUE] ELSE closed
          /\ refd' = IF takes /\ ~room THEN [refd EXCEPT ![h] = @ \union {f.n}] ELSE refd
          /\ net' = (net \ {f}) \union (IF f.seq >= old.seq /\ ~f.mir /\ room THEN mirrors ELSE {})
    /\ UNCHANGED <<sess, changes, cur, lost, expired, subd, bad, left, logged>>

\* hub h expires its record of n (Reach::expire): with Tomb the record stays, naming no peer, so n is alone in its
\* component; without it the record is forgotten (sequence back to 0)
Expire(h, n) ==
    /\ tab[h][n].seq > 0 /\ tab[h][n].live /\ expired < MaxExpire
    /\ LET t2 == [tab[h] EXCEPT ![n] = IF Tomb THEN [@ EXCEPT !.live = FALSE] ELSE None]
       IN /\ tab' = [tab EXCEPT ![h] = t2]
          /\ lab' = IF Rebuild THEN [lab EXCEPT ![h] = Labels(t2)] ELSE lab
    /\ expired' = expired + 1
    /\ UNCHANGED <<sess, changes, cur, net, lost, subd, bad, closed, refd, left, logged>>

\* member n leaves for good with no session up (Topics::release on every hub, Reach::leave): the hubs forget its
\* subscriptions, and it sends and publishes nothing more
Leave(n) ==
    /\ n \notin left /\ Cardinality(left) < MaxLeave /\ Nbrs(n) = {}
    /\ left' = left \union {n}
    /\ subd' = [h \in Hubs |-> subd[h] \ {n}]
    /\ UNCHANGED <<sess, changes, cur, tab, lab, net, lost, expired, bad, closed, refd, logged>>

\* hub h's log lets the last message of a member that left go (the log window passes)
Drain(h, n) ==
    /\ n \in left /\ n \in logged[h]
    /\ logged' = [logged EXCEPT ![h] = @ \ {n}]
    /\ UNCHANGED <<sess, changes, cur, tab, lab, net, lost, expired, subd, bad, closed, refd, left>>

\* hub h drops the expired record of a member that left once its log holds nothing of it (Reach::drop_gone)
Drop(h, n) ==
    /\ n \in left /\ n \notin logged[h] /\ tab[h][n].seq > 0 /\ ~tab[h][n].live
    /\ LET t2 == [tab[h] EXCEPT ![n] = None]
       IN /\ tab' = [tab EXCEPT ![h] = t2]
          /\ lab' = IF Rebuild THEN [lab EXCEPT ![h] = Labels(t2)] ELSE lab
    /\ UNCHANGED <<sess, changes, cur, net, lost, expired, subd, bad, closed, refd, left, logged>>

\* member s subscribes at its primary hub; its record went first on the same stream, so the hub took it or its full
\* table refused it
Sub(s) ==
    /\ s \notin left /\ s \notin subd[Prim(s)]
    /\ tab[Prim(s)][s].seq > 0 \/ s \in refd[Prim(s)]
    /\ subd' = [subd EXCEPT ![Prim(s)] = @ \union {s}]
    /\ UNCHANGED <<sess, changes, cur, tab, lab, net, lost, expired, bad, closed, refd, left, logged>>

\* hub h hands o's logged message to subscriber s, checking reach (the push, Topics::hub_store) or, for a repair
\* answer (on_sub, on_get, have_to, peer_writable), checking it only with ScopedRepair; bad records a hand-over the
\* sessions do not justify. The publish and the mirror of messages are BroadcastPublish.tla's, so a hand-over is a
\* check at the current state, not a state of its own.
Hand(h, o, s, repair) ==
    /\ s \in subd[h] /\ o \in logged[h] /\ s /= o
    /\ (repair /\ ~ScopedRepair) \/ Allowed(h, o, s)
    /\ bad' = (bad \/ ~Linked(Good(h), o, s))
    /\ UNCHANGED <<sess, changes, cur, tab, lab, net, lost, expired, subd, closed, refd, left, logged>>

Next == \/ \E u, v \in Nodes : Toggle(u, v)
        \/ \E n \in Nodes : Report(n) \/ Refresh(n) \/ Sub(n) \/ Leave(n)
        \/ \E n \in Liars : \E P \in SUBSET (Nodes \ {n}) : Lie(n, P)
        \/ \E f \in net : Lose(f) \/ Recv(f)
        \/ \E h \in Hubs, n \in Nodes : Expire(h, n) \/ Drain(h, n) \/ Drop(h, n)
        \/ \E h \in Hubs, o, s \in Nodes, r \in BOOLEAN : Hand(h, o, s, r)

\* honest members report their changes, frames in flight arrive, and members refresh; losses and expiries are
\* bounded, so in the end every hub hears every member's newest record
Spec == /\ Init /\ [][Next]_vars
        /\ \A n \in Nodes : WF_vars(Report(n)) /\ WF_vars(Refresh(n))
        /\ \A h \in Hubs : \A n \in Nodes : WF_vars(\E f \in net : f.to = h /\ f.n = n /\ Recv(f))

(* ---------------------------- the checked properties ---------------------------- *)
\* a hub never hands a message to a subscriber that sessions, or a word still on its way, do not link to the origin
DeliverySound == ~bad
\* an edge a hub uses is one it may rightly use (the lemma DeliverySound rests on)
EdgesGood == \A h \in Hubs : Edges(tab[h]) \subseteq Good(h)
\* the labels a hub uses are those of its records (with Rebuild)
LabelsFresh == \A h \in Hubs : lab[h] = Labels(tab[h])
\* the tables stay within their bounds: sequence numbers, and at most TableMax records a hub
Bounds == /\ \A n \in Nodes : cur[n].seq <= MaxSeq
          /\ \A h \in Hubs : \A n \in Nodes : tab[h][n].seq <= cur[n].seq
          /\ \A h \in Hubs : Count(tab[h]) <= TableMax
\* once the sessions stop changing, every hub's components are the sessions' components (honest members only)
Converges == <>[](\A h \in Hubs : \A u, v \in Nodes : (lab[h][u] = lab[h][v]) <=> Linked(sess, u, v))
=============================================================================
