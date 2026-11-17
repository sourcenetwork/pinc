--------------------------- MODULE ConnectMailbox ---------------------------
(***************************************************************************)
(* Model check of the mailbox (mailbox.rs) and of the hold and wake step   *)
(* of the relay (route.rs hold, discovery.rs sleep_notice), over the       *)
(* operators of ConnectMailboxOps.tla. The steps are Push (a packet for a  *)
(* member, through hold when a member sleeps), Pass (deliver_held), Sweep, *)
(* Clear, and the sleep mark of a member (SleepNotice, Return). Time is    *)
(* monotone and takes values of the finite set Times. A delivery pass is   *)
(* Look, the hand-over (which the caller may refuse), then Remove.         *)
(*                                                                         *)
(* Properties (Lean: Vinc/ConnectMailbox.lean):                            *)
(*  Bounds       used = sum of sizes <= B, count = length, members <= N,   *)
(*               head < B (mailbox_bounds)                                 *)
(*  Conserved    stored = delivered + dropped + expired + held             *)
(*               (conservation), so every loss is counted                  *)
(*  OrderOnce    messages leave in arrival order and each at most once    *)
(*               (order_once)                                              *)
(*  Age          a delivered message is younger than Age (age_bound)       *)
(*  RefusedKept  a message whose hand-over was refused is still held, in   *)
(*               front: a refusal never removes it                         *)
(*  DropOldest   the dropped messages are the oldest (drop_oldest)         *)
(*  Drain*       the release pass of the relay (DrainFit) is one ordered   *)
(*               walk of the member's queue that steps over a message too  *)
(*               long for the route: DrainOffered (it offers the fitting   *)
(*               messages in arrival order up to the one the taker refuses *)
(*               and none after it), DrainKept (what stays is the rest in  *)
(*               arrival order, none lost), DrainBooks (count and byte     *)
(*               total are those of what stays), DrainFresh (nothing       *)
(*               expired stays), DrainSteps (the same mailbox as LookFit   *)
(*               and RemoveSeq in steps); WithDrain adds the pass (ConnectMailbox_drain). Bug puts a fault in: ConnectMailbox_w{order,lose,bytes} *)
(*  WakeFirst    the first held message of a sleeping member requests a    *)
(*               wake; WakeSpaced: otherwise only Rearm after the last one *)
(*               (wake_first, wake_spaced)                                 *)
(***************************************************************************)
EXTENDS ConnectMailboxOps

CONSTANTS H, B, N, MaxPkt, Age, Rearm, Nodes, Srcs, Times, MaxSeq, Max, OldRule, Bug, WithDrain
c == [H |-> H, B |-> B, N |-> N, MaxPkt |-> MaxPkt, Age |-> Age, Rearm |-> Rearm]

VARIABLES mb, sl, clock, lastOut, lastPush, lastWake, popped, lastDrain
vars == <<mb, sl, clock, lastOut, lastPush, lastWake, popped, lastDrain>>

Init == /\ mb = Empty /\ sl = [x \in {} |-> 0] /\ clock = 0
        /\ lastOut = [node |-> 0, got |-> FALSE, m |-> NoMsg, now |-> 0, prev |-> -1, kept |-> TRUE]
        /\ lastPush = [res |-> "none", first |-> FALSE, sleeping |-> FALSE, fired |-> FALSE, droppedOldest |-> TRUE]
        /\ lastWake = [first |-> TRUE, gap |-> 0]
        /\ popped = {}
        /\ lastDrain = [node |-> 0, max |-> 0, k |-> 0, now |-> 0, live |-> <<>>, offered |-> <<>>, taken |-> <<>>,
                        kept |-> <<>>, cnt |-> 0, used |-> 0, same |-> TRUE]

Tick == \E t \in Times : t >= clock /\ clock' = t

\* hold: a packet for a member; when the member sleeps this is route.rs hold, else a bare push
DoPush(node, src, flag, len) ==
    /\ Tick /\ mb.seq < MaxSeq
    /\ LET r == Push(c, mb, clock', node, src, flag, len)
           s == sl[node]
           fire == node \in DOMAIN sl /\ r.res = "stored" /\ ShouldWake(c, clock', s, r.first)
           oldest == node \in DOMAIN mb.held => \A k \in 1..r.dropped : TRUE
       IN /\ mb' = r.mb
          /\ sl' = IF fire THEN Put(sl, node, [woke |-> clock']) ELSE sl
          /\ lastPush' = [res |-> r.res, first |-> r.first, sleeping |-> node \in DOMAIN sl, fired |-> fire,
                          droppedOldest |-> (r.res = "stored" => (r.dropped = 0 \/ node \in DOMAIN mb.held))]
          /\ lastWake' = IF fire THEN [first |-> r.first, gap |-> Sat(clock' - s.woke)] ELSE lastWake
    /\ UNCHANGED <<lastOut, popped, lastDrain>>

\* deliver_held: the oldest message is looked at, handed over (ok) or refused (~ok), and removed only when handed over.
\* OldRule is the code that removed it first: a refused message is then gone, which RefusedKept catches.
DoPass(node, max, ok) ==
    /\ Tick
    /\ LET l == Look(c, mb, clock', node, max)
           gone == l.got /\ (ok \/ OldRule)
           nm == IF gone THEN Pop(c, mb, clock', node, max).mb ELSE l.mb
       IN /\ mb' = nm
          /\ lastOut' = [node |-> node, got |-> gone, m |-> l.m, now |-> clock',
                         prev |-> IF node \in DOMAIN mb.held /\ mb.held[node].q # <<>> THEN Head(mb.held[node].q).seq ELSE -1,
                         kept |-> (l.got /\ ~ok) => (node \in DOMAIN nm.held /\ nm.held[node].q # <<>>
                                                    /\ Head(nm.held[node].q).seq = l.m.seq)]
          /\ popped' = IF ~gone THEN popped ELSE popped \cup {l.m.seq}
    /\ UNCHANGED <<sl, lastPush, lastWake, lastDrain>>

\* the witnesses put a wrong pass in place of DrainFit, one fault each (Bug): offers out of order, a kept message lost, a
\* byte total that leaves the headers of what was taken
Rev(q) == [i \in 1..Len(q) |-> q[Len(q) + 1 - i]]
Faulty(d) ==
    IF Bug = "order" THEN [d EXCEPT !.offered = Rev(@)]
    ELSE IF Bug = "lose" /\ d.kept # <<>>
         THEN [d EXCEPT !.kept = Tail(@), !.h = [q |-> Tail(d.kept), head |-> d.h.head,
                                                   used |-> Sub(d.h.used, Size(c, Head(d.kept))), count |-> d.h.count - 1]]
    ELSE IF Bug = "bytes" THEN [d EXCEPT !.h.used = @ + c.H * Len(d.taken)]
    ELSE d

\* the release pass: one ordered walk of the member's queue; the taker accepts the first k offers and then says stop
RECURSIVE Steps(_, _, _, _, _)
Steps(m, now, node, max, k) ==
    LET l == LookFit(c, m, now, node, max) IN
    IF k = 0 \/ ~l.got THEN l.mb ELSE Steps(RemoveSeq(c, l.mb, node, l.m.seq), now, node, max, k - 1)

DoDrain(node, max, k) ==
    /\ Tick
    /\ LET d == Faulty(DrainFit(c, mb, clock', node, max, k))
           nm == DrainMb(mb, node, d)
       IN /\ mb' = nm
          /\ lastDrain' = [node |-> node, max |-> max, k |-> k, now |-> clock', live |-> d.live, offered |-> d.offered,
                           taken |-> d.taken, kept |-> d.kept, cnt |-> d.h.count, used |-> d.h.used,
                           same |-> Steps(mb, clock', node, max, k) = nm]
          /\ popped' = popped \cup {d.taken[i].seq : i \in 1..Len(d.taken)}
    /\ UNCHANGED <<sl, lastOut, lastPush, lastWake>>

DoSweep == /\ Tick /\ mb' = Sweep(c, mb, clock') /\ UNCHANGED <<sl, lastOut, lastPush, lastWake, popped, lastDrain>>
DoClear(node) == /\ mb' = Clear(mb, node) /\ UNCHANGED <<sl, clock, lastOut, lastPush, lastWake, popped, lastDrain>>
\* sleep_notice keeps woke across a second notice; member_returned and carrier_opened clear the mark
DoSleep(node) == /\ sl' = Put(sl, node, IF node \in DOMAIN sl THEN sl[node] ELSE [woke |-> 0])
                 /\ UNCHANGED <<mb, clock, lastOut, lastPush, lastWake, popped, lastDrain>>
DoReturn(node) == /\ node \in DOMAIN sl /\ sl' = Del(sl, node) /\ UNCHANGED <<mb, clock, lastOut, lastPush, lastWake, popped, lastDrain>>

Next == \/ \E n \in Nodes, s \in Srcs, l \in 0..MaxPkt : DoPush(n, s, 0, l)
        \/ \E n \in Nodes, m \in {MaxPkt, 0}, ok \in BOOLEAN : DoPass(n, m, ok)
        \/ (WithDrain /\ \E n \in Nodes, m \in 0..MaxPkt, k \in 0..MaxSeq : DoDrain(n, m, k))
        \/ DoSweep \/ \E n \in Nodes : DoClear(n) \/ DoSleep(n) \/ DoReturn(n)

Spec == Init /\ [][Next]_vars

Held == mb.held
Sum(q) == LET F[i \in 0..Len(q)] == IF i = 0 THEN 0 ELSE F[i - 1] + Size(c, q[i]) IN F[Len(q)]
Total == LET F[S \in SUBSET DOMAIN Held] == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN Held[x].count + F[S \ {x}]
        IN F[DOMAIN Held]
Incr(q) == \A i \in 1..(Len(q) - 1) : q[i].seq < q[i + 1].seq

Bounds == /\ Cardinality(DOMAIN Held) <= N
          /\ \A x \in DOMAIN Held : LET h == Held[x] IN
               /\ h.used = Sum(h.q) /\ h.used <= B /\ h.count = Len(h.q) /\ h.count > 0 /\ h.head < B
               /\ \A i \in 1..Len(h.q) : h.q[i].len >= 1 /\ h.q[i].len <= MaxPkt /\ h.q[i].seq < mb.seq

Conserved == mb.st.stored = mb.st.delivered + mb.st.dropped + mb.st.expired + Total

\* delivered messages come out front first, each once
OrderOnce == /\ \A x \in DOMAIN Held : Incr(Held[x].q) /\ ~ \E i \in 1..Len(Held[x].q) : Held[x].q[i].seq \in popped
             /\ lastOut.got /\ lastOut.node \in DOMAIN Held => \A i \in 1..Len(Held[lastOut.node].q) : Held[lastOut.node].q[i].seq > lastOut.m.seq

AgeBound == lastOut.got => Sat(lastOut.now - lastOut.m.t) < Age
WakeFirst == (lastPush.res = "stored" /\ lastPush.sleeping /\ lastPush.first) => lastPush.fired
WakeSpaced == lastWake.first \/ lastWake.gap >= Rearm
DropOldest == lastPush.droppedOldest
RefusedKept == lastOut.kept
Range(q) == {q[i] : i \in 1..Len(q)}
\* the release pass offers exactly the fitting messages, in arrival order, up to the one the taker refuses, and nothing
\* after it; what it took is the front of them
DrainOffered == LET d == lastDrain fit == Fits(d.live, d.max)
                    stop == d.k < Len(fit)
                IN /\ d.offered = SubSeq(fit, 1, IF stop THEN d.k + 1 ELSE Len(fit))
                   /\ d.taken = SubSeq(d.offered, 1, Len(d.offered) - (IF stop THEN 1 ELSE 0))
\* what stays is the unexpired queue less what was taken, in arrival order, none lost
DrainKept == LET d == lastDrain IN
             /\ Incr(d.kept) /\ Len(d.kept) + Len(d.taken) = Len(d.live)
             /\ \A m \in Range(d.live) : m \in Range(d.kept) <=> m \notin Range(d.taken)
\* the count and the byte total of the member are those of what stays
DrainBooks == lastDrain.cnt = Len(lastDrain.kept) /\ lastDrain.used = Sum(lastDrain.kept)
\* nothing expired stays
DrainFresh == \A m \in Range(lastDrain.kept) : Sat(lastDrain.now - m.t) < Age
\* the one-walk pass leaves the mailbox the steps of LookFit and RemoveSeq leave
DrainSteps == lastDrain.same
\* bounds the refusal counters, which no step of the model otherwise limits
Bound == mb.st.oversize <= 1 /\ mb.st.members <= 1
=============================================================================
