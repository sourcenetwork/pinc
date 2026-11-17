------------------------- MODULE ConnectMailboxOps -------------------------
(***************************************************************************)
(* The operators of the mailbox of vinc-connect/src/mailbox.rs and of the  *)
(* hold and wake step of relay/route.rs, as pure functions of the state.   *)
(* ConnectMailbox.tla (the model check) and TraceConnectMailbox.tla (the   *)
(* trace validation) both use these operators, so the two cannot differ.   *)
(*                                                                         *)
(* A configuration c has H (ENTRY_HEAD), B (BYTES of one member), N (NODES)*)
(* MaxPkt (MAX_PACKET_LEN), Age (max_age_ns), Rearm (WAKE_REARM_NS). The   *)
(* real values are 52, any B, any N, 1452, any age and 30e9; TLC checks    *)
(* small ones and the Lean theorems (ConnectMailbox.lean) hold for all.    *)
(*                                                                         *)
(* A member's ring is its (head, used, count) and the queue of messages it *)
(* holds, oldest first; a message is (src, flag, len, t, seq) and takes    *)
(* H + len bytes. The member table is the finite function held, which      *)
(* stands for the Table of table.rs (ConnectTable.tla refines it).         *)
(* Subtractions that the Rust code leaves unchecked (used -= size, count   *)
(* -= 1) stop TLC when they would underflow, so a finished check shows     *)
(* they are not reachable. u64 counters count events, 2^64 of them are not *)
(* reachable.                                                              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

Sat(x) == IF x < 0 THEN 0 ELSE x
Sub(a, b) == IF a >= b THEN a - b ELSE Assert(FALSE, "unchecked subtraction underflows")
Size(c, m) == c.H + m.len

ZeroStats == [stored |-> 0, delivered |-> 0, dropped |-> 0, droppedBytes |-> 0, expired |-> 0,
              oversize |-> 0, members |-> 0]
NewHeld == [q |-> <<>>, head |-> 0, used |-> 0, count |-> 0]
NoMsg == [src |-> 0, flag |-> 0, len |-> 0, t |-> 0, seq |-> 0]
Empty == [held |-> [x \in {} |-> NewHeld], seq |-> 0, st |-> ZeroStats]

Put(f, k, v) == [x \in DOMAIN f \cup {k} |-> IF x = k THEN v ELSE f[x]]
Del(f, k) == [x \in DOMAIN f \ {k} |-> f[x]]
Bump(st, k, n) == [st EXCEPT ![k] = @ + n]

(* Held::skip_front *)
SkipFront(c, h) ==
    IF h.q = <<>> THEN [h |-> h, fr |-> 0]
    ELSE LET m == Head(h.q) IN
         [h |-> [q |-> Tail(h.q), head |-> (h.head + Size(c, m)) % c.B, used |-> Sub(h.used, Size(c, m)),
                 count |-> Sub(h.count, 1)],
          fr |-> Size(c, m)]

(* Mailbox::expire: drop from the front while the front is at least Age old *)
RECURSIVE ExpireH(_, _, _)
ExpireH(c, now, h) ==
    IF h.q = <<>> \/ Sat(now - Head(h.q).t) < c.Age THEN [h |-> h, n |-> 0]
    ELSE LET r == ExpireH(c, now, SkipFront(c, h).h) IN [h |-> r.h, n |-> r.n + 1]

(* the quota loop of push: while used + size > B drop the oldest *)
RECURSIVE DropLoop(_, _, _, _)
DropLoop(c, size, h, st) ==
    IF h.used + size > c.B
    THEN LET s == SkipFront(c, h) IN
         IF s.fr = 0 THEN [h |-> h, st |-> st, d |-> 0]
         ELSE LET r == DropLoop(c, size, s.h, Bump(Bump(st, "dropped", 1), "droppedBytes", s.fr)) IN
              [h |-> r.h, st |-> r.st, d |-> r.d + 1]
    ELSE [h |-> h, st |-> st, d |-> 0]

(* Mailbox::push; res is "stored", "toolarge" or "noslot" *)
Push(c, mb, now, node, src, flag, len) ==
    LET size == c.H + len IN
    IF len = 0 \/ len > c.MaxPkt \/ size > c.B
    THEN [mb |-> [mb EXCEPT !.st = Bump(@, "oversize", 1)], res |-> "toolarge", seq |-> 0, dropped |-> 0, first |-> FALSE]
    ELSE IF node \notin DOMAIN mb.held /\ Cardinality(DOMAIN mb.held) >= c.N
    THEN [mb |-> [mb EXCEPT !.st = Bump(@, "members", 1)], res |-> "noslot", seq |-> 0, dropped |-> 0, first |-> FALSE]
    ELSE LET h0 == IF node \in DOMAIN mb.held THEN mb.held[node] ELSE NewHeld
             e == ExpireH(c, now, h0)
             first == e.h.count = 0
             d == DropLoop(c, size, e.h, Bump(mb.st, "expired", e.n))
             h3 == [q |-> Append(d.h.q, [src |-> src, flag |-> flag, len |-> len, t |-> now, seq |-> mb.seq]),
                    head |-> d.h.head, used |-> d.h.used + size, count |-> d.h.count + 1]
         IN [mb |-> [held |-> Put(mb.held, node, h3), seq |-> mb.seq + 1, st |-> Bump(d.st, "stored", 1)],
             res |-> "stored", seq |-> mb.seq, dropped |-> d.d, first |-> first]

(* Mailbox::look; got says a live message with a body of at most max is at the front, m is it. Nothing leaves but the
   expired messages: the message stays held, in front *)
Look(c, mb, now, node, max) ==
    IF node \notin DOMAIN mb.held THEN [mb |-> mb, got |-> FALSE, m |-> NoMsg]
    ELSE LET e == ExpireH(c, now, mb.held[node])
             ok == e.h.q # <<>> /\ Head(e.h.q).len <= max
         IN [mb |-> [held |-> IF e.h.count = 0 THEN Del(mb.held, node) ELSE Put(mb.held, node, e.h),
                     seq |-> mb.seq, st |-> Bump(mb.st, "expired", e.n)],
             got |-> ok, m |-> IF ok THEN Head(e.h.q) ELSE NoMsg]

(* Mailbox::remove (MbRemove, as Remove is the session table's): the front message leaves when it is the one
   numbered seq, and is counted delivered *)
MbRemove(c, mb, node, seq) ==
    IF node \notin DOMAIN mb.held \/ mb.held[node].q = <<>> \/ Head(mb.held[node].q).seq # seq THEN mb
    ELSE LET h2 == SkipFront(c, mb.held[node]).h IN
         [held |-> IF h2.count = 0 THEN Del(mb.held, node) ELSE Put(mb.held, node, h2),
          seq |-> mb.seq, st |-> Bump(mb.st, "delivered", 1)]

(* Mailbox::pop_fitting: the look followed by the removal of what it returned; max is the longest body the caller can
   deliver *)
Pop(c, mb, now, node, max) ==
    LET l == Look(c, mb, now, node, max) IN
    IF l.got THEN [mb |-> MbRemove(c, l.mb, node, l.m.seq), got |-> TRUE, m |-> l.m] ELSE l

(* Mailbox::sweep: expire every member, free the empty ones *)
Sweep(c, mb, now) ==
    LET ex == [x \in DOMAIN mb.held |-> ExpireH(c, now, mb.held[x])]
        keep == {x \in DOMAIN mb.held : ex[x].h.count > 0}
    IN [held |-> [x \in keep |-> ex[x].h], seq |-> mb.seq,
        st |-> Bump(mb.st, "expired", LET F[S \in SUBSET DOMAIN mb.held] ==
                       IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN ex[x].n + F[S \ {x}]
                  IN F[DOMAIN mb.held]) ]

(* Mailbox::clear *)
Clear(mb, node) ==
    IF node \in DOMAIN mb.held
    THEN [mb EXCEPT !.held = Del(@, node), !.st = Bump(@, "expired", mb.held[node].count)]
    ELSE mb

(* route.rs hold, the wake part: s is the Sleeper of the member ([woke |-> w]); returns the new woke and whether a
   wake-up is requested. Called only for a stored push. *)
ShouldWake(c, now, s, first) == first \/ Sat(now - s.woke) >= c.Rearm

(* the bytes and messages a member holds, as Mailbox::pending *)
Pending(mb, node) == IF node \in DOMAIN mb.held THEN <<mb.held[node].count, mb.held[node].used>> ELSE <<0, 0>>
=============================================================================
