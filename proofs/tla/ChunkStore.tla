------------------------------ MODULE ChunkStore ------------------------------
(***************************************************************************)
(* The endpoint's chunk store (pinc#651).                                  *)
(*                                                                         *)
(* Who acts: the slots of one endpoint, their sessions, and the one store  *)
(* of 16 KiB chunks they all take their buffers from. The store is made    *)
(* with the endpoint and never grows, shrinks or frees anything.           *)
(*                                                                         *)
(* What can happen: every slot has a floor of F chunks set aside from the  *)
(* start; above it a slot reserves from the burst room, what is left once  *)
(* every floor is set aside. A peer dials and its session is admitted. A   *)
(* live session opens a stream and grants the peer a window of W chunks,   *)
(* which it first reserves; if the burst room cannot cover it the grant is *)
(* deferred and the slot joins a first-in first-out queue. Room given back *)
(* goes to the oldest waiter first, reserved for it at once, and its       *)
(* session is told to grant again. The peer's data arrives into chunks     *)
(* taken from the store; the application reads them and they go back. A    *)
(* stream ends once read, and its reservation shrinks back to the floor. A *)
(* session closes and gives everything above the floor back.               *)
(*                                                                         *)
(* What must never happen:                                                 *)
(*  - the reservations passing the store (Conservation), a session holding *)
(*    a chunk its reservation does not cover (UsedWithinRes), a chunk held *)
(*    by two sessions (OneOwner), a granted window the reservation does    *)
(*    not cover (Backing), a live session below its floor (FloorHeld), a   *)
(*    session reading bytes another session wrote (NoForeignBytes), a peer *)
(*    refused for want of a floor (NoneRefused), or a deferred grant out   *)
(*    of the queue with no wake on its way (QueueIsDeferred);              *)
(*  - a granted window that never fills (WindowsDrain): the worst case is  *)
(*    that nothing of a window can be read until all of it arrived (a hole *)
(*    at its start), so a window that finds no chunk would wait for ever;  *)
(*  - a peer that keeps dialling never being admitted (NewcomerIn);        *)
(*  - a deferred grant never being made (DeferEnds): once the others go    *)
(*    quiet the room comes back, and the queue hands it to the waiters in  *)
(*    order, which nothing of the waiter's own would do.                   *)
(*                                                                         *)
(* Code: crates/pinc-transport/src/stream/store.rs (ChunkStore::new sets   *)
(* the floors aside; grow, shrink, release, wait, leave, serve, pop_ready, *)
(* take, give); stream/pool.rs (BufferPool::make_room, trim, alloc_chunk); *)
(* stream/table.rs (Streams::grant reserves the window or waits,           *)
(* Streams::settle trims at a stream's end, Streams::regrant); pinc-core/  *)
(* src/endpoint.rs (Endpoint::free_slot releases, wake_store drains        *)
(* pop_ready). Lean counterpart: proofs/lean/Pinc/ChunkStore.lean.         *)
(* The stream credit is a soft promise and is left out: a credited stream  *)
(* takes no chunk before its data arrives, and a frame of its opening      *)
(* window is held back and sent again when it finds none (counted as       *)
(* StoreStats::shortage_first), which a window that is granted must never  *)
(* be; the Hoard RED shows what reserving it does.                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

\* Sessions are the endpoint's slots; B is the store's chunks; F the floor;
\* Cap a session's pool; W a window; G and Cl bound the grants and closes so
\* that every run goes quiet in the end.
CONSTANTS Sessions, B, F, Cap, W, G, Cl
\* The guards; a RED configuration breaks one. Floor: every slot's floor is
\* set aside from the start, so bursts draw only from the rest. Clear: a
\* foreign chunk is zeroed. ResCheck: a chunk is taken only inside the
\* reservation. Backed: a window is granted only when reserved. Hoard: TRUE
\* reserves the credit and keeps it (the bug fixed in #651). Release: a
\* closed session gives its reservation back. Wake: room given back is
\* handed to the waiters and wakes them. WantAll: a deferred grant queues for
\* all the room its check asks for (Streams::grant queues the window with the
\* stream credit kept beside it, the sum the check measures).
CONSTANTS Floor, Clear, ResCheck, Backed, Hoard, Release, Wake, WantAll

\* The chunks of the store, by number.
Chunks == 1..B
\* No session holds the chunk.
None == 0
\* The chunk was never handed out: it is still the system's zero page.
Fresh == 0
\* The session that last held the chunk has ended: its bytes are foreign to all.
Gone == 100
\* What a slot keeps whatever it does: its floor when floors are set aside.
Base == IF Floor THEN F ELSE 0
\* The most a slot can ever reserve: its floor and the whole burst room.
MostRes == F + (B - Cardinality(Sessions) * F)

\* sent: of the chunks a session holds, those its own writes hold until the
\* peer acknowledges them (at most one, to keep the model small).
\* want: the peer dials. live: the session is admitted. res: its reservation.
\* used: chunks it holds, sent ones included. owed: chunks of its granted
\* window not yet arrived. open: a stream is open. owner: who holds each
\* chunk. last: who held it last. leak: a session was handed another's
\* bytes. grants, closes: counts. defer: the session's window grant found no
\* room and waits. queue: the waiting slots, oldest first. wantq: the
\* reservation each waiter waits for. poke: the waiter's room was reserved
\* and it is told to grant again. refused: a peer was refused for want of a
\* floor.
VARIABLES sent, want, live, res, used, owed, open, owner, last, leak, grants, closes,
          defer, queue, wantq, poke, refused

vars == <<sent, want, live, res, used, owed, open, owner, last, leak, grants, closes,
          defer, queue, wantq, poke, refused>>

\* The smaller and the larger of two numbers.
Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

\* The sum of f over a set of sessions, one session at a time.
RECURSIVE SumOver(_, _)
SumOver(f, S) == IF S = {} THEN 0
                 ELSE LET s == CHOOSE x \in S : TRUE
                      IN f[s] + SumOver(f, S \ {s})

\* The chunks every slot has reserved together, floors included.
Reserved == SumOver(res, Sessions)
\* The chunks no slot has reserved: the burst room left.
Unreserved == B - Reserved
\* The sessions in the queue.
InQueue == {queue[i] : i \in 1..Len(queue)}
\* The queue without session s.
Drop(q, s) == SelectSeq(q, LAMBDA x : x /= s)
\* A slot may grow only while no one waits, or when it is the oldest waiter
\* (ChunkStore::grow): no slot passes the queue.
CanGrow(s) == queue = <<>> \/ Head(queue) = s

\* The reservation a grant of session s holding u chunks asks for
\* (make_room): the window beside what it holds, within the pool and within
\* what the burst room can ever give it. The Hoard RED asks for the pool.
WantAt(s, u) == Min(IF Hoard THEN Cap ELSE Min(Cap, u + W), MostRes)
\* What a deferred grant queues for: its whole want. The WantAll RED queues
\* for one chunk less, as the code did when it left the stream credit beside
\* the window out of the want while its check still asked for it.
QueueWantAt(s, u) == IF WantAll THEN WantAt(s, u) ELSE WantAt(s, u) - 1
\* What the reservation becomes: as far as the burst room allows.
GrantResAt(s, u) == LET room == IF CanGrow(s) THEN Unreserved ELSE 0
                    IN res[s] + Min(Max(WantAt(s, u) - res[s], 0), room)
\* The window fits in that reservation beside the chunks held (the Unbacked
\* RED grants whatever was reserved).
FitsAt(s, u) == ~Backed \/ W <= GrantResAt(s, u) - u

\* A grant of session s holding u chunks: the window is granted and the slot
\* leaves the queue, or the grant is deferred. A deferred slot whose
\* reservation fell short of its want waits in the queue, keeping its place
\* if it already has one (Streams::grant, ChunkStore::wait); one whose
\* reservation covers its want waits only for chunks of its own to come back,
\* which its own ack or read retries, so it stays out of the queue (else the
\* store would hand it nothing, over and over).
TryGrant(s, u) ==
    /\ res' = [res EXCEPT ![s] = GrantResAt(s, u)]
    /\ IF FitsAt(s, u)
       THEN /\ owed' = [owed EXCEPT ![s] = W] /\ defer' = [defer EXCEPT ![s] = FALSE]
            /\ queue' = Drop(queue, s) /\ wantq' = wantq
       ELSE /\ owed' = owed /\ defer' = [defer EXCEPT ![s] = TRUE]
            /\ queue' = IF GrantResAt(s, u) >= QueueWantAt(s, u) THEN Drop(queue, s)
                        ELSE IF s \in InQueue THEN queue ELSE Append(queue, s)
            /\ wantq' = [wantq EXCEPT ![s] = QueueWantAt(s, u)]

\* A step of the session's own that leaves it holding u chunks settles its
\* streams, which tries a deferred grant again (Streams::settle, regrant).
RegrantAt(s, u) == IF defer[s] THEN TryGrant(s, u)
                   ELSE UNCHANGED <<res, owed, defer, queue, wantq>>

\* Every variable has the type it should.
TypeOK == /\ sent \in [Sessions -> 0..1]
          /\ \A s \in Sessions : sent[s] <= used[s]
          /\ want \in [Sessions -> BOOLEAN] /\ live \in [Sessions -> BOOLEAN]
          /\ res \in [Sessions -> 0..B] /\ used \in [Sessions -> 0..B]
          /\ owed \in [Sessions -> 0..W] /\ open \in [Sessions -> BOOLEAN]
          /\ owner \in [Chunks -> Sessions \cup {None}]
          /\ last \in [Chunks -> Sessions \cup {Fresh, Gone}]
          /\ leak \in BOOLEAN /\ grants \in 0..G /\ closes \in 0..Cl
          /\ defer \in [Sessions -> BOOLEAN] /\ poke \in [Sessions -> BOOLEAN]
          /\ wantq \in [Sessions -> 0..B] /\ refused \in 0..1
          /\ Len(queue) <= Cardinality(Sessions)

\* A new endpoint: no session, the whole store untouched, every floor set
\* aside (none with the FloorPool RED, which takes it at admission).
Init == /\ sent = [s \in Sessions |-> 0]
        /\ want = [s \in Sessions |-> FALSE] /\ live = [s \in Sessions |-> FALSE]
        /\ res = [s \in Sessions |-> Base] /\ used = [s \in Sessions |-> 0]
        /\ owed = [s \in Sessions |-> 0] /\ open = [s \in Sessions |-> FALSE]
        /\ owner = [c \in Chunks |-> None] /\ last = [c \in Chunks |-> Fresh]
        /\ leak = FALSE /\ grants = 0 /\ closes = 0
        /\ defer = [s \in Sessions |-> FALSE] /\ queue = <<>>
        /\ wantq = [s \in Sessions |-> 0] /\ poke = [s \in Sessions |-> FALSE]
        /\ refused = 0

\* A peer dials a session that is not live.
Dial(s) == /\ ~live[s] /\ ~want[s]
           /\ want' = [want EXCEPT ![s] = TRUE]
           /\ UNCHANGED <<sent, live, res, used, owed, open, owner, last, leak, grants, closes,
                          defer, queue, wantq, poke, refused>>

\* Admission (alloc_slot): the slot's floor is already set aside, so the
\* session is let in. With the FloorPool RED the floor is reserved now from
\* the burst room, which other sessions' bursts may have taken.
Admit(s) == /\ want[s] /\ ~live[s]
            /\ Unreserved >= F - res[s]
            /\ res' = [res EXCEPT ![s] = Max(res[s], F)]
            /\ live' = [live EXCEPT ![s] = TRUE] /\ want' = [want EXCEPT ![s] = FALSE]
            /\ UNCHANGED <<sent, used, owed, open, owner, last, leak, grants, closes,
                           defer, queue, wantq, poke, refused>>

\* The peer is refused: the store had no floor for it (store_refused). It
\* dials again.
Refuse(s) == /\ want[s] /\ ~live[s] /\ Unreserved < F - res[s]
             /\ refused' = 1
             /\ UNCHANGED <<sent, want, live, res, used, owed, open, owner, last, leak, grants,
                            closes, defer, queue, wantq, poke>>

\* A stream opens on a live session (no chunk is taken yet).
Open(s) == /\ live[s] /\ ~open[s]
           /\ open' = [open EXCEPT ![s] = TRUE]
           /\ UNCHANGED <<sent, want, live, res, used, owed, owner, last, leak, grants, closes,
                          defer, queue, wantq, poke, refused>>

\* A window grant (Streams::grant).
Grant(s) == /\ live[s] /\ open[s] /\ owed[s] = 0 /\ ~defer[s] /\ grants < G
            /\ TryGrant(s, used[s])
            /\ grants' = grants + 1
            /\ UNCHANGED <<sent, want, live, used, open, owner, last, leak, closes, poke, refused>>

\* Room given back covers the oldest waiter's want (ChunkStore::serve, run
\* inside the shrink or release that gave it back): it is reserved for the
\* waiter, which leaves the queue and is told to grant again (pop_ready).
\* Without the Wake guard nothing hands the room on.
Serve == /\ Wake /\ queue /= <<>>
         /\ LET h == Head(queue)
                need == Max(wantq[h] - res[h], 0)
            IN /\ need <= Unreserved
               /\ res' = [res EXCEPT ![h] = res[h] + need]
               /\ poke' = [poke EXCEPT ![h] = TRUE]
         /\ queue' = Tail(queue)
         /\ UNCHANGED <<sent, want, live, used, owed, open, owner, last, leak, grants, closes,
                        defer, wantq, refused>>

\* The told session grants again (Endpoint::wake_store drains pop_ready and
\* has the session regrant within the same call).
Retry(s) == /\ poke[s]
            /\ poke' = [poke EXCEPT ![s] = FALSE]
            /\ IF live[s] /\ defer[s] THEN TryGrant(s, used[s])
               ELSE UNCHANGED <<res, owed, defer, queue, wantq>>
            /\ UNCHANGED <<sent, want, live, used, open, owner, last, leak, grants, closes, refused>>

\* One chunk is taken for session s (Arrive and Write): make_room may add
\* one chunk to the reservation when the slot may grow and the burst room
\* has one; the chunk is taken only inside the reservation (the ResCheck RED
\* takes any free one). A chunk another session held is zeroed first
\* (ChunkStore::take).
TakeChunk(s) ==
    LET grow == used[s] >= res[s] /\ res[s] < Cap /\ Unreserved > 0 /\ CanGrow(s)
        r == IF grow THEN res[s] + 1 ELSE res[s]
    IN /\ ResCheck => used[s] < r
       /\ \E c \in Chunks :
            /\ owner[c] = None
            /\ owner' = [owner EXCEPT ![c] = s]
            /\ leak' = (leak \/ (~Clear /\ last[c] \notin {s, Fresh}))
            /\ last' = [last EXCEPT ![c] = s]
       /\ res' = [res EXCEPT ![s] = r]
       /\ used' = [used EXCEPT ![s] = used[s] + 1]

\* One chunk of a granted window arrives (recv.rs's missing-chunks check).
Arrive(s) == /\ live[s] /\ owed[s] > 0
             /\ TakeChunk(s)
             /\ owed' = [owed EXCEPT ![s] = owed[s] - 1]
             /\ UNCHANGED <<sent, want, live, open, grants, closes, defer, queue, wantq, poke, refused>>

\* The session writes a chunk of its own (send.rs); a write may use room a
\* window reserved, never another session's.
Write(s) == /\ live[s] /\ open[s] /\ sent[s] = 0
            /\ TakeChunk(s)
            /\ sent' = [sent EXCEPT ![s] = 1]
            /\ UNCHANGED <<want, live, owed, open, grants, closes, defer, queue, wantq, poke, refused>>

\* The peer acknowledges the written chunk, which goes back to the store;
\* the ack is a packet of the session's own, so it tries a deferred grant.
Ack(s) == /\ live[s] /\ sent[s] = 1
          /\ \E c \in Chunks :
               /\ owner[c] = s
               /\ owner' = [owner EXCEPT ![c] = None]
          /\ used' = [used EXCEPT ![s] = used[s] - 1]
          /\ sent' = [sent EXCEPT ![s] = 0]
          /\ RegrantAt(s, used[s] - 1)
          /\ UNCHANGED <<want, live, open, last, leak, grants, closes, poke, refused>>

\* The application reads and consumes a received chunk, which goes back to
\* the store; the read settles the stream, which tries a deferred grant.
\* Worst case: nothing of a window is read before all of it arrived.
Read(s) == /\ live[s] /\ used[s] - sent[s] > 0 /\ owed[s] = 0
           /\ \E c \in Chunks :
                /\ owner[c] = s
                /\ owner' = [owner EXCEPT ![c] = None]
           /\ used' = [used EXCEPT ![s] = used[s] - 1]
           /\ RegrantAt(s, used[s] - 1)
           /\ UNCHANGED <<sent, want, live, open, last, leak, grants, closes, poke, refused>>

\* The stream ends once all is read and no grant waits (Streams::settle):
\* the reservation is trimmed to the floor, or to what is still held when
\* that is more (ChunkStore::shrink). The Hoard RED keeps all.
End(s) == /\ live[s] /\ open[s] /\ owed[s] = 0 /\ used[s] = 0 /\ ~defer[s]
          /\ open' = [open EXCEPT ![s] = FALSE]
          /\ res' = [res EXCEPT ![s] = IF Hoard THEN res[s] ELSE Max(F, used[s])]
          /\ UNCHANGED <<sent, want, live, used, owed, owner, last, leak, grants, closes,
                         defer, queue, wantq, poke, refused>>

\* A session closes (free_slot, ChunkStore::release): its chunks go back,
\* every chunk it held last is foreign now, it leaves the queue, and its
\* slot keeps only its floor (the NoRelease RED keeps the reservation).
Close(s) == /\ live[s] /\ closes < Cl
            /\ owner' = [c \in Chunks |-> IF owner[c] = s THEN None ELSE owner[c]]
            /\ last' = [c \in Chunks |-> IF last[c] = s THEN Gone ELSE last[c]]
            /\ res' = [res EXCEPT ![s] = IF Release THEN Base ELSE res[s]]
            /\ live' = [live EXCEPT ![s] = FALSE]
            /\ used' = [used EXCEPT ![s] = 0] /\ owed' = [owed EXCEPT ![s] = 0]
            /\ open' = [open EXCEPT ![s] = FALSE]
            /\ closes' = closes + 1
            /\ sent' = [sent EXCEPT ![s] = 0]
            /\ defer' = [defer EXCEPT ![s] = FALSE]
            /\ queue' = Drop(queue, s)
            /\ poke' = [poke EXCEPT ![s] = FALSE]
            /\ UNCHANGED <<want, leak, grants, wantq, refused>>

\* The endpoint is between inputs: no room is waiting to be handed on, and
\* no told session is waiting to grant. The store serves inside the call
\* that gave the room back, and the endpoint has the told sessions grant
\* before the call returns, so nothing else happens in between.
Settled == /\ \A t \in Sessions : ~poke[t]
           /\ ~ENABLED Serve

\* A step of a session other than the store's own work.
Other(s) == Settled /\ (Dial(s) \/ Admit(s) \/ Refuse(s) \/ Open(s) \/ Grant(s) \/ Arrive(s)
                        \/ Write(s) \/ Ack(s) \/ Read(s) \/ End(s) \/ Close(s))

\* Any step.
Next == Serve \/ \E s \in Sessions : Retry(s) \/ Other(s)

\* Data is read and writes are acknowledged. Data that finds no chunk is sent
\* again, so it gets in when a chunk is free infinitely often (strong
\* fairness: a write may take the free chunk first each time). Streams end
\* when they could infinitely often: the others go quiet in the end, which is
\* what "once chunks come back" means. A peer that keeps dialling is let in
\* when it could be infinitely often. The store serves and told sessions
\* grant whenever they can.
Fair == /\ WF_vars(Serve)
        /\ \A s \in Sessions : /\ SF_vars(Settled /\ Arrive(s)) /\ WF_vars(Settled /\ Read(s))
                               /\ WF_vars(Settled /\ Ack(s)) /\ SF_vars(Settled /\ End(s))
                               /\ SF_vars(Settled /\ Admit(s)) /\ WF_vars(Retry(s))

\* The behaviours: from a new endpoint, any steps, fairly.
Spec == Init /\ [][Next]_vars /\ Fair

\* The reservations never pass the store.
Conservation == Reserved <= B
\* No session holds a chunk its reservation does not cover.
UsedWithinRes == \A s \in Sessions : used[s] <= res[s]
\* Each chunk has one holder, and a session's count is the chunks it holds.
OneOwner == \A s \in Sessions : Cardinality({c \in Chunks : owner[c] = s}) = used[s]
\* Every granted window is covered by the reservation, beside the chunks
\* received (a write may borrow the room for a moment: its ack gives it back).
Backing == \A s \in Sessions : owed[s] <= res[s] - (used[s] - sent[s])
\* A live session keeps at least its floor.
FloorHeld == \A s \in Sessions : live[s] => res[s] >= F
\* No session ever saw another session's bytes.
NoForeignBytes == ~leak
\* No peer was ever refused for want of a floor.
NoneRefused == refused = 0
\* A deferred grant short of room is in the queue, or its room was reserved
\* and its session told; one in the queue is deferred and short of room
\* (so the store never serves it nothing); a slot is in the queue at most once.
QueueIsDeferred == /\ \A s \in Sessions : (defer[s] /\ res[s] < wantq[s]) => (s \in InQueue \/ poke[s] \/ ~Wake)
                   /\ \A s \in InQueue : defer[s] /\ res[s] < wantq[s]
                   /\ Cardinality(InQueue) = Len(queue)

\* A granted window always fills.
WindowsDrain == \A s \in Sessions : (owed[s] > 0) ~> (owed[s] = 0)
\* A peer that dials gets in.
NewcomerIn == \A s \in Sessions : want[s] ~> live[s]
\* A deferred grant is made in the end, or its session ends.
DeferEnds == \A s \in Sessions : defer[s] ~> ~defer[s]
=============================================================================
