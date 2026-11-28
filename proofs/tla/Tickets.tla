------------------------------- MODULE Tickets -------------------------------
(***************************************************************************)
(* The ticket stores of pinc-security/src/tickets.rs: ServerTickets and    *)
(* ClientTickets.                                                          *)
(*                                                                         *)
(* A store is a sequence of N slots (a ticket with its stamp, or "none")   *)
(* and a clock that stamps every insertion. Victim is the slot an inserted *)
(* ticket goes to: the first empty slot, else the first expired one, else  *)
(* the one with the lowest stamp (the tickets are stored in the order of   *)
(* the stamps, which are distinct).                                        *)
(*                                                                         *)
(* ServerTickets: issue_batch draws ticket ids with fresh_id, at most      *)
(* Attempts draws (8 in the code), each of which must differ from every    *)
(* stored id, else the call fails with the ticket-id failure. The random   *)
(* generator is the environment: the draws are an arbitrary sequence,      *)
(* including ids that are already stored. So the stored ids are unique by  *)
(* the code, which the invariant UniqueIds checks over every reachable     *)
(* store. A failure keeps the tickets of the same call that were already   *)
(* placed (the code stores each ticket as it is drawn). A ticket of a      *)
(* batch never evicts another of the same batch: when the victim holds one *)
(* of them (the store is full of this batch) the batch ends there, so it   *)
(* holds min(count, MaxBatch, N) tickets and every one it returns is       *)
(* stored (BatchStored, BatchLen; Tickets_server1.cfg has a store smaller  *)
(* than a batch). The model before let a batch evict its own tickets and   *)
(* return them, and no invariant asked whether a returned ticket was still *)
(* stored, which is how the bug went through.                              *)
(*                                                                         *)
(* ClientTickets: one ticket per peer (the newest replaces the older), at  *)
(* most N peers; accept_batch inserts the tickets of a batch in order, so  *)
(* the last is the one kept; take drops the expired tickets and removes    *)
(* and returns the peer's ticket if the ALPN matches; export lists the     *)
(* newest at most max (and at most 255) unexpired tickets, oldest first    *)
(* (the stores of the configs hold fewer than 255); restore checks the     *)
(* whole input before it stores anything and then inserts every entry that *)
(* has not expired. The byte format is in the Lean model (TicketsWire); a  *)
(* blob here is its logical content: the version, the entries (a ticket or *)
(* "bad" for an entry the reader rejects) and whether bytes trail.         *)
(*                                                                         *)
(* Times are integers; a lifetime of L seconds is L * Unit nanoseconds     *)
(* (Unit = 10^9 in the code; the u64 saturation of the sum is not modelled *)
(* and is proved in Lean, Tickets.expiryOf).                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Unit, Attempts, MaxBatch,
          Peers, Alpns, Tids, Psks, AeadVals, CreditVals, ExpVals, Nows, Ids,
          NC, NS, MaxClock, Mode,
          TicketSet, Batches, Streams  \* the cfg replaces them with TicketSetDef, BatchesDef, StreamsDef (evaluated once)

None == [full |-> FALSE]
Bad == [full |-> FALSE, bad |-> TRUE]

Min(a, b) == IF a < b THEN a ELSE b
MinOf(S) == CHOOSE i \in S : \A j \in S : i <= j

Exp(now, life) == now + life * Unit

(* ---- slots and the victim ---- *)

EmptyStore(n) == [slots |-> [i \in 1..n |-> None], clock |-> 0]

Occ(slots) == {i \in 1..Len(slots) : slots[i].full}
Expired(slots, now) == {i \in Occ(slots) : slots[i].exp < now}
Empties(slots) == {i \in 1..Len(slots) : ~slots[i].full}

Victim(slots, now) ==
    IF Empties(slots) /= {} THEN MinOf(Empties(slots))
    ELSE IF Expired(slots, now) /= {} THEN MinOf(Expired(slots, now))
    ELSE IF slots = <<>> THEN 0
    ELSE CHOOSE i \in Occ(slots) : \A j \in Occ(slots) \ {i} : slots[i].stamp < slots[j].stamp

(* ---- the server store ---- *)

SSlot(tid, exp, c) == [full |-> TRUE, tid |-> tid, exp |-> exp, stamp |-> c]

Fresh(slots, tid) == \A i \in Occ(slots) : slots[i].tid /= tid

\* fresh_id: at most k draws from position p of the generator output ds; running out of draws is the generator
\* refusing
RECURSIVE FreshId(_, _, _, _)
FreshId(slots, ds, k, p) ==
    IF k = 0 THEN [res |-> "ticketId", p |-> p]
    ELSE IF p > Len(ds) THEN [res |-> "rand", p |-> p]
    ELSE IF Fresh(slots, ds[p]) THEN [res |-> "ok", tid |-> ds[p], p |-> p + 1]
    ELSE FreshId(slots, ds, k - 1, p + 1)

Put(slots, at, slot) == IF at = 0 THEN slots ELSE [slots EXCEPT ![at] = slot]

\* issue_batch: the ticket drawn for each of k tickets goes to the victim slot; mine holds the slots of this batch's
\* tickets. They are the newest and never expired, so the victim is one of them only when every slot is (or there is
\* no slot, 0): the batch ends there, after the draw and the clock step, as in the code. Operators take their pieces as
\* arguments because TLC re-evaluates LET definitions.
RECURSIVE IssueLoop(_, _, _, _, _, _, _), IssueStep(_, _, _, _, _, _, _), IssueFin(_, _, _, _, _, _, _, _)
IssueJoin(f, rest) ==
    [sv |-> rest.sv, res |-> rest.res, batch |-> IF rest.res /= "ok" THEN <<>> ELSE <<f.tid>> \o rest.batch]

IssueLoop(sv, ds, now, life, k, p, mine) ==
    IF k = 0 THEN [sv |-> sv, res |-> "ok", batch |-> <<>>]
    ELSE IssueStep(sv, ds, now, life, k, FreshId(sv.slots, ds, Attempts, p), mine)

IssueStep(sv, ds, now, life, k, f, mine) ==
    IF f.res /= "ok" THEN [sv |-> sv, res |-> f.res, batch |-> <<>>]
    ELSE IssueFin(Victim(sv.slots, now), sv, ds, now, life, k, f, mine)

IssueFin(v, sv, ds, now, life, k, f, mine) ==
    IF v = 0 \/ v \in mine THEN [sv |-> [sv EXCEPT !.clock = @ + 1], res |-> "ok", batch |-> <<>>]
    ELSE IssueJoin(f, IssueLoop([slots |-> Put(sv.slots, v, SSlot(f.tid, Exp(now, life), sv.clock + 1)),
                                 clock |-> sv.clock + 1], ds, now, life, k - 1, f.p, mine \cup {v}))

IssueBatch(sv, ds, now, life, count) == IssueLoop(sv, ds, now, life, Min(count, MaxBatch), 1, {})

SRemove(sv, i) == [sv EXCEPT !.slots[i] = None]

(* ---- the client store ---- *)

CSlot(tk, c) == [full |-> TRUE, peer |-> tk.peer, alpn |-> tk.alpn, tid |-> tk.tid, psk |-> tk.psk, aead |-> tk.aead,
                 exp |-> tk.exp, credit |-> tk.credit, stamp |-> c]
Strip(s) == [full |-> TRUE, peer |-> s.peer, alpn |-> s.alpn, tid |-> s.tid, psk |-> s.psk, aead |-> s.aead,
             exp |-> s.exp, credit |-> s.credit]

SameIdx(slots, peer) == {i \in Occ(slots) : slots[i].peer = peer}

\* the slot an inserted ticket goes to: the peer's own, else the victim
InsertAt(slots, peer, now) ==
    IF SameIdx(slots, peer) /= {} THEN MinOf(SameIdx(slots, peer)) ELSE Victim(slots, now)

Insert(c, tk, now) ==
    [slots |-> Put(c.slots, InsertAt(c.slots, tk.peer, now), CSlot(tk, c.clock + 1)), clock |-> c.clock + 1]

RECURSIVE AcceptSeq(_, _, _)
AcceptSeq(c, tks, now) ==
    IF tks = <<>> THEN c ELSE AcceptSeq(Insert(c, Head(tks), now), Tail(tks), now)

DropExpired(slots, now) ==
    [i \in 1..Len(slots) |-> IF slots[i].full /\ slots[i].exp < now THEN None ELSE slots[i]]

TakeSet(d, peer, alpn) == {i \in Occ(d) : d[i].peer = peer /\ d[i].alpn = alpn}

TakeAt(d, clock, i) == [cl |-> [slots |-> [d EXCEPT ![i] = None], clock |-> clock], got |-> Strip(d[i])]

TakeIn(d, clock, peer, alpn) ==
    IF TakeSet(d, peer, alpn) = {} THEN [cl |-> [slots |-> d, clock |-> clock], got |-> None]
    ELSE TakeAt(d, clock, MinOf(TakeSet(d, peer, alpn)))


Take(c, peer, alpn, now) == TakeIn(DropExpired(c.slots, now), c.clock, peer, alpn)

Live(slots, now) == {i \in Occ(slots) : slots[i].exp >= now}

Before(slots, i, j) == slots[i].stamp < slots[j].stamp \/ (slots[i].stamp = slots[j].stamp /\ i < j)

MinBy(slots, S) == CHOOSE i \in S : \A j \in S \ {i} : Before(slots, i, j)

RECURSIVE SortedIdx(_, _)
SortedIdx(slots, S) ==
    IF S = {} THEN <<>> ELSE <<MinBy(slots, S)>> \o SortedIdx(slots, S \ {MinBy(slots, S)})

\* export: the newest at most max live tickets, oldest first
ExportTail(s, max) == SubSeq(s, Len(s) - Min(Len(s), max) + 1, Len(s))
ExportIdx(slots, now, max) == ExportTail(SortedIdx(slots, Live(slots, now)), max)
StripAt(slots, ix) == [k \in 1..Len(ix) |-> Strip(slots[ix[k]])]
Export(slots, now, max) == StripAt(slots, ExportIdx(slots, now, max))

\* a blob: the version, the entries (a ticket, or Bad for an entry the reader rejects), whether bytes trail
Wellformed(b) == b.ver = 1 /\ ~b.trailing /\ \A k \in 1..Len(b.ents) : b.ents[k].full

BlobOf(tks) == [ver |-> 1, ents |-> tks, trailing |-> FALSE]

RestoreIn(c, live, now) == [cl |-> AcceptSeq(c, live, now), n |-> Len(live)]

\* restore: nothing is stored unless the whole input is well formed; then the live entries are inserted
Restore(c, b, now) ==
    IF ~Wellformed(b) THEN [cl |-> c, n |-> -1]
    ELSE RestoreIn(c, SelectSeq(b.ents, LAMBDA t : t.exp >= now), now)

(* ---- the model ---- *)

VARIABLES cl, sv
vars == <<cl, sv>>

TicketSetDef == {t \in [full : {TRUE}, peer : Peers, alpn : Alpns, tid : Tids, psk : Psks, aead : AeadVals, exp : ExpVals, credit : CreditVals] : TRUE}

\* batches: tickets of one peer and ALPN, as the tickets of one session
BatchesDef == UNION {{<<>>} \cup {<<a>> : a \in {t \in TicketSetDef : t.peer = p /\ t.alpn = l}}
                      \cup {<<a, b>> : a, b \in {t \in TicketSetDef : t.peer = p /\ t.alpn = l}} : p \in Peers, l \in Alpns}

StreamsDef == {s \in UNION {[1..n -> Ids] : n \in 0..(MaxBatch * Attempts)} : TRUE}
\* the quick profile (quick/Tickets_server.cfg substitutes it for Streams): one draw fewer than a full batch with every
\* retry, enough for a batch whose second ticket fails after a retry
StreamsDefQuick == {s \in UNION {[1..n -> Ids] : n \in 0..(MaxBatch * Attempts - 1)} : TRUE}

Init == cl = EmptyStore(NC) /\ sv = EmptyStore(NS)

CAccept == \E b \in Batches, now \in Nows : cl' = AcceptSeq(cl, b, now) /\ sv' = sv

CTake == \E p \in Peers, l \in Alpns, now \in Nows : cl' = Take(cl, p, l, now).cl /\ sv' = sv

SIssue == \E ds \in Streams, now \in Nows, life \in 0..1, count \in 0..MaxBatch :
              sv' = IssueBatch(sv, ds, now, life, count).sv /\ cl' = cl

SDrop == \E i \in 1..NS : sv' = SRemove(sv, i) /\ cl' = cl

\* Mode keeps the client and the server stores apart in the model check: the two are independent
Next == IF Mode = "client" THEN CAccept \/ CTake ELSE SIssue \/ SDrop

Spec == Init /\ [][Next]_vars

Bounded == cl.clock <= MaxClock /\ sv.clock <= MaxClock

(* ---- invariants ---- *)

TypeOK ==
    /\ Len(cl.slots) = NC /\ Len(sv.slots) = NS
    /\ cl.clock \in Nat /\ sv.clock \in Nat
    /\ \A i \in Occ(cl.slots) : cl.slots[i].peer \in Peers /\ cl.slots[i].exp \in Int /\ cl.slots[i].stamp \in 1..cl.clock
    /\ \A i \in Occ(sv.slots) : sv.slots[i].tid \in Ids /\ sv.slots[i].stamp \in 1..sv.clock

\* the stores hold at most N tickets; N = 0 stores nothing
ServerBound == Cardinality(Occ(sv.slots)) <= NS
ClientBound == Cardinality(Occ(cl.slots)) <= NC
ZeroStoresNothing == (NC = 0 => Occ(cl.slots) = {}) /\ (NS = 0 => Occ(sv.slots) = {})

\* at most one ticket per peer
OnePerPeer == \A i, j \in Occ(cl.slots) : cl.slots[i].peer = cl.slots[j].peer => i = j

\* the stored ids are unique, whatever the generator returned
UniqueIds == \A i, j \in Occ(sv.slots) : sv.slots[i].tid = sv.slots[j].tid => i = j

StampsDistinct ==
    /\ \A i, j \in Occ(cl.slots) : cl.slots[i].stamp = cl.slots[j].stamp => i = j
    /\ \A i, j \in Occ(sv.slots) : sv.slots[i].stamp = sv.slots[j].stamp => i = j

InsertOK(c, tk, now, r) ==
    /\ r.clock = c.clock + 1
    /\ Len(c.slots) = 0 => r.slots = c.slots
    /\ Len(c.slots) > 0 =>
         \E at \in 1..Len(c.slots) :
             /\ {i \in 1..Len(c.slots) : r.slots[i] /= c.slots[i]} = {at}
             /\ r.slots[at] = CSlot(tk, r.clock)
             /\ IF SameIdx(c.slots, tk.peer) /= {} THEN at = MinOf(SameIdx(c.slots, tk.peer))
                ELSE IF Empties(c.slots) /= {} THEN at = MinOf(Empties(c.slots))
                ELSE IF Expired(c.slots, now) /= {} THEN at = MinOf(Expired(c.slots, now))
                ELSE \A j \in Occ(c.slots) \ {at} : c.slots[at].stamp < c.slots[j].stamp

IssueOK(s, d, now, life, r) ==
    IF ~Fresh(s.slots, d) \/ Len(s.slots) = 0
    THEN r.sv.slots = s.slots /\ r.batch = <<>>
    ELSE \E at \in 1..Len(s.slots) :
             /\ {i \in 1..Len(s.slots) : r.sv.slots[i] /= s.slots[i]} = {at}
             /\ r.batch = <<d>>
             /\ r.sv.slots[at] = SSlot(d, Exp(now, life), r.sv.clock)
             /\ IF Empties(s.slots) /= {} THEN at = MinOf(Empties(s.slots))
                ELSE IF Expired(s.slots, now) /= {} THEN at = MinOf(Expired(s.slots, now))
                ELSE \A j \in Occ(s.slots) \ {at} : s.slots[at].stamp < s.slots[j].stamp

LastKept(r, last) ==
    \E i \in Occ(r.slots) : Strip(r.slots[i]) = last /\ r.slots[i].stamp = r.clock
        /\ \A j \in Occ(r.slots) : r.slots[j].peer = last.peer => j = i

\* insert: a peer's ticket replaces its slot; else the first empty slot; else the first expired; else the oldest
InsertOrder ==
    \A tk \in TicketSet, now \in Nows : \A r \in {Insert(cl, tk, now)} :
        InsertOK(cl, tk, now, r)

\* issue: the same order for the server store, whatever id was drawn
IssueOrder ==
    \A d \in Ids, now \in Nows, life \in 0..1 : \A r \in {IssueBatch(sv, <<d>>, now, life, 1)} :
        IssueOK(sv, d, now, life, r)

\* all of the draws collide: the ticket-id failure, and nothing is stored by a one-ticket call
CollisionFails ==
    \A ds \in [1..Attempts -> Ids] :
        (\A k \in 1..Attempts : ~Fresh(sv.slots, ds[k]))
            => \A r \in {IssueBatch(sv, ds, 0, 0, 1)} : r.res = "ticketId" /\ r.sv = sv

\* issue_batch never evicts its own tickets: every ticket of a batch it returns is stored, and the batch holds as many
\* as asked up to MaxBatch and the store's size
BatchStored ==
    \A ds \in Streams, now \in Nows, life \in 0..1, count \in 0..MaxBatch : \A r \in {IssueBatch(sv, ds, now, life, count)} :
        r.res = "ok" => \A k \in 1..Len(r.batch) : \E i \in Occ(r.sv.slots) : r.sv.slots[i].tid = r.batch[k]
BatchLen ==
    \A ds \in Streams, now \in Nows, life \in 0..1, count \in 0..MaxBatch : \A r \in {IssueBatch(sv, ds, now, life, count)} :
        r.res = "ok" => Len(r.batch) = Min(Min(count, MaxBatch), NS)

\* take: a ticket taken is for the peer and ALPN, was not expired, and is not taken again
TakeOnce ==
    \A p \in Peers, l \in Alpns, now \in Nows : \A r \in {Take(cl, p, l, now)} :
        /\ r.got.full => /\ r.got.peer = p /\ r.got.alpn = l /\ r.got.exp >= now
                          /\ \A now2 \in Nows : ~Take(r.cl, p, l, now2).got.full
        /\ \A i \in Occ(r.cl.slots) : r.cl.slots[i].exp >= now
        /\ r.cl.clock = cl.clock

\* a ticket for another ALPN is not returned and stays
TakeAlpn ==
    \A p \in Peers, l \in Alpns, now \in Nows : \A r \in {Take(cl, p, l, now)} :
        ~r.got.full =>
            \A i \in Occ(cl.slots) : (cl.slots[i].peer = p /\ cl.slots[i].exp >= now)
                => (cl.slots[i].alpn /= l /\ \E j \in Occ(r.cl.slots) : r.cl.slots[j] = cl.slots[i])

\* accept_batch: the last ticket of a batch is the one kept
BatchLastKept ==
    \A b \in Batches, now \in Nows :
        (Len(b) > 0 /\ NC > 0) => \A r \in {AcceptSeq(cl, b, now)} : LastKept(r, b[Len(b)])

\* export: at most max live tickets, newest, oldest first, none expired
ExportOK ==
    \A now \in Nows, max \in 0..NC : \A ix \in {ExportIdx(cl.slots, now, max)} :
        /\ Len(ix) = Min(Cardinality(Live(cl.slots, now)), max)
        /\ \A k \in 1..Len(ix) : ix[k] \in Live(cl.slots, now)
        /\ \A k \in 1..(Len(ix) - 1) : cl.slots[ix[k]].stamp < cl.slots[ix[k + 1]].stamp
        /\ \A j \in Live(cl.slots, now) \ {ix[k] : k \in 1..Len(ix)} :
              \A k \in 1..Len(ix) : cl.slots[j].stamp < cl.slots[ix[k]].stamp

\* restoring an export into an empty store with room for it yields the same tickets, oldest first
RoundTrip ==
    \A now \in Nows, max \in 0..NC : \A e \in {Export(cl.slots, now, max)} :
        \A r \in {Restore(EmptyStore(NC), BlobOf(e), now)} :
            /\ r.n = Len(e)
            /\ \A k \in 1..Len(e) : Strip(r.cl.slots[k]) = e[k]
            /\ \A k \in (Len(e) + 1)..NC : ~r.cl.slots[k].full

\* an input the reader rejects stores nothing
MalformedStoresNothing ==
    \A tk \in TicketSet, now \in Nows :
        /\ Restore(cl, [ver |-> 1, ents |-> <<tk, Bad>>, trailing |-> FALSE], now) = [cl |-> cl, n |-> -1]
        /\ Restore(cl, [ver |-> 1, ents |-> <<Bad>>, trailing |-> FALSE], now) = [cl |-> cl, n |-> -1]
        /\ Restore(cl, [ver |-> 1, ents |-> <<tk>>, trailing |-> TRUE], now) = [cl |-> cl, n |-> -1]
        /\ Restore(cl, [ver |-> 2, ents |-> <<tk>>, trailing |-> FALSE], now) = [cl |-> cl, n |-> -1]

\* restore inserts only entries that have not expired, as accept_batch does
RestoreFilters ==
    \A tk \in TicketSet, now \in Nows :
        IF tk.exp >= now THEN Restore(cl, BlobOf(<<tk>>), now) = [cl |-> Insert(cl, tk, now), n |-> 1]
                         ELSE Restore(cl, BlobOf(<<tk>>), now) = [cl |-> cl, n |-> 0]

=============================================================================
