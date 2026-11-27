------------------------------ MODULE CoreState ------------------------------
(***************************************************************************)
(* The saved state of the endpoint (pinc-core state.rs): the tickets, the  *)
(* round trip of each peer and the peers that cache this node's prekey,    *)
(* written by `export_state` and loaded by `restore_state`. The operators  *)
(* are CoreStateOps.tla, which follow the code field by field and stage by *)
(* stage.                                                                  *)
(*                                                                         *)
(* What the code promises, and what TLC checks of it for a set of states   *)
(* (empty, one entry of each kind, tables exactly at their bounds and past  *)
(* them, a peer repeated, a round trip of 0, tickets expired before, at    *)
(* and after the time of the restore), every cut, appended bytes, wrong     *)
(* tags and claims, and every byte of every state changed to three other    *)
(* values:                                                                  *)
(*   RT       the bytes of a state read back as that state                  *)
(*   Fresh    restoring into an empty endpoint what was written gives      *)
(*            exactly the tables written (a canonical state: one entry per *)
(*            peer, within the bounds, round trips above 0, tickets not     *)
(*            expired), and restoring it again changes nothing; for any    *)
(*            state the tables hold the entries of the state that fit, no  *)
(*            expired ticket, one entry per peer, never more than their    *)
(*            bounds, and the counts reported are the ones stored (the     *)
(*            ticket count: the state's tickets still in the store once    *)
(*            the whole state was applied)                                 *)
(*   Canon    a byte string that is accepted is the encoding of the state  *)
(*            it reads: one reading, no leniency                           *)
(*   Atomic   restore accepts exactly what the parse reads, and a refused  *)
(*            input leaves a live endpoint's three tables as they were     *)
(*            (the writes of the stages that cannot fail come after every  *)
(*            check that can)                                              *)
(*   Strict   a wrong version, a cut, appended bytes, a length or count    *)
(*            that claims more than the input holds, an unknown tag or a   *)
(*            bad ALPN length is refused, and refused without effect       *)
(*                                                                         *)
(* Witnesses: CoreState_lazy.cfg (the check of the round trips and prekey  *)
(* peers deferred to the stage that stores them: `Atomic` fails, the       *)
(* tickets are already stored) and CoreState_tail.cfg (bytes after the     *)
(* state accepted: `Canon` and `Strict` fail).                             *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/CoreState.lean, CoreStateThm.lean.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS CT, KR, EK, LAZY, LAXTAIL

O == INSTANCE CoreStateOps

Fill(n, s) == [j \in 1..n |-> (j * 7 + s) % 256]

Tk(k, alg, al, ex) == [alg |-> alg, node |-> Fill(32, k), alpn |-> Fill(al, 50 + k), tid |-> Fill(16, k + 1),
                       psk |-> Fill(32, k + 2), aead |-> 1 + (k % 2), expiry |-> O!BEr(ex, 8), credit |-> Fill(6, k)]
Kr(k, alg, r) == [alg |-> alg, node |-> Fill(32, k), rtt |-> O!BEr(r, 8)]
Ek(k, alg, h) == [alg |-> alg, node |-> Fill(32, k), hash |-> Fill(32, h)]

NOW == 100

Cases ==
    {[tk |-> <<>>, kr |-> <<>>, ek |-> <<>>],
     [tk |-> <<Tk(1, 1, 1, 200)>>, kr |-> <<Kr(1, 1, 5)>>, ek |-> <<Ek(1, 1, 3)>>],
     [tk |-> <<Tk(1, 1, 32, 200), Tk(2, 2, 3, 300)>>, kr |-> <<Kr(1, 1, 5), Kr(2, 2, 7)>>, ek |-> <<Ek(1, 1, 3), Ek(2, 2, 4)>>],
     [tk |-> <<Tk(1, 3, 2, 200), Tk(2, 4, 2, 300), Tk(3, 1, 2, 400)>>,
      kr |-> <<Kr(1, 1, 5), Kr(2, 2, 7), Kr(3, 3, 9)>>, ek |-> <<Ek(1, 1, 3), Ek(2, 2, 4), Ek(3, 3, 5)>>],
     [tk |-> <<Tk(1, 1, 1, 200), Tk(2, 2, 2, 300), Tk(1, 1, 3, 250)>>,
      kr |-> <<Kr(1, 1, 5), Kr(1, 1, 9), Kr(3, 3, 0)>>, ek |-> <<Ek(1, 1, 3), Ek(1, 1, 4)>>],
     [tk |-> <<Tk(1, 1, 1, 99), Tk(2, 2, 1, 100), Tk(3, 3, 1, 101)>>, kr |-> <<>>, ek |-> <<>>],
     [tk |-> <<>>, kr |-> <<Kr(1, 1, 0), Kr(2, 2, 0)>>, ek |-> <<>>]}

Empty == [tk |-> <<>>, kr |-> <<>>, ek |-> <<>>]
Lives == {Empty,
          [tk |-> <<Tk(7, 1, 1, 500)>>, kr |-> <<Kr(7, 1, 3)>>, ek |-> <<Ek(7, 1, 6)>>],
          [tk |-> <<Tk(7, 1, 1, 500), Tk(8, 2, 4, 600)>>, kr |-> <<Kr(7, 1, 3), Kr(8, 2, 4)>>, ek |-> <<Ek(7, 1, 6), Ek(8, 2, 6)>>]}
\* the quick profile (proofs/tla/quick): the empty endpoint and the one with one entry per table, not the full one (a
\* restore of a case of 2 or 3 entries over it still passes the bounds)
LivesQuick == {Empty, [tk |-> <<Tk(7, 1, 1, 500)>>, kr |-> <<Kr(7, 1, 3)>>, ek |-> <<Ek(7, 1, 6)>>]}

Take(bs, k) == SubSeq(bs, 1, k)
Mutate(bs, i, d) == [bs EXCEPT ![i] = IF d = 0 THEN 0 ELSE IF d = 1 THEN 255 ELSE (bs[i] + 1) % 256]

\* the offsets (1-based) of the identity tags, the AEAD tags and the ALPN lengths of an encoding; the tickets start at 8
RECURSIVE TkAlg(_, _)
TkAlg(tk, at) == IF tk = <<>> THEN {} ELSE {at} \cup TkAlg(Tail(tk), at + 97 + Len(tk[1].alpn))
RECURSIVE TkLen(_, _)
TkLen(tk, at) == IF tk = <<>> THEN {} ELSE {at + 33} \cup TkLen(Tail(tk), at + 97 + Len(tk[1].alpn))
RECURSIVE TkAead(_, _)
TkAead(tk, at) == IF tk = <<>> THEN {} ELSE {at + 82 + Len(tk[1].alpn)} \cup TkAead(Tail(tk), at + 97 + Len(tk[1].alpn))
K0(s) == 5 + Len(O!EncTkSec(s.tk)) + 3
E0(s) == K0(s) + 41 * Len(s.kr) + 2
AlgPos(s) == TkAlg(s.tk, 8) \cup {K0(s) + 41 * j : j \in 0..(Len(s.kr) - 1)} \cup {E0(s) + 65 * j : j \in 0..(Len(s.ek) - 1)}

Offs(s) == {1, 2, 3, 4, 5, 6, 7, K0(s) - 2, K0(s) - 1, E0(s) - 2, E0(s) - 1}
           \cup AlgPos(s) \cup TkLen(s.tk, 8) \cup TkAead(s.tk, 8)

Positions(s, n) == ((1..24) \cup ((n - 9)..n) \cup Offs(s) \cup {p \in 25..n : p % 7 = 0}) \cap (1..n)
\* the quick profile: every 21st byte past the first 24, not every 7th (21 is prime to 8, so each of the 16 mutation
\* checks still gets middle bytes); the head, the tail and every tag, length and count offset kept
PositionsQuick(s, n) == ((1..24) \cup ((n - 9)..n) \cup Offs(s) \cup {p \in 25..n : p % 21 = 0}) \cap (1..n)

\* canonical: one entry per peer, within the bounds, round trips above 0, tickets not expired
Distinct(l) == \A i, j \in 1..Len(l) : i # j => O!Peer(l[i]) # O!Peer(l[j])
Canonical(s) ==
    /\ Distinct(s.tk) /\ Len(s.tk) <= CT /\ \A i \in 1..Len(s.tk) : O!Ge(s.tk[i].expiry, O!BEr(NOW, 8))
    /\ Distinct(s.kr) /\ Len(s.kr) <= KR /\ \A i \in 1..Len(s.kr) : O!NonZero(s.kr[i].rtt)
    /\ Distinct(s.ek) /\ Len(s.ek) <= EK

Within(live) == Len(live.tk) <= CT /\ Len(live.kr) <= KR /\ Len(live.ek) <= EK
Members(l, s) == \A i \in 1..Len(l) : \E j \in 1..Len(s) : l[i] = s[j]

Canon(bs) == LET r == O!Parse(bs) IN r.ok => O!Enc(r.v) = bs
Same(l, live) == l = live
\* refused: nothing changed; accepted exactly when the parse reads a state
Atomic(live, bs) ==
    LET r == O!Restore(live, bs, NOW)
    IN /\ r.ok = O!Parse(bs).ok
       /\ ~r.ok => r.live = live
Refused(live, bs) == ~O!Parse(bs).ok /\ O!Restore(live, bs, NOW) = [ok |-> FALSE, live |-> live]

VARIABLE s
Checks == {"rt", "fresh", "trunc", "trail", "tcanon", "tags", "claims", "version"} \cup {"m0", "m1", "m2", "m3", "m4", "m5", "m6", "m7", "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"}
Init == s = [t |-> "root"]
Next == \/ s.t = "root" /\ \E c \in Cases, k \in Checks : s' = [t |-> "case", c |-> c, chk |-> k]
Spec == Init /\ [][Next]_s

Body(c, chk) ==
    LET bs == O!Enc(c)
        n == Len(bs)
        tl == Len(O!EncTkSec(c.tk))
        r == O!Restore(Empty, bs, NOW)
        expired == {i \in 1..Len(c.tk) : ~O!Ge(c.tk[i].expiry, O!BEr(NOW, 8))}
    IN CASE chk = "rt" ->
              /\ O!Parse(bs) = [ok |-> TRUE, v |-> c]
              /\ n = 9 + tl + 41 * Len(c.kr) + 65 * Len(c.ek)
       [] chk = "fresh" ->
              /\ r.ok /\ Within(r.live)
              /\ Distinct(r.live.tk) /\ Distinct(r.live.kr) /\ Distinct(r.live.ek)
              /\ Members(r.live.tk, c.tk) /\ Members(r.live.kr, c.kr) /\ Members(r.live.ek, c.ek)
              /\ \A i \in 1..Len(r.live.tk) : O!Ge(r.live.tk[i].expiry, O!BEr(NOW, 8))
              /\ \A i \in 1..Len(r.live.kr) : O!NonZero(r.live.kr[i].rtt)
              \* into an empty endpoint every ticket stored is one of the state, so the count is the store's length
              /\ r.res[1] = Len(r.live.tk) /\ r.res[1] <= Len(c.tk) - Cardinality(expired) /\ r.res[3] = Len(c.ek)
              /\ r.res[2] <= Len(c.kr)
              /\ (Canonical(c) => /\ r.live = c /\ r.res = <<Len(c.tk), Len(c.kr), Len(c.ek)>>
                                  /\ O!Restore(r.live, bs, NOW) = r)
              \* a second restore of any state keeps the bounds, whatever the tables held
              /\ \A L \in Lives : LET q == O!Restore(L, bs, NOW) IN q.ok /\ Within(q.live) /\ Distinct(q.live.tk)
                                                                  /\ q.res[1] <= Len(q.live.tk)
       [] chk = "trunc" -> \A k \in 0..(n - 1) : \A L \in Lives : Refused(L, Take(bs, k))
       [] chk = "trail" -> \A x \in 1..5 : \A L \in Lives : Refused(L, bs \o Fill(x, 9))
       [] chk = "tcanon" -> \A x \in 1..5 : Canon(bs \o Fill(x, 9)) /\ Canon(Take(bs, n - x))
       [] chk = "version" -> \A v \in {0, 2, 255}, L \in Lives : Refused(L, [bs EXCEPT ![1] = v])
       [] chk = "tags" ->
              \* an identity tag outside 1..4, an AEAD tag outside 1..2, an ALPN length of 0 or past 32
              /\ \A p \in AlgPos(c), v \in {0, 5, 255}, L \in Lives : Refused(L, [bs EXCEPT ![p] = v])
              /\ \A p \in TkAead(c.tk, 8), v \in {0, 3, 255}, L \in Lives : Refused(L, [bs EXCEPT ![p] = v])
              /\ \A p \in TkLen(c.tk, 8), v \in {0, 33, 255}, L \in Lives : Refused(L, [bs EXCEPT ![p] = v])
       [] chk = "claims" ->
              \* a length or a count that claims more than the input holds
              /\ \A v \in {<<255, 255, 255, 255>>, <<128, 0, 0, 0>>, O!BEw(n, 4)}, L \in Lives :
                    Refused(L, <<bs[1]>> \o v \o SubSeq(bs, 6, n))
              /\ \A L \in Lives : Refused(L, Take(bs, 5 + tl) \o <<255, 255>> \o SubSeq(bs, 5 + tl + 3, n))
              /\ \A L \in Lives : Refused(L, Take(bs, 5 + tl + 2 + 41 * Len(c.kr)) \o <<255, 255>>
                                              \o SubSeq(bs, 5 + tl + 2 + 41 * Len(c.kr) + 3, n))
       [] OTHER -> \A p \in Positions(c, n), d \in 0..2 :
                  LET m == Mutate(bs, p, d) IN
                  /\ "m" \o ToString(p % 8) = chk => Canon(m)
                  /\ "a" \o ToString(p % 8) = chk => \A L \in Lives : Atomic(L, m)

IsM(k) == k \in {"m0", "m1", "m2", "m3", "m4", "m5", "m6", "m7"}
IsA(k) == k \in {"a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"}

\* the properties, each an invariant of its own so that a witness can name the one it breaks
RT == s.t = "root" \/ s.chk # "rt" \/ Body(s.c, "rt")
Fresh == s.t = "root" \/ s.chk # "fresh" \/ Body(s.c, "fresh")
Strict == s.t = "root" \/ s.chk \notin {"trunc", "trail", "version", "tags", "claims"} \/ Body(s.c, s.chk)
CanonInv == s.t = "root" \/ ~(IsM(s.chk) \/ s.chk = "tcanon") \/ Body(s.c, s.chk)
AtomicInv == s.t = "root" \/ ~IsA(s.chk) \/ Body(s.c, s.chk)
\* reachability witnesses (TLC must violate them): a changed byte that is still a state, and tables full at every bound
NoAcceptedMutant == s.t = "root" \/ ~IsM(s.chk) \/
    \A p \in Positions(s.c, Len(O!Enc(s.c))), d \in 0..2 : ~O!Parse(Mutate(O!Enc(s.c), p, d)).ok
NoFullTables == s.t = "root" \/ s.chk # "fresh" \/
    LET r == O!Restore(Empty, O!Enc(s.c), NOW) IN ~(Len(r.live.tk) = CT /\ Len(r.live.kr) = KR /\ Len(r.live.ek) = EK)
NoEviction == s.t = "root" \/ s.chk # "fresh" \/ ~(Len(s.c.tk) > CT /\ Len(s.c.kr) > KR /\ Len(s.c.ek) > EK)
TruncInv ==s.t = "root" \/ s.chk # "trunc" \/ Body(s.c, "trunc")
TrailInv == s.t = "root" \/ s.chk # "trail" \/ Body(s.c, "trail")
=============================================================================
