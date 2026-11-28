------------------------------ MODULE ReasmPair ------------------------------
(***************************************************************************)
(* The reassembly of a handshake message that only one session receives   *)
(* (a dialing side's Reply, a responder's Finish when it takes more than   *)
(* one datagram), pinc-transport conn/handshake_rx.rs add_pair and receive *)
(* over two candidates in the handshake's chunk (conn/reasm.rs, the        *)
(* agreement rule of ReasmOps.tla AddV), against a third party that sends  *)
(* forged fragments of the message (any offset, any length, the same or    *)
(* another message length) from the sender's address, before, between or  *)
(* after the genuine ones.                                                 *)
(*                                                                         *)
(* The message is MX = 3 bytes in two genuine datagrams (bytes 0 and 1,    *)
(* then byte 2), each sent once per flight; the third party sends at most  *)
(* F forged fragments per flight and FT in all, of the forged messages FV  *)
(* (2 is one message of the same length; {2, 3} adds one a byte shorter). *)
(* FK "copy": each is a damaged copy of a genuine datagram (its offset and *)
(* length); FK "any": any offset and length. A message that completes is   *)
(* authenticated by the machine: only the genuine one (every byte of       *)
(* version 1) is taken (done).                                             *)
(*                                                                         *)
(* RULE "pair", the code's rule: a fragment goes to every candidate that   *)
(* holds something and agrees with it; when none does, to an empty         *)
(* candidate, else it starts over the one written least recently. RULE     *)
(* "one": the agreement rule with one candidate. RULE "last": the rule     *)
(* before the handshake fix (one candidate, the last bytes win, a message  *)
(* that fails starts over).                                                *)
(*                                                                         *)
(* VERDICT, when the machine says whether a complete message               *)
(* authenticates. "sync": in the call that hands it over; a candidate      *)
(* whose message fails goes back to its runs before that fragment and the  *)
(* next candidate that completed gets its turn. The dialing side's Reply   *)
(* is never decided so: the machine asks the host to decapsulate (a key    *)
(* request, Pending::Decap) and the verdict comes in a later call          *)
(* (on_key_response), with fragments arriving meanwhile; the machine       *)
(* refuses another Reply until then. "code": what the transport does with  *)
(* that today: the first candidate that completed (rx, then alt) is handed *)
(* over, every candidate that completed is emptied (Reassembly::add starts *)
(* a fresh message), and a failed verdict restores nothing. "keep": every  *)
(* candidate that completed goes back at once to its runs before the       *)
(* fragment (the machine holds its own copy of the message it was handed), *)
(* the other one that completed in the same fragment is kept ready, its    *)
(* buffer untouched, and takes no fragment until a failed verdict hands it *)
(* over; fragments that arrive meanwhile go to the candidates. "hold", the *)
(* rule that meets the bounds with a later verdict: "keep", and while a    *)
(* verdict is awaited no fragment is applied: each is held, in the order   *)
(* it came; after a failed verdict (and the ready candidate's turn) the    *)
(* held fragments are applied in that order, as if they had come after the *)
(* verdict, so the run is one of the "sync" rule's. The hold is unbounded  *)
(* here: the code bounds it in bytes (one chunk), above a flight.          *)
(* A verdict comes within the flight it was asked in (a key operation is   *)
(* answered within a resend interval).                                     *)
(*                                                                         *)
(* Checked: Served, by the end of flight FMAX the genuine message was      *)
(* taken. ReasmPair.cfg: every genuine datagram raced by a damaged copy,   *)
(* in any order, taken by the end of the second flight (one resend         *)
(* interval). ReasmPair_any.cfg: one forged fragment of any offset and     *)
(* length, the same bound; ReasmPair_any3.cfg: one such fragment in every  *)
(* flight, taken by the end of the third. All three with VERDICT "hold",   *)
(* which includes a verdict at once. Witnesses ReasmPair_one and           *)
(* ReasmPair_last: damaged copies block the message in every flight.       *)
(* ReasmPair_async: the transport's handling of a later verdict ("code")   *)
(* loses the genuine candidate; ReasmPair_keep: so does "keep", a damaged  *)
(* last part ahead of the genuine one in every flight. ReasmPair_two is    *)
(* the stated ceiling, not met: two forged fragments of any offset and     *)
(* length per flight defeat two candidates.                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS F, FT, FMAX, FV, FK, RULE, VERDICT

MX == 3
NR == 2
INSTANCE ReasmOps

\* pend: the candidate whose message waits for the machine's verdict ("none"); pg: whether that message is the genuine
\* one; rdy: the candidates kept ready with a complete message not handed over yet; rg: whether each one's is genuine;
\* hq: the fragments held while a verdict is awaited ("hold"), oldest first, each <<total, off, len, v>>
VARIABLES a, b, lru, fl, gs, nf, nt, done, pend, pg, rdy, rg, hq
vars == <<a, b, lru, fl, gs, nf, nt, done, pend, pg, rdy, rg, hq>>

K == {"a", "b"}
\* the genuine message in two datagrams
G == <<[off |-> 0, len |-> 2], [off |-> 2, len |-> 1]>>
Genuine(msg) == \A p \in 0..(MX - 1) : msg[p] = 1
\* the length of forged message v
Tot(v) == IF v = 2 THEN MX ELSE MX - 1
Busy(c) == c.r.runs # <<>>
\* the rules that keep a completed candidate ready
Keeps == VERDICT \in {"keep", "hold"}

Init == a = RV0(MX) /\ b = RV0(MX) /\ lru = "a" /\ fl = 1 /\ gs = {} /\ nf = 0 /\ nt = 0 /\ done = FALSE
    /\ pend = "none" /\ pg = FALSE /\ rdy = {} /\ rg = [k \in K |-> FALSE] /\ hq = <<>>

\* one candidate c takes a fragment: ok, it agreed; c, its state after; won, the genuine message was handed over
Take1(c, total, off, len, v) ==
    LET y == AddV(c, MX, NR, total, off, len, v, RULE # "last")
    IN CASE y.out = -2 -> [ok |-> FALSE, c |-> c, won |-> FALSE]
         [] y.out >= 0 /\ Genuine(y.msg) -> [ok |-> TRUE, c |-> y.rv, won |-> TRUE]
         [] y.out >= 0 -> [ok |-> TRUE, c |-> IF RULE = "last" THEN y.rv ELSE c, won |-> FALSE]
         [] OTHER -> [ok |-> TRUE, c |-> y.rv, won |-> FALSE]

DeliverSync(total, off, len, v) ==
    /\ UNCHANGED <<pend, pg, rdy, rg>>
    /\ IF RULE # "pair"
       THEN LET x == Take1(a, total, off, len, v) IN a' = x.c /\ done' = x.won /\ UNCHANGED <<b, lru>>
       ELSE LET xa == Take1(a, total, off, len, v)
                xb == Take1(b, total, off, len, v)
                x0 == Take1(RV0(MX), total, off, len, v)
                ta == Busy(a) /\ xa.ok
                tb == Busy(b) /\ xb.ok
            IN IF ta \/ tb
               THEN /\ a' = (IF ta THEN xa.c ELSE a) /\ b' = (IF tb THEN xb.c ELSE b)
                    /\ done' = ((ta /\ xa.won) \/ (tb /\ xb.won))
                    /\ lru' = IF ta /\ ~tb THEN "b" ELSE IF tb /\ ~ta THEN "a" ELSE lru
               ELSE LET to == IF ~Busy(a) THEN "a" ELSE IF ~Busy(b) THEN "b" ELSE lru
                    IN IF to = "a"
                       THEN a' = x0.c /\ b' = b /\ lru' = "b" /\ done' = x0.won
                       ELSE b' = x0.c /\ a' = a /\ lru' = "a" /\ done' = x0.won

\* candidate c takes a fragment, the verdict left to the machine: ok, it agreed; comp, it completed; gen, the message
\* it completed is the genuine one; after, its state after the add (emptied when it completed)
Take2(c, total, off, len, v) ==
    LET y == AddV(c, MX, NR, total, off, len, v, TRUE)
    IN [ok |-> y.out # -2, comp |-> y.out >= 0, gen |-> y.out >= 0 /\ Genuine(y.msg), after |-> y.rv]

DeliverLater(total, off, len, v) ==
    LET cur == [k \in K |-> IF k = "a" THEN a ELSE b]
        \* a ready candidate takes no fragment ("keep")
        open == {k \in K : ~(Keeps /\ k \in rdy)}
        x == [k \in K |-> Take2(cur[k], total, off, len, v)]
        agreed == {k \in open : Busy(cur[k]) /\ x[k].ok}
        to == IF "a" \in open /\ ~Busy(a) THEN "a"
              ELSE IF "b" \in open /\ ~Busy(b) THEN "b"
              ELSE IF lru \in open THEN lru
              ELSE "none"
        x0 == Take2(RV0(MX), total, off, len, v)
        took == IF agreed # {} THEN agreed ELSE IF to = "none" THEN {} ELSE {to}
        res == [k \in K |-> IF agreed # {} THEN x[k] ELSE x0]
        \* the state of each candidate before the fragment (a candidate that starts over is emptied first)
        undo == [k \in K |-> IF agreed # {} THEN cur[k] ELSE RV0(MX)]
        st == [k \in K |-> IF k \in took THEN res[k].after ELSE cur[k]]
        comp == {k \in took : res[k].comp /\ res[k].ok}
        first == IF "a" \in comp THEN "a" ELSE "b"
        new == [k \in K |->
                  IF k \in comp /\ (pend # "none" \/ Keeps) THEN undo[k] ELSE st[k]]
    IN /\ a' = new["a"] /\ b' = new["b"]
       /\ lru' = IF agreed = {} THEN (CASE to = "a" -> "b" [] to = "b" -> "a" [] OTHER -> lru)
                 ELSE IF agreed = {"a"} THEN "b" ELSE IF agreed = {"b"} THEN "a" ELSE lru
       /\ done' = done
       /\ IF pend = "none" /\ comp # {}
          THEN /\ pend' = first /\ pg' = res[first].gen
               /\ rdy' = IF Keeps THEN comp \ {first} ELSE {}
               /\ rg' = [k \in K |-> IF k \in comp THEN res[k].gen ELSE rg[k]]
          \* the machine is waiting for a verdict: it refuses a message that completes meanwhile
          ELSE UNCHANGED <<pend, pg, rdy, rg>>

Deliver(total, off, len, v) ==
    IF VERDICT = "sync" THEN DeliverSync(total, off, len, v) ELSE DeliverLater(total, off, len, v)

\* a fragment arrives: with "hold", while a verdict is awaited or fragments are held, it is held after them
Holding == VERDICT = "hold" /\ (pend # "none" \/ hq # <<>>)
Arrive(total, off, len, v) ==
    IF Holding
    THEN hq' = Append(hq, <<total, off, len, v>>) /\ UNCHANGED <<a, b, lru, done, pend, pg, rdy, rg>>
    ELSE Deliver(total, off, len, v) /\ UNCHANGED hq

\* "hold": no verdict awaited, the oldest held fragment is applied (the code applies them all within the call that
\* brings the failed verdict, stopping at a message that waits for a verdict again)
Replay ==
    /\ VERDICT = "hold" /\ pend = "none" /\ hq # <<>>
    /\ hq' = Tail(hq) /\ UNCHANGED <<fl, gs, nf, nt>>
    /\ Deliver(Head(hq)[1], Head(hq)[2], Head(hq)[3], Head(hq)[4])

\* the host answers the key request: the genuine message is taken; a forged one is dropped, and with "keep" the
\* candidate kept ready is handed over ("keep", "hold")
Verdict ==
    /\ VERDICT # "sync" /\ pend # "none"
    /\ IF pg
       THEN done' = TRUE /\ pend' = "none" /\ rdy' = {} /\ UNCHANGED pg
       ELSE IF rdy # {}
            THEN LET r == CHOOSE r \in rdy : TRUE IN pend' = r /\ pg' = rg[r] /\ rdy' = rdy \ {r} /\ done' = FALSE
            ELSE pend' = "none" /\ pg' = FALSE /\ rdy' = {} /\ done' = FALSE
    /\ UNCHANGED <<a, b, lru, fl, gs, nf, nt, rg, hq>>

GenuineStep == \E i \in {1, 2} \ gs :
    /\ gs' = gs \cup {i} /\ UNCHANGED <<fl, nf, nt>>
    /\ Arrive(MX, G[i].off, G[i].len, 1)
ForgedStep == nf < F /\ nt < FT /\ \E off \in 0..(MX - 1), len \in 1..MX, v \in FV :
    /\ FK = "copy" => \E i \in {1, 2} : off = G[i].off /\ len = G[i].len
    /\ nf' = nf + 1 /\ nt' = nt + 1 /\ UNCHANGED <<gs, fl>>
    /\ Arrive(Tot(v), off, len, v)
EndFlight == gs = {1, 2} /\ pend = "none" /\ hq = <<>> /\ fl' = fl + 1 /\ gs' = {} /\ nf' = 0
    /\ UNCHANGED <<a, b, lru, nt, done, pend, pg, rdy, rg, hq>>

Next == ~done /\ fl <= FMAX /\ (GenuineStep \/ ForgedStep \/ Verdict \/ Replay \/ EndFlight)
Spec == Init /\ [][Next]_vars

Served == fl > FMAX => done
=============================================================================
