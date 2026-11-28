----------------------------- MODULE FirstFlight -----------------------------
(***************************************************************************)
(* The endpoint's intake of a first message in fragments for one id        *)
(* (pinc-core rx.rs offer, unrouted, replay_held; orphan.rs; each holder's *)
(* reassembly, pinc-transport conn/reasm.rs with the agreement rule of     *)
(* ReasmOps.tla AddV), against a third party that sends forged fragments   *)
(* of the first message from the dialer's address before, between or      *)
(* after the genuine ones. A first message cannot be authenticated: any    *)
(* message that completes is taken.                                        *)
(*                                                                         *)
(* The first message is MX = 3 bytes in two genuine datagrams: the start   *)
(* (bytes 0 .. GCUT - 1) and a later part (the rest), sent once per        *)
(* flight; at most F forged fragments arrive per flight, FT in all; FK     *)
(* "copy": each has the offset and length of a genuine datagram, FK "any": *)
(* any offset and length; FW "one": its bytes are all of one forged        *)
(* message (version 2), FW "byte": it is a copy of the genuine bytes       *)
(* damaged at one offset or more (each offset 1 or 2). The holders are at  *)
(* most MAXH = MAX_CANDIDATES (4) and the orphan table NO = ORPHANS (4),   *)
(* as in the code. A holder is a half-open session of the id: cur, its     *)
(* reassembly, and first, the message it took (<<>> for none). A datagram  *)
(* is handed to the holders oldest first; one a holder only adds a part to *)
(* goes on to the others when there are several; one that every holder     *)
(* refuses as different makes a new holder if it starts the message       *)
(* (fewer than MAXH holders), else it is held (the oldest entry given up   *)
(* when the table is full; an entry lives through its flight and may be    *)
(* gone by the next). A new holder takes the datagram that made it, then   *)
(* the held parts.                                                         *)
(*                                                                         *)
(* RULE "new", the code's rule: a holder that has its first message checks *)
(* a repeat fragment against it byte for byte (refused as different when   *)
(* it differs) and reassembles the equal ones again, so forged bytes       *)
(* cannot mix into a repeat; a complete repeat ends the offer. Before the  *)
(* first message, the agreement rule. And held starts: a start taken only  *)
(* as a repeat is held, and makes a new holder at once when parts no       *)
(* holder took are held; a later part no holder took makes a new holder    *)
(* from the newest held start, which stays held until it expires; a held  *)
(* part the new holder refuses stays held.                                 *)
(* FIX, the fork rule R2 that closes the gaps the property tests found    *)
(* (pbt replays 1:86, 3:3 and 5:114), three changes: "fork", a later part  *)
(* that no holder took into its first message while one refused it as      *)
(* different forks from a held start (or is held), whatever repeats took   *)
(* it; "add", a part that added no byte to a holder's first message does   *)
(* not count as taken into it; "agree", the start it forks from is the     *)
(* newest held start that agrees with it on the offsets both hold.         *)
(* RULE "b4": held starts without the step that makes a holder from a      *)
(* repeat start. RULE "cmp": without held starts. RULE "agree": the        *)
(* agreement rule alone, repeats reassembled with it. RULE "old": the rule *)
(* before the handshake fix (the last bytes win).                          *)
(*                                                                         *)
(* Checked: Served, by the end of flight FMAX some holder took the genuine *)
(* message. With R2: FirstFlight.cfg, a single forged fragment of any      *)
(* offset and length, FMAX 2 (one resend interval); FirstFlight_cut, one   *)
(* damaged fragment against a later part of two bytes, FMAX 2;             *)
(* FirstFlight_two, two damaged fragments in one flight or two, FMAX 3.    *)
(* Witnesses (Served fails): FirstFlight_code_cut (the code: a forged byte *)
(* inside a longer later part, replays 1:86 and 3:3), FirstFlight_code_two *)
(* (the code: two damaged whole messages in one flight, replay 5:114),     *)
(* FirstFlight_nofork, _noadd, _noagree (each change of R2 is needed),     *)
(* FirstFlight_b4, _cmp, _agree and _old (each step of the rule is         *)
(* needed). The stated ceiling, not met: FirstFlight_race, damaged copies  *)
(* racing every genuine datagram in an order the third party picks;        *)
(* FirstFlight_fill, three damaged copies, one per flight, fill the        *)
(* holders with mixed messages.                                            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS MAXH, NO, F, FT, FK, FMAX, RULE, GCUT, FW, FIX

MX == 3
NR == 2
INSTANCE ReasmOps

VARIABLES hs, orph, fl, gs, nf, nt
vars == <<hs, orph, fl, gs, nf, nt>>

\* a fragment: its offset, its length and the version of every offset (0 outside it)
Frag(off, len, w) == [off |-> off, len |-> len, w |-> [p \in 0..(MX - 1) |-> IF p >= off /\ p < off + len THEN w[p] ELSE 0]]
Ones == [p \in 0..(MX - 1) |-> 1]
GFrag == <<Frag(0, GCUT, Ones), Frag(GCUT, MX - GCUT, Ones)>>
GMsg == Ones
H0 == [cur |-> RV0(MX), first |-> <<>>]
Cmp == RULE \in {"new", "b4", "cmp"}
B4 == RULE \in {"new", "b4"}
Fix(r) == RULE = "new" /\ r \in FIX

Init == hs = <<>> /\ orph = <<>> /\ fl = 1 /\ gs = {} /\ nf = 0 /\ nt = 0

Same(h, fr) == \A p \in fr.off..(fr.off + fr.len - 1) : h.first[p] = fr.w[p]

\* a holder takes a fragment: "took" its first message, "same" the same message again (complete), "rep" a part of the
\* same message again, "part" a part of its first message, "diff" refused as different. A repeat is compared with the
\* first message byte for byte (handshake_rx.rs part_of_first) and, when equal, reassembled again (add_pair): forged
\* bytes cannot mix into it, and it completes once the repeats cover the message.
Feed(h, fr) ==
    IF Cmp /\ h.first # <<>>
    THEN IF ~Same(h, fr) THEN [r |-> "diff", h |-> h, add |-> FALSE]
         ELSE LET y == AddW(h.cur, MX, NR, MX, fr.off, fr.len, fr.w, TRUE)
              IN IF y.out >= 0 THEN [r |-> "same", h |-> [h EXCEPT !.cur = y.rv], add |-> FALSE]
                 ELSE [r |-> "rep", h |-> [h EXCEPT !.cur = y.rv], add |-> FALSE]
    ELSE LET y == AddW(h.cur, MX, NR, MX, fr.off, fr.len, fr.w, RULE # "old")
         IN CASE y.out = -2 -> [r |-> "diff", h |-> h, add |-> FALSE]
              [] y.out >= 0 /\ h.first = <<>> -> [r |-> "took", h |-> [cur |-> y.rv, first |-> y.msg], add |-> TRUE]
              [] y.out >= 0 /\ y.msg = h.first -> [r |-> "same", h |-> [h EXCEPT !.cur = y.rv], add |-> FALSE]
              [] y.out >= 0 -> [r |-> "diff", h |-> [h EXCEPT !.cur = y.rv], add |-> FALSE]
              [] OTHER -> [r |-> IF h.first = <<>> THEN "part" ELSE "rep", h |-> [h EXCEPT !.cur = y.rv],
                           add |-> y.rv.r # h.cur.r]

\* offer: the holders from i on, oldest first. took: some holder took the datagram (any answer but "diff"); strong: one
\* took it into its first message, completed or not (with "add": and it added bytes the holder did not have); diff: one
\* refused it as different. A part or a repeat part goes on to the next holder when there are several; a complete
\* repeat ends the offer.
RECURSIVE OfferFrom(_, _, _, _)
OfferFrom(hl, i, fr, acc) ==
    IF i > Len(hl) THEN acc
    ELSE LET x == Feed(hl[i], fr)
             hl2 == [hl EXCEPT ![i] = x.h]
             acc2 == [acc EXCEPT !.hl = hl2, !.took = @ \/ x.r # "diff", !.strong = @ \/ x.r = "took" \/ (x.r = "part" /\ (x.add \/ ~Fix("add"))),
                                 !.diff = @ \/ x.r = "diff"]
             on == x.r = "diff" \/ (x.r \in {"part", "rep"} /\ Len(hl) > 1)
         IN IF on THEN OfferFrom(hl2, i + 1, fr, acc2) ELSE acc2

\* the orphan table: hold appends, giving up the oldest entry when full
Hold(o, kind, fr) == Append(IF Len(o) >= NO THEN Tail(o) ELSE o, [kind |-> kind, fr |-> fr])

\* replay_held: the held later parts go to the new holder, oldest first; the held starts stay, and so does a part the
\* new holder refuses (RULE "new": it is still a part of no holder's message)
RECURSIVE Replay(_, _, _)
Replay(h, o, keep) ==
    IF o = <<>> THEN [h |-> h, o |-> keep]
    ELSE IF Head(o).kind = "part"
         THEN LET x == Feed(h, Head(o).fr)
              IN Replay(x.h, Tail(o), IF B4 /\ x.r = "diff" THEN Append(keep, Head(o)) ELSE keep)
    ELSE Replay(h, Tail(o), Append(keep, Head(o)))

\* unrouted: a new holder from the start st (at most MAXH), then the datagram fr that made it, then the held parts
NewHolder(base, st, fr) ==
    IF Len(base) >= MAXH THEN hs' = base /\ orph' = orph
    ELSE LET h1 == Feed(H0, st).h
             x == Replay(IF fr = st THEN h1 ELSE Feed(h1, fr).h, orph, <<>>)
         IN hs' = Append(base, x.h) /\ orph' = x.o

\* the held starts; start_of picks the newest (with "agree": the newest that agrees with the part on the offsets both
\* hold, since every resend of the genuine message carries the same bytes at the same offsets)
Starts(o) == {j \in 1..Len(o) : o[j].kind = "start"}
Agree(a, b) == \A p \in 0..(MX - 1) : (a.w[p] # 0 /\ b.w[p] # 0) => a.w[p] = b.w[p]
Forks(o, fr) == {j \in Starts(o) : Fix("agree") => Agree(o[j].fr, fr)}
Newest(S) == CHOOSE j \in S : \A m \in S : m <= j
Held(o, fr) == \E j \in 1..Len(o) : o[j] = [kind |-> "start", fr |-> fr]
Parts(o) == \E j \in 1..Len(o) : o[j].kind = "part"

\* The code (FIX = {}): a start taken only as a repeat is held, and makes a holder at once when parts are held; a later
\* part no holder took forks from the newest held start, or is held. The fork rule R2 is three changes: "fork", a
\* later part that no holder took into its first message while one refused it as different forks (or is held),
\* whatever repeats took it; "add", a part that added no byte to a holder's first message does not count as taken
\* into it; "agree", the start it forks from is the newest that agrees with it.
Arrive(fr) ==
    LET o == OfferFrom(hs, 1, fr, [hl |-> hs, took |-> FALSE, strong |-> FALSE, diff |-> FALSE])
        start == fr.off = 0
        weak == ~o.strong
        fork == IF Fix("fork") THEN ~o.strong /\ o.diff ELSE ~o.took
    IN IF start /\ o.took
       THEN IF RULE = "new" /\ weak /\ Parts(orph) /\ Len(hs) < MAXH
            THEN NewHolder(o.hl, fr, fr)
            ELSE /\ hs' = o.hl
                 /\ orph' = IF B4 /\ weak /\ ~Held(orph, fr) THEN Hold(orph, "start", fr) ELSE orph
       ELSE IF start THEN NewHolder(o.hl, fr, fr)
       ELSE IF B4 /\ fork /\ Forks(orph, fr) # {} /\ Len(hs) < MAXH THEN NewHolder(o.hl, orph[Newest(Forks(orph, fr))].fr, fr)
       ELSE IF fork \/ ~o.took THEN hs' = o.hl /\ orph' = Hold(orph, "part", fr)
       ELSE hs' = o.hl /\ orph' = orph

\* the versions a forged fragment may carry at each offset: FW "one" all of the forged message (2); "byte" a copy of the
\* genuine bytes damaged in places (each offset 1 or 2, at least one 2)
Forged(off, len) ==
    {w \in [0..(MX - 1) -> {1, 2}] :
        /\ \A p \in 0..(MX - 1) : (p < off \/ p >= off + len) => w[p] = 1
        /\ \E p \in off..(off + len - 1) : w[p] = 2
        /\ FW = "one" => \A p \in off..(off + len - 1) : w[p] = 2}

GenuineStep == \E i \in {1, 2} \ gs : gs' = gs \cup {i} /\ UNCHANGED <<fl, nf, nt>> /\ Arrive(GFrag[i])
ForgedStep == nf < F /\ nt < FT /\ \E off \in 0..(MX - 1), len \in 1..MX :
    /\ off + len <= MX
    /\ FK = "copy" => \E i \in {1, 2} : off = GFrag[i].off /\ len = GFrag[i].len
    /\ nf' = nf + 1 /\ nt' = nt + 1 /\ UNCHANGED <<gs, fl>>
    /\ \E w \in Forged(off, len) : Arrive(Frag(off, len, w))
\* a held entry lives ORPHAN_LIFE (1 s): it stays through a flight, and by the next one it may have expired or not
EndFlight == gs = {1, 2} /\ fl' = fl + 1 /\ gs' = {} /\ nf' = 0 /\ orph' \in {orph, <<>>} /\ UNCHANGED <<hs, nt>>

Got == \E i \in 1..Len(hs) : hs[i].first = GMsg
Served == fl > FMAX => Got
Next == ~Got /\ fl <= FMAX /\ (GenuineStep \/ ForgedStep \/ EndFlight)
Spec == Init /\ [][Next]_vars

TypeOK == Len(hs) <= MAXH /\ Len(orph) <= NO
=============================================================================
