---------------------------- MODULE ReconcileSess ----------------------------
(***************************************************************************)
(* The reply loop with rollback, the frames, the root, the final check,    *)
(* the cold stream and the handlers of the initiator and the responder     *)
(* (core.rs answer/turn/resume, session.rs). TLA+ counterpart of           *)
(* Pinc/ReconcileSession.lean.                                             *)
(*                                                                         *)
(* An initiator is [core, phase] with phase in "idle" "open" "checking"    *)
(* "done"; a responder is [core, side] with side in "fresh" "open" "cold"  *)
(* "done". Every handler returns Ok(<<step, bytes, new state>>) or an      *)
(* error; on an error the caller drops the state (the drivers reset the    *)
(* channel), as the Lean model does.                                       *)
(***************************************************************************)
EXTENDS ReconcileCore

(* answer: the state, the unread bytes (from the first part that did not fit, if some did not) and the parts left *)
RECURSIVE AnswerLoop(_, _, _, _, _)
AnswerLoop(o, S, c, r, k) ==
    IF k = 0 THEN Ok(<<c, r, 0>>)
    ELSE LET cnt0 == c.ans.cnt
             mk == OutMark(c.out)
             mark == mk[1]
             c1 == [c EXCEPT !.out = mk[2], !.bsnap = c.blast]
         IN Bind(ProcPart(o, S, c1, r, mark), LAMBDA pr :
            LET c2 == pr[1] IN
            IF Len(c2.out.body) > Cap(c2.lim)
            THEN IF mark = 0 THEN Er("messageTooLarge")
                 ELSE Ok(<<[c2 EXCEPT !.out = OutRollback(c2.out, mark), !.blast = c.blast,
                                      !.ans.cnt = cnt0], r, k>>)
            ELSE AnswerLoop(o, S, c2, pr[2], k - 1))

PushFrame(c, rest, left) ==
    IF Len(c.frames) >= MAX_NEST THEN Er("tooManyRounds")
    ELSE Ok([c EXCEPT !.frames = <<[buf |-> rest, left |-> left, last |-> c.blast]>> \o c.frames])

CoreResume(o, S, c) ==
    IF c.frames = <<>> THEN Er("state")
    ELSE LET f == Head(c.frames)
             tl == Tail(c.frames)
         IN Bind(AnswerLoop(o, S, [c EXCEPT !.blast = f.last], f.buf, f.left), LAMBDA ar :
            LET c2 == ar[1] IN
            IF ar[3] = 0
            THEN IF ar[2] # <<>> THEN Er("frame")
                 ELSE Ok(<<[c2 EXCEPT !.frames = tl], TRUE>>)
            ELSE Ok(<<[c2 EXCEPT !.frames = <<[buf |-> ar[2], left |-> ar[3], last |-> c2.blast]>> \o tl],
                      ar[3] < f.left>>))

RECURSIVE ResumeLoop(_, _, _, _)
ResumeLoop(o, S, fuel, c) ==
    IF fuel = 0 THEN Ok(c)
    ELSE IF c.frames # <<>> /\ Len(c.out.body) < Cap(c.lim)
         THEN Bind(CoreResume(o, S, c), LAMBDA rr :
                IF rr[2] THEN ResumeLoop(o, S, fuel - 1, rr[1]) ELSE Ok(rr[1]))
         ELSE Ok(c)

RECURSIVE FrameFuel(_)
FrameFuel(fs) == IF fs = <<>> THEN 1 ELSE Head(fs).left + 1 + FrameFuel(Tail(fs))

(* turn: process the parts of a message and build the reply parts *)
CoreTurn(o, S, c, r, nparts) ==
    LET c0 == [c EXCEPT !.out = OutReset(c.out), !.blast = <<>>, !.ans = AnsEmpty]
    IN Bind(AnswerLoop(o, S, c0, r, nparts), LAMBDA ar :
       Bind(IF ar[3] > 0 THEN PushFrame(ar[1], ar[2], ar[3])
            ELSE IF ar[2] # <<>> THEN Er("frame") ELSE Ok(ar[1]), LAMBDA c1 :
       Bind(ResumeLoop(o, S, FrameFuel(c1.frames), c1), LAMBDA c2 : Ok(<<c2, c2.ans>>))))

Holds(c) == c.frames # <<>>

CoreRound(c) == IF c.rounds + 1 > c.lim.maxRounds THEN Er("tooManyRounds") ELSE Ok([c EXCEPT !.rounds = c.rounds + 1])

FrameCap(c) == Cap(c.lim) + 2 * c.lim.maxItem + 4 * VARMAX

CoreBody(c, msg) ==
    Bind(FrameBody(msg), LAMBDA b : IF Len(b) > FrameCap(c) THEN Er("messageTooLarge") ELSE Ok(b))

CoreFinish(c, withHdr, cnt, more) ==
    LET body == (IF withHdr THEN c.hdr ELSE <<>>) \o PutParts(cnt, more) \o c.out.body
        h == FrameHeader(Len(body))
    IN IF h = None \/ Len(body) > FrameCap(c) THEN Er("messageTooLarge") ELSE Ok(h[1] \o body)

CoreEndMsg(c) == CoreFinish([c EXCEPT !.out = OutReset(c.out)], FALSE, 0, FALSE)

CoreRoot(o, S, c) ==
    LET c0 == [c EXCEPT !.out = OutReset(c.out)]
        n == c0.n
    IN Bind(IF n <= ALEAF THEN LeafOk(c0.lim, S, <<>>, None, 0, n, c0.exact) ELSE Ok(FALSE), LAMBDA ok :
       IF ok
       THEN LET c1 == [c0 EXCEPT !.leafed = TRUE]
            IN Bind(IF c1.exact THEN ItemsPart(c1.lim, S, c1.out, 3, <<>>, None, 0, n)
                    ELSE IdsPart(o, c1.lim, S, c1.out, <<>>, None, 0, n), LAMBDA out :
                    Ok(<<[c1 EXCEPT !.out = out], 1>>))
       ELSE Bind(SplitFit(o, c0.lim, S, c0.out, <<>>, None, 0, n, 0, SPLIT, 0), LAMBDA sp :
            Ok(<<[c0 EXCEPT !.out = sp[1]], sp[2]>>)))

CoreStart(o, S, c, ref) ==
    IF Len(ref) > c.lim.maxItem THEN Er("itemTooLarge")
    ELSE LET c1 == [CoreClear(c) EXCEPT !.n = Len(S), !.hdr = Venc(Len(ref)) \o ref \o Venc(Len(S))]
         IN Bind(CoreRoot(o, S, c1), LAMBDA rt :
            Bind(CoreFinish(rt[1], TRUE, rt[2], FALSE), LAMBDA msg : Ok(<<rt[1], msg>>)))

CoreRestartExact(o, S, c) ==
    LET c1 == [c EXCEPT !.exact = TRUE, !.leafed = FALSE, !.frames = <<>>, !.here = <<>>, !.there = <<>>]
    IN Bind(CoreRoot(o, S, c1), LAMBDA rt :
       Bind(CoreFinish(rt[1], FALSE, rt[2], FALSE), LAMBDA msg : Ok(<<rt[1], msg>>)))

CoreCheckMsg(o, S, c) ==
    LET fp == XorFp(XorFp(FpRange(o, S, 0, c.n), XorH(o, c.here)), XorH(o, c.there))
        o1 == OutHead(OutReset(c.out), 6, <<>>, None)
        c1 == [c EXCEPT !.out = [o1 EXCEPT !.body = o1.body \o fp]]
    IN Bind(CoreFinish(c1, FALSE, 1, FALSE), LAMBDA msg : Ok(<<c1, msg>>))

(* is_cold: na is the initiator's item count, saturated like every varint *)
IsCold(na, nb) == nb <= ALEAF \/ na * COLD_RATIO < nb

RECURSIVE ColdGo(_, _, _, _, _, _, _, _, _)
ColdGo(lim, S, n, i, fixed, budget, j, longest, stage) ==
    IF j >= n THEN Ok(<<j, stage>>)
    ELSE Bind(ReadItem(lim, S, j), LAMBDA x :
         LET lg == Max(longest, Len(x)) IN
         IF j > i /\ Len(stage) + Len(x) + VARMAX + fixed + BoundLen(lg + 1) > budget THEN Ok(<<j, stage>>)
         ELSE ColdGo(lim, S, n, i, fixed, budget, j + 1, lg, stage \o Venc(Len(x)) \o x))

CoreColdChunk(S, c) ==
    LET lim == c.lim
        n == c.n
        i == c.coldAt
        budget == Min(Cap(lim), 1048576)
        fixed == 2 * VARMAX + BoundLen(Len(c.coldLo))
    IN Bind(ColdGo(lim, S, n, i, fixed, budget, i, 0, <<>>), LAMBDA gj :
       LET j == gj[1]
           stage == gj[2]
           last == j >= n
           out0 == OutReset(c.out)
       IN Bind(IF last THEN Ok(<<OutHead(out0, 5, c.coldLo, None), c.coldLo>>)
               ELSE Bind(ReadItem(lim, S, j - 1), LAMBDA p :
                    Bind(ReadItem(lim, S, j), LAMBDA q :
                       LET k == Cpl(p, q) + 1 IN
                       IF k > Len(q) THEN Er("badIndex")
                       ELSE Ok(<<OutHead(out0, 5, c.coldLo, Some(Take(q, k))), Take(q, k)>>))), LAMBDA ho :
          LET out1 == [ho[1] EXCEPT !.body = ho[1].body \o Venc(j - i) \o stage, !.stage = stage]
              c1 == [c EXCEPT !.out = out1, !.coldLo = ho[2], !.coldAt = j]
          IN Bind(CoreFinish(c1, FALSE, 1, FALSE), LAMBDA msg : Ok(<<c1, msg, last>>))))

(* ---- the handlers ---- *)

NewInitiator(lim) == [core |-> NewCore(lim, TRUE), phase |-> "idle"]
NewResponder(lim) == [core |-> NewCore(lim, FALSE), side |-> "fresh"]

InitStart(o, S, s, ref) ==
    Bind(CoreStart(o, S, s.core, ref), LAMBDA r : Ok(<<[core |-> r[1], phase |-> "open"], r[2]>>))

InitClose(o, S, s, peerDone) ==
    IF s.phase = "checking" THEN Ok(<<"done", <<>>, [s EXCEPT !.phase = "done"]>>)
    ELSE IF s.core.leafed
         THEN Bind(CoreCheckMsg(o, S, s.core), LAMBDA r :
                Ok(<<"send", r[2], [core |-> r[1], phase |-> "checking"]>>))
    ELSE IF peerDone THEN Ok(<<"done", <<>>, [s EXCEPT !.phase = "done"]>>)
    ELSE Bind(CoreEndMsg(s.core), LAMBDA m : Ok(<<"last", m, [s EXCEPT !.phase = "done"]>>))

InitHandle(o, S, s, msg) ==
    IF ~(s.phase = "open" \/ s.phase = "checking") THEN Er("state")
    ELSE Bind(CoreRound(s.core), LAMBDA c0 :
         Bind(CoreBody(c0, msg), LAMBDA body :
         Bind(ReadParts(body), LAMBDA pm :
         Bind(CoreTurn(o, S, c0, pm[2], pm[1][1]), LAMBDA tr :
           LET c == tr[1]
               ans == tr[2]
               np == pm[1][1]
               more == pm[1][2]
               s1 == [s EXCEPT !.core = c]
           IN IF ans.cold
              THEN IF ans.coldEnd THEN Ok(<<"done", <<>>, [s1 EXCEPT !.phase = "done"]>>)
                   ELSE Ok(<<"wait", <<>>, s1>>)
              ELSE IF s.phase = "checking" /\ np > 0 /\ ~ans.miss THEN Er("state")
              ELSE IF ans.miss
                   THEN IF c.exact THEN Er("mismatch")
                        ELSE Bind(CoreRestartExact(o, S, c), LAMBDA rr :
                               Ok(<<"send", rr[2], [core |-> rr[1], phase |-> "open"]>>))
              ELSE IF ans.cnt > 0 \/ Holds(c)
                   THEN Bind(CoreFinish(c, FALSE, ans.cnt, Holds(c)), LAMBDA m : Ok(<<"send", m, s1>>))
              ELSE IF more THEN Bind(CoreEndMsg(c), LAMBDA m : Ok(<<"send", m, s1>>))
              ELSE InitClose(o, S, s1, np = 0)))))

RespResume(S, s) ==
    IF s.side # "cold" THEN Er("state")
    ELSE Bind(CoreColdChunk(S, s.core), LAMBDA r :
         IF r[3] THEN Ok(<<"last", r[2], [core |-> r[1], side |-> "done"]>>)
         ELSE Ok(<<"chunk", r[2], [s EXCEPT !.core = r[1]]>>))

RespRun(o, S, s, r) ==
    Bind(CoreRound(s.core), LAMBDA c0 :
    Bind(ReadParts(r), LAMBDA pm :
    Bind(CoreTurn(o, S, c0, pm[2], pm[1][1]), LAMBDA tr :
       LET c == tr[1]
           ans == tr[2]
       IN IF ans.cnt > 0 \/ Holds(c)
          THEN Bind(CoreFinish(c, FALSE, ans.cnt, Holds(c)), LAMBDA m :
                 Ok(<<"send", m, [core |-> c, side |-> "open"]>>))
          ELSE IF pm[1][2] THEN Bind(CoreEndMsg(c), LAMBDA m : Ok(<<"send", m, [core |-> c, side |-> "open"]>>))
          ELSE IF pm[1][1] = 0 THEN Ok(<<"done", <<>>, [core |-> c, side |-> "done"]>>)
          ELSE Bind(CoreEndMsg(c), LAMBDA m : Ok(<<"last", m, [core |-> c, side |-> "done"]>>)))))

RespHandle(o, S, s, msg) ==
    LET fresh == s.side = "fresh" IN
    IF ~fresh /\ s.side # "open" THEN Er("state")
    ELSE Bind(CoreBody(s.core, msg), LAMBDA body :
         IF fresh
         THEN LET c == CoreClear(s.core) IN
              Bind(Count(body), LAMBDA l :
                IF l[1] > c.lim.maxItem THEN Er("itemTooLarge")
                ELSE Bind(ReadBytes(l[1], l[2]), LAMBDA rf :
                     Bind(Count(rf[2]), LAMBDA na :
                       LET c1 == [c EXCEPT !.n = Len(S)] IN
                       IF IsCold(na[1], c1.n)
                       THEN RespResume(S, [core |-> [c1 EXCEPT !.coldAt = 0, !.coldLo = <<>>], side |-> "cold"])
                       ELSE RespRun(o, S, [core |-> c1, side |-> "open"], na[2]))))
         ELSE RespRun(o, S, s, body))

(* The header of a first message is refused before the responder commits to the session (the frame, the set       *)
(* reference, the size of the other set): a fresh responder that refuses it stays fresh, after that it is done.   *)
RespHeaderRefused(s, msg) ==
    LET rb == CoreBody(s.core, msg) IN
    IF ~rb.ok THEN TRUE
    ELSE LET rl == Count(rb.v) IN
         IF ~rl.ok THEN TRUE
         ELSE IF rl.v[1] > s.core.lim.maxItem THEN TRUE
         ELSE LET rf == ReadBytes(rl.v[1], rl.v[2]) IN
              IF ~rf.ok THEN TRUE ELSE ~Count(rf.v[2]).ok

(* the responder after Responder::handle refused msg *)
RespAfterErr(s, msg) == IF s.side = "fresh" /\ RespHeaderRefused(s, msg) THEN s ELSE [s EXCEPT !.side = "done"]

=============================================================================
