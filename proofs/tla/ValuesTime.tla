------------------------------ MODULE ValuesTime ------------------------------
(***************************************************************************)
(* The time rules of the value fetch, model checked over every input of a  *)
(* small world (properties 4 and 8): HEAD_HOLD (the first granule is held  *)
(* until 96 KiB of verified bytes stand behind it, the value ends in the   *)
(* buffer, 40 later granules verified, 2 s passed, or the fetch is done)   *)
(* and STALL_REDIAL (the wait 4 s doubling to 16 s, raised by ARK_PACE,    *)
(* BYTE_LIVE, STALL_RTT and STALL_LIVE), with the order of the checks of   *)
(* on_timeout and the deadline.                                            *)
(*                                                                         *)
(* The operators are ValuesTimeOps.tla (exact u64 saturating arithmetic of *)
(* U64.tla). This module adds the world: a value of NG granules of 16 KiB, *)
(* a clock that only moves forward over the finite TimeSet, and the inputs *)
(* the environment may give in any order: bytes, a completed frame that is *)
(* matched with a group or skipped, a group verified out of order, a store *)
(* refusal, an eviction, the end of a stream, a timer call with the        *)
(* session's answers w (STALL_RTT) and lv (STALL_LIVE) drawn from WSet and *)
(* LVSet, and the arming of the steal and retry timers.                    *)
(*                                                                         *)
(* Configs (scripts/proofs.sh):                                            *)
(*  _hold      real HOLD_B (6 granules) and HOLD_NV, 7 granules, groups     *)
(*             verified in every order, timer calls: every cause but       *)
(*             Granules (40 later granules do not fit; Lean and the trace  *)
(*             cover HOLD_NV = 40, _holdsmall covers the cause with 2);    *)
(*  _holdsmall HOLD_B = 2 granules, HOLD_NV = 2, the first request offset  *)
(*             mid-granule (the tail is the end of the wanted ranges);        *)
(*  _stall, _live, _max, _dl  the wait, STALL_RTT, STALL_LIVE, clocks up   *)
(*             to u64::MAX, the deadline;                                  *)
(*  _first     bytes, timer calls and arming, no frame (found by NoRedialUnheard): *)
(*             the stall rule never redials a fetch that has no granule;   *)
(*  witnesses (TLC must violate the named property): _wredial (NeverRedialed:   *)
(*             a skipped frame starts the stall rule, the next call redials), *)
(*             _seq (the wait       *)
(*             reaches 16 s), _low (the wait is not monotone), _wbuf,      *)
(*             _wbufreal, _wtail, _wgran, _wtime, _wdone (each release     *)
(*             cause is reachable).                                        *)
(*                                                                         *)
(* Checked (INVARIANT / PROPERTY in the .cfg files):                       *)
(*  AnnStored, HeldNotAnn, FirstOnce, DoneReleased, AnnOnce: the first     *)
(*   granule is announced only after it is verified and stored, exactly    *)
(*   once, and not while held;                                             *)
(*  J0, PollBound, NoLateAct, HoldBound, LaterImmediate: no cause that     *)
(*   holds is ignored between calls, poll_timeout offers at most t0 +      *)
(*   HOLD_MAX, an on_timeout at or after it leaves no held granule, a      *)
(*   later granule is announced right after its verification;              *)
(*  SwGe, SwLe, SwDecrease, RedialOnly, NoRedialUnheard: the wait stays within  *)
(*   [4 s, cap], falls only where the code lowers it, a redial needs the   *)
(*   wait spent and a frame completed (the first granule starts the rule);  *)
(*  DeadlineAct, FailReasonAct, OneTerminal, PollDeadline: the deadline.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Acts,            \* the enabled inputs: subset of {"bytes","frame","frames","framesf","ahead","aheadf","evict","end","arm","timeout"}
          TimeSet,         \* the clock values
          WSet, LVSet,     \* the answers of the session: STALL_RTT and STALL_LIVE
          RtSet,           \* the values the steal, retry and first-request timers may be armed with
          NG,              \* the value has NG granules of GR bytes
          O0,              \* the first request offset
          WantG,           \* the wanted granules, a subset of 0..NG-1
          Hb, Nvl,         \* HOLD_B and HOLD_NV
          HasDl, DlW,      \* a deadline: whether there is one, and its word
          Striped, NProv, Sto0, DupOK, MaxN, Treq0

GR == 16384
VARIABLES s, now, kind, env, ver, ann, nterm, low, done, n, seen
vars == <<s, now, kind, env, ver, ann, nterm, low, done, n, seen>>
StepBound == n <= MaxN

OP == INSTANCE ValuesTimeOps
U == INSTANCE U64

(* the clocks of the checked worlds, in seconds *)
TS(l) == {OP!Secs(k) : k \in l}
TimesHold == TS({0, 1, 2, 3})
TimesHoldQuick == TS({0, 3})  \* the quick profile (proofs/tla/quick/ValuesTime_hold.cfg): no time, and past HOLD_MAX
TimesStall == TS({0, 1, 3, 9, 17, 33, 100})
TimesStallQuick == TS({0, 1, 9, 17})  \* the quick profile (proofs/tla/quick/ValuesTime_stall.cfg): a redial due by 9 s (the deadline), and late
TimesWait == TS({0, 2, 4, 8, 12, 16, 24, 40, 70})
TimesLive == TS({0, 1, 5, 10, 60, 75, 120})
TimesDl == TS({0, 2, 3, 5, 9, 12})
TimesSeq == TS({0, 2, 8, 16, 40, 70})
TimesLow == TS({0, 1, 41, 100})
TimesWbufQuick == TS({0})  \* the quick profile (proofs/tla/quick/ValuesTime_wbufreal.cfg): the buffered release needs no time
TimesMax == TS({0, 1}) \cup {OP!SSub(U!Max64, OP!Secs(1)), U!Max64}
Sec(k) == OP!Secs(k)
Sec1 == OP!Secs(1)
W1 == {OP!Z}
W2 == {OP!Z, OP!Secs(12)}
W3 == {OP!Z, OP!Secs(12), OP!Secs(60)}
L1 == {OP!Z}
L2 == {OP!Z, OP!Secs(8)}
ZeroW == OP!Z
Dl9 == OP!Secs(9)
Dl5 == OP!Secs(5)
Dl3 == OP!Secs(3)
DlMax == U!Max64


Grp(k) == [off |-> k * GR, len |-> GR]
Groups == {Grp(k) : k \in 0..(NG - 1)}
Offs == {g.off : g \in Groups}
Dl == IF HasDl THEN DlW ELSE OP!Z
WE == (CHOOSE k \in WantG : \A j \in WantG : j <= k) * GR + GR   \* the wanted granules are asked in ascending order
Cfg == [o0 |-> O0, wg |-> {Grp(k) : k \in WantG}, we |-> WE, hasdl |-> HasDl, dl |-> Dl, striped |-> Striped, hb |-> Hb, nvl |-> Nvl]

HasEv(ev, p) == \E i \in 1..Len(ev) : ev[i] = p
Cnt(ev, p) == Cardinality({i \in 1..Len(ev) : ev[i] = p})
Terms(ev) == Cnt(ev, <<"done">>) + Cnt(ev, <<"fail", "Store">>) + Cnt(ev, <<"fail", "Lied">>) + Cnt(ev, <<"fail", "Deadline">>)
HeadG == CHOOSE g \in Groups : g.off <= O0 /\ O0 < g.off + g.len

Init == /\ s = [OP!Init({Grp(k) : k \in Sto0}, NProv) EXCEPT !.treq = Treq0]
        /\ now = OP!Z /\ kind = "init" /\ env = <<OP!Z, OP!Z>>
        /\ ver = {} /\ ann = [o \in Offs |-> 0] /\ nterm = 0 /\ low = FALSE /\ done = FALSE /\ n = 0 /\ seen = {}

(* one transition: the operator's result becomes the state, its records are counted *)
Go(res, t, k, e) ==
    /\ s' = res /\ now' = t /\ kind' = k /\ env' = e
    /\ ver' = ver \cup {res.ev[i][2] : i \in {j \in 1..Len(res.ev) : res.ev[j][1] = "ver"}}
    /\ ann' = [o \in Offs |-> ann[o] + Cnt(res.ev, <<"rd", o>>)]
    /\ nterm' = nterm + Terms(res.ev)
    /\ low' = (low \/ U!Lt(res.sw, s.sw))
    /\ done' = (done \/ HasEv(res.ev, <<"done">>))
    /\ n' = n + 1
    /\ seen' = seen \cup {res.ev[i][3] : i \in {j \in 1..Len(res.ev) : res.ev[j][1] = "rel"}}

S0 == [s EXCEPT !.ev = <<>>]
Times == {t \in TimeSet : ~U!Lt(t, now)}
Free(g) == DupOK \/ (g \notin s.sto /\ g.off \notin ver)

ActBytes == \E t \in Times : Go(OP!ByteLive(S0, t), t, "bytes", env)
ActFrame == \E t \in Times, b \in BOOLEAN, g \in Groups : Free(g) /\ Go(OP!FrameIn(Cfg, S0, t, b, g), t, "frame", env)
ActFrameSkip == \E t \in Times, b \in BOOLEAN : Go(OP!FrameIn(Cfg, S0, t, b, OP!Skip), t, "frames", env)
ActFrameFail == \E t \in Times, b \in BOOLEAN : Go(OP!FrameStoreFail(S0, t, b), t, "framesf", env)
ActAhead == \E t \in Times, g \in Groups : Free(g) /\ Go(OP!Verify(Cfg, S0, t, g), t, "ahead", env)
ActAheadFail == \E t \in Times : Go(OP!Fail(S0, "Store"), t, "aheadf", env)
ActEvict == \E t \in Times, b \in BOOLEAN : Go(OP!Evict(S0, t, b), t, "evict", env)
ActEnd == \E t \in Times : Go(OP!CheckDone(Cfg, S0, t), t, "end", env)
ActArm == \E t \in Times, tw \in RtSet, rt \in RtSet, tq \in RtSet :
            Go([S0 EXCEPT !.tw = tw, !.rt = rt, !.treq = tq], t, "arm", env)
ActTimeout == \E t \in Times, w \in WSet, lv \in LVSet, rearm \in BOOLEAN, rtn \in RtSet :
                Go(OP!OnTimeout(Cfg, S0, t, w, lv, rearm, rtn), t, "timeout", <<w, lv>>)

Next == /\ s.run
        /\ \/ "bytes" \in Acts /\ ActBytes
           \/ "frame" \in Acts /\ ActFrame
           \/ "frames" \in Acts /\ ActFrameSkip
           \/ "framesf" \in Acts /\ ActFrameFail
           \/ "ahead" \in Acts /\ ActAhead
           \/ "aheadf" \in Acts /\ ActAheadFail
           \/ "evict" \in Acts /\ ActEvict
           \/ "end" \in Acts /\ ActEnd
           \/ "arm" \in Acts /\ ActArm
           \/ "timeout" \in Acts /\ ActTimeout

Spec == Init /\ [][Next]_vars

(* ---------------------------- properties of property 4 ---------------------------- *)
AnnStored == \A g \in Groups : ann[g.off] > 0 => (g \in s.sto /\ g.off \in ver)
HeldNotAnn == s.head.h => (ann[s.head.g.off] = 0 /\ s.head.g \in s.sto /\ ~s.rel /\ s.head.g.off \in ver)
AnnOnce == \A g \in Groups : ann[g.off] <= 1
FirstOnce == (HeadG.off \in ver) =>
               ((s.head.h /\ s.head.g = HeadG /\ ann[HeadG.off] = 0 /\ ~s.rel)
                \/ (~s.head.h /\ s.rel /\ ann[HeadG.off] = 1))
DoneReleased == done => (~s.head.h /\ (HeadG.off \in ver => ann[HeadG.off] = 1))

J0 == s.head.h =>
        LET e == s.head.g.off + s.head.g.len
            b == OP!Chain(s.sto, e)
        IN b < Hb /\ e + b < Cfg.we /\ s.nv < Nvl

PollBound == (s.run /\ s.head.h) =>
               (OP!Poll(Cfg, s).p /\ U!Le(OP!Poll(Cfg, s).v, OP!SAdd(s.head.t0, OP!HoldMax)))
PollDeadline == (s.run /\ HasDl) => (OP!Poll(Cfg, s).p /\ U!Le(OP!Poll(Cfg, s).v, OP!SAdd(Dl, U!One)))

NoLateAct == [][ (kind' \in {"frame", "ahead", "end", "timeout"} /\ s'.head.h /\ s'.run)
                   => U!Lt(now', OP!SAdd(s'.head.t0, OP!HoldMax)) ]_vars
HoldBound == [][ (kind' = "timeout" /\ s.run /\ s.head.h /\ U!Le(OP!SAdd(s.head.t0, OP!HoldMax), now')) => ~s'.head.h ]_vars
LaterImmediate == [][ (kind' \in {"frame", "ahead"}) =>
                       \A i \in 1..Len(s'.ev) : s'.ev[i][1] = "ver" =>
                         LET off == s'.ev[i][2]
                         IN IF ~s.rel /\ off <= O0 /\ O0 < off + GR
                            THEN s'.ev[i + 1] = <<"held", off>>
                            ELSE s'.ev[i + 1] = <<"rd", off>> ]_vars

(* ---------------------------- properties of property 8 ---------------------------- *)
MaxLV == CHOOSE m \in LVSet : \A x \in LVSet : U!Le(x, m)
SwMax == IF MaxLV = OP!Z THEN OP!RttCap ELSE OP!SAdd(OP!LiveCap, MaxLV)
HasEvRel(ev, why) == \E i \in 1..Len(ev) : ev[i][1] = "rel" /\ ev[i][3] = why
TailMeansDone == [][ HasEvRel(s'.ev, "tail") => (Cfg.wg \subseteq s'.sto) ]_vars

SwGe == U!Le(OP!StallWait, s.sw)
SwLe == U!Le(s.sw, SwMax)
SwNeverLowered == ~low
SwNot16 == s.sw # OP!Secs(16)
NoRedial == s.sw = OP!StallWait
NoBuffered == "buffered" \notin seen
NoTail == "tail" \notin seen
NoGranules == "granules" \notin seen
NoTimeout == "timeout" \notin seen
NoDone == "done" \notin seen
W0 == {OP!Z}

Redialed == \E i \in 1..Len(s'.ev) : s'.ev[i][1] = "redial"
OverflowDue(p) == ~U!Fits(U!Add(OP!Base(p), p.sw))
SwDecrease == [][ U!Lt(s'.sw, s.sw) =>
                    ( (kind' \in {"frame", "frames", "framesf"} /\ U!Lt(OP!ArkCap, s.sw))
                      \/ (kind' = "timeout" /\ Redialed /\ U!Lt(OP!StallCap, s.sw))
                      \/ (kind' = "timeout" /\ ~Redialed /\ OverflowDue(s)) ) ]_vars
NeverRedialed == [][ ~Redialed ]_vars
NoRedialUnheard == [][ Redialed => s.lastp # OP!Z ]_vars
RedialOnly == [][ Redialed => (kind' = "timeout" /\ s.run /\ ~OP!Late(Cfg, now') /\ OP!Due(s, now')
                               /\ ~OP!RttWait(s, now', env'[1]) /\ env'[2] = OP!Z) ]_vars

(* ---------------------------- the deadline ---------------------------- *)
DeadlineAct == [][ (kind' = "timeout" /\ s.run /\ OP!Late(Cfg, now')) =>
                     ( ~s'.run /\ s'.sw = s.sw /\ s'.lastp = s.lastp /\ s'.lastb = s.lastb /\ s'.tw = s.tw /\ s'.rt = s.rt
                       /\ ~Redialed /\ (HasEv(s'.ev, <<"done">>) \/ HasEv(s'.ev, <<"fail", "Deadline">>))
                       /\ ~(HasEv(s'.ev, <<"done">>) /\ HasEv(s'.ev, <<"fail", "Deadline">>)) ) ]_vars
FailReasonAct == [][ ( HasEv(s'.ev, <<"fail", "Deadline">>) => (kind' = "timeout" /\ s.run /\ OP!Late(Cfg, now')) )
                     /\ ( HasEv(s'.ev, <<"fail", "Store">>) => (kind' \in {"framesf", "aheadf"} /\ s.run) )
                     /\ ( HasEv(s'.ev, <<"fail", "Lied">>) => (kind' = "evict" /\ s.run /\ s.trusted <= 1) ) ]_vars
OneTerminal == nterm <= 1
=============================================================================
