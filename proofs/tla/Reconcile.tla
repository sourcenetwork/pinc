------------------------------ MODULE Reconcile ------------------------------
(***************************************************************************)
(* The reconciliation session of pinc-reconcile as a system: an initiator  *)
(* and a responder (ReconcileSess.tla, a byte-level mirror of core.rs and  *)
(* session.rs) joined by two lockstep streams exactly as tests/            *)
(* reconcile_common.rs run_with and drive.rs run them: the initiator sends *)
(* a message, the responder answers it with one message (or, for a cold    *)
(* side, a stream of chunks), the initiator handles each answer, a `last`  *)
(* answer is delivered to the responder at once.                           *)
(*                                                                         *)
(* Inputs are enumerated by `Scenario` (CASE below): "all" is every pair   *)
(* of subsets of a universe of variable length items (the empty item, items *)
(* that are prefixes of others), "real*" are fixed larger sets with the    *)
(* real constants. A case also fixes the message limit, the item limit and *)
(* the id function (idf(x) = rank(x) mod IdMod, so IdMod = 1 collides all  *)
(* ids and IdMod >= |U| is injective).                                     *)
(*                                                                         *)
(* HASH MODEL (the explicit assumption). The code fingerprints a range as  *)
(* a hash of the group sum of its items and their count; the model uses    *)
(* the ideal hash, a homomorphism from signed multisets of items into 32   *)
(* bytes added bytewise modulo 256 (ReconcileOps.tla: AddFp, SubFp).       *)
(* Mode "onehot": item i of the universe (0-based, in LexLt order) is the  *)
(* vector with 1 in byte i, so the fingerprint of a signed multiset is its *)
(* coefficient vector modulo 256. That is injective as long as two         *)
(* coefficients that can occur never differ by a multiple of 256. A        *)
(* coefficient in a range is 0 or 1; in a final check it is 1 for the      *)
(* whole set plus the occurrences in `here` minus those in `there`. Every  *)
(* occurrence in `here` or `there` costs at least one byte of the report,  *)
(* so it is at most MaxReportC, and a coefficient lies in -MaxReportC ..   *)
(* 1 + MaxReportC, a window of 2 MaxReportC + 2 values. The ASSUME below   *)
(* requires the universe to have at most FPLEN = 32 items and the window   *)
(* to fit in 256 (1 + MaxReportC < 128), so equal fingerprints mean equal  *)
(* signed multisets even for a peer that repeats an item; a duplicate does *)
(* not cancel. This states the no-collision assumption exactly. The count *)
(* of the code's fingerprint is the sum of the coefficients, which the     *)
(* injective sum already determines, so the model does not fold it in.     *)
(* Mode "mix" is not that: a pseudo-random 32 byte value per item under    *)
(* bytewise addition, not injective, kept to exercise the code path with   *)
(* realistic bytes (universes above 32 items). The exactness claims of     *)
(* the model rest on the onehot configs.                                   *)
(*                                                                         *)
(* PROPERTIES (INVARIANTS, over every behaviour of every case):            *)
(*  Terminates     the run reaches done / failed / exhausted within        *)
(*                 StepBound handler calls (no deadlock: a state with no   *)
(*                 enabled action is an error). Lean: aps_finishes,         *)
(*                 aps_steps_bound, machine_steps_bound (honest peer),     *)
(*                 initServed_le, respServed_le (any peer, max_rounds)     *)
(*  Correct        on done the report is exactly B \ A and A \ B, each     *)
(*                 item once, through splits, id leaves, item leaves, cold *)
(*                 streams, chunked rounds, narrowed splits and the exact  *)
(*                 pass after an id collision. Lean: aps_session_exact,    *)
(*                 machine_session_exact                                   *)
(*  NoWrong        a wrong result is never reported: with an honest        *)
(*                 responder a collision gives MISS, the exact pass is     *)
(*                 exact; a second disagreement is "mismatch", never a     *)
(*                 wrong answer. Lean: check_detects_wrong,                 *)
(*                 exact_passes_check, aps_session_exact                   *)
(*  HonestOutcome  with cap >= MinMessage and indexes within the item      *)
(*                 limit an honest session ends done; below, it may end    *)
(*                 messageTooLarge and nothing else (plus tooManyRounds    *)
(*                 when the frame stack is scaled below the tree depth).   *)
(*  Cost           handler calls <= RoundsBound, parts sent <= PartsBound,  *)
(*                 bytes <= BytesBound (formulas below). Lean: the parts of *)
(*                 a pass, aps_steps_bound, aps_depth_bound; the rounds    *)
(*                 and bytes bounds are TLC only (not measured in Lean)    *)
(*  Bounds         every body <= FrameCap, the parts of a reply <= cap,    *)
(*                 the report <= maxReport, frames <= MAX_NEST, rounds <=  *)
(*                 maxRounds. Lean: turn_frames, initHandle_frames,         *)
(*                 respHandle_frames, finish_framed, initHandle_rounds     *)
(*  Reset          a reset at any message restarts the session; the        *)
(*                 restarted pair behaves exactly like a fresh pair (a     *)
(*                 shadow pair of fresh machines gets the same inputs and  *)
(*                 must give the same outputs); all attempts reset gives   *)
(*                 "exhausted". Lean: attempt_reset_first, runAttempts_stops,*)
(*                 runAttempts_exhausted, initiator_refused_dead           *)
(*  Garbage        an arbitrary peer (a menu of valid and corrupt          *)
(*                 messages): the initiator ends within maxRounds handler  *)
(*                 calls and a malformed message is refused with the       *)
(*                 reason the menu entry is built to trigger. Lean:        *)
(*                 initServed_le, respServed_le, readParts_canonical       *)
(*  Liar           "miss": a responder that answers every final check with *)
(*                 MISS ends in "mismatch" or an exact report; "never": a  *)
(*                 responder that never answers MISS can make the          *)
(*                 initiator report a wrong result (the witness           *)
(*                 Reconcile_never.cfg): soundness is relative to the      *)
(*                 responder's check verdict. Lean: check_detects_wrong    *)
(*                                                                         *)
(* COST FORMULAS. D = |A xor B|, n = max(|A|,|B|), F = SPLIT if FanTight  *)
(* (no part is narrowed) else 2, LL(1) = 1, LL(m) = 1 + LL(ceil(m/F)),     *)
(* H = 2 LL(n) + 2 (the hops of the range tree: each hop shrinks the       *)
(* receiver's count by F).                                                 *)
(*   PartsBound = 2 (SPLIT (D H + 1) + 3 D + 3) + n + 2                    *)
(* (a differing range yields at most SPLIT children, differing ranges of a *)
(* level are disjoint and each holds a difference item, so at most D per   *)
(* level; a leaf range costs an ids/items part, a reply and a bound of     *)
(* three; the factor 2 is the exact pass; n + 2 the chunks of a cold side) *)
(*   RoundsBound = 2 PartsBound + 8 (a message holds a part, or is an      *)
(*                 empty acknowledgement of a message that holds more)      *)
(*   BytesBound  = PartsBound (1 + 2 BL(mi) + 32) + 4 D leafItems ItemCost *)
(*                 + n ItemCost + (RoundsBound + 1) (3 + 9) + mi + 18      *)
(* with BL(m) = 1 + len(venc(m)) + m, ItemCost = 8 + 9 + mi, leafItems =   *)
(* max(ALEAF, 6).                                                          *)
(***************************************************************************)
EXTENDS ReconcileSess

CONSTANTS ALPHA, MAXLEN, UniMax, Scenario, HashMode, CapSet, MaxItemSet, IdMods, MaxReportC, MaxRoundsC,
          Attempts, ResetOn, Shadow, Liar, Garbage, SmallMenu, FanTight, AllowTMR

RECURSIVE Words(_)
Words(k) == IF k = 0 THEN {<<>>} ELSE {w \o <<x>> : w \in Words(k - 1), x \in ALPHA}
UniAll == UNION {Words(k) : k \in 0..MAXLEN}

RECURSIVE SortedSeq(_)
SortedSeq(X) ==
    IF X = {} THEN <<>>
    ELSE LET m == CHOOSE m \in X : \A y \in X : y = m \/ LexLt(m, y) IN <<m>> \o SortedSeq(X \ {m})

Range(s) == {s[i] : i \in 1..Len(s)}

UniSeq == Take(SortedSeq(UniAll), UniMax)
Universe == Range(UniSeq)
IdxOf == [x \in UniAll |-> Cardinality({y \in UniAll : LexLt(y, x)})]

RECURSIVE Gen(_, _)
Gen(st, k) == IF k = 0 THEN <<>> ELSE LET s2 == (st * 75 + 74) % 65537 IN <<s2 % 256>> \o Gen(s2, k - 1)

HashOf(n) ==
    IF HashMode = "onehot"
    THEN [i \in 1..FPLEN |-> IF i = n + 1 THEN 1 ELSE 0]
    ELSE Gen(n + 5, FPLEN)

AllSeq == SortedSeq(UniAll)
(* the one-hot values need a byte per item of the whole word space, not only of the universe, and every coefficient
   (at most MaxReportC occurrences, see the HASH MODEL) must stay inside a window of 256 values *)
ASSUME HashMode = "onehot" => Len(AllSeq) <= FPLEN /\ 1 + MaxReportC < 128
MkOracle(idm) == [H |-> [i \in 1..Len(AllSeq) |-> <<AllSeq[i], HashOf(i - 1)>>],
                  idb |-> [i \in 1..Len(AllSeq) |-> <<AllSeq[i], BeBytes(IDLEN, (i - 1) % idm)>>]]

(* the quick profile (quick/Reconcile_real*.cfg substitute UniSeq <- UniSeqQuick, AllSeq <- AllSeqQuick and
   IdxOf <- IdxOfQuick): the words in the order of LexLt built directly (the empty word, then the words under each
   letter in turn) and the index of a word counted from its letters, equal to SortedSeq(UniAll), its first UniMax
   words and IdxOf, so that every word is not sorted at start-up *)
RECURSIVE AlphaSeq(_)
AlphaSeq(X) == IF X = {} THEN <<>> ELSE LET m == CHOOSE m \in X : \A y \in X : m <= y IN <<m>> \o AlphaSeq(X \ {m})
RECURSIVE LexWords(_)
LexWords(k) ==
    IF k = 0 THEN <<<<>>>>
    ELSE LET sub == LexWords(k - 1)
             al == AlphaSeq(ALPHA)
         IN <<<<>>>> \o Flat([i \in 1..Len(al) |-> [j \in 1..Len(sub) |-> <<al[i]>> \o sub[j]]])
AllSeqQuick == LexWords(MAXLEN)
UniSeqQuick == Take(AllSeqQuick, UniMax)
RECURSIVE WordsUpTo(_)
WordsUpTo(m) == IF m < 0 THEN 0 ELSE 1 + Cardinality(ALPHA) * WordsUpTo(m - 1)
RECURSIVE WordRank(_, _)
WordRank(w, j) ==
    IF j > Len(w) THEN 0
    ELSE 1 + Cardinality({b \in ALPHA : b < w[j]}) * WordsUpTo(MAXLEN - j) + WordRank(w, j + 1)
IdxOfQuick == [x \in UniAll |-> WordRank(x, 1)]

(* ---- the cases ---- *)

Pick(pred(_)) == SelectSeq(UniSeq, pred)
IdxIn(x, lo, hi, step) == IdxOf[x] >= lo /\ IdxOf[x] < hi /\ (IdxOf[x] - lo) % step = 0
SubSets == {SortedSeq(X) : X \in SUBSET Universe}
(* the quick profile of the real cases (quick/Reconcile_real*.cfg substitute SubSets <- SubSetsQuick): the same set,
   the strictly ascending sequences of words of the universe, as a set TLC does not enumerate at start-up (it tries to
   enumerate SubSets over a universe of the real cases until it runs out of memory; the real cases never read it) *)
SubSetsQuick == {s \in Seq(Universe) : Len(s) <= UniMax /\ \A i \in 1..(Len(s) - 1) : LexLt(s[i], s[i + 1])}

Pairs ==
    CASE Scenario = "all" -> SubSets \X SubSets
      [] Scenario = "cold" ->
            \* a tiny or cold side against a big one, both directions
            {p \in SubSets \X SubSets : Len(p[1]) <= 1 \/ Len(p[2]) <= 1 \/ Len(p[1]) * 3 < Len(p[2]) \/ Len(p[2]) * 3 < Len(p[1])}
      [] Scenario = "dense" ->
            \* dense ranges: many items under one long shared prefix
            {p \in SubSets \X SubSets : Len(p[1]) >= 3 /\ Len(p[2]) >= 3}
      [] Scenario = "real_mid" ->
            {<<Pick(LAMBDA x : IdxOf[x] >= 5 /\ IdxOf[x] < 205),
               Pick(LAMBDA x : IdxOf[x] >= 5 /\ IdxOf[x] < 205 /\ IdxOf[x] # 40 /\ IdxOf[x] # 41 /\ IdxOf[x] # 150)>>}
      [] Scenario = "real_swap" ->
            {<<Pick(LAMBDA x : IdxOf[x] >= 5 /\ IdxOf[x] < 205 /\ IdxOf[x] # 40 /\ IdxOf[x] # 41 /\ IdxOf[x] # 150),
               Pick(LAMBDA x : IdxOf[x] >= 5 /\ IdxOf[x] < 205)>>}
      [] Scenario = "real_cold" ->
            {<<Pick(LAMBDA x : IdxOf[x] >= 5 /\ IdxOf[x] < 9), Pick(LAMBDA x : IdxOf[x] >= 3 /\ IdxOf[x] < 120)>>,
              <<Pick(LAMBDA x : IdxOf[x] >= 3 /\ IdxOf[x] < 120), Pick(LAMBDA x : IdxOf[x] >= 5 /\ IdxOf[x] < 9)>>,
              <<<<>>, Pick(LAMBDA x : IdxOf[x] < 60)>>,
              <<Pick(LAMBDA x : IdxOf[x] < 60), <<>>>>}
      [] Scenario = "real_dense" ->
            \* items 2 and 3 bytes long, all sharing the first byte
            {<<Pick(LAMBDA x : Len(x) >= 2 /\ x[1] = 1 /\ IdxOf[x] % 2 = 0),
               Pick(LAMBDA x : Len(x) >= 2 /\ x[1] = 1 /\ IdxOf[x] % 3 = 0)>>}
      [] Scenario = "real_varlen" ->
            {<<Pick(LAMBDA x : IdxOf[x] < 150 /\ IdxOf[x] % 2 = 0),
               Pick(LAMBDA x : IdxOf[x] < 150 /\ IdxOf[x] % 5 # 1)>>}

Cases == {[A |-> p[1], B |-> p[2], cap |-> cp, mi |-> mi, idm |-> idm] :
          p \in Pairs, cp \in CapSet, mi \in MaxItemSet, idm \in IdMods}

Ref == <<1>>
LimOf(cs) == [maxItem |-> cs.mi, maxMessage |-> cs.cap, maxReport |-> MaxReportC, maxRounds |-> MaxRoundsC]

(* ---- cost bounds ---- *)

RECURSIVE LL(_, _)
LL(m, F) == IF m <= 1 THEN 1 ELSE 1 + LL((m + F - 1) \div F, F)

SymDiff(cs) == (Range(cs.A) \ Range(cs.B)) \cup (Range(cs.B) \ Range(cs.A))
NMax(cs) == Max(Len(cs.A), Len(cs.B))
DCnt(cs) == Cardinality(SymDiff(cs))
Hops(cs) == 2 * LL(NMax(cs), IF FanTight THEN SPLIT ELSE 2) + 2
PartsBound(cs) == 2 * (SPLIT * (DCnt(cs) * Hops(cs) + 1) + 3 * DCnt(cs) + 3) + NMax(cs) + 2
RoundsBound(cs) == 2 * PartsBound(cs) + 8
ItemCost(cs) == IDLEN + VARMAX + cs.mi
BytesBound(cs) ==
    PartsBound(cs) * (1 + 2 * BoundLen(cs.mi) + FPLEN) + 4 * DCnt(cs) * Max(ALEAF, 6) * ItemCost(cs)
    + NMax(cs) * ItemCost(cs) + (RoundsBound(cs) + 1) * (3 + VARMAX) + cs.mi + 2 * VARMAX

(* ---- the garbage menu ---- *)

Frame(body) == BeBytes(3, Len(body)) \o body
FpBytes == [i \in 1..FPLEN |-> 7]
Hd(kind, lo, hi) == PutHead(<<>>, kind, lo, hi)[1]
PartsMenu ==
    {Hd(1, <<>>, None) \o FpBytes, Hd(1, <<>>, Some(<<1>>)) \o FpBytes, Hd(1, <<1>>, Some(<<1, 1>>)) \o FpBytes,
     Hd(3, <<>>, None) \o Venc(1) \o Venc(1) \o <<1>>, Hd(5, <<>>, None) \o Venc(1) \o Venc(1) \o <<0>>,
     Hd(5, <<>>, None) \o Venc(0), Hd(4, <<>>, None) \o Venc(0) \o Venc(0), Hd(4, <<>>, None) \o Venc(1) \o <<1>> \o Venc(0),
     Hd(7, <<>>, None), Hd(7, <<1>>, None), Hd(2, <<>>, None) \o Venc(0), Hd(6, <<>>, None) \o FpBytes,
     <<9, 0, 0>>, <<1, 0>>, Hd(1, <<>>, None)}
BodiesMenu ==
    {PutParts(0, FALSE), PutParts(0, TRUE), <<>>, <<255>>} \cup
    {PutParts(1, m) \o p : p \in PartsMenu, m \in BOOLEAN} \cup
    {PutParts(2, FALSE) \o p \o q : p \in PartsMenu, q \in PartsMenu} \cup
    {PutParts(1, FALSE) \o p \o <<0>> : p \in PartsMenu} \cup
    {Take(PutParts(1, FALSE) \o p, k) : p \in PartsMenu, k \in {2, 4, 9}}
SmallParts == {Hd(1, <<>>, None) \o FpBytes, Hd(3, <<>>, None) \o Venc(1) \o Venc(1) \o <<1>>, Hd(5, <<>>, None) \o Venc(0),
               Hd(4, <<>>, None) \o Venc(0) \o Venc(0), Hd(7, <<>>, None), Hd(2, <<>>, None) \o Venc(0)}
SmallBodies ==
    {PutParts(0, FALSE), PutParts(0, TRUE)} \cup {PutParts(1, m) \o p : p \in SmallParts, m \in BOOLEAN}
GarbageMenu ==
    IF SmallMenu THEN {Frame(b) : b \in SmallBodies}
    ELSE {Frame(b) : b \in BodiesMenu} \cup {<<0, 0>>, <<0, 0, 5, 0>>, <<0, 0, 1, 0, 0>>}

VARIABLES cs, ini, rsp, shI, shR, pc, tx, replies, nxt, fmsg, attempt, delivered, steps, err, cnt,
          shOk, bad
vars == <<cs, ini, rsp, shI, shR, pc, tx, replies, nxt, fmsg, attempt, delivered, steps, err, cnt, shOk, bad>>

Terminal == pc \in {"done", "failed", "exhausted"}
EmptyCnt == [calls |-> 0, bytes |-> 0, msgs |-> 0, parts |-> 0, maxBody |-> 0]

PartsOf(msg) ==
    IF msg = <<>> THEN 0
    ELSE LET fb == FrameBody(msg) IN
         IF ~fb.ok THEN 0
         ELSE LET rp == ReadParts(fb.v) IN IF rp.ok THEN rp.v[1][1] ELSE 0

Account(c, out) ==
    [calls |-> c.calls + 1, bytes |-> c.bytes + Len(out), msgs |-> c.msgs + IF out = <<>> THEN 0 ELSE 1,
     parts |-> c.parts + PartsOf(out), maxBody |-> Max(c.maxBody, Len(out))]

Init ==
    /\ cs \in Cases
    /\ ini = NewInitiator(LimOf(cs))
    /\ rsp = NewResponder(LimOf(cs))
    /\ shI = NewInitiator(LimOf(cs))
    /\ shR = NewResponder(LimOf(cs))
    /\ pc = "start"
    /\ tx = <<>> /\ replies = <<>> /\ nxt = None /\ fmsg = <<>>
    /\ attempt = 1 /\ delivered = 0 /\ steps = 0 /\ err = "" /\ cnt = EmptyCnt /\ shOk = TRUE /\ bad = <<>>

OrcTab == [idm \in IdMods |-> MkOracle(idm)]
orc == OrcTab[cs.idm]

Same(x, y) == x = y
Fail(e) == /\ pc' = "failed" /\ err' = e /\ UNCHANGED <<tx, nxt, fmsg>>

(* the shadow: a fresh pair gets the same inputs; used after a restart *)
DoStart ==
    /\ pc = "start"
    /\ LET r == InitStart(orc, cs.A, ini, Ref)
           sr == IF Shadow THEN InitStart(orc, cs.A, shI, Ref) ELSE r
       IN IF ~r.ok
          THEN /\ Fail(r.err) /\ UNCHANGED <<ini, rsp, shI, shR, shOk, bad, replies>>
          ELSE /\ ini' = r.v[1] /\ tx' = r.v[2]
               /\ rsp' = [rsp EXCEPT !.side = "fresh"]
               /\ shI' = IF sr.ok THEN sr.v[1] ELSE shI
               /\ shR' = NewResponder(LimOf(cs))
               /\ shOk' = (shOk /\ (~Shadow \/ (sr.ok /\ sr.v[2] = r.v[2])))
               /\ replies' = <<>> /\ nxt' = None /\ fmsg' = <<>>
               /\ pc' = IF Garbage THEN "gh" ELSE "rh"
               /\ UNCHANGED <<err, bad>>
    /\ UNCHANGED <<cs, attempt, delivered, cnt>>
    /\ steps' = steps

ShadowEq(r, sr) == ~Shadow \/ (r.ok = sr.ok /\ (r.ok => r.v[1] = sr.v[1] /\ r.v[2] = sr.v[2]) /\ (~r.ok => r.err = sr.err))

\* the responder's answer to a delivered message; the liar rewrites the verdict on the final check
IsCheck(msg) == LET fb == FrameBody(msg) IN fb.ok /\ Len(fb.v) >= 2 /\ fb.v[1] = 2 /\ fb.v[2] = 6 + 128
MissMsg == Frame(PutParts(1, FALSE) \o Hd(7, <<>>, None))
EndMsg == Frame(PutParts(0, FALSE))

RespCall(s, msg) ==
    LET r == RespHandle(orc, cs.B, s, msg) IN
    IF Liar = "miss" /\ IsCheck(msg) /\ r.ok THEN Ok(<<"send", MissMsg, [r.v[3] EXCEPT !.side = "open"]>>)
    ELSE IF Liar = "never" /\ IsCheck(msg) /\ r.ok /\ r.v[2] # EndMsg
         THEN Ok(<<"last", EndMsg, [r.v[3] EXCEPT !.side = "done"]>>)
    ELSE r

DoRH ==
    /\ pc = "rh" /\ ~Garbage
    /\ LET r == RespCall(rsp, tx)
           sr == IF Shadow THEN RespCall(shR, tx) ELSE r
       IN /\ shOk' = (shOk /\ ShadowEq(r, sr))
          /\ cnt' = Account(cnt, IF r.ok THEN r.v[2] ELSE <<>>)
          /\ IF ~r.ok
             THEN /\ Fail(r.err) /\ UNCHANGED <<rsp, shR, replies>>
             ELSE /\ rsp' = r.v[3] /\ shR' = IF sr.ok THEN sr.v[3] ELSE shR
                  /\ replies' = IF r.v[1] \in {"send", "last", "chunk"} THEN Append(replies, r.v[2]) ELSE replies
                  /\ pc' = IF r.v[1] = "chunk" THEN "rr" ELSE "ih"
                  /\ UNCHANGED <<err, tx, nxt, fmsg>>
    /\ delivered' = delivered + 1 /\ steps' = steps + 1
    /\ UNCHANGED <<cs, ini, shI, attempt, bad>>

DoRR ==
    /\ pc = "rr"
    /\ LET r == RespResume(cs.B, rsp)
           sr == IF Shadow THEN RespResume(cs.B, shR) ELSE r
       IN /\ shOk' = (shOk /\ ShadowEq(r, sr))
          /\ cnt' = Account(cnt, IF r.ok THEN r.v[2] ELSE <<>>)
          /\ IF ~r.ok
             THEN /\ Fail(r.err) /\ UNCHANGED <<rsp, shR, replies>>
             ELSE /\ rsp' = r.v[3] /\ shR' = IF sr.ok THEN sr.v[3] ELSE shR
                  /\ replies' = Append(replies, r.v[2])
                  /\ pc' = IF r.v[1] = "chunk" THEN "rr" ELSE "ih"
                  /\ UNCHANGED <<err, tx, nxt, fmsg>>
    /\ steps' = steps + 1
    /\ UNCHANGED <<cs, ini, shI, attempt, delivered, bad>>

DoIH ==
    /\ pc = "ih"
    /\ IF replies = <<>>
       THEN /\ IF nxt = None THEN pc' = "done" /\ UNCHANGED <<tx, nxt>>
                ELSE pc' = (IF Garbage THEN "gh" ELSE "rh") /\ tx' = nxt[1] /\ nxt' = None
            /\ UNCHANGED <<ini, shI, replies, fmsg, err, cnt, shOk, steps, delivered, bad>>
       ELSE LET m == Head(replies)
                r == InitHandle(orc, cs.A, ini, m)
                sr == IF Shadow THEN InitHandle(orc, cs.A, shI, m) ELSE r
            IN /\ steps' = steps + 1 /\ delivered' = delivered + 1
               /\ replies' = Tail(replies)
               /\ shOk' = (shOk /\ ShadowEq(r, sr))
               /\ IF ~r.ok
                  THEN /\ Fail(r.err) /\ UNCHANGED <<ini, shI, cnt>>
                  ELSE /\ ini' = r.v[3] /\ shI' = IF sr.ok THEN sr.v[3] ELSE shI
                       /\ cnt' = Account(cnt, r.v[2])
                       /\ IF r.v[1] = "send" THEN nxt' = Some(r.v[2]) /\ UNCHANGED <<pc, fmsg>>
                          ELSE IF r.v[1] = "last" THEN fmsg' = r.v[2] /\ pc' = "fin" /\ UNCHANGED nxt
                          ELSE UNCHANGED <<nxt, fmsg, pc>>
                       /\ UNCHANGED <<err>>
               /\ UNCHANGED <<tx>>
    /\ UNCHANGED <<cs, rsp, shR, attempt, bad>>

DoFin ==
    /\ pc = "fin"
    /\ LET r == RespCall(rsp, fmsg)
           sr == IF Shadow THEN RespCall(shR, fmsg) ELSE r
       IN /\ shOk' = (shOk /\ ShadowEq(r, sr))
          /\ IF ~r.ok
             THEN /\ Fail(r.err) /\ UNCHANGED <<rsp, shR, replies>>
             ELSE /\ rsp' = r.v[3] /\ shR' = IF sr.ok THEN sr.v[3] ELSE shR
                  /\ pc' = "ih" /\ UNCHANGED <<err, tx, replies, nxt, fmsg>>
    /\ delivered' = delivered + 1 /\ steps' = steps + 1
    /\ UNCHANGED <<cs, ini, shI, attempt, cnt, bad>>

\* the arbitrary peer: any menu message as the answer to what the initiator sent
DoGarbage ==
    /\ pc = "gh"
    /\ \E m \in GarbageMenu : replies' = <<m>> /\ bad' = m
    /\ pc' = "ih"
    /\ steps' = steps + 1
    /\ UNCHANGED <<cs, ini, rsp, shI, shR, tx, nxt, fmsg, attempt, delivered, err, cnt, shOk>>

\* a reset in place of a delivery: the whole session restarts, once per attempt
DoReset ==
    /\ ResetOn /\ pc \in {"rh", "ih", "fin", "rr"}
    /\ attempt' = attempt + 1
    /\ pc' = IF attempt + 1 > Attempts THEN "exhausted" ELSE "start"
    /\ tx' = <<>> /\ replies' = <<>> /\ nxt' = None /\ fmsg' = <<>>
    /\ steps' = steps
    /\ UNCHANGED <<cs, ini, rsp, shI, shR, delivered, err, cnt, shOk, bad>>

Stutter == Terminal /\ UNCHANGED vars

Next == DoStart \/ DoRH \/ DoRR \/ DoIH \/ DoFin \/ DoGarbage \/ DoReset \/ Stutter

Spec == Init /\ [][Next]_vars

(* ---- invariants ---- *)

Honest == ~Garbage /\ Liar = "none"
TooLong == \E x \in Range(cs.A) \cup Range(cs.B) : Len(x) > cs.mi
Exact == /\ Range(ini.core.here) = Range(cs.B) \ Range(cs.A) /\ Len(ini.core.here) = Cardinality(Range(cs.B) \ Range(cs.A))
         /\ Range(ini.core.there) = Range(cs.A) \ Range(cs.B) /\ Len(ini.core.there) = Cardinality(Range(cs.A) \ Range(cs.B))

\* Correct and NoWrong: a finished honest session reports the exact difference
Correct == (Honest /\ pc = "done") => Exact
NoWrong == (Liar # "never" /\ ~Garbage /\ pc = "done") => Exact
Witness_NotWrong == (pc = "done") => Exact

\* Terminates
StepBound == RoundsBound(cs) * Attempts + 4
Terminates == steps <= StepBound
Settled == Terminal => ~(pc = "done" /\ ini.phase # "done")

HonestOutcome ==
    (Honest /\ ~ResetOn /\ pc = "failed") =>
        (  (cs.cap < MinMessage(LimOf(cs)) /\ err = "messageTooLarge")
        \/ (TooLong /\ err = "index")
        \/ (AllowTMR /\ err = "tooManyRounds"))
HonestDone == (Honest /\ ~ResetOn /\ cs.cap >= MinMessage(LimOf(cs)) /\ ~TooLong /\ ~AllowTMR) => pc # "failed"

Exhausted == pc = "exhausted" => attempt = Attempts + 1 /\ ResetOn
ShadowAgrees == shOk

\* Cost: counted over the handler calls of one attempt (a restart re-runs the whole session)
Cost == (Honest /\ ~ResetOn /\ pc = "done") =>
          /\ cnt.calls <= RoundsBound(cs)
          /\ cnt.parts <= PartsBound(cs)
          /\ cnt.bytes <= BytesBound(cs)
FullCost == (Honest /\ ~ResetOn /\ Terminal) => cnt.calls <= RoundsBound(cs) + 1

CoreBounds(c) ==
    \* the parts of a reply stay within the limit from MinMessage up; below it only the root (one part that cannot be cut
    \* further, no message to roll back to) may pass it, and the frame cap still bounds the body
    /\ Len(c.out.body) <= (IF Cap(c.lim) >= MinMessage(c.lim) THEN Cap(c.lim) ELSE FrameCap(c))
    /\ Len(c.frames) <= MAX_NEST
    /\ c.rounds <= c.lim.maxRounds
    /\ DataLen(c.here) + DataLen(c.there) <= c.lim.maxReport
    /\ \A i \in 1..Len(c.frames) : Len(c.frames[i].buf) <= FrameCap(c)

Bounds ==
    /\ CoreBounds(ini.core) /\ CoreBounds(rsp.core)
    /\ cnt.maxBody <= FrameCap(ini.core)

\* Garbage: a malformed menu message is refused (state or reason), never accepted as success
Refused ==
    (Garbage /\ pc = "failed") => err \in {"frame", "truncated", "tag", "bound", "count", "item", "state",
                                             "index", "badIndex", "messageTooLarge", "itemTooLarge",
                                             "reportTooLarge", "tooManyRounds", "mismatch"}
GarbageEnds == Garbage => steps <= MaxRoundsC * 2 + 4
\* a message that is malformed by construction gets the code's reason at the first handling
Expect(m) ==
    LET fb == FrameBody(m) IN
    IF ~fb.ok THEN fb.err
    ELSE IF fb.v = <<>> THEN "truncated"
    ELSE IF fb.v = <<1>> THEN "count"
    ELSE ""
GarbageReason == (Garbage /\ steps = 2 /\ bad # <<>> /\ Expect(bad) # "") => (pc = "failed" /\ err = Expect(bad))
LiarOutcome == (Liar = "miss" /\ pc = "failed") => err = "mismatch"

(* ---- reachability witnesses: TLC must violate each (witness_tlc in scripts/proofs.sh) ---- *)
NotMiss == ~(ini.core.exact)
NotHeld == ~(Holds(rsp.core) \/ Holds(ini.core))
NotDone == pc # "done"
NotMismatch == err # "mismatch"
NotTMR == err # "tooManyRounds"
NotColdStream == ~(rsp.side = "cold")
NotNarrowed == ~(pc = "rh" /\ cnt.calls = 0 /\ Len(cs.A) > ALEAF /\ PartsOf(tx) < SPLIT /\ PartsOf(tx) > 0)
NotTooLarge == err # "messageTooLarge"
NotChunk == ~(pc = "rr")
NotExhausted == pc # "exhausted"
NotRefused == ~(Garbage /\ pc = "failed" /\ err = "truncated")
=============================================================================
