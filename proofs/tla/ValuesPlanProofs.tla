--------------------------- MODULE ValuesPlanProofs ---------------------------
(***************************************************************************)
(* The range-proof frames the value server sends (server.rs): proof_k,     *)
(* Server::proofs and the loss, send and PROOF_REQ events that call it.    *)
(* The model is the code step for step: the end of the proofs, the frame   *)
(* size k (the cost bound and its halving loop, deep trees get none), the *)
(* start (the block of `from`, never before what was sent), the loop that *)
(* cuts frames at block boundaries (at most MaxF per call, stopping at the *)
(* first frame the store or the session refuses: failAt), the state it     *)
(* keeps (deep, pf_to, the send frontier, the window, armed).              *)
(*                                                                         *)
(* The reference for a frame is the range encoder of vinc-dag              *)
(* (ValuesPlanOps RefSteps): its parent steps are the pairs of the proof.  *)
(* Every call is checked for: frames cut at block boundaries (k <= 16      *)
(* groups) and inside one block; a proof of at most PMax (1100) bytes and *)
(* a body inside PROOF_BODY_MAX; the pair count equal to range_pairs of    *)
(* the group range (what fetch/wt.rs on_ext accepts) and to the parents of*)
(* the encoder; at most MaxF frames per call; frames abut and start at or  *)
(* after what was sent and the block of `from`; the groups a call covers   *)
(* start at most `eff` (the upto asked for, else the frontier plus the     *)
(* window) into the value, and on the proactive path at most Lead past the *)
(* frontier; a deep tree (fewer than MinK groups fit) gets none, exactly   *)
(* when it has more than 2^16 groups, and stays deep.                      *)
(*                                                                         *)
(* G is a constant here: TLC integers are 32 bits, so the model runs at a  *)
(* small group size (the tree depth, hence the cost bound, is the same     *)
(* function of the group count); the deep threshold of the code (a value   *)
(* over 1 GiB) is 65536 groups of 16384 bytes.                             *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/ValuesPlanProofsK.lean (protoK_deep_ *)
(* iff, protoK_pow, parentsIn_aligned, proof_bytes_le) and                 *)
(* ValuesPlanProofsFrames.lean (proofs_frames, server_wt_pairs,            *)
(* proofs_deep_sticky), unbounded.                                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS G, PMax, MaxK, MinK, MaxF, Lead, MaxU, BodyHead

Ops == INSTANCE ValuesPlanOps WITH HDR <- 16, PAR <- 64, MaxS <- 1000000, MaxR <- 255

\* x.checked_ilog2().map_or(0, |b| b + 1): the number of bits of x
RECURSIVE BitsGo(_, _)
BitsGo(x, m) == IF x = 0 THEN m ELSE BitsGo(x \div 2, m + 1)
Bits(x) == BitsGo(x, 0)
Cost(dep, k) == 64 * (k - 1) + 64 * Ops!Max(0, dep - Bits(k - 1)) + 8
DepOf(ln) == Bits(Ops!Groups(ln) - 1)

RECURSIVE KLoop(_, _)
KLoop(dep, k) == IF k > 1 /\ Cost(dep, k) > PMax THEN KLoop(dep, k \div 2) ELSE k

(* proof_k: the groups per frame, 0 when the tree is too deep *)
ProofK(ln) ==
    LET dep == DepOf(ln)
        k == KLoop(dep, MaxK)
    IN IF Cost(dep, k) <= PMax /\ k >= MinK THEN k ELSE 0

(* the frame loop: frames sent so far j, `failAt` the first frame the store refuses *)
RECURSIVE FrameLoop(_, _, _, _, _)
FrameLoop(endB, block, at, j, failAt) ==
    IF at < endB /\ j < MaxF
    THEN IF j >= failAt THEN [at |-> at, fr |-> <<>>]
         ELSE LET wn == Ops!Min(block - (at % block), endB - at)
                  r == FrameLoop(endB, block, at + wn, j + 1, failAt)
              IN [at |-> r.at, fr |-> <<[at |-> at, wn |-> wn]>> \o r.fr]
    ELSE [at |-> at, fr |-> <<>>]

(* Server::proofs: the state after and the frames sent *)
ProofsCall(ln, st, vfront, window, from, upto, failAt) ==
    IF ln = 0 \/ st.deep THEN [st |-> st, fr |-> <<>>]
    ELSE LET end0 == Ops!Min(IF upto # 0 THEN upto + G ELSE vfront + window + G, MaxU)
             endB == Ops!Min(ln, end0 - (end0 % G))
             k == ProofK(ln)
         IN IF k = 0 THEN [st |-> [st EXCEPT !.deep = TRUE], fr |-> <<>>]
            ELSE LET block == k * G
                     start == Ops!Max((from \div block) * block, st.pfTo)
                     r == FrameLoop(endB, block, start, 0, failAt)
                 IN [st |-> [st EXCEPT !.pfTo = r.at], fr |-> r.fr]

(* ---- the checks of one call ---- *)
CountP(steps) == Cardinality({i \in 1 .. Len(steps) : steps[i].k = "p"})

FrameOK(ln, k, from, st, f) ==
    LET block == k * G
        a == f.at \div G
        b == (f.at + f.wn + G - 1) \div G
        n == Ops!Groups(ln)
        pairs == Ops!RangePairs(n, a, b)
    IN /\ f.at % G = 0 /\ f.wn >= 1 /\ f.wn <= block /\ f.at + f.wn <= ln
       /\ f.at >= st.pfTo /\ f.at >= (from \div block) * block
       /\ f.at \div block = (f.at + f.wn - 1) \div block
       /\ pairs = CountP(Ops!RefSteps(ln, a, b))
       /\ pairs * 64 <= PMax /\ pairs * 64 + 8 <= Cost(DepOf(ln), k)
       /\ BodyHead + pairs * 64 <= 9 + 21 + PMax

RECURSIVE Abut(_)
Abut(fr) == IF Len(fr) < 2 THEN TRUE
            ELSE fr[1].at + fr[1].wn = fr[2].at /\ Abut(Tail(fr))

CallOK(ln, st, vfront, window, from, upto, failAt) ==
    LET res == ProofsCall(ln, st, vfront, window, from, upto, failAt)
        k == ProofK(ln)
        eff == IF upto # 0 THEN upto ELSE vfront + window
    IN /\ Len(res.fr) <= MaxF
       /\ res.st.pfTo >= st.pfTo
       /\ (res.st.pfTo % G = 0 \/ res.st.pfTo >= ln)
       /\ Abut(res.fr)
       /\ \A i \in 1 .. Len(res.fr) :
            /\ k > 0 /\ FrameOK(ln, k, from, st, res.fr[i])
            /\ ((res.fr[i].at + res.fr[i].wn - 1) \div G) * G <= eff
       /\ (k = 0 => res.st.deep /\ res.fr = <<>>)
       /\ (st.deep => res = [st |-> st, fr |-> <<>>])
       /\ (k = 0 <=> ln > 65536 * G)

(* ---- the machine: a served response in any state its invariants allow, and one event fed to it ---- *)
LNs == {1, 17 * G, 100 * G + 1, 4097 * G, 65536 * G, 65536 * G + 1}

Offs(l) == {0, l \div 2, l, l + 3 * G}
Wins == {0, 64, 400}
Fails == {1, 99}

\* what the invariants allow of pf_to: on a group, or at the end of the value (or past it after a request beyond it)
PfTos(l) == {0, 8 * G, l, l + 5 * G}

VARIABLES ln, st, vfront, window, armed, ok, fired
vars == <<ln, st, vfront, window, armed, ok, fired>>

Init == /\ ln \in LNs
        /\ st \in [deep : BOOLEAN, pfTo : PfTos(ln)]
        /\ vfront \in Offs(ln) /\ window \in Wins /\ armed \in BOOLEAN
        /\ ok = TRUE /\ fired = FALSE

\* ServerIn::Loss: arms, takes the window, moves the frontier, sends from the lost group
Loss == \E from \in Offs(ln), vf \in Offs(ln), w \in Wins, fl \in Fails :
    LET v2 == Ops!Max(vfront, Ops!Min(vf, ln))
        res == ProofsCall(ln, st, v2, w, from, 0, fl)
    IN /\ ok' = CallOK(ln, st, v2, w, from, 0, fl)
       /\ st' = res.st /\ vfront' = v2 /\ window' = w /\ armed' = TRUE /\ ln' = ln

\* ServerIn::Sent: proactive proofs a window ahead once armed, when the frontier passes half way to pf_to
Sent == \E vf \in Offs(ln), w \in Wins, fl \in Fails :
    LET v2 == Ops!Max(vfront, Ops!Min(vf, ln))
        go == armed /\ ~st.deep /\ Ops!Min(v2 + (w \div 2), MaxU) > st.pfTo
        upto == Ops!Min(v2 + Ops!Min(w, Lead), MaxU)
        from == IF v2 = 0 THEN 0 ELSE v2 - 1
        res == ProofsCall(ln, st, v2, w, from, upto, fl)
    IN /\ vfront' = v2 /\ window' = w /\ armed' = armed /\ ln' = ln
       /\ IF go THEN /\ ok' = (CallOK(ln, st, v2, w, from, upto, fl)
                              /\ \A i \in 1 .. Len(res.fr) : ((res.fr[i].at + res.fr[i].wn - 1) \div G) * G <= v2 + Lead)
                     /\ st' = res.st
                ELSE /\ ok' = TRUE /\ st' = st

\* a PROOF_REQ: arms and sends the range asked for
Ext == \E from \in Offs(ln), upto \in Offs(ln) \cup {0, MaxU - 1, MaxU}, fl \in Fails :
    LET res == ProofsCall(ln, st, vfront, window, from, upto, fl)
    IN /\ ok' = CallOK(ln, st, vfront, window, from, upto, fl)
       /\ st' = res.st /\ armed' = TRUE /\ UNCHANGED <<ln, vfront, window>>

Next == /\ ~fired /\ (Loss \/ Sent \/ Ext) /\ fired' = TRUE
Spec == Init /\ [][Next]_vars

Inv == ok
=============================================================================
