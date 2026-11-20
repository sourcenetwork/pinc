---------------------------- MODULE TraceSecurity ----------------------------
(***************************************************************************)
(* Trace validation of the pure parts of pinc-security: the labels, the    *)
(* credit record, the anti-amplification budget and the padding sizes.     *)
(*                                                                         *)
(* The Rust test tests/trace_security.rs drives the public API and records *)
(* one event per call in security.ndjson:                                  *)
(*  lbl   labels::ALL, labels::PREFIX and the labels of pinc-crypto must   *)
(*        equal the strings of Labels.tla;                                 *)
(*  cred  CreditRecord::new (the window request as four 16-bit limbs, the  *)
(*        record, window_bytes and the 6 bytes), decode of 6 bytes and     *)
(*        covers of two records must equal Credit.tla at its real width    *)
(*        (W = 16, Unit = 2^14), through the same operators;               *)
(*  amp   on_receive, on_send, validate and can_send of an AmpBudget, with *)
(*        the counters after the call, must equal the operations of        *)
(*        AmpOps.tla over the 80-bit words of U64.tla (Max64 saturation,   *)
(*        OVERHEAD 48 from Padding.tla); the trace records a send also in  *)
(*        the saturation runs that do not ask can_send first, so it checks *)
(*        the operations, not the discipline (Amp.tla checks the bound);   *)
(*  pad   min_initial_len and reply_len of every algorithm and form with   *)
(*        the key and signature lengths, and the size constants, must equal*)
(*        the operators and constants of Padding.tla.                      *)
(*                                                                         *)
(* A window request is narrowed for Credit.tla: the quotient by the unit   *)
(* (a shift by 14 on the u64) is kept exactly below 2^17 and replaced by   *)
(* 2^17 above, which NewFromUnits clamps to the same largest field.        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds security.ndjson.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLES i, bud, run
vars == <<i, bud, run>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/security.ndjson")

U == INSTANCE U64
Unit16 == 16384
ASSUME Unit16 = 2 ^ 14

L == INSTANCE Labels WITH x <- i
C == INSTANCE CreditOps WITH W <- 16, Unit <- Unit16
P == INSTANCE Padding WITH x <- i

Times3(a) == U!Add(a, U!Shl(a, 1))
A == INSTANCE AmpOps WITH Zero <- U!Zero, Top <- U!Max64, Ovh <- U!W(P!Overhead), Plus <- U!Add, Leq <- U!Le,
                          Times3 <- Times3

Rec(a) == [wu |-> a[1], ms |-> a[2], md |-> a[3]]
Narrow(q) == IF U!Lt(q, U!Pw(17)) THEN U!Val(q) ELSE 2 ^ 17

LblOK(ev) ==
    /\ ev.all = L!AllLabels
    /\ ev.prefix = L!Prefix
    /\ {ev.crypto[k] : k \in 1..Len(ev.crypto)} = L!CryptoLabels
    /\ Len(ev.crypto) = 2

CredOK(ev) ==
    IF ev.op = "new"
    THEN LET r == C!NewFromUnits(Narrow(U!Shr(U!FromLimbs(ev.w), 14)), ev.s, ev.d)
         IN /\ r = Rec(ev.rec)
            /\ C!WindowBytes(r) = ev.wb
            /\ C!Encode(r) = ev.enc
            /\ C!Decode(ev.enc) = r
    ELSE IF ev.op = "dec"
    THEN LET r == C!Decode(ev.b)
         IN /\ Len(ev.b) = 6
            /\ r = Rec(ev.rec)
            /\ C!Encode(r) = ev.enc
            /\ ev.enc = ev.b
    ELSE /\ ev.op = "cov"
         /\ C!Covers(Rec(ev.a), Rec(ev.b)) = ev.ok

PadOK(ev) ==
    IF ev.op = "min"
    THEN /\ ev.pk = P!Pk[ev.alg]
         /\ ev.sig = P!Sig[ev.alg]
         /\ ev.reply = P!ReplyLen(ev.alg)
         /\ ev.dgs = P!Datagrams(ev.reply)
         /\ ev.min = P!MinInitial(ev.form, ev.alg)
    ELSE /\ ev.op = "const"
         /\ ev.full = P!FullMin /\ ev.short = P!ShortMin /\ ev.dg = P!MinDatagram
         /\ ev.frag = P!FragHeader /\ ev.whole = P!WholeReplyMax /\ ev.splitcid = P!SplitCidMax
         /\ ev.txcid <= P!SplitCidMax /\ ev.epcid <= P!SplitCidMax
         /\ ev.idsig = P!MaxIdSig /\ ev.sealed = P!MaxSealed /\ ev.msg = P!MaxMessage
         /\ ev.overhead = P!Overhead /\ ev.factor = P!Factor
         /\ ev.maxpk = P!MaxPk /\ ev.maxsig = P!MaxSig
         /\ ev.kemct = P!KemCt /\ ev.tag = P!TagLen /\ ev.credit = P!CreditLen /\ ev.cid = P!MaxCid

(* the budget after an amp event, from the budget before it (a fresh one at seq 0) *)
AmpAfter(ev, b0) ==
    LET n == U!FromLimbs(ev.n)
    IN IF ev.op = "rx" THEN A!Recv(b0, n)
       ELSE IF ev.op = "tx" THEN A!Send(b0, n)
       ELSE IF ev.op = "val" THEN A!Validate(b0)
       ELSE b0

AmpOK(ev, b0, b1) ==
    LET n == U!FromLimbs(ev.n)
    IN /\ ev.op \in {"rx", "tx", "val", "can"}
       /\ (ev.op = "can") => (A!CanSend(b0.valid, b0.tx, b0.rx, n) = ev.can)
       /\ b1.rx = U!FromLimbs(ev.rx)
       /\ b1.tx = U!FromLimbs(ev.tx)
       /\ b1.valid = ev.valid

Init == i = 1 /\ bud = A!New /\ run = 0

Step ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i]
       IN /\ i' = i + 1
          /\ IF ev.t = "lbl" THEN LblOK(ev) /\ UNCHANGED <<bud, run>>
             ELSE IF ev.t = "cred" THEN CredOK(ev) /\ UNCHANGED <<bud, run>>
             ELSE IF ev.t = "pad" THEN PadOK(ev) /\ UNCHANGED <<bud, run>>
             ELSE /\ ev.t = "amp"
                  /\ LET b0 == IF ev.seq = 0 THEN A!New ELSE bud
                         b1 == AmpAfter(ev, b0)
                     IN /\ (ev.seq = 0 \/ ev.run = run)
                        /\ AmpOK(ev, b0, b1)
                        /\ bud' = b1
                        /\ run' = ev.run

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == Step \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

(* the whole recorded trace is a behaviour of the specifications *)
TraceAccepted == <>(i = Len(Trace) + 1)
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
