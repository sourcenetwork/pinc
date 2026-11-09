----------------------------- MODULE TraceKeystore -----------------------------
(***************************************************************************)
(* Trace validation of vinc-keystore: the software store, the key host,    *)
(* the sealed format and the TPM store.                                    *)
(*                                                                         *)
(* tests/trace_keystore.rs records keystore.ndjson (events "ks"): handles  *)
(* of two stores and the exact result of every call on them, the binding   *)
(* and answers of a key host, sealed blobs and what unseal makes of them.  *)
(* tests/trace_keystore_tpm.rs records keystore_tpm.ndjson (events "kt")   *)
(* against a software TPM: canned responses, the bytes of every command    *)
(* and response of every store operation with the handles the TPM holds,   *)
(* the sealed blob and every error of unseal. Each event must equal the   *)
(* operators of KeystoreSealed.tla, KeystoreStore.tla and KeystoreTpm.tla: *)
(*  ks: new, rm, sign, pub, nodeid, dec follow the table of handles;       *)
(*      bind, hrm, ans follow the host's binding and Answer; seal and     *)
(*      unseal follow the layout and the genuine blobs of the store        *)
(*  kt: resp is ParseResp; prog has canonical commands, a command list    *)
(*      that is ProgramOf for a failure point, handles that are            *)
(*      live_before + Net, and equal to the entries the store tracks;      *)
(*      hnd and auth are the refusals that send nothing; seal and unseal   *)
(*      follow ParseHeader and UnsealResult                                *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds the two files.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES i, st
vars == <<i, st>>

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/keystore.ndjson")
         \o ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/keystore_tpm.ndjson")

T == INSTANCE KeystoreTpm WITH FlushCanFail <- FALSE, tpm <- 0, primary <- 0, keys <- 0, leaked <- 0, log <- 0, op <- 0, nh <- 0, steps <- 0
I == INSTANCE CryptoIdentity WITH x <- 0

SigLen(a) == I!SigLen[a]
PkLen(a) == I!PkLen[a]

(* ---- the software store ---- *)
Kind(ev) == IF ev.kind = "kem" THEN [k |-> "kem"] ELSE [k |-> "id", alg |-> ev.alg]
Find(tab, h) == {e \in tab : e.h = h}
Classify(tab, h) ==
    IF Find(tab, h) = {} THEN [r |-> "UnknownKey"]
    ELSE LET e == CHOOSE e \in Find(tab, h) : TRUE
         IN IF e.kind.k = "kem" THEN [r |-> "WrongKeyKind"] ELSE [r |-> "ok", alg |-> e.kind.alg]

Min2(a, b) == IF a < b THEN a ELSE b
Genuine(sealed, s, blob) ==
    IF Len(blob) = 0 THEN {}
    ELSE IF blob[1] # 1 THEN {}
    ELSE IF Len(blob) < 1 + 12 + 16 THEN {}
    ELSE {e \in sealed[s] : e.blob = blob}

HostKinds == 1 :> [k |-> "id", alg |-> 1] @@ 2 :> [k |-> "id", alg |-> 2] @@ 3 :> [k |-> "id", alg |-> 3]
             @@ 4 :> [k |-> "id", alg |-> 4] @@ 5 :> [k |-> "kem"]

HostKind(hostTab, bound, sec) ==
    LET bs == {b \in bound : b.sec = sec}
        hs == {e \in hostTab : \E b \in bs : b.h = e.h}
    IN IF hs = {} THEN [k |-> "none"] ELSE (CHOOSE e \in hs : TRUE).kind

HostAnswer(hostTab, bound, ev) ==
    LET kd == HostKind(hostTab, bound, ev.sec)
    IN IF ev.req = "sign"
       THEN IF kd.k = "id" /\ kd.alg = ev.alg THEN [ans |-> "sig", alg |-> ev.alg, len |-> SigLen(ev.alg)] ELSE [ans |-> "failed"]
       ELSE IF kd.k = "kem" THEN [ans |-> "secret"] ELSE [ans |-> "failed"]

SoftOK(ev, s0) ==
    LET s == IF "s" \in DOMAIN ev THEN ev.s ELSE 0
        hm == IF "h" \in DOMAIN ev /\ ev.op # "new" /\ ev.h \in DOMAIN s0.idx THEN s0.idx[ev.h] ELSE 0
        c == Classify(s0.tab[s], hm)
    IN CASE ev.op = "new" -> ev.distinct /\ ~(ev.h \in DOMAIN s0.idx)
         [] ev.op = "rm" -> ev.res = (Find(s0.tab[s], hm) # {})
         [] ev.op = "sign" ->
              IF c.r = "ok" THEN ev.res = "ok" /\ ev.alg = c.alg /\ ev.len = SigLen(c.alg) /\ ev.ver ELSE ev.res = c.r
         [] ev.op = "pub" ->
              IF c.r = "ok" THEN ev.res = "ok" /\ ev.alg = c.alg /\ ev.len = PkLen(c.alg) ELSE ev.res = c.r
         [] ev.op = "nodeid" -> ev.res = c.r /\ ev.same
         [] ev.op = "dec" ->
              IF Find(s0.tab[s], hm) = {} THEN ev.res = "UnknownKey"
              ELSE IF (CHOOSE e \in Find(s0.tab[s], hm) : TRUE).kind.k = "kem"
                   THEN IF ev.ctlen = 1088 THEN ev.res = "ok" /\ ev.agree ELSE ev.res = "Crypto(InvalidLength)"
                   ELSE ev.res = "WrongKeyKind"
         [] ev.op = "bind" -> TRUE
         [] ev.op = "hrm" -> Find(s0.hostTab, ev.k + 1) # {}
         [] ev.op = "ans" ->
              LET a == HostAnswer(s0.hostTab, s0.bound, ev)
              IN IF a.ans = "sig" THEN ev.ans = "sig" /\ ev.alg = a.alg /\ ev.len = a.len /\ ev.ok
                 ELSE IF a.ans = "secret" THEN ev.ans = "secret" /\ ev.ok
                 ELSE ev.ans = "failed"
         [] ev.op = "seal" ->
              /\ ev.blob[1] = 1 /\ Len(ev.blob) = 1 + 12 + Len(ev.pt) + 16
              /\ \A e \in s0.sealed[ev.s] : e.blob # ev.blob
         [] ev.op = "unseal" ->
              LET g == Genuine(s0.sealed, ev.s, ev.blob)
              IN IF g # {} THEN ev.res = "ok" /\ ev.pt = (CHOOSE e \in g : TRUE).pt
                 ELSE ev.res = "InvalidSealed" /\ ev.pt = <<>>
         [] OTHER -> FALSE

SoftNext(ev, s0) ==
    LET s == IF "s" \in DOMAIN ev THEN ev.s ELSE 0
    IN CASE ev.op = "new" ->
              [s0 EXCEPT !.next = @ + 1,
                         !.tab[s] = @ \cup {[h |-> s0.next, kind |-> Kind(ev)]},
                         !.idx = @ @@ (ev.h :> s0.next)]
         [] ev.op = "rm" -> [s0 EXCEPT !.tab[s] = {e \in @ : e.h # s0.idx[ev.h]}]
         [] ev.op = "bind" ->
              [s0 EXCEPT !.hostTab = IF s0.hostTab = {} THEN {[h |-> k, kind |-> HostKinds[k]] : k \in 1..5} ELSE @,
                         !.bound = {b \in @ : b.sec # ev.sec} \cup {[sec |-> ev.sec, h |-> ev.k + 1]}]
         [] ev.op = "hrm" -> [s0 EXCEPT !.hostTab = {e \in @ : e.h # ev.k + 1}]
         [] ev.op = "seal" -> [s0 EXCEPT !.sealed[ev.s] = @ \cup {[blob |-> ev.blob, pt |-> ev.pt]}]
         [] OTHER -> s0

(* ---- the TPM store ---- *)
Auth(m, ev) == IF m \in {"createPrimary", "evictControl"} THEN ev.owner ELSE IF m \in {"sign", "unseal"} THEN ev.key ELSE <<>>
Be32(b, k) == T!Be32(b, k)
KnownCc(cmd) == Len(cmd) >= 10 /\ Be32(cmd, 7)[1] = 0 /\ \E m \in T!Methods : T!CC[m] = Be32(cmd, 7)[2]
MethodOf(cmd) == T!MethodOfCc(Be32(cmd, 7)[2])
RcOf(rsp) == Be32(rsp, 7)
CmdsOK(ev, own, key) ==
    \A k \in 1..Len(ev.cmds) :
        LET c == ev.cmds[k]
        IN /\ KnownCc(c.cmd)
           /\ T!Canonical(MethodOf(c.cmd),
                          IF MethodOf(c.cmd) \in {"createPrimary", "evictControl"} THEN own
                          ELSE IF MethodOf(c.cmd) \in {"sign", "unseal"} THEN key ELSE <<>>, c.cmd)
           /\ Len(c.rsp) >= 10 /\ Be32(c.rsp, 3) = T!LenW(Len(c.rsp))
(* The client sends a command again, with the same bytes, while the TPM answers TPM_RC_RETRY, TPM_RC_YIELDED or        *)
(* TPM_RC_TESTING, at most 8 sends in all. The program is checked on the commands that took effect.                    *)
ResendRc == {<<0, 2338>>, <<0, 2312>>, <<0, 2314>>}
Resent(ev, k) == k < Len(ev.cmds) /\ RcOf(ev.cmds[k].rsp) \in ResendRc /\ ev.cmds[k + 1].cmd = ev.cmds[k].cmd
KeptIdx(ev) == SelectSeq([k \in 1..Len(ev.cmds) |-> k], LAMBDA k : ~Resent(ev, k))
Kept(ev) == [x \in 1..Len(KeptIdx(ev)) |-> ev.cmds[KeptIdx(ev)[x]]]
ResendBound(ev) == \A k \in 1..Len(ev.cmds) : ~(\A d \in 0..7 : Resent(ev, k + d))
Recorded(ev) == [k \in 1..Len(Kept(ev)) |-> <<MethodOf(Kept(ev)[k].cmd), RcOf(Kept(ev)[k].rsp) = T!Zero2>>]
AllOk(rec) == \A k \in 1..Len(rec) : rec[k][2]
FirstBad(ev) == (CHOOSE k \in 1..Len(Kept(ev)) : RcOf(Kept(ev)[k].rsp) # T!Zero2)
ProgOp(name) ==
    CASE name = "open" -> "open" [] name = "generate" -> "generate" [] name = "load_persistent" -> "loadPersistent"
      [] name = "persist" -> "persist" [] name = "sign" -> "sign" [] name = "seal" -> "seal"
      [] name = "generate_unsupported" -> "none" [] OTHER -> "random"

FitsProgram(name, n, rec) ==
    IF name = "random"
    THEN IF AllOk(rec) THEN Len(rec) = (n + 31) \div 32 /\ \A k \in 1..Len(rec) : rec[k][1] = "getRandom"
         ELSE Len(rec) >= 1 /\ \A k \in 1..(Len(rec) - 1) : rec[k] = <<"getRandom", TRUE>>
         /\ rec[Len(rec)] = <<"getRandom", FALSE>>
    ELSE \E f \in -1..2 : T!ProgramOf(ProgOp(name), f).cmds = rec

DeltaOf(name, rec) == T!Net(rec)

TpmOK(ev, st0) ==
    CASE ev.op = "resp" ->
           IF ev.link # "" THEN ev.res = "Transport"
           ELSE LET r == T!ParseResp(ev.rsp, ev.body_ok)
                IN IF r.err = "ok" THEN ev.res = "ok"
                   ELSE IF r.err = "Protocol" THEN ev.res = "Protocol"
                   ELSE ev.res = "Tpm" /\ ev.code = r.code
      [] ev.op = "prog" ->
           LET rec == Recorded(ev)
               la == ev.live_after
               lb == ev.live_before
           IN /\ CmdsOK(ev, ev.owner, ev.key)
              /\ ResendBound(ev)
              /\ FitsProgram(ev.prog, ev.n, rec)
              /\ la = lb + T!Net(rec)
              /\ la = ev.slots
              /\ IF ev.prog = "generate_unsupported" THEN ev.res = "Unsupported"
                 ELSE (ev.res = "ok") = AllOk(rec)
              /\ (~AllOk(rec) /\ ev.res = "Tpm") => ev.code = RcOf(Kept(ev)[FirstBad(ev)].rsp)
      [] ev.op = "hnd" ->
           IF ev.call = "persist_again" THEN ev.res = "InvalidHandle" /\ ev.ncmds = 0
           ELSE IF T!Persistent(ev.h) THEN ev.res # "InvalidHandle" /\ ev.ncmds >= 1
           ELSE ev.res = "InvalidHandle" /\ ev.ncmds = 0
      [] ev.op = "auth" ->
           IF ev.len > T!MaxAuth THEN ev.res = "InvalidAuth" /\ ev.ncmds = 0 ELSE ev.res # "InvalidAuth"
      [] ev.op = "dropped" -> ev.live_after = 0
      [] ev.op = "seal" ->
           LET h == T!ParseHeader(ev.blob, ev.lib_ok)
           IN h.ok /\ h.hdr = ev.hdr /\ Len(ev.blob) = h.hdr + 12 + Len(ev.pt) + 16
      [] ev.op = "unseal" ->
           LET rec == Recorded(ev)
               h == T!ParseHeader(ev.blob, ev.lib_ok)
               Rc(m) == IF \E k \in 1..Len(rec) : rec[k][1] = m
                        THEN RcOf(Kept(ev)[CHOOSE k \in 1..Len(rec) : rec[k][1] = m].rsp) ELSE T!Zero2
               Dek == IF \E k \in 1..Len(rec) : rec[k][1] = "unseal" /\ rec[k][2]
                      THEN LET r == Kept(ev)[CHOOSE k \in 1..Len(rec) : rec[k][1] = "unseal"].rsp IN r[15] * 256 + r[16]
                      ELSE 0
               aead == \E b \in st0.tseal : b = ev.blob
               r == T!UnsealResult(h.ok, Rc("load"), Rc("unseal"), Rc("flush"), Dek, aead)
           IN /\ CmdsOK(ev, ev.owner, ev.key)
              /\ ResendBound(ev)
              /\ (h.ok => h.hdr = ev.hdr)
              /\ (Len(rec) = 0) = ~h.ok
              /\ (Len(rec) = 0 \/ \E f \in -1..1 : T!ProgramOf("unseal", f).cmds = rec)
              /\ IF r.err = "ok" THEN ev.res = "ok" /\ ev.genuine
                 ELSE IF r.err = "InvalidSealed" THEN ev.res = "InvalidSealed"
                 ELSE ev.res = "Tpm" /\ ev.code = r.code
              /\ ev.live_after = ev.live_before
      [] OTHER -> FALSE

TpmNext(ev, st0) == IF ev.op = "seal" THEN [st0 EXCEPT !.tseal = @ \cup {ev.blob}] ELSE st0

EventOK(ev, st0) == IF ev.t = "ks" THEN SoftOK(ev, st0) ELSE TpmOK(ev, st0)
Advance(ev, st0) == IF ev.t = "ks" THEN SoftNext(ev, st0) ELSE TpmNext(ev, st0)

Init == i = 1 /\ st = [next |-> 1, tab |-> [s \in {0, 1} |-> {}], idx |-> << >>, sealed |-> [s \in {0, 1} |-> {}],
                       hostTab |-> {}, bound |-> {}, tseal |-> {}]

Step == /\ i <= Len(Trace)
        /\ EventOK(Trace[i], st)
        /\ st' = Advance(Trace[i], st)
        /\ i' = i + 1
Done == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Done
TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

TraceAccepted == <>(i = Len(Trace) + 1)
=============================================================================
