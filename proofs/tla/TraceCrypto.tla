------------------------------ MODULE TraceCrypto ------------------------------
(***************************************************************************)
(* Trace validation of pinc-crypto: the KDF, node ids and identities, the  *)
(* DRBG, the provider and the secrets.                                     *)
(*                                                                         *)
(* The Rust test tests/trace_crypto.rs calls the public API and records    *)
(* one event per call in crypto.ndjson, with the answers of the primitive  *)
(* libraries (BLAKE3, the signature crates, ChaCha20, AES, X25519), which  *)
(* it called directly, as the oracle. Each event must equal the operators  *)
(* of CryptoKdf.tla, CryptoIdentity.tla, CryptoDrbg.tla, CryptoProvider.tla*)
(* and CryptoSecret.tla on the recorded inputs:                            *)
(*  lbl            the label constants equal the registry                  *)
(*  expand,extract the call fed to the oracle is the model's call, and the*)
(*                 output is the oracle's (a prefix of the XOF)            *)
(*  tags,alg       from_tag for every byte, the lengths                    *)
(*  nid,kpid,match node ids and matches, with the oracle's derive_key      *)
(*  ver,mlv,vnode  verify, verify_ml_dsa_65 and verify_node: the result is *)
(*                 the decision table of the model on the verdicts of the  *)
(*                 libraries                                               *)
(*  kp,write       from_seed, public_key and sign buffer rules             *)
(*  drbg           the limit, the output as the bytes after the next key   *)
(*  key,aead,hpc,hpa,dh,kemkey,kemct  the provider checks and masks        *)
(*  cteq,secret,drop  ct_eq, Secret equality and the bytes after a drop    *)
(* The offset of a ChaCha20 mask and the Ed25519 and P-256 numbers are     *)
(* exact (U64.tla words; the 256-bit seeds as 16 limbs).                   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds crypto.ndjson.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE i

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/crypto.ndjson")

U == INSTANCE U64
K == INSTANCE CryptoKdf WITH x <- i
L == INSTANCE Labels WITH x <- i
I == INSTANCE CryptoIdentity WITH x <- i
D == INSTANCE CryptoDrbg WITH key <- 0, used <- 0, outs <- 0, pc <- 0, residue <- 0, steps <- 0
P == INSTANCE CryptoProvider WITH x <- i
S == INSTANCE CryptoSecret WITH x <- i

FirstB(b) == IF Len(b) > 0 THEN b[1] ELSE 0
KeyOf(b) == I!Key(Len(b), FirstB(b), b)
Flags(l) == I!F(l)
Zeros(n) == [k \in 1..n |-> 0]
Prefix(b, n) == SubSeq(b, 1, n)
Min2(a, b) == IF a < b THEN a ELSE b
ErrOf(r) == IF r.ok THEN "ok" ELSE r.err

(* from_public with the oracle's output for the derive_key call *)
FP(alg, pk, orc) ==
    LET r == I!FromPublic(alg, KeyOf(pk))
    IN IF r.ok THEN [ok |-> TRUE, alg |-> alg, bytes |-> IF alg = 1 THEN pk ELSE orc]
       ELSE [ok |-> FALSE, err |-> r.err]

OracleOK(ev, alg, pk) ==
    IF alg # 1 /\ Len(pk) = I!PkLen[alg]
    THEN /\ Len(ev.orc) = 32 /\ ev.orc_in = K!NodeIdCall(alg, pk).material
    ELSE /\ ev.orc = <<>> /\ ev.orc_in = <<>>

MatchesT(id, alg, pk, orc) == LET r == FP(alg, pk, orc) IN r.ok /\ r.alg = id.alg /\ r.bytes = id.bytes

DigOK(ev, alg) ==
    /\ ev.hyb = (alg = 4)
    /\ IF ev.hyb THEN ev.dig_in = ev.msg /\ ev.dig_in = K!HybridCall(ev.msg).material /\ Len(ev.dig) = 32
       ELSE ev.dig = <<>> /\ ev.dig_in = <<>>

VerifyT(alg, pk, sig, fe, fm) == I!Verify(alg, KeyOf(pk), [len |-> Len(sig)], Flags(fe), Flags(fm))

VerifyNodeT(id, pk, sig, fe, fm, orc) ==
    IF ~MatchesT(id, id.alg, pk, orc) THEN "NodeIdMismatch" ELSE VerifyT(id.alg, pk, sig, fe, fm)

Limbs16(b) == [k \in 1..16 |-> b[2 * k - 1] * 256 + b[2 * k]]
Chains == {"chacha", "aes"}

DrbgOp(o) ==
    IF o.k = "reseed" THEN Len(o.e) = 32
    ELSE IF "err" \in DOMAIN o THEN o.n > D!MaxFill /\ o.err = "InputTooLong"
    ELSE /\ o.n <= D!MaxFill
         /\ D!Fits(o.n)
         /\ Len(o.orc) = 32 + o.n /\ Len(o.out) = o.n
         /\ o.out = SubSeq(o.orc, 33, 32 + o.n)

AllZero(b) == \A k \in 1..Len(b) : b[k] = 0

EventOK(ev) ==
    /\ ev.t = "cr"
    /\ CASE ev.op = "lbl" ->
              /\ ev.prefix = L!Prefix
              /\ ev.sec = L!AllLabels /\ ev.crypto = K!CryptoLabels /\ ev.dtn = K!DtnLabels
              /\ ev.sec \o ev.crypto \o ev.dtn = K!Registry
              /\ K!RegistryOK
         [] ev.op = "expand" ->
              LET c == K!ExpandCall(ev.prk, ev.label, ev.ctx)
              IN /\ Len(ev.prk) = 32
                 /\ c.material = ev.orc_in /\ c.mode = "derive"
                 /\ Len(ev.out) = ev.n /\ ev.out = ev.orc
                 /\ Prefix(ev.orc, Min2(ev.n, 32)) = Prefix(ev.orc32, Min2(ev.n, 32))
         [] ev.op = "extract" ->
              LET c == K!ExtractCall(ev.salt, ev.ikm)
              IN /\ Len(ev.salt) = 32 /\ c.mode = "keyed"
                 /\ ev.orc_key = c.label /\ ev.orc_in = c.material
                 /\ ev.out = ev.orc /\ Len(ev.out) = 32
         [] ev.op = "tags" ->
              /\ Len(ev.res) = 256
              /\ \A t \in 0..255 : ev.res[t + 1] = IF I!FromTag(t).ok THEN I!FromTag(t).alg ELSE 0
         [] ev.op = "alg" ->
              /\ ev.pk = I!PkLen[ev.alg] /\ ev.sig = I!SigLen[ev.alg] /\ ev.seed = I!SeedLen[ev.alg]
              /\ ev.maxpk = I!MaxPk /\ ev.maxsig = I!MaxSig
         [] ev.op = "nid" ->
              LET r == FP(ev.alg, ev.pk, ev.orc)
              IN /\ OracleOK(ev, ev.alg, ev.pk)
                 /\ IF "ok" \in DOMAIN ev.res THEN r.ok /\ r.bytes = ev.res.ok /\ r.alg = ev.alg
                    ELSE ~r.ok /\ r.err = ev.res.err
         [] ev.op = "kpid" ->
              /\ OracleOK(ev, ev.alg, ev.pk)
              /\ FP(ev.alg, ev.pk, ev.orc).ok /\ FP(ev.alg, ev.pk, ev.orc).bytes = ev.id
         [] ev.op = "match" ->
              /\ OracleOK(ev, ev.alg, ev.pk)
              /\ MatchesT(ev.id, ev.alg, ev.pk, ev.orc) = ev.res
         [] ev.op = "ver" ->
              /\ DigOK(ev, ev.alg)
              /\ VerifyT(ev.alg, ev.pk, ev.sig, ev.fe, ev.fm) = ev.res
         [] ev.op = "mlv" ->
              I!MV(KeyOf(ev.pk), ev.ctx, [len |-> Len(ev.sig)], Flags(ev.fm)) = ev.res
         [] ev.op = "vnode" ->
              /\ OracleOK(ev, ev.id.alg, ev.pk)
              /\ DigOK(ev, ev.id.alg)
              /\ VerifyNodeT(ev.id, ev.pk, ev.sig, ev.fe, ev.fm, ev.orc) = ev.res
         [] ev.op = "kp" ->
              I!FromSeed(ev.alg, Len(ev.seed), IF Len(ev.seed) = 32 THEN Limbs16(ev.seed) ELSE <<>>) = ev.res
         [] ev.op = "write" ->
              LET need == IF ev.kind = "pub" THEN I!PkLen[ev.alg] ELSE I!SigLen[ev.alg]
              IN /\ I!WriteOut(need, ev.out) = ev.res
                 /\ ev.n = IF ev.res = "ok" THEN need ELSE 0
         [] ev.op = "drbg" ->
              /\ ev.max = D!MaxFill /\ Len(ev.seed) = 32
              /\ \A k \in 1..Len(ev.ops) : DrbgOp(ev.ops[k])
         [] ev.op = "key" ->
              LET a == IF ev.alg = 0 THEN "chacha" ELSE "aes"
              IN /\ ev.keylen = P!KeyLen[a] /\ P!KeySetup(a, ev.len) = ev.res
         [] ev.op = "aead" ->
              /\ ev.clen = ev.plen /\ ev.tag = P!TagLen
              /\ ev.open = "ok" /\ ev.badtag = P!OpenW(FALSE) /\ ev.badnonce = P!OpenW(FALSE)
         [] ev.op = "hpc" ->
              /\ Len(ev.key) = 32 /\ Len(ev.sample) = P!SampleLen /\ Len(ev.orc) = P!MaskLen
              /\ U!Shl(P!LE32(Prefix(ev.sample, 4)), 6) = U!FromLimbs(ev.orc_off)
              /\ U!Le(U!Add(U!FromLimbs(ev.orc_off), U!W(P!MaskLen)), P!StreamEnd)
              /\ ev.mask = ev.orc
         [] ev.op = "hpa" ->
              /\ Len(ev.key) = 16 /\ Len(ev.sample) = P!SampleLen /\ Len(ev.orc) = 16
              /\ ev.mask = Prefix(ev.orc, P!MaskLen)
         [] ev.op = "dh" ->
              LET zero == ev.orc = Zeros(32)
              IN /\ Len(ev.orc) = 32
                 /\ IF "ok" \in DOMAIN ev.res THEN ~zero /\ ev.res.ok = ev.orc /\ P!DhW(zero) = "ok"
                    ELSE zero /\ ev.res.err = P!DhW(zero)
         [] ev.op = "kemkey" -> P!KemKey(ev.len, ev.mod) = ev.res
         [] ev.op = "kemct" -> P!KemCt(ev.len) = ev.res
         [] ev.op = "cteq" -> S!CtEq(ev.a, ev.b) = ev.eq
         [] ev.op = "secret" ->
              /\ S!CtEq(ev.a, ev.b) = ev.ab /\ S!CtEq(ev.a, ev.c) = ev.ac
              /\ ev.debug = S!Debug(ev.a) /\ S!Debug(ev.a) = S!Debug(ev.c)
         [] ev.op = "drop" -> Len(ev.after) = ev.n /\ AllZero(ev.after) /\ ev.after = S!Zeroize(ev.after)
         [] OTHER -> FALSE

vars == <<i>>
Init == i = 1
Step == /\ i <= Len(Trace)
        /\ EventOK(Trace[i])
        /\ i' = i + 1
Done == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Done
TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

TraceAccepted == <>(i = Len(Trace) + 1)
=============================================================================
