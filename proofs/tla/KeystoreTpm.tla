----------------------------- MODULE KeystoreTpm -----------------------------
(***************************************************************************)
(* The TPM store of pinc-keystore (tpm/client.rs, tpm/store.rs): how a     *)
(* response is read, how a command is laid out, the commands of every      *)
(* store operation, the handles the TPM holds, the sealed blob header and  *)
(* the order of the errors of unseal.                                      *)
(*                                                                         *)
(* A 32-bit number is a pair of 16-bit limbs (TLC integers are 32 bits    *)
(* wide). The marshaling of parameters and bodies is tpm2-protocol's: its  *)
(* verdict on a body (and on the public area of a sealed blob) is an input.*)
(* Transport contract (assumed, not checked): one transmit is one command  *)
(* and its own response; a response does not echo the command code.        *)
(*                                                                         *)
(* The machine runs the operations of the store with every outcome the TPM *)
(* can give (each command may be refused) and keeps three sets: the        *)
(* transient handles the TPM holds, the primary and keys the store tracks, *)
(* and the leaked handles. FlushCanFail is whether a flush may be refused: *)
(*   KeystoreTpm.cfg           flushes succeed: the TPM holds exactly the  *)
(*                             tracked handles after every operation       *)
(*                             (NoLeak), and the commands of every         *)
(*                             operation are the table's (ProgramShape)    *)
(*   KeystoreTpm_flushfails.cfg a refused flush leaks its handle: only the *)
(*                             refused flush of the cleanup of generate    *)
(*                             and of unseal does (LeakAccounted,          *)
(*                             LeakOnlyByRefusedFlush)                     *)
(* Checked besides: ResponseRules, CommandRules (tag, size, code, handle   *)
(* area and password session of every method), UnsealOrder, HeaderRules,   *)
(* RangeRule, AuthRule.                                                    *)
(* TraceKeystore.tla checks the recorded bytes and programs against the    *)
(* operators. Lean counterpart: proofs/lean/Pinc/KeystoreTpm.lean          *)
(* (parseResp_ok_iff, cc_injective, programs_balance, unsealResult_ok_iff).*)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANT FlushCanFail
VARIABLES tpm, primary, keys, leaked, log, op, nh, steps
vars == <<tpm, primary, keys, leaked, log, op, nh, steps>>

(* ---- reading a response ---- *)
Be32(b, i) == <<b[i] * 256 + b[i + 1], b[i + 2] * 256 + b[i + 3]>>
LenW(n) == <<n \div 65536, n % 65536>>
Zero2 == <<0, 0>>

ParseResp(rsp, bodyOk) ==
    IF Len(rsp) < 10 THEN [err |-> "Protocol"]
    ELSE IF Be32(rsp, 3) # LenW(Len(rsp)) THEN [err |-> "Protocol"]
    ELSE IF Be32(rsp, 7) # Zero2 THEN [err |-> "Tpm", code |-> Be32(rsp, 7)]
    ELSE IF ~bodyOk THEN [err |-> "Protocol"]
    ELSE [err |-> "ok"]

(* ---- commands ---- *)
Methods == {"startup", "getRandom", "createPrimary", "create", "load", "evictControl", "readPublic", "sign", "unseal", "flush"}
CC == [startup |-> 324, getRandom |-> 379, createPrimary |-> 305, create |-> 339, load |-> 343, evictControl |-> 288,
       readPublic |-> 371, sign |-> 349, unseal |-> 350, flush |-> 357]
SessionMethods == {"createPrimary", "create", "load", "evictControl", "sign", "unseal"}
NHandles(m) == IF m = "evictControl" THEN 2 ELSE IF m \in {"startup", "getRandom", "flush"} THEN 0 ELSE 1
MethodOfCc(cc) == CHOOSE m \in Methods : CC[m] = cc

AuthAreaSize(n) == 9 + n
MinLen(m, n) == 10 + 4 * NHandles(m) + IF m \in SessionMethods THEN 4 + AuthAreaSize(n) ELSE 0

Canonical(m, auth, cmd) ==
    LET n == Len(auth)
        area == SubSeq(cmd, 11 + 4 * NHandles(m), Len(cmd))
    IN /\ Len(cmd) >= MinLen(m, n)
       /\ cmd[1] = 128 /\ cmd[2] = (IF m \in SessionMethods THEN 2 ELSE 1)
       /\ Be32(cmd, 3) = LenW(Len(cmd))
       /\ Be32(cmd, 7) = <<0, CC[m]>>
       /\ (m \in SessionMethods) =>
            /\ Be32(area, 1) = LenW(AuthAreaSize(n))
            /\ SubSeq(area, 5, 8) = <<64, 0, 0, 9>>
            /\ SubSeq(area, 9, 10) = <<0, 0>>
            /\ area[11] = 1
            /\ SubSeq(area, 12, 13) = <<n \div 256, n % 256>>
            /\ SubSeq(area, 14, 13 + n) = auth

MaxAuth == 64

(* ---- the commands of each operation ---- *)
Ok(m) == <<m, TRUE>>
Bad(m) == <<m, FALSE>>
(* ProgramOf(op, f): the commands sent when command f (an index; -1: none) is refused, and the change in the store's
   transient entries *)
ProgramOf(o, f) ==
    CASE o = "open" -> IF f = -1 THEN [cmds |-> <<Ok("createPrimary")>>, d |-> 1] ELSE [cmds |-> <<Bad("createPrimary")>>, d |-> 0]
      [] o = "generate" ->
           IF f = -1 THEN [cmds |-> <<Ok("create"), Ok("load"), Ok("readPublic")>>, d |-> 1]
           ELSE IF f = 0 THEN [cmds |-> <<Bad("create")>>, d |-> 0]
           ELSE IF f = 1 THEN [cmds |-> <<Ok("create"), Bad("load")>>, d |-> 0]
           ELSE [cmds |-> <<Ok("create"), Ok("load"), Bad("readPublic"), Ok("flush")>>, d |-> 0]
      [] o = "loadPersistent" -> IF f = -1 THEN [cmds |-> <<Ok("readPublic")>>, d |-> 0] ELSE [cmds |-> <<Bad("readPublic")>>, d |-> 0]
      [] o = "persist" ->
           IF f = -1 THEN [cmds |-> <<Ok("evictControl"), Ok("flush")>>, d |-> -1]
           ELSE IF f = 0 THEN [cmds |-> <<Bad("evictControl")>>, d |-> 0]
           ELSE [cmds |-> <<Ok("evictControl"), Bad("flush")>>, d |-> 0]
      [] o = "sign" -> IF f = -1 THEN [cmds |-> <<Ok("sign")>>, d |-> 0] ELSE [cmds |-> <<Bad("sign")>>, d |-> 0]
      [] o = "seal" ->
           IF f = -1 THEN [cmds |-> <<Ok("getRandom"), Ok("getRandom"), Ok("create")>>, d |-> 0]
           ELSE IF f = 0 THEN [cmds |-> <<Bad("getRandom")>>, d |-> 0]
           ELSE IF f = 1 THEN [cmds |-> <<Ok("getRandom"), Bad("getRandom")>>, d |-> 0]
           ELSE [cmds |-> <<Ok("getRandom"), Ok("getRandom"), Bad("create")>>, d |-> 0]
      [] o = "unseal" ->
           IF f = -1 THEN [cmds |-> <<Ok("load"), Ok("unseal"), Ok("flush")>>, d |-> 0]
           ELSE IF f = 0 THEN [cmds |-> <<Bad("load")>>, d |-> 0]
           ELSE [cmds |-> <<Ok("load"), Bad("unseal"), Ok("flush")>>, d |-> 0]
      [] OTHER -> [cmds |-> <<>>, d |-> 0]

Delta(c) ==
    IF c[1] = "createPrimary" /\ c[2] THEN 1
    ELSE IF c[1] = "load" /\ c[2] THEN 1
    ELSE IF c[1] = "flush" /\ c[2] THEN -1
    ELSE 0
RECURSIVE Net(_)
Net(p) == IF Len(p) = 0 THEN 0 ELSE Delta(Head(p)) + Net(Tail(p))

(* ---- the sealed blob header ---- *)
Tpm2bLen(b) ==
    IF Len(b) < 2 THEN 0
    ELSE IF Len(b) < 2 + b[1] * 256 + b[2] THEN 0 ELSE 2 + b[1] * 256 + b[2]

ParseHeader(s, libOk) ==
    IF Len(s) = 0 THEN [ok |-> FALSE]
    ELSE IF s[1] # 2 THEN [ok |-> FALSE]
    ELSE LET body == Tail(s)
             a == Tpm2bLen(body)
             rest == IF a = 0 THEN <<>> ELSE SubSeq(body, a + 1, Len(body))
             b == Tpm2bLen(rest)
         IN IF a = 0 \/ b = 0 \/ ~libOk THEN [ok |-> FALSE] ELSE [ok |-> TRUE, hdr |-> 1 + a + b]

(* ---- the errors of unseal, in the order the code reports them ---- *)
UnsealResult(parseOk, loadRc, unsealRc, flushRc, dekLen, aeadOk) ==
    IF ~parseOk THEN [err |-> "InvalidSealed"]
    ELSE IF loadRc # Zero2 THEN [err |-> "Tpm", code |-> loadRc]
    ELSE IF unsealRc # Zero2 THEN [err |-> "Tpm", code |-> unsealRc]
    ELSE IF flushRc # Zero2 THEN [err |-> "Tpm", code |-> flushRc]
    ELSE IF dekLen # 32 THEN [err |-> "InvalidSealed"]
    ELSE IF ~aeadOk THEN [err |-> "InvalidSealed"]
    ELSE [err |-> "ok"]

Persistent(h) == h[1] >= 33024 /\ h[1] <= 33279       \* 0x8100_0000 ..= 0x81FF_FFFF as limbs: high limb 0x8100 to 0x81FF

(* ---- the machine ---- *)
Init == /\ tpm = {} /\ primary = 0 /\ keys = {} /\ leaked = {} /\ log = <<>> /\ op = <<"none", -1>> /\ nh = 1 /\ steps = 0

Tracked == IF primary = 0 THEN {} ELSE {primary} \cup {k.h : k \in {k \in keys : ~k.per}}

FlushOk == IF FlushCanFail THEN BOOLEAN ELSE {TRUE}

OpenOp == /\ primary = 0 /\ steps < 5
          /\ \E f \in {-1, 0} :
               /\ log' = ProgramOf("open", f).cmds /\ op' = <<"open", f>>
               /\ IF f = -1 THEN tpm' = tpm \cup {nh} /\ primary' = nh /\ nh' = nh + 1
                  ELSE UNCHANGED <<tpm, primary, nh>>
          /\ steps' = steps + 1 /\ UNCHANGED <<keys, leaked>>

GenerateOk == /\ primary # 0 /\ steps < 5
              /\ op' = <<"generate", -1>> /\ log' = ProgramOf("generate", -1).cmds
              /\ tpm' = tpm \cup {nh} /\ keys' = keys \cup {[h |-> nh, per |-> FALSE]} /\ nh' = nh + 1
              /\ steps' = steps + 1 /\ UNCHANGED <<primary, leaked>>

GenerateRefused == /\ primary # 0 /\ steps < 5
                   /\ \E f \in 0..1 : op' = <<"generate", f>> /\ log' = ProgramOf("generate", f).cmds
                   /\ steps' = steps + 1 /\ UNCHANGED <<tpm, primary, keys, leaked, nh>>

GenerateReadFails == /\ primary # 0 /\ steps < 5
                     /\ \E fo \in FlushOk :
                          /\ op' = <<"generate", 2>>
                          /\ log' = <<Ok("create"), Ok("load"), Bad("readPublic"), <<"flush", fo>>>>
                          /\ tpm' = IF fo THEN tpm ELSE tpm \cup {nh}
                          /\ leaked' = IF fo THEN leaked ELSE leaked \cup {nh}
                     /\ nh' = nh + 1 /\ steps' = steps + 1 /\ UNCHANGED <<primary, keys>>

GenerateOp == GenerateOk \/ GenerateRefused \/ GenerateReadFails

PersistOk == /\ steps < 5
             /\ \E k \in keys : ~k.per /\ tpm' = tpm \ {k.h} /\ keys' = (keys \ {k}) \cup {[h |-> k.h, per |-> TRUE]}
             /\ op' = <<"persist", -1>> /\ log' = ProgramOf("persist", -1).cmds
             /\ steps' = steps + 1 /\ UNCHANGED <<leaked, nh, primary>>

PersistRefused == /\ steps < 5
                  /\ \E k \in keys : ~k.per
                  /\ \E f \in 0..1 : (f = 1 => FlushCanFail) /\ op' = <<"persist", f>> /\ log' = ProgramOf("persist", f).cmds
                  /\ steps' = steps + 1 /\ UNCHANGED <<tpm, keys, leaked, nh, primary>>

PersistOp == PersistOk \/ PersistRefused

UnsealOp == /\ primary # 0 /\ steps < 5
            /\ \E f \in -1..1, fo \in FlushOk :
                 /\ op' = <<"unseal", f>>
                 /\ IF f = 0 THEN /\ log' = <<Bad("load")>> /\ UNCHANGED <<tpm, leaked>> /\ nh' = nh
                    ELSE /\ log' = <<Ok("load"), IF f = -1 THEN Ok("unseal") ELSE Bad("unseal"), <<"flush", fo>>>>
                         /\ tpm' = IF fo THEN tpm ELSE tpm \cup {nh}
                         /\ leaked' = IF fo THEN leaked ELSE leaked \cup {nh}
                         /\ nh' = nh + 1
            /\ steps' = steps + 1 /\ UNCHANGED <<primary, keys>>

SignOp == /\ steps < 5 /\ \E f \in {-1, 0} : op' = <<"sign", f>> /\ log' = ProgramOf("sign", f).cmds
          /\ steps' = steps + 1 /\ UNCHANGED <<tpm, primary, keys, leaked, nh>>

Next == OpenOp \/ GenerateOp \/ PersistOp \/ UnsealOp \/ SignOp
Spec == Init /\ [][Next]_vars

NoLeak == tpm = Tracked
LeakAccounted == tpm = Tracked \cup leaked /\ leaked \cap Tracked = {}
PersistentNotTransient == \A k \in keys : k.per => k.h \notin tpm

(* the commands of the last operation are the table's for the failure point it chose (a refused or accepted flush
   after a failed readPublic or unseal is the same program with the flush's own outcome) *)
ProgramShape ==
    /\ op[1] \in {"open", "persist", "sign"} => log = ProgramOf(op[1], op[2]).cmds
    /\ op[1] = "unseal" =>
         \/ log = ProgramOf("unseal", op[2]).cmds
         \/ \E fo \in BOOLEAN : log = <<Ok("load"), IF op[2] = -1 THEN Ok("unseal") ELSE Bad("unseal"), <<"flush", fo>>>>
    /\ op[1] = "generate" =>
         \/ log = ProgramOf("generate", op[2]).cmds
         \/ \E fo \in BOOLEAN : log = <<Ok("create"), Ok("load"), Bad("readPublic"), <<"flush", fo>>>>

(* the handles the table says the operation adds, against the machine *)
TableBalances == \A o \in {"open", "generate", "loadPersistent", "persist", "sign", "seal", "unseal"} : \A f \in -1..2 :
    Net(ProgramOf(o, f).cmds) = ProgramOf(o, f).d

(* a handle leaks only when a flush the code sent was refused *)
LeakOnlyByRefusedFlush ==
    [][leaked' # leaked => \E i \in 1..Len(log') : log'[i] = <<"flush", FALSE>>]_vars

(* ---- pure rules ---- *)
ResponseRules ==
    /\ \A n \in 10..11 : \A sz \in {n - 1, n, n + 1} : \A cd \in {0, 256} : \A bo \in BOOLEAN :
          LET rsp == [i \in 1..n |-> IF i = 6 THEN sz ELSE IF i = 9 THEN cd \div 256 ELSE IF i = 10 THEN cd % 256 ELSE 0]
              r == ParseResp(rsp, bo)
          IN /\ (sz # n => r.err = "Protocol")
             /\ (sz = n /\ cd # 0 => r.err = "Tpm" /\ r.code = <<0, 256>>)
             /\ (sz = n /\ cd = 0 => (r.err = "ok") = bo)
    /\ \A n \in 0..9 : ParseResp([i \in 1..n |-> 0], TRUE).err = "Protocol"

CommandRules ==
    /\ \A a, b \in Methods : CC[a] = CC[b] => a = b
    /\ \A m \in Methods : MethodOfCc(CC[m]) = m
    /\ \A n \in {0, 1, 32, 64} : AuthAreaSize(n) = 4 + 2 + 1 + 2 + n
    /\ \A m \in Methods : \A auth \in {<<>>, <<7>>, <<7, 8>>} :
          LET n == Len(auth)
              hdr == <<128, IF m \in SessionMethods THEN 2 ELSE 1>>
              body == [i \in 1..(4 * NHandles(m)) |-> 0]
              area == IF m \in SessionMethods
                      THEN <<0, 0>> \o <<0, AuthAreaSize(n)>> \o <<64, 0, 0, 9>> \o <<0, 0>> \o <<1>> \o <<0, n>> \o auth
                      ELSE <<>>
              len == 10 + Len(body) + Len(area)
              cmd == hdr \o <<0, 0, 0, len>> \o <<0, 0, CC[m] \div 256, CC[m] % 256>> \o body \o area
          IN /\ Canonical(m, auth, cmd)
             /\ ~Canonical(m, auth, [cmd EXCEPT ![2] = 3 - hdr[2]])
             /\ ~Canonical(m, auth, [cmd EXCEPT ![6] = len + 1])

UnsealOrder ==
    \A p, a \in BOOLEAN : \A l, u, f \in {Zero2, <<0, 1>>, <<0, 2>>} : \A d \in {31, 32} :
        LET r == UnsealResult(p, l, u, f, d, a)
        IN /\ (r.err = "ok") <=> (p /\ l = Zero2 /\ u = Zero2 /\ f = Zero2 /\ d = 32 /\ a)
           /\ (p /\ l # Zero2 => r = [err |-> "Tpm", code |-> l])
           /\ (p /\ l = Zero2 /\ u # Zero2 => r = [err |-> "Tpm", code |-> u])
           /\ (~p => r.err = "InvalidSealed")

HeaderRules ==
    /\ ~ParseHeader(<<>>, TRUE).ok /\ ~ParseHeader(<<1, 0, 0, 0, 0>>, TRUE).ok /\ ~ParseHeader(<<3, 0, 0, 0, 0>>, TRUE).ok
    /\ ParseHeader(<<2, 0, 1, 7, 0, 1, 8>>, TRUE) = [ok |-> TRUE, hdr |-> 7]
    /\ ~ParseHeader(<<2, 0, 1, 7, 0, 1, 8>>, FALSE).ok
    /\ ~ParseHeader(<<2, 0, 5, 7>>, TRUE).ok /\ ~ParseHeader(<<2, 0, 1, 7, 0, 3, 8>>, TRUE).ok
    /\ ~ParseHeader(<<2, 0>>, TRUE).ok /\ ~ParseHeader(<<2>>, TRUE).ok

RangeRule ==
    /\ Persistent(<<33024, 0>>) /\ Persistent(<<33279, 65535>>)
    /\ ~Persistent(<<33023, 65535>>) /\ ~Persistent(<<33280, 0>>) /\ ~Persistent(<<0, 0>>)

AuthRule == MaxAuth = 64
=============================================================================
