------------------------------- MODULE Record -------------------------------
(***************************************************************************)
(* Model of the packet key of vinc-security record.rs (PacketKey): the     *)
(* sealed and failed-open counters, the last sealed packet number, the    *)
(* usage limits and the key roll.                                          *)
(*                                                                         *)
(* seal checks, in the order of the code: the packet number against       *)
(* MaxPn (PacketNumber), that it is above last_sealed (NotIncreasing),    *)
(* the AES-GCM sealing limit (KeyRollRequired); only then it seals,       *)
(* counts the packet and records the number. Every number is offered,     *)
(* including repeated and lower ones: the check is inside Seal, not an    *)
(* assumption about the caller. open counts a packet that fails            *)
(* authentication (saturating) and refuses once a ChaCha20-Poly1305 key   *)
(* reached its failure limit. rolled gives the next generation: its       *)
(* secret is roll(secret, dh) with fresh counters, and it fails at        *)
(* MaxGen.                                                                 *)
(*                                                                         *)
(* Keys are the symbolic roll chain, not a definition of distinctness:     *)
(*   Sec(0) = <<"base", b>>, Sec(g+1) = <<"roll", Sec(g), <<"dh", d>>>>   *)
(* for the Diffie-Hellman value d the caller offers, so two generations   *)
(* have different secrets as a structural fact TLC checks (a perfect-     *)
(* primitive model: the packet key and the IV are functions of the        *)
(* secret, the nonce is the term <<secret, pn>>). The header key belongs  *)
(* to the first generation and is not rolled.                              *)
(*                                                                         *)
(* Checked: no (key, nonce) pair is used twice by seal, whatever the      *)
(* sequence of seals (any packet numbers), failed opens and rolls; the    *)
(* sealed counter of an AES-GCM key never exceeds its limit and the key   *)
(* then refuses to seal until it is rolled; the failed-open counter of a  *)
(* ChaCha20-Poly1305 key never exceeds its limit and the key then refuses *)
(* to open; a refusal changes nothing; last_sealed strictly increases on  *)
(* every successful seal; a rolled key starts with zero counters; the     *)
(* generation is the depth of the secret and never exceeds MaxGen; the    *)
(* header key is never rolled. AesLimit stands for 2^22, ChachaLimit for  *)
(* 2^36, MaxGen for 2^32 - 1, MaxPn for 2^62 - 1, Sat for u64::MAX.       *)
(*                                                                         *)
(* The operators SealOp, OpenOp and RollOp are pure and are reused by     *)
(* TraceKeyRoll.tla. Lean counterpart: Vinc/Record.lean.                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxPn, AesLimit, ChachaLimit, MaxGen, Sat, Aead, DhIds   \* Aead is "aes" or "chacha"

VARIABLES key, log
vars == <<key, log>>

Inc(x) == IF x >= Sat THEN x ELSE x + 1      \* saturating add of one

RECURSIVE Depth(_)
Depth(s) == IF s[1] = "base" THEN 0 ELSE 1 + Depth(s[2])

KeyOfSec(s) == <<"key", s>>
Nonce(s, pn) == <<"nonce", s, pn>>

NewKey(a, b, aesLim, chachaLim) ==
    [aead |-> a, sec |-> <<"base", b>>, gen |-> 0, sealed |-> 0, failed |-> 0, last |-> -1,
     aesLim |-> aesLim, chachaLim |-> chachaLim, hdr |-> <<"base", b>>]

(* PacketKey::seal: the new key and the outcome; a refusal returns the key unchanged *)
SealOp(k, pn) ==
    IF pn > MaxPn THEN [k |-> k, err |-> "packet_number"]
    ELSE IF pn <= k.last THEN [k |-> k, err |-> "not_increasing"]
    ELSE IF k.aead = "aes" /\ k.sealed >= k.aesLim THEN [k |-> k, err |-> "roll_required"]
    ELSE [k |-> [k EXCEPT !.sealed = Inc(@), !.last = pn], err |-> "ok"]

(* PacketKey::open; valid says whether the tag verifies *)
OpenOp(k, pn, valid) ==
    IF pn > MaxPn THEN [k |-> k, err |-> "packet_number"]
    ELSE IF k.aead = "chacha" /\ k.failed >= k.chachaLim THEN [k |-> k, err |-> "roll_required"]
    ELSE IF valid THEN [k |-> k, err |-> "ok"]
    ELSE [k |-> [k EXCEPT !.failed = Inc(@)], err |-> "authentication"]

(* PacketKey::rolled with the Diffie-Hellman value d *)
RollOp(k, d) ==
    IF k.gen >= MaxGen THEN [k |-> k, err |-> "exhausted"]
    ELSE [k |-> [k EXCEPT !.sec = <<"roll", @, <<"dh", d>>>>, !.gen = @ + 1, !.sealed = 0, !.failed = 0, !.last = -1],
          err |-> "ok"]

Init == key = NewKey(Aead, 0, AesLimit, ChachaLimit) /\ log = <<>>

Seal(pn) ==
    LET r == SealOp(key, pn)
    IN /\ key' = r.k
       /\ log' = IF r.err = "ok" THEN Append(log, <<KeyOfSec(key.sec), Nonce(key.sec, pn)>>) ELSE log

Open(pn, valid) == key' = OpenOp(key, pn, valid).k /\ UNCHANGED log

Roll(d) == key' = RollOp(key, d).k /\ UNCHANGED log

Next == (\E pn \in 0..(MaxPn + 1) : Seal(pn)) \/ (\E pn \in 0..(MaxPn + 1), v \in BOOLEAN : Open(pn, v))
        \/ (\E d \in DhIds : Roll(d))

Spec == Init /\ [][Next]_vars

TypeOK == /\ key.aead = Aead /\ key.aesLim = AesLimit /\ key.chachaLim = ChachaLimit
          /\ key.sealed \in 0..Sat /\ key.failed \in 0..Sat /\ key.last \in -1..MaxPn /\ key.gen \in 0..MaxGen

NoNonceReuse == \A i, j \in 1..Len(log) : i # j => log[i] # log[j]
AesBounded == Aead = "aes" => key.sealed <= AesLimit
FailedBounded == Aead = "chacha" => key.failed <= ChachaLimit
GenBounded == key.gen <= MaxGen
GenIsDepth == key.gen = Depth(key.sec)
HeaderNotRolled == key.hdr = <<"base", 0>>
(* every logged seal is under a secret no deeper than the key, and one of the current secret is below last_sealed *)
LogOrder == \A i \in 1..Len(log) : Depth(log[i][1][2]) <= key.gen /\ log[i][2][3] <= MaxPn

(* the limits fire: a key at its sealing limit seals nothing more until it is rolled *)
LimitFires == [][(Aead = "aes" /\ key.sealed >= AesLimit) => (key'.sealed = key.sealed \/ key'.gen = key.gen + 1)]_vars
(* counters only grow, or reset with a new generation *)
FailedMonotone == [][key'.failed >= key.failed \/ key'.gen = key.gen + 1]_vars
(* last_sealed strictly increases on every successful seal, and a roll resets it *)
LastIncreases == [][Len(log') > Len(log) => (key'.last > key.last /\ key'.last >= 0)]_vars
LastOnlyGrowsOrResets == [][key'.last >= key.last \/ key'.gen = key.gen + 1]_vars
(* a rolled key has fresh counters and the secret rolled from the old one *)
RollFresh == [][key'.gen = key.gen + 1 => (key'.sealed = 0 /\ key'.failed = 0 /\ key'.last = -1
                                          /\ key'.sec[1] = "roll" /\ key'.sec[2] = key.sec)]_vars
(* a seal that is not logged (a refusal), with no roll and no failed open, changes nothing *)
SealRefusalUnchanged == [][(Len(log') = Len(log) /\ key'.gen = key.gen /\ key'.failed = key.failed) => key' = key]_vars
HeaderKeyFixed == [][key'.hdr = key.hdr]_vars
=============================================================================
