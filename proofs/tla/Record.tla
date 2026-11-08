------------------------------- MODULE Record -------------------------------
(***************************************************************************)
(* Model of the packet key of vinc-security record.rs (PacketKey): key     *)
(* generations, the sealed and failed-open counters and their limits.      *)
(*                                                                         *)
(* A generation's key is derived from the previous secret only, so two     *)
(* generations never share a key (a stated assumption of the key           *)
(* derivation: the key of generation g is the term <<"key", g>>). The      *)
(* nonce of packet number pn under a key is iv XOR pn, injective in pn;    *)
(* it is the term <<g, pn>>. The caller numbers packets strictly           *)
(* increasing, also across generations (the key itself does not track      *)
(* it), and a packet number is at most MaxPn (the code's 2^62 - 1).        *)
(* The limits are small constants here (AesLimit stands for 2^22,          *)
(* ChachaLimit for 2^36, MaxGen for 2^32 - 1).                             *)
(*                                                                         *)
(* Checked: no (key, nonce) pair is used twice by seal, whatever the       *)
(* sequence of seals, failed opens and key updates; the sealed counter of  *)
(* an AES-GCM key never exceeds its limit and the key then refuses to seal *)
(* until it is updated; the failed-open counter of a ChaCha20-Poly1305 key *)
(* never exceeds its limit and the key then refuses to open; a refusal     *)
(* changes nothing; the generation never exceeds MaxGen and an update past *)
(* it is refused.                                                          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxPn, AesLimit, ChachaLimit, MaxGen, Aead   \* Aead is "aes" or "chacha"

VARIABLES gen, sealed, failed, last, log
vars == <<gen, sealed, failed, last, log>>

Key(g) == <<"key", g>>
Nonce(g, pn) == <<"nonce", g, pn>>

Init == gen = 0 /\ sealed = 0 /\ failed = 0 /\ last = -1 /\ log = <<>>

(* PacketKey::seal with packet number pn; a refusal leaves the key unchanged *)
Seal(pn) ==
    /\ pn > last
    /\ IF pn > MaxPn \/ (Aead = "aes" /\ sealed >= AesLimit)
       THEN UNCHANGED vars
       ELSE /\ sealed' = sealed + 1
            /\ last' = pn
            /\ log' = Append(log, <<Key(gen), Nonce(gen, pn)>>)
            /\ UNCHANGED <<gen, failed>>

(* PacketKey::open of a packet that fails authentication *)
OpenFails ==
    IF Aead = "chacha" /\ failed >= ChachaLimit THEN UNCHANGED vars
    ELSE /\ failed' = IF failed > ChachaLimit THEN failed ELSE failed + 1   \* saturates
         /\ UNCHANGED <<gen, sealed, last, log>>

(* PacketKey::next_generation *)
Update ==
    IF gen >= MaxGen THEN UNCHANGED vars
    ELSE /\ gen' = gen + 1
         /\ sealed' = 0
         /\ failed' = 0
         /\ UNCHANGED <<last, log>>

Next == (\E pn \in 0..(MaxPn + 1) : Seal(pn)) \/ OpenFails \/ Update

Spec == Init /\ [][Next]_vars

NoNonceReuse == \A i, j \in 1..Len(log) : i # j => log[i] # log[j]
AesBounded == Aead = "aes" => sealed <= AesLimit
FailedBounded == failed <= ChachaLimit + 1 /\ (Aead = "chacha" => failed <= ChachaLimit)
GenBounded == gen <= MaxGen

(* the limits fire: a key at its sealing limit seals nothing more, and the counter only grows or resets with a new generation *)
LimitFires == [][(Aead = "aes" /\ sealed >= AesLimit) => (sealed' = sealed \/ gen' = gen + 1)]_vars
(* a refused seal or open changes nothing, so a key at a limit stays at it until updated *)
FailedMonotone == [][failed' >= failed \/ gen' = gen + 1]_vars
=============================================================================
