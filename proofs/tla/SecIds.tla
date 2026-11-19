-------------------------------- MODULE SecIds --------------------------------
(***************************************************************************)
(* The identifiers and parameters of pinc-security ids.rs: ConnId::new and *)
(* as_bytes, Alpn::new and as_bytes, AlpnList::new and find, aead_tag and  *)
(* aead_from_tag, AeadSet (offer, from_bits, bits, contains, choose) and   *)
(* LocalIdentity::new with its accessors. A ConnId or an Alpn is its       *)
(* visible bytes: the doc says the unused tail is kept zero "so equality   *)
(* is equality of the visible bytes", which the trace check tests on the   *)
(* code (TraceSecIds.tla). An AEAD is its wire tag (1 ChaCha20-Poly1305, 2 *)
(* AES-128-GCM) and a set its wire bits; a refusal (None or an error) is   *)
(* 0 for a number and [ok |-> FALSE] for a value.                          *)
(*                                                                         *)
(* Checked over every byte value, every length from 0 to 40 and 255, 256   *)
(* (the u8 bound of the stored length), and every pair of sets:            *)
(*  - CidRange, AlpnRange: accepted exactly at 0..MAX_CID_LEN (20) and     *)
(*    1..MAX_ALPN_LEN (32) bytes, and as_bytes gives the bytes back;       *)
(*  - ListRule: AlpnList::new accepts 1 to MAX_ALPNS (9) valid ALPNs and   *)
(*    nothing else; find answers an ALPN of the list equal to the one      *)
(*    wanted, and nothing when none is;                                    *)
(*  - TagRoundTrip: aead_from_tag accepts 1 and 2 only and aead_tag gives  *)
(*    the tag back;                                                        *)
(*  - SetRule: from_bits accepts 1..3 only (never empty, no unknown bit),  *)
(*    bits gives them back, contains is the bit of the tag, the offer is   *)
(*    {ChaCha} or {ChaCha, AES} and always holds ChaCha;                   *)
(*  - ChooseRule: choose answers an AEAD in both sets, AES-128-GCM when    *)
(*    both hold it, and nothing exactly when they share none; symmetric;   *)
(*  - IdentRule: LocalIdentity::new accepts a public key of exactly the    *)
(*    length of its algorithm (32, 33, 1952, 1984) and nothing else, and   *)
(*    public_key, alg and key give back what it was made of (checked on    *)
(*    the code by TraceSecIds.tla, with the node id of an Ed25519 key      *)
(*    being the key itself).                                               *)
(* Not modelled: the node id of the other algorithms (a BLAKE3 derive_key, *)
(* an ideal primitive); the trace test compares it with NodeId::           *)
(* from_public of pinc-crypto.                                             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

P == INSTANCE Padding WITH x <- 0

MaxCid == P!MaxCid
MaxAlpn == 32
MaxAlpns == 9

None == [ok |-> FALSE]
Some(v) == [ok |-> TRUE, v |-> v]

\* ConnId::new and as_bytes: u8::try_from of the length, then at most MAX_CID_LEN
CidNew(b) == IF Len(b) <= 255 /\ Len(b) <= MaxCid THEN Some(b) ELSE None
\* Alpn::new and as_bytes
AlpnNew(b) == IF Len(b) <= 255 /\ Len(b) >= 1 /\ Len(b) <= MaxAlpn THEN Some(b) ELSE None
\* AlpnList::new: the count, then every item valid
ListNew(l) == Len(l) >= 1 /\ Len(l) <= MaxAlpns /\ \A i \in 1..Len(l) : AlpnNew(l[i]).ok
\* AlpnList::find on a list that new accepted: the first item equal to wanted
ListFind(l, w) == IF \E i \in 1..Len(l) : l[i] = w THEN Some(w) ELSE None

\* aead_from_tag then aead_tag; 0 for None
FromTag(t) == IF t \in 1..2 THEN t ELSE 0
\* AeadSet::from_bits then bits; 0 for None
FromBits(b) == IF b = 0 \/ b > 3 THEN 0 ELSE b
\* AeadSet::contains: bits & tag != 0, for a tag of 1 or 2
Has(s, t) == (s \div t) % 2 = 1
\* AeadSet::choose: the tag, 0 for None
Choose(a, b) == IF Has(a, 2) /\ Has(b, 2) THEN 2 ELSE IF Has(a, 1) /\ Has(b, 1) THEN 1 ELSE 0
\* AeadSet::offer
Offer(hw) == IF hw THEN 3 ELSE 1

\* LocalIdentity::new(alg, public_key, key): NodeId::from_public checks the length first
IdentNew(alg, pk) == Len(pk) = P!Pk[alg]

VARIABLE x
Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

Pat(n, s) == [i \in 1..n |-> (i * s + 3) % 256]
Lens == (0..40) \cup {255, 256}
A(n) == Pat(n, 7)

CidRange == \A n \in Lens : LET r == CidNew(Pat(n, 5)) IN (r.ok <=> n <= MaxCid) /\ (r.ok => r.v = Pat(n, 5))
AlpnRange == \A n \in Lens : LET r == AlpnNew(A(n)) IN (r.ok <=> n \in 1..MaxAlpn) /\ (r.ok => r.v = A(n))

Lists == {[i \in 1..n |-> A(1 + i % 3)] : n \in 0..11}
         \cup {[i \in 1..n |-> IF i = j THEN A(bad) ELSE A(1 + i % 3)] : n \in 1..9, j \in 1..9, bad \in {0, 33}}
Wanted == {A(1), A(2), A(3), A(32), <<>>, A(33)}
ListRule ==
    \A l \in Lists :
        /\ ListNew(l) <=> (Len(l) \in 1..MaxAlpns /\ \A i \in 1..Len(l) : Len(l[i]) \in 1..MaxAlpn)
        /\ ListNew(l) => \A w \in Wanted :
              LET f == ListFind(l, w) IN (f.ok => \E i \in 1..Len(l) : l[i] = f.v /\ f.v = w) /\ (~f.ok => \A i \in 1..Len(l) : l[i] # w)

TagRoundTrip == /\ \A t \in 0..255 : FromTag(t) # 0 <=> t \in {1, 2}
                /\ \A t \in {1, 2} : FromTag(t) = t

Sets == 1..3
SetRule == /\ \A b \in 0..255 : FromBits(b) # 0 <=> b \in Sets
           /\ \A b \in Sets : FromBits(b) = b
           /\ \A b \in Sets : \A t \in {1, 2} : Has(b, t) <=> (t = 1 /\ b \in {1, 3}) \/ (t = 2 /\ b \in {2, 3})
           /\ \A hw \in BOOLEAN : Offer(hw) \in Sets /\ Has(Offer(hw), 1) /\ (Has(Offer(hw), 2) <=> hw)
ChooseRule == \A a, b \in Sets :
                  /\ Choose(a, b) = Choose(b, a)
                  /\ Choose(a, b) # 0 => Has(a, Choose(a, b)) /\ Has(b, Choose(a, b))
                  /\ (Has(a, 2) /\ Has(b, 2)) => Choose(a, b) = 2
                  /\ Choose(a, b) = 0 <=> ~\E t \in {1, 2} : Has(a, t) /\ Has(b, t)

KeyLens(a) == {0, 1, 31, 32, 33, 34, 1951, 1952, 1953, 1984, 1985, P!Pk[a] - 1, P!Pk[a], P!Pk[a] + 1}
IdentRule == \A a \in 1..4 : \A n \in KeyLens(a) : IdentNew(a, Pat(n, 11)) <=> n = P!Pk[a]
=============================================================================
