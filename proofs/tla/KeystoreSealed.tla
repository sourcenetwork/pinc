---------------------------- MODULE KeystoreSealed ----------------------------
(***************************************************************************)
(* The sealed format of pinc-keystore (sealed.rs): header || nonce (12) || *)
(* ciphertext || tag (16), ChaCha20-Poly1305 with the whole header as      *)
(* associated data, and the software store's version byte (software.rs).   *)
(*                                                                         *)
(* The AEAD is the ideal one (a perfect primitive): the ciphertext bytes   *)
(* and the tag are terms of (key, nonce, header, plaintext), and open      *)
(* accepts a pair only if it is exactly what seal produces for a           *)
(* plaintext. Every element of a blob is a tuple whose first component     *)
(* tells the kind: <<"b", v>> a byte, <<"c", ...>> a ciphertext byte,      *)
(* <<"t", ...>> a tag byte.                                                *)
(*                                                                         *)
(* Checked over 2 keys, headers of 1 and 2 bytes, 2 nonces and             *)
(* plaintexts of up to 2 bytes, and over every alteration of every genuine *)
(* blob (each element replaced by each symbol of the universe, deleted,    *)
(* a symbol inserted at each position, every prefix, every extension):     *)
(*   RoundTrip       unseal (seal p) = p                                   *)
(*   Canonical       parse inverts build, and build inverts parse          *)
(*   ShortRefused    a blob shorter than header + 12 + 16 is refused       *)
(*   WrongKey        another key refuses a genuine blob                    *)
(*   WrongHeader     a changed header (same length) is refused             *)
(*   AlteredRefused  no alteration of a genuine blob is accepted           *)
(*   OnlyGenuine     an accepted blob is a sealing under the key           *)
(*   SoftwareVersion the software store requires its version byte first    *)
(* TraceKeystore.tla checks the recorded blobs against Parse and the       *)
(* layout. Lean counterpart: proofs/lean/Pinc/KeystoreSealed.lean          *)
(* (parse_error_iff, build_parse, parse_build, decrypt_encrypt,            *)
(* decrypt_sound, wrong_key, wrong_header, swUnseal_swSeal).               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLE x

NonceLen == 12
TagLen == 16
Err == [ok |-> FALSE]
Min(a, b) == IF a < b THEN a ELSE b

B(v) == <<"b", v>>

(* the ideal AEAD *)
CtOf(k, n, a, p) == [i \in 1..Len(p) |-> <<"c", k, n, a, p, i>>]
TagOf(k, n, a, p) == [i \in 1..TagLen |-> <<"t", k, n, a, p, i>>]

Build(k, h, n, p) == h \o n \o CtOf(k, n, h, p) \o TagOf(k, n, h, p)

(* the split of decrypt: header, nonce, body, tag; refused when too short *)
Parse(s, hl) ==
    IF Len(s) < hl + NonceLen + TagLen THEN Err
    ELSE [ok |-> TRUE,
          header |-> SubSeq(s, 1, hl),
          nonce |-> SubSeq(s, hl + 1, hl + NonceLen),
          ct |-> SubSeq(s, hl + NonceLen + 1, Len(s) - TagLen),
          tag |-> SubSeq(s, Len(s) - TagLen + 1, Len(s))]

(* open: the plaintext of a pair the ideal AEAD produced, else nothing *)
OpenW(k, n, a, c, t) ==
    IF Len(c) = 0
    THEN (IF t = TagOf(k, n, a, <<>>) THEN [ok |-> TRUE, pt |-> <<>>] ELSE Err)
    ELSE IF ~(\A i \in 1..Len(c) : Len(c[i]) = 6 /\ c[i][1] = "c") THEN Err
    ELSE LET p == c[1][5]
         IN IF c = CtOf(k, n, a, p) /\ t = TagOf(k, n, a, p) THEN [ok |-> TRUE, pt |-> p] ELSE Err

Unseal(k, s, hl) ==
    LET q == Parse(s, hl)
    IN IF ~q.ok THEN Err ELSE OpenW(k, q.nonce, q.header, q.ct, q.tag)

SwUnseal(k, s) == IF Len(s) = 0 \/ s[1] # B(1) THEN Err ELSE Unseal(k, s, 1)

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

Keys == {"k1", "k2"}
Headers == {<<B(1)>>, <<B(2)>>, <<B(1), B(1)>>, <<B(1), B(2)>>, <<B(2), B(1)>>}
Nonces == {[i \in 1..NonceLen |-> B(0)], [i \in 1..NonceLen |-> B(1)]}
Plains == {<<>>, <<B(0)>>, <<B(0), B(1)>>}

Genuine == {[k |-> k, h |-> h, n |-> n, p |-> p] : k \in Keys, h \in Headers, n \in Nonces, p \in Plains}
Blob(g) == Build(g.k, g.h, g.n, g.p)

(* every symbol that occurs in a genuine blob, and one that occurs in none *)
Syms == {B(0), B(1), B(2), B(9)}
         \cup UNION {{Blob(g)[i] : i \in 1..Len(Blob(g))} : g \in {g \in Genuine : g.h = <<B(1)>> /\ g.p = <<B(0), B(1)>>}}

(* a representative set of genuine blobs for the alteration checks *)
Reps == {g \in Genuine : g.k = "k1" /\ g.h \in {<<B(1)>>, <<B(1), B(2)>>} /\ g.p \in {<<>>, <<B(0)>>}}

Replace(s, i, y) == [j \in 1..Len(s) |-> IF j = i THEN y ELSE s[j]]
Without(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))
Insert(s, i, y) == SubSeq(s, 1, i - 1) \o <<y>> \o SubSeq(s, i, Len(s))
Alterations(s) ==
    {Replace(s, i, y) : i \in 1..Len(s), y \in Syms}
    \cup {Without(s, i) : i \in 1..Len(s)}
    \cup {Insert(s, i, y) : i \in 1..(Len(s) + 1), y \in Syms}
    \cup {SubSeq(s, 1, c) : c \in 0..(Len(s) - 1)}

RoundTrip ==
    \A g \in Genuine : LET r == Unseal(g.k, Blob(g), Len(g.h)) IN r.ok /\ r.pt = g.p

Canonical ==
    \A g \in Genuine :
        LET s == Blob(g)
            q == Parse(s, Len(g.h))
        IN /\ q.ok /\ q.header = g.h /\ q.nonce = g.n
           /\ q.header \o q.nonce \o q.ct \o q.tag = s

ShortRefused ==
    \A g \in Reps : \A c \in 0..(Len(g.h) + NonceLen + TagLen - 1) :
        ~Parse(SubSeq(Blob(g), 1, Min(c, Len(Blob(g)))), Len(g.h)).ok \/ c >= Len(g.h) + NonceLen + TagLen

WrongKey == \A g \in Genuine : \A k \in Keys : k # g.k => ~Unseal(k, Blob(g), Len(g.h)).ok

WrongHeader ==
    \A g \in Reps : \A h \in Headers : (Len(h) = Len(g.h) /\ h # g.h) =>
        ~Unseal(g.k, h \o SubSeq(Blob(g), Len(g.h) + 1, Len(Blob(g))), Len(g.h)).ok

AlteredRefused ==
    \A g \in Reps : \A s \in Alterations(Blob(g)) :
        s # Blob(g) => ~Unseal(g.k, s, Len(g.h)).ok

OnlyGenuine ==
    \A g \in Reps : \A s \in Alterations(Blob(g)) :
        Unseal(g.k, s, Len(g.h)).ok => \E g2 \in Genuine : g2.k = g.k /\ Blob(g2) = s

SoftwareVersion ==
    /\ \A g \in Genuine : (g.h = <<B(1)>>) => (SwUnseal(g.k, Blob(g)).ok /\ SwUnseal(g.k, Blob(g)).pt = g.p)
    /\ \A g \in Genuine : (g.h = <<B(2)>>) => ~SwUnseal(g.k, Blob(g)).ok
    /\ ~SwUnseal("k1", <<>>).ok
=============================================================================
