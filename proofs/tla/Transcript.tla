----------------------------- MODULE Transcript -----------------------------
(***************************************************************************)
(* The transcript encoding of vinc-crypto Transcript::absorb and the field *)
(* lists of vinc-security schedule.rs.                                     *)
(*                                                                         *)
(* absorb writes a field as its varint length followed by its bytes, and a *)
(* transcript hashes the concatenation. The hash cannot tell two lists     *)
(* apart whose encodings are equal, so the encoding must be injective.     *)
(*                                                                         *)
(* SCALING. TLC cannot enumerate real fields (up to 1184 bytes over 256    *)
(* byte values). The model keeps the structure and shrinks the sizes:      *)
(* bytes come from a small Alphabet, fields have at most MaxLen bytes, and *)
(* the varint of a length below 128 is that one byte (all the scaled       *)
(* lengths are), so Absorb(f) = <<Len(f)>> \o f. The length byte lives in  *)
(* the same alphabet as the data, as in the code. Multi-byte varints are   *)
(* covered by Varint.tla and proofs/lean/Vinc/Varint.lean, and the         *)
(* injectivity for fields of any length by Transcript.lean                 *)
(* (encode_injective).                                                     *)
(*                                                                         *)
(* Checked, exhaustively at that scale:                                    *)
(*  - the encoding is injective on every list of up to 3 fields (pairwise)  *)
(*    and on every list of up to MaxFields fields (the image has as many   *)
(*    elements as there are lists);                                        *)
(*  - the Initial list [label, version, alpn, dcid, scid, credit, offer, e, *)
(*    prekey hash] determines each of its arguments separately, and so do  *)
(*    the resume Hello list [label, version, alpn, dcid, scid, aead, tid, e,*)
(*    credit], the full-handshake list (the Initial list followed by the    *)
(*    reply, the responder identity, credit and signature, the initiator    *)
(*    identity and signature) and the resumption list (the Hello list       *)
(*    followed by binder, scid, e, credit, tickets): the number of distinct *)
(*    encodings equals the number of argument tuples; every argument that   *)
(*    is a variable-length field ranges over lengths 0 to 2, so a split of  *)
(*    bytes between two neighbouring fields is exercised;                   *)
(*  - an Initial list and a Hello list never have the same encoding, and a  *)
(*    full-handshake list and a resumption list never do (the label; checked *)
(*    also for every tail of up to 3 fields under the two labels);          *)
(*  - the identity and credit absorb [alg, key, credit] and the ticket      *)
(*    context [tid, credit] are injective.                                  *)
(*                                                                         *)
(* The labels are two distinct constants of the same length here (the real *)
(* labels differ in length), which is the harder case for the encoding.    *)
(* Lean counterpart: proofs/lean/Vinc/Transcript.lean.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Alphabet, MaxLen, MaxFields
VARIABLE x

Absorb(f) == <<Len(f)>> \o f

RECURSIVE Encode(_)
Encode(fs) == IF fs = <<>> THEN <<>> ELSE Absorb(Head(fs)) \o Encode(Tail(fs))

Fields == UNION {[1..n -> Alphabet] : n \in 0..MaxLen}
Lists(m) == UNION {[1..n -> Fields] : n \in 0..m}

HsLabel == <<1, 0, 1>>
ResumeLabel == <<1, 1, 0>>

(* the small domains of the arguments: a byte, a variable-length field, a fixed-length credit record *)
Byte == {0, 1}
Var == {<<>>, <<0>>, <<1>>, <<0, 1>>}
Var2 == {<<>>, <<0>>}
Cred == {<<0, 0>>, <<1, 1>>}
Cred1 == {<<0, 0>>}

(* initial_transcript *)
InitialL(v, al, dc, sc, cr, of, e, h) == <<HsLabel, <<v>>, al, dc, sc, cr, <<of>>, e, h>>
(* hello_transcript *)
HelloL(v, al, dc, sc, ae, ti, e, cr) == <<ResumeLabel, <<v>>, al, dc, sc, <<ae>>, ti, e, cr>>
(* the rest of a full handshake *)
ReplyL(sc, ae, e, ct, ra, rk, rc, rs, ia, ik, is) == <<sc, <<ae>>, e, ct, <<ra>>, rk, rc, rs, <<ia>>, ik, is>>
(* absorb_resume_reply and the tickets *)
ResumeL(bi, sc, e, cr, tk) == <<bi, sc, e, cr, tk>>

InitialImage == {Encode(InitialL(v, al, dc, sc, cr, of, e, h)) :
                    v \in Byte, al \in Var, dc \in Var, sc \in Var, cr \in Cred, of \in Byte, e \in Var, h \in Var}
InitialCount == 2 * 4 * 4 * 4 * 2 * 2 * 4 * 4

HelloImage == {Encode(HelloL(v, al, dc, sc, ae, ti, e, cr)) :
                  v \in Byte, al \in Var, dc \in Var, sc \in Var, ae \in Byte, ti \in Var, e \in Var, cr \in Cred}
HelloCount == 2 * 4 * 4 * 4 * 2 * 4 * 4 * 2

FullImage == {Encode(InitialL(v, al, <<>>, <<0>>, <<0, 0>>, 0, <<1>>, h) \o ReplyL(s2, ae, e2, ct, ra, rk, rc, rs, ia, ik, is)) :
                 v \in Byte, al \in Var2, h \in Var2,
                 s2 \in Var2, ae \in Byte, e2 \in Var2, ct \in Var2, ra \in Byte, rk \in Var2, rc \in Cred,
                 rs \in Var2, ia \in Byte, ik \in Var2, is \in Var2}
FullCount == 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2

ResumeImage == {Encode(HelloL(v, al, <<0>>, <<>>, ae, ti, <<1>>, <<0, 0>>) \o ResumeL(bi, s2, e2, cr2, tk)) :
                   v \in Byte, al \in Var2, ae \in Byte, ti \in Var2,
                   bi \in Var2, s2 \in Var2, e2 \in Var2, cr2 \in Cred, tk \in Var2}
ResumeCount == 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2

IdCredImage == {Encode(<<<<a>>, k, c>>) : a \in Byte, k \in Var, c \in Cred}
TicketCtxImage == {Encode(<<t, c>>) : t \in Var, c \in Cred}

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

InjectiveSmall == \A l1, l2 \in Lists(3) : Encode(l1) = Encode(l2) => l1 = l2
InjectiveImage == Cardinality({Encode(l) : l \in Lists(MaxFields)}) = Cardinality(Lists(MaxFields))
InitialRecovered == Cardinality(InitialImage) = InitialCount
HelloRecovered == Cardinality(HelloImage) = HelloCount
FullRecovered == Cardinality(FullImage) = FullCount
ResumeRecovered == Cardinality(ResumeImage) = ResumeCount
InitialNeHello == InitialImage \cap HelloImage = {}
FullNeResume == FullImage \cap ResumeImage = {}
(* the label separates: the same remaining fields under the two labels never encode alike (the Initial and full
   lists start with the handshake label, the Hello and resumption lists with the resume label) *)
LabelSeparates == \A fs, gs \in Lists(3) : Encode(<<HsLabel>> \o fs) # Encode(<<ResumeLabel>> \o gs)
InitialNeResume == InitialImage \cap ResumeImage = {}
IdCredInjective == Cardinality(IdCredImage) = 2 * 4 * 2
TicketCtxInjective == Cardinality(TicketCtxImage) = 4 * 2
=============================================================================
