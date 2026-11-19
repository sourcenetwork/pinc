--------------------------- MODULE TraceTranscript ---------------------------
(***************************************************************************)
(* Trace validation of the order of the fields every transcript absorbs.   *)
(*                                                                         *)
(* The Rust test tests/trace_transcript.rs arms the test-only record of     *)
(* pinc-crypto's Transcript and drives every kind of transcript of the     *)
(* workspace through the public API. Each snapshot of a transcript is one  *)
(* line of transcript.ndjson: its label and, for each field absorbed so    *)
(* far, the tag the call site gave the field and its length, in the order  *)
(* of the absorb calls.                                                    *)
(*                                                                         *)
(* This module holds the field list of each kind (the lists of             *)
(* Transcript.tla and proofs/lean/Pinc/Transcript.lean, with the tag of    *)
(* each field and the length it may have) and requires each recorded line  *)
(* to be a prefix of the list of its label, field by field: the tag and    *)
(* the length of the k-th absorb must be the k-th field's. A transcript    *)
(* that absorbs two fields in the other order, leaves one out, adds one,   *)
(* or gives a field a length it cannot have, is not a behaviour of this     *)
(* module. Every kind must also be seen in full at least once, so that no  *)
(* field of any list goes unchecked.                                       *)
(*                                                                         *)
(* What this does not show: the tag is the call site's claim about the     *)
(* bytes it absorbs. The lengths pin down the fields of different sizes;   *)
(* what the bytes of a field are is covered by the handshake traces, whose *)
(* term and id bijection binds every field of every transcript. The record *)
(* layer and the credit record absorb nothing into a transcript.           *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds transcript.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES i, full
vars == <<i, full>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/transcript.ndjson")

L == INSTANCE Labels WITH x <- i

(* a field of exactly n bytes, and a field of lo to hi bytes *)
Fx(t, n) == [tag |-> t, lo |-> n, hi |-> n]
Vr(t, lo, hi) == [tag |-> t, lo |-> lo, hi |-> hi]

(* the bounds of the variable-length fields: connection ids (ids.rs MAX_CID_LEN), ALPNs (MAX_ALPN_LEN), public keys
   (32 for Ed25519 to 1984 for the hybrid identity), signatures (64 to 3373), the tickets of a resume Reply
   (TicketBatch::encode, at most 81 bytes), and a field of the callers that take any slice *)
Cid(t) == Vr(t, 0, 20)
Alpn(t) == Vr(t, 1, 32)
IdKey == Vr("id_key", 32, 1984)
Sig == Vr("sig", 64, 3373)
AnyLen == 1000000

(* the security labels (labels.rs; checked against Labels.tla below) *)
HsL == "PINC 2026 v1 handshake"
ResumeL == "PINC 2026 v1 resume handshake"
ChainL == "PINC 2026 v1 chain"
PrekeyHashL == "PINC 2026 v1 prekey hash"
TicketL == "PINC 2026 v1 ticket"
SubCtxL == "PINC 2026 v1 sub session context"
RollIdL == "PINC 2026 v1 key roll id"
(* the delay-tolerant delivery labels (pinc-dtn labels.rs) *)
DtnChainL == "PINC 2026 v1 dtn chain"
DtnTranscriptL == "PINC 2026 v1 dtn transcript"
DtnBundleIdL == "PINC 2026 v1 dtn bundle id"
DtnHeadL == "PINC 2026 v1 dtn head"
DtnAckL == "PINC 2026 v1 dtn custody ack"

ASSUME {HsL, ResumeL, ChainL, PrekeyHashL, TicketL, SubCtxL, RollIdL} \subseteq {L!AllLabels[k] : k \in DOMAIN L!AllLabels}

(* initial_transcript: the label (22 bytes) is also the first field *)
InitialF == <<Fx("label", 22), Fx("version", 1), Alpn("alpn"), Cid("dcid"), Cid("scid"), Fx("credit", 6),
              Fx("offer", 1), Fx("e", 32), Fx("prekey_hash", 32)>>
(* absorb_reply, absorb_identity and absorb_credit of the responder, its signature, the initiator's identity and its
   signature: the rest of the full handshake *)
FullF == InitialF \o <<Cid("r_scid"), Fx("aead", 1), Fx("r_e", 32), Fx("ct", 1088),
                       Fx("id_alg", 1), IdKey, Fx("r_credit", 6), Sig, Fx("id_alg", 1), IdKey, Sig>>
(* hello_transcript, absorb_resume_reply and the tickets of the confirmation; the label is 29 bytes *)
ResumeF == <<Fx("label", 29), Fx("version", 1), Alpn("alpn"), Cid("dcid"), Cid("scid"), Fx("aead", 1),
             Fx("tid", 16), Fx("e", 32), Fx("credit", 6),
             Fx("binder", 32), Cid("r_scid"), Fx("r_e", 32), Fx("r_credit", 6), Vr("tickets", 0, 81)>>

Specs ==   (HsL :> FullF)
       @@ (ResumeL :> ResumeF)
       @@ (TicketL :> <<Fx("tid", 16), Fx("credit", 6)>>)
       @@ (SubCtxL :> <<Vr("alpn", 0, AnyLen), Vr("cc", 0, AnyLen), Vr("cs", 0, AnyLen)>>)
       @@ (RollIdL :> <<Fx("share", 32)>>)
       @@ (PrekeyHashL :> <<Fx("encaps_key", 1184)>>)
       @@ (ChainL :> <<>>)
       @@ (DtnChainL :> <<>>)
       @@ (DtnBundleIdL :> <<Fx("node_alg", 1), Fx("node_key", 32), Fx("wall", 8), Fx("counter", 4), Fx("eph", 32)>>)
       @@ (DtnTranscriptL :> <<Fx("eph", 32), Fx("x25519", 32), Fx("kem_ek", 1184), Fx("kem_ct", 1088),
                               Fx("node_alg", 1), Fx("node_key", 32), Fx("epoch", 4), Fx("id", 32)>>)
       @@ (DtnHeadL :> <<Vr("body", 0, AnyLen)>>)
       @@ (DtnAckL :> <<Vr("body", 0, AnyLen)>>)

Kinds == DOMAIN Specs

(* the recorded fields are the first Len(fs) fields of the list, tag and length *)
Prefix(spec, fs) ==
    /\ Len(fs) <= Len(spec)
    /\ \A k \in DOMAIN fs :
         /\ fs[k][1] = spec[k].tag
         /\ fs[k][2] >= spec[k].lo
         /\ fs[k][2] <= spec[k].hi

Init ==
    /\ i = 1
    /\ full = {}

Check ==
    /\ i <= Len(Trace)
    /\ LET ev == Trace[i] IN
       /\ ev.t = "tr"
       /\ ev.label \in Kinds
       /\ Prefix(Specs[ev.label], ev.fields)
       /\ full' = IF Len(ev.fields) = Len(Specs[ev.label]) THEN full \cup {ev.label} ELSE full
    /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

Next == Check \/ Done

TraceSpec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* the whole recorded trace is a behaviour of the field lists *)
TraceAccepted == <>(i = Len(Trace) + 1)

(* every kind was seen with all its fields *)
Covered == i > Len(Trace) => full = Kinds
=============================================================================
