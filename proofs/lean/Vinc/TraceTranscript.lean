import Vinc.Json
import Vinc.Labels
import Vinc.Transcript

/-!
# Replay of the transcript traces

The Lean half of the trace validation of the order of the fields every transcript absorbs; the port of
`proofs/tla/TraceTranscript.tla`. The Rust test `trace_transcript` arms the test-only record of `vinc-crypto`'s
`Transcript` and writes one `tr` line per snapshot of a transcript: its label and the tag and length of each field
absorbed so far, in the order of the `absorb` calls.

`kinds` holds the field list of each kind of transcript: the tag of each field and the lengths it may have. The
handshake and resumption lists are the lists of `Vinc.Transcript` (`fullFields`, `resumeFields`), with a tag on each
field; `fullSpec_length`, `resumeSpec_length`, `ticketSpec_length` and the stage lengths below tie the two, field for
field. A line is accepted if its fields are a prefix of the list of its label, tag and length at every position.
After the last line every kind must have been seen with all its fields (`covered`).
-/

namespace Vinc.TraceTranscript
open Vinc.Json

/-- One field of a transcript: its tag and the fewest and the most bytes it may have. -/
structure Spec where
  tag : String
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

def fx (t : String) (n : Nat) : Spec := ⟨t, n, n⟩
def vr (t : String) (lo hi : Nat) : Spec := ⟨t, lo, hi⟩

/-- A connection id (`MAX_CID_LEN`), an ALPN (`MAX_ALPN_LEN`), a public key (Ed25519 to hybrid), a signature, and a
field of the callers that take any slice. -/
def cid (t : String) : Spec := vr t 0 20
def alpn (t : String) : Spec := vr t 1 32
def idKey : Spec := vr "id_key" 32 1984
def sig : Spec := vr "sig" 64 3373
def anyLen : Nat := 1000000

/-- The vinc-dtn labels (`vinc-dtn/src/labels.rs`). -/
def dtnChain : String := "VINC 2026 v1 dtn chain"
def dtnTranscript : String := "VINC 2026 v1 dtn transcript"
def dtnBundleId : String := "VINC 2026 v1 dtn bundle id"
def dtnHead : String := "VINC 2026 v1 dtn head"
def dtnAck : String := "VINC 2026 v1 dtn custody ack"

/-- `initial_transcript`: the label is also the first absorbed field. -/
def initialSpec : List Spec :=
  [fx "label" Labels.handshake.length, fx "version" 1, alpn "alpn", cid "dcid", cid "scid", fx "credit" 6, fx "offer" 1,
   fx "e" 32, fx "prekey_hash" 32]

/-- The whole full handshake: `absorb_reply`, `absorb_identity` and `absorb_credit` of the responder, its signature,
the initiator's identity and its signature. -/
def fullSpec : List Spec :=
  initialSpec ++ [cid "r_scid", fx "aead" 1, fx "r_e" 32, fx "ct" 1088, fx "id_alg" 1, idKey, fx "r_credit" 6, sig,
    fx "id_alg" 1, idKey, sig]

/-- `hello_transcript`, `absorb_resume_reply` and the tickets of `confirmation`. -/
def resumeSpec : List Spec :=
  [fx "label" Labels.resumeHandshake.length, fx "version" 1, alpn "alpn", cid "dcid", cid "scid", fx "aead" 1,
   fx "tid" 16, fx "e" 32, fx "credit" 6, fx "binder" 32, cid "r_scid", fx "r_e" 32, fx "r_credit" 6,
   vr "tickets" 0 81]

def ticketSpec : List Spec := [fx "tid" 16, fx "credit" 6]

/-- The field list of each kind of transcript, by label. -/
def kinds : List (String × List Spec) :=
  [(Labels.handshake, fullSpec), (Labels.resumeHandshake, resumeSpec), (Labels.ticket, ticketSpec),
   (Labels.subSessionContext, [vr "alpn" 0 anyLen, vr "cc" 0 anyLen, vr "cs" 0 anyLen]),
   (Labels.keyRollId, [fx "share" 32]), (Labels.kemKeyHash, [fx "encaps_key" 1184]), (Labels.chain, []),
   (dtnChain, []),
   (dtnBundleId, [fx "node_alg" 1, fx "node_key" 32, fx "wall" 8, fx "counter" 4, fx "eph" 32]),
   (dtnTranscript, [fx "eph" 32, fx "x25519" 32, fx "kem_ek" 1184, fx "kem_ct" 1088, fx "node_alg" 1,
      fx "node_key" 32, fx "epoch" 4, fx "id" 32]),
  (dtnHead, [vr "body" 0 anyLen]), (dtnAck, [vr "body" 0 anyLen])]

/-! ## The lists are the proved ones -/

open Vinc.Transcript in
/-- The tagged full-handshake list has a field for each field of `fullFields`, and so for each stage hash. -/
theorem fullSpec_length (i : Initial) (r : ReplyExt) : fullSpec.length = (fullFields i r).length := by
  simp [fullSpec, initialSpec, fullFields, th4Fields, th3Fields, th2Fields, th1Fields, initialFields]

open Vinc.Transcript in
theorem initialSpec_length (i : Initial) : initialSpec.length = (initialFields i).length := by
  simp [initialSpec, initialFields]

open Vinc.Transcript in
theorem th1Spec_length (i : Initial) (r : ReplyExt) : initialSpec.length + 4 = (th1Fields i r).length := by
  simp [initialSpec, th1Fields, initialFields]

open Vinc.Transcript in
theorem resumeSpec_length (h : Hello) (r : ResumeExt) : resumeSpec.length = (resumeFields h r).length := by
  simp [resumeSpec, resumeFields, helloFields]

open Vinc.Transcript in
theorem ticketSpec_length (tid credit : Field) : ticketSpec.length = (ticketCtxFields tid credit).length := by
  simp [ticketSpec, ticketCtxFields]

/-- The label field is the label: its length is that of the label string, the fixed length of the field. -/
theorem label_lengths : Labels.handshake.length = 22 ∧ Labels.resumeHandshake.length = 29 := by decide

/-! ## The replay -/

/-- The kinds seen with all their fields. -/
structure TS where
  full : List String := []

/-- The fields of a line must be the first fields of the list, tag and length at every position. -/
def prefixOK : List Spec → List (String × Nat) → Bool
  | _, [] => true
  | [], _ :: _ => false
  | s :: ss, (t, n) :: fs => s.tag == t && s.lo ≤ n && n ≤ s.hi && prefixOK ss fs

def fieldPairs (j : J) : Except String (List (String × Nat)) := do
  match j.arr? with
  | some a => a.toList.mapM fun v => do
    match v.arr? with
    | some #[t, n] =>
      match t.str?, n.nat? with
      | some t, some n => pure (t, n)
      | _, _ => throw "a field is not a tag and a length"
    | _ => throw "a field is not a pair"
  | none => throw "fields is not an array"

/-- TraceTranscript `Check`. -/
def replayEvent (j : J) (st : TS) : Except String TS := do
  let label ← strF j "label"
  let fs ← fieldPairs (← field j "fields")
  let some spec := kinds.lookup label | throw s!"a transcript of an unknown kind {label}"
  check (prefixOK spec fs) s!"the fields of a {label} transcript are not a prefix of its list: {fs}"
  pure { full := if fs.length == spec.length && !st.full.contains label then label :: st.full else st.full }

/-- TraceTranscript `Covered`: every kind was seen with all its fields. -/
def covered (st : TS) : Except String Unit :=
  check (kinds.all fun k => st.full.contains k.1) s!"kinds never seen in full: {(kinds.filter fun k => !st.full.contains k.1).map (·.1)}"

end Vinc.TraceTranscript
