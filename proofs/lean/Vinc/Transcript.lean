import Vinc.Varint
import Vinc.Labels

/-!
# Transcript encoding

`vinc_crypto::Transcript::absorb` feeds the hash one field as its multiformats varint length followed by its bytes.
`encode` is the concatenation of the fields so absorbed, and `encode_injective` shows that different lists of
fields give different byte strings, so a transcript hash separates different handshakes as soon as the hash is
collision resistant (`HashInj`, a hypothesis, never assumed as a postulate).

The field lists of the handshake transcripts are those `schedule.rs` builds, in the same order. `initialFields`
is `initial_transcript`, `helloFields` is `hello_transcript`, and the `*Fields` lists after them are the `absorb_*`
functions. Bytes are `Nat`s. Every field the handshake binds is a field of its own (the version byte, the ALPN, both
connection ids, the 6-byte credit record, the AEAD offer byte, the public values, the prekey hash), never folded into
another, so each argument is recovered separately from a list. The label of the transcript is the hash's domain
(`with_label`, the `label` argument of `th`) and also the first absorbed field.
-/

namespace Vinc.Transcript
open Vinc.Varint

/-- One absorbed field: a list of bytes. -/
abbrev Field := List Nat

/-- `Transcript::absorb`: the varint length, then the bytes. -/
def absorb (f : Field) : List Nat := encodeBytes f.length ++ f

/-- The bytes a transcript hashes for a list of absorbed fields. -/
def encode : List Field → List Nat
  | [] => []
  | f :: fs => absorb f ++ encode fs

/-- A slice is shorter than the varint limit (`isize::MAX < 2^63`). -/
def Bounded (fs : List Field) : Prop := ∀ f ∈ fs, f.length < limit

theorem encode_cons (f : Field) (fs : List Field) : encode (f :: fs) = encodeBytes f.length ++ (f ++ encode fs) := by
  simp [encode, absorb]

theorem encode_eq_nil (gs : List Field) (h : [] = encode gs) : gs = [] := by
  cases gs with
  | nil => rfl
  | cons g gs =>
    rw [encode_cons] at h
    have := congrArg List.length h
    have hp := encodedLen_pos g.length
    simp [length_encodeBytes] at this
    omega

/-- The field encoding is injective: different lists of fields give different byte strings. -/
theorem encode_injective : ∀ (fs gs : List Field), Bounded fs → Bounded gs → encode fs = encode gs → fs = gs
  | [], gs, _, _, h => (encode_eq_nil gs h).symm
  | f :: fs, [], _, _, h => absurd (encode_eq_nil (f :: fs) h.symm) (by simp)
  | f :: fs, g :: gs, hf, hg, h => by
    rw [encode_cons, encode_cons] at h
    have hfl : f.length < limit := hf f (by simp)
    have hgl : g.length < limit := hg g (by simp)
    have d1 := decode_encode f.length (f ++ encode fs) hfl
    have d2 := decode_encode g.length (g ++ encode gs) hgl
    rw [h] at d1
    rw [d1] at d2
    have hlen : f.length = g.length := by
      have := Except.ok.inj d2
      exact (Prod.mk.inj this).1
    rw [hlen] at h
    have h' := List.append_cancel_left h
    obtain ⟨hfg, hrest⟩ := List.append_inj h' (by omega)
    subst hfg
    rw [encode_injective fs gs (fun x hx => hf x (by simp [hx])) (fun x hx => hg x (by simp [hx])) hrest]

/-! ## The hash hypothesis -/

/-- The transcript hash `Transcript::with_label(label)` over the absorbed bytes is collision resistant: it
determines the label and the bytes. A hypothesis about BLAKE3, passed to the theorems that need it. -/
structure HashInj {β : Type} (H : List Nat → List Nat → β) : Prop where
  inj : ∀ l₁ b₁ l₂ b₂, H l₁ b₁ = H l₂ b₂ → l₁ = l₂ ∧ b₁ = b₂

/-- The hash of a transcript: its label and the fields absorbed. -/
def th {β : Type} (H : List Nat → List Nat → β) (label : String) (fs : List Field) : β :=
  H (Labels.bytes label) (encode fs)

/-- Two transcripts with the same hash have the same label and the same fields. -/
theorem th_injective {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) {l₁ l₂ : String}
    {fs gs : List Field} (hf : Bounded fs) (hg : Bounded gs) (h : th H l₁ fs = th H l₂ gs) :
    Labels.bytes l₁ = Labels.bytes l₂ ∧ fs = gs := by
  obtain ⟨h1, h2⟩ := hH.inj _ _ _ _ h
  exact ⟨h1, encode_injective fs gs hf hg h2⟩

/-! ## The handshake field lists -/

/-- The fields of an Initial that the transcript absorbs (`InitialFields`). `version` and `offer` are one byte each;
`credit` is the 6 bytes of the initiator's credit record (`CreditRecord::encode`). -/
structure Initial where
  version : Nat
  alpn : Field
  dcid : Field
  scid : Field
  credit : Field
  offer : Nat
  e : Field
  prekeyHash : Field
  deriving DecidableEq

/-- `initial_transcript`: the absorbed fields, in order: the label, the version byte, the ALPN, both connection ids,
the credit record, the AEAD offer byte, the public value and the prekey hash. -/
def initialFields (i : Initial) : List Field :=
  [Labels.bytes Labels.handshake, [i.version], i.alpn, i.dcid, i.scid, i.credit, [i.offer], i.e, i.prekeyHash]

/-- What the responder and then the initiator absorb after the Initial: the reply (`absorb_reply`), the responder's
identity (`absorb_identity`) and credit record (`absorb_credit`), its signature, the initiator's identity and its
signature. -/
structure ReplyExt where
  scid : Field
  aead : Nat
  e : Field
  ct : Field
  respAlg : Nat
  respKey : Field
  respCredit : Field
  respSig : Field
  initAlg : Nat
  initKey : Field
  initSig : Field
  deriving DecidableEq

/-- The transcript hash `th1` of the handshake secrets: the Initial and the responder's reply. -/
def th1Fields (i : Initial) (r : ReplyExt) : List Field :=
  initialFields i ++ [r.scid, [r.aead], r.e, r.ct]

/-- The fields `th2` covers, which the responder signs: `th1`, the responder's identity and its credit record. -/
def th2Fields (i : Initial) (r : ReplyExt) : List Field :=
  th1Fields i r ++ [[r.respAlg], r.respKey, r.respCredit]

/-- `th3`, the associated data of the Finish: `th2` and the responder's signature. -/
def th3Fields (i : Initial) (r : ReplyExt) : List Field := th2Fields i r ++ [r.respSig]

/-- `th4`, which the initiator signs: `th3` and the initiator's identity. -/
def th4Fields (i : Initial) (r : ReplyExt) : List Field := th3Fields i r ++ [[r.initAlg], r.initKey]

/-- The fields of the whole full handshake, in the order they are absorbed: `th4` and the initiator's signature. -/
def fullFields (i : Initial) (r : ReplyExt) : List Field := th4Fields i r ++ [r.initSig]

/-- The fields of a resume Hello (`HelloFields`) in `hello_transcript`. -/
structure Hello where
  version : Nat
  alpn : Field
  dcid : Field
  scid : Field
  aead : Nat
  tid : Field
  e : Field
  credit : Field
  deriving DecidableEq

def helloFields (h : Hello) : List Field :=
  [Labels.bytes Labels.resumeHandshake, [h.version], h.alpn, h.dcid, h.scid, [h.aead], h.tid, h.e, h.credit]

/-- `absorb_resume_reply` followed by the tickets that `confirmation` absorbs: the binder, the responder's
connection id, public value and credit record, then the bytes of the tickets. -/
structure ResumeExt where
  binder : Field
  scid : Field
  e : Field
  credit : Field
  tickets : Field
  deriving DecidableEq

def resumeFields (h : Hello) (r : ResumeExt) : List Field :=
  helloFields h ++ [r.binder, r.scid, r.e, r.credit, r.tickets]

/-- `absorb_identity` and `absorb_credit`: an identity (algorithm tag byte, public key) and a credit record. -/
def identityCreditFields (alg : Nat) (key credit : Field) : List Field := [[alg], key, credit]

/-- The context of a ticket's pre-shared key (`ticket_psk`): the ticket id and the credit record. -/
def ticketCtxFields (tid credit : Field) : List Field := [tid, credit]

theorem initialFields_injective (a b : Initial) (h : initialFields a = initialFields b) : a = b := by
  obtain ⟨v, p, d, s, c, o, e, k⟩ := a
  obtain ⟨v', p', d', s', c', o', e', k'⟩ := b
  simp_all [initialFields]

theorem helloFields_injective (a b : Hello) (h : helloFields a = helloFields b) : a = b := by
  obtain ⟨v, p, d, s, o, t, e, c⟩ := a
  obtain ⟨v', p', d', s', o', t', e', c'⟩ := b
  simp_all [helloFields]

theorem th1Fields_injective (a b : Initial) (r s : ReplyExt) (h : th1Fields a r = th1Fields b s) :
    a = b ∧ r.scid = s.scid ∧ r.aead = s.aead ∧ r.e = s.e ∧ r.ct = s.ct := by
  obtain ⟨v, p, d, sc, c, o, e, k⟩ := a
  obtain ⟨v', p', d', sc', c', o', e', k'⟩ := b
  simp_all [th1Fields, initialFields]

theorem th2Fields_injective (a b : Initial) (r s : ReplyExt) (h : th2Fields a r = th2Fields b s) :
    a = b ∧ r.scid = s.scid ∧ r.aead = s.aead ∧ r.e = s.e ∧ r.ct = s.ct ∧ r.respAlg = s.respAlg ∧
      r.respKey = s.respKey ∧ r.respCredit = s.respCredit := by
  obtain ⟨v, p, d, sc, c, o, e, k⟩ := a
  obtain ⟨v', p', d', sc', c', o', e', k'⟩ := b
  simp_all [th2Fields, th1Fields, initialFields]

theorem th3Fields_injective (a b : Initial) (r s : ReplyExt) (h : th3Fields a r = th3Fields b s) :
    a = b ∧ r.scid = s.scid ∧ r.aead = s.aead ∧ r.e = s.e ∧ r.ct = s.ct ∧ r.respAlg = s.respAlg ∧
      r.respKey = s.respKey ∧ r.respCredit = s.respCredit ∧ r.respSig = s.respSig := by
  obtain ⟨v, p, d, sc, c, o, e, k⟩ := a
  obtain ⟨v', p', d', sc', c', o', e', k'⟩ := b
  simp_all [th3Fields, th2Fields, th1Fields, initialFields]

theorem th4Fields_injective (a b : Initial) (r s : ReplyExt) (h : th4Fields a r = th4Fields b s) :
    a = b ∧ r.scid = s.scid ∧ r.aead = s.aead ∧ r.e = s.e ∧ r.ct = s.ct ∧ r.respAlg = s.respAlg ∧
      r.respKey = s.respKey ∧ r.respCredit = s.respCredit ∧ r.respSig = s.respSig ∧ r.initAlg = s.initAlg ∧
      r.initKey = s.initKey := by
  obtain ⟨v, p, d, sc, c, o, e, k⟩ := a
  obtain ⟨v', p', d', sc', c', o', e', k'⟩ := b
  simp_all [th4Fields, th3Fields, th2Fields, th1Fields, initialFields]

/-- The whole list of a full handshake determines every argument, each as its own field. -/
theorem fullFields_injective (a b : Initial) (r s : ReplyExt) (h : fullFields a r = fullFields b s) :
    a = b ∧ r = s := by
  obtain ⟨v, p, d, sc, c, o, e, k⟩ := a
  obtain ⟨v', p', d', sc', c', o', e', k'⟩ := b
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := r
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := s
  simp_all [fullFields, th4Fields, th3Fields, th2Fields, th1Fields, initialFields]

theorem resumeFields_injective (a b : Hello) (r s : ResumeExt) (h : resumeFields a r = resumeFields b s) :
    a = b ∧ r = s := by
  obtain ⟨v, p, d, sc, o, t, e, c⟩ := a
  obtain ⟨v', p', d', sc', o', t', e', c'⟩ := b
  obtain ⟨r1, r2, r3, r4, r5⟩ := r
  obtain ⟨s1, s2, s3, s4, s5⟩ := s
  simp_all [resumeFields, helloFields]

/-- The identity and credit absorb is injective: the algorithm tag, the public key and the credit record are each
recovered. -/
theorem identityCreditFields_injective (a b : Nat) (k k' c c' : Field)
    (h : identityCreditFields a k c = identityCreditFields b k' c') : a = b ∧ k = k' ∧ c = c' := by
  simp_all [identityCreditFields]

/-- The ticket context is injective in the ticket id and the credit record. -/
theorem ticketCtxFields_injective (t t' c c' : Field) (h : ticketCtxFields t c = ticketCtxFields t' c') :
    t = t' ∧ c = c' := by
  simp_all [ticketCtxFields]

/-- An Initial list never equals a Hello list: the first field is the label. -/
theorem initial_ne_hello (i : Initial) (h : Hello) : initialFields i ≠ helloFields h := by
  intro heq
  have h1 : Labels.bytes Labels.handshake = Labels.bytes Labels.resumeHandshake := by
    have := congrArg List.head? heq
    simpa [initialFields, helloFields] using this
  revert h1
  decide

/-- No stage of a full handshake equals a stage of a resumption: the first field differs. -/
theorem fullFields_ne_resumeFields (i : Initial) (r : ReplyExt) (h : Hello) (s : ResumeExt) :
    fullFields i r ≠ resumeFields h s := by
  intro heq
  have h1 := congrArg List.head? heq
  simp [fullFields, th4Fields, th3Fields, th2Fields, th1Fields, resumeFields, initialFields, helloFields] at h1
  revert h1
  decide

/-- The same for every stage list that the full handshake hashes: each starts with the handshake label, each
resume list with the resume label. -/
theorem stages_ne_resume (i : Initial) (r : ReplyExt) (h : Hello) (s : ResumeExt) :
    (initialFields i ≠ resumeFields h s) ∧ (th1Fields i r ≠ resumeFields h s) ∧ (th2Fields i r ≠ resumeFields h s) ∧
      (th3Fields i r ≠ resumeFields h s) ∧ (th4Fields i r ≠ resumeFields h s) := by
  have key : ∀ l : List Field, l.head? = some (Labels.bytes Labels.handshake) → l ≠ resumeFields h s := by
    intro l hl heq
    rw [heq] at hl
    simp [resumeFields, helloFields] at hl
    revert hl
    decide
  refine ⟨key _ ?_, key _ ?_, key _ ?_, key _ ?_, key _ ?_⟩ <;>
    simp [initialFields, th1Fields, th2Fields, th3Fields, th4Fields]

/-- Fields are short enough: every field of a handshake is a header field of at most a few kilobytes (the largest is
the 1184-byte prekey, the 1088-byte ciphertext and the sealed blobs), so `Bounded` holds for every real list. -/
theorem bounded_of_lengths (fs : List Field) (h : ∀ f ∈ fs, f.length < 2 ^ 32) : Bounded fs := by
  intro f hf
  have := h f hf
  unfold limit
  omega

/-! ## The hash corollaries -/

/-- Two different full handshakes never share a transcript hash: different Initial or reply arguments give different
hashes under `HashInj`. -/
theorem full_th_injective {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a b : Initial) (r s : ReplyExt)
    (hf : Bounded (fullFields a r)) (hg : Bounded (fullFields b s))
    (h : th H Labels.handshake (fullFields a r) = th H Labels.handshake (fullFields b s)) : a = b ∧ r = s :=
  fullFields_injective a b r s (th_injective hH hf hg h).2

/-- The hash after the Initial determines every field of the Initial. -/
theorem initial_th_injective {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a b : Initial)
    (hf : Bounded (initialFields a)) (hg : Bounded (initialFields b))
    (h : th H Labels.handshake (initialFields a) = th H Labels.handshake (initialFields b)) : a = b :=
  initialFields_injective a b (th_injective hH hf hg h).2

/-- The hash `th1` (the input of the handshake secrets) determines the Initial and the reply. -/
theorem th1_th_injective {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a b : Initial) (r s : ReplyExt)
    (hf : Bounded (th1Fields a r)) (hg : Bounded (th1Fields b s))
    (h : th H Labels.handshake (th1Fields a r) = th H Labels.handshake (th1Fields b s)) :
    a = b ∧ r.scid = s.scid ∧ r.aead = s.aead ∧ r.e = s.e ∧ r.ct = s.ct :=
  th1Fields_injective a b r s (th_injective hH hf hg h).2

/-- The hash `th2` that the responder signs determines the Initial, the reply, the responder's identity and its
credit record. -/
theorem th2_th_injective {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a b : Initial) (r s : ReplyExt)
    (hf : Bounded (th2Fields a r)) (hg : Bounded (th2Fields b s))
    (h : th H Labels.handshake (th2Fields a r) = th H Labels.handshake (th2Fields b s)) :
    a = b ∧ r.scid = s.scid ∧ r.aead = s.aead ∧ r.e = s.e ∧ r.ct = s.ct ∧ r.respAlg = s.respAlg ∧
      r.respKey = s.respKey ∧ r.respCredit = s.respCredit :=
  th2Fields_injective a b r s (th_injective hH hf hg h).2

/-- Two different resumptions never share a transcript hash. -/
theorem resume_th_injective {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a b : Hello) (r s : ResumeExt)
    (hf : Bounded (resumeFields a r)) (hg : Bounded (resumeFields b s))
    (h : th H Labels.resumeHandshake (resumeFields a r) = th H Labels.resumeHandshake (resumeFields b s)) :
    a = b ∧ r = s :=
  resumeFields_injective a b r s (th_injective hH hf hg h).2

/-- The hash after the Hello determines every field of the Hello (the binder is computed over it). -/
theorem hello_th_injective {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a b : Hello)
    (hf : Bounded (helloFields a)) (hg : Bounded (helloFields b))
    (h : th H Labels.resumeHandshake (helloFields a) = th H Labels.resumeHandshake (helloFields b)) : a = b :=
  helloFields_injective a b (th_injective hH hf hg h).2

/-- A hash of an Initial is never a hash of a Hello, whatever their fields: the labels differ. -/
theorem initial_th_ne_hello_th {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a : Initial) (b : Hello)
    (hf : Bounded (initialFields a)) (hg : Bounded (helloFields b)) :
    th H Labels.handshake (initialFields a) ≠ th H Labels.resumeHandshake (helloFields b) := by
  intro h
  have := (th_injective hH hf hg h).1
  revert this
  decide

/-- A full-handshake hash is never a resumption hash. -/
theorem full_th_ne_resume_th {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a : Initial) (r : ReplyExt)
    (b : Hello) (s : ResumeExt) (hf : Bounded (fullFields a r)) (hg : Bounded (resumeFields b s)) :
    th H Labels.handshake (fullFields a r) ≠ th H Labels.resumeHandshake (resumeFields b s) := by
  intro h
  have := (th_injective hH hf hg h).1
  revert this
  decide

/-- The ticket context hash `H(tid, credit)` (a transcript labelled with the ticket label) determines the ticket id
and the credit record. -/
theorem ticketCtx_th_injective {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (t t' c c' : Field)
    (hf : Bounded (ticketCtxFields t c)) (hg : Bounded (ticketCtxFields t' c'))
    (h : th H Labels.ticket (ticketCtxFields t c) = th H Labels.ticket (ticketCtxFields t' c')) : t = t' ∧ c = c' :=
  ticketCtxFields_injective t t' c c' (th_injective hH hf hg h).2

end Vinc.Transcript

#audit_axioms Vinc.Transcript.encode_injective
#audit_axioms Vinc.Transcript.th_injective
#audit_axioms Vinc.Transcript.initialFields_injective
#audit_axioms Vinc.Transcript.helloFields_injective
#audit_axioms Vinc.Transcript.th1Fields_injective
#audit_axioms Vinc.Transcript.th2Fields_injective
#audit_axioms Vinc.Transcript.th3Fields_injective
#audit_axioms Vinc.Transcript.th4Fields_injective
#audit_axioms Vinc.Transcript.fullFields_injective
#audit_axioms Vinc.Transcript.resumeFields_injective
#audit_axioms Vinc.Transcript.identityCreditFields_injective
#audit_axioms Vinc.Transcript.ticketCtxFields_injective
#audit_axioms Vinc.Transcript.initial_ne_hello
#audit_axioms Vinc.Transcript.fullFields_ne_resumeFields
#audit_axioms Vinc.Transcript.stages_ne_resume
#audit_axioms Vinc.Transcript.full_th_injective
#audit_axioms Vinc.Transcript.initial_th_injective
#audit_axioms Vinc.Transcript.th1_th_injective
#audit_axioms Vinc.Transcript.th2_th_injective
#audit_axioms Vinc.Transcript.resume_th_injective
#audit_axioms Vinc.Transcript.hello_th_injective
#audit_axioms Vinc.Transcript.initial_th_ne_hello_th
#audit_axioms Vinc.Transcript.full_th_ne_resume_th
#audit_axioms Vinc.Transcript.ticketCtx_th_injective
