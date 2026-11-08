import Vinc.Varint
import Vinc.Labels

/-!
# Transcript encoding

`vinc_crypto::Transcript::absorb` feeds the hash one field as its multiformats varint length followed by its bytes.
`encode` is the concatenation of the fields so absorbed, and `encode_injective` shows that different lists of
fields give different byte strings, so a transcript hash separates different handshakes as soon as the hash is
collision resistant (`HashInj`, a hypothesis, never assumed as a postulate).

The field lists of the handshake transcripts are those `schedule.rs` builds, in the same order. `initialFields`
is `initial_transcript`, `helloFields` is `hello_transcript`, and the `*Ext` lists are the `absorb_*` functions.
Bytes are `Nat`s; fixed-width fields (the version, in 4 bytes) are modelled by their big-endian bytes.
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

/-! ## Fixed-width integers -/

/-- The 4 big-endian bytes of a `u32`. -/
def be4 (v : Nat) : List Nat := [v / 2 ^ 24 % 256, v / 2 ^ 16 % 256, v / 2 ^ 8 % 256, v % 256]

theorem be4_injective (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : be4 a = be4 b) : a = b := by
  simp [be4] at h
  omega

/-! ## The handshake field lists -/

/-- The fields of an Initial that the transcript absorbs (`InitialFields`). -/
structure Initial where
  version : Nat
  dcid : Field
  scid : Field
  alpn : Field
  offer : Nat
  e : Field
  prekeyHash : Field
  token : Field
  deriving DecidableEq

/-- `initial_transcript`: the absorbed fields, in order. -/
def initialFields (i : Initial) : List Field :=
  [Labels.bytes Labels.handshake, be4 i.version, i.alpn, i.dcid, i.scid, i.token, [i.offer], i.e, i.prekeyHash]

/-- The responder's contribution (`absorb_reply`) followed by its identity (`absorb_identity`) and signature. -/
structure ReplyExt where
  scid : Field
  aead : Nat
  e : Field
  ct : Field
  respAlg : Nat
  respKey : Field
  respSig : Field
  initAlg : Nat
  initKey : Field
  initSig : Field
  deriving DecidableEq

/-- Everything absorbed after the Initial up to the end of the full handshake. -/
def replyFields (r : ReplyExt) : List Field :=
  [r.scid, [r.aead], r.e, r.ct, [r.respAlg], r.respKey, r.respSig, [r.initAlg], r.initKey, r.initSig]

/-- The fields of the whole full handshake, in the order they are absorbed. -/
def fullFields (i : Initial) (r : ReplyExt) : List Field := initialFields i ++ replyFields r

/-- The fields of a resume Hello (`HelloFields`) in `hello_transcript`. -/
structure Hello where
  version : Nat
  alpn : Field
  dcid : Field
  scid : Field
  aead : Nat
  tid : Field
  e : Field
  deriving DecidableEq

def helloFields (h : Hello) : List Field :=
  [Labels.bytes Labels.resumeHandshake, be4 h.version, h.alpn, h.dcid, h.scid, [h.aead], h.tid, h.e]

/-- `absorb_resume_reply`: the binder, the responder's connection id and public value. -/
structure ResumeExt where
  binder : Field
  scid : Field
  e : Field
  deriving DecidableEq

def resumeFields (h : Hello) (r : ResumeExt) : List Field := helloFields h ++ [r.binder, r.scid, r.e]

theorem initialFields_injective (a b : Initial) (ha : a.version < 2 ^ 32) (hb : b.version < 2 ^ 32)
    (h : initialFields a = initialFields b) : a = b := by
  have hv := be4_injective _ _ ha hb (by
    have := congrArg (fun l => l[1]?) h
    simpa [initialFields] using this)
  obtain ⟨v, d, s, p, o, e, k, t⟩ := a
  obtain ⟨v', d', s', p', o', e', k', t'⟩ := b
  simp_all [initialFields]

theorem helloFields_injective (a b : Hello) (ha : a.version < 2 ^ 32) (hb : b.version < 2 ^ 32)
    (h : helloFields a = helloFields b) : a = b := by
  have hv := be4_injective _ _ ha hb (by
    have := congrArg (fun l => l[1]?) h
    simpa [helloFields] using this)
  obtain ⟨v, p, d, s, o, t, e⟩ := a
  obtain ⟨v', p', d', s', o', t', e'⟩ := b
  simp_all [helloFields]

theorem replyFields_injective (a b : ReplyExt) (h : replyFields a = replyFields b) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := b
  simp [replyFields] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

/-- The whole list of a full handshake determines every argument. -/
theorem fullFields_injective (a b : Initial) (r s : ReplyExt) (ha : a.version < 2 ^ 32) (hb : b.version < 2 ^ 32)
    (h : fullFields a r = fullFields b s) : a = b ∧ r = s := by
  have hl : (initialFields a).length = (initialFields b).length := by simp [initialFields]
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  exact ⟨initialFields_injective a b ha hb h1, replyFields_injective r s h2⟩

theorem resumeFields_injective (a b : Hello) (r s : ResumeExt) (ha : a.version < 2 ^ 32) (hb : b.version < 2 ^ 32)
    (h : resumeFields a r = resumeFields b s) : a = b ∧ r = s := by
  have hl : (helloFields a).length = (helloFields b).length := by simp [helloFields]
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  refine ⟨helloFields_injective a b ha hb h1, ?_⟩
  obtain ⟨r1, r2, r3⟩ := r
  obtain ⟨s1, s2, s3⟩ := s
  simp at h2
  obtain ⟨_, _, _⟩ := h2
  subst_vars; rfl

/-- An Initial list never equals a Hello list: the first field is the label. -/
theorem initial_ne_hello (i : Initial) (h : Hello) : initialFields i ≠ helloFields h := by
  intro heq
  have h1 : Labels.bytes Labels.handshake = Labels.bytes Labels.resumeHandshake := by
    have := congrArg List.head? heq
    simpa [initialFields, helloFields] using this
  revert h1
  decide

theorem fullFields_ne_resumeFields (i : Initial) (r : ReplyExt) (h : Hello) (s : ResumeExt) :
    fullFields i r ≠ resumeFields h s := by
  intro heq
  have h1 := congrArg List.head? heq
  simp [fullFields, resumeFields, initialFields, helloFields, replyFields] at h1
  revert h1
  decide

/-- Fields are short enough: every field of a handshake is a header field of at most a few kilobytes (the largest is
the 1184-byte prekey, the 1088-byte ciphertext and the sealed blobs), so `Bounded` holds for every real list. -/
theorem bounded_of_lengths (fs : List Field) (h : ∀ f ∈ fs, f.length < 2 ^ 32) : Bounded fs := by
  intro f hf
  have := h f hf
  unfold limit
  omega

/-- Two different handshakes never share a transcript hash: different Initial or reply arguments give different
hashes under `HashInj`. -/
theorem full_th_injective {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (a b : Initial) (r s : ReplyExt)
    (ha : a.version < 2 ^ 32) (hb : b.version < 2 ^ 32) (hf : Bounded (fullFields a r)) (hg : Bounded (fullFields b s))
    (h : th H Labels.handshake (fullFields a r) = th H Labels.handshake (fullFields b s)) : a = b ∧ r = s :=
  fullFields_injective a b r s ha hb (th_injective hH hf hg h).2

end Vinc.Transcript

#audit_axioms Vinc.Transcript.encode_injective
#audit_axioms Vinc.Transcript.th_injective
#audit_axioms Vinc.Transcript.initialFields_injective
#audit_axioms Vinc.Transcript.helloFields_injective
#audit_axioms Vinc.Transcript.fullFields_injective
#audit_axioms Vinc.Transcript.resumeFields_injective
#audit_axioms Vinc.Transcript.initial_ne_hello
#audit_axioms Vinc.Transcript.fullFields_ne_resumeFields
#audit_axioms Vinc.Transcript.full_th_injective
