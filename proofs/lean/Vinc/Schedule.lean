import Vinc.Transcript

/-!
# Key schedule structure

The domain separation of `schedule.rs`: every `expand(prk, label, ctx)` of the key schedule is a derivation with a
`Purpose`, and the label is a function of the purpose that never repeats (`Labels.all_nodup`), so two derivations
of different purposes never share a (label, context) pair, whatever their contexts. A derivation whose context is a
transcript hash (the handshake, application and early-data secrets) takes `th H label fields` as its context; under
the hash hypothesis (`Transcript.HashInj`, never assumed as a postulate) the context determines the transcript and the label of the
transcript, so the secrets of two handshakes with different transcripts are derived from different inputs, for
whatever chaining keys they start from.

The signature messages `label ++ th` are injective in the label and the hash because the two signature labels have
the same length.
-/

namespace Vinc.Schedule
open Vinc.Transcript

/-- Why a key is derived: every `derive`/`expand` call of the security layer. -/
inductive Purpose where
  | hsInitiator | hsResponder | appInitiator | appResponder | resumption | confirm | ticket | binder | early
  | subSession | packetKey | packetIv | headerKey | keyUpdate
  deriving DecidableEq, Repr

/-- The label of each purpose, as the code passes it. -/
def Purpose.label : Purpose → String
  | .hsInitiator => Labels.handshakeInitiator
  | .hsResponder => Labels.handshakeResponder
  | .appInitiator => Labels.applicationInitiator
  | .appResponder => Labels.applicationResponder
  | .resumption => Labels.resumption
  | .confirm => Labels.resumeConfirm
  | .ticket => Labels.ticket
  | .binder => Labels.binder
  | .early => Labels.earlyData
  | .subSession => Labels.subSession
  | .packetKey => Labels.packetKey
  | .packetIv => Labels.packetIv
  | .headerKey => Labels.headerKey
  | .keyUpdate => Labels.keyUpdate

def Purpose.all : List Purpose :=
  [.hsInitiator, .hsResponder, .appInitiator, .appResponder, .resumption, .confirm, .ticket, .binder, .early,
   .subSession, .packetKey, .packetIv, .headerKey, .keyUpdate]

theorem Purpose.mem_all (p : Purpose) : p ∈ Purpose.all := by cases p <;> simp [Purpose.all]

/-- No two purposes share a label. -/
theorem labels_nodup : (Purpose.all.map Purpose.label).Nodup := by decide

/-- Every label a purpose uses is one of the 22 labels. -/
theorem labels_known : ∀ p ∈ Purpose.all, p.label ∈ Labels.all := by decide

theorem label_injective {p q : Purpose} (h : p.label = q.label) : p = q := by
  have key : ∀ (l : List Purpose), (l.map Purpose.label).Nodup → ∀ a ∈ l, ∀ b ∈ l, a.label = b.label → a = b := by
    intro l
    induction l with
    | nil => intro _ a ha; simp at ha
    | cons x l ih =>
      intro hn a ha b hb hab
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
      rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · exact absurd ⟨b, hb', hab.symm⟩ hn.1
      · exact absurd ⟨a, ha', hab⟩ hn.1
      · exact ih hn.2 a ha' b hb' hab
  exact key _ labels_nodup p p.mem_all q q.mem_all h

/-- Two derivations of different purposes have different (label, context) pairs, for any contexts. -/
theorem distinct_purposes {p q : Purpose} (hpq : p ≠ q) {α : Type} (c c' : α) :
    (p.label, c) ≠ (q.label, c') := fun h => hpq (label_injective (Prod.mk.inj h).1)

/-- A derivation input: the key, the label of the purpose and the context. -/
structure Input (α β : Type) where
  prk : α
  label : String
  ctx : β
  deriving DecidableEq

/-- The input of a derivation whose context is the transcript hash of `fs` (handshake, application and early-data
secrets). -/
def thInput {α β : Type} (H : List Nat → List Nat → β) (prk : α) (p : Purpose) (transcriptLabel : String)
    (fs : List Field) : Input α β :=
  ⟨prk, p.label, th H transcriptLabel fs⟩

/-- Same input means same chaining key, same purpose, same transcript label and same fields. -/
theorem thInput_injective {α β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) {prk prk' : α}
    {p q : Purpose} {l l' : String} {fs gs : List Field} (hf : Bounded fs) (hg : Bounded gs)
    (h : thInput H prk p l fs = thInput H prk' q l' gs) :
    prk = prk' ∧ p = q ∧ Labels.bytes l = Labels.bytes l' ∧ fs = gs := by
  simp only [thInput, Input.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h4, h5⟩ := th_injective hH hf hg h3
  exact ⟨h1, label_injective h2, h4, h5⟩

/-- The secrets of two handshakes with different transcripts are derived from different inputs, whatever the
chaining keys: the context (the transcript hash) differs. -/
theorem different_transcripts_different_inputs {α β : Type} {H : List Nat → List Nat → β} (hH : HashInj H)
    {fs gs : List Field} (hf : Bounded fs) (hg : Bounded gs) (hne : fs ≠ gs) (prk prk' : α) (p q : Purpose)
    (l l' : String) : thInput H prk p l fs ≠ thInput H prk' q l' gs :=
  fun h => hne (thInput_injective hH hf hg h).2.2.2

/-- A full-handshake transcript hash is never a resumption transcript hash: the transcript labels differ. -/
theorem full_ne_resume_hash {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) {fs gs : List Field}
    (hf : Bounded fs) (hg : Bounded gs) : th H Labels.handshake fs ≠ th H Labels.resumeHandshake gs := by
  intro h
  have := (th_injective hH hf hg h).1
  revert this
  decide

/-! ## Signature messages -/

/-- The message a signature covers: `label ++ th`. -/
def sigMsg (label : String) (th : List Nat) : List Nat := Labels.bytes label ++ th

/-- The two signature labels have the same length. -/
theorem sig_labels_same_length :
    (Labels.bytes Labels.signatureResponder).length = (Labels.bytes Labels.signatureInitiator).length := by decide

/-- A responder signature message is never an initiator one, and each determines its hash. -/
theorem sigMsg_injective {l l' : String} (hl : l = Labels.signatureResponder ∨ l = Labels.signatureInitiator)
    (hl' : l' = Labels.signatureResponder ∨ l' = Labels.signatureInitiator) {t t' : List Nat}
    (h : sigMsg l t = sigMsg l' t') : l = l' ∧ t = t' := by
  have hlen : (Labels.bytes l).length = (Labels.bytes l').length := by
    rcases hl with rfl | rfl <;> rcases hl' with rfl | rfl
    · rfl
    · exact sig_labels_same_length
    · exact sig_labels_same_length.symm
    · rfl
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  refine ⟨?_, h2⟩
  rcases hl with rfl | rfl <;> rcases hl' with rfl | rfl
  · rfl
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · rfl

theorem sigMsg_responder_ne_initiator (t t' : List Nat) :
    sigMsg Labels.signatureResponder t ≠ sigMsg Labels.signatureInitiator t' := by
  intro h
  have := (sigMsg_injective (Or.inl rfl) (Or.inr rfl) h).1
  revert this
  decide

end Vinc.Schedule

#audit_axioms Vinc.Schedule.labels_nodup
#audit_axioms Vinc.Schedule.labels_known
#audit_axioms Vinc.Schedule.label_injective
#audit_axioms Vinc.Schedule.distinct_purposes
#audit_axioms Vinc.Schedule.thInput_injective
#audit_axioms Vinc.Schedule.different_transcripts_different_inputs
#audit_axioms Vinc.Schedule.full_ne_resume_hash
#audit_axioms Vinc.Schedule.sigMsg_injective
#audit_axioms Vinc.Schedule.sigMsg_responder_ne_initiator
