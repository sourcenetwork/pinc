import Vinc.Credit

/-!
# Key schedule structure

The domain separation of `schedule.rs`: every `expand(prk, label, ctx)` of the key schedule is a derivation with a
`Purpose`, and the label is a function of the purpose that never repeats (`Labels.all_nodup`), so two derivations
of different purposes never share a (label, context) pair, whatever their contexts. A derivation whose context is a
transcript hash (the handshake, application and early-data secrets) takes `th H label fields` as its context; under
the hash hypothesis (`Transcript.HashInj`, never assumed as a postulate) the context determines the transcript and the label of the
transcript, so the secrets of two handshakes with different transcripts are derived from different inputs, for
whatever chaining keys they start from.

The context of a ticket's pre-shared key is `H(tid, credit.encode())` (`ticket_psk`); it is injective in the ticket id
and the credit record (`ticketInput_injective`), so a resumption derives the same key only against the record the
ticket remembers. A key roll derives `expand(extract(secret, dh), KEY_ROLL)` (`roll_secret`); its input is modelled by
`rollInput`, with the extraction as a function `ext` that is injective as a hypothesis about the hash.

The signature messages `label ++ th` are injective in the label and the hash because the two signature labels have
the same length.
-/

namespace Vinc.Schedule
open Vinc.Transcript

/-- Why a key is derived: every `derive`/`expand` call of the security layer. -/
inductive Purpose where
  | hsInitiator | hsResponder | appInitiator | appResponder | resumption | confirm | ticket | binder | early
  | subSession | packetKey | packetIv | headerKey | keyRoll | keyRollId | cidSecret
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
  | .keyRoll => Labels.keyRoll
  | .keyRollId => Labels.keyRollId
  | .cidSecret => Labels.cidSecret

def Purpose.all : List Purpose :=
  [.hsInitiator, .hsResponder, .appInitiator, .appResponder, .resumption, .confirm, .ticket, .binder, .early,
   .subSession, .packetKey, .packetIv, .headerKey, .keyRoll, .keyRollId, .cidSecret]

theorem Purpose.mem_all (p : Purpose) : p ∈ Purpose.all := by cases p <;> simp [Purpose.all]

/-- No two purposes share a label. -/
theorem labels_nodup : (Purpose.all.map Purpose.label).Nodup := by decide

/-- Every label a purpose uses is one of the 23 labels. -/
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


/-! ## The ticket key -/

/-- The input of `ticket_psk(resume, tid, credit)`: the resumption secret as the key, the ticket label, and as
context the hash of the transcript `tid, credit.encode()` labelled with the ticket label. -/
def ticketInput {α β : Type} (H : List Nat → List Nat → β) (resume : α) (tid : Field) (credit : Credit.Record) :
    Input α β :=
  ⟨resume, Purpose.ticket.label, th H Labels.ticket (ticketCtxFields tid (Credit.encode credit))⟩

/-- Two ticket keys are derived from the same input only for the same resumption secret, ticket id and credit
record: a resumption works only against the record the ticket remembers. -/
theorem ticketInput_injective {α β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) {resume resume' : α}
    {tid tid' : Field} {r s : Credit.Record} (hr : Credit.Valid r) (hs : Credit.Valid s)
    (hf : Bounded (ticketCtxFields tid (Credit.encode r))) (hg : Bounded (ticketCtxFields tid' (Credit.encode s)))
    (h : ticketInput H resume tid r = ticketInput H resume' tid' s) : resume = resume' ∧ tid = tid' ∧ r = s := by
  simp only [ticketInput, Input.mk.injEq] at h
  obtain ⟨h1, _, h3⟩ := h
  obtain ⟨h4, h5⟩ := Credit.ticketCtx_credit_recovered tid tid' r s hr hs (th_injective hH hf hg h3).2
  exact ⟨h1, h4, h5⟩

/-- A ticket remembered with a different credit record gives a different key input: a client cannot resume a ticket
against a record other than the remembered one. -/
theorem ticket_psk_binds_credit {α β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (resume resume' : α)
    (tid tid' : Field) {r s : Credit.Record} (hr : Credit.Valid r) (hs : Credit.Valid s) (hne : r ≠ s)
    (hf : Bounded (ticketCtxFields tid (Credit.encode r))) (hg : Bounded (ticketCtxFields tid' (Credit.encode s))) :
    ticketInput H resume tid r ≠ ticketInput H resume' tid' s :=
  fun h => hne (ticketInput_injective hH hr hs hf hg h).2.2

/-- The context of the ticket key is the same hash function as every transcript, labelled `ticket`: it differs from
the hash of any handshake or resumption transcript. -/
theorem ticket_ctx_ne_handshake {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (tid : Field)
    (r : Credit.Record) (fs : List Field) (hf : Bounded (ticketCtxFields tid (Credit.encode r))) (hg : Bounded fs) :
    th H Labels.ticket (ticketCtxFields tid (Credit.encode r)) ≠ th H Labels.handshake fs ∧
      th H Labels.ticket (ticketCtxFields tid (Credit.encode r)) ≠ th H Labels.resumeHandshake fs := by
  constructor <;> intro h <;> have := (th_injective hH hf hg h).1 <;> revert this <;> decide

/-! ## The key roll -/

/-- The input of `roll_secret(secret, dh)`: the chaining key `extract(secret, dh)` (`ext` stands for the extraction),
the key-roll label and the empty context. -/
def rollInput {α γ : Type} (ext : α → α → γ) (secret dh : α) : Input γ (List Nat) :=
  ⟨ext secret dh, Purpose.keyRoll.label, []⟩

/-- Two rolls share an input only when the extraction input (the old secret and the fresh Diffie-Hellman value) is
the same, if the extraction is injective (a hypothesis about the keyed hash, never a postulate). -/
theorem rollInput_injective {α γ : Type} {ext : α → α → γ} (hext : ∀ a b c d, ext a b = ext c d → a = c ∧ b = d)
    {s s' d d' : α} (h : rollInput ext s d = rollInput ext s' d') : s = s' ∧ d = d' := by
  simp only [rollInput, Input.mk.injEq] at h
  exact hext _ _ _ _ h.1

/-- A key roll never shares its derivation input with another purpose, whatever the keys and contexts: the label
is `key roll`. -/
theorem rollInput_ne_other {α γ : Type} (ext : α → α → γ) (s d : α) {p : Purpose} (hp : p ≠ .keyRoll) (k : γ)
    (c : List Nat) : rollInput ext s d ≠ (⟨k, p.label, c⟩ : Input γ (List Nat)) := by
  intro h
  simp only [rollInput, Input.mk.injEq] at h
  exact hp (label_injective h.2.1).symm

/-- The secrets derived from the final transcript (`application_secrets`) have five distinct purposes, so five
distinct inputs from the same chaining key and transcript hash: the application secrets of both directions, the
resumption secret, the confirmation key and the connection id secret. -/
theorem app_secret_labels_nodup :
    ([Purpose.appInitiator, .appResponder, .resumption, .confirm, .cidSecret].map Purpose.label).Nodup := by decide

/-- The derivations from `ck1` and the transcript hash after the reply (`handshake_keys`). -/
theorem handshake_secret_labels_nodup :
    ([Purpose.hsInitiator, .hsResponder].map Purpose.label).Nodup := by decide

/-- The record layer derives three keys from one traffic secret with three distinct labels. -/
theorem record_labels_nodup : ([Purpose.packetKey, .packetIv, .headerKey].map Purpose.label).Nodup := by decide

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
#audit_axioms Vinc.Schedule.ticketInput_injective
#audit_axioms Vinc.Schedule.ticket_psk_binds_credit
#audit_axioms Vinc.Schedule.ticket_ctx_ne_handshake
#audit_axioms Vinc.Schedule.rollInput_injective
#audit_axioms Vinc.Schedule.rollInput_ne_other
#audit_axioms Vinc.Schedule.app_secret_labels_nodup
#audit_axioms Vinc.Schedule.handshake_secret_labels_nodup
#audit_axioms Vinc.Schedule.record_labels_nodup
