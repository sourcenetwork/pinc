import Vinc.Axioms

/-!
# Origin authentication of `vinc-broadcast`

The Lean counterpart of `proofs/tla/BroadcastAuth.tla` (the model of `auth.rs`). The signature is an unforgeable
oracle per identity: the term `(signer, statement)` exists only if the signer published a message with that
statement, and a verifier accepts a message only if the term names the message's origin and the statement the
message presents (`verify`). The hash of the body is collision free, so a body stands for its hash.

The theorems are unbounded: the types of origins, topics, ids, bodies and timestamps are arbitrary.
* `statement_injective`: the bytes `topic | mid | H(body) | ts | isb` that `auth::statement` signs determine every
  part (the topic is the only variable-length part and comes first, so the fixed-size tail fixes where it ends).
* `delivered_exact`: whatever a verifier accepts was published, in every field, by its origin; a relay or a hub that
  holds every signature ever made cannot make another message.
* `mutated_*_refused`: a message that differs from the published one in the topic, the id, the body, the timestamp
  or the flag alone is refused.
-/

namespace Vinc.BroadcastAuth

/-- The bytes a message signs: `topic | mid | H(body) | ts | isb`. -/
def stmtBytes (topic mid hb ts : List UInt8) (isb : Bool) : List UInt8 :=
  topic ++ mid ++ hb ++ ts ++ [if isb then 1 else 0]

private theorem flag_inj {a b : Bool} (h : ([if a then (1 : UInt8) else 0] : List UInt8) = [if b then 1 else 0]) :
    a = b := by
  cases a <;> cases b <;> simp_all

/-- The signed bytes determine the topic, the id, the body hash, the timestamp and the flag, when the id is 8 bytes,
the hash 32 and the timestamp 12 (the sizes of `MID_LEN`, the hash and `TS_LEN`). -/
theorem statement_injective {t t' m m' h h' s s' : List UInt8} {b b' : Bool}
    (hm : m.length = 8) (hm' : m'.length = 8) (hh : h.length = 32) (hh' : h'.length = 32)
    (hs : s.length = 12) (hs' : s'.length = 12)
    (e : stmtBytes t m h s b = stmtBytes t' m' h' s' b') :
    t = t' ∧ m = m' ∧ h = h' ∧ s = s' ∧ b = b' := by
  unfold stmtBytes at e
  obtain ⟨e1, e2⟩ := List.append_inj' e (by simp)
  have hb := flag_inj e2
  obtain ⟨e3, e4⟩ := List.append_inj' e1 (by simp [hs, hs'])
  obtain ⟨e5, e6⟩ := List.append_inj' e3 (by simp [hh, hh'])
  obtain ⟨e7, e8⟩ := List.append_inj' e5 (by simp [hm, hm'])
  exact ⟨e7, e8, e6, e4, hb⟩

variable {O T M B S : Type}

/-- A message: origin, topic, id, body, timestamp and body flag. -/
structure Msg (O T M B S : Type) where
  origin : O
  topic : T
  mid : M
  body : B
  ts : S
  isb : Bool
  deriving DecidableEq

/-- What the signature covers: everything but the origin, which selects the key. -/
structure Stmt (T M B S : Type) where
  topic : T
  mid : M
  body : B
  ts : S
  isb : Bool
  deriving DecidableEq

/-- The statement of a message. -/
def Msg.stmt (m : Msg O T M B S) : Stmt T M B S := ⟨m.topic, m.mid, m.body, m.ts, m.isb⟩

/-- The oracle: the signature terms that exist, one per published message, made by its origin. -/
def sigs (ps : List (Msg O T M B S)) : List (O × Stmt T M B S) := ps.map fun p => (p.origin, p.stmt)

/-- `auth::verify`: the signature is the origin's over exactly the statement the message presents. -/
def verify (m : Msg O T M B S) (sig : O × Stmt T M B S) : Prop := sig.1 = m.origin ∧ sig.2 = m.stmt

/-- The messages that were published: only an origin's own `Publish` step extends the list. -/
inductive Reach : List (Msg O T M B S) → Prop
  | init : Reach []
  | publish (m : Msg O T M B S) {ps} : Reach ps → Reach (m :: ps)

private theorem eq_of_stmt {m p : Msg O T M B S} (ho : p.origin = m.origin) (hs : p.stmt = m.stmt) : p = m := by
  cases m; cases p
  simp only [Msg.stmt, Stmt.mk.injEq] at hs
  simp_all

/-- Whatever a verifier accepts with a signature that exists was published, field for field, by its origin. -/
theorem delivered_exact {ps : List (Msg O T M B S)} (_ : Reach ps) {m : Msg O T M B S} {sig}
    (hsig : sig ∈ sigs ps) (hv : verify m sig) : m ∈ ps := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hsig
  obtain ⟨h1, h2⟩ := hv
  have : p = m := eq_of_stmt h1 h2
  exact this ▸ hp

/-- A relay cannot forge: a message nobody published is refused under every signature that exists. -/
theorem relay_cannot_forge {ps : List (Msg O T M B S)} (r : Reach ps) {m : Msg O T M B S}
    (hm : m ∉ ps) : ∀ sig ∈ sigs ps, ¬ verify m sig :=
  fun _ hs hv => hm (delivered_exact r hs hv)

/-- A message that differs from the only published one in the topic alone is refused. -/
theorem mutated_topic_refused {m : Msg O T M B S} {t' : T} (hne : t' ≠ m.topic) :
    ∀ sig ∈ sigs [m], ¬ verify { m with topic := t' } sig := by
  intro sig hs hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  have : p = m := by simpa using hp
  subst this
  exact hne (by have := hv.2; simp [Msg.stmt] at this; exact this.symm)

/-- ... in the id alone. -/
theorem mutated_mid_refused {m : Msg O T M B S} {x : M} (hne : x ≠ m.mid) :
    ∀ sig ∈ sigs [m], ¬ verify { m with mid := x } sig := by
  intro sig hs hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  have : p = m := by simpa using hp
  subst this
  exact hne (by have := hv.2; simp [Msg.stmt] at this; exact this.symm)

/-- ... in the body alone. -/
theorem mutated_body_refused {m : Msg O T M B S} {x : B} (hne : x ≠ m.body) :
    ∀ sig ∈ sigs [m], ¬ verify { m with body := x } sig := by
  intro sig hs hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  have : p = m := by simpa using hp
  subst this
  exact hne (by have := hv.2; simp [Msg.stmt] at this; exact this.symm)

/-- ... in the timestamp alone. -/
theorem mutated_ts_refused {m : Msg O T M B S} {x : S} (hne : x ≠ m.ts) :
    ∀ sig ∈ sigs [m], ¬ verify { m with ts := x } sig := by
  intro sig hs hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  have : p = m := by simpa using hp
  subst this
  exact hne (by have := hv.2; simp [Msg.stmt] at this; exact this.symm)

/-- ... in the body flag alone. -/
theorem mutated_isb_refused {m : Msg O T M B S} {x : Bool} (hne : x ≠ m.isb) :
    ∀ sig ∈ sigs [m], ¬ verify { m with isb := x } sig := by
  intro sig hs hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  have : p = m := by simpa using hp
  subst this
  exact hne (by have := hv.2; simp [Msg.stmt] at this; exact this.symm)

/-- ... in the origin alone (a signature of another identity does not authenticate the message). -/
theorem mutated_origin_refused [DecidableEq O] {m : Msg O T M B S} {x : O} (hne : x ≠ m.origin) :
    ∀ sig ∈ sigs [m], ¬ verify { m with origin := x } sig := by
  intro sig hs hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  have : p = m := by simpa using hp
  subst this
  exact hne (by have := hv.1; simpa using this.symm)

end Vinc.BroadcastAuth
