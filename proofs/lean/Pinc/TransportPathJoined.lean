import Pinc.TransportPath

/-!
# A reply with a 1-RTT packet behind it, and the responder

The part of the model of `Pinc.TransportPath` that the correction after #399 is about. A datagram whose handshake
packet completes the reply on a path the dial does not hold may carry a 1-RTT packet behind it; `process_payload`
then learns the path from the slot `handle_inner` found at the start of the datagram (none), after `follow_reply`
learnt it. With the look-up of `learn` that learning finds the path: the datagram is the reply alone (`joined_eq`), no
path is held twice (`joined_unique`), and at a full table exactly one path is given up, never the one the session
left (`joined_gives_up_one`). Without the look-up, the rule before the correction, this model found the path held twice
(`noLookup_dup`; `lookup_once` is the same datagram under the corrected rule). The responder learns by the same `learn`
and keeps the table bounded, adds no path twice and keeps its active path (`respRx_*`).
-/

namespace Pinc.TransportPath

/-- The 1-RTT packet behind the reply that established the session learns nothing new: its path is held by then, or
there was no room for it and there still is none. So the joined datagram is the reply alone. -/
theorem joined_eq {np : Nat} {c : C} {pid : Nat} (hi : Inv np c) (hhs : c.hs ≠ .done) (s : Bool) :
    rx false np c pid .auth true s = rx false np c pid .auth false s := by
  have hc1 : Inv np (hsMsg np c pid .auth s) := inv_hsMsg hi s
  have hdone : (hsMsg np c pid .auth s).hs = .done := by
    rw [hsMsg_auth hhs]; exact (follow_keeps np _).1
  have hkeep : (learn np (hsMsg np c pid .auth s).t (hsMsg np c pid .auth s).act pid).1 =
      (hsMsg np c pid .auth s).t := by
    cases hfind : find np (hsMsg np c pid .auth s).t pid with
    | some _ => rw [learn_found hfind]
    | none =>
      rw [learn_fresh hfind]
      have ha := rx_auth (pid := pid) hi hhs s
      rw [rx_plain] at ha
      by_cases room : (find np c.t pid).isSome ∨ (slot np c.t c.act).isSome
      · obtain ⟨p, hp, hpid, _⟩ := ha.2.1 room
        obtain ⟨k, hk⟩ := first_isSome (f := fun i => holds pid ((hsMsg np c pid .auth s).t i)) hc1.act_lt
          (by simp [hp, holds, hpid])
        unfold find at hfind
        rw [hk] at hfind
        cases hfind
      · have hf : find np c.t pid = none := by
          cases h : find np c.t pid with
          | none => rfl
          | some _ => exact absurd (Or.inl (by simp [h])) room
        have hs : slot np c.t c.act = none := by
          cases h : slot np c.t c.act with
          | none => rfl
          | some _ => exact absurd (Or.inr (by simp [h])) room
        obtain ⟨ht, hact⟩ := ha.2.2 hf hs
        rw [ht, hact]
        unfold learnNew
        rw [hs]
  rw [rx_plain]
  unfold rx
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.true_and, hdone, decide_true]
  split
  · rw [hkeep, ← hdone]
  · rfl

/-- With the look-up no datagram makes a path held twice, a reply with a 1-RTT packet behind it included. -/
theorem joined_unique {np : Nat} {c : C} {pid : Nat} {k : Kind} (hi : Inv np c) (old coal s : Bool) :
    Unique (rx old np c pid k coal s).t :=
  (inv_rx hi old coal s).unique

/-- What `follow` does to the table when the reply's path is learnt in slot `i`. -/
theorem follow_slots {np : Nat} {c : C} {pid i : Nat} (hrf : c.rf = some pid) (hf : find np c.t pid = none)
    (hs : slot np c.t c.act = some i) (hia : i ≠ c.act) :
    (follow np c).act = i ∧ (follow np c).t i = some ⟨pid, true, .direct⟩ ∧
      (follow np c).t c.act = (c.t c.act).map (fun p => { p with v := keptV c.t c.act }) ∧
      ∀ j, j ≠ i → j ≠ c.act → (follow np c).t j = c.t j := by
  have hl : (learnNew np c.t c.act pid).2 = some i := by rw [learnNew_snd, hs]
  rw [follow_learnt hrf hf hl, ite_eq_right hia]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · show setV (setV (learnNew np c.t c.act pid).1 c.act (keptV c.t c.act)) i true i = _
    rw [setV_at, setV_other _ _ _ hia, learnNew_at hl]
    rfl
  · show setV (setV (learnNew np c.t c.act pid).1 c.act (keptV c.t c.act)) i true c.act = _
    rw [setV_other _ _ _ (Ne.symm hia), setV_at,
      learnNew_other (by rw [hl]; intro e; exact hia (Option.some.inj e))]
  · intro j hji hja
    show setV (setV (learnNew np c.t c.act pid).1 c.act (keptV c.t c.act)) i true j = _
    rw [setV_other _ _ _ hji, setV_other _ _ _ hja,
      learnNew_other (by rw [hl]; intro e; exact hji (Option.some.inj e).symm)]

/-- A reply with a 1-RTT packet behind it, on a path the dial does not hold, that joins at slot `i`: the session is
on it, the path it left is held (no longer validated), and every other slot is as it was, so at a full table exactly
one path is given up, the one in slot `i`, never the one the session left. -/
theorem joined_gives_up_one {np : Nat} {c : C} {pid i : Nat} (hi : Inv np c) (hhs : c.hs ≠ .done)
    (hf : find np c.t pid = none) (hs : slot np c.t c.act = some i) (s : Bool) :
    (rx false np c pid .auth true s).act = i ∧ (rx false np c pid .auth true s).t i = some ⟨pid, true, .direct⟩ ∧
      (rx false np c pid .auth true s).t c.act = (c.t c.act).map (fun p => { p with v := keptV c.t c.act }) ∧
      ∀ j, j ≠ i → j ≠ c.act → (rx false np c pid .auth true s).t j = c.t j := by
  obtain ⟨pa, hpa, _⟩ := hi.active
  have hia : i ≠ c.act := slot_ne_act hpa hs
  rw [joined_eq hi hhs, rx_plain, hsMsg_auth hhs]
  exact follow_slots (c := { c with rf := some pid, hs := .done, pend := none, smp := c.smp || s }) rfl hf hs hia

/-- The rule before the correction (found by this model): the same datagram, the dial on path 1 with two free slots
and the resume Reply on path 9, leaves path 9 held twice. -/
theorem noLookup_dup :
    (rxNoLook 3 (dial 1) 9 .auth true false).t 1 = some ⟨9, true, .direct⟩ ∧
      (rxNoLook 3 (dial 1) 9 .auth true false).t 2 = some ⟨9, false, .direct⟩ ∧
      (rxNoLook 3 (dial 1) 9 .auth true false).act = 1 ∧
      uniqueB 3 (rxNoLook 3 (dial 1) 9 .auth true false).t = false := by
  decide

/-- The corrected rule on that datagram holds path 9 once. -/
theorem lookup_once :
    (rx false 3 (dial 1) 9 .auth true false).t 1 = some ⟨9, true, .direct⟩ ∧
      (rx false 3 (dial 1) 9 .auth true false).t 2 = none ∧
      uniqueB 3 (rx false 3 (dial 1) 9 .auth true false).t = true := by
  decide

/-! ## The responder: the same learning keeps the bound -/

theorem respRx_cases (np : Nat) (c : C) (pid : Nat) (est : Bool) :
    ∃ c1 : C, (c1 = c ∨ (find np c.t pid = none ∧ c1 = { c with t := (learn np c.t c.act pid).1 })) ∧
      (respRx np c pid est = c1 ∨ respRx np c pid est = { c1 with hs := .done, t := setV c1.t c1.act true }) := by
  unfold respRx
  dsimp only
  split
  · rename_i h
    refine ⟨_, Or.inr ⟨h.1, rfl⟩, ?_⟩
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · refine ⟨_, Or.inl rfl, ?_⟩
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem respRx_bounded {np : Nat} {c : C} {pid : Nat} (hb : Bounded np c.t) (est : Bool) :
    Bounded np (respRx np c pid est).t := by
  obtain ⟨c1, h1, h2⟩ := respRx_cases np c pid est
  have hb1 : Bounded np c1.t := by
    rcases h1 with h | ⟨_, h⟩ <;> subst h
    · exact hb
    · exact learn_bounded hb
  rcases h2 with h | h <;> rw [h]
  · exact hb1
  · exact bounded_setV hb1 _ _

theorem respRx_unique {np : Nat} {c : C} {pid : Nat} (hb : Bounded np c.t) (hu : Unique c.t) (est : Bool) :
    Unique (respRx np c pid est).t := by
  obtain ⟨c1, h1, h2⟩ := respRx_cases np c pid est
  have hu1 : Unique c1.t := by
    rcases h1 with h | ⟨hf, h⟩ <;> subst h
    · exact hu
    · exact learn_unique hb hu
  rcases h2 with h | h <;> rw [h]
  · exact hu1
  · exact unique_setV hu1 _ _

/-- The responder never gives up its active path: the slot keeps its path's id and stays the active one. -/
theorem respRx_active {np : Nat} {c : C} {pid : Nat} {p : P} (hp : c.t c.act = some p) (est : Bool) :
    idOf (respRx np c pid est).t c.act = some p.id ∧ (respRx np c pid est).act = c.act := by
  obtain ⟨c1, h1, h2⟩ := respRx_cases np c pid est
  have ha1 : c1.t c1.act = some p ∧ c1.act = c.act := by
    rcases h1 with h | ⟨_, h⟩ <;> subst h
    · exact ⟨hp, rfl⟩
    · exact ⟨learn_keeps_active hp, rfl⟩
  rcases h2 with h | h <;> rw [h]
  · exact ⟨by rw [ha1.2.symm]; simp [idOf, ha1.1], ha1.2⟩
  · refine ⟨?_, ha1.2⟩
    show idOf (setV c1.t c1.act true) c.act = some p.id
    rw [setV_idOf, ← ha1.2]; simp [idOf, ha1.1]

#audit_axioms joined_eq
#audit_axioms joined_unique
#audit_axioms joined_gives_up_one
#audit_axioms noLookup_dup
#audit_axioms lookup_once
#audit_axioms respRx_bounded
#audit_axioms respRx_unique
#audit_axioms respRx_active

end Pinc.TransportPath
