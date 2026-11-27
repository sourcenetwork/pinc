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
and keeps the table bounded, adds no path twice and keeps its active path (`respRx_*`). A resumed responder validates
nothing at the Hello (`resume_proves_nothing`); the dialer's first 1-RTT packet validates the path its one Reply went
to (`confirm_validates`) and no other (`confirm_only`), a 0-RTT packet validates nothing (`confirm_early`), and a Reply
resent on another path gives the proof up (`resend_one_path`).
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
    (follow np c).act = i ∧ (follow np c).t i = some ⟨pid, false⟩ ∧
      (follow np c).t c.act = (c.t c.act).map (fun p => { p with v := false }) ∧
      ∀ j, j ≠ i → j ≠ c.act → (follow np c).t j = c.t j := by
  have hl : (learnNew np c.t c.act pid).2 = some i := by rw [learnNew_snd, hs]
  rw [follow_learnt hrf hf hl, ite_eq_right hia]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · show setV (setV (learnNew np c.t c.act pid).1 c.act false) i false i = _
    rw [setV_at, setV_other _ _ _ hia, learnNew_at hl]
    rfl
  · show setV (setV (learnNew np c.t c.act pid).1 c.act false) i false c.act = _
    rw [setV_other _ _ _ (Ne.symm hia), setV_at,
      learnNew_other (by rw [hl]; intro e; exact hia (Option.some.inj e))]
  · intro j hji hja
    show setV (setV (learnNew np c.t c.act pid).1 c.act false) i false j = _
    rw [setV_other _ _ _ hji, setV_other _ _ _ hja,
      learnNew_other (by rw [hl]; intro e; exact hji (Option.some.inj e).symm)]

/-- A reply with a 1-RTT packet behind it, on a path the dial does not hold, that joins at slot `i`: the session is
on it (unvalidated: the reply alone proves nothing about it), the path it left is held (no longer validated), and every other slot is as it was, so at a full table exactly
one path is given up, the one in slot `i`, never the one the session left. -/
theorem joined_gives_up_one {np : Nat} {c : C} {pid i : Nat} (hi : Inv np c) (hhs : c.hs ≠ .done)
    (hf : find np c.t pid = none) (hs : slot np c.t c.act = some i) (s : Bool) :
    (rx false np c pid .auth true s).act = i ∧ (rx false np c pid .auth true s).t i = some ⟨pid, false⟩ ∧
      (rx false np c pid .auth true s).t c.act = (c.t c.act).map (fun p => { p with v := false }) ∧
      ∀ j, j ≠ i → j ≠ c.act → (rx false np c pid .auth true s).t j = c.t j := by
  obtain ⟨pa, hpa⟩ := hi.held
  have hia : i ≠ c.act := slot_ne_act hpa hs
  rw [joined_eq hi hhs, rx_plain, hsMsg_auth hhs]
  exact follow_slots (c := { c with rf := some pid, hs := .done, pend := none, smp := c.smp || s }) rfl hf hs hia

/-- The rule before the correction (found by this model): the same datagram, the dial on path 1 with two free slots
and the resume Reply on path 9, leaves path 9 held twice. -/
theorem noLookup_dup :
    (rxNoLook 3 (dial 1) 9 .auth true false).t 1 = some ⟨9, false⟩ ∧
      (rxNoLook 3 (dial 1) 9 .auth true false).t 2 = some ⟨9, false⟩ ∧
      (rxNoLook 3 (dial 1) 9 .auth true false).act = 1 ∧
      uniqueB 3 (rxNoLook 3 (dial 1) 9 .auth true false).t = false := by
  decide

/-- The corrected rule on that datagram holds path 9 once. -/
theorem lookup_once :
    (rx false 3 (dial 1) 9 .auth true false).t 1 = some ⟨9, false⟩ ∧
      (rx false 3 (dial 1) 9 .auth true false).t 2 = none ∧
      uniqueB 3 (rx false 3 (dial 1) 9 .auth true false).t = true := by
  decide

/-! ## The responder: the same learning keeps the bound -/

theorem respRx_cases (np : Nat) (c : C) (pid : Nat) (m : RMsg) :
    ∃ c1 : C, (c1 = c ∨ (find np c.t pid = none ∧ c1 = { c with t := (learn np c.t c.act pid).1 })) ∧
      (respRx np c pid m = c1 ∨ (m = .finish ∧ respRx np c pid m = { c1 with hs := .done, t := setV c1.t c1.act true }) ∨
        (m = .resume ∧ respRx np c pid m = { c1 with hs := .done, rp := idOf c1.t c1.act })) := by
  unfold respRx
  dsimp only
  split
  · rename_i h
    refine ⟨_, Or.inr ⟨h.1, rfl⟩, ?_⟩
    split
    · rename_i hm
      split
      · rename_i hfin
        exact Or.inr (Or.inl ⟨hfin, rfl⟩)
      · rename_i hfin
        refine Or.inr (Or.inr ⟨?_, rfl⟩)
        cases m with
        | part => exact absurd rfl hm.1
        | finish => exact absurd rfl hfin
        | resume => rfl
    · exact Or.inl rfl
  · refine ⟨_, Or.inl rfl, ?_⟩
    split
    · rename_i hm
      split
      · rename_i hfin
        exact Or.inr (Or.inl ⟨hfin, rfl⟩)
      · rename_i hfin
        refine Or.inr (Or.inr ⟨?_, rfl⟩)
        cases m with
        | part => exact absurd rfl hm.1
        | finish => exact absurd rfl hfin
        | resume => rfl
    · exact Or.inl rfl

theorem respRx_bounded {np : Nat} {c : C} {pid : Nat} (hb : Bounded np c.t) (m : RMsg) :
    Bounded np (respRx np c pid m).t := by
  obtain ⟨c1, h1, h2⟩ := respRx_cases np c pid m
  have hb1 : Bounded np c1.t := by
    rcases h1 with h | ⟨_, h⟩ <;> subst h
    · exact hb
    · exact learn_bounded hb
  rcases h2 with h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h]
  · exact hb1
  · exact bounded_setV hb1 _ _
  · exact hb1

theorem respRx_unique {np : Nat} {c : C} {pid : Nat} (hb : Bounded np c.t) (hu : Unique c.t) (m : RMsg) :
    Unique (respRx np c pid m).t := by
  obtain ⟨c1, h1, h2⟩ := respRx_cases np c pid m
  have hu1 : Unique c1.t := by
    rcases h1 with h | ⟨hf, h⟩ <;> subst h
    · exact hu
    · exact learn_unique hb hu
  rcases h2 with h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h]
  · exact hu1
  · exact unique_setV hu1 _ _
  · exact hu1

/-- The responder never gives up its active path: the slot keeps its path's id and stays the active one. -/
theorem respRx_active {np : Nat} {c : C} {pid : Nat} {p : P} (hp : c.t c.act = some p) (m : RMsg) :
    idOf (respRx np c pid m).t c.act = some p.id ∧ (respRx np c pid m).act = c.act := by
  obtain ⟨c1, h1, h2⟩ := respRx_cases np c pid m
  have ha1 : c1.t c1.act = some p ∧ c1.act = c.act := by
    rcases h1 with h | ⟨_, h⟩ <;> subst h
    · exact ⟨hp, rfl⟩
    · exact ⟨learn_keeps_active hp, rfl⟩
  rcases h2 with h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h]
  · exact ⟨by rw [ha1.2.symm]; simp [idOf, ha1.1], ha1.2⟩
  · refine ⟨?_, ha1.2⟩
    show idOf (setV c1.t c1.act true) c.act = some p.id
    rw [setV_idOf, ← ha1.2]; simp [idOf, ha1.1]
  · exact ⟨by rw [ha1.2.symm]; simp [idOf, ha1.1], ha1.2⟩

/-- A slot that learning leaves validated was validated before: a learnt path joins unvalidated. -/
theorem learn_valid {np : Nat} {t : T} {act pid j : Nat} {p : P} (h : (learn np t act pid).1 j = some p)
    (hv : p.v = true) : t j = some p := by
  cases hf : find np t pid with
  | some _ => rw [learn_found hf] at h; exact h
  | none =>
    rw [learn_fresh hf] at h
    by_cases hj : (learnNew np t act pid).2 = some j
    · rw [learnNew_at hj] at h
      cases h
      simp at hv
    · rw [learnNew_other hj] at h; exact h

/-- A resumption Hello validates no path the responder did not hold validated before it: anyone who saw the Hello can
send a copy of it from any source. -/
theorem resume_proves_nothing {np : Nat} {c : C} {pid j : Nat} {p : P}
    (h : (respRx np c pid .resume).t j = some p) (hv : p.v = true) : c.t j = some p := by
  obtain ⟨c1, h1, h2⟩ := respRx_cases np c pid .resume
  have hc1 : c1.t j = some p → c.t j = some p := by
    intro hj
    rcases h1 with e | ⟨_, e⟩ <;> subst e
    · exact hj
    · exact learn_valid hj hv
  rcases h2 with e | ⟨hfin, _⟩ | ⟨_, e⟩
  · rw [e] at h; exact hc1 h
  · cases hfin
  · rw [e] at h; exact hc1 h

/-- What the confirmation point does to the table: nothing, or it validates one slot. -/
theorem confirm_t (np : Nat) (c : C) (k : Pkt) :
    (confirm np c k).t = c.t ∨ ∃ i, (confirm np c k).t = setV c.t i true := by
  cases k with
  | early => exact Or.inl rfl
  | app =>
    cases hx : c.rp with
    | none => exact Or.inl (by simp [confirm, hx])
    | some x =>
      cases hf : find np c.t x with
      | none => exact Or.inl (by simp [confirm, hx, hf])
      | some i => exact Or.inr ⟨i, by simp [confirm, hx, hf]⟩

/-- A 0-RTT packet proves nothing. -/
theorem confirm_early (np : Nat) (c : C) : confirm np c .early = c := rfl

/-- The dialer's first 1-RTT packet validates the path the proof names, if it is still held, wherever it came. -/
theorem confirm_validates {np : Nat} {c : C} {x i : Nat} (hx : c.rp = some x) (hf : find np c.t x = some i) :
    ∃ p, (confirm np c .app).t i = some p ∧ p.id = x ∧ p.v = true ∧ (confirm np c .app).rp = none := by
  obtain ⟨_, p, hp, hpid⟩ := find_some hf
  have he : confirm np c .app = { c with t := setV c.t i true, rp := none } := by simp [confirm, hx, hf]
  rw [he]
  refine ⟨{ p with v := true }, ?_, hpid, rfl, rfl⟩
  show setV c.t i true i = _
  rw [setV_at, hp]
  rfl

/-- ... and no other: a slot it leaves validated was validated before, or holds the path the proof named. -/
theorem confirm_only {np : Nat} {c : C} {k : Pkt} {j : Nat} {p : P} (h : (confirm np c k).t j = some p)
    (hv : p.v = true) : c.t j = some p ∨ c.rp = some p.id := by
  cases k with
  | early => exact Or.inl h
  | app =>
    cases hx : c.rp with
    | none =>
      have he : confirm np c .app = c := by simp [confirm, hx]
      rw [he] at h; exact Or.inl h
    | some x =>
      cases hf : find np c.t x with
      | none =>
        have he : confirm np c .app = { c with rp := none } := by simp [confirm, hx, hf]
        rw [he] at h; exact Or.inl h
      | some i =>
        have he : confirm np c .app = { c with t := setV c.t i true, rp := none } := by simp [confirm, hx, hf]
        rw [he] at h
        change setV c.t i true j = some p at h
        by_cases hji : j = i
        · subst hji
          obtain ⟨_, q, hq, hqid⟩ := find_some hf
          rw [setV_at, hq] at h
          cases h
          exact Or.inr (by simp [hqid])
        · rw [setV_other _ _ _ hji] at h; exact Or.inl h

theorem confirm_bounded {np : Nat} {c : C} (hb : Bounded np c.t) (k : Pkt) : Bounded np (confirm np c k).t := by
  rcases confirm_t np c k with e | ⟨i, e⟩ <;> rw [e]
  · exact hb
  · exact bounded_setV hb _ _

theorem confirm_unique {np : Nat} {c : C} (hu : Unique c.t) (k : Pkt) : Unique (confirm np c k).t := by
  rcases confirm_t np c k with e | ⟨i, e⟩ <;> rw [e]
  · exact hu
  · exact unique_setV hu _ _

/-- A proof still owed after a resend names the active path the Reply left on. -/
theorem resend_one_path {c : C} {x : Nat} (h : (resend c).rp = some x) : idOf c.t c.act = some x := by
  unfold resend at h
  split at h
  · simp at h
  · rename_i hn
    by_cases he : c.rp = idOf c.t c.act
    · rw [← he]; exact h
    · exact absurd ⟨by rw [h]; rfl, he⟩ hn

#audit_axioms joined_eq
#audit_axioms joined_unique
#audit_axioms joined_gives_up_one
#audit_axioms noLookup_dup
#audit_axioms lookup_once
#audit_axioms respRx_bounded
#audit_axioms respRx_unique
#audit_axioms respRx_active
#audit_axioms resume_proves_nothing
#audit_axioms confirm_early
#audit_axioms confirm_validates
#audit_axioms confirm_only
#audit_axioms resend_one_path
#audit_axioms confirm_bounded
#audit_axioms confirm_unique

end Pinc.TransportPath
