import Pinc.ReconcileFrames

/-!
# Reconcile rounds: every session ends by the bound, and a refused message ends the session

Task property 1 against a dishonest or garbage peer, on the byte machine, for every input:

* `initHandle_rounds`, `respHandle_rounds`: a message that a handler accepts counts one round and the round was within
  `max_rounds` (`Core.round` refuses the first round past it); the limits never change in a session.
* `initServed_le`, `respServed_le`: so a peer, honest or not, can have at most `max_rounds` messages accepted by an
  initiator that has been started (and `max_rounds + 1` by a responder, whose first message opens the session): after
  that every message is refused with `Err.tooManyRounds`.
* `initiator_refused_dead`, `responder_refused_dead`, `resume_refused_dead`: a refused message ends the session of the
  object that refused it (`afterErr`), and the next call is refused with `Reason::State`, so a caller that ignores the
  error cannot go on with a half-merged report.
-/

namespace Pinc.Reconcile

/-- The limits, the round counter and the role of a core. -/
def Kp (c c' : Core) : Prop := c'.lim = c.lim ∧ c'.rounds = c.rounds ∧ c'.init = c.init

theorem Kp.refl (c : Core) : Kp c c := ⟨rfl, rfl, rfl⟩
theorem Kp.trans {a b c : Core} (h1 : Kp a b) (h2 : Kp b c) : Kp a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩
theorem Keeps.kp {c₀ c c' : Core} (h : Keeps c₀ c') (hl : c₀.lim = c.lim) (hr : c₀.rounds = c.rounds)
    (hi : c₀.init = c.init) : Kp c c' := ⟨h.2.1.trans hl, h.2.2.2.2.2.1.trans hr, h.2.2.2.1.trans hi⟩

theorem pushFrame_kp (c : Core) (rest : List Nat) (left : Nat) : Ok (fun c' => Kp c c') (c.pushFrame rest left) := by
  unfold Core.pushFrame
  split
  · exact Ok.throw _
  · exact Ok.pure _ ⟨rfl, rfl, rfl⟩

theorem resume_kp (o : Oracle) (S : List Item) (c : Core) : Ok (fun p => Kp c p.1) (c.resume o S) := by
  unfold Core.resume
  cases hf : c.frames with
  | nil => exact Ok.throw _
  | cons f tl =>
    refine Ok.bind (P := fun p : Core × List Nat × Nat => Kp c p.1) ?_ ?_
    · refine Ok.mono (answerLoop_keeps o S f.left _ f.buf) ?_
      intro p hp
      exact Keeps.kp hp rfl rfl rfl
    · rintro ⟨c2, rest, left⟩ hc2
      simp only at hc2
      refine Ok.ite (fun _ => Ok.ite (fun _ => Ok.throw _) (fun _ => Ok.pure _ ?_)) (fun _ => Ok.pure _ ?_)
      · exact Kp.trans hc2 ⟨rfl, rfl, rfl⟩
      · exact Kp.trans hc2 ⟨rfl, rfl, rfl⟩

theorem resumeLoop_kp (o : Oracle) (S : List Item) :
    ∀ (f : Nat) (c : Core), Ok (fun c' => Kp c c') (resumeLoop o S f c)
  | 0, c => Ok.pure _ (Kp.refl c)
  | f + 1, c => by
    unfold resumeLoop
    refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure _ (Kp.refl c))
    refine Ok.bind (P := fun p : Core × Bool => Kp c p.1) (resume_kp o S c) ?_
    rintro ⟨c', adv⟩ hc'
    refine Ok.ite (fun _ => Ok.mono (resumeLoop_kp o S f c') fun x hx => Kp.trans hc' hx) (fun _ => Ok.pure _ hc')

theorem turn_kp (o : Oracle) (S : List Item) (c : Core) (r : List Nat) (np : Nat) :
    Ok (fun p => Kp c p.1) (c.turn o S r np) := by
  unfold Core.turn
  dsimp only
  refine Ok.bind (P := fun p : Core × List Nat × Nat => Kp c p.1) ?_ ?_
  · exact Ok.mono (answerLoop_keeps o S np _ r) fun p hp => Keeps.kp hp rfl rfl rfl
  · rintro ⟨c1, rest, left⟩ h1
    simp only at h1 ⊢
    have tail : ∀ c2 : Core, Kp c c2 →
        Ok (fun p : Core × Ans => Kp c p.1)
          (resumeLoop o S (c2.frames.foldl (fun s f => s + f.left + 1) 1) c2 >>= fun c3 => pure (c3, c3.ans)) :=
      fun c2 h2 => Ok.bind (P := fun c3 : Core => Kp c c3) (Ok.mono (resumeLoop_kp o S _ c2) fun x hx => Kp.trans h2 hx)
        (fun c3 h3 => Ok.pure _ h3)
    exact Ok.ite (fun _ => Ok.bind (P := fun c2 : Core => Kp c c2) (Ok.mono (pushFrame_kp c1 rest left) fun x hx => Kp.trans h1 hx)
        (fun c2 h2 => tail c2 h2)) (fun _ => Ok.ite (fun _ => Ok.bind (P := fun _ => False) (Ok.throw _)
        (fun _ ha => ha.elim)) (fun _ => Ok.bind (P := fun c2 : Core => Kp c c2) (Ok.pure _ h1)
        (fun c2 h2 => tail c2 h2)))

macro "okp" : tactic => `(tactic| first
  | (refine Ok.bind_any (fun _ => ?_))
  | (refine Ok.ite (fun _ => ?_) (fun _ => ?_))
  | (apply Ok.pure; first | exact Kp.refl _ | exact ⟨rfl, rfl, rfl⟩ | (split <;> exact ⟨rfl, rfl, rfl⟩))
  | exact Ok.throw _
  | split
  | (dsimp only [letFun])
  | (dsimp only))

theorem root_kp (o : Oracle) (S : List Item) (c : Core) : Ok (fun p => Kp c p.1) (c.root o S) := by
  unfold Core.root
  repeat' okp

theorem checkMsg_kp (o : Oracle) (S : List Item) (c : Core) : Ok (fun p => Kp c p.1) (c.checkMsg o S) := by
  unfold Core.checkMsg
  repeat' okp

theorem restartExact_kp (o : Oracle) (S : List Item) (c : Core) : Ok (fun p => Kp c p.1) (c.restartExact o S) := by
  unfold Core.restartExact
  dsimp only
  refine Ok.bind (P := fun p : Core × Nat => Kp c p.1) (Ok.mono (root_kp o S _) fun p hp => hp) ?_
  rintro ⟨c1, cnt⟩ h1
  exact Ok.bind_any (fun _ => Ok.pure _ h1)

theorem round_rounds (c : Core) :
    Ok (fun c' => c'.lim = c.lim ∧ c'.rounds = c.rounds + 1 ∧ c.rounds + 1 ≤ c.lim.maxRounds ∧ c'.init = c.init) c.round := by
  unfold Core.round; split
  · exact Ok.throw _
  · next h => exact Ok.pure _ ⟨rfl, rfl, by omega, rfl⟩

theorem close_kp (o : Oracle) (S : List Item) (s : Initiator) (pd : Bool) :
    Ok (fun p => Kp s.core p.2.2.core) (s.close o S pd) := by
  unfold Initiator.close
  dsimp only
  refine Ok.ite (fun _ => Ok.pure _ (Kp.refl _)) (fun _ => Ok.ite (fun _ => ?_) (fun _ => ?_))
  · exact Ok.bind (P := fun p : Core × List Nat => Kp s.core p.1) (checkMsg_kp o S _)
      (fun p hp => Ok.pure _ hp)
  · exact Ok.ite (fun _ => Ok.pure _ (Kp.refl _)) (fun _ => Ok.bind_any (fun _ => Ok.pure _ (Kp.refl _)))

/-- One handled message of the initiator: the limits stay, the round counter goes up by one, and the round was within
`max_rounds`. -/
theorem initHandle_rounds (o : Oracle) (S : List Item) (s : Initiator) (msg : List Nat) :
    Ok (fun p => p.2.2.core.lim = s.core.lim ∧ p.2.2.core.rounds = s.core.rounds + 1 ∧
        s.core.rounds + 1 ≤ s.core.lim.maxRounds) (s.handle o S msg) := by
  unfold Initiator.handle
  dsimp only
  refine Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)
  refine Ok.bind (P := fun c : Core => c.lim = s.core.lim ∧ c.rounds = s.core.rounds + 1 ∧
    s.core.rounds + 1 ≤ s.core.lim.maxRounds ∧ c.init = s.core.init) (round_rounds _) ?_
  intro c hc
  refine Ok.bind_any (fun body => Ok.bind_any (fun pr => ?_))
  obtain ⟨⟨np, more⟩, r⟩ := pr
  dsimp only
  refine Ok.bind (P := fun p : Core × Ans => Kp c p.1) (turn_kp o S c r np) ?_
  rintro ⟨c2, ans⟩ h2
  simp only at h2 ⊢
  have h2' : c2.lim = s.core.lim ∧ c2.rounds = s.core.rounds + 1 ∧ s.core.rounds + 1 ≤ s.core.lim.maxRounds :=
    ⟨h2.1.trans hc.1, h2.2.1.trans hc.2.1, hc.2.2.1⟩
  refine Ok.ite (fun _ => Ok.ite (fun _ => Ok.pure _ h2') (fun _ => Ok.pure _ h2')) (fun _ => ?_)
  refine Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)
  refine Ok.ite (fun _ => Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)) (fun _ => ?_)
  · refine Ok.bind (P := fun p : Core × List Nat => Kp c2 p.1) (restartExact_kp o S c2) ?_
    rintro ⟨c3, m⟩ h3
    exact Ok.pure _ ⟨h3.1.trans h2'.1, h3.2.1.trans h2'.2.1, h2'.2.2⟩
  · refine Ok.ite (fun _ => Ok.bind_any (fun _ => Ok.pure _ h2')) (fun _ => Ok.ite (fun _ => Ok.bind_any (fun _ => Ok.pure _ h2')) (fun _ => ?_))
    refine Ok.mono (close_kp o S { s with core := c2 } _) ?_
    intro p hp
    exact ⟨hp.1.trans h2'.1, hp.2.1.trans h2'.2.1, h2'.2.2⟩

theorem coldChunk_kp (S : List Item) (c : Core) : Ok (fun p => Kp c p.1) (c.coldChunk S) := by
  unfold Core.coldChunk
  repeat' okp

theorem respRun_rounds (o : Oracle) (S : List Item) (s : Responder) (r : List Nat) :
    Ok (fun p => p.2.2.core.lim = s.core.lim ∧ p.2.2.core.rounds = s.core.rounds + 1 ∧
        s.core.rounds + 1 ≤ s.core.lim.maxRounds ∧ p.2.2.side ≠ .fresh) (s.run o S r) := by
  unfold Responder.run
  dsimp only
  refine Ok.bind (P := fun c : Core => c.lim = s.core.lim ∧ c.rounds = s.core.rounds + 1 ∧
    s.core.rounds + 1 ≤ s.core.lim.maxRounds ∧ c.init = s.core.init) (round_rounds _) ?_
  intro c hc
  refine Ok.bind_any (fun pr => ?_)
  obtain ⟨⟨np, more⟩, r1⟩ := pr
  dsimp only
  refine Ok.bind (P := fun p : Core × Ans => Kp c p.1) (turn_kp o S c r1 np) ?_
  rintro ⟨c2, ans⟩ h2
  simp only at h2 ⊢
  have h2' : c2.lim = s.core.lim ∧ c2.rounds = s.core.rounds + 1 ∧ s.core.rounds + 1 ≤ s.core.lim.maxRounds :=
    ⟨h2.1.trans hc.1, h2.2.1.trans hc.2.1, hc.2.2.1⟩
  refine Ok.ite (fun _ => Ok.bind_any (fun _ => Ok.pure _ ⟨h2'.1, h2'.2.1, h2'.2.2, by simp⟩))
    (fun _ => Ok.ite (fun _ => Ok.bind_any (fun _ => Ok.pure _ ⟨h2'.1, h2'.2.1, h2'.2.2, by simp⟩)) (fun _ => ?_))
  exact Ok.ite (fun _ => Ok.pure _ ⟨h2'.1, h2'.2.1, h2'.2.2, by simp⟩)
    (fun _ => Ok.bind_any (fun _ => Ok.pure _ ⟨h2'.1, h2'.2.1, h2'.2.2, by simp⟩))

theorem respResume_kp (o : Oracle) (S : List Item) (s : Responder) :
    Ok (fun p => p.2.2.core.lim = s.core.lim ∧ p.2.2.core.rounds = s.core.rounds ∧ p.2.2.side ≠ .fresh) (s.resume o S) := by
  intro v hv
  unfold Responder.resume at hv
  split at hv
  · cases hv
  · next hne =>
    have hcold : s.side = .cold := by simpa using hne
    cases hc : s.core.coldChunk S with
    | error e => simp [hc] at hv
    | ok q =>
      obtain ⟨c, m, last⟩ := q
      have hk := coldChunk_kp S s.core (c, m, last) hc
      simp only [hc] at hv
      split at hv
      · cases hv; exact ⟨hk.1, hk.2.1, by simp⟩
      · cases hv; exact ⟨hk.1, hk.2.1, by simp [hcold]⟩

/-- One handled message of the responder: the limits stay, the round counter is at most `max_rounds`, it goes up by one
after the first message, and the responder is no longer fresh. -/
theorem respHandle_rounds (o : Oracle) (S : List Item) (s : Responder) (msg : List Nat) :
    Ok (fun p => p.2.2.core.lim = s.core.lim ∧ p.2.2.core.rounds ≤ s.core.lim.maxRounds ∧ p.2.2.side ≠ .fresh ∧
        (s.side ≠ .fresh → p.2.2.core.rounds = s.core.rounds + 1 ∧ s.core.rounds + 1 ≤ s.core.lim.maxRounds))
      (s.handle o S msg) := by
  unfold Responder.handle
  dsimp only
  refine Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)
  refine Ok.bind_any (fun body => ?_)
  refine Ok.ite (fun hf => ?_) (fun hf => ?_)
  · refine Ok.bind_any (fun pr => ?_)
    obtain ⟨l, r1⟩ := pr
    dsimp only
    refine Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)
    refine Ok.bind_any (fun pr => ?_)
    obtain ⟨u, r2⟩ := pr
    dsimp only
    refine Ok.bind_any (fun pr => ?_)
    obtain ⟨na, r3⟩ := pr
    dsimp only
    have hfresh : s.side = .fresh := by simpa using hf
    refine Ok.ite (fun _ => ?_) (fun _ => ?_)
    · refine Ok.mono (respResume_kp o S _) ?_
      intro p hp
      refine ⟨hp.1, ?_, hp.2.2, fun h => absurd hfresh h⟩
      rw [hp.2.1]; simp [Core.clear]
    · refine Ok.mono (respRun_rounds o S _ r3) ?_
      intro p hp
      refine ⟨hp.1, ?_, hp.2.2.2, fun h => absurd hfresh h⟩
      rw [hp.2.1]; simp [Core.clear]; exact hp.2.2.1
  · have hopen : s.side ≠ .fresh := by simpa using hf
    refine Ok.mono (respRun_rounds o S s body) ?_
    intro p hp
    exact ⟨hp.1, hp.2.1 ▸ hp.2.2.1, hp.2.2.2, fun _ => ⟨hp.2.1, hp.2.2.1⟩⟩

/-- The number of messages an initiator accepts, from the first one to the first refusal. -/
def initServed (o : Oracle) (S : List Item) : Initiator → List (List Nat) → Nat
  | _, [] => 0
  | s, m :: ms =>
    match s.handle o S m with
    | .ok (_, _, s') => initServed o S s' ms + 1
    | .error _ => 0

/-- At most `max_rounds` messages (less the rounds already counted) are accepted by an initiator, whatever they hold. -/
theorem initServed_le (o : Oracle) (S : List Item) :
    ∀ (ms : List (List Nat)) (s : Initiator), initServed o S s ms ≤ s.core.lim.maxRounds - s.core.rounds
  | [], s => by simp [initServed]
  | m :: ms, s => by
    unfold initServed
    cases h : s.handle o S m with
    | error e => simp
    | ok q =>
      obtain ⟨st, out, s'⟩ := q
      have hr := initHandle_rounds o S s m (st, out, s') h
      simp only at hr
      have ih := initServed_le o S ms s'
      rw [hr.1, hr.2.1] at ih
      simp only
      omega

/-- The number of messages a responder accepts, from the first one to the first refusal. -/
def respServed (o : Oracle) (S : List Item) : Responder → List (List Nat) → Nat
  | _, [] => 0
  | s, m :: ms =>
    match s.handle o S m with
    | .ok (_, _, s') => respServed o S s' ms + 1
    | .error _ => 0

/-- Once the responder has seen its first message, at most `max_rounds` more are accepted. -/
theorem respServed_le_open (o : Oracle) (S : List Item) :
    ∀ (ms : List (List Nat)) (s : Responder), s.side ≠ .fresh →
      respServed o S s ms ≤ s.core.lim.maxRounds - s.core.rounds
  | [], s, _ => by simp [respServed]
  | m :: ms, s, hs => by
    unfold respServed
    cases h : s.handle o S m with
    | error e => simp
    | ok q =>
      obtain ⟨st, out, s'⟩ := q
      have hr := respHandle_rounds o S s m (st, out, s') h
      simp only at hr
      have ih := respServed_le_open o S ms s' hr.2.2.1
      rw [hr.1, (hr.2.2.2 hs).1] at ih
      have := (hr.2.2.2 hs).2
      simp only
      omega

/-- A responder accepts at most `max_rounds + 1` messages of a session, whatever they hold. -/
theorem respServed_le (o : Oracle) (S : List Item) (s : Responder) (ms : List (List Nat)) :
    respServed o S s ms ≤ s.core.lim.maxRounds + 1 := by
  by_cases hf : s.side = .fresh
  · cases ms with
    | nil => simp [respServed]
    | cons m ms =>
      unfold respServed
      cases h : s.handle o S m with
      | error e => simp
      | ok q =>
        obtain ⟨st, out, s'⟩ := q
        have hr := respHandle_rounds o S s m (st, out, s') h
        simp only at hr
        have := respServed_le_open o S ms s' hr.2.2.1
        rw [hr.1] at this
        simp only
        omega
  · have := respServed_le_open o S ms s hf
    omega

/-- A refused message ends the session of an initiator that was open or checking. -/
theorem initiator_refused_dead (o : Oracle) (S : List Item) (s : Initiator) (m : List Nat) :
    s.afterErr.handle o S m = .error (.malformed .state) := by
  unfold Initiator.afterErr Initiator.handle
  split <;> simp_all [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- ... and of a responder that was not fresh, or that refused more than the header of its first message. -/
theorem responder_refused_dead (o : Oracle) (S : List Item) (s : Responder) (msg m : List Nat)
    (h : ¬ (s.side = .fresh ∧ s.headerRefused msg = true)) :
    (s.afterErr msg).handle o S m = .error (.malformed .state) := by
  unfold Responder.afterErr
  rw [if_neg h]
  unfold Responder.handle
  simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem resume_refused_dead (o : Oracle) (S : List Item) (s : Responder) :
    s.afterResumeErr.resume o S = .error (.malformed .state) := by
  simp [Responder.afterResumeErr, Responder.resume]

#audit_axioms Pinc.Reconcile.initHandle_rounds
#audit_axioms Pinc.Reconcile.respHandle_rounds
#audit_axioms Pinc.Reconcile.initServed_le
#audit_axioms Pinc.Reconcile.respServed_le
#audit_axioms Pinc.Reconcile.initiator_refused_dead
#audit_axioms Pinc.Reconcile.responder_refused_dead
#audit_axioms Pinc.Reconcile.resume_refused_dead

end Pinc.Reconcile
