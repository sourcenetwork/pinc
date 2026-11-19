import Pinc.ReconcileStale
import Pinc.ReconcileDrive

/-!
# Reconcile stale state, the sessions: a reused object behaves as a new one

`Kept c d` says two cores have the same limits and the same role: the two fields a session keeps on purpose.

PROVED (unbounded, for every state of the objects, reachable or not):

* `initStart_any`: `Initiator::start` on any two initiators whose cores are `Kept` writes the same first message or
  fails with the same error, and leaves cores that differ only in fields no later call reads (`Initiator.Bd`);
* `initHandle_bd`, `respHandle_bd`, `respResume_bd`: every handler maps two such objects and the same message to the
  same step, the same bytes or the same error, and to two such objects again. A responder in the `fresh` side needs
  only `Kept` (`respHandle_fresh`): its first message clears the rest;
* `attempt_any`: one attempt of the driver (`Initiator::run` against `Responder::serve`, with any reset) on two
  pairs of objects that are `Kept` ends in the same result, the reported items included, and leaves pairs that are
  `Kept`;
* `runAttempts_any`, `runAttempts_fresh`: so does `Initiator::run_retry` over any number of attempts, and the run
  on used objects, in whatever state the earlier sessions left them (finished, failed, refused or reset), ends as
  the run on objects made new with the same limits.

This is the unbounded counterpart of `ShadowAgrees` of `Reconcile.tla` (`Reconcile_reset.cfg`: a shadow pair of new
machines gets the same inputs and must give the same outputs).

NOT COVERED: the scratch buffers of the Rust objects that the model does not carry (`Scratch`, the transmit and
receive buffers of the drivers); they are covered by the trace of reused objects.
-/

namespace Pinc.Reconcile

/-- The two fields a session keeps on purpose: the limits and the role. -/
def Kept (c d : Core) : Prop := d.lim = c.lim ∧ d.init = c.init

theorem Core.Bd.kept {c d : Core} (h : Core.Bd c d) : Kept c d := by
  obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := h; exact ⟨rfl, rfl⟩

theorem Core.Bd.here {c d : Core} (h : Core.Bd c d) : d.here = c.here := by
  obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := h; rfl

theorem Core.Bd.there {c d : Core} (h : Core.Bd c d) : d.there = c.there := by
  obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := h; rfl

theorem endMsg_rel {c d : Core} (h : Core.Bd c d) : Rel (fun m m' : List Nat => m = m') c.endMsg d.endMsg := by
  rw [endMsg_bd h]
  exact Rel.refl _

theorem body_rel {c d : Core} (h : d.lim = c.lim) (msg : List Nat) :
    Rel (fun m m' : List Nat => m = m') (c.body msg) (d.body msg) := by
  rw [body_lim h]
  exact Rel.refl _

/-- A chunk of a cold stream reads the cold bound and the cursor, and resets the reply before it writes. -/
theorem coldChunk_bd (S : List Item) {c d : Core} (h : Core.Bd c d) (hl : d.coldLo = c.coldLo) :
    Rel (fun p q : Core × List Nat × Bool => Core.Bd p.1 q.1 ∧ q.1.coldLo = p.1.coldLo ∧ p.2 = q.2)
      (c.coldChunk S) (d.coldChunk S) := by
  obtain ⟨lim, n, init, exact, leafed, rounds, coldAt, coldLo, frames, blast, bsnap, out, ans, hdr, here, there⟩ := c
  obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := h
  simp only at hl
  subst hl
  unfold Core.coldChunk
  dsimp only
  refine Rel.bind_same (fun p => ?_)
  obtain ⟨j, stage⟩ := p
  dsimp only
  refine Rel.ite
    (fun _ => Rel.bind (R := fun a b : Out × Item => Out.BL a.1 b.1 ∧ a.2 = b.2)
      (Rel.pure ⟨head_bl (p := out.reset) (q := ou.reset) ⟨rfl, rfl⟩ _ _ _, rfl⟩) ?_)
    (fun _ => Rel.bind_same fun p => Rel.bind_same fun q => Rel.ite
      (fun _ => Rel.bind (R := fun _ _ => False) (Rel.throw _) (fun _ _ hh => hh.elim))
      (fun _ => Rel.bind (R := fun a b : Out × Item => Out.BL a.1 b.1 ∧ a.2 = b.2)
        (Rel.pure ⟨head_bl (p := out.reset) (q := ou.reset) ⟨rfl, rfl⟩ _ _ _, rfl⟩) ?_))
  all_goals
    rintro ⟨X, lo⟩ ⟨Y, lo'⟩ ⟨hb, hlo⟩
    simp only at hb hlo
    subst hlo
    dsimp only
    refine Rel.bind (finish_rel ?_ ?_ 1 false) ?_
    · rfl
    · show Y.body ++ _ ++ _ = X.body ++ _ ++ _
      rw [hb.1]
    · rintro m m' rfl
      exact Rel.pure ⟨⟨_, _, _, _, _, _, rfl⟩, rfl, rfl⟩

/-! ## The handlers -/

/-- Two initiators between calls: the same phase, cores that differ in fields no call reads. -/
def Initiator.Bd (i j : Initiator) : Prop := Core.Bd i.core j.core ∧ j.phase = i.phase

/-- Two responders between calls: the same side and the kept fields; once the first message was read, cores that
differ in fields no call reads, and the same cold bound while a cold stream is open. -/
def Responder.Bd (r s : Responder) : Prop :=
  s.side = r.side ∧ Kept r.core s.core ∧
    (r.side ≠ .fresh → Core.Bd r.core s.core ∧ (r.side = .cold → s.core.coldLo = r.core.coldLo))

/-- The same step and the same bytes, and two initiators that are related again. -/
def IRes (p q : Step × List Nat × Initiator) : Prop := p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ Initiator.Bd p.2.2 q.2.2

/-- The same step and the same bytes, and two responders that are related again. -/
def RRes (p q : Step × List Nat × Responder) : Prop := p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ Responder.Bd p.2.2 q.2.2

theorem Responder.Bd.of_core {c d : Core} (h : Core.Bd c d) {sd : Side} (hs : sd ≠ .cold) :
    Responder.Bd { core := c, side := sd } { core := d, side := sd } :=
  ⟨rfl, h.kept, fun _ => ⟨h, fun hc => (hs hc).elim⟩⟩

/-- `Initiator::start` on any two initiators with the same limits and role: the same first message or the same
error. -/
theorem initStart_any (o : Oracle) (S : List Item) (i j : Initiator) (h : Kept i.core j.core) (ref : Item) :
    Rel (fun p q : Initiator × List Nat => Initiator.Bd p.1 q.1 ∧ p.2 = q.2) (i.start o S ref) (j.start o S ref) := by
  unfold Initiator.start
  refine Rel.bind (start_any o S i.core j.core h.1 h.2 ref) ?_
  rintro ⟨c, m⟩ ⟨d, m'⟩ ⟨hc, hm⟩
  exact Rel.pure ⟨⟨hc, rfl⟩, hm⟩

theorem close_bd (o : Oracle) (S : List Item) {s t : Initiator} (h : Initiator.Bd s t) (pd : Bool) :
    Rel IRes (s.close o S pd) (t.close o S pd) := by
  obtain ⟨c, ph⟩ := s
  obtain ⟨d, ph'⟩ := t
  obtain ⟨hc, hp⟩ := h
  simp only at hc hp
  subst hp
  have hlf : d.leafed = c.leafed := by obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := hc; rfl
  unfold Initiator.close
  dsimp only
  rw [hlf]
  refine Rel.ite (fun _ => Rel.pure ⟨rfl, rfl, ⟨hc, rfl⟩⟩) (fun _ => Rel.ite (fun _ => ?_) (fun _ => Rel.ite
    (fun _ => Rel.pure ⟨rfl, rfl, ⟨hc, rfl⟩⟩)
    (fun _ => Rel.bind (endMsg_rel hc) (fun m m' hm => Rel.pure ⟨rfl, hm, ⟨hc, rfl⟩⟩))))
  refine Rel.bind (checkMsg_bd o S hc) ?_
  rintro ⟨c1, m⟩ ⟨d1, m'⟩ ⟨h1, hm⟩
  exact Rel.pure ⟨rfl, hm, ⟨h1, rfl⟩⟩

/-- `Initiator::handle` reads nothing the last session or the last call left in the scratch fields. -/
theorem initHandle_bd (o : Oracle) (S : List Item) {s t : Initiator} (h : Initiator.Bd s t) (msg : List Nat) :
    Rel IRes (s.handle o S msg) (t.handle o S msg) := by
  obtain ⟨c, ph⟩ := s
  obtain ⟨d, ph'⟩ := t
  obtain ⟨hc, hp⟩ := h
  simp only at hc hp
  subst hp
  unfold Initiator.handle
  dsimp only
  refine Rel.ite (fun _ => Rel.throw _) (fun _ => ?_)
  refine Rel.bind (round_bd hc) ?_
  intro c1 d1 h1
  refine Rel.bind (body_rel h1.lim msg) ?_
  rintro body _ rfl
  refine Rel.bind_same (fun pr => ?_)
  obtain ⟨⟨np, more⟩, r⟩ := pr
  dsimp only
  refine Rel.bind (turn_bd o S h1 r np) ?_
  rintro ⟨c2, ans⟩ ⟨d2, ans'⟩ ⟨h2, ha⟩
  simp only at h2 ha
  subst ha
  have he : d2.exact = c2.exact := by obtain ⟨s', bs', l', hd', rfl⟩ := h2; rfl
  have hh : d2.holds = c2.holds := by obtain ⟨s', bs', l', hd', rfl⟩ := h2; rfl
  have hb : d2.out.body = c2.out.body := by obtain ⟨s', bs', l', hd', rfl⟩ := h2; rfl
  dsimp only
  simp only [he, hh]
  refine Rel.ite (fun _ => Rel.ite (fun _ => Rel.pure ⟨rfl, rfl, ⟨h2.bd, rfl⟩⟩)
    (fun _ => Rel.pure ⟨rfl, rfl, ⟨h2.bd, rfl⟩⟩)) (fun _ => ?_)
  refine Rel.ite (fun _ => Rel.throw _) (fun _ => ?_)
  refine Rel.ite (fun _ => Rel.ite (fun _ => Rel.throw _) (fun _ => ?_)) (fun _ => ?_)
  · refine Rel.bind (restartExact_bd o S h2.bd) ?_
    rintro ⟨c3, m⟩ ⟨d3, m'⟩ ⟨h3, hm⟩
    exact Rel.pure ⟨rfl, hm, ⟨h3, rfl⟩⟩
  · refine Rel.ite
      (fun _ => Rel.bind (finish_rel h2.bd.lim hb _ _) (fun m m' hm => Rel.pure ⟨rfl, hm, ⟨h2.bd, rfl⟩⟩))
      (fun _ => Rel.ite
        (fun _ => Rel.bind (endMsg_rel h2.bd) (fun m m' hm => Rel.pure ⟨rfl, hm, ⟨h2.bd, rfl⟩⟩)) (fun _ => ?_))
    exact close_bd o S (s := { core := c2, phase := ph' }) (t := { core := d2, phase := ph' }) ⟨h2.bd, rfl⟩ _

/-- The rounds of a responder after the first message. -/
theorem respRun_bd (o : Oracle) (S : List Item) (s t : Responder) (h : Core.Bd s.core t.core) (r : List Nat) :
    Rel RRes (s.run o S r) (t.run o S r) := by
  unfold Responder.run
  refine Rel.bind (round_bd h) ?_
  intro c1 d1 h1
  refine Rel.bind_same (fun pr => ?_)
  obtain ⟨⟨np, more⟩, r1⟩ := pr
  dsimp only
  refine Rel.bind (turn_bd o S h1 r1 np) ?_
  rintro ⟨c2, ans⟩ ⟨d2, ans'⟩ ⟨h2, ha⟩
  simp only at h2 ha
  subst ha
  have hh : d2.holds = c2.holds := by obtain ⟨s', bs', l', hd', rfl⟩ := h2; rfl
  have hb : d2.out.body = c2.out.body := by obtain ⟨s', bs', l', hd', rfl⟩ := h2; rfl
  dsimp only
  simp only [hh]
  refine Rel.ite
    (fun _ => Rel.bind (finish_rel h2.bd.lim hb _ _)
      (fun m m' hm => Rel.pure ⟨rfl, hm, Responder.Bd.of_core h2.bd (by decide)⟩))
    (fun _ => Rel.ite
      (fun _ => Rel.bind (endMsg_rel h2.bd) (fun m m' hm => Rel.pure ⟨rfl, hm, Responder.Bd.of_core h2.bd (by decide)⟩))
      (fun _ => Rel.ite (fun _ => Rel.pure ⟨rfl, rfl, Responder.Bd.of_core h2.bd (by decide)⟩)
        (fun _ => Rel.bind (endMsg_rel h2.bd)
          (fun m m' hm => Rel.pure ⟨rfl, hm, Responder.Bd.of_core h2.bd (by decide)⟩))))

/-- `Responder::resume`: the next chunk of a cold stream. -/
theorem respResume_bd (o : Oracle) (S : List Item) {s t : Responder} (h : Responder.Bd s t) :
    Rel RRes (s.resume o S) (t.resume o S) := by
  obtain ⟨c, sd⟩ := s
  obtain ⟨d, sd'⟩ := t
  obtain ⟨hs, hk, hr⟩ := h
  simp only at hs hk hr
  subst hs
  unfold Responder.resume
  dsimp only
  refine Rel.ite (fun _ => Rel.err _) (fun hcold => ?_)
  have hsd : sd' = Side.cold := by cases sd' <;> first | rfl | exact (hcold (by decide)).elim
  subst hsd
  obtain ⟨hbd, hcl⟩ := hr (by decide)
  have hcc := coldChunk_bd S hbd (hcl rfl)
  revert hcc
  generalize c.coldChunk S = X
  generalize d.coldChunk S = Y
  intro hcc
  cases hcc with
  | err e => exact Rel.err e
  | ok hh =>
    rename_i u v
    obtain ⟨c1, m, last⟩ := u
    obtain ⟨d1, m', last'⟩ := v
    obtain ⟨h1, hl1, hm⟩ := hh
    simp only [Prod.mk.injEq] at h1 hl1 hm
    obtain ⟨rfl, rfl⟩ := hm
    dsimp only
    split
    · exact Rel.ok ⟨rfl, rfl, Responder.Bd.of_core h1 (by decide)⟩
    · exact Rel.ok ⟨rfl, rfl, ⟨rfl, h1.kept, fun _ => ⟨h1, fun _ => hl1⟩⟩⟩

/-- `Responder::handle`. In the `fresh` side the two cores need only the same limits and role: the first message
clears the session state and writes the item count before anything is read. -/
theorem respHandle_bd (o : Oracle) (S : List Item) {s t : Responder} (h : Responder.Bd s t) (msg : List Nat) :
    Rel RRes (s.handle o S msg) (t.handle o S msg) := by
  obtain ⟨c, sd⟩ := s
  obtain ⟨d, sd'⟩ := t
  obtain ⟨hs, hk, hr⟩ := h
  simp only at hs hk hr
  subst hs
  obtain ⟨lim, n, init, exact, leafed, rounds, coldAt, coldLo, frames, blast, bsnap, out, ans, hdr, here, there⟩ := c
  obtain ⟨lim', n', init', exact', leafed', rounds', coldAt', coldLo', frames', blast', bsnap', out', ans', hdr', here',
    there'⟩ := d
  obtain ⟨hl, hi⟩ := hk
  simp only at hl hi
  subst hl hi
  unfold Responder.handle
  dsimp only [Core.clear]
  refine Rel.ite (fun _ => Rel.throw _) (fun _ => ?_)
  refine Rel.bind (body_rel ?_ msg) ?_
  · rfl
  rintro body _ rfl
  refine Rel.ite (fun _ => ?_) (fun hnf => respRun_bd o S _ _ (hr (by simpa using hnf)).1 body)
  refine Rel.bind_same (fun pr => ?_)
  obtain ⟨l, r1⟩ := pr
  dsimp only
  refine Rel.ite (fun _ => Rel.throw _) (fun _ => ?_)
  refine Rel.bind_same (fun pr => ?_)
  obtain ⟨u, r2⟩ := pr
  dsimp only
  refine Rel.bind_same (fun pr => ?_)
  obtain ⟨na, r3⟩ := pr
  dsimp only
  refine Rel.ite (fun _ => ?_) (fun _ => ?_)
  · exact respResume_bd o S ⟨rfl, ⟨rfl, rfl⟩, fun _ => ⟨⟨_, _, _, _, _, _, rfl⟩, fun _ => rfl⟩⟩
  · refine respRun_bd o S _ _ ?_ r3
    exact ⟨_, _, _, _, _, _, rfl⟩

/-- The first message of a session, to any two responders with the same limits and role, whatever they hold. -/
theorem respHandle_fresh (o : Oracle) (S : List Item) (r s : Responder) (h : Kept r.core s.core) (msg : List Nat) :
    Rel RRes (({ r with side := .fresh } : Responder).handle o S msg)
      (({ s with side := .fresh } : Responder).handle o S msg) :=
  respHandle_bd o S (s := { r with side := .fresh }) (t := { s with side := .fresh })
    ⟨rfl, h, fun hf => (hf rfl).elim⟩ msg

/-! ## The driver -/

theorem respServe_bd (o : Oracle) (S : List Item) :
    ∀ (fuel : Nat) (r s : Responder) (step : Step) (out : List Nat) (acc : List (List Nat)), Responder.Bd r s →
      Rel (fun p q : List (List Nat) × Responder => p.1 = q.1 ∧ Responder.Bd p.2 q.2)
        (respServe o S fuel r step out acc) (respServe o S fuel s step out acc) := by
  intro fuel
  induction fuel with
  | zero => intro r s step out acc h; exact Rel.ok ⟨rfl, h⟩
  | succ f ih =>
    intro r s step out acc h
    cases step with
    | send => exact Rel.ok ⟨rfl, h⟩
    | last => exact Rel.ok ⟨rfl, h⟩
    | wait => exact Rel.ok ⟨rfl, h⟩
    | done => exact Rel.ok ⟨rfl, h⟩
    | chunk =>
      simp only [respServe]
      have hr := respResume_bd o S h
      revert hr
      generalize r.resume o S = X
      generalize s.resume o S = Y
      intro hr
      cases hr with
      | err e => exact Rel.err e
      | ok hh =>
        rename_i u v
        obtain ⟨st, m, r'⟩ := u
        obtain ⟨st', m', s'⟩ := v
        obtain ⟨h1, h2, h3⟩ := hh
        simp only at h1 h2 h3
        subst h1 h2
        exact ih r' s' st m _ h3

/-- What a responder writes for one received message: the same messages or the same error. -/
theorem respHandleAll_bd (o : Oracle) (S : List Item) {r s : Responder} (h : Responder.Bd r s) (tx : List Nat) :
    Rel (fun p q : List (List Nat) × Responder => p.1 = q.1 ∧ Responder.Bd p.2 q.2)
      (respHandle o S r tx) (respHandle o S s tx) := by
  unfold respHandle
  have hr := respHandle_bd o S h tx
  revert hr
  generalize r.handle o S tx = X
  generalize s.handle o S tx = Y
  intro hr
  cases hr with
  | err e => exact Rel.err e
  | ok hh =>
    rename_i u v
    obtain ⟨st, m, r'⟩ := u
    obtain ⟨st', m', s'⟩ := v
    obtain ⟨h1, h2, h3⟩ := hh
    simp only at h1 h2 h3
    subst h1 h2
    exact respServe_bd o S _ r' s' st m [] h3

/-- The initiator handles the replies: the same count, the same pending message, the same result. -/
theorem initReplies_bd (o : Oracle) (S : List Item) (cut : Cut) :
    ∀ (ms : List (List Nat)) (n : Nat) (i j : Initiator) (pend : Option (List Nat)), Initiator.Bd i j →
      (initReplies o S cut ms n i pend).1 = (initReplies o S cut ms n j pend).1 ∧
      Initiator.Bd (initReplies o S cut ms n i pend).2.1 (initReplies o S cut ms n j pend).2.1 ∧
      (initReplies o S cut ms n i pend).2.2 = (initReplies o S cut ms n j pend).2.2 := by
  intro ms
  induction ms with
  | nil => intro n i j pend h; exact ⟨rfl, h, rfl⟩
  | cons m ms ih =>
    intro n i j pend h
    simp only [initReplies]
    split
    · exact ⟨rfl, h, rfl⟩
    · have hr := initHandle_bd o S h m
      revert hr
      generalize i.handle o S m = X
      generalize j.handle o S m = Y
      intro hr
      cases hr with
      | err e => exact ⟨rfl, h, rfl⟩
      | ok hh =>
        rename_i u v
        obtain ⟨st, out, i'⟩ := u
        obtain ⟨st', out', j'⟩ := v
        obtain ⟨h1, h2, h3⟩ := hh
        simp only at h1 h2 h3
        subst h1 h2
        cases st with
        | send => exact ih _ i' j' _ h3
        | wait => exact ih _ i' j' _ h3
        | chunk => exact ⟨rfl, h3, rfl⟩
        | last => exact ⟨rfl, h3, by simp only [h3.1.here, h3.1.there]⟩
        | done => exact ⟨rfl, h3, by simp only [h3.1.here, h3.1.there]⟩

/-- A session in lockstep on two related pairs: the same result, and the kept fields stay equal. -/
theorem sessionLoop_bd (oI oR : Oracle) (SI SR : List Item) (cut : Cut) :
    ∀ (fuel nr ni : Nat) (i j : Initiator) (r s : Responder) (tx : List Nat), Initiator.Bd i j → Responder.Bd r s →
      (sessionLoop oI oR SI SR cut fuel nr ni i r tx).1 = (sessionLoop oI oR SI SR cut fuel nr ni j s tx).1 ∧
      Kept (sessionLoop oI oR SI SR cut fuel nr ni i r tx).2.1.core (sessionLoop oI oR SI SR cut fuel nr ni j s tx).2.1.core ∧
      Kept (sessionLoop oI oR SI SR cut fuel nr ni i r tx).2.2.core (sessionLoop oI oR SI SR cut fuel nr ni j s tx).2.2.core := by
  intro fuel
  induction fuel with
  | zero => intro nr ni i j r s tx hi hr; exact ⟨rfl, hi.1.kept, hr.2.1⟩
  | succ f ih =>
    intro nr ni i j r s tx hi hr
    simp only [sessionLoop]
    split
    · exact ⟨rfl, hi.1.kept, hr.2.1⟩
    · have hh := respHandleAll_bd oR SR hr tx
      revert hh
      generalize respHandle oR SR r tx = X
      generalize respHandle oR SR s tx = Y
      intro hh
      cases hh with
      | err e => exact ⟨rfl, hi.1.kept, hr.2.1⟩
      | ok hh =>
        rename_i u v
        obtain ⟨replies, r'⟩ := u
        obtain ⟨replies', s'⟩ := v
        obtain ⟨h1, h2⟩ := hh
        simp only at h1 h2
        subst h1
        have hq := initReplies_bd oI SI cut replies ni i j none hi
        rcases hA : initReplies oI SI cut replies ni i none with ⟨ni', i', pend, res⟩
        rcases hB : initReplies oI SI cut replies ni j none with ⟨ni'', j', pend', res'⟩
        rw [hA, hB] at hq
        obtain ⟨q1, q2, q3⟩ := hq
        simp only [Prod.mk.injEq] at q1 q2 q3
        obtain ⟨rfl, rfl⟩ := q3
        subst q1
        simp only [hA, hB]
        cases res with
        | some run => exact ⟨rfl, q2.1.kept, h2.2.1⟩
        | none =>
          cases pend with
          | some tx' => exact ih _ _ i' j' r' s' tx' q2 h2
          | none => exact ⟨rfl, q2.1.kept, h2.2.1⟩

/-- One attempt on two pairs of objects with the same limits and roles, whatever else they hold: the same result,
and the limits and roles stay the same. -/
theorem attempt_any (oI oR : Oracle) (SI SR : List Item) (ref : Item) (cut : Cut) (fuel : Nat)
    (i j : Initiator) (r s : Responder) (hi : Kept i.core j.core) (hr : Kept r.core s.core) :
    (attempt oI oR SI SR ref cut fuel i r).1 = (attempt oI oR SI SR ref cut fuel j s).1 ∧
      Kept (attempt oI oR SI SR ref cut fuel i r).2.1.core (attempt oI oR SI SR ref cut fuel j s).2.1.core ∧
      Kept (attempt oI oR SI SR ref cut fuel i r).2.2.core (attempt oI oR SI SR ref cut fuel j s).2.2.core := by
  unfold attempt
  have hs := initStart_any oI SI i j hi ref
  revert hs
  generalize i.start oI SI ref = X
  generalize j.start oI SI ref = Y
  intro hs
  cases hs with
  | err e => exact ⟨rfl, hi, hr⟩
  | ok hh =>
    rename_i u v
    obtain ⟨i0, tx⟩ := u
    obtain ⟨j0, tx'⟩ := v
    obtain ⟨h1, h2⟩ := hh
    simp only at h1 h2
    subst h2
    exact sessionLoop_bd oI oR SI SR cut fuel 0 0 i0 j0 { r with side := .fresh } { s with side := .fresh } tx h1
      ⟨rfl, hr, fun hf => (hf rfl).elim⟩

/-- `Initiator::run_retry` on two pairs of objects with the same limits and roles: the same result, whatever the
earlier sessions left in them and wherever the resets fall. -/
theorem runAttempts_any (oI oR : Oracle) (SI SR : List Item) (ref : Item) (fuel : Nat) (cuts : Nat → Cut) :
    ∀ (n k : Nat) (i j : Initiator) (r s : Responder), Kept i.core j.core → Kept r.core s.core →
      (runAttempts oI oR SI SR ref fuel cuts n k i r).1 = (runAttempts oI oR SI SR ref fuel cuts n k j s).1 := by
  intro n
  induction n with
  | zero => intro k i j r s hi hr; rfl
  | succ n ih =>
    intro k i j r s hi hr
    simp only [runAttempts]
    have ha := attempt_any oI oR SI SR ref (cuts k) fuel i j r s hi hr
    revert ha
    generalize attempt oI oR SI SR ref (cuts k) fuel i r = A
    generalize attempt oI oR SI SR ref (cuts k) fuel j s = B
    intro ha
    obtain ⟨res, i', r'⟩ := A
    obtain ⟨res', j', s'⟩ := B
    obtain ⟨a1, a2, a3⟩ := ha
    simp only at a1 a2 a3
    subst a1
    cases res with
    | reset => exact ih (k + 1) i' j' r' s' a2 a3
    | done here there => rfl
    | protocol e => rfl
    | closed => rfl
    | exhausted => rfl

/-- A run on used objects, in whatever state earlier sessions left them, ends as the run on objects made new with
the same limits. -/
theorem runAttempts_fresh (oI oR : Oracle) (SI SR : List Item) (ref : Item) (fuel : Nat) (cuts : Nat → Cut)
    (n k : Nat) (i : Initiator) (r : Responder) :
    (runAttempts oI oR SI SR ref fuel cuts n k i r).1 =
      (runAttempts oI oR SI SR ref fuel cuts n k { core := { lim := i.core.lim, init := i.core.init } }
        { core := { lim := r.core.lim, init := r.core.init } }).1 :=
  runAttempts_any oI oR SI SR ref fuel cuts n k i _ r _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

#audit_axioms Pinc.Reconcile.initStart_any
#audit_axioms Pinc.Reconcile.initHandle_bd
#audit_axioms Pinc.Reconcile.respHandle_bd
#audit_axioms Pinc.Reconcile.respResume_bd
#audit_axioms Pinc.Reconcile.respHandle_fresh
#audit_axioms Pinc.Reconcile.attempt_any
#audit_axioms Pinc.Reconcile.runAttempts_any
#audit_axioms Pinc.Reconcile.runAttempts_fresh

end Pinc.Reconcile
