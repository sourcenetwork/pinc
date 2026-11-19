import Pinc.ReconcileKeeps

/-!
# Reconcile stale state: what a core carries from one session into the next is never read

The initiator and the responder objects are reused across attempts (`Initiator::run_retry`, `Responder::serve`).
`Core::clear` resets the exact flag, the leaf flag, the round counter, the cold cursor, the frames and the two report
arenas; `start` then writes the item count and the header, and the first message of a fresh responder writes the item
count. The limits and the role are kept on purpose. Everything else is left as the last session wrote it: the reply
under construction (`out`, with the snapshot of its previous bound), the previous bound of the message read (`blast`)
and its snapshot (`bsnap`), the answer counters (`ans`), the lower bound of a cold stream (`coldLo`) and, on a
responder, the header (`hdr`).

This file proves that none of those left fields is read before it is written. Two relations say which fields may
differ:

* `Bd c d` (between two calls of a handler): `d` is `c` with any `out`, `blast`, `bsnap`, `ans`, `coldLo` and `hdr`;
* `Scr c d` (inside `turn`): `d` is `c` with any `out.snap`, `bsnap`, `coldLo` and `hdr`.

`Rel R x y` says two runs fail with the same error or succeed with values related by `R`. Every function of the
session is walked once with the rules of `Rel`, both runs side by side. The one place where a left field is read is
`Out::rollback` in `split_fit` at the root (`mark = 0`): it restores the previous bound from `snap`, which `root` does
not reset. The lower bound of the root is empty, an empty bound is encoded the same against any previous bound
(`putBound_nil`), and it becomes the previous bound, so the bytes do not depend on `snap` (`splitParts_nil`,
`splitFit_root`).

The theorems about whole sessions are in `ReconcileStaleRun`.
-/

namespace Pinc.Reconcile

/-- Both runs fail with the same error, or both succeed with related values. -/
inductive Rel {ε α β : Type} (R : α → β → Prop) : Except ε α → Except ε β → Prop
  | ok {a : α} {b : β} (h : R a b) : Rel R (.ok a) (.ok b)
  | err (e : ε) : Rel R (.error e) (.error e)

namespace Rel
variable {ε α β γ δ : Type} {R : α → β → Prop} {Q : γ → δ → Prop}

theorem pure {a : α} {b : β} (h : R a b) : Rel R (Pure.pure a : Except ε α) (Pure.pure b) := Rel.ok h

theorem throw (e : ε) : Rel R (throw e : Except ε α) (throw e : Except ε β) := Rel.err e

theorem bind {x : Except ε α} {y : Except ε β} {f : α → Except ε γ} {g : β → Except ε δ} (hx : Rel R x y)
    (hf : ∀ a b, R a b → Rel Q (f a) (g b)) : Rel Q (x >>= f) (y >>= g) := by
  cases hx with
  | ok h => exact hf _ _ h
  | err e => exact Rel.err e

/-- The same first step on both sides. -/
theorem bind_same {x : Except ε α} {f : α → Except ε γ} {g : α → Except ε δ}
    (hf : ∀ a, Rel Q (f a) (g a)) : Rel Q (x >>= f) (x >>= g) := by
  cases x with
  | error e => exact Rel.err e
  | ok a => exact hf a

/-- The same first step on both sides, with what is known of its result. -/
theorem bind_ok {P : α → Prop} {x : Except ε α} {f : α → Except ε γ} {g : α → Except ε δ} (hx : Ok P x)
    (hf : ∀ a, P a → Rel Q (f a) (g a)) : Rel Q (x >>= f) (x >>= g) := by
  cases h : x with
  | error e => exact Rel.err e
  | ok a => exact hf a (hx a h)

theorem ite {c : Prop} [Decidable c] {x x' : Except ε α} {y y' : Except ε β} (h1 : c → Rel R x y)
    (h2 : ¬c → Rel R x' y') : Rel R (if c then x else x') (if c then y else y') := by
  split
  · next h => exact h1 h
  · next h => exact h2 h

theorem mono {R' : α → β → Prop} {x : Except ε α} {y : Except ε β} (h : Rel R x y) (hr : ∀ a b, R a b → R' a b) :
    Rel R' x y := by
  cases h with
  | ok h => exact Rel.ok (hr _ _ h)
  | err e => exact Rel.err e

theorem refl (x : Except ε α) : Rel (fun a b => a = b) x x := by
  cases x with
  | error e => exact Rel.err e
  | ok a => exact Rel.ok rfl

/-- Related by equality: the two runs are equal. -/
theorem eq {x y : Except ε α} (h : Rel (fun a b => a = b) x y) : x = y := by
  cases h with
  | ok h => rw [h]
  | err e => rfl

end Rel

/-! ## The reply under construction -/

/-- Two replies with the same bytes and the same previous bound (the staged items and the snapshot may differ). -/
def Out.BL (p q : Out) : Prop := q.body = p.body ∧ q.last = p.last

theorem cpl_nil_right (l : List Nat) : cpl l [] = 0 := by cases l <;> rfl

/-- An empty bound is encoded the same against any previous bound. -/
theorem putBound_nil (last : Item) : putBound last [] = putBound [] [] := by
  simp [putBound, cpl_nil_right, cpl]

theorem putHead_nil (last : Item) (kind : Nat) (hi : Option Item) : putHead last kind [] hi = putHead [] kind [] hi := by
  simp only [putHead, putBound_nil last]

theorem head_bl {p q : Out} (h : Out.BL p q) (kind : Nat) (lo : Item) (hi : Option Item) :
    Out.BL (p.head kind lo hi) (q.head kind lo hi) := by
  obtain ⟨hb, hl⟩ := h
  unfold Out.head Out.BL
  rw [hl, hb]
  exact ⟨rfl, rfl⟩

/-- A head with an empty lower bound: the same bytes whatever the previous bound was. -/
theorem head_nil {p q : Out} (h : q.body = p.body) (kind : Nat) (hi : Option Item) :
    Out.BL (p.head kind [] hi) (q.head kind [] hi) := by
  unfold Out.head Out.BL
  rw [putHead_nil p.last, putHead_nil q.last, h]
  exact ⟨rfl, rfl⟩

theorem idsPart_bl (o : Oracle) (lim : Limits) (S : List Item) {p q : Out} (h : Out.BL p q) (lo : Item)
    (hi : Option Item) (a b : Nat) : Rel Out.BL (idsPart o lim S p lo hi a b) (idsPart o lim S q lo hi a b) := by
  unfold idsPart
  cases readRange lim S a (b - a) with
  | error e => exact Rel.err e
  | ok xs =>
    obtain ⟨hb, hl⟩ := head_bl h tIDS lo hi
    exact Rel.ok ⟨by simp only [hb], hl⟩

theorem itemsPart_bl (lim : Limits) (S : List Item) {p q : Out} (h : Out.BL p q) (kind : Nat) (lo : Item)
    (hi : Option Item) (a b : Nat) : Rel Out.BL (itemsPart lim S p kind lo hi a b) (itemsPart lim S q kind lo hi a b) := by
  unfold itemsPart
  cases readRange lim S a (b - a) with
  | error e => exact Rel.err e
  | ok xs =>
    obtain ⟨hb, hl⟩ := head_bl h kind lo hi
    exact Rel.ok ⟨by simp only [hb], hl⟩

theorem bl_append {p q : Out} (h : Out.BL p q) (bs : List Nat) :
    Out.BL { p with body := p.body ++ bs } { q with body := q.body ++ bs } := ⟨by simp only [h.1], h.2⟩

/-- The loop of `split` reads the bytes and the previous bound of the reply, nothing else of it. -/
theorem splitGo_bl (o : Oracle) (lim : Limits) (S : List Item) (hi : Option Item) (b step : Nat) :
    ∀ (fuel x : Nat) (l : Item) (p q : Out) (cnt : Nat), Out.BL p q →
      Rel (fun u v : Out × Nat => Out.BL u.1 v.1 ∧ u.2 = v.2) (splitParts.go o lim S hi b step x l p cnt fuel)
        (splitParts.go o lim S hi b step x l q cnt fuel) := by
  intro fuel
  induction fuel with
  | zero => intro x l p q cnt h; exact Rel.ok ⟨h, rfl⟩
  | succ f ih =>
    intro x l p q cnt h
    simp only [splitParts.go]
    by_cases hx : x < b
    · simp only [hx, ite_true]
      by_cases hy : min b (x + step) < b
      · simp only [hy, ite_true]
        cases readItem lim S (min b (x + step) - 1) with
        | error e => exact Rel.err _
        | ok u =>
          cases readItem lim S (min b (x + step)) with
          | error e => exact Rel.err _
          | ok v =>
            dsimp only
            split
            · exact Rel.err _
            · exact ih _ _ _ _ _ (bl_append (head_bl h _ _ _) _)
      · simp only [hy, ite_false]
        exact ih _ _ _ _ _ (bl_append (head_bl h _ _ _) _)
    · simp only [hx, ite_false]
      exact Rel.ok ⟨h, rfl⟩

/-- A split whose lower bound is empty and whose range is not: the bytes do not depend on the previous bound. -/
theorem splitParts_nil (o : Oracle) (lim : Limits) (S : List Item) {p q : Out} (h : q.body = p.body)
    (hi : Option Item) (a b fan : Nat) (hab : a < b) :
    Rel (fun u v : Out × Nat => Out.BL u.1 v.1 ∧ u.2 = v.2) (splitParts o lim S p [] hi a b fan)
      (splitParts o lim S q [] hi a b fan) := by
  unfold splitParts
  dsimp only
  obtain ⟨f, hf⟩ : ∃ f, b - a + 1 = f + 1 := ⟨b - a, rfl⟩
  rw [hf]
  simp only [splitParts.go, hab, ite_true]
  split
  · cases readItem lim S (min b (a + max 1 ((b - a + fan - 1) / fan)) - 1) with
    | error e => exact Rel.err _
    | ok u =>
      cases readItem lim S (min b (a + max 1 ((b - a + fan - 1) / fan))) with
      | error e => exact Rel.err _
      | ok v =>
        dsimp only
        split
        · exact Rel.err _
        · exact splitGo_bl o lim S hi b _ _ _ _ _ _ _ (bl_append (head_nil h _ _) _)
  · exact splitGo_bl o lim S hi b _ _ _ _ _ _ _ (bl_append (head_nil h _ _) _)

/-- `split_fit` at the root (`mark = 0`): the rollback restores the previous bound from a snapshot the root did not
write, and the bytes are the same whatever that snapshot holds. -/
theorem splitFit_root (o : Oracle) (lim : Limits) (S : List Item) (hi : Option Item) (a b : Nat) (hab : a < b) :
    ∀ (k : Nat) (p q : Out), q.body = p.body →
      Rel (fun u v : Out × Nat => v.1.body = u.1.body ∧ u.2 = v.2) (splitFit o lim S p [] hi a b 0 k)
        (splitFit o lim S q [] hi a b 0 k) := by
  intro k
  induction k with
  | zero =>
    intro p q h
    exact Rel.mono (splitParts_nil o lim S h hi a b 2 hab) (fun u v hh => ⟨hh.1.1, hh.2⟩)
  | succ k ih =>
    intro p q h
    simp only [splitFit]
    have hs := splitParts_nil o lim S h hi a b (spl / 2 ^ (2 - k)) hab
    revert hs
    generalize splitParts o lim S p [] hi a b (spl / 2 ^ (2 - k)) = X
    generalize splitParts o lim S q [] hi a b (spl / 2 ^ (2 - k)) = Y
    intro hs
    cases hs with
    | err e => exact Rel.err e
    | ok hh =>
      rename_i u v
      obtain ⟨u1, u2⟩ := u
      obtain ⟨v1, v2⟩ := v
      obtain ⟨⟨hb, _⟩, hc⟩ := hh
      simp only at hb hc
      subst hc
      dsimp only
      rw [hb]
      split
      · exact Rel.ok ⟨hb, rfl⟩
      · exact ih _ _ (by simp [Out.rollback])

/-! ## The two relations on cores -/

/-- Between two calls of a handler: `d` is `c` with any reply, previous bound, snapshot, answer counters, cold bound
and header. -/
def Core.Bd (c d : Core) : Prop :=
  ∃ (ou : Out) (bl bs : Item) (an : Ans) (l : Item) (h : List Nat),
    d = { c with out := ou, blast := bl, bsnap := bs, ans := an, coldLo := l, hdr := h }

/-- Inside `turn`: `d` is `c` with any snapshot of the reply's previous bound, snapshot of the read bound, cold bound
and header. -/
def Core.Scr (c d : Core) : Prop :=
  ∃ (s bs l : Item) (h : List Nat), d = { c with out := { c.out with snap := s }, bsnap := bs, coldLo := l, hdr := h }

theorem Core.Scr.bd {c d : Core} (h : Core.Scr c d) : Core.Bd c d := by
  obtain ⟨s, bs, l, hd, rfl⟩ := h
  exact ⟨_, _, _, _, _, _, rfl⟩

theorem Core.Bd.refl (c : Core) : Core.Bd c c := ⟨_, _, _, _, _, _, rfl⟩

/-! ## A part rule reads neither the cold bound nor the header -/

macro "relw" : tactic => `(tactic| first
  | (refine Rel.bind_same (fun _ => ?_))
  | (refine Rel.ite (fun _ => ?_) (fun _ => ?_))
  | exact Rel.throw _
  | (apply Rel.pure; first | exact ⟨rfl, rfl⟩ | (unfold Core.bump; (try split) <;> exact ⟨rfl, rfl⟩))
  | split
  | (dsimp only [letFun])
  | (dsimp only))

theorem tailPart_cold (o : Oracle) (S : List Item) (c : Core) (l : Item) (h : List Nat) (kind : Nat) (lo : Item)
    (hi : Option Item) (r : List Nat) (mark : Nat) :
    Rel (fun p q : Core × List Nat => q.1 = { p.1 with coldLo := l, hdr := h } ∧ q.2 = p.2)
      (tailPart o S c kind lo hi r mark) (tailPart o S { c with coldLo := l, hdr := h } kind lo hi r mark) := by
  unfold tailPart
  repeat' relw

theorem procPart_cold (o : Oracle) (S : List Item) (c : Core) (l : Item) (h : List Nat) (r : List Nat) (mark : Nat) :
    Rel (fun p q : Core × List Nat => q.1 = { p.1 with coldLo := l, hdr := h } ∧ q.2 = p.2)
      (procPart o S c r mark) (procPart o S { c with coldLo := l, hdr := h } r mark) := by
  rw [procPart_eq, procPart_eq]
  dsimp only
  cases readHead c.blast r c.lim.maxItem with
  | error e => exact Rel.err _
  | ok q =>
    obtain ⟨⟨kind, lo, hi⟩, l', r1⟩ := q
    exact tailPart_cold o S { c with blast := l' } l h kind lo hi r1 mark

/-! ## `answer`, the frames and `turn` -/

theorem answerLoop_scr (o : Oracle) (S : List Item) :
    ∀ (k : Nat) (c d : Core) (r : List Nat), Core.Scr c d →
      Rel (fun p q : Core × List Nat × Nat => Core.Scr p.1 q.1 ∧ p.2 = q.2) (answerLoop o S c r k)
        (answerLoop o S d r k) := by
  intro k
  induction k with
  | zero => intro c d r h; exact Rel.ok ⟨h, rfl⟩
  | succ k ih =>
    intro c d r h
    obtain ⟨s, bs, l, hd, rfl⟩ := h
    simp only [answerLoop]
    dsimp only [Out.mark]
    refine Rel.bind (procPart_cold o S { c with out := { c.out with snap := c.out.last }, bsnap := c.blast } l hd r
      c.out.body.length) ?_
    rintro ⟨c1, r1⟩ ⟨c2, r2⟩ ⟨h1, h2⟩
    simp only at h1 h2
    subst h1 h2
    dsimp only
    refine Rel.ite (fun _ => Rel.ite (fun _ => Rel.throw _) (fun _ => Rel.pure ⟨⟨_, _, l, hd, rfl⟩, rfl⟩)) (fun _ => ?_)
    exact ih c1 _ _ ⟨_, _, l, hd, rfl⟩

theorem pushFrame_scr {c d : Core} (h : Core.Scr c d) (rest : List Nat) (left : Nat) :
    Rel Core.Scr (c.pushFrame rest left) (d.pushFrame rest left) := by
  obtain ⟨s, bs, l, hd, rfl⟩ := h
  unfold Core.pushFrame
  dsimp only
  exact Rel.ite (fun _ => Rel.err _) (fun _ => Rel.ok ⟨_, _, _, _, rfl⟩)

theorem resume_scr (o : Oracle) (S : List Item) {c d : Core} (h : Core.Scr c d) :
    Rel (fun p q : Core × Bool => Core.Scr p.1 q.1 ∧ p.2 = q.2) (c.resume o S) (d.resume o S) := by
  obtain ⟨s, bs, l, hd, rfl⟩ := h
  obtain ⟨lim, n, init, exact, leafed, rounds, coldAt, coldLo, frames, blast, bsnap, out, ans, hdr, here, there⟩ := c
  unfold Core.resume
  dsimp only
  cases frames with
  | nil => exact Rel.err _
  | cons f tl =>
    dsimp only
    refine Rel.bind (R := fun p q : Core × List Nat × Nat => Core.Scr p.1 q.1 ∧ p.2 = q.2)
      (answerLoop_scr o S _ _ _ _ ⟨s, bs, l, hd, rfl⟩) ?_
    rintro ⟨c1, rest, left⟩ ⟨c2, rest2, left2⟩ ⟨⟨s', bs', l', hd', rfl⟩, h2⟩
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    dsimp only
    refine Rel.ite (fun _ => Rel.ite (fun _ => Rel.throw _) (fun _ => Rel.pure ⟨⟨_, _, _, _, rfl⟩, rfl⟩))
      (fun _ => Rel.pure ⟨⟨_, _, _, _, rfl⟩, rfl⟩)

theorem resumeLoop_scr (o : Oracle) (S : List Item) :
    ∀ (fuel : Nat) (c d : Core), Core.Scr c d → Rel Core.Scr (resumeLoop o S fuel c) (resumeLoop o S fuel d) := by
  intro fuel
  induction fuel with
  | zero => intro c d h; exact Rel.ok h
  | succ f ih =>
    intro c d h
    simp only [resumeLoop]
    have h' := h
    obtain ⟨s, bs, l, hd, rfl⟩ := h'
    dsimp only
    refine Rel.ite (fun _ => ?_) (fun _ => Rel.ok h)
    refine Rel.bind (resume_scr o S h) ?_
    rintro ⟨c1, adv⟩ ⟨c2, adv2⟩ ⟨h1, h2⟩
    simp only at h1 h2
    subst h2
    dsimp only
    exact Rel.ite (fun _ => ih c1 c2 h1) (fun _ => Rel.pure h1)

/-- `turn` resets the reply, the previous bound and the answer counters before it reads anything. -/
theorem turn_bd (o : Oracle) (S : List Item) {c d : Core} (h : Core.Bd c d) (r : List Nat) (np : Nat) :
    Rel (fun p q : Core × Ans => Core.Scr p.1 q.1 ∧ p.2 = q.2) (c.turn o S r np) (d.turn o S r np) := by
  obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := h
  unfold Core.turn
  dsimp only
  refine Rel.bind (answerLoop_scr o S np { c with out := c.out.reset, blast := [], ans := {} } _ r
    ⟨ou.snap, bs, l, hd, rfl⟩) ?_
  rintro ⟨c1, rest, left⟩ ⟨c2, rest2, left2⟩ ⟨h1, h2⟩
  simp only [Prod.mk.injEq] at h1 h2
  obtain ⟨rfl, rfl⟩ := h2
  dsimp only
  have tail : ∀ c3 c4 : Core, Core.Scr c3 c4 →
      Rel (fun p q : Core × Ans => Core.Scr p.1 q.1 ∧ p.2 = q.2)
        (resumeLoop o S (c3.frames.foldl (fun s f => s + f.left + 1) 1) c3 >>= fun c => Pure.pure (c, c.ans))
        (resumeLoop o S (c4.frames.foldl (fun s f => s + f.left + 1) 1) c4 >>= fun c => Pure.pure (c, c.ans)) := by
    intro c3 c4 h3
    have hf : c4.frames = c3.frames := by obtain ⟨s, bs, l, hd, rfl⟩ := h3; rfl
    rw [hf]
    refine Rel.bind (resumeLoop_scr o S _ c3 c4 h3) ?_
    intro c5 c6 h5
    refine Rel.pure ⟨h5, ?_⟩
    obtain ⟨s, bs, l, hd, rfl⟩ := h5
    rfl
  refine Rel.ite (fun _ => Rel.bind (pushFrame_scr h1 _ _) tail) (fun _ => Rel.ite
    (fun _ => Rel.bind (R := fun _ _ => False) (Rel.throw _) (fun _ _ hh => hh.elim))
    (fun _ => Rel.bind (R := Core.Scr) (Rel.pure h1) tail))

/-! ## The other steps of a handler -/

theorem Core.Bd.lim {c d : Core} (h : Core.Bd c d) : d.lim = c.lim := by
  obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := h; rfl

theorem round_bd {c d : Core} (h : Core.Bd c d) : Rel Core.Bd c.round d.round := by
  obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := h
  unfold Core.round
  dsimp only
  exact Rel.ite (fun _ => Rel.err _) (fun _ => Rel.ok ⟨_, _, _, _, _, _, rfl⟩)

theorem body_lim {c d : Core} (h : d.lim = c.lim) (msg : List Nat) : d.body msg = c.body msg := by
  unfold Core.body Core.frameCap
  rw [h]

/-- `finish` reads the limits, the bytes of the reply and, for a first message, the header. -/
theorem finish_eq {c d : Core} (hl : d.lim = c.lim) (hb : d.out.body = c.out.body) (w : Bool)
    (hh : w = true → d.hdr = c.hdr) (cnt : Nat) (more : Bool) : d.finish w cnt more = c.finish w cnt more := by
  unfold Core.finish Core.frameCap
  cases w with
  | false => simp only [hl, hb, Bool.false_eq_true, ite_false]
  | true => simp only [hl, hb, hh rfl]

theorem finish_rel {c d : Core} (hl : d.lim = c.lim) (hb : d.out.body = c.out.body) (cnt : Nat) (more : Bool) :
    Rel (fun m m' : List Nat => m = m') (c.finish false cnt more) (d.finish false cnt more) := by
  rw [finish_eq hl hb false (fun hw => by cases hw)]
  exact Rel.refl _

theorem endMsg_bd {c d : Core} (h : Core.Bd c d) : d.endMsg = c.endMsg := by
  obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := h
  unfold Core.endMsg
  exact finish_eq rfl rfl false (fun hw => by cases hw) 0 false

/-- `root` resets the reply before it writes; its bytes are the same, and it keeps the header. -/
theorem root_bd (o : Oracle) (S : List Item) {c d : Core} (h : Core.Bd c d) :
    Rel (fun p q : Core × Nat => Core.Bd p.1 q.1 ∧ q.1.out.body = p.1.out.body ∧ (d.hdr = c.hdr → q.1.hdr = p.1.hdr) ∧
        p.2 = q.2) (c.root o S) (d.root o S) := by
  obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := h
  unfold Core.root
  dsimp only
  refine Rel.ite (fun _ => Rel.bind_ok (P := fun ok => ok = false → 0 < c.n) ?_ ?_)
    (fun hn => Rel.bind_ok (P := fun ok => ok = false → 0 < c.n)
      (Ok.pure _ (fun _ => by simp only [aleaf] at hn; omega)) ?_)
  · intro v hv
    unfold leafOk at hv
    split at hv
    · cases hv; intro hf; cases hf
    · intro _; omega
  all_goals
    intro ok hok
    refine Rel.ite (fun hk => Rel.ite
      (fun _ => Rel.bind (R := Out.BL) (itemsPart_bl _ _ (p := c.out.reset) (q := ou.reset) ⟨rfl, rfl⟩ _ _ _ _ _)
        (fun o1 o2 (hb : Out.BL o1 o2) => Rel.pure ⟨⟨_, _, _, _, _, _, rfl⟩, hb.1, fun hh => hh, rfl⟩))
      (fun _ => Rel.bind (R := Out.BL) (idsPart_bl _ _ _ (p := c.out.reset) (q := ou.reset) ⟨rfl, rfl⟩ _ _ _ _)
        (fun o1 o2 (hb : Out.BL o1 o2) => Rel.pure ⟨⟨_, _, _, _, _, _, rfl⟩, hb.1, fun hh => hh, rfl⟩))) (fun hk => ?_)
    refine Rel.bind (splitFit_root o c.lim S none 0 c.n (hok (by simpa using hk)) 3 _ _ rfl) ?_
    rintro ⟨o1, n1⟩ ⟨o2, n2⟩ ⟨hb, hc⟩
    simp only at hb hc
    subst hc
    exact Rel.pure ⟨⟨_, _, _, _, _, _, rfl⟩, hb, fun hh => hh, rfl⟩

/-- `start` on any two cores with the same limits and role: the same first message or the same error. Nothing else
of the core it starts from is read. -/
theorem start_any (o : Oracle) (S : List Item) (c d : Core) (hl : d.lim = c.lim) (hi : d.init = c.init) (ref : Item) :
    Rel (fun p q : Core × List Nat => Core.Bd p.1 q.1 ∧ p.2 = q.2) (c.start o S ref) (d.start o S ref) := by
  obtain ⟨lim, n, init, exact, leafed, rounds, coldAt, coldLo, frames, blast, bsnap, out, ans, hdr, here, there⟩ := c
  obtain ⟨lim', n', init', exact', leafed', rounds', coldAt', coldLo', frames', blast', bsnap', out', ans', hdr', here',
    there'⟩ := d
  simp only at hl hi
  subst hl hi
  unfold Core.start
  dsimp only [Core.clear]
  refine Rel.ite (fun _ => Rel.throw _) (fun _ => ?_)
  refine Rel.bind (root_bd o S ⟨out', blast', bsnap', ans', coldLo', _, rfl⟩) ?_
  rintro ⟨c1, cnt⟩ ⟨c2, cnt2⟩ ⟨hbd, hb, hh, hc⟩
  simp only at hbd hb hh hc
  subst hc
  dsimp only
  rw [finish_eq hbd.lim hb true (fun _ => hh trivial)]
  exact Rel.bind_same (fun m => Rel.pure ⟨hbd, rfl⟩)

theorem restartExact_bd (o : Oracle) (S : List Item) {c d : Core} (h : Core.Bd c d) :
    Rel (fun p q : Core × List Nat => Core.Bd p.1 q.1 ∧ p.2 = q.2) (c.restartExact o S) (d.restartExact o S) := by
  obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := h
  unfold Core.restartExact
  dsimp only
  refine Rel.bind (root_bd o S (c := { c with exact := true, leafed := false, frames := [], here := [], there := [] })
    ⟨ou, bl, bs, an, l, hd, rfl⟩) ?_
  rintro ⟨c1, cnt⟩ ⟨c2, cnt2⟩ ⟨hbd, hb, _, hc⟩
  simp only at hbd hb hc
  subst hc
  dsimp only
  rw [finish_eq hbd.lim hb false (fun hw => by cases hw)]
  exact Rel.bind_same (fun m => Rel.pure ⟨hbd, rfl⟩)

theorem checkMsg_bd (o : Oracle) (S : List Item) {c d : Core} (h : Core.Bd c d) :
    Rel (fun p q : Core × List Nat => Core.Bd p.1 q.1 ∧ p.2 = q.2) (c.checkMsg o S) (d.checkMsg o S) := by
  obtain ⟨ou, bl, bs, an, l, hd, rfl⟩ := h
  have hb : (ou.reset.head tCHECK [] none).body = (c.out.reset.head tCHECK [] none).body :=
    (head_bl (p := c.out.reset) (q := ou.reset) ⟨rfl, rfl⟩ tCHECK [] none).1
  unfold Core.checkMsg
  show Rel _ (Core.finish _ false 1 false >>= _) (Core.finish _ false 1 false >>= _)
  refine Rel.bind (finish_rel ?_ ?_ 1 false) ?_
  · rfl
  · show (ou.reset.head tCHECK [] none).body ++ _ = (c.out.reset.head tCHECK [] none).body ++ _
    rw [hb]
  · rintro m m' rfl
    exact Rel.pure ⟨⟨_, _, _, _, _, _, rfl⟩, rfl⟩

#audit_axioms Pinc.Reconcile.splitFit_root
#audit_axioms Pinc.Reconcile.procPart_cold
#audit_axioms Pinc.Reconcile.turn_bd
#audit_axioms Pinc.Reconcile.root_bd
#audit_axioms Pinc.Reconcile.start_any
#audit_axioms Pinc.Reconcile.restartExact_bd
#audit_axioms Pinc.Reconcile.checkMsg_bd

end Pinc.Reconcile
