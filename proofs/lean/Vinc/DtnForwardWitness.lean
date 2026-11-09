import Vinc.DtnForwardInv

/-!
# A finished bundle stays finished

`Forwarder` remembers every accepted bundle, held or finished, in its memory table `ds` until the bundle's own expiry
(`Seen`: id and expiry). A hold of an id with a remembered, unexpired entry that is not held is refused with
`Err.finished` and leaves exactly the advanced state, so a late duplicate of a hold never re-creates copies the
budget already counted. A new hold takes the first memory slot that is free or whose entry has expired, so an entry
leaves a slot only by being overwritten after its expiry.

This file proves it for every table capacity:

* `hold_finished`: the refusal itself, a statement about `step` for every state;
* `step_keeps_entry`, `poll_keeps_entry`: a memory entry whose expiry is still in the future survives every `step`
  and `poll`;
* `mem_reach`: in every reachable state every held bundle that has not expired has its memory entry;
* `finished_after_release`, `finished_after_forget`: after the release of a bundle at poll (or its forget) that has not
  expired, a hold of the same id is refused with `.finished` and the state is unchanged (`finished_run` is the
  concrete run: hold, deliver, acknowledge, release, hold again);
* `no_reentry`: along any run, an id absent from the bundle slots whose memory entry is live can never get into the
  bundle slots again before that expiry; `copies_after_release`: so a node holds and hands no copy of a released
  bundle until it expires, and the `balance` statement (copies held plus handed equal the copies the single hold
  gave) holds across the release.

Counterparts: `proofs/tla/DtnForward.tla` (`A_NoReHold`, `MemoryKeeps`, `HeldRemembered`) and
`proofs/tla/DtnForwardNet.tla` (`NoReplay`, `Account`, `HeldAlways`).
-/

namespace Vinc.DtnForward

/-- The memory of `f` holds the bundle `id` with the expiry `e`. -/
def Remembers (f : F) (id e : Nat) : Prop := ∃ k, slot f.ds k = some ⟨id, e⟩

/-- A slot of `freeD` is free or expired. -/
theorem freeD_some {now : Nat} {l : List (Option Seen)} {k : Nat} (h : freeD now l = some k) :
    k < l.length ∧ ∀ s, slot l k = some s → s.exp ≤ now := by
  induction l generalizing k with
  | nil => simp [freeD] at h
  | cons o r ih =>
    simp only [freeD, List.findIdx?_cons] at h
    by_cases ho : (o.all fun d => decide (d.exp ≤ now)) = true
    · simp [ho] at h
      subst h
      refine ⟨by simp, fun s hs => ?_⟩
      rw [slot_cons_zero] at hs
      subst hs
      simpa using ho
    · simp [ho] at h
      obtain ⟨j, hj, rfl⟩ := h
      obtain ⟨a, b⟩ := ih (by simpa [freeD] using hj)
      exact ⟨by simpa using a, fun s hs => b s (by simpa [slot_cons_succ] using hs)⟩

/-- **The refusal.** A hold of a bundle that is not held and whose memory entry has not expired is refused as
finished, and the state is the advanced one. -/
theorem hold_finished (f : F) (n id d ex c e : Nat) (hc : c ≠ 0)
    (hb : anyS (·.id == id) (advance f n).bs = false) (hr : Remembers (advance f n) id e)
    (hlive : (advance f n).now < e) : step f n (.hold id d ex c) = (advance f n, .finished) := by
  obtain ⟨k, hk⟩ := hr
  have hs : anyS (fun s => s.id == id && decide ((advance f n).now < s.exp)) (advance f n).ds = true :=
    (anyS_iff _ _).mpr ⟨k, ⟨id, e⟩, hk, by simp [hlive]⟩
  unfold step
  simp only
  have hc' : (c == 0) = false := by simpa using hc
  simp [hc', hb, hs]

/-! ### What a move keeps -/

/-- The bundle slots of `f'` are slots of `f` with the same id and expiry (a move never invents a bundle). -/
def Carry (f f' : F) : Prop :=
  ∀ i b', slot f'.bs i = some b' → ∃ b, slot f.bs i = some b ∧ b.id = b'.id ∧ b.exp = b'.exp

theorem carry_refl (f : F) : Carry f f := fun _ b h => ⟨b, h, rfl, rfl⟩

theorem carry_clear (bs : List (Option Bundle)) (i : Nat) :
    ∀ j b', slot (upd bs i fun _ => none) j = some b' → ∃ b, slot bs j = some b ∧ b.id = b'.id ∧ b.exp = b'.exp := by
  intro j b' h
  by_cases hj : j = i
  · subst hj
    have hl := slot_lt h
    rw [upd_length] at hl
    rw [slot_upd_same _ _ _ hl] at h; cases h
  · rw [slot_upd_ne _ _ _ _ hj] at h
    exact ⟨b', h, rfl, rfl⟩

theorem carry_dropB (f : F) (id : Nat) : Carry f (dropB f id) := by
  intro j b' h
  simp only [dropB] at h
  cases hf : firstIdx (·.id == id) f.bs with
  | none => simp only [hf] at h; exact ⟨b', h, rfl, rfl⟩
  | some i => simp only [hf] at h; exact carry_clear f.bs i j b' h

theorem carry_map (bs : List (Option Bundle)) (i : Nat) (g : Bundle → Bundle) (hi : ∀ b, (g b).id = b.id)
    (he : ∀ b, (g b).exp = b.exp) :
    ∀ j b', slot (upd bs i (Option.map g)) j = some b' → ∃ b, slot bs j = some b ∧ b.id = b'.id ∧ b.exp = b'.exp := by
  intro j b' h
  rw [slot_upd_map] at h
  by_cases hj : j = i
  · simp only [hj, if_true] at h
    cases hs : slot bs i with
    | none => simp [hs] at h
    | some b =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨b, hj ▸ hs, (hi b).symm, (he b).symm⟩
  · simp only [hj, if_false] at h
    exact ⟨b', h, rfl, rfl⟩

/-- A poll changes neither the memory nor the clock, and invents no bundle. -/
theorem poll_facts {f f' : F} {a : Act} (h : poll f = (f', a)) : Carry f f' ∧ f'.ds = f.ds ∧ f'.now = f.now := by
  unfold poll at h
  cases hd : doneIdx f with
  | some i =>
    simp only [hd, Prod.mk.injEq] at h
    rw [← h.1]
    exact ⟨carry_dropB f _, rfl, rfl⟩
  | none =>
    simp only [hd] at h
    cases hq : retr (upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a0 =>
      cases a0 with
      | some y => simp only [hq, Prod.mk.injEq] at h; rw [← h.1]; exact ⟨carry_refl _, rfl, rfl⟩
      | none =>
        simp only [hq] at h
        have hf : (spray { f with ts := ts' }).1 = f' := congrArg Prod.fst h
        rcases spray_cases { f with ts := ts' } with hs | ⟨f1, p, id, c, hs⟩
        · rw [hs] at hf; subst hf; exact ⟨carry_refl _, rfl, rfl⟩
        · obtain ⟨_, li, bi, s, l, b, _, _, hb, hfs, _, _, _, hff⟩ := spray_unfold hs
          rw [hs] at hf; subst hf
          rw [hff]
          exact ⟨carry_map _ _ _ (fun _ => rfl) (fun _ => rfl), rfl, rfl⟩

/-- A step other than a hold changes the memory not at all, and invents no bundle. -/
theorem step_nonhold {f0 f' : F} {n : Nat} {inp : Input} {e : Err} (h : step f0 n inp = (f', e))
    (hn : ∀ id d ex c, inp ≠ .hold id d ex c) :
    Carry f0 f' ∧ f'.ds = f0.ds ∧ f'.now = max f0.now n := by
  cases inp with
  | hold id d ex c => exact absurd rfl (hn id d ex c)
  | tick => simp only [step, Prod.mk.injEq] at h; rw [← h.1]; exact ⟨carry_refl _, rfl, rfl⟩
  | forget id =>
    rcases step_forget f0 n id f' e h with ⟨_, hf, _⟩ | ⟨_, hf, _⟩
    · rw [hf]; exact ⟨carry_refl _, rfl, rfl⟩
    · rw [hf]; exact ⟨carry_dropB _ _, rfl, rfl⟩
  | linkUp peer =>
    obtain ⟨hb, _⟩ := step_link_shape f0 n peer true f' e (by simpa using h)
    unfold step at h
    simp only at h
    split at h
    · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact ⟨carry_refl _, rfl, rfl⟩
    · split at h <;> (simp only [Prod.mk.injEq] at h; rw [← h.1]; exact ⟨carry_refl _, rfl, rfl⟩)
  | linkDown peer =>
    obtain ⟨hb, _⟩ := step_link_shape f0 n peer false f' e (by simpa using h)
    unfold step at h
    simp only at h
    split at h
    · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact ⟨carry_refl _, rfl, rfl⟩
    · split at h <;> (simp only [Prod.mk.injEq] at h; rw [← h.1]; exact ⟨carry_refl _, rfl, rfl⟩)
  | acked peer id =>
    unfold step at h
    simp only at h
    split at h
    · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact ⟨carry_refl _, rfl, rfl⟩
    · split at h
      · split at h
        · simp only [Prod.mk.injEq] at h; rw [← h.1]
          exact ⟨carry_map _ _ _ (fun _ => rfl) (fun _ => rfl), rfl, rfl⟩
        · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact ⟨carry_refl _, rfl, rfl⟩
      · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact ⟨carry_refl _, rfl, rfl⟩

/-- The clock after a step. -/
theorem step_now {f0 f' : F} {n : Nat} {inp : Input} {e : Err} (h : step f0 n inp = (f', e)) :
    f'.now = max f0.now n := by
  cases inp with
  | hold id d ex c =>
    rcases hold_total f0 n id d ex c f' e h 0 with ⟨_, hf⟩ | ⟨_, _, _, _, i, _, k, _, hf⟩
    · rw [hf]; rfl
    · rw [hf]; rfl
  | tick => exact (step_nonhold h (by intro _ _ _ _ hh; cases hh)).2.2
  | linkUp _ => exact (step_nonhold h (by intro _ _ _ _ hh; cases hh)).2.2
  | linkDown _ => exact (step_nonhold h (by intro _ _ _ _ hh; cases hh)).2.2
  | acked _ _ => exact (step_nonhold h (by intro _ _ _ _ hh; cases hh)).2.2
  | forget _ => exact (step_nonhold h (by intro _ _ _ _ hh; cases hh)).2.2

/-- **A live entry survives a step.** A memory entry whose expiry is still in the future after the step is still in
its slot: a slot is only ever overwritten after its entry expired. -/
theorem step_keeps_entry {f0 f' : F} {n : Nat} {inp : Input} {e : Err} (h : step f0 n inp = (f', e)) {id ex : Nat}
    (hr : Remembers f0 id ex) (hlive : f'.now < ex) : Remembers f' id ex := by
  obtain ⟨j, hj⟩ := hr
  cases inp with
  | hold id' d ex' c =>
    rcases hold_total f0 n id' d ex' c f' e h 0 with ⟨_, hf⟩ | ⟨_, _, _, _, i, _, k, hk, hf⟩
    · rw [hf]; exact ⟨j, hj⟩
    · rw [hf] at hlive ⊢
      obtain ⟨hkl, hkx⟩ := freeD_some hk
      by_cases hjk : j = k
      · subst hjk
        have := hkx _ hj
        simp only [advance_now] at this hlive
        have : ex ≤ max f0.now n := this
        have : max f0.now n < ex := hlive
        omega
      · exact ⟨j, by simp only; rw [slot_upd_ne _ _ _ _ hjk]; exact hj⟩
  | tick | linkUp _ | linkDown _ | acked _ _ | forget _ =>
    first
    | (obtain ⟨_, hd, _⟩ := step_nonhold h (by intro _ _ _ _ hh; cases hh); exact ⟨j, by rw [hd]; exact hj⟩)

/-- A poll keeps the memory. -/
theorem poll_keeps_entry {f f' : F} {a : Act} (h : poll f = (f', a)) {id ex : Nat} (hr : Remembers f id ex) :
    Remembers f' id ex := by
  obtain ⟨_, hd, _⟩ := poll_facts h
  obtain ⟨j, hj⟩ := hr
  exact ⟨j, by rw [hd]; exact hj⟩

/-- Every held bundle that has not expired has its memory entry. -/
def Mem (f : F) : Prop := ∀ i b, slot f.bs i = some b → f.now < b.exp → Remembers f b.id b.exp

theorem mem_new (r m now b l t d : Nat) : Mem (F.new r m now b l t d) := by
  intro i bb h
  have : slot (F.new r m now b l t d).bs i = none := slot_replicate_none _ _
  rw [this] at h; cases h

theorem mem_step {f0 f' : F} {n : Nat} {inp : Input} {e : Err} (h : step f0 n inp = (f', e)) (hm : Mem f0) :
    Mem f' := by
  have hmono : f0.now ≤ f'.now := by rw [step_now h]; exact Nat.le_max_left _ _
  have carry : ∀ (i : Nat) (b : Bundle), (∃ b0, slot f0.bs i = some b0 ∧ b0.id = b.id ∧ b0.exp = b.exp) → f'.now < b.exp →
      Remembers f' b.id b.exp := by
    rintro i b ⟨b0, hb0, hid, hex⟩ hlive
    rw [← hid, ← hex] at *
    exact step_keeps_entry h (hm i b0 hb0 (by omega)) hlive
  intro i b hb hlive
  cases inp with
  | hold id' d ex' c =>
    rcases hold_total f0 n id' d ex' c f' e h 0 with ⟨_, hf⟩ | ⟨_, _, _, _, i0, _, k, hk, hf⟩
    · rw [hf] at hb
      exact carry i b ⟨b, hb, rfl, rfl⟩ hlive
    · by_cases hi : i = i0
      · subst hi
        have hl : i < (advance f0 n).bs.length := by
          have := (freeIdx_some ‹freeIdx (advance f0 n).bs = some i›).2; exact this
        have hb' : slot f'.bs i = some ⟨id', d, ex', c, false⟩ := by
          rw [hf]; exact (slot_upd_same _ _ _ hl).trans rfl
        rw [hb'] at hb; cases hb
        have hkl := (freeD_some hk).1
        refine ⟨k, ?_⟩
        rw [hf]; exact slot_upd_same _ _ _ hkl
      · rw [hf] at hb
        simp only at hb
        rw [slot_upd_ne _ _ _ _ hi] at hb
        exact carry i b ⟨b, hb, rfl, rfl⟩ hlive
  | tick | linkUp _ | linkDown _ | acked _ _ | forget _ =>
    first
    | (obtain ⟨hc, _, _⟩ := step_nonhold h (by intro _ _ _ _ hh; cases hh); exact carry i b (hc i b hb) hlive)

theorem mem_poll {f f' : F} {a : Act} (h : poll f = (f', a)) (hm : Mem f) : Mem f' := by
  obtain ⟨hc, hd, hn⟩ := poll_facts h
  intro i b hb hlive
  obtain ⟨b0, hb0, hid, hex⟩ := hc i b hb
  have h0 := hm i b0 hb0 (by rw [hex, ← hn]; exact hlive)
  rw [← hid, ← hex]
  exact poll_keeps_entry h h0

/-- **Memory.** In every reachable state every held bundle that has not expired has its memory entry. -/
theorem mem_reach {f : F} {g : Nat → Nat} (h : Reach f g) : Mem f := by
  induction h with
  | init r m now b l tt dd => exact mem_new r m now b l tt dd
  | holdOk n id d ex c _ hs ih => exact mem_step hs ih
  | forgetOk n id _ hs ih => exact mem_step hs ih
  | stepKeep n inp e _ hs _ _ ih => exact mem_step hs ih
  | release id _ hp ih => exact mem_poll hp ih
  | pollKeep a _ hp _ ih => exact mem_poll hp ih

/-! ### After a release or a forget -/

/-- Clearing a slot of a list with unique ids leaves no slot with that slot's id. -/
theorem uniq_clear_absent : ∀ (l : List (Option Bundle)) (i : Nat) (b : Bundle), Uniq l → slot l i = some b →
    anyS (·.id == b.id) (upd l i fun _ => none) = false
  | [], _, _, _, h => by simp at h
  | o :: r, i, b, ⟨h1, h2⟩, hs => by
    cases i with
    | zero =>
      simp only [slot_cons_zero] at hs; subst hs
      simpa [upd, anyS_cons] using h1 b rfl
    | succ n =>
      have ih := uniq_clear_absent r n b h2 (by simpa [slot_cons_succ] using hs)
      cases o with
      | none => simpa [upd, anyS_cons] using ih
      | some b0 =>
        have hne : (b0.id == b.id) = false := by
          cases hh : (b0.id == b.id) with
          | false => rfl
          | true =>
            have h3 := h1 b0 rfl
            have : anyS (·.id == b0.id) r = true :=
              (anyS_iff _ _).mpr ⟨n, b, by simpa [slot_cons_succ] using hs, by simp at hh ⊢; omega⟩
            rw [h3] at this; simp at this
        simp [upd, anyS_cons, hne, ih]

/-- After `dropB` of a held id, with unique ids, the id is absent. -/
theorem dropB_absent {f : F} (hU : Uniq f.bs) {id : Nat} (h : anyS (·.id == id) f.bs = true) :
    anyS (·.id == id) (dropB f id).bs = false := by
  cases hf : firstIdx (·.id == id) f.bs with
  | none => rw [anyS_eq, hf] at h; simp at h
  | some i =>
    obtain ⟨b, hb, hp, _⟩ := firstIdx_some hf
    have := uniq_clear_absent f.bs i b hU hb
    have hbid : b.id = id := by simpa using hp
    simp only [dropB, hf]
    rw [hbid] at this
    exact this

/-- **A released bundle stays finished.** After the release of a held bundle at poll, a hold of the same id,
whatever its copies, destination and expiry, is refused as finished and leaves exactly the advanced state, as long
as the bundle has not expired. For every table capacity and every reachable state. -/
theorem finished_after_release {f f' : F} {g : Nat → Nat} (hr : Reach f g) {id : Nat}
    (hp : poll f = (f', .release id)) {i : Nat} {b : Bundle} (hb : slot f.bs i = some b) (hid : b.id = id)
    (n d ex c : Nat) (hc : c ≠ 0) (hlive : max f'.now n < b.exp) :
    step f' n (.hold id d ex c) = (advance f' n, .finished) := by
  obtain ⟨hU, _, _⟩ := balance hr
  obtain ⟨_, hd, hn⟩ := poll_facts hp
  have hshape := poll_release_shape hp
  have hrem := mem_reach hr i b hb (by
    have : f'.now ≤ max f'.now n := Nat.le_max_left _ _
    omega)
  rw [hid] at hrem
  refine hold_finished f' n id d ex c b.exp hc ?_ ?_ hlive
  · have hany : anyS (·.id == id) f.bs = true := (anyS_iff _ _).mpr ⟨i, b, hb, by simp [hid]⟩
    have := dropB_absent hU hany
    rw [hshape]; exact this
  · obtain ⟨k, hk⟩ := hrem
    exact ⟨k, by simp only [advance]; rw [hd]; exact hk⟩

/-- **A forgotten bundle stays finished.** The same after `Forget` of a held bundle. -/
theorem finished_after_forget {f f' : F} {g : Nat → Nat} (hr : Reach f g) {id : Nat} (m : Nat)
    (hs : step f m (.forget id) = (f', .ok)) {i : Nat} {b : Bundle} (hb : slot f.bs i = some b) (hid : b.id = id)
    (n d ex c : Nat) (hc : c ≠ 0) (hlive : max f'.now n < b.exp) :
    step f' n (.hold id d ex c) = (advance f' n, .finished) := by
  obtain ⟨hU, _, _⟩ := balance hr
  obtain ⟨_, hd, hnow⟩ := step_nonhold hs (by intro _ _ _ _ hh; cases hh)
  rcases step_forget f m id f' .ok hs with ⟨he, _⟩ | ⟨_, hf, hany⟩
  · cases he
  · have hrem := mem_reach hr i b hb (by
      have h1 : f'.now ≤ max f'.now n := Nat.le_max_left _ _
      have h2 : f.now ≤ f'.now := by rw [hnow]; exact Nat.le_max_left _ _
      omega)
    rw [hid] at hrem
    refine hold_finished f' n id d ex c b.exp hc ?_ ?_ hlive
    · have := dropB_absent (f := advance f m) hU hany
      rw [hf]; exact this
    · obtain ⟨k, hk⟩ := hrem
      exact ⟨k, by simp only [advance]; rw [hd]; exact hk⟩

/-- The concrete run: hold 4 copies for destination 2, link 2 up, deliver, acknowledge, release, then the same hold
again: refused as finished, the node holds nothing, and the state is the advanced one. -/
def finishedRun : (Option Nat × Act × Act × Err × Bool) :=
  let f0 := F.new 3 3 0 1 2 1 1
  let f1 := (step f0 0 (.hold 1 2 100 4)).1
  let f2 := (step f1 0 (.linkUp 2)).1
  let (f3, a3) := poll f2
  let f4 := (step f3 1 (.acked 2 1)).1
  let (f5, a5) := poll f4
  let (f6, e6) := step f5 2 (.hold 1 2 100 4)
  (copiesHeld f6 1, a3, a5, e6, decide (f6 = advance f5 2))

theorem finished_run :
    finishedRun = (none, .send 2 1 0 false, .release 1, .finished, true) := by decide

/-- The same hold once the bundle has expired (clock 100) is accepted: the memory ended with the bundle. -/
def expiredRun : (Option Nat × Err) :=
  let f0 := F.new 3 3 0 1 2 1 1
  let f1 := (step f0 0 (.hold 1 2 100 4)).1
  let f2 := (step f1 0 (.linkUp 2)).1
  let (f3, _) := poll f2
  let f4 := (step f3 1 (.acked 2 1)).1
  let (f5, _) := poll f4
  let (f6, e6) := step f5 100 (.hold 1 2 200 4)
  (copiesHeld f6 1, e6)

theorem expired_run : expiredRun = (some 4, .ok) := by decide

/-- A full memory refuses a new bundle even with a free bundle slot (capacity one, a different id). -/
def fullRun : (Err × Err) :=
  let f0 := F.new 3 3 0 2 2 1 1
  let (f1, e1) := step f0 0 (.hold 1 2 100 4)
  let (_, e2) := step f1 0 (.hold 2 2 100 4)
  (e1, e2)

theorem full_run : fullRun = (.ok, .full) := by decide

/-! ### Along a run -/

/-- Any number of `step`s and `poll`s. -/
inductive Moves : F → F → Prop where
  | refl (f : F) : Moves f f
  | step {f g f' : F} (n : Nat) (inp : Input) (e : Err) : Moves f g → step g n inp = (f', e) → Moves f f'
  | poll {f g f' : F} (a : Act) : Moves f g → poll g = (f', a) → Moves f f'

theorem moves_now {f f' : F} (h : Moves f f') : f.now ≤ f'.now := by
  induction h with
  | refl => exact Nat.le_refl _
  | step n inp e _ hs ih => rw [step_now hs]; exact Nat.le_trans ih (Nat.le_max_left _ _)
  | poll a _ hp ih => rw [(poll_facts hp).2.2]; exact ih

/-- One step cannot bring an id with a live memory entry into the bundle slots. -/
theorem barred_step {g f' : F} {n : Nat} {inp : Input} {e : Err} (h : step g n inp = (f', e)) {id ex : Nat}
    (hr : Remembers g id ex) (hb : anyS (·.id == id) g.bs = false) (hlive : f'.now < ex) :
    anyS (·.id == id) f'.bs = false := by
  cases inp with
  | hold id' d ex' c =>
    by_cases hi : id' = id
    · subst hi
      by_cases hc : c = 0
      · subst hc
        simp [step] at h
        rw [← h.1]; exact hb
      · have hnow := step_now h
        have := hold_finished g n id' d ex' c ex hc hb (by obtain ⟨k, hk⟩ := hr; exact ⟨k, hk⟩)
          (by rw [← advance_now] at hnow; omega)
        rw [this] at h
        have := (Prod.mk.inj h).1
        rw [← this]; exact hb
    · rcases hold_total g n id' d ex' c f' e h 0 with ⟨_, hf⟩ | ⟨_, _, _, _, i, _, k, _, hf⟩
      · rw [hf]; exact hb
      · rw [hf]
        cases hx : anyS (·.id == id) (upd (advance g n).bs i fun _ => some ⟨id', d, ex', c, false⟩) with
        | false => rfl
        | true =>
          rcases anyS_upd_fill _ _ _ _ hx with h1 | h1
          · have h1' : anyS (·.id == id) g.bs = true := h1
            rw [h1'] at hb; exact absurd hb (by simp)
          · simp at h1; omega
  | tick | linkUp _ | linkDown _ | acked _ _ | forget _ =>
    first
    | (obtain ⟨hc, _, _⟩ := step_nonhold h (by intro _ _ _ _ hh; cases hh)
       cases hx : anyS (·.id == id) f'.bs with
       | false => rfl
       | true =>
         obtain ⟨i, b', hs, hp⟩ := (anyS_iff _ _).mp hx
         obtain ⟨b0, hb0, hid, _⟩ := hc i b' hs
         have : anyS (·.id == id) g.bs = true := (anyS_iff _ _).mpr ⟨i, b0, hb0, by simpa [hid] using hp⟩
         rw [this] at hb; exact absurd hb (by simp))

theorem barred_poll {g f' : F} {a : Act} (h : poll g = (f', a)) {id : Nat}
    (hb : anyS (·.id == id) g.bs = false) : anyS (·.id == id) f'.bs = false := by
  obtain ⟨hc, _, _⟩ := poll_facts h
  cases hx : anyS (·.id == id) f'.bs with
  | false => rfl
  | true =>
    obtain ⟨i, b', hs, hp⟩ := (anyS_iff _ _).mp hx
    obtain ⟨b0, hb0, hid, _⟩ := hc i b' hs
    have : anyS (·.id == id) g.bs = true := (anyS_iff _ _).mpr ⟨i, b0, hb0, by simpa [hid] using hp⟩
    rw [this] at hb; exact absurd hb (by simp)

/-- **No re-entry.** Along any run, an id absent from the bundle slots whose memory entry is live can never get
into the bundle slots again before that expiry, and its entry stays. -/
theorem no_reentry {f f' : F} (hm : Moves f f') {id ex : Nat} (hr : Remembers f id ex)
    (hb : anyS (·.id == id) f.bs = false) (hlive : f'.now < ex) :
    anyS (·.id == id) f'.bs = false ∧ Remembers f' id ex := by
  induction hm with
  | refl => exact ⟨hb, hr⟩
  | @step g f1 n inp e hmv hs ih =>
    have hnow := step_now hs
    have hg : g.now < ex := by
      have : g.now ≤ f1.now := by rw [hnow]; exact Nat.le_max_left _ _
      omega
    obtain ⟨hb', hr'⟩ := ih hg
    exact ⟨barred_step hs hr' hb' hlive, step_keeps_entry hs hr' hlive⟩
  | @poll g f1 a hmv hp ih =>
    have hg : g.now < ex := by rw [← (poll_facts hp).2.2]; exact hlive
    obtain ⟨hb', hr'⟩ := ih hg
    exact ⟨barred_poll hp hb', poll_keeps_entry hp hr'⟩

/-- Every move of a reachable state leads to a reachable state. -/
theorem reach_moves {f f' : F} {g : Nat → Nat} (hr : Reach f g) (hm : Moves f f') : ∃ g', Reach f' g' := by
  induction hm with
  | refl => exact ⟨g, hr⟩
  | step n inp e _ hs ih =>
    obtain ⟨g1, h1⟩ := ih
    by_cases hok : e = .ok
    · subst hok
      cases inp with
      | hold id d ex c => exact ⟨_, Reach.holdOk n id d ex c h1 hs⟩
      | forget id => exact ⟨_, Reach.forgetOk n id h1 hs⟩
      | tick => exact ⟨g1, Reach.stepKeep n _ _ h1 hs (by intro _ _ _ _ hh; cases hh) (by intro _ hh; cases hh)⟩
      | linkUp _ => exact ⟨g1, Reach.stepKeep n _ _ h1 hs (by intro _ _ _ _ hh; cases hh) (by intro _ hh; cases hh)⟩
      | linkDown _ => exact ⟨g1, Reach.stepKeep n _ _ h1 hs (by intro _ _ _ _ hh; cases hh) (by intro _ hh; cases hh)⟩
      | acked _ _ => exact ⟨g1, Reach.stepKeep n _ _ h1 hs (by intro _ _ _ _ hh; cases hh) (by intro _ hh; cases hh)⟩
    · exact ⟨g1, Reach.stepKeep n inp e h1 hs (fun _ _ _ _ _ => hok) (fun _ _ => hok)⟩
  | poll a _ hp ih =>
    obtain ⟨g1, h1⟩ := ih
    cases a with
    | release id => exact ⟨_, Reach.release id h1 hp⟩
    | none => exact ⟨g1, Reach.pollKeep _ h1 hp (by intro _ hh; cases hh)⟩
    | send _ _ _ _ => exact ⟨g1, Reach.pollKeep _ h1 hp (by intro _ hh; cases hh)⟩

/-- **The copies of a released bundle stay out.** After the release of a held bundle at poll, along any run until
the bundle's expiry, the node holds no slot of that id and holds and has handed no copy of it: with `balance`, the
copies handed for a bundle never exceed what the single hold gave. -/
theorem copies_after_release {f f' f'' : F} {g : Nat → Nat} (hr : Reach f g) {id : Nat}
    (hp : poll f = (f', .release id)) {i : Nat} {b : Bundle} (hb : slot f.bs i = some b) (hid : b.id = id)
    (hm : Moves f' f'') (hlive : f''.now < b.exp) :
    anyS (·.id == id) f''.bs = false ∧ total f'' id = 0 := by
  obtain ⟨hU, _, _⟩ := balance hr
  obtain ⟨_, hd, hn⟩ := poll_facts hp
  have hshape := poll_release_shape hp
  have hrem := mem_reach hr i b hb (by have := moves_now hm; omega)
  rw [hid] at hrem
  have hany : anyS (·.id == id) f.bs = true := (anyS_iff _ _).mpr ⟨i, b, hb, by simp [hid]⟩
  have hab : anyS (·.id == id) f'.bs = false := by rw [hshape]; exact dropB_absent hU hany
  obtain ⟨k, hk⟩ := hrem
  obtain ⟨hout, _⟩ := no_reentry hm ⟨k, by rw [hd]; exact hk⟩ hab hlive
  obtain ⟨g1, h1⟩ := reach_moves (Reach.release id hr hp) hm
  obtain ⟨_, hL, _⟩ := balance h1
  exact ⟨hout, total_absent hL hout⟩

#print axioms hold_finished
#print axioms finished_after_release
#print axioms finished_after_forget
#print axioms no_reentry
#print axioms copies_after_release

end Vinc.DtnForward
