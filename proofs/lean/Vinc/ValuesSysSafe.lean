import Vinc.ValuesSysModel

/-!
# Safety of the value fetch system

The unbounded counterparts of the TLC invariants of `proofs/tla/ValuesSys.tla`, proved by induction over every
execution of `Vinc.ValuesSys.Step`, for every number of groups, every wanted set, every providers and every adversary
the model allows:

* `Inv.store`, `Inv.events` (property 1, ONLY_VERIFIED): the store never holds a byte that is not a byte of the true
  value (`wr` is never `junk`, a committed group holds `good`), and a `Readable` event or the held first granule
  names a committed group, so never before the store commit, in the in-order path and in the write-through path;
* `verified_grows`: the verified set only grows, restart included;
* `Inv.one` (property 3, final event): at most one final event, `late = 0` (nothing is emitted after it), and the final
  event exists exactly when the fetch is done;
* `Inv.reasons` (properties 2 and 3): each failure has its reason: `EveryProviderLied` only when every named provider
  was evicted for lying, `Deadline` only after the deadline, `NoProvider` only with none named, `Store` only when the
  store refuses, `BadRoot` only for the empty value under another root, and `Complete` only when everything wanted is
  verified and every group verified by this fetch was announced;
* `Inv.liars`: only a provider that is a liar is ever evicted (an honest provider never is), an evicted provider
  holds no unverified work and is not a share holder, and nothing it sent is in the store (`store`);
* `Inv.work` (property 2, work conserved across steal, evict and resume): every missing wanted group is queued or
  assigned to a provider that holds a share;
* `Inv.resume` (property 5): nothing that was verified when the fetch started is asked for.
-/

namespace Vinc.ValuesSys
open Classical

/-- The invariant of every reachable state. -/
structure Inv (c : Cfg) (s : St) : Prop where
  noJunk : ∀ g, s.wr g ≠ .junk
  verGood : ∀ g, s.ver g = true → s.wr g = .good
  ann : ∀ g, 0 < s.ann g → s.ver g = true
  hdVer : ∀ g, s.hd = some g → s.ver g = true
  hdHead : ∀ g, s.hd = some g → g = c.head0 ∧ s.rel = false
  pdGood : ∀ d, s.pd = some d → d.c = .good ∧ (d.committing = true → s.wr d.g = .good)
  pdRun : s.pd ≠ none → s.run = .running
  late : s.late = 0
  doneFin : (s.run = .done ↔ s.nfin = 1) ∧ (s.fin = none ↔ s.nfin = 0) ∧ s.nfin ≤ 1
  ver0 : ∀ g, s.ver0 g = true → s.ver g = true
  announced : ∀ g, s.ver g = true → s.ver0 g = false → 0 < s.ann g ∨ s.hd = some g
  inAP : ∀ p, s.inA p = true → s.inP p = true
  inPL : ∀ p, s.inP p = true → c.listed p = true ∨ s.run = .idle
  liarsOnly : ∀ p, s.lied p = true → c.liars p = true
  evictedLied : s.run ≠ .idle → ∀ p, c.listed p = true → s.inP p = false → s.lied p = true
  holders : s.run = .running → ∀ p, s.inA p = false → ∀ g, s.asg p g = true → s.ver g = true
  work : s.run = .running → ∀ g, c.want g = true → s.ver g = false →
    s.queue g = true ∨ ∃ p, s.inA p = true ∧ s.asg p g = true
  resume : ∀ g, s.reqd g = true → s.ver0 g = false
  reasonLied : s.fin = some .everyProviderLied → (∃ p, c.listed p = true) ∧ ∀ p, c.listed p = true → s.inP p = false
  reasonDeadline : s.fin = some .deadline → ∃ d, c.deadline = some d ∧ d < s.now
  reasonNoProv : s.fin = some .noProvider → ∀ p, c.listed p = false
  reasonStore : s.fin = some .store → c.storeFail = true
  reasonRoot : s.fin = some .badRoot → c.empty = true ∧ c.rootOk = false
  reasonDone : s.fin = some .complete → (∀ g, c.want g = true → s.ver g = true) ∧ s.hd = none
  stateIdle : s.run = .idle → s.fin = none ∧ s.pd = none ∧ s.hd = none ∧ s.rel = false ∧ (∀ g, s.ann g = 0) ∧
    (∀ p, s.inA p = false ∧ s.inP p = false) ∧ s.nfin = 0 ∧ s.late = 0 ∧ (∀ g, s.reqd g = false) ∧
    (∀ p g, s.asg p g = false)


theorem inv_init (c : Cfg) (rs : Nat) : Inv c (init c rs) := by
  apply Inv.mk <;> intros <;> simp_all [init, emp] <;> grind

section step
variable {c : Cfg} {s s' : St}

theorem Inv.tick (h : Inv c s) (n : Nat) (hn : s.now ≤ n) : Inv c { s with now := n } := by
  refine { h with reasonDeadline := ?_ }
  intro e
  obtain ⟨d, hd, hlt⟩ := h.reasonDeadline e
  exact ⟨d, hd, by simp only; omega⟩

theorem Inv.same (h : Inv c s) (e : s' = s) : Inv c s' := e ▸ h

/-- The frames inside a header-accepted state are bookkeeping: no invariant mentions them. -/
theorem Inv.mid (h : Inv c s) (m : List (Nat × Nat × Kind)) : Inv c { s with mid := m } := { h with }

/-- While the fetch runs there is no final event yet. -/
theorem Inv.running_fin (h : Inv c s) (hr : s.run = .running) : s.fin = none ∧ s.nfin = 0 := by
  have h1 := h.doneFin
  have : s.nfin ≠ 1 := fun e => by have := h1.1.2 e; simp_all
  grind

/-- The final event ends a running fetch with the facts that belong to its reason. -/
theorem Inv.ofFinish (h : Inv c s) (hr : s.run = .running) (f : Final)
    (hL : f = .everyProviderLied → (∃ p, c.listed p = true) ∧ ∀ p, c.listed p = true → s.inP p = false)
    (hD : f = .deadline → ∃ d, c.deadline = some d ∧ d < s.now)
    (hN : f = .noProvider → ∀ p, c.listed p = false)
    (hS : f = .store → c.storeFail = true)
    (hR : f = .badRoot → c.empty = true ∧ c.rootOk = false)
    (hC : f = .complete → (∀ g, c.want g = true → s.ver g = true) ∧ s.hd = none) :
    Inv c (finish s f) := by
  obtain ⟨hf, hn⟩ := h.running_fin hr
  have hd : s.run ≠ .done := by simp [hr]
  refine { h with pdRun := ?pdRun, late := ?late, doneFin := ?doneFin, holders := ?holders, work := ?work,
                  stateIdle := ?stateIdle, reasonLied := ?reasonLied, reasonDeadline := ?reasonDeadline,
                  reasonNoProv := ?reasonNoProv, reasonStore := ?reasonStore, reasonRoot := ?reasonRoot,
                  reasonDone := ?reasonDone, pdGood := ?pdGood, evictedLied := ?evictedLied, inPL := ?inPL }
  case pdRun => intro e; simp [finish] at e
  case late => simp [finish, hd, h.late]
  case doneFin => simp [finish, hn]
  case holders => intro e; simp [finish, hr] at e
  case work => intro e; simp [finish, hr] at e
  case stateIdle => intro e; simp [finish, hr] at e
  case reasonLied => intro e; simp [finish] at e; subst e; exact hL rfl
  case reasonDeadline => intro e; simp [finish] at e; subst e; exact hD rfl
  case reasonNoProv => intro e; simp [finish] at e; subst e; exact hN rfl
  case reasonStore => intro e; simp [finish] at e; subst e; exact hS rfl
  case reasonRoot => intro e; simp [finish] at e; subst e; exact hR rfl
  case reasonDone => intro e; simp [finish] at e; subst e; exact hC rfl
  case pdGood => intro d e; simp [finish] at e
  case evictedLied => intro _ p hp hi; exact h.evictedLied (by simp [hr]) p hp hi
  case inPL => intro p hp; have := h.inPL p hp; simp_all [finish]

/-- The three ways a start ends at once. -/
theorem Inv.startFinal (h : Inv c s) (hi : s.run = .idle) (f : Final)
    (hN : f = .noProvider → ∀ p, c.listed p = false)
    (hR : f = .badRoot → c.empty = true ∧ c.rootOk = false)
    (hC : f = .complete → ∀ g, c.want g = true → s.ver g = true)
    (hL : f ≠ .everyProviderLied) (hD : f ≠ .deadline) (hS : f ≠ .store) :
    Inv c (finish { s with run := .running, ver0 := s.ver, reqd := emp, inP := c.listed } f) := by
  obtain ⟨hf, hpd, hhd, hrel, hann, hp, hn, hl, hre, has⟩ := h.stateIdle hi
  refine { h with pdRun := ?pdRun, late := ?late, doneFin := ?doneFin, holders := ?holders, work := ?work,
                  stateIdle := ?stateIdle, reasonLied := ?reasonLied, reasonDeadline := ?reasonDeadline,
                  reasonNoProv := ?reasonNoProv, reasonStore := ?reasonStore, reasonRoot := ?reasonRoot,
                  reasonDone := ?reasonDone, pdGood := ?pdGood, evictedLied := ?evictedLied, inPL := ?inPL,
                  ver0 := ?ver0, announced := ?announced, inAP := ?inAP, resume := ?resume }
  case pdRun => intro e; simp [finish] at e
  case late => simp [finish, hl]
  case doneFin => simp [finish, hn]
  case holders => intro e; simp [finish] at e
  case work => intro e; simp [finish] at e
  case stateIdle => intro e; simp [finish] at e
  case reasonLied => intro e; simp [finish] at e; subst e; exact absurd rfl hL
  case reasonDeadline => intro e; simp [finish] at e; subst e; exact absurd rfl hD
  case reasonNoProv => intro e; simp [finish] at e; subst e; exact hN rfl
  case reasonStore => intro e; simp [finish] at e; subst e; exact absurd rfl hS
  case reasonRoot => intro e; simp [finish] at e; subst e; exact hR rfl
  case reasonDone => intro e; simp [finish] at e; subst e; exact ⟨hC rfl, hhd⟩
  case pdGood => intro d e; simp [finish] at e
  case evictedLied => intro _ p hp' hi'; simp [finish] at hi'; simp_all
  case inPL => intro p hp'; simp [finish] at hp'; simp [hp']
  case ver0 => intro g hg; simpa [finish] using hg
  case announced => intro g hg h0; simp [finish] at hg h0; simp_all
  case inAP => intro p hp'; simp [finish] at hp'; simp_all
  case resume => intro g hg; simp [finish, emp] at hg

/-- The start that hands the work to the queue. -/
theorem Inv.begin (h : Inv c s) (hi : s.run = .idle) :
    Inv c { s with run := .running, ver0 := s.ver, reqd := emp, inP := c.listed, inA := c.listed,
                   queue := dif c.want s.ver, asg := fun _ => emp } := by
  obtain ⟨hf, hpd, hhd, hrel, hann, hp, hn, hl, hre, has⟩ := h.stateIdle hi
  refine { h with pdRun := ?pdRun, late := ?late, doneFin := ?doneFin, holders := ?holders, work := ?work,
                  stateIdle := ?stateIdle, reasonLied := ?reasonLied, reasonDeadline := ?reasonDeadline,
                  reasonNoProv := ?reasonNoProv, reasonStore := ?reasonStore, reasonRoot := ?reasonRoot,
                  reasonDone := ?reasonDone, evictedLied := ?evictedLied, inPL := ?inPL,
                  ver0 := ?ver0, announced := ?announced, inAP := ?inAP, resume := ?resume }
  case pdRun => intro _; rfl
  case late => simpa using hl
  case doneFin => simp [hn, hf]
  case holders => intro _ p _ g; simp [emp]
  case work => intro _ g hw hv; have hv' : s.ver g = false := hv; left; simp [dif, hw, hv']
  case stateIdle => intro e; simp at e
  case reasonLied => intro e; simp [hf] at e
  case reasonDeadline => intro e; simp [hf] at e
  case reasonNoProv => intro e; simp [hf] at e
  case reasonStore => intro e; simp [hf] at e
  case reasonRoot => intro e; simp [hf] at e
  case reasonDone => intro e; simp [hf] at e
  case evictedLied => intro _ p hp' hi'; simp_all
  case inPL => intro p hp'; simp_all
  case ver0 => intro g hg; simpa using hg
  case announced => intro g hg h0; simp at hg h0; simp_all
  case inAP => intro p hp'; simpa using hp'
  case resume => intro g hg; simp [emp] at hg

theorem Inv.plumb (h : Inv c s) (hr : s.run = .running) {q : GSet} {a : Nat → GSet} {r : GSet}
    (po : PlumbOk c s q a r) : Inv c { s with queue := q, asg := a, reqd := r } := by
  refine { h with holders := ?holders, work := ?work, stateIdle := ?stateIdle, resume := ?resume }
  case holders =>
    intro _ p hp g hg
    rcases po.holders p hp with h1 | h1
    · simp_all [emp]
    · exact h1 g hg
  case work => intro _ g hw hv; exact po.conserved g hw hv
  case stateIdle => intro e; simp [hr] at e
  case resume =>
    intro g hg
    rcases po.asks g hg with h1 | ⟨_, h1⟩
    · exact h.resume g h1
    · by_cases hc : s.ver0 g = false
      · exact hc
      · have := h.ver0 g (by simpa using hc); simp_all

/-- Every operation of the scheduler keeps what `PlumbOk` asks, in every state that satisfies the invariant. -/
theorem Op.plumbOk (h : Inv c s) (hr : s.run = .running) (op : Op) (hok : Op.ok c s op) :
    PlumbOk c s (Op.out c s op).1 (Op.out c s op).2.1 (Op.out c s op).2.2 := by
  have hw := h.work hr
  have hh := h.holders hr
  cases op with
  | topUp p chunk =>
    obtain ⟨hp, hch⟩ := hok
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [Op.out, uni] at hg
      by_cases hc : chunk g = true
      · obtain ⟨_, h2, h3⟩ := hch g hc; exact Or.inr ⟨h2, h3⟩
      · left; simpa [hc] using hg
    · intro g hg; simp [Op.out, uni, hg]
    · intro g hwg hvg
      rcases hw g hwg hvg with hq | ⟨q, hq, hqg⟩
      · by_cases hc : chunk g = true
        · right; exact ⟨p, hp, by simp [Op.out, setAt, uni, hc]⟩
        · left; simp [Op.out, dif, hq, hc]
      · by_cases hqp : q = p
        · subst hqp; right; exact ⟨q, hq, by simp [Op.out, setAt, uni, dif, hqg, hvg]⟩
        · right; exact ⟨q, hq, by simp [Op.out, setAt, hqp, hqg]⟩
    · intro q hq
      have hqp : q ≠ p := fun e => by subst e; simp_all
      right; intro g hg
      exact hh q hq g (by simpa [Op.out, setAt, hqp] using hg)
  | steal p v tail =>
    obtain ⟨hpv, hp, hv, hthief, htail⟩ := hok
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [Op.out, uni] at hg
      by_cases hc : tail g = true
      · obtain ⟨_, h2, h3⟩ := htail g hc; exact Or.inr ⟨h2, h3⟩
      · left; simpa [hc] using hg
    · intro g hg; simp [Op.out, uni, hg]
    · intro g hwg hvg
      rcases hw g hwg hvg with hq | ⟨q, hq, hqg⟩
      · left; simpa [Op.out] using hq
      · by_cases hqp : q = p
        · subst hqp; exact absurd (hthief g hqg) (by simp [hvg])
        · by_cases hqv : q = v
          · subst hqv
            by_cases hc : tail g = true
            · right; exact ⟨p, hp, by simp [Op.out, setAt, uni, hc]⟩
            · right; exact ⟨q, hq, by simp [Op.out, setAt, dif, hqg, hc, Ne.symm hpv, hpv]⟩
          · right; exact ⟨q, hq, by simp [Op.out, setAt, hqp, hqv, hqg]⟩
    · intro q hq
      have hqp : q ≠ p := fun e => by subst e; simp_all
      have hqv : q ≠ v := fun e => by subst e; simp_all
      right; intro g hg
      exact hh q hq g (by simpa [Op.out, setAt, hqp, hqv] using hg)
  | redial p =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [Op.out, uni] at hg
      by_cases hc : s.reqd g = true
      · exact Or.inl hc
      · right; simp at hg; simp_all
    · intro g hg; simp [Op.out, uni, hg]
    · intro g hwg hvg; simpa [Op.out] using hw g hwg hvg
    · intro q hq; right; intro g hg; exact hh q hq g (by simpa [Op.out] using hg)

/-- An accepted frame: the group is on its way into the store, with the bytes of a frame that verifies. -/
theorem Inv.accept (h : Inv c s) (hr : s.run = .running) (k : Kind) (hk : k.verifies = true) (g : Nat) :
    Inv c { s with pd := some { g := g, c := k.content, committing := false } } := by
  refine { h with pdGood := ?pdGood, pdRun := ?pdRun, stateIdle := ?stateIdle }
  case stateIdle => intro e; simp [hr] at e
  case pdGood => intro d e; simp at e; subst e; simp [Kind.verifies_genuine k hk]
  case pdRun => intro _; exact hr

theorem Inv.write (h : Inv c s) (hr : s.run = .running) (d : Pd) (hd : s.pd = some d) (_hc : d.committing = false) :
    Inv c { s with wr := fun x => if x = d.g then d.c else s.wr x, pd := some { d with committing := true } } := by
  have hg := (h.pdGood d hd).1
  refine { h with noJunk := ?noJunk, verGood := ?verGood, pdGood := ?pdGood, pdRun := ?pdRun, stateIdle := ?stateIdle }
  case stateIdle => intro e; simp [hr] at e
  case noJunk => intro x; by_cases hx : x = d.g <;> simp [hx, hg, h.noJunk x]
  case verGood => intro x hx; by_cases hxx : x = d.g <;> simp [hxx, hg, h.verGood x hx] <;> grind
  case pdGood => intro d' e; simp at e; subst e; simp [hg]
  case pdRun => intro _; exact hr

theorem ins_apply (a : GSet) (g x : Nat) : ins a g x = (a x || decide (x = g)) := rfl

/-- The commit of the first granule's group: the group is verified, its announcement is held back. -/
theorem Inv.commitHold (h : Inv c s) (hr : s.run = .running) (d : Pd) (hd : s.pd = some d)
    (hc : d.committing = true) (hrel : s.rel = false) (hh : d.g = c.head0) :
    Inv c { { s with ver := ins s.ver d.g, pd := none } with hd := some d.g } := by
  have hw := (h.pdGood d hd).2 hc
  obtain ⟨hf, hn⟩ := h.running_fin hr
  refine { h with verGood := ?verGood, hdVer := ?hdVer, hdHead := ?hdHead, pdGood := ?pdGood, pdRun := ?pdRun,
                  announced := ?announced, work := ?work, holders := ?holders, ver0 := ?ver0, stateIdle := ?stateIdle,
                  reasonDone := ?reasonDone, ann := ?ann }
  case verGood => intro x hx; simp only [ins_apply] at hx; by_cases e : x = d.g <;> simp_all [h.verGood x]
  case hdVer => intro x hx; simp at hx; subst hx; simp [ins_apply]
  case hdHead => intro x hx; simp at hx; subst hx; simp [hh, hrel]
  case pdGood => intro d' e; simp at e
  case pdRun => intro e; simp at e
  case announced =>
    intro x hx h0
    by_cases e : x = d.g
    · right; simp [e]
    · left
      have hx' : s.ver x = true := by simpa [ins_apply, e] using hx
      rcases h.announced x hx' h0 with h1 | h1
      · exact h1
      · exact absurd ((h.hdHead x h1).1.trans hh.symm) e
  case work =>
    intro _ x hw' hv; simp only [ins_apply] at hv
    have hv' : s.ver x = false := (by simpa using hv : s.ver x = false ∧ ¬x = d.g).1
    exact h.work hr x hw' hv'
  case holders =>
    intro _ p hp x hx; simp only [ins_apply]; simp [h.holders hr p hp x hx]
  case ver0 => intro x hx; simp only [ins_apply]; simp [h.ver0 x hx]
  case stateIdle => intro e; simp [hr] at e
  case reasonDone => intro e; simp [hf] at e
  case ann => intro x hx; simp only [ins_apply]; simp [h.ann x hx]

/-- The commit of any other group: the group is verified and announced. -/
theorem Inv.commitRead (h : Inv c s) (hr : s.run = .running) (d : Pd) (hd : s.pd = some d)
    (hc : d.committing = true) :
    Inv c (readable { s with ver := ins s.ver d.g, pd := none } d.g) := by
  have hw := (h.pdGood d hd).2 hc
  obtain ⟨hf, hn⟩ := h.running_fin hr
  have hdn : s.run ≠ .done := by simp [hr]
  refine { h with verGood := ?verGood, ann := ?ann, hdVer := ?hdVer, pdGood := ?pdGood, pdRun := ?pdRun,
                  late := ?late, announced := ?announced, work := ?work, holders := ?holders, ver0 := ?ver0,
                  stateIdle := ?stateIdle, reasonDone := ?reasonDone }
  case verGood =>
    intro x hx; simp only [readable, ins_apply] at hx
    by_cases e : x = d.g
    · simp [readable, e, hw]
    · simp_all [readable, h.verGood x]
  case ann =>
    intro x hx; simp only [readable, ins_apply]; by_cases e : x = d.g
    · simp [e]
    · have : 0 < s.ann x := by simpa [readable, e] using hx
      simp [h.ann x this]
  case hdVer => intro x hx; have := h.hdVer x hx; simp only [readable, ins_apply]; simp [this]
  case pdGood => intro d' e; simp [readable] at e
  case pdRun => intro e; simp [readable] at e
  case late => simp [readable, hdn, h.late]
  case announced =>
    intro x hx h0
    by_cases e : x = d.g
    · left; simp [readable, e]; omega
    · have hx' : s.ver x = true := by simpa [readable, ins_apply, e] using hx
      simpa [readable, e] using h.announced x hx' h0
  case work =>
    intro _ x hw' hv; simp only [readable, ins_apply] at hv
    have hv' : s.ver x = false := (by simpa using hv : s.ver x = false ∧ ¬x = d.g).1
    exact h.work hr x hw' hv'
  case holders => intro _ p hp x hx; simp only [readable, ins_apply]; simp [h.holders hr p hp x hx]
  case ver0 => intro x hx; simp only [readable, ins_apply]; simp [h.ver0 x hx]
  case stateIdle => intro e; simp [readable, hr] at e
  case reasonDone => intro e; simp [readable, hf] at e

/-- HEAD_HOLD: the first granule is announced. -/
theorem Inv.ofRelease (h : Inv c s) (hr : s.run = .running) : Inv c (releaseHd s) := by
  obtain ⟨hf, hn⟩ := h.running_fin hr
  have hdn : s.run ≠ .done := by simp [hr]
  unfold releaseHd
  cases hh : s.hd with
  | none => exact h
  | some g =>
    have hg := h.hdVer g hh
    refine { h with ann := ?ann, hdVer := ?hdVer, hdHead := ?hdHead, late := ?late, announced := ?announced,
                    stateIdle := ?stateIdle, reasonDone := ?reasonDone }
    case ann =>
      intro x hx; by_cases e : x = g
      · simp [readable, e, hg]
      · exact h.ann x (by simpa [readable, e] using hx)
    case hdVer => intro x hx; simp at hx
    case hdHead => intro x hx; simp at hx
    case late => simp [readable, hdn, h.late]
    case announced =>
      intro x hx h0
      by_cases e : x = g
      · left; simp [readable, e]; omega
      · rcases h.announced x hx h0 with h1 | h1
        · left; simpa [readable, e] using h1
        · exfalso; rw [hh] at h1; simp at h1; exact e h1.symm
    case stateIdle => intro e; simp [readable, hr] at e
    case reasonDone => intro e; simp [readable, hf] at e

theorem Inv.ofEvictBooks (h : Inv c s) (hr : s.run = .running) (p : Nat) (hp : s.inP p = true)
    (hl : c.liars p = true) : Inv c (evictBooks s p) := by
  obtain ⟨hf, hn⟩ := h.running_fin hr
  by_cases h1 : ∀ q, (evict1 s p).inA q = false
  · have e2 : evict2 s p = { evict1 s p with inA := (evict1 s p).inP } := by simp [evict2, h1]
    simp only [evictBooks, e2]
    refine { h with inAP := ?inAP, inPL := ?inPL, liarsOnly := ?liarsOnly, evictedLied := ?evictedLied,
                    holders := ?holders, work := ?work, stateIdle := ?stateIdle, reasonLied := ?reasonLied }
    case reasonLied => intro e; simp [evict1, hf] at e
    case inAP => intro q hq; simpa [evict1] using hq
    case inPL =>
      intro q hq
      by_cases e : q = p
      · simp [evict1, e] at hq
      · have hq' : s.inP q = true := by simpa [evict1, e] using hq
        rcases h.inPL q hq' with h2 | h2
        · exact Or.inl h2
        · exact absurd h2 (by simp [hr])
    case liarsOnly => intro q hq; by_cases e : q = p <;> simp_all [evict1, h.liarsOnly q]
    case evictedLied =>
      intro _ q hq hi; by_cases e : q = p <;> simp_all [evict1, h.evictedLied (by simp [hr]) q hq]
    case holders =>
      intro _ q hq x hx
      by_cases e : q = p
      · simp_all [evict1, emp]
      · have hia : s.inA q = false := by
          by_cases ha : s.inA q = true
          · have := h.inAP q ha; simp_all [evict1]
          · simpa using ha
        simp_all [evict1, h.holders hr q hia x]
    case work =>
      intro _ x hw hv
      rcases h.work hr x hw hv with h2 | ⟨q, hq, hx⟩
      · left; simp [evict1, h2]
      · by_cases e : q = p
        · subst e; have hv' : s.ver x = false := hv; left; simp [evict1, dif, hx, hv']
        · exfalso; have := h1 q; simp [evict1, e, hq] at this
    case stateIdle => intro e; simp [evict1, hr] at e
  · have e2 : evict2 s p = evict1 s p := by simp [evict2, h1]
    simp only [evictBooks, e2]
    refine { h with inAP := ?inAP, inPL := ?inPL, liarsOnly := ?liarsOnly, evictedLied := ?evictedLied,
                    holders := ?holders, work := ?work, stateIdle := ?stateIdle, reasonLied := ?reasonLied }
    case reasonLied => intro e; simp [evict1, hf] at e
    case inAP => intro q hq; by_cases e : q = p <;> simp_all [evict1, h.inAP q]
    case inPL =>
      intro q hq
      by_cases e : q = p
      · simp [evict1, e] at hq
      · have hq' : s.inP q = true := by simpa [evict1, e] using hq
        rcases h.inPL q hq' with h2 | h2
        · exact Or.inl h2
        · exact absurd h2 (by simp [hr])
    case liarsOnly => intro q hq; by_cases e : q = p <;> simp_all [evict1, h.liarsOnly q]
    case evictedLied =>
      intro _ q hq hi; by_cases e : q = p <;> simp_all [evict1, h.evictedLied (by simp [hr]) q hq]
    case holders =>
      intro _ q hq x hx
      by_cases e : q = p
      · simp_all [evict1, emp]
      · simp_all [evict1, h.holders hr q]
    case work =>
      intro _ x hw hv
      rcases h.work hr x hw hv with h2 | ⟨q, hq, hx⟩
      · left; simp [evict1, h2]
      · by_cases e : q = p
        · subst e; have hv' : s.ver x = false := hv; left; simp [evict1, dif, hx, hv']
        · right; exact ⟨q, by simp [evict1, e, hq], by simp [evict1, e, hx]⟩
    case stateIdle => intro e; simp [evict1, hr] at e

theorem Inv.evict (h : Inv c s) (hr : s.run = .running) (p : Nat) (hp : s.inP p = true)
    (hl : c.liars p = true) : Inv c (evictSt s p) := by
  have hb := h.ofEvictBooks hr p hp hl
  obtain ⟨hf, hn⟩ := h.running_fin hr
  unfold evictSt
  split
  next h1 =>
    -- every candidate is gone: the fetch fails
    have hbr : (evictBooks s p).run = .running := by
      have : (evict2 s p).run = s.run := by unfold evict2; split <;> rfl
      simpa [evictBooks, this] using hr
    have hnone : ∀ q, (evictBooks s p).inP q = false := by
      intro q
      by_cases h3 : ∀ q, (evict1 s p).inA q = false
      · have := h1 q; simpa [evict2, h3, evictBooks] using this
      · exfalso
        apply h3
        intro q'
        have := h1 q'
        simpa [evict2, h3] using this
    have hlist : c.listed p = true := by
      rcases h.inPL p hp with h2 | h2
      · exact h2
      · exact absurd h2 (by simp [hr])
    have hfin := hb.ofFinish hbr .everyProviderLied
      (fun _ => And.intro ⟨p, hlist⟩ (fun (q : Nat) (_ : c.listed q = true) => hnone q)) (by simp) (by simp) (by simp) (by simp) (by simp)
    -- the queue does not matter once the fetch is done
    refine { hfin with work := ?work, holders := ?holders }
    case work => intro e; simp [finish] at e
    case holders => intro e; simp [finish] at e
  next h1 => exact hb

theorem Inv.restart (h : Inv c s) (n : Nat) :
    Inv c { (init c n) with wr := s.wr, ver := s.ver, ver0 := s.ver } := by
  refine { h with ann := ?ann, hdVer := ?hdVer, hdHead := ?hdHead, pdGood := ?pdGood, pdRun := ?pdRun, late := ?late,
                  doneFin := ?doneFin, announced := ?announced, inAP := ?inAP, inPL := ?inPL, liarsOnly := ?liarsOnly,
                  evictedLied := ?evictedLied, holders := ?holders, work := ?work, resume := ?resume,
                  reasonLied := ?reasonLied, reasonDeadline := ?reasonDeadline, reasonNoProv := ?reasonNoProv,
                  reasonStore := ?reasonStore, reasonRoot := ?reasonRoot, reasonDone := ?reasonDone,
                  stateIdle := ?stateIdle, ver0 := ?ver0 }
  case ann => intro g hg; simp [init] at hg
  case hdVer => intro g hg; simp [init] at hg
  case hdHead => intro g hg; simp [init] at hg
  case pdGood => intro d hd; simp [init] at hd
  case pdRun => intro e; simp [init] at e
  case late => simp [init]
  case doneFin => simp [init]
  case announced => intro g hg h0; simp at h0; simp_all
  case inAP => intro p hp; simp [init] at hp
  case inPL => intro p hp; simp [init] at hp
  case liarsOnly => intro p hp; simp [init] at hp
  case evictedLied => intro e; simp [init] at e
  case holders => intro e; simp [init] at e
  case work => intro e; simp [init] at e
  case resume => intro g hg; simp [init, emp] at hg
  case reasonLied => intro e; simp [init] at e
  case reasonDeadline => intro e; simp [init] at e
  case reasonNoProv => intro e; simp [init] at e
  case reasonStore => intro e; simp [init] at e
  case reasonRoot => intro e; simp [init] at e
  case reasonDone => intro e; simp [init] at e
  case stateIdle => intro _; simp [init, emp]
  case ver0 => intro g hg; simpa using hg

theorem Inv.step (h : Inv c s) (st : Step c s s') : Inv c s' := by
  cases st with
  | startBadRoot h1 h2 h3 =>
    exact h.startFinal h1 .badRoot (by simp) (fun _ => ⟨h2, h3⟩) (by simp) (by simp) (by simp) (by simp)
  | startComplete h1 h2 h3 =>
    exact h.startFinal h1 .complete (by simp) (by simp) (fun _ => h3) (by simp) (by simp) (by simp)
  | startNoProvider h1 h2 h3 h4 =>
    exact h.startFinal h1 .noProvider (fun _ => h4) (by simp) (by simp) (by simp) (by simp) (by simp)
  | begin h1 h2 h3 h4 => exact h.begin h1
  | sched op h1 h2 hok => exact h.plumb h1 (Op.plumbOk h h1 op hok)
  | acceptHdr p g k h1 h2 h3 h4 h5 h6 h7 => exact h.mid _
  | acceptEnd p g k h1 h2 h3 h4 h5 h6 => exact (h.accept h1 k h6 g).mid _
  | acceptDup p g k h1 h2 h3 h4 h5 => exact h.mid _
  | accept p g k h1 h2 h3 h4 h5 h6 h7 => exact h.accept h1 k h7 g
  | skip p g h1 h2 h3 h4 h5 => exact h
  | acceptAhead p g k h1 h2 h3 h4 h5 h6 h7 => exact h.accept h1 k h7 g
  | evict p h1 h2 h3 h4 => exact h.evict h1 p h3 h4
  | write d h1 h2 h3 => exact h.write h1 d h2 h3
  | writeRefused d h1 h2 h3 h4 =>
    exact h.ofFinish (c := c) h1 .store (by simp) (by simp) (by simp) (fun _ => h4) (by simp) (by simp)
  | commit d h1 h2 h3 =>
    unfold commitSt
    split
    next hc => exact h.commitHold h1 d h2 h3 hc.1 hc.2
    next hc => exact h.commitRead h1 d h2 h3
  | commitRefused d h1 h2 h3 h4 =>
    exact h.ofFinish (c := c) h1 .store (by simp) (by simp) (by simp) (fun _ => h4) (by simp) (by simp)
  | release h1 h2 h3 => exact h.ofRelease h1
  | check h1 h2 h3 =>
    have hr := h.ofRelease h1
    have hv : ∀ g, (releaseHd s).ver g = s.ver g := by intro g; unfold releaseHd; cases s.hd <;> simp [readable]
    have hrun : (releaseHd s).run = .running := by unfold releaseHd; cases s.hd <;> simp [readable, h1]
    have hhd : (releaseHd s).hd = none := by
      rcases hh : s.hd with _ | g <;> simp [releaseHd, hh, readable]
    exact hr.ofFinish hrun .complete (by simp) (by simp) (by simp) (by simp) (by simp)
      (fun _ => ⟨fun g hg => by rw [hv]; exact h3 g hg, hhd⟩)
  | tick h1 h2 => exact h.tick (s.now + 1) (by omega)
  | deadlineFire d h1 h2 h3 h4 =>
    exact h.ofFinish (c := c) h1 .deadline (by simp) (fun _ => ⟨d, h3, h4⟩) (by simp) (by simp) (by simp) (by simp)
  | restart h1 h2 => exact h.restart _


/-- Every reachable state satisfies the invariant. -/
theorem reach_inv {c : Cfg} {rs : Nat} {s : St} (h : Reach c rs s) : Inv c s := by
  induction h with
  | init => exact inv_init c rs
  | step s s' _ st ih => exact ih.step st

/-- The verified set only grows (a restart keeps it). -/
theorem verified_grows {c : Cfg} {s s' : St} (st : Step c s s') : ∀ g, s.ver g = true → s'.ver g = true := by
  intro g hg
  cases st with
  | startBadRoot h1 h2 h3 => simpa [finish] using hg
  | startComplete h1 h2 h3 => simpa [finish] using hg
  | startNoProvider h1 h2 h3 => simpa [finish] using hg
  | begin h1 h2 h3 h4 => simpa using hg
  | sched op h1 h2 hok => simpa using hg
  | acceptHdr p g' k h1 h2 h3 h4 h5 h6 h7 => simpa using hg
  | acceptEnd p g' k h1 h2 h3 h4 h5 h6 => simpa using hg
  | acceptDup p g' k h1 h2 h3 h4 h5 => simpa using hg
  | accept p g' k h1 h2 h3 h4 h5 h6 h7 => simpa using hg
  | skip p g' h1 h2 h3 h4 h5 => exact hg
  | acceptAhead p g' k h1 h2 h3 h4 h5 h6 h7 => simpa using hg
  | evict p h1 h2 h3 h4 =>
    unfold evictSt; split
    · have : (evict2 s p).ver = s.ver := by unfold evict2; split <;> rfl
      simpa [finish, this] using hg
    · simp only [evictBooks]; have : (evict2 s p).ver = s.ver := by unfold evict2; split <;> rfl
      simpa [this] using hg
  | write d h1 h2 h3 => simpa using hg
  | writeRefused d h1 h2 h3 h4 => simpa [finish] using hg
  | commit d h1 h2 h3 =>
    unfold commitSt; split
    · simp [ins]; exact Or.inl hg
    · simp [readable, ins]; exact Or.inl hg
  | commitRefused d h1 h2 h3 h4 => simpa [finish] using hg
  | release h1 h2 h3 => unfold releaseHd; cases s.hd <;> simpa [readable] using hg
  | check h1 h2 h3 => unfold releaseHd; cases s.hd <;> simpa [finish, readable] using hg
  | tick h1 h2 => simpa using hg
  | deadlineFire d h1 h2 h3 h4 => simpa [finish] using hg
  | restart h1 h2 => simpa using hg

end step

/-! ### The theorems of the properties -/

section thms
variable {c : Cfg} {rs : Nat} {s : St}

/-- PROPERTY 1, ONLY_VERIFIED: no byte of the store is anything but a byte of the true value, in the in-order path and
in the write-through path, whatever the adversary does; a committed group holds the true bytes. -/
theorem only_verified (h : Reach c rs s) :
    (∀ g, s.wr g ≠ .junk) ∧ (∀ g, s.ver g = true → s.wr g = .good) := by
  have i := reach_inv h; exact ⟨i.noJunk, i.verGood⟩

/-- PROPERTY 1: a `Readable` event, and the held first granule, name committed groups with the true bytes: never
before the store commit. -/
theorem readable_after_commit (h : Reach c rs s) :
    (∀ g, 0 < s.ann g → s.ver g = true ∧ s.wr g = .good) ∧ (∀ g, s.hd = some g → s.ver g = true ∧ s.wr g = .good) := by
  have i := reach_inv h
  exact ⟨fun g hg => ⟨i.ann g hg, i.verGood g (i.ann g hg)⟩, fun g hg => ⟨i.hdVer g hg, i.verGood g (i.hdVer g hg)⟩⟩

/-- PROPERTY 3: at most one final event, none is emitted after it, and the final event exists exactly when the fetch
is done. -/
theorem one_final_event (h : Reach c rs s) :
    s.late = 0 ∧ s.nfin ≤ 1 ∧ (s.run = .done ↔ s.nfin = 1) ∧ (s.fin = none ↔ s.nfin = 0) := by
  have i := reach_inv h; exact ⟨i.late, i.doneFin.2.2, i.doneFin.1, i.doneFin.2.1⟩

/-- PROPERTY 3: only a provider that sent a bad frame is evicted; an honest provider (not in `liars`) never is. -/
theorem liar_only (h : Reach c rs s) (p : Nat) (hl : s.lied p = true) : c.liars p = true :=
  (reach_inv h).liarsOnly p hl

/-- PROPERTY 3: an evicted provider is not a candidate, holds no share, and holds no unverified work. -/
theorem evicted_holds_nothing (h : Reach c rs s) (hr : s.run = .running) (p : Nat) (hp : s.inP p = false) :
    s.inA p = false ∧ ∀ g, s.asg p g = true → s.ver g = true := by
  have i := reach_inv h
  have ha : s.inA p = false := by
    by_cases e : s.inA p = true
    · have := i.inAP p e; simp_all
    · simpa using e
  exact ⟨ha, i.holders hr p ha⟩

/-- PROPERTY 3: every provider named is evicted for lying when the fetch fails with `EveryProviderLied`. -/
theorem every_provider_lied (h : Reach c rs s) (hf : s.fin = some .everyProviderLied) :
    (∃ p, c.listed p = true) ∧ ∀ p, c.listed p = true → s.inP p = false ∧ s.lied p = true := by
  have i := reach_inv h
  obtain ⟨hex, hall⟩ := i.reasonLied hf
  refine ⟨hex, fun p hp => ⟨hall p hp, ?_⟩⟩
  exact i.evictedLied (by intro e; have := i.stateIdle e; simp_all) p hp (hall p hp)

/-- PROPERTY 2: the right reason for each failure. -/
theorem failure_reasons (h : Reach c rs s) :
    (s.fin = some .deadline → ∃ d, c.deadline = some d ∧ d < s.now) ∧ (s.fin = some .noProvider → ∀ p, c.listed p = false) ∧
    (s.fin = some .store → c.storeFail = true) ∧ (s.fin = some .badRoot → c.empty = true ∧ c.rootOk = false) := by
  have i := reach_inv h; exact ⟨i.reasonDeadline, i.reasonNoProv, i.reasonStore, i.reasonRoot⟩

/-- PROPERTY 2: `Complete` only when every wanted group is verified and every group this fetch verified was announced
(the held first granule released first). -/
theorem complete_means_all (h : Reach c rs s) (hf : s.fin = some .complete) :
    (∀ g, c.want g = true → s.ver g = true) ∧ s.hd = none ∧
      (∀ g, c.want g = true → s.ver0 g = false → 0 < s.ann g) := by
  have i := reach_inv h
  obtain ⟨hv, hd⟩ := i.reasonDone hf
  refine ⟨hv, hd, fun g hg h0 => ?_⟩
  rcases i.announced g (hv g hg) h0 with h1 | h1
  · exact h1
  · simp_all

/-- PROPERTY 2, work conserved: while the fetch runs every missing wanted group is queued or assigned to a provider
that holds a share. -/
theorem work_conserved (h : Reach c rs s) (hr : s.run = .running) :
    ∀ g, c.want g = true → s.ver g = false → s.queue g = true ∨ ∃ p, s.inA p = true ∧ s.asg p g = true :=
  (reach_inv h).work hr

/-- PROPERTY 5, resume: nothing that was verified when the fetch started is asked for. -/
theorem resume_not_asked (h : Reach c rs s) : ∀ g, s.reqd g = true → s.ver0 g = false :=
  (reach_inv h).resume

/-- The verified set of any run only grows. -/
theorem reach_grows {c : Cfg} {rs : Nat} {s s' : St} (_h : Reach c rs s) (st : Step c s s') :
    ∀ g, s.ver g = true → s'.ver g = true := verified_grows st

end thms

end Vinc.ValuesSys
