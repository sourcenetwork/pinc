import Vinc.DtnForwardInv

/-!
# The transfer table: one transfer per (bundle, peer), and the send counter

`TI f` says two things of every state reachable from a new forwarder:

* **one transfer per (bundle, peer)**: no two transfer slots share a bundle and a peer;
* **the send counter**: a transfer that is still sending has `1 <= sends <= max 1 maxSends`.

`reach_ti` proves both for every reachable state, for every capacity and policy. `gives_up_exact` is the consequence for
the give-up: a transfer gives up at exactly `max 1 maxSends` sends (the first send is always made, so a limit of 0 or 1
means one send). The proof goes through one relation `R f f'` between the transfer tables before and after any
operation: every transfer slot of the new table is an old one with the same bundle and peer (its timer or phase may
change, a send counter only through the retransmission with sends left), or the one new transfer of a handover, whose
(bundle, peer) had no transfer.
-/

namespace Vinc.DtnForward

def TInv (f : F) : Prop :=
  (∀ i j (t t' : Transfer), slot f.ts i = some t → slot f.ts j = some t' → t.bundle = t'.bundle → t.peer = t'.peer → i = j) ∧
  (∀ i (t : Transfer) r s, slot f.ts i = some t → t.phase = .sent r s → 1 ≤ s ∧ s ≤ max 1 f.maxSends)

/-- One operation's effect on the transfer table. -/
def R (f f' : F) : Prop :=
  f'.maxSends = f.maxSends ∧
  (∀ i (t' : Transfer), slot f'.ts i = some t' →
    (∃ t : Transfer, slot f.ts i = some t ∧ t'.bundle = t.bundle ∧ t'.peer = t.peer ∧
      ((∀ r s, t'.phase = .sent r s → ∃ r0, t.phase = .sent r0 s) ∨
        ∃ s, t.phase = .sent 0 s ∧ s < f.maxSends ∧ t'.phase = .sent f.retry (sat8 (s + 1)))) ∨
    (slot f.ts i = none ∧ t'.phase = .sent f.retry 1 ∧
      anyS (fun u : Transfer => u.bundle == t'.bundle && u.peer == t'.peer) f.ts = false)) ∧
  (∀ i j, slot f.ts i = none → slot f.ts j = none → slot f'.ts i ≠ none → slot f'.ts j ≠ none → i = j)

theorem ti_of_R {f f' : F} (h : TInv f) (hr : R f f') : TInv f' := by
  obtain ⟨hu, hs⟩ := h
  obtain ⟨hm, hslots, hnew⟩ := hr
  refine ⟨fun i j t t' hi hj hb hp => ?_, fun i t r s hi hph => ?_⟩
  · rcases hslots i t hi with ⟨a, ha, hab, hap, _⟩ | ⟨hfi, _, hno⟩ <;>
      rcases hslots j t' hj with ⟨b, hb', hbb, hbp, _⟩ | ⟨hfj, _, hno2⟩
    · exact hu i j a b ha hb' (by rw [← hab, ← hbb, hb]) (by rw [← hap, ← hbp, hp])
    · exfalso
      have : anyS (fun u : Transfer => u.bundle == t'.bundle && u.peer == t'.peer) f.ts = true :=
        (anyS_iff _ _).mpr ⟨i, a, ha, by simp [← hb, ← hp, hab, hap]⟩
      rw [hno2] at this; exact absurd this (by simp)
    · exfalso
      have : anyS (fun u : Transfer => u.bundle == t.bundle && u.peer == t.peer) f.ts = true :=
        (anyS_iff _ _).mpr ⟨j, b, hb', by simp [hb, hp, hbb, hbp]⟩
      rw [hno] at this; exact absurd this (by simp)
    · exact hnew i j hfi hfj (by rw [hi]; simp) (by rw [hj]; simp)
  · rw [hm]
    rcases hslots i t hi with ⟨a, ha, _, _, hph' | ⟨s0, ha0, hlt, hph'⟩⟩ | ⟨_, hph', _⟩
    · obtain ⟨r0, hr0⟩ := hph' r s hph
      exact hs i a r0 s ha hr0
    · rw [hph] at hph'
      simp only [Phase.sent.injEq] at hph'
      obtain ⟨_, rfl⟩ := hph'
      simp only [sat8]
      omega
    · rw [hph] at hph'
      simp only [Phase.sent.injEq] at hph'
      obtain ⟨_, rfl⟩ := hph'
      omega

theorem R_refl_ts {f f' : F} (hm : f'.maxSends = f.maxSends) (ht : f'.ts = f.ts) : R f f' := by
  refine ⟨hm, fun i t' h => Or.inl ⟨t', by rw [ht] at h; exact h, rfl, rfl, Or.inl fun r s hp => ⟨r, hp⟩⟩, fun i j hi hj hi' _ => ?_⟩
  rw [ht, hi] at hi'; exact absurd rfl hi'

theorem R_advance (f : F) (n : Nat) : R f (advance f n) := by
  refine ⟨rfl, fun i t' h => ?_, fun i j hi hj hi' _ => ?_⟩
  · simp only [advance] at h
    rw [slot_map _ _ rfl] at h
    cases hs : slot f.ts i with
    | none => rw [hs] at h; simp at h
    | some t0 =>
      rw [hs] at h
      refine Or.inl ⟨t0, rfl, ?_⟩
      cases hp : t0.phase with
      | acked => simp [hp] at h; subst h; simp [hp]
      | gaveUp => simp [hp] at h; subst h; simp [hp]
      | sent r0 s0 =>
        simp only [hp, Option.map_some] at h
        split at h
        · cases h; refine ⟨rfl, rfl, Or.inl fun r s hq => ?_⟩
          simp only [Phase.sent.injEq] at hq; exact ⟨r0, by rw [hq.2]⟩
        · cases h; exact ⟨rfl, rfl, Or.inl fun r s hq => ⟨r0, by have h2 := hq; rw [hp] at h2; simp only [Phase.sent.injEq] at h2; rw [h2.2]⟩⟩
  · simp only [advance] at hi'
    rw [slot_map _ _ rfl, hi] at hi'
    simp at hi'

theorem R_dropB (f : F) (id : Nat) : R f (dropB f id) := by
  refine ⟨rfl, fun i t' h => ?_, fun i j hi hj hi' _ => ?_⟩
  · simp only [dropB] at h
    rw [slot_map _ _ (by simp)] at h
    cases hs : slot f.ts i with
    | none => rw [hs] at h; simp at h
    | some t0 =>
      rw [hs] at h
      split at h
      · simp at h
      · simp only [Option.some.injEq] at h; subst h
        exact Or.inl ⟨_, rfl, rfl, rfl, Or.inl fun r s hq => ⟨r, hq⟩⟩
  · simp only [dropB] at hi'
    rw [slot_map _ _ (by simp), hi] at hi'
    simp at hi'

theorem R_ackUpd (f : F) (ii : Nat) : R f { f with ts := upd f.ts ii (Option.map fun t => { t with phase := .acked }) } := by
  refine ⟨rfl, fun i t' h => ?_, fun i j hi hj hi' _ => ?_⟩
  · simp only at h
    rw [slot_upd_map] at h
    by_cases hi : i = ii
    · rw [if_pos hi] at h
      cases hs : slot f.ts i with
      | none => rw [hs] at h; simp at h
      | some t0 =>
        rw [hs] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
        exact Or.inl ⟨t0, rfl, rfl, rfl, Or.inl fun r s hq => by simp at hq⟩
    · rw [if_neg hi] at h
      exact Or.inl ⟨t', h, rfl, rfl, Or.inl fun r s hq => ⟨r, hq⟩⟩
  · simp only at hi'
    rw [slot_upd_map, hi] at hi'
    split at hi' <;> simp_all

theorem R_retr (f : F) (ts' : List (Option Transfer)) (a : Option Act)
    (h : retr (upLink f.ls) f.retry f.maxSends f.ts = (ts', a)) : R f { f with ts := ts' } := by
  have hrel := (retr_rel (upLink f.ls) f.retry f.maxSends f.ts).2
  rw [h] at hrel
  refine ⟨rfl, fun i t' ht => ?_, fun i j hi hj hi' _ => ?_⟩
  · have := hrel i
    simp only at ht
    rw [ht] at this
    cases hs : slot f.ts i with
    | none => rw [hs] at this; simp [TRel] at this
    | some t0 =>
      rw [hs] at this
      simp only [TRel] at this
      obtain ⟨hb, hp, _, _, h1 | ⟨s, h2, h3, h4, h5⟩ | ⟨s, h2, h3, h4, h5, _⟩⟩ := this
      · subst h1; exact Or.inl ⟨_, rfl, rfl, rfl, Or.inl fun r s hq => ⟨r, hq⟩⟩
      · subst h5; exact Or.inl ⟨_, rfl, rfl, rfl, Or.inl fun r s' hq => by simp at hq⟩
      · subst h5; exact Or.inl ⟨_, rfl, rfl, rfl, Or.inr ⟨s, h2, h4, rfl⟩⟩
  · have := hrel i
    simp only at hi'
    rw [hi] at this
    cases hq : slot ts' i with
    | none => exact absurd hq hi'
    | some _ => rw [hq] at this; simp [TRel] at this

theorem R_spray (g : F) : R g (spray g).1 := by
  rcases spray_cases g with hs | ⟨f1, p, id, c, hs⟩
  · rw [hs]; exact R_refl_ts rfl rfl
  · obtain ⟨_, li, bi, s, l, b, hc, hl, hb, hfs, _, _, hcc, hf⟩ := spray_unfold hs
    obtain ⟨hsn, hsl⟩ := freeIdx_some hfs
    obtain ⟨l', b', hl', hu, hb', hno, _⟩ := cand_spec hc
    rw [hl] at hl'; rw [hb] at hb'; cases hl'; cases hb'
    rw [hs]
    show R g f1
    rw [hf]
    refine ⟨rfl, fun i t' ht => ?_, fun i j hi hj hi' hj' => ?_⟩
    · simp only at ht
      by_cases hix : i = s
      · subst hix
        rw [slot_upd_same _ _ _ hsl] at ht
        cases ht
        exact Or.inr ⟨hsn, rfl, hno⟩
      · rw [slot_upd_ne _ _ _ _ hix] at ht
        exact Or.inl ⟨t', ht, rfl, rfl, Or.inl fun r s' hq => ⟨r, hq⟩⟩
    · simp only at hi' hj'
      have key : ∀ k, slot g.ts k = none → slot (upd g.ts s fun _ => some (⟨b.id, l.peer, c, l.peer == b.dest, .sent g.retry 1⟩ : Transfer)) k ≠ none → k = s := by
        intro k hk hk'
        by_cases hks : k = s
        · exact hks
        · rw [slot_upd_ne _ _ _ _ hks, hk] at hk'; exact absurd rfl hk'
      exact (key i hi hi').trans (key j hj hj').symm

theorem R_congr {f f2 f' : F} (h : R f f2) (hm : f'.maxSends = f2.maxSends) (ht : f'.ts = f2.ts) : R f f' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hm, h1], fun i t' h => ?_, fun i j hi hj hi' hj' => ?_⟩
  · rw [ht] at h; exact h2 i t' h
  · rw [ht] at hi' hj'; exact h3 i j hi hj hi' hj'

theorem step_ms (f0 : F) (n : Nat) (inp : Input) : (step f0 n inp).1.maxSends = f0.maxSends := by
  unfold step
  cases inp <;> simp only <;> (repeat' split) <;> simp [advance, dropB]

theorem step_ts (f0 : F) (n : Nat) (f' : F) (e : Err) (inp : Input) (h : step f0 n inp = (f', e))
    (hn : ∀ id, inp ≠ .forget id) (hk : ∀ peer id, inp ≠ .acked peer id) : f'.ts = (advance f0 n).ts := by
  cases inp with
  | tick => simp [step] at h; rw [← h.1]
  | forget id => exact absurd rfl (hn id)
  | acked p i => exact absurd rfl (hk p i)
  | hold id d ex c =>
    rcases hold_total f0 n id d ex c f' e h 0 with ⟨_, hf⟩ | ⟨_, _, _, _, i, _, hf⟩
    · rw [hf]
    · rw [hf]
  | linkUp peer => exact (step_link_shape f0 n peer true f' e (by simpa using h)).2
  | linkDown peer => exact (step_link_shape f0 n peer false f' e (by simpa using h)).2

theorem ti_step {f0 f' : F} {n : Nat} {inp : Input} {e : Err} (h : step f0 n inp = (f', e)) (hT : TInv f0) :
    TInv f' := by
  have hms : f'.maxSends = f0.maxSends := by
    have := step_ms f0 n inp; rw [h] at this; exact this
  have hTa := ti_of_R hT (R_advance f0 n)
  have hma : (advance f0 n).maxSends = f0.maxSends := rfl
  cases inp with
  | forget id =>
    rcases step_forget f0 n id f' e h with ⟨_, hf, _⟩ | ⟨_, hf, _⟩
    · rw [hf]; exact hTa
    · rw [hf]; exact ti_of_R hTa (R_dropB _ _)
  | acked peer id =>
    rcases step_ack_shape f0 n peer id f' e h with ⟨_, ht⟩ | ⟨i, ht, _⟩
    · exact ti_of_R hTa (R_refl_ts (by rw [hms]; rfl) ht)
    · exact ti_of_R hTa (R_congr (R_ackUpd (advance f0 n) i) (by rw [hms]; rfl) ht)
  | tick => exact ti_of_R hTa (R_refl_ts (by rw [hms]; rfl) (step_ts f0 n f' e _ h (by simp) (by simp)))
  | hold id d ex c => exact ti_of_R hTa (R_refl_ts (by rw [hms]; rfl) (step_ts f0 n f' e _ h (by simp) (by simp)))
  | linkUp peer => exact ti_of_R hTa (R_refl_ts (by rw [hms]; rfl) (step_ts f0 n f' e _ h (by simp) (by simp)))
  | linkDown peer => exact ti_of_R hTa (R_refl_ts (by rw [hms]; rfl) (step_ts f0 n f' e _ h (by simp) (by simp)))

theorem ti_poll {f f' : F} {a : Act} (h : poll f = (f', a)) (hT : TInv f) : TInv f' := by
  unfold poll at h
  cases hd : doneIdx f with
  | some i =>
    simp only [hd, Prod.mk.injEq] at h
    rw [← h.1]; exact ti_of_R hT (R_dropB _ _)
  | none =>
    simp only [hd] at h
    cases hq : retr (upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a0 =>
      have hR := R_retr f ts' a0 hq
      cases a0 with
      | some y => simp only [hq, Prod.mk.injEq] at h; rw [← h.1]; exact ti_of_R hT hR
      | none =>
        simp only [hq] at h
        rw [← show (spray { f with ts := ts' }).1 = f' from congrArg Prod.fst h]
        exact ti_of_R (ti_of_R hT hR) (R_spray _)

theorem reach_ti {f : F} {g : Nat → Nat} (h : Reach f g) : TInv f := by
  induction h with
  | init r m now b l tt =>
    refine ⟨fun i j t t' hi => ?_, fun i t rr s hi => ?_⟩ <;>
    · have : slot (F.new r m now b l tt).ts i = none := slot_replicate_none _ _
      rw [this] at hi; cases hi
  | holdOk n id d ex c hr hs ih => exact ti_step hs ih
  | forgetOk n id hr hs ih => exact ti_step hs ih
  | stepKeep n inp e hr hs hh hfg ih => exact ti_step hs ih
  | release id hr hs ih => exact ti_poll hs ih
  | pollKeep a hr hs hn ih => exact ti_poll hs ih

/-- **One transfer per (bundle, peer)**, in every reachable state. -/
theorem reach_one_transfer {f : F} {g : Nat → Nat} (h : Reach f g) {i j : Nat} {t t' : Transfer}
    (hi : slot f.ts i = some t) (hj : slot f.ts j = some t') (hb : t.bundle = t'.bundle) (hp : t.peer = t'.peer) :
    i = j := (reach_ti h).1 i j t t' hi hj hb hp

/-- **The send counter**: a sending transfer has made at least one and at most `max 1 maxSends` sends. -/
theorem reach_sends {f : F} {g : Nat → Nat} (h : Reach f g) {i : Nat} {t : Transfer} {r s : Nat}
    (hi : slot f.ts i = some t) (hp : t.phase = .sent r s) : 1 ≤ s ∧ s ≤ max 1 f.maxSends :=
  (reach_ti h).2 i t r s hi hp

/-- **Give-up is exact**: a transfer gives up when its timer is out, its link is up, and it has made exactly
`max 1 maxSends` sends (the first send is always made). -/
theorem gives_up_exact {f f' : F} {g : Nat → Nat} (hr : Reach f g) {a : Act} (h : poll f = (f', a)) {i : Nat}
    {t t' : Transfer} (ht : slot f.ts i = some t) (ht' : slot f'.ts i = some t') (hg : t'.phase = .gaveUp) :
    t.phase = .gaveUp ∨ ∃ s, t.phase = .sent 0 s ∧ upLink f.ls t.peer = true ∧ s = max 1 f.maxSends := by
  rcases poll_gives_up_only h ht ht' hg with h1 | ⟨s, h2, h3, h4⟩
  · exact Or.inl h1
  · have := reach_sends hr ht h2
    exact Or.inr ⟨s, h2, h3, by omega⟩

#print axioms reach_ti
#print axioms gives_up_exact

end Vinc.DtnForward
