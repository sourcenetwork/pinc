import Vinc.ReconcileApsProc

/-!
# Reconcile APS, part 4: safety and coverage

`InvS` holds in every reachable state (`reach_inv`): `Safe` arenas (`here` only items of `B` that `A` lacks, `there`
only items of `A`, each once, whatever the id function), pairwise disjoint pending intervals, arena items outside
every pending interval, well-formed parts.

`Lossless` states (an exact pass, or a pass that has not used an ids leaf) also keep `Cov`: every item of the
symmetric difference is in an arena or in a pending interval (`reach_cov`, needs `Indep`). So a lossless pass that has
no pending part left reports exactly (`final_exact_of_lossless`); a pass 1 with ids leaves always ends `Safe`, and
`ReconcileApsSession` closes the argument with the final check.
-/

namespace Vinc.Reconcile

def Lossless (s : St) : Prop := s.exact = true ∨ s.leafed = false

def InvS (c : Cfg) (s : St) : Prop :=
  Safe c.A c.B s.here s.there ∧
  s.pend.Pairwise (fun p q => p.iv.Disj q.iv) ∧
  (∀ x ∈ s.here ++ s.there, ∀ p ∈ s.pend, p.iv.has x = false) ∧
  (∀ p ∈ s.pend, WF p)

theorem inv_init {c : Cfg} {s : St} (h : (∃ ex, Init c ex s) ∨ ColdInit c s) : InvS c s := by
  rcases h with ⟨ex, h⟩ | h
  · cases h with
    | leaf hcnt hf =>
      refine ⟨⟨by simp, by simp, List.nodup_nil, List.nodup_nil⟩, by simp, by simp, ?_⟩
      intro p hp; simp at hp; subst hp
      cases ex <;> simp [WF]
    | split hno hf1 hf2 =>
      obtain ⟨_, h2, _⟩ := split_kids c c.A c.hA Iv.top (fan := _) (by have := c.hmin; omega) hf2
        (two_le_of_no_leaf_top c ex hno) false 0
      refine ⟨⟨by simp, by simp, List.nodup_nil, List.nodup_nil⟩, h2, by simp, ?_⟩
      intro p hp; obtain ⟨J, _, rfl⟩ := List.mem_map.mp hp; simp [WF]
  · cases h with
    | mk blocks hf hne =>
      refine ⟨⟨by simp, by simp, List.nodup_nil, List.nodup_nil⟩, ?_, by simp, ?_⟩
      · unfold coldIvs
        by_cases hb : blocks = []
        · simp [hb]
        · simp only [hb, ↓reduceIte]
          obtain ⟨_, _, hd, _⟩ := ivs_props none blocks [] hb hne (by rw [hf]; exact c.hB)
            (fun x _ => Iv.top_has x)
          rw [List.pairwise_map]; exact hd
      · intro p hp; obtain ⟨J, _, rfl⟩ := List.mem_map.mp hp; simp [WF]

theorem inv_step {c : Cfg} {s s' : St} (hi : InvS c s) (hs : PStep c s s') : InvS c s' := by
  obtain ⟨hsafe, hpw, hout, hwf⟩ := hi
  cases hs with
  | @step p rest kids ha ta lf hperm hp =>
    obtain ⟨fsub, fdisj, fin, fno, fwf, _, _⟩ := hp.facts
    obtain ⟨sh, st, nh, nt⟩ := hp.safe_adds
    have hpmem : p ∈ s.pend := hperm.symm.mem_iff.mp (List.mem_cons_self)
    have hpw' := ((List.Perm.pairwise_iff (R := fun p q : Part => p.iv.Disj q.iv) (fun {x y} h => Iv.Disj.symm h)) hperm).mp hpw
    rw [List.pairwise_cons] at hpw'
    obtain ⟨hpr, hrest⟩ := hpw'
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hsafe.1 x h
      · exact sh x h
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hsafe.2.1 x h
      · exact st x h
    · rw [List.nodup_append]
      refine ⟨hsafe.2.2.1, nh, fun a ha' b hb hab => ?_⟩
      have h1 := hout a (List.mem_append_left _ ha') p hpmem
      have h2 := fin b (List.mem_append_left _ hb)
      subst hab; simp [h1] at h2
    · rw [List.nodup_append]
      refine ⟨hsafe.2.2.2, nt, fun a ha' b hb hab => ?_⟩
      have h1 := hout a (List.mem_append_right _ ha') p hpmem
      have h2 := fin b (List.mem_append_right _ hb)
      subst hab; simp [h1] at h2
    · rw [List.pairwise_append]
      refine ⟨fdisj, hrest, fun k hk q hq z hz => ?_⟩
      have := hpr q hq z (fsub k hk z hz)
      exact this
    · intro x hx q hq
      have hx' : x ∈ (s.here ++ s.there) ∨ x ∈ ha ++ ta := by
        rcases List.mem_append.mp hx with h | h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl (List.mem_append_left _ h)
          · exact Or.inr (List.mem_append_left _ h)
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl (List.mem_append_right _ h)
          · exact Or.inr (List.mem_append_right _ h)
      rcases List.mem_append.mp hq with hq | hq
      · rcases hx' with hx' | hx'
        · cases hh : q.iv.has x with
          | false => rfl
          | true => have := hout x hx' p hpmem; rw [fsub q hq x hh] at this; simp at this
        · have : kids = [] := by
            refine Decidable.byContradiction (fun hne => ?_)
            obtain ⟨e1, e2⟩ := fno hne
            simp [e1, e2] at hx'
          subst this; simp at hq
      · rcases hx' with hx' | hx'
        · exact hout x hx' q ((hperm.symm.mem_iff).mp (List.mem_cons_of_mem _ hq) |> fun h => h)
        · exact hpr q hq x (fin x hx')
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact fwf q hq
      · exact hwf q (hperm.symm.mem_iff.mp (List.mem_cons_of_mem _ hq))

theorem reach_inv {c : Cfg} {s : St} (h : PReach c s) : InvS c s := by
  induction h with
  | init h => exact inv_init (Or.inl ⟨_, h⟩)
  | cold h => exact inv_init (Or.inr h)
  | step _ hs ih => exact inv_step ih hs


/-! ## Coverage -/

def NoIds (s : St) : Prop := Lossless s → ∀ p ∈ s.pend, p.kind ≠ .ids ∧ p.kind ≠ .reply true

def Cov (c : Cfg) (s : St) : Prop :=
  (∀ x, ((x ∈ c.B ∧ x ∉ c.A) → x ∈ s.here ∨ ∃ p ∈ s.pend, p.iv.has x = true) ∧
       ((x ∈ c.A ∧ x ∉ c.B) → x ∈ s.there ∨ ∃ p ∈ s.pend, p.iv.has x = true)) ∧
  (∀ x ∈ s.there, x ∉ c.B)

/-- Away from an ids reply, `there` only gets items `B` lacks. -/
theorem Proc.there_nb {c : Cfg} {ex : Bool} {p : Part} {kids : List Part} {ha ta : List Item} {lf : Bool}
    (hp : Proc c ex p kids ha ta lf) (hk : p.kind ≠ .reply true) : ∀ x ∈ ta, x ∉ c.B := by
  cases hp with
  | fullInit => intro x hx; exact ((c.exactThere_mem _ _).mp hx).2.2
  | replyExact => intro x hx; exact ((c.exactThere_mem _ _).mp hx).2.2
  | replyIds => exact absurd rfl hk
  | _ => simp

def CovL (c : Cfg) (s : St) : Prop := Lossless s → Cov c s

/-- Ids parts and their replies come only from a non-exact leaf of the initiator. -/
theorem Proc.kids_kind {c : Cfg} {ex : Bool} {p : Part} {kids : List Part} {ha ta : List Item} {lf : Bool}
    (hp : Proc c ex p kids ha ta lf) :
    (∀ k ∈ kids, k.kind = .ids → ex = false ∧ lf = true) ∧ (∀ k ∈ kids, k.kind = .reply true → p.kind = .ids) := by
  cases hp with
  | fpEq h => simp
  | fpLeafResp => simp
  | fpLeafInit hne hcnt hf =>
    refine ⟨?_, ?_⟩
    · intro k hk hki
      simp at hk; subst hk
      cases ex <;> simp_all
    · intro k hk hr
      simp at hk; subst hk
      cases ex <;> simp at hr
  | fpSplit => refine ⟨?_, ?_⟩ <;> intro k hk <;> (obtain ⟨J, _, rfl⟩ := List.mem_map.mp hk) <;> simp
  | respLeaf hk hcnt hf =>
    refine ⟨by simp, ?_⟩
    intro k' hk' hr
    simp at hk' hr; subst hk'
    rcases hk with rfl | rfl
    · rfl
    · simp at hr
  | respNarrow => refine ⟨?_, ?_⟩ <;> intro k hk <;> (obtain ⟨J, _, rfl⟩ := List.mem_map.mp hk) <;> simp
  | fullInit => simp
  | replyExact => simp
  | replyIds => simp

theorem cover_top_kids {c : Cfg} {side : Bool} {d : Nat} {fan : Nat} (hf : 2 ≤ fan) (hno : 2 ≤ cnt c.A Iv.top) (x : Item) :
    ∃ k ∈ (splitIvs c.A Iv.top fan).map (fun J => (⟨.fp, side, J, d⟩ : Part)), k.iv.has x = true := by
  obtain ⟨J, hJ, hJx⟩ := (splitIvs_spec c.hA Iv.top hf hno).1 x (Iv.top_has x)
  exact ⟨⟨.fp, side, J, d⟩, List.mem_map.mpr ⟨J, hJ, rfl⟩, hJx⟩

theorem init_cov {c : Cfg} {s : St} (h : (∃ ex, Init c ex s) ∨ ColdInit c s) : NoIds s ∧ CovL c s := by
  rcases h with ⟨ex, h⟩ | h
  · cases h with
    | leaf hcnt hf =>
      constructor
      · intro hl p hp
        simp at hp; subst hp
        cases ex <;> simp_all [Lossless]
      · intro hl
        have hex : ex = true := by
          cases ex
          · simp [Lossless] at hl
          · rfl
        subst hex
        refine ⟨fun x => ⟨fun _ => Or.inr ⟨⟨.full, false, Iv.top, 1⟩, List.mem_singleton_self _, Iv.top_has x⟩,
          fun _ => Or.inr ⟨⟨.full, false, Iv.top, 1⟩, List.mem_singleton_self _, Iv.top_has x⟩⟩, by simp⟩
    | @split fan hno hf1 hf2 =>
      constructor
      · intro _ p hp; obtain ⟨J, _, rfl⟩ := List.mem_map.mp hp; simp
      · intro _
        refine ⟨fun x => ?_, by simp⟩
        obtain ⟨k, hk, hkx⟩ := cover_top_kids (c := c) (side := false) (d := 1) (fan := fan) (by have := c.hmin; omega)
          (two_le_of_no_leaf_top c ex hno) x
        exact ⟨fun _ => Or.inr ⟨k, hk, hkx⟩, fun _ => Or.inr ⟨k, hk, hkx⟩⟩
  · cases h with
    | mk blocks hf hne =>
      constructor
      · intro _ p hp; obtain ⟨J, _, rfl⟩ := List.mem_map.mp hp; simp
      · intro _
        refine ⟨fun x => ?_, by simp⟩
        have : ∃ J ∈ coldIvs blocks, J.has x = true := by
          unfold coldIvs
          by_cases hb : blocks = []
          · simp [hb, Iv.top_has]
          · simp only [hb, ↓reduceIte]
            exact (ivs_props none blocks [] hb hne (by rw [hf]; exact c.hB) (fun x _ => Iv.top_has x)).1 x
              (Iv.top_has x)
        obtain ⟨J, hJ, hJx⟩ := this
        exact ⟨fun _ => Or.inr ⟨⟨.full, true, J, 0⟩, List.mem_map.mpr ⟨J, hJ, rfl⟩, hJx⟩,
          fun _ => Or.inr ⟨⟨.full, true, J, 0⟩, List.mem_map.mpr ⟨J, hJ, rfl⟩, hJx⟩⟩

theorem step_cov {c : Cfg} (hI : Indep c.o) {s s' : St} (hn : NoIds s) (hc : CovL c s) (hs : PStep c s s') :
    NoIds s' ∧ CovL c s' := by
  cases hs with
  | @step p rest kids ha ta lf hperm hp =>
    have hmem : ∀ q, q ∈ s.pend ↔ q = p ∨ q ∈ rest := fun q => by
      rw [hperm.mem_iff]; simp
    obtain ⟨kk1, kk2⟩ := hp.kids_kind
    have hlossy : Lossless ⟨kids ++ rest, s.here ++ ha, s.there ++ ta, s.leafed || lf, s.exact, s.log ++ [p]⟩ →
        Lossless s ∧ (s.exact = false → lf = false) := by
      intro h
      unfold Lossless at h ⊢
      simp only [Bool.or_eq_false_iff] at h
      refine ⟨?_, ?_⟩
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr h.1
      · intro he; rcases h with h | h
        · simp [he] at h
        · exact h.2
    refine ⟨?_, ?_⟩
    · intro hl q hq
      obtain ⟨hl0, hlf⟩ := hlossy hl
      rcases List.mem_append.mp hq with hq | hq
      · refine ⟨fun hki => ?_, fun hkr => ?_⟩
        · have := kk1 q hq hki
          have hl' := hl
          unfold Lossless at hl'
          simp only at hl'
          rcases hl' with h | h
          · rw [this.1] at h; exact absurd h (by simp)
          · simp [this.2] at h
        · have := kk2 q hq hkr
          exact (hn hl0 p ((hmem p).mpr (Or.inl rfl))).1 this
      · exact hn hl0 q ((hmem q).mpr (Or.inr hq))
    · intro hl
      obtain ⟨hl0, hlf⟩ := hlossy hl
      have hcov0 := hc hl0
      have hpk := (hn hl0 p ((hmem p).mpr (Or.inl rfl))).2
      have hthere : ∀ x ∈ s.there ++ ta, x ∉ c.B := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hcov0.2 x h
        · exact hp.there_nb hpk x h
      refine ⟨fun x => ?_, hthere⟩
      have hcov := hcov0.1 x
      refine ⟨fun hx => ?_, fun hx => ?_⟩
      · rcases hcov.1 hx with h | ⟨q, hq, hqx⟩
        · exact Or.inl (List.mem_append_left _ h)
        · rcases (hmem q).mp hq with rfl | hr
          · rcases (Proc.cover hI hp hpk x hqx).1 hx.1 hx.2 with h | ⟨k, hk, hkx⟩
            · exact Or.inl (List.mem_append_right _ h)
            · exact Or.inr ⟨k, List.mem_append_left _ hk, hkx⟩
          · exact Or.inr ⟨q, List.mem_append_right _ hr, hqx⟩
      · rcases hcov.2 hx with h | ⟨q, hq, hqx⟩
        · exact Or.inl (List.mem_append_left _ h)
        · rcases (hmem q).mp hq with rfl | hr
          · rcases (Proc.cover hI hp hpk x hqx).2 hx.1 hx.2 with h | ⟨k, hk, hkx⟩
            · exact Or.inl (List.mem_append_right _ h)
            · exact Or.inr ⟨k, List.mem_append_left _ hk, hkx⟩
          · exact Or.inr ⟨q, List.mem_append_right _ hr, hqx⟩

theorem reach_cov {c : Cfg} (hI : Indep c.o) {s : St} (h : PReach c s) : NoIds s ∧ CovL c s := by
  induction h with
  | init h => exact init_cov (Or.inl ⟨_, h⟩)
  | cold h => exact init_cov (Or.inr h)
  | step _ hs ih => exact step_cov hI ih.1 ih.2 hs

/-- A lossless pass with nothing pending reports exactly the symmetric difference. -/
theorem final_exact_of_lossless {c : Cfg} (hI : Indep c.o) {s : St} (h : PReach c s) (hl : Lossless s)
    (hp : s.pend = []) : ExactReport c.A c.B s.here s.there := by
  obtain ⟨hsafe, _⟩ := reach_inv h
  obtain ⟨_, hc⟩ := reach_cov hI h
  have hcov0 := hc hl
  have hcov := hcov0.1
  obtain ⟨h1, h2, h3, h4⟩ := hsafe
  refine ⟨fun x => ⟨h1 x, fun hx => ?_⟩, fun x => ⟨fun ht => ⟨h2 x ht, hcov0.2 x ht⟩, fun hx => ?_⟩, h3, h4⟩
  · rcases (hcov x).1 hx with h | ⟨q, hq, _⟩
    · exact h
    · simp [hp] at hq
  · rcases (hcov x).2 hx with h | ⟨q, hq, _⟩
    · exact h
    · simp [hp] at hq

end Vinc.Reconcile
