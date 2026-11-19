import Pinc.FacadeAcpForget

/-!
# The facade's access decisions: every reachable state keeps the promises

The model, its promises and the lemmas about one check are in `Pinc/FacadeAcpForget.lean`. Here: each action of the
model keeps the promises with the code's settings (`inv_step`), so every reachable state does (`inv_reach`), whatever
protocols the node lists and dials; with each session asked on its own no session is taken up on an allow given for
another question (`noCrossAllow_reach`); and the two promises about refusals read off the invariant
(`noCrossDeny_reach`, `noCut_reach`). The settings that break a promise are in `Pinc/FacadeAcpForgetBad.lean`.
-/

namespace Pinc.FacadeAcpForget

/-- Dropping the endpoint's answer for `p` while only `p`'s hook answers and revoked bit may change keeps every
cached allow sound: `p` has none left, and no other peer's answer or gate moved. -/
theorem forget_cache (c : Cfg) (s t : State) (p : Nat) (hg : ∀ x, x ≠ p → ∀ q, gate t x q = gate s x q)
    (hcache : t.cache = set s.cache p .none) (hc : CacheSound c s) : CacheSound c t := by
  intro x hx
  rw [hcache] at hx
  by_cases hxp : x = p
  · rw [hxp, set_same] at hx
    exact absurd hx (by decide)
  · rw [set_other _ _ _ _ hxp] at hx
    rw [anyB_congr c s t x (hg x hxp)]
    exact hc x hx

/-- Dropping the remembered allow of `p` under the same condition keeps every remembered allow sound. -/
theorem forget_known (s t : State) (p : Nat) (hg : ∀ x, x ≠ p → ∀ q, gate t x q = gate s x q)
    (hknown : t.known = set s.known p none) (hk : KnownSound s) : KnownSound t := by
  intro x q hxq
  rw [hknown] at hxq
  by_cases hxp : x = p
  · rw [hxp, set_same] at hxq
    cases hxq
  · rw [set_other _ _ _ _ hxp] at hxq
    rw [hg x hxp q]
    exact hk x q hxq

/-- Dropping the endpoint's answer for `p` under the same condition, while no other peer's held questions grow, keeps
every deny off the listed and the held questions. -/
theorem forget_deny (c : Cfg) (s t : State) (p : Nat) (hg : ∀ x, x ≠ p → ∀ q, gate t x q = gate s x q)
    (hcache : t.cache = set s.cache p .none) (hsess : ∀ x, x ≠ p → ∀ q, q ∈ t.sess x → q ∈ s.sess x)
    (hx : NoCrossDeny c s) : NoCrossDeny c t := by
  intro x hxd r hr
  rw [hcache] at hxd
  by_cases hxp : x = p
  · rw [hxp, set_same] at hxd
    exact absurd hxd (by decide)
  · rw [set_other _ _ _ _ hxp] at hxd
    rw [hg x hxp r]
    rcases hr with h | h
    · exact hx x hxd r (Or.inl h)
    · exact hx x hxd r (Or.inr (hsess x hxp r h))

/-- With the fix, a dial that does not drop a refusal held for its peer is one the gate refuses. -/
theorem drop_false (c : Cfg) (hda : c.dialAsks = true) (s : State) (p : Nat) (q : Q)
    (hD : dropB c s p q = false) (hcd : s.cache p = .deny) : gate s p q = false := by
  unfold dropB at hD
  rw [hda, hcd] at hD
  unfold gate at hD ⊢
  revert hD
  generalize s.revoked p = r
  generalize s.hook p q = h
  generalize c.refuseDial = d
  cases r <;> cases h <;> cases d <;> decide

/-- The questions held with each peer after a dial of `q` to `p`: `q` or what was held with `p`, and for every other
peer what was held. -/
theorem dial_sess (c : Cfg) (s : State) (p : Nat) (q : Q) (x : Nat) (y : Q) (hy : y ∈ (dialS c s p q).sess x) :
    (x = p ∧ (y = q ∨ y ∈ s.sess p)) ∨ (x ≠ p ∧ y ∈ s.sess x) := by
  rcases sess_at s.sess (dialS c s p q).sess p _ rfl x y hy with ⟨hxp, hm⟩ | ⟨hxp, hm⟩
  · cases hR : (c.refuseDial && s.revoked p) with
    | true =>
      rw [hR] at hm
      exact Or.inl ⟨hxp, Or.inr hm⟩
    | false =>
      rw [hR] at hm
      exact Or.inl ⟨hxp, List.mem_cons.mp hm⟩
  · exact Or.inr ⟨hxp, hm⟩

/-- With the code's settings every step keeps the promises, whatever protocols the node lists and dials. -/
theorem inv_step (c : Cfg) (hl : c.forgetOnLift = true) (hr : c.forgetOnRevoke = true) (hd : c.refuseDial = true)
    (hh : c.forgetOnChange = true) (ha : c.askEach = true) (hn : c.answerAny = true) (hheld : c.askHeld = true)
    (hda : c.dialAsks = true) (s t : State) (hs : Inv c s) (st : Step c s t) : Inv c t := by
  obtain ⟨hf, hc, hk, ho, hx, hcut, hso⟩ := hs
  cases st with
  | cached p q hp hq hout =>
    have hmem : q ∈ listedQs c ∨ q ∈ s.sess p := by
      rcases qs_split c q hq with h | h
      · exact Or.inl h
      · exact Or.inr (hout h)
    have hep : gate s p q = true → asBool (s.cache p) = true := by
      intro hg
      cases hcp : s.cache p with
      | none => exact absurd hcp hp
      | allow => rfl
      | deny =>
        rw [hx p hcp q hmem] at hg
        exact absurd hg (by decide)
    refine ⟨fun _ => ⟨upOf_eq c ha s p q _ _ hep (hk p q), fun he => ?_, fun he => ?_⟩, hc, hk, ho, ?_, hcut, ?_⟩
    · have he' : asBool (s.cache p) = true := he
      have hca : s.cache p = .allow := by
        cases hcp : s.cache p with
        | none => exact absurd hcp hp
        | allow => rfl
        | deny =>
          rw [hcp] at he'
          exact absurd he' (by decide)
      exact hc p hca
    · have he' : asBool (s.cache p) = false := he
      have hcd : s.cache p = .deny := by
        cases hcp : s.cache p with
        | none => exact absurd hcp hp
        | allow =>
          rw [hcp] at he'
          exact absurd he' (by decide)
        | deny => rfl
      refine heldB_false c s p q (fun r hr => ?_)
      rcases hr with h | h
      · exact hx p hcd r (Or.inl h)
      · rcases List.mem_cons.mp h with e | m
        · rw [e]
          exact hx p hcd q hmem
        · exact hx p hcd r (Or.inr m)
    · intro x hxd r hr
      have hxd' : s.cache x = .deny := hxd
      rcases hr with h | h
      · exact hx x hxd' r (Or.inl h)
      · rcases sess_at s.sess (cachedS c s p q).sess p _ rfl x r h with ⟨hxp, hm⟩ | ⟨_, hm⟩
        · rw [hxp] at hxd'
          rw [hxp]
          rcases mem_grow _ q r _ hm with e | m
          · rw [e]
            exact hx p hxd' q hmem
          · exact hx p hxd' r (Or.inr m)
        · exact hx x hxd' r (Or.inr hm)
    · intro x r h
      rcases sess_at s.sess (cachedS c s p q).sess p _ rfl x r h with ⟨_, hm⟩ | ⟨_, hm⟩
      · rcases mem_grow _ q r _ hm with e | m
        · rw [e]
          exact hq
        · exact hso p r m
      · exact hso x r hm
  | ask p q a _ hq _ has =>
    have haq : a ∈ qs c := asked_qs c q a hq has
    have hsp : ∀ r, r ∈ s.sess p → r ∈ qs c := fun r => hso p r
    have hep : gate s p q = true → told c s p a q = true := told_of_gate c hn hheld s p a q
    refine ⟨fun _ => ⟨upOf_eq c ha s p q _ _ hep (knownAfter_sound c s p a q), fun he => ?_, fun he => ?_⟩,
      ?_, ?_, ho, ?_, ?_, ?_⟩
    · exact told_any c s p a q haq hq hsp he
    · exact heldB_false c s p q (fun r hr => told_false c hn hheld s p a q r he hr)
    · intro x hxa
      have hxa' : set s.cache p (cacheOf (told c s p a q)) x = .allow := hxa
      by_cases hxp : x = p
      · rw [hxp, set_same] at hxa'
        rw [hxp]
        cases ht : told c s p a q with
        | true => exact told_any c s p a q haq hq hsp ht
        | false =>
          rw [ht] at hxa'
          exact absurd hxa' (by decide)
      · rw [set_other _ _ _ _ hxp] at hxa'
        exact hc x hxa'
    · intro x y hxy
      have hxy' : set s.known p (knownAfter c s p a) x = some y := hxy
      by_cases hxp : x = p
      · rw [hxp, set_same] at hxy'
        rw [hxp]
        exact knownAfter_sound c s p a y hxy'
      · rw [set_other _ _ _ _ hxp] at hxy'
        exact hk x y hxy'
    · intro x hxd r hr
      have hxd' : set s.cache p (cacheOf (told c s p a q)) x = .deny := hxd
      by_cases hxp : x = p
      · rw [hxp, set_same] at hxd'
        have ht : told c s p a q = false := by
          cases h : told c s p a q with
          | false => rfl
          | true =>
            rw [h] at hxd'
            exact absurd hxd' (by decide)
        rw [hxp]
        rcases hr with h | h
        · exact told_false c hn hheld s p a q r ht (Or.inl h)
        · rcases sess_at s.sess (askS c s p q a).sess p _ rfl x r h with ⟨_, hm⟩ | ⟨hne, _⟩
          · rw [ht] at hm
            simp at hm
          · exact absurd hxp hne
      · rw [set_other _ _ _ _ hxp] at hxd'
        rcases hr with h | h
        · exact hx x hxd' r (Or.inl h)
        · rcases sess_at s.sess (askS c s p q a).sess p _ rfl x r h with ⟨hxp', _⟩ | ⟨_, hm⟩
          · exact absurd hxp' hxp
          · exact hx x hxd' r (Or.inr hm)
    · have hcut' : (askS c s p q a).cut = (s.cut || (!told c s p a q && (q :: s.sess p).any (gate s p))) := rfl
      show (askS c s p q a).cut = false
      rw [hcut', hcut, Bool.false_or]
      cases ht : told c s p a q with
      | true => rfl
      | false =>
        rw [Bool.not_false, Bool.true_and]
        exact any_false s p _ (fun r hr => told_false c hn hheld s p a q r ht (Or.inr hr))
    · intro x r h
      rcases sess_at s.sess (askS c s p q a).sess p _ rfl x r h with ⟨_, hm⟩ | ⟨_, hm⟩
      · cases ht : told c s p a q with
        | false =>
          rw [ht] at hm
          simp at hm
        | true =>
          rw [ht] at hm
          rcases mem_grow _ q r _ hm with e | m
          · rw [e]
            exact hq
          · exact hso p r m
      · exact hso x r hm
  | recheck p q a hallow _ _ =>
    refine ⟨hf, ?_, ?_, ho, ?_, ?_, ?_⟩
    · intro x hxa
      have hxa' : set s.cache p (cacheOf (told c s p a q)) x = .allow := hxa
      by_cases hxp : x = p
      · rw [hxp]
        exact hc p hallow
      · rw [set_other _ _ _ _ hxp] at hxa'
        exact hc x hxa'
    · intro x y hxy
      have hxy' : set s.known p (knownAfter c s p a) x = some y := hxy
      by_cases hxp : x = p
      · rw [hxp, set_same] at hxy'
        rw [hxp]
        exact knownAfter_sound c s p a y hxy'
      · rw [set_other _ _ _ _ hxp] at hxy'
        exact hk x y hxy'
    · intro x hxd r hr
      have hxd' : set s.cache p (cacheOf (told c s p a q)) x = .deny := hxd
      by_cases hxp : x = p
      · rw [hxp, set_same] at hxd'
        have ht : told c s p a q = false := by
          cases h : told c s p a q with
          | false => rfl
          | true =>
            rw [h] at hxd'
            exact absurd hxd' (by decide)
        rw [hxp]
        rcases hr with h | h
        · exact told_false c hn hheld s p a q r ht (Or.inl h)
        · rcases sess_at s.sess (recheckS c s p q a).sess p _ rfl x r h with ⟨_, hm⟩ | ⟨hne, _⟩
          · rw [ht] at hm
            simp at hm
          · exact absurd hxp hne
      · rw [set_other _ _ _ _ hxp] at hxd'
        rcases hr with h | h
        · exact hx x hxd' r (Or.inl h)
        · rcases sess_at s.sess (recheckS c s p q a).sess p _ rfl x r h with ⟨hxp', _⟩ | ⟨_, hm⟩
          · exact absurd hxp' hxp
          · exact hx x hxd' r (Or.inr hm)
    · have hcut' : (recheckS c s p q a).cut = (s.cut || (!told c s p a q && (s.sess p).any (gate s p))) := rfl
      show (recheckS c s p q a).cut = false
      rw [hcut', hcut, Bool.false_or]
      cases ht : told c s p a q with
      | true => rfl
      | false =>
        rw [Bool.not_false, Bool.true_and]
        exact any_false s p _
          (fun r hr => told_false c hn hheld s p a q r ht (Or.inr (List.mem_cons.mpr (Or.inr hr))))
    · intro x r h
      rcases sess_at s.sess (recheckS c s p q a).sess p _ rfl x r h with ⟨_, hm⟩ | ⟨_, hm⟩
      · cases ht : told c s p a q with
        | false =>
          rw [ht] at hm
          simp at hm
        | true =>
          rw [ht] at hm
          exact hso p r hm
      · exact hso x r hm
  | revoke p =>
    have hgate : ∀ x, x ≠ p → ∀ z, gate (revokeS c s p) x z = gate s x z := fun x hxp z => by
      simp only [gate, revokeS]
      rw [set_other _ _ _ _ hxp]
    have hcache : (revokeS c s p).cache = set s.cache p .none := by simp [revokeS, hr]
    have hknown : (revokeS c s p).known = set s.known p none := by simp [revokeS, hr]
    have hsess : ∀ x, x ≠ p → ∀ z, z ∈ (revokeS c s p).sess x → z ∈ s.sess x := fun x hxp z hz => by
      rcases sess_at s.sess (revokeS c s p).sess p _ rfl x z hz with ⟨he, _⟩ | ⟨_, hm⟩
      · exact absurd he hxp
      · exact hm
    refine ⟨hf, forget_cache c s _ p hgate hcache hc, forget_known s _ p hgate hknown hk, fun y hy => ?_,
      forget_deny c s _ p hgate hcache hsess hx, hcut, fun x r h => ?_⟩
    · simp only [revokeS] at hy ⊢
      by_cases hyp : y = p
      · rw [hyp, set_same] at hy
        exact absurd hy (by decide)
      · rw [set_other _ _ _ _ hyp] at hy ⊢
        exact ho y hy
    · rcases sess_at s.sess (revokeS c s p).sess p _ rfl x r h with ⟨_, hm⟩ | ⟨_, hm⟩
      · simp at hm
      · exact hso x r hm
  | lift p =>
    have hgate : ∀ x, x ≠ p → ∀ z, gate (liftS c s p) x z = gate s x z := fun x hxp z => by
      simp only [gate, liftS]
      rw [set_other _ _ _ _ hxp]
    have hcache : (liftS c s p).cache = set s.cache p .none := by simp [liftS, hl]
    have hknown : (liftS c s p).known = set s.known p none := by simp [liftS, hl]
    refine ⟨hf, forget_cache c s _ p hgate hcache hc, forget_known s _ p hgate hknown hk, fun y hy => ?_,
      forget_deny c s _ p hgate hcache (fun _ _ _ h => h) hx, hcut, hso⟩
    simp only [liftS] at hy ⊢
    by_cases hyp : y = p
    · rw [hyp, set_same]
    · rw [set_other _ _ _ _ hyp]
      exact ho y hy
  | expire p =>
    exact ⟨hf, forget_cache c s (expireS s p) p (fun _ _ _ => rfl) rfl hc, hk, ho,
      forget_deny c s (expireS s p) p (fun _ _ _ => rfl) rfl (fun _ _ _ h => h) hx, hcut, hso⟩
  | lapse p => exact ⟨hf, hc, forget_known s (lapseS s p) p (fun _ _ _ => rfl) rfl hk, ho, hx, hcut, hso⟩
  | clear => exact ⟨hf, hc, fun x q hxq => by simp [clearS] at hxq, ho, hx, hcut, hso⟩
  | dial p q hq _ =>
    refine ⟨hf, ?_, ?_, fun y hy => ?_, ?_, hcut, ?_⟩
    · intro x hxa
      have hxa' : (bif dropB c s p q then set s.cache p .none else s.cache) x = .allow := hxa
      cases hD : dropB c s p q with
      | false =>
        rw [hD] at hxa'
        exact hc x hxa'
      | true =>
        rw [hD] at hxa'
        have hxa'' : set s.cache p .none x = .allow := hxa'
        by_cases hxp : x = p
        · rw [hxp, set_same] at hxa''
          exact absurd hxa'' (by decide)
        · rw [set_other _ _ _ _ hxp] at hxa''
          exact hc x hxa''
    · intro x y hxy
      have hxy' : (bif dropB c s p q then set s.known p none else s.known) x = some y := hxy
      cases hD : dropB c s p q with
      | false =>
        rw [hD] at hxy'
        exact hk x y hxy'
      | true =>
        rw [hD] at hxy'
        have hxy'' : set s.known p none x = some y := hxy'
        by_cases hxp : x = p
        · rw [hxp, set_same] at hxy''
          cases hxy''
        · rw [set_other _ _ _ _ hxp] at hxy''
          exact hk x y hxy''
    · simp only [dialS, hd, Bool.true_and] at hy ⊢
      cases hrv : s.revoked p with
      | true =>
        simp [hrv] at hy
        exact ho y hy
      | false =>
        simp [hrv] at hy
        by_cases hyp : y = p
        · rw [hyp]
          exact hrv
        · rw [set_other _ _ _ _ hyp] at hy
          exact ho y hy
    · intro x hxd r hr
      have hxd' : (bif dropB c s p q then set s.cache p .none else s.cache) x = .deny := hxd
      by_cases hxp : x = p
      · cases hD : dropB c s p q with
        | true =>
          rw [hD] at hxd'
          have hxd'' : set s.cache p .none x = .deny := hxd'
          rw [hxp, set_same] at hxd''
          exact absurd hxd'' (by decide)
        | false =>
          rw [hD] at hxd'
          have hcd : s.cache x = .deny := hxd'
          rw [hxp] at hcd
          rw [hxp]
          rcases hr with h | h
          · exact hx p hcd r (Or.inl h)
          · rcases dial_sess c s p q x r h with ⟨_, e | m⟩ | ⟨hne, _⟩
            · rw [e]
              exact drop_false c hda s p q hD hcd
            · exact hx p hcd r (Or.inr m)
            · exact absurd hxp hne
      · have hcd : s.cache x = .deny := by
          cases hD : dropB c s p q with
          | true =>
            rw [hD] at hxd'
            have hxd'' : set s.cache p .none x = .deny := hxd'
            rw [set_other _ _ _ _ hxp] at hxd''
            exact hxd''
          | false =>
            rw [hD] at hxd'
            exact hxd'
        rcases hr with h | h
        · exact hx x hcd r (Or.inl h)
        · rcases dial_sess c s p q x r h with ⟨he, _⟩ | ⟨_, hm⟩
          · exact absurd he hxp
          · exact hx x hcd r (Or.inr hm)
    · intro x r h
      rcases dial_sess c s p q x r h with ⟨_, e | m⟩ | ⟨_, hm⟩
      · rw [e]
        exact hq
      · exact hso p r m
      · exact hso x r hm
  | hangup p =>
    refine ⟨hf, hc, hk, fun y hy => ?_, hx, hcut, hso⟩
    simp only [hangupS] at hy ⊢
    by_cases hyp : y = p
    · rw [hyp, set_same] at hy
      exact absurd hy (by decide)
    · rw [set_other _ _ _ _ hyp] at hy
      exact ho y hy
  | finish p q _ =>
    have hsub : ∀ x y, y ∈ (endS s p q).sess x → y ∈ s.sess x := by
      intro x y hy
      rcases sess_at s.sess (endS s p q).sess p _ rfl x y hy with ⟨hxp, hm⟩ | ⟨_, hm⟩
      · rw [hxp]
        exact (List.mem_filter.mp hm).1
      · exact hm
    exact ⟨hf, hc, hk, ho, fun x hxd r hr => hx x hxd r (hr.imp id (hsub x r)), hcut,
      fun x r h => hso x r (hsub x r h)⟩
  | rehook p y =>
    have hgate : ∀ x, x ≠ p → ∀ z, gate (rehookS c s p y) x z = gate s x z := fun x hxp z => by
      simp only [gate, rehookS]
      rw [set_other _ _ _ _ hxp]
    have hcache : (rehookS c s p y).cache = set s.cache p .none := by simp [rehookS, hh]
    have hknown : (rehookS c s p y).known = set s.known p none := by simp [rehookS, hh]
    exact ⟨hf, forget_cache c s _ p hgate hcache hc, forget_known s _ p hgate hknown hk, ho,
      forget_deny c s _ p hgate hcache (fun _ _ _ h => h) hx, hcut, hso⟩

/-- With the code's settings every reachable state keeps the promises, whatever protocols the node lists and dials. -/
theorem inv_reach (c : Cfg) (hl : c.forgetOnLift = true) (hr : c.forgetOnRevoke = true) (hd : c.refuseDial = true)
    (hh : c.forgetOnChange = true) (ha : c.askEach = true) (hn : c.answerAny = true) (hheld : c.askHeld = true)
    (hda : c.dialAsks = true) (s : State) (h : Reach c s) : Inv c s := by
  induction h with
  | init => exact inv_init c
  | step s t _ st ih => exact inv_step c hl hr hd hh ha hn hheld hda s t ih st

/-- With each session asked on its own, no session is taken up on an allow given for another protocol or direction,
whatever the host does with revoke, unrevoke, `admission_changed` and the protocols it lists. -/
theorem noCrossAllow_reach (c : Cfg) (ha : c.askEach = true) (s : State) (h : Reach c s) : NoCrossAllow s := by
  induction h with
  | init => intro hd; simp [init] at hd
  | step s t _ st ih =>
    cases st with
    | cached p q _ _ _ => exact fun _ hu => upOf_cross c ha s p q _ _ hu
    | ask p q a _ _ _ _ => exact fun _ hu => upOf_cross c ha s p q _ _ hu
    | _ => exact ih

/-- With the code's settings the endpoint never holds a deny for a peer the gate allows a listed question or the
question of a session or dial this node holds with it: a refusal of one protocol never refuses a session or a dial of
another the hook allows. -/
theorem noCrossDeny_reach (c : Cfg) (hl : c.forgetOnLift = true) (hr : c.forgetOnRevoke = true)
    (hd : c.refuseDial = true) (hh : c.forgetOnChange = true) (ha : c.askEach = true) (hn : c.answerAny = true)
    (hheld : c.askHeld = true) (hda : c.dialAsks = true) (s : State) (h : Reach c s) : NoCrossDeny c s :=
  (inv_reach c hl hr hd hh ha hn hheld hda s h).2.2.2.2.1

/-- With the code's settings no refusal ever closes a session whose question the gate allows at that moment. -/
theorem noCut_reach (c : Cfg) (hl : c.forgetOnLift = true) (hr : c.forgetOnRevoke = true)
    (hd : c.refuseDial = true) (hh : c.forgetOnChange = true) (ha : c.askEach = true) (hn : c.answerAny = true)
    (hheld : c.askHeld = true) (hda : c.dialAsks = true) (s : State) (h : Reach c s) : NoCut s :=
  (inv_reach c hl hr hd hh ha hn hheld hda s h).2.2.2.2.2.1

#audit_axioms Pinc.FacadeAcpForget.inv_reach
#audit_axioms Pinc.FacadeAcpForget.noCrossAllow_reach
#audit_axioms Pinc.FacadeAcpForget.noCrossDeny_reach
#audit_axioms Pinc.FacadeAcpForget.noCut_reach

end Pinc.FacadeAcpForget
