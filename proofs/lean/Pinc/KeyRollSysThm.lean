import Pinc.KeyRollSysReach

/-!
# Properties of the key roll system

Every theorem here is about a reachable state (`Reach P S`) of `Pinc.KeyRollSys`, for every parameter `P`. The names are
those of the invariants and action properties of `KeyRoll.tla`.
-/

namespace Pinc.KeyRollSys
open Pinc.KeyRoll

section State
variable {P : Params} {S : Sys} (hr : Reach P S)
include hr

/-- The generation of a key is the depth of its secret (`GenIsDepth`). -/
theorem genIsDepth (n : Bool) :
    (S.nd n).sk.g = (S.nd n).sk.sec.depth ∧ (S.nd n).cur.g = (S.nd n).cur.sec.depth := by
  have := ((hr.inv).node n).depths
  exact ⟨this.1.symm, this.2.1.symm⟩

/-- The phase bit is the parity of the generation, for every key held (`PhaseParity`). -/
theorem phaseParity (n : Bool) :
    (S.nd n).sph = decide ((S.nd n).sk.g % 2 = 1) ∧ (S.nd n).rph = decide ((S.nd n).cur.g % 2 = 1) ∧
    (∀ k, (S.nd n).stg = some k → k.g = (S.nd n).sk.g + 1) ∧
    (∀ x, (S.nd n).nxt = some x → x.k.g = (S.nd n).cur.g + 1) ∧
    (∀ pv, (S.nd n).prev = some pv → pv.k.g + 1 = (S.nd n).cur.g) := by
  have h := (hr.inv).node n
  exact ⟨h.phS, h.phR, fun k hk => (h.kfStg k hk).2, fun x hx => (h.kfNxt x hx).2, fun pv hpv => (h.kfPrev pv hpv).2⟩


/-- The generations of the sending and receiving keys of the two nodes. -/
def gens (S : Sys) : List Nat := [(S.nd false).sk.g, (S.nd false).cur.g, (S.nd true).sk.g, (S.nd true).cur.g]

/-- Both sides stay in step: any two of these generations differ by at most one (`InStep`). -/
theorem inStep : ∀ a ∈ gens S, ∀ b ∈ gens S, a ≤ b + 1 := by
  have I := hr.inv
  have d0 := I.d1 false
  have d1 := I.d1 true
  have c0 := (I.node false).cn
  have c1 := (I.node true).cn
  simp only [Bool.not_false, Bool.not_true] at d0 d1
  have g0 : (S.nd false).cur.g ≤ (S.nd false).sk.g ∧ (S.nd false).sk.g ≤ (S.nd false).cur.g + 1 := by
    by_cases a : (S.nd false).stg.isSome = true
    · have n1 := c0.2.2.2.2 a; have s1 := c0.1 a; have n2 := c0.2.2.1 n1; omega
    · have a' : (S.nd false).stg.isSome = false := by simpa using a
      have := c0.2.1 a'
      by_cases b : (S.nd false).nxt.isSome = true
      · have := c0.2.2.1 b; omega
      · have b' : (S.nd false).nxt.isSome = false := by simpa using b
        have := c0.2.2.2.1 b'; omega
  have g1 : (S.nd true).cur.g ≤ (S.nd true).sk.g ∧ (S.nd true).sk.g ≤ (S.nd true).cur.g + 1 := by
    by_cases a : (S.nd true).stg.isSome = true
    · have n1 := c1.2.2.2.2 a; have s1 := c1.1 a; have n2 := c1.2.2.1 n1; omega
    · have a' : (S.nd true).stg.isSome = false := by simpa using a
      have := c1.2.1 a'
      by_cases b : (S.nd true).nxt.isSome = true
      · have := c1.2.2.1 b; omega
      · have b' : (S.nd true).nxt.isSome = false := by simpa using b
        have := c1.2.2.2.1 b'; omega
  intro a ha b hb'
  simp only [gens, List.mem_cons, List.not_mem_nil, or_false] at ha hb'
  omega

/-- The keys of one direction: what the sender holds and what the receiver holds. -/
def held (S : Sys) (n : Bool) : List PK :=
  [(S.nd n).sk] ++ ((S.nd n).stg.toList) ++ [(S.nd (!n)).cur] ++ ((S.nd (!n)).prev.toList.map (·.k)) ++
    ((S.nd (!n)).nxt.toList.map (·.k))

end State

/-- A key is the roll of its base by the first `g` Diffie-Hellman values of its holder, `g` within the number of
derivations. -/
theorem key_form {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) :
    (∃ k, k = s.sk ∧ k.sec = rollAll (.base (nid n)) ((dhs s).take k.g) ∧ k.g ≤ s.chg) ∧
    (∀ k, s.stg = some k → k.sec = rollAll (.base (nid n)) ((dhs s).take k.g) ∧ k.g ≤ s.chg) ∧
    (s.cur.sec = rollAll (.base (nid (!n))) ((dhs s).take s.cur.g) ∧ s.cur.g ≤ s.chg) ∧
    (∀ pv, s.prev = some pv → pv.k.sec = rollAll (.base (nid (!n))) ((dhs s).take pv.k.g) ∧ pv.k.g ≤ s.chg) ∧
    (∀ x, s.nxt = some x → x.k.sec = rollAll (.base (nid (!n))) ((dhs s).take x.k.g) ∧ x.k.g ≤ s.chg) := by
  have c1 := h.cnSk
  have c2 := h.cnCur
  refine ⟨⟨_, rfl, h.kfSk, ?_⟩, fun k hk => ?_, ⟨h.kfCur, ?_⟩, fun pv hpv => ?_, fun x hx => ?_⟩
  · split at c1 <;> omega
  · obtain ⟨a, b⟩ := h.kfStg k hk
    refine ⟨by rw [b]; exact a, ?_⟩
    simp only [hk, Option.isSome_some, ↓reduceIte] at c1; omega
  · split at c2 <;> omega
  · obtain ⟨a, b⟩ := h.kfPrev pv hpv
    refine ⟨a, ?_⟩
    split at c2 <;> omega
  · obtain ⟨a, b⟩ := h.kfNxt x hx
    refine ⟨by rw [b]; exact a, ?_⟩
    simp only [hx, Option.isSome_some, ↓reduceIte] at c2; omega

theorem take_eq_of_pp {α : Type} {a b : List α} (h : PP a b) {g : Nat} (ha : g ≤ a.length) (hb : g ≤ b.length) :
    a.take g = b.take g := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [List.take_append_of_le_length ha]
  · rw [List.take_append_of_le_length hb]

section State
variable {P : Params} {S : Sys} (hr : Reach P S)
include hr


omit hr in
theorem dhs_pp {P : Params} {S : Sys} (I : Inv P S) (n : Bool) : PP (dhs (S.nd n)) (dhs (S.nd (!n))) := by
  have h := I.ppn n
  have e : ∀ s : Node, dhs s = (s.ders.map Der.core).map Prod.snd := by intro s; simp [dhs, Der.core, Function.comp_def]
  rw [e, e]
  rcases h with h | h
  · exact Or.inl (h.map _)
  · exact Or.inr (h.map _)

/-- The keys of one direction agree: two of the same generation are the same secret (`KeysAgree`). -/
theorem keysAgree (n : Bool) : ∀ x ∈ held S n, ∀ y ∈ held S n, x.g = y.g → x.sec = y.sec := by
  have I := hr.inv
  have fn := key_form (I.node n)
  have fm := key_form (I.node (!n))
  simp only [Bool.not_not] at fm
  have pp := dhs_pp I n
  -- every held key is a roll of the base of node n by a prefix of one of the two derivation lists
  have mem : ∀ x ∈ held S n, (x.sec = rollAll (.base (nid n)) ((dhs (S.nd n)).take x.g) ∧ x.g ≤ (S.nd n).chg) ∨
      (x.sec = rollAll (.base (nid n)) ((dhs (S.nd (!n))).take x.g) ∧ x.g ≤ (S.nd (!n)).chg) := by
    intro x hx
    simp only [held, List.mem_append, List.mem_singleton, Option.toList, List.mem_map] at hx
    rcases hx with ((((hx | hx) | hx) | hx) | hx)
    · subst hx; left; obtain ⟨_, rfl, a, b⟩ := fn.1; exact ⟨a, b⟩
    · cases hs : (S.nd n).stg with
      | none => rw [hs] at hx; simp at hx
      | some k => rw [hs] at hx; simp at hx; (first | rw [hx] | rw [← hx]); left; exact fn.2.1 k hs
    · subst hx; right; exact fm.2.2.1
    · cases hs : (S.nd (!n)).prev with
      | none => rw [hs] at hx; simp at hx
      | some pv => rw [hs] at hx; simp at hx; (first | rw [← hx] | rw [hx]); right; exact fm.2.2.2.1 pv hs
    · cases hs : (S.nd (!n)).nxt with
      | none => rw [hs] at hx; simp at hx
      | some y => rw [hs] at hx; simp at hx; (first | rw [← hx] | rw [hx]); right; exact fm.2.2.2.2 y hs
  intro x hx y hy hg
  rcases mem x hx with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases mem y hy with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · rw [a1, b1, hg]
  · rw [a1, b1, ← hg]
    rw [take_eq_of_pp pp (by simpa [dhs_length] using a2) (by rw [dhs_length]; omega)]
  · rw [a1, b1, hg]
    rw [take_eq_of_pp pp.comm (by rw [dhs_length]; omega) (by simpa [dhs_length] using b2)]
  · rw [a1, b1, hg]

/-- No packet number is sealed twice under a key, and a node's sending generation never goes back (`NoKeyReuse`). -/
theorem noKeyReuse : (∀ x ∈ S.slog, ∀ y ∈ S.slog, x.n = y.n → x.pn < y.pn → x.g ≤ y.g) ∧
    (∀ x ∈ S.slog, ∀ y ∈ S.slog, x.sec = y.sec → x.pn = y.pn → x = y) := by
  have I := hr.inv
  refine ⟨I.slogOrd, fun x hx y hy hs hp => ?_⟩
  obtain ⟨_, _, _, ds, hds⟩ := I.slogOK x hx
  obtain ⟨_, _, _, es, hes⟩ := I.slogOK y hy
  have := (rollAll_base_inj _ _ _ _ (hds.symm.trans (hs.trans hes))).1
  have hn : x.n = y.n := by
    cases hx' : x.n <;> cases hy' : y.n <;> simp_all [nid]
  exact I.slogUniq x hx y hy hn hp

/-- Every request share is used for one roll, and the completed-rolls counter counts the derivations
(`SharesOnce`); the counter saturates at `u64::MAX`. -/
theorem sharesOnce : (∀ c ∈ S.comp, ∀ c' ∈ S.comp, c.req = c'.req → c = c') ∧
    ∀ n, (S.nd n).roll.rolls = min (S.nd n).chg Record.u64max :=
  ⟨(hr.inv).compUniq, fun n => ((hr.inv).node n).rolls⟩

/-- The old key is held exactly one probe timeout: its deadline is the promotion time plus `pto` (`HoldOnePTO`). -/
theorem holdOnePTO (n : Bool) : ∀ pv, (S.nd n).prev = some pv → ∃ t, (S.nd n).promAt = some t ∧ pv.dl = t + P.pto :=
  ((hr.inv).node n).hold

/-- When both complete a roll they computed the same Diffie-Hellman value (`AgreeDh`). -/
theorem agreeDh : ∀ c ∈ S.comp, c.dh = c.gdh := (hr.inv).agree

/-- The floor in an answer is a true floor: every packet the peer sealed under the staged next key has a number
at or above it (`FloorHonoured`). -/
theorem floorHonoured (n : Bool) : ∀ x, (S.nd n).nxt = some x → ∀ p ∈ S.net, p.src = !n → p.sec = x.k.sec →
    x.floor ≤ p.pn := by
  have I := hr.inv
  intro x hx p hp hsrc hsec
  rcases I.nxtFloor n x hx with h0 | ⟨c, hc, hcn, hpos, hspn⟩
  · omega
  · have hseal := I.netSlog p hp
    obtain ⟨_, _, _, _, _, h6, _⟩ := I.stlOK c hc
    have hdep := ((I.node n).depths).2.2.2.1 x hx
    have hxg := (NodeInv.kfNxt (I.node n) x hx).2
    have := h6 _ hseal (by simp only; rw [hsrc, hcn]) (by simp only; rw [hsec, hdep, hxg, ← hpos]; omega)
    simp only at this
    omega

end State

end Pinc.KeyRollSys
