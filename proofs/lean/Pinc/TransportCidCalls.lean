import Pinc.Axioms
import Pinc.TransportCidInv

/-!
# Connection ids: the calls and the runs

`install_inv` and `auth_inv` carry the table shape and the lookahead through the calls that fill the table;
`claim_some` and `claim_none` say what the sender's call takes, `claim_sender` that the index is 0 or in the window
of the highest one confirmed, `confirm_sender` and `confirm_usable` what a confirmation does; `Reach` is a run of any
calls with the indices forgotten recorded, and `reach_inv` shows that after any run the table has its shape, the
lookahead is held once the secret is installed, the highest index confirmed is one the sender took, and every index
forgotten is at least `look` below the highest one seen and not held: a retired id is never accepted again.
-/

namespace Pinc.TransportCid

theorem slotOf_spec (c : C) (k s : Nat) (h : slotOf c k = some s) : s < slots ∧ ∃ e, c.ent s = some e ∧ e.idx = k := by
  unfold slotOf at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  refine ⟨List.mem_range.1 h2, ?_⟩
  cases he : c.ent s with
  | none => simp [he] at h1
  | some e => simp [he] at h1; exact ⟨e, rfl, h1⟩

theorem core_tick (c : C) (hc : Core c) : Core { c with tick := c.tick + 1 } :=
  ⟨hc.bound, hc.nodup, hc.pos, hc.window, hc.seenLe⟩

theorem core_mark (c : C) (hc : Core c) (s k : Nat) (hs : s < slots) (e : E) (he : c.ent s = some e)
    (hk : e.idx = k) (h2 : Nat) (hh : c.hi ≤ h2) (hkh : k ≤ h2) (u : Nat) :
    Core { put c s ⟨k, u, true⟩ with hi := h2 } := by
  refine ⟨put_bound c s _ hs hc.bound, ?_, ?_, ?_, ?_⟩
  · intro s' t' a b ha hb hab
    simp only [put_ent] at ha hb
    by_cases h1 : s' = s <;> by_cases h2 : t' = s
    · rw [h1, h2]
    · simp [h1] at ha; simp [h2] at hb
      subst ha; exact absurd (hc.nodup s t' e b he hb (by rw [hk]; exact hab)) (fun h => h2 h.symm)
    · simp [h2] at hb; simp [h1] at ha
      subst hb; exact absurd (hc.nodup s' s a e ha he (by rw [hk]; exact hab)) h1
    · simp [h1] at ha; simp [h2] at hb
      exact hc.nodup s' t' a b ha hb hab
  · intro s' a ha
    simp only [put_ent] at ha
    by_cases h1 : s' = s
    · simp [h1] at ha; subst ha; have := hc.pos s e he; simpa [hk] using this
    · simp [h1] at ha; exact hc.pos s' a ha
  · intro s' a ha
    simp only [put_ent] at ha
    by_cases h1 : s' = s
    · simp [h1] at ha; subst ha
      have := hc.window s e he
      simp only [look] at this ⊢
      omega
    · simp [h1] at ha
      have := hc.window s' a ha
      simp only [look] at this ⊢
      omega
  · intro s' a ha hseen
    simp only [put_ent] at ha
    by_cases h1 : s' = s
    · simp [h1] at ha; subst ha; exact hkh
    · simp [h1] at ha
      have := hc.seenLe s' a ha hseen
      show a.idx ≤ h2
      omega

theorem has_mark (c : C) (hc : Core c) (s k : Nat) (hs : s < slots) (e : E) (he : c.ent s = some e)
    (hk : e.idx = k) (u : Nat) (b : Bool) (j : Nat) : has (put c s ⟨k, u, b⟩) j = has c j := by
  have hb := hc.bound
  cases h1 : has c j with
  | false =>
    cases h2 : has (put c s ⟨k, u, b⟩) j with
    | false => rfl
    | true =>
      rw [put_has c hb s hs] at h2
      rcases h2 with h | ⟨t, f, _, ht, hf⟩
      · have : has c j = true := (has_iff c hb j).2 ⟨s, e, he, by simpa [hk] using h⟩
        rw [h1] at this; simp at this
      · have : has c j = true := (has_iff c hb j).2 ⟨t, f, ht, hf⟩
        rw [h1] at this; simp at this
  | true =>
    rw [put_has c hb s hs]
    obtain ⟨t, f, ht, hf⟩ := (has_iff c hb j).1 h1
    by_cases hts : t = s
    · subst hts; rw [he] at ht; simp at ht; subst ht; exact Or.inl (by simpa [hk] using hf)
    · exact Or.inr ⟨t, f, hts, ht, hf⟩

theorem core_init : Core ({} : C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

theorem install_inv (c : C) (hc : Core c) :
    Core (install c).1 ∧ Ahead (install c).1 ∧
      (∀ v ∈ (install c).2, v + look ≤ c.hi ∧ has (install c).1 v = false) ∧ (install c).1.hi = c.hi ∧ (∀ j, has (install c).1 j = true → has c j = true ∨ (c.hi < j ∧ j ≤ c.hi + look)) := by
  unfold install
  have hc0 : Core { c with sec := true } := ⟨hc.bound, hc.nodup, hc.pos, hc.window, hc.seenLe⟩
  generalize hdef : ({ c with sec := true } : C) = c0 at hc0 ⊢
  have e_hi : c0.hi = c.hi := by rw [← hdef]
  have e_sec : c0.sec = true := by rw [← hdef]
  have e_has : ∀ j, has c0 j = has c j := by intro j; rw [← hdef]; rfl
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := refill_spec' c0 hc0
  refine ⟨r1, ?_, fun v hv => ⟨by have := r9 v hv; omega, r10 v hv⟩, by rw [r2, e_hi], fun j hj => ?_⟩
  · intro _ j hj1 hj2
    rw [r2, e_hi] at hj1 hj2
    have h7 := r7 e_sec
    rw [e_hi] at h7
    by_cases h : j = c.hi + 1
    · subst h; exact h7.1
    · have : j = c.hi + 2 := by simp [look] at hj2; omega
      subst this; exact h7.2
  · rcases r11 j hj with h | h
    · exact Or.inl (by rw [← e_has j]; exact h)
    · obtain ⟨h1, h2⟩ := h
      exact Or.inr ⟨by omega, by simp only [look] at h2 ⊢; omega⟩

theorem authAt_inv (c1 : C) (hc : Core c1) (ha : Ahead c1) (k s : Nat) (hs : s < slots) (e : E)
    (he : c1.ent s = some e) (hek : e.idx = k) :
    Core (authAt c1 k s).1 ∧ Ahead (authAt c1 k s).1 ∧ c1.hi ≤ (authAt c1 k s).1.hi ∧
      (∀ v ∈ (authAt c1 k s).2, v + look ≤ (authAt c1 k s).1.hi ∧ has (authAt c1 k s).1 v = false) ∧
      (∀ j, has (authAt c1 k s).1 j = true → has c1 j = true ∨ (c1.hi < j ∧ j ≤ (authAt c1 k s).1.hi + look)) := by
  unfold authAt
  have hm : ∀ j, has (put c1 s ⟨k, c1.tick, true⟩) j = has c1 j := has_mark c1 hc s k hs e he hek _ _
  by_cases hlt : c1.hi < k
  · rw [if_pos hlt]
    have hc3 := core_mark c1 hc s k hs e he hek k (by omega) (Nat.le_refl _) c1.tick
    generalize hdef : ({ put c1 s ⟨k, c1.tick, true⟩ with hi := k } : C) = c3 at hc3 ⊢
    have e_hi : c3.hi = k := by rw [← hdef]
    have e_has : ∀ j, has c3 j = has c1 j := by intro j; rw [← hdef]; exact hm j
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := refill_spec' c3 hc3
    refine ⟨r1, ?_, by rw [r2, e_hi]; omega, fun v hv => ⟨by rw [r2, e_hi]; have := r9 v hv; omega, r10 v hv⟩, ?_⟩
    · intro hsec j hj1 hj2
      rw [r2, e_hi] at hj1 hj2
      have hs3 : c3.sec = true := by rw [← r3]; exact hsec
      have h7 := r7 hs3
      rw [e_hi] at h7
      by_cases h : j = k + 1
      · subst h; exact h7.1
      · have : j = k + 2 := by simp [look] at hj2; omega
        subst this; exact h7.2
    · intro j hj
      rcases r11 j hj with h | h
      · exact Or.inl (by rw [← e_has j]; exact h)
      · right
        obtain ⟨h1, h2⟩ := h
        rw [r2, e_hi]
        rw [e_hi] at h1 h2
        exact ⟨by omega, by simp only [look] at h2 ⊢; omega⟩
  · rw [if_neg hlt]
    have hc3 := core_mark c1 hc s k hs e he hek c1.hi (Nat.le_refl _) (by omega) c1.tick
    refine ⟨⟨hc3.bound, hc3.nodup, hc3.pos, hc3.window, hc3.seenLe⟩, ?_, Nat.le_refl _, fun v hv => by simp at hv,
      fun j hj => Or.inl (by rw [← hm j]; exact hj)⟩
    intro hsec j hj1 hj2
    rw [hm j]
    exact ha hsec j hj1 hj2

theorem auth_cases (c : C) (k : Nat) :
    auth c k = ({ c with tick := c.tick + 1 }, []) ∨
      ∃ s, slotOf { c with tick := c.tick + 1 } k = some s ∧ auth c k = authAt { c with tick := c.tick + 1 } k s := by
  unfold auth
  by_cases hk : k < 1
  · left; simp [hk]
  · cases hsl : slotOf { c with tick := c.tick + 1 } k with
    | none => left; simp [hk, hsl]
    | some s => right; exact ⟨s, rfl, by simp [hk, hsl]⟩

theorem auth_inv (c : C) (hc : Core c) (ha : Ahead c) (k : Nat) :
    Core (auth c k).1 ∧ Ahead (auth c k).1 ∧ c.hi ≤ (auth c k).1.hi ∧
      (∀ v ∈ (auth c k).2, v + look ≤ (auth c k).1.hi ∧ has (auth c k).1 v = false) ∧
      (∀ j, has (auth c k).1 j = true → has c j = true ∨ (c.hi < j ∧ j ≤ (auth c k).1.hi + look)) := by
  rcases auth_cases c k with h | ⟨s, hs', h⟩
  · rw [h]
    exact ⟨core_tick c hc, fun h j h1 h2 => ha h j h1 h2, Nat.le_refl _, fun v hv => by simp at hv, fun j hj => Or.inl hj⟩
  · obtain ⟨hslt, e, he, hek⟩ := slotOf_spec _ k s hs'
    rw [h]
    exact authAt_inv { c with tick := c.tick + 1 } (core_tick c hc) (fun h j h1 h2 => ha h j h1 h2) k s hslt e he hek

theorem refill1_sender (c : C) (k : Nat) : (refill1 c k).1.cf = c.cf ∧ (refill1 c k).1.ns = c.ns := by
  unfold refill1
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem refill_sender (c : C) : (refill c).1.cf = c.cf ∧ (refill c).1.ns = c.ns := by
  unfold refill
  split
  · have h1 := refill1_sender c (c.hi + 1)
    have h2 := refill1_sender (refill1 c (c.hi + 1)).1 (c.hi + 2)
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
  · exact ⟨rfl, rfl⟩

/-- The calls of the receiving side leave the sender's counters alone. -/
theorem install_sender (c : C) : (install c).1.cf = c.cf ∧ (install c).1.ns = c.ns :=
  refill_sender { c with sec := true }

theorem auth_sender (c : C) (k : Nat) : (auth c k).1.cf = c.cf ∧ (auth c k).1.ns = c.ns := by
  rcases auth_cases c k with h | ⟨s, _, h⟩
  · rw [h]; exact ⟨rfl, rfl⟩
  · rw [h]
    unfold authAt
    split
    · exact refill_sender _
    · exact ⟨rfl, rfl⟩

/-- What the sender's counters keep: the highest index confirmed is 0 or one the sender took. -/
def Sender (c : C) : Prop := c.cf = 0 ∨ c.cf < c.ns

/-- A claim that takes an index: the peer's first id is known, the secret is installed for an index past 0, and
either the next index is within `look` of the highest one confirmed and is the one taken, or it is past that window
and the index taken is one of the window, which the sender took before (it is below the next index). -/
theorem claim_some (c c' : C) (k : Nat) (h : claim c = (c', some k)) :
    c.fr = true ∧ (k = 0 ∨ c.sec = true) ∧ c'.ent = c.ent ∧ c'.hi = c.hi ∧ c'.sec = c.sec ∧ c'.cf = c.cf ∧
      ((c.ns ≤ c.cf + look ∧ k = c.ns ∧ c'.ns = c.ns + 1 ∧ c'.ru = c.ru) ∨
        (c.cf + look < c.ns ∧ c.cf < k ∧ k ≤ c.cf + look ∧ c'.ns = c.ns ∧ c'.ru = c.ru + 1)) := by
  unfold claim at h
  by_cases hc : (!c.fr || (decide (0 < claimIndex c) && !c.sec)) = true
  · simp [hc] at h
  · simp only [hc, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, not_and] at hc
    obtain ⟨h1, h2⟩ := hc
    have hfr : c.fr = true := by simpa using h1
    have hsec : claimIndex c = 0 ∨ c.sec = true := by
      by_cases hn : claimIndex c = 0
      · exact Or.inl hn
      · right; have := h2 (by omega); simpa using this
    by_cases hf : claimFresh c = true
    · have hle : c.ns ≤ c.cf + look := by simpa [claimFresh] using hf
      have hi : claimIndex c = c.ns := by simp [claimIndex, hf]
      rw [if_pos hf]
      exact ⟨hfr, hsec, rfl, rfl, rfl, rfl, Or.inl ⟨hle, hi, rfl, rfl⟩⟩
    · have hgt : c.cf + look < c.ns := by
        have : ¬ c.ns ≤ c.cf + look := by simpa [claimFresh] using hf
        omega
      have hi : claimIndex c = c.cf + 1 + c.ru % look := by simp [claimIndex, hf]
      have hm : c.ru % look < look := Nat.mod_lt _ (by decide)
      rw [if_neg hf]
      exact ⟨hfr, hsec, rfl, rfl, rfl, rfl, Or.inr ⟨hgt, by rw [hi]; omega, by rw [hi]; omega, rfl, rfl⟩⟩

theorem claim_none (c c' : C) (h : claim c = (c', none)) : c' = c := by
  unfold claim at h
  by_cases hc : (!c.fr || (decide (0 < claimIndex c) && !c.sec)) = true
  · simp only [hc, if_true, Prod.mk.injEq] at h; exact h.1.symm
  · simp [hc] at h

/-- The index a claim takes is 0 or one of the `look` indices after the highest one confirmed, and it is below the
next index (so the indices taken are those below `ns`); the counters keep their relation. -/
theorem claim_sender (c c' : C) (k : Nat) (hs : Sender c) (h : claim c = (c', some k)) :
    (k = 0 ∨ (c.cf < k ∧ k ≤ c.cf + look)) ∧ k < c'.ns ∧ Sender c' := by
  obtain ⟨_, _, _, _, _, hcf, hk⟩ := claim_some c c' k h
  unfold Sender at *
  rw [hcf]
  rcases hk with ⟨h1, h2, h3, _⟩ | ⟨h1, h2, h3, h4, _⟩
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨Or.inr ⟨h2, h3⟩, by omega, by omega⟩

/-- The peer is known to accept the id a claim takes (`remote_usable` of the index, right after the claim). -/
theorem claim_usable (c c' : C) (k : Nat) (hs : Sender c) (h : claim c = (c', some k)) :
    remoteUsable c' k = true := by
  have hcf := (claim_some c c' k h).2.2.2.2.2.1
  have hw := (claim_sender c c' k hs h).1
  unfold remoteUsable
  rw [hcf]
  rcases hw with h0 | ⟨h1, _⟩
  · simp [h0]
  · simp [h1]

/-- A confirmation of an index the sender took keeps the relation of the counters. -/
theorem confirm_sender (c : C) (k : Nat) (hs : Sender c) (hk : k < c.ns) : Sender (confirm c k) := by
  unfold Sender at *
  show max c.cf k = 0 ∨ max c.cf k < c.ns
  omega

/-- A confirmation moves the highest index confirmed up to `k`, never down. -/
theorem confirm_cf (c : C) (k : Nat) :
    c.cf ≤ (confirm c k).cf ∧ k ≤ (confirm c k).cf ∧ ((confirm c k).cf = c.cf ∨ (confirm c k).cf = k) := by
  show c.cf ≤ max c.cf k ∧ k ≤ max c.cf k ∧ (max c.cf k = c.cf ∨ max c.cf k = k)
  omega

/-- An index the peer is known to accept after a confirmation was known to be accepted before it, and it is 0 or
above the index confirmed (a path that holds the index confirmed or a lower one without an answer of its own gives
it up). -/
theorem confirm_usable (c : C) (k j : Nat) (h : remoteUsable (confirm c k) j = true) :
    remoteUsable c j = true ∧ (j = 0 ∨ k < j) := by
  have hc := confirm_cf c k
  unfold remoteUsable at *
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  omega

/-- A run of calls, with the indices the table forgot. The connection confirms the index a path claimed
(`confirm_dcid` in `conn/send.rs`), so a confirmation is of an index the sender took. -/
inductive Reach : C → List Nat → Prop
  | init : Reach {} []
  | install (c : C) (ret : List Nat) : Reach c ret → Reach (install c).1 ((install c).2 ++ ret)
  | auth (c : C) (ret : List Nat) (k : Nat) : Reach c ret → Reach (auth c k).1 ((auth c k).2 ++ ret)
  | frem (c : C) (ret : List Nat) : Reach c ret → Reach (setFirstRemote c) ret
  | claim (c : C) (ret : List Nat) : Reach c ret → Reach (claim c).1 ret
  | confirm (c : C) (ret : List Nat) (k : Nat) : Reach c ret → k < c.ns → Reach (confirm c k) ret

theorem claim_fst (c : C) : ∃ n r, (claim c).1 = { c with ns := n, ru := r } := by
  unfold claim
  split
  · exact ⟨c.ns, c.ru, rfl⟩
  · split
    · exact ⟨c.ns + 1, c.ru, rfl⟩
    · exact ⟨c.ns, c.ru + 1, rfl⟩

/-- After any run: the table has its shape, the lookahead is held once the secret is installed, the highest index
confirmed is 0 or one the sender took, and every index forgotten is at least `look` below the highest one seen and
not held. -/
theorem reach_inv {c : C} {ret : List Nat} (h : Reach c ret) :
    Core c ∧ Ahead c ∧ Sender c ∧ ∀ r ∈ ret, r + look ≤ c.hi ∧ has c r = false := by
  induction h with
  | init =>
    refine ⟨core_init, ?_, Or.inl rfl, fun r hr => by simp at hr⟩
    intro h; simp at h
  | install c ret _ ih =>
    obtain ⟨hc, ha, hs, hr⟩ := ih
    obtain ⟨i1, i2, i3, i4, i5⟩ := install_inv c hc
    obtain ⟨s1, s2⟩ := install_sender c
    refine ⟨i1, i2, by unfold Sender at *; omega, ?_⟩
    intro r hr'
    rcases List.mem_append.1 hr' with h1 | h1
    · exact ⟨by have := (i3 r h1).1; omega, (i3 r h1).2⟩
    · obtain ⟨h2, h3⟩ := hr r h1
      refine ⟨by omega, ?_⟩
      apply Classical.byContradiction; intro hx
      have hx' : has (install c).1 r = true := by simpa using hx
      rcases i5 r hx' with h4 | h4
      · rw [h3] at h4; simp at h4
      · omega
  | auth c ret k _ ih =>
    obtain ⟨hc, ha, hs, hr⟩ := ih
    obtain ⟨i1, i2, i3, i4, i5⟩ := auth_inv c hc ha k
    obtain ⟨s1, s2⟩ := auth_sender c k
    refine ⟨i1, i2, by unfold Sender at *; omega, ?_⟩
    intro r hr'
    rcases List.mem_append.1 hr' with h1 | h1
    · exact i4 r h1
    · obtain ⟨h2, h3⟩ := hr r h1
      refine ⟨by omega, ?_⟩
      apply Classical.byContradiction; intro hx
      have hx' : has (auth c k).1 r = true := by simpa using hx
      rcases i5 r hx' with h4 | h4
      · rw [h3] at h4; simp at h4
      · omega
  | frem c ret _ ih =>
    obtain ⟨hc, ha, hs, hr⟩ := ih
    exact ⟨⟨hc.bound, hc.nodup, hc.pos, hc.window, hc.seenLe⟩, ha, hs, hr⟩
  | claim c ret _ ih =>
    obtain ⟨hc, ha, hs, hr⟩ := ih
    have hs' : Sender (claim c).1 := by
      rcases hcl : claim c with ⟨c', o⟩
      cases o with
      | none => rw [claim_none c c' hcl]; exact hs
      | some k => exact (claim_sender c c' k hs hcl).2.2
    obtain ⟨n, r, hn⟩ := claim_fst c
    rw [hn] at hs' ⊢
    exact ⟨⟨hc.bound, hc.nodup, hc.pos, hc.window, hc.seenLe⟩, ha, hs', hr⟩
  | confirm c ret k _ hk ih =>
    obtain ⟨hc, ha, hs, hr⟩ := ih
    exact ⟨⟨hc.bound, hc.nodup, hc.pos, hc.window, hc.seenLe⟩, ha, confirm_sender c k hs hk, hr⟩

/-- After any run, the index a claim takes is 0 or one of the `look` indices after the highest one confirmed. -/
theorem reach_claim {c : C} {ret : List Nat} (h : Reach c ret) (c' : C) (k : Nat) (hcl : claim c = (c', some k)) :
    k = 0 ∨ (c.cf < k ∧ k ≤ c.cf + look) :=
  (claim_sender c c' k (reach_inv h).2.2.1 hcl).1

end Pinc.TransportCid
