import Pinc.Axioms
import Pinc.CoreNodeBackoff

/-!
# The node's table of failed dials: bounded, doubling to a cap, never evicting, saturating

What the model proves about the table of failed dials and the dials in progress, for any table size, any times (a
clock that steps back included) and any run of calls:

- each table stays within its bound (`setFailed_length_le`, `backoff_length_le`, `denyBack_length_le`,
  `closed_length_le`, `prune_length_le`, `connecting_length_le`), and has one entry per peer (`put_keys`,
  `step_inv`);
- a full table refuses an entry for a peer it has none for and changes nothing; it never evicts, and no call but a
  reset and the prune takes an entry away (`setFailed_full`, `setFailed_keeps`, `backoff_full`, `denyBack_full`,
  `setFailed_other`);
- a failed dial waits `first` the first time and then twice the wait of its entry up to the cap, 16 s for a hub and
  60 s for any other node, and never more than the cap (`backoff_first`, `backoff_double`, `backoff_le_cap`); from an
  empty table the waits are `min (first * 2 ^ k) cap` (`chain_wait`, `chain_hub`);
- a refusal waits `denyFirst`, or from an entry of at least that twice up to `denyCap` (`denyBack_first`,
  `denyBack_double`, `denyBack_le`);
- the entry's time is the time of the failure plus its wait, saturating at `u64::MAX`, and never below the wait
  (`setFailed_get`, `satAdd_le`, `satAdd_ge`, `until_ge_back`);
- a dial is made only outside the backoff window and a dial is refused inside it (`gate_no_window`,
  `window_no_gate`); an entry is a window until its time and not from then on (`window_iff`);
- a closed session forgets the entry of its peer when it lived at least `lived`, is a failed dial when it lived less
  and a refusal when the peer refused us (`closed_long`, `closed_short`, `closed_den`);
- a dial whose session came up and that the full session table shed (`hub_connected`, the step `shed`) is a failed
  dial: the peer is not dialed before the wait is over, and, the shed having ended its dial in progress, it is dialed
  from then on when nothing else refuses (`shed_waits`, `shed_redials`);
- the prune lets go of exactly the entries whose time plus `keep` (saturating) is not after now (`prune_mem`);
- every table stays within its bound and the dials in progress never overlap the sessions through any run of the
  steps of the node (`step_inv`, `reach_inv`).
-/

namespace Pinc.NodeBackoff

theorem MAXU_pos : 0 < MAXU := by unfold MAXU; omega

theorem satAdd_le (a b : Nat) : satAdd a b ≤ MAXU := by unfold satAdd; omega
theorem satAdd_ge (a b : Nat) (ha : a ≤ MAXU) : a ≤ satAdd a b := by unfold satAdd; omega
theorem satAdd_ge_right (a b : Nat) (hb : b ≤ MAXU) : b ≤ satAdd a b := by unfold satAdd; omega
theorem satAdd_eq (a b : Nat) (h : a + b ≤ MAXU) : satAdd a b = a + b := by unfold satAdd; omega
theorem satAdd_sat (a b : Nat) (h : MAXU ≤ a + b) : satAdd a b = MAXU := by unfold satAdd; omega
theorem satMul2_le (b : Nat) : satMul2 b ≤ MAXU := by unfold satMul2; omega

/-! ## The map operations -/

theorem get_put_self (f : Tab) (p u b : Nat) : get (put f p u b) p = some (u, b) := by
  induction f with
  | nil => simp [put, get]
  | cons e r ih =>
    obtain ⟨q, u', b'⟩ := e
    by_cases h : q = p
    · simp [put, get, h]
    · simp [put, get, h, ih]

theorem get_put_other (f : Tab) (p q u b : Nat) (h : q ≠ p) : get (put f p u b) q = get f q := by
  induction f with
  | nil => simp [put, get, Ne.symm h]
  | cons e r ih =>
    obtain ⟨q', u', b'⟩ := e
    by_cases h1 : q' = p
    · subst h1
      simp [put, get, Ne.symm h]
    · by_cases h2 : q' = q
      · subst h2; simp [put, get, h1]
      · simp [put, get, h1, h2, ih]

theorem get_del_self (f : Tab) (p : Nat) : get (del f p) p = none := by
  induction f with
  | nil => simp [del, get]
  | cons e r ih =>
    obtain ⟨q, u, b⟩ := e
    by_cases h : q = p
    · simpa [del, h] using ih
    · simp [del, get, h]
      simpa [del] using ih

theorem get_del_other (f : Tab) (p q : Nat) (h : q ≠ p) : get (del f p) q = get f q := by
  induction f with
  | nil => simp [del, get]
  | cons e r ih =>
    obtain ⟨q', u, b⟩ := e
    by_cases h1 : q' = p
    · subst h1
      simpa [del, get, h, Ne.symm h] using ih
    · by_cases h2 : q' = q
      · subst h2; simp [del, get, h1]
      · simp [del, get, h1, h2]
        simpa [del] using ih

theorem length_put (f : Tab) (p u b : Nat) :
    (put f p u b).length = if (get f p).isSome then f.length else f.length + 1 := by
  induction f with
  | nil => simp [put, get]
  | cons e r ih =>
    obtain ⟨q, u', b'⟩ := e
    by_cases h : q = p
    · simp [put, get, h]
    · simp [put, get, h, ih]
      split <;> simp

/-- The peers of a table. -/
def keys (f : Tab) : List Nat := f.map (·.1)

theorem put_keys (f : Tab) (p u b : Nat) :
    keys (put f p u b) = if p ∈ keys f then keys f else keys f ++ [p] := by
  induction f with
  | nil => simp [put, keys]
  | cons e r ih =>
    obtain ⟨q, u', b'⟩ := e
    by_cases h : q = p
    · simp [put, keys, h]
    · have ih' : (put r p u b).map (·.1) =
          if p ∈ r.map (·.1) then r.map (·.1) else r.map (·.1) ++ [p] := ih
      by_cases hm : p ∈ r.map (·.1) <;> simp [keys, put, h, ih', hm, Ne.symm h]

theorem keys_filter (f : Tab) (g : Nat × Nat × Nat → Bool) :
    (keys (f.filter g)).Sublist (keys f) := by
  unfold keys
  exact (List.filter_sublist).map _

theorem keys_nodup_put (f : Tab) (p u b : Nat) (h : (keys f).Nodup) : (keys (put f p u b)).Nodup := by
  rw [put_keys]
  split
  · exact h
  · rename_i hm
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb hab
    simp at hb
    subst hb; subst hab
    exact hm ha

theorem keys_nodup_filter (f : Tab) (g : Nat × Nat × Nat → Bool) (h : (keys f).Nodup) :
    (keys (f.filter g)).Nodup := (keys_filter f g).nodup h

theorem length_del_le (f : Tab) (p : Nat) : (del f p).length ≤ f.length := List.length_filter_le _ _
theorem length_prune_le (f : Tab) (now : Nat) : (prune f now).length ≤ f.length := List.length_filter_le _ _

/-! ## `set_failed` and the two waits -/

/-- A table within its bound stays within it. -/
theorem setFailed_length_le (max : Nat) (f : Tab) (now p back : Nat) (h : f.length ≤ max) :
    (setFailed max f now p back).length ≤ max := by
  unfold setFailed
  split
  · rename_i hc
    rw [length_put]
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    split
    · exact h
    · rename_i hn
      rcases hc with hc | hc
      · omega
      · simp [hc] at hn
  · exact h

/-- A full table refuses a peer it has no entry for, and changes nothing. -/
theorem setFailed_full (max : Nat) (f : Tab) (now p back : Nat) (hfull : max ≤ f.length)
    (hnone : get f p = none) : setFailed max f now p back = f := by
  unfold setFailed
  have : ¬ (f.length < max || (get f p).isSome) = true := by simp [hnone]; omega
  simp [this]

/-- The entry is stored when there is room or the peer has one: its time is the failure's plus the wait. -/
theorem setFailed_get (max : Nat) (f : Tab) (now p back : Nat)
    (h : f.length < max ∨ (get f p).isSome = true) :
    get (setFailed max f now p back) p = some (satAdd now back, back) := by
  unfold setFailed
  have : (f.length < max || (get f p).isSome) = true := by simpa using h
  simp only [this, ↓reduceIte]
  exact get_put_self ..

/-- Every other peer's entry is as it was. -/
theorem setFailed_other (max : Nat) (f : Tab) (now p back q : Nat) (h : q ≠ p) :
    get (setFailed max f now p back) q = get f q := by
  unfold setFailed
  split
  · exact get_put_other _ _ _ _ _ h
  · rfl

/-- A peer that has an entry keeps one: a full table never evicts. -/
theorem setFailed_keeps (max : Nat) (f : Tab) (now p back q : Nat) (h : (get f q).isSome = true) :
    (get (setFailed max f now p back) q).isSome = true := by
  by_cases hq : q = p
  · subst hq
    rw [setFailed_get max f now q back (Or.inr h)]; rfl
  · rw [setFailed_other max f now p back q hq]; exact h

theorem setFailed_keys_nodup (max : Nat) (f : Tab) (now p back : Nat) (h : (keys f).Nodup) :
    (keys (setFailed max f now p back)).Nodup := by
  unfold setFailed
  split
  · exact keys_nodup_put _ _ _ _ h
  · exact h

theorem backoff_length_le (max : Nat) (hub : Bool) (f : Tab) (now p : Nat) (h : f.length ≤ max) :
    (backoff max hub f now p).2.length ≤ max := setFailed_length_le _ _ _ _ _ h

theorem denyBack_length_le (max : Nat) (f : Tab) (now p : Nat) (h : f.length ≤ max) :
    (denyBack max f now p).2.length ≤ max := setFailed_length_le _ _ _ _ _ h

theorem backoff_full (max : Nat) (hub : Bool) (f : Tab) (now p : Nat) (hfull : max ≤ f.length)
    (hnone : get f p = none) : (backoff max hub f now p).2 = f := setFailed_full _ _ _ _ _ hfull hnone

theorem denyBack_full (max : Nat) (f : Tab) (now p : Nat) (hfull : max ≤ f.length)
    (hnone : get f p = none) : (denyBack max f now p).2 = f := setFailed_full _ _ _ _ _ hfull hnone

/-! ## The waits -/

theorem first_le_hubCap : first ≤ hubCap := by decide
theorem first_le_cap : first ≤ cap := by decide
theorem hubCap_le_cap : hubCap ≤ cap := by decide
theorem cap_le_denyCap : cap ≤ denyCap := by decide
theorem denyFirst_le_denyCap : denyFirst ≤ denyCap := by decide
theorem denyCap_le_MAXU : denyCap ≤ MAXU := by decide

theorem capOf_le (hub : Bool) : capOf hub ≤ cap := by
  cases hub <;> simp [capOf, hubCap_le_cap]

theorem first_le_capOf (hub : Bool) : first ≤ capOf hub := by
  cases hub <;> simp [capOf, first_le_hubCap, first_le_cap]

theorem backoff_first (max : Nat) (hub : Bool) (f : Tab) (now p : Nat) (h : get f p = none) :
    (backoff max hub f now p).1 = first := by
  simp [backoff, backWait, h]

/-- A peer with an entry waits twice its wait, up to the cap. -/
theorem backoff_double (max : Nat) (hub : Bool) (f : Tab) (now p u b : Nat) (h : get f p = some (u, b)) :
    (backoff max hub f now p).1 = min (satMul2 b) (capOf hub) := by
  simp [backoff, backWait, h]

/-- A wait never passes the cap of its peer. -/
theorem backoff_le_cap (max : Nat) (hub : Bool) (f : Tab) (now p : Nat) :
    (backoff max hub f now p).1 ≤ capOf hub := by
  unfold backoff backWait
  split
  · exact first_le_capOf hub
  · exact Nat.min_le_right _ _

/-- No wait is shorter than the first. -/
theorem first_le_backoff (max : Nat) (hub : Bool) (f : Tab) (now p : Nat)
    (hf : ∀ q u b, get f q = some (u, b) → first ≤ b) : first ≤ (backoff max hub f now p).1 := by
  unfold backoff backWait
  split
  · exact Nat.le_refl _
  · rename_i u b hg
    have := hf p u b hg
    unfold satMul2
    have := first_le_capOf hub
    simp only [Nat.le_min]
    constructor
    · have : first ≤ MAXU := by decide
      omega
    · exact this

theorem denyBack_first (max : Nat) (f : Tab) (now p : Nat) (h : get f p = none) :
    (denyBack max f now p).1 = denyFirst := by
  simp [denyBack, denyWait, h]

theorem denyBack_small (max : Nat) (f : Tab) (now p u b : Nat) (h : get f p = some (u, b)) (hb : b < denyFirst) :
    (denyBack max f now p).1 = denyFirst := by
  simp [denyBack, denyWait, h, Nat.not_le.mpr hb]

theorem denyBack_double (max : Nat) (f : Tab) (now p u b : Nat) (h : get f p = some (u, b)) (hb : denyFirst ≤ b) :
    (denyBack max f now p).1 = min (satMul2 b) denyCap := by
  simp [denyBack, denyWait, h, hb]

theorem denyBack_le (max : Nat) (f : Tab) (now p : Nat) :
    denyFirst ≤ (denyBack max f now p).1 ∧ (denyBack max f now p).1 ≤ denyCap := by
  unfold denyBack denyWait
  split
  · rename_i u b hg
    split
    · rename_i hb
      have h2 : denyFirst ≤ satMul2 b := by unfold satMul2; have : denyFirst ≤ MAXU := by decide
                                            omega
      exact ⟨Nat.le_min.mpr ⟨h2, denyFirst_le_denyCap⟩, Nat.min_le_right _ _⟩
    · exact ⟨Nat.le_refl _, denyFirst_le_denyCap⟩
  · exact ⟨Nat.le_refl _, denyFirst_le_denyCap⟩

/-! ## The waits from an empty table: the doubling and the cap -/

/-- `n` failed dials of one peer in a row, all at `now`, on a table of room for it. -/
def runBackoff (max : Nat) (hub : Bool) (now p : Nat) : Nat → Tab → Tab
  | 0, f => f
  | n + 1, f => runBackoff max hub now p n (backoff max hub f now p).2

theorem runBackoff_succ_right (max : Nat) (hub : Bool) (now p n : Nat) (f : Tab) :
    runBackoff max hub now p (n + 1) f = (backoff max hub (runBackoff max hub now p n f) now p).2 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [runBackoff] at ih ⊢; rw [ih]

/-- From an empty table with room, the wait after `k + 1` failed dials is `min (first * 2 ^ k)` of the cap. -/
theorem chain_wait (max : Nat) (hub : Bool) (now p : Nat) (hm : 1 ≤ max) (k : Nat) :
    (get (runBackoff max hub now p (k + 1) []) p).map (·.2) = some (min (first * 2 ^ k) (capOf hub)) := by
  induction k with
  | zero =>
    have h0 : (backoff max hub [] now p).1 = first := backoff_first _ _ _ _ _ (by simp [get])
    show (get (setFailed max [] now p (backWait hub [] p)) p).map (·.2) = _
    rw [setFailed_get]
    · simp [backWait, get]
      exact (Nat.min_eq_left (first_le_capOf hub)).symm
    · left; simp; omega
  | succ k ih =>
    rw [runBackoff_succ_right]
    generalize runBackoff max hub now p (k + 1) [] = t at ih ⊢
    obtain ⟨u, hu⟩ : ∃ u, get t p = some (u, min (first * 2 ^ k) (capOf hub)) := by
      cases hg : get t p with
      | none => simp [hg] at ih
      | some e =>
        obtain ⟨u, b⟩ := e
        refine ⟨u, ?_⟩
        simp [hg] at ih
        simp [ih]
    have hd := backoff_double max hub t now p u _ hu
    show (get (setFailed max t now p (backWait hub t p)) p).map (·.2) = _
    rw [setFailed_get]
    · simp only [backWait, hu, Option.map_some]
      have hc : capOf hub ≤ cap := capOf_le hub
      have hcm : capOf hub ≤ MAXU - 1 := by
        have : cap ≤ MAXU - 1 := by decide
        omega
      simp only [satMul2, Option.some.injEq]
      have hp : first * 2 ^ (k + 1) = 2 * (first * 2 ^ k) := by
        rw [Nat.pow_succ]; unfold first; generalize 2 ^ k = X; omega
      rw [hp]
      omega
    · right; simp [hu]

/-- A hub's waits from an empty table: 2, 4, 8, 16 s, and then 16 s again. -/
theorem chain_hub (max now p : Nat) (hm : 1 ≤ max) (k : Nat) :
    (get (runBackoff max true now p (k + 4) []) p).map (·.2) = some hubCap := by
  rw [chain_wait max true now p hm (k + 3)]
  simp only [capOf, ↓reduceIte]
  have : hubCap ≤ first * 2 ^ (k + 3) := by
    have h8 : 2 ^ (k + 3) ≥ 8 := by
      have : 2 ^ (k + 3) = 2 ^ k * 8 := by rw [Nat.pow_add]
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    unfold hubCap first
    omega
  simp [Nat.min_eq_right this]

/-! ## The window and the dial -/

theorem window_iff (f : Tab) (now p u b : Nat) (h : get f p = some (u, b)) : window f now p = true ↔ now < u := by
  simp [window, h]

theorem window_none (f : Tab) (now p : Nat) (h : get f p = none) : window f now p = false := by
  simp [window, h]

/-- A dial passes the guard only outside the backoff window. -/
theorem gate_no_window (f : Tab) (now p : Nat) (conn c rev : List Nat) (lv : Bool)
    (h : gate f now p conn c rev lv = true) : window f now p = false ∧ lv = false ∧ p ∉ conn ∧ p ∉ c ∧ p ∉ rev := by
  simp [gate] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h5, h1, h2, h3, h4⟩

/-- A peer inside its window is not dialed. -/
theorem window_no_gate (f : Tab) (now p : Nat) (conn c rev : List Nat) (lv : Bool)
    (h : window f now p = true) : gate f now p conn c rev lv = false := by
  simp [gate, h]

/-- The guard is open exactly when none of its reasons to refuse holds. -/
theorem gate_iff (f : Tab) (now p : Nat) (conn c rev : List Nat) (lv : Bool) :
    gate f now p conn c rev lv = true ↔
      (lv = false ∧ p ∉ conn ∧ p ∉ c ∧ p ∉ rev ∧ window f now p = false) := by
  simp [gate, and_assoc]

/-- After a failed dial that was stored, the peer is in its window at every time before the wait is over. -/
theorem window_after_backoff (max : Nat) (hub : Bool) (f : Tab) (now p t : Nat)
    (hs : f.length < max ∨ (get f p).isSome = true) (ht : t < satAdd now (backoff max hub f now p).1) :
    window (backoff max hub f now p).2 t p = true := by
  have hg := setFailed_get max f now p (backWait hub f p) hs
  have e : (backoff max hub f now p).2 = setFailed max f now p (backWait hub f p) := rfl
  have e1 : (backoff max hub f now p).1 = backWait hub f p := rfl
  rw [e1] at ht
  rw [e, window_iff _ _ _ _ _ hg]
  exact ht

/-- And outside it from the time on. -/
theorem no_window_after (max : Nat) (hub : Bool) (f : Tab) (now p t : Nat)
    (hs : f.length < max ∨ (get f p).isSome = true) (ht : satAdd now (backoff max hub f now p).1 ≤ t) :
    window (backoff max hub f now p).2 t p = false := by
  have hg := setFailed_get max f now p (backWait hub f p) hs
  have e : (backoff max hub f now p).2 = setFailed max f now p (backWait hub f p) := rfl
  have e1 : (backoff max hub f now p).1 = backWait hub f p := rfl
  rw [e1] at ht
  rw [e]
  have hw := window_iff _ t p _ _ hg
  by_cases hh : window (setFailed max f now p (backWait hub f p)) t p = true
  · have := hw.mp hh
    omega
  · simpa using hh

/-- After a dial whose session the full session table shed (`hub_connected` calls `backoff`), stored because the
table had room or an entry for the peer, the peer is not dialed at any time before the wait is over: a shed hub is
not redialed at every duty pass. -/
theorem shed_waits (max : Nat) (hub : Bool) (f : Tab) (now p t : Nat) (conn c rev : List Nat) (lv : Bool)
    (hs : f.length < max ∨ (get f p).isSome = true) (ht : t < satAdd now (backoff max hub f now p).1) :
    gate (backoff max hub f now p).2 t p conn c rev lv = false :=
  window_no_gate _ _ _ _ _ _ _ (window_after_backoff max hub f now p t hs ht)

/-- And the shed ended the dial in progress, so from the end of the wait on the peer is dialed when nothing else
refuses: no session, not revoked, the node not leaving. -/
theorem shed_redials (max : Nat) (hub : Bool) (f : Tab) (now p t : Nat) (conn c rev : List Nat)
    (hs : f.length < max ∨ (get f p).isSome = true) (hc : c.Nodup)
    (ht : satAdd now (backoff max hub f now p).1 ≤ t) (hconn : p ∉ conn) (hrev : p ∉ rev) :
    gate (backoff max hub f now p).2 t p conn (c.erase p) rev false = true := by
  rw [gate_iff]
  refine ⟨rfl, hconn, ?_, hrev, no_window_after max hub f now p t hs ht⟩
  rw [List.Nodup.mem_erase_iff hc]
  simp

/-- The time of an entry is never below its wait: no wraparound. -/
theorem until_ge_back (max : Nat) (f : Tab) (now p back : Nat) (hb : back ≤ MAXU) (u b : Nat)
    (h : get (setFailed max f now p back) p = some (u, b)) (hs : f.length < max ∨ (get f p).isSome = true) :
    b ≤ u := by
  rw [setFailed_get max f now p back hs] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1; subst h2
  exact satAdd_ge_right _ _ hb

/-! ## A closed session -/

theorem closed_length_le (max : Nat) (hub : Bool) (f : Tab) (now p opened : Nat) (den : Bool) (h : f.length ≤ max) :
    (closed max hub f now p opened den).2.length ≤ max := by
  unfold closed
  split
  · exact denyBack_length_le _ _ _ _ h
  · split
    · exact backoff_length_le _ _ _ _ _ h
    · exact Nat.le_trans (length_del_le _ _) h

/-- A session that lived at least `lived` forgets the entry of its peer and leaves the others. -/
theorem closed_long (max : Nat) (hub : Bool) (f : Tab) (now p opened : Nat) (hl : lived ≤ now - opened) :
    (closed max hub f now p opened false).1 = none ∧ get (closed max hub f now p opened false).2 p = none ∧
      ∀ q, q ≠ p → get (closed max hub f now p opened false).2 q = get f q := by
  have : ¬ now - opened < lived := by omega
  refine ⟨by simp [closed, this], ?_, ?_⟩
  · simp [closed, this, get_del_self]
  · intro q hq
    simp [closed, this]
    exact get_del_other _ _ _ hq

/-- A session that lived less is a failed dial. -/
theorem closed_short (max : Nat) (hub : Bool) (f : Tab) (now p opened : Nat) (hl : now - opened < lived) :
    closed max hub f now p opened false = (some (backoff max hub f now p).1, (backoff max hub f now p).2) := by
  simp [closed, hl]

/-- A refusal is `deny_back`. -/
theorem closed_den (max : Nat) (hub : Bool) (f : Tab) (now p opened : Nat) :
    closed max hub f now p opened true = (some (denyBack max f now p).1, (denyBack max f now p).2) := by
  simp [closed]

/-! ## The prune -/

theorem prune_mem (f : Tab) (now : Nat) (e : Nat × Nat × Nat) :
    e ∈ prune f now ↔ e ∈ f ∧ now < satAdd e.2.1 keep := by
  simp [prune]

theorem prune_length_le' (f : Tab) (now : Nat) (max : Nat) (h : f.length ≤ max) :
    (prune f now).length ≤ max := Nat.le_trans (length_prune_le _ _) h

theorem prune_keys_nodup (f : Tab) (now : Nat) (h : (keys f).Nodup) : (keys (prune f now)).Nodup :=
  keys_nodup_filter _ _ h

theorem get_none_of_not_mem (r : Tab) (p : Nat) (h : p ∉ keys r) : get r p = none := by
  induction r with
  | nil => rfl
  | cons e r ih =>
    obtain ⟨q, u, b⟩ := e
    simp only [keys, List.map_cons, List.mem_cons, not_or] at h
    have hq : ¬ q = p := fun hh => h.1 hh.symm
    simp [get, hq]
    exact ih (by simpa [keys] using h.2)

theorem get_filter (f : Tab) (g : Nat × Nat × Nat → Bool) (p : Nat) (hk : (keys f).Nodup) :
    get (f.filter g) p = match get f p with
      | some (u, b) => if g (p, u, b) = true then some (u, b) else none
      | none => none := by
  induction f with
  | nil => simp [get]
  | cons e r ih =>
    obtain ⟨q, u, b⟩ := e
    have hk' : (q ∉ keys r) ∧ (keys r).Nodup := by simpa [keys] using hk
    by_cases hq : q = p
    · subst hq
      have hn : get (r.filter g) q = none :=
        get_none_of_not_mem _ _ (fun hm => hk'.1 ((keys_filter r g).subset hm))
      by_cases hg : g (q, u, b) = true
      · simp [hg, get]
      · simp [hg, get, hn]
    · by_cases hg : g (q, u, b) = true
      · simp [hg, get, hq]
        exact ih hk'.2
      · simp [hg, get, hq]
        exact ih hk'.2

/-- An entry whose time plus `keep` has passed is gone; an entry still inside it stays. -/
theorem prune_get (f : Tab) (now p : Nat) (hk : (keys f).Nodup) :
    get (prune f now) p = match get f p with
      | some (u, b) => if now < satAdd u keep then some (u, b) else none
      | none => none := by
  unfold prune
  rw [get_filter f _ p hk]
  cases get f p with
  | none => rfl
  | some e => obtain ⟨u, b⟩ := e; simp

/-! ## The dials in progress -/

theorem connecting_length_le (max : Nat) (c : List Nat) (p : Nat) (h : c.length ≤ max) :
    (connecting max c p).length ≤ max := by
  unfold connecting
  split
  · rename_i hl
    split
    · exact h
    · simp; omega
  · exact h

theorem connecting_nodup (max : Nat) (c : List Nat) (p : Nat) (h : c.Nodup) : (connecting max c p).Nodup := by
  unfold connecting
  split
  · split
    · exact h
    · rename_i hn
      rw [List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb hab
      simp at hb
      subst hb; subst hab
      simp_all
  · exact h

theorem connecting_mem (max : Nat) (c : List Nat) (p q : Nat) (h : q ∈ connecting max c p) : q ∈ c ∨ q = p := by
  unfold connecting at h
  split at h
  · split at h
    · exact Or.inl h
    · simp at h
      exact h
  · exact Or.inl h

/-! ## The whole node: every table stays within its bound through any run of steps -/

/-- The tables of a node: the failed dials, the dials in progress, the peers with a session. -/
structure St where
  f : Tab
  c : List Nat
  conn : List Nat

/-- The state is well formed: both tables within `max`, one entry per peer, no peer both dialed and in a session. -/
structure Inv (max : Nat) (s : St) : Prop where
  f_le : s.f.length ≤ max
  f_nodup : (keys s.f).Nodup
  c_le : s.c.length ≤ max
  c_nodup : s.c.Nodup
  disjoint : ∀ p, p ∈ s.c → p ∉ s.conn

/-- One step of the node: a dial the guard lets through that reaches the transport or does not; a session that
comes up; a dial that fails or is refused; a dial whose session came up and that the full session table shed (the
session table is not in the state, so a shed may come for any peer); a session that closes; the prune. `hub` says
whether a peer is a hub, `rev` is the revoked set and `lv` whether the node is leaving. -/
inductive Step (max : Nat) (hub : Nat → Bool) (rev : List Nat) (lv : Bool) : St → St → Prop
  | dialOk (s : St) (now p : Nat) :
      gate s.f now p s.conn s.c rev lv = true →
      Step max hub rev lv s { s with c := connecting max s.c p }
  | dialErr (s : St) (now p : Nat) :
      gate s.f now p s.conn s.c rev lv = true →
      Step max hub rev lv s { s with f := (backoff max (hub p) s.f now p).2 }
  | connected (s : St) (p : Nat) :
      p ∉ s.conn →
      Step max hub rev lv s { s with c := s.c.erase p, conn := p :: s.conn }
  | failed (s : St) (now p : Nat) (den : Bool) :
      p ∈ s.c →
      Step max hub rev lv s
        { f := if den then (denyBack max s.f now p).2 else (backoff max (hub p) s.f now p).2
          c := s.c.erase p, conn := s.conn }
  | shed (s : St) (now p : Nat) :
      Step max hub rev lv s { s with f := (backoff max (hub p) s.f now p).2, c := s.c.erase p }
  | closes (s : St) (now p opened : Nat) (den : Bool) :
      p ∈ s.conn →
      Step max hub rev lv s { s with conn := s.conn.erase p, f := (closed max (hub p) s.f now p opened den).2 }
  | prunes (s : St) (now : Nat) :
      Step max hub rev lv s { s with f := prune s.f now }

theorem backoff_keys_nodup (max : Nat) (hub : Bool) (f : Tab) (now p : Nat) (h : (keys f).Nodup) :
    (keys (backoff max hub f now p).2).Nodup := setFailed_keys_nodup _ _ _ _ _ h

theorem denyBack_keys_nodup (max : Nat) (f : Tab) (now p : Nat) (h : (keys f).Nodup) :
    (keys (denyBack max f now p).2).Nodup := setFailed_keys_nodup _ _ _ _ _ h

theorem closed_keys_nodup (max : Nat) (hub : Bool) (f : Tab) (now p opened : Nat) (den : Bool)
    (h : (keys f).Nodup) : (keys (closed max hub f now p opened den).2).Nodup := by
  unfold closed
  split
  · exact denyBack_keys_nodup _ _ _ _ h
  · split
    · exact backoff_keys_nodup _ _ _ _ _ h
    · exact keys_nodup_filter _ _ h

theorem init_inv (max : Nat) : Inv max { f := [], c := [], conn := [] } :=
  ⟨by simp, by simp [keys], by simp, List.nodup_nil, by simp⟩

/-- Every step keeps the tables within their bound and well formed. -/
theorem step_inv {max : Nat} {hub : Nat → Bool} {rev : List Nat} {lv : Bool} {s s' : St}
    (hs : Inv max s) (st : Step max hub rev lv s s') : Inv max s' := by
  cases st with
  | dialOk now p hg =>
    obtain ⟨_, _, hpc, hpconn, _⟩ := (by simpa using gate_no_window _ _ _ _ _ _ _ hg :
      window s.f now p = false ∧ lv = false ∧ p ∉ s.conn ∧ p ∉ s.c ∧ p ∉ rev)
    refine ⟨hs.f_le, hs.f_nodup, connecting_length_le _ _ _ hs.c_le, connecting_nodup _ _ _ hs.c_nodup, ?_⟩
    intro q hq
    rcases connecting_mem _ _ _ _ hq with h | h
    · exact hs.disjoint q h
    · subst h; exact hpc
  | dialErr now p hg =>
    exact ⟨backoff_length_le _ _ _ _ _ hs.f_le, backoff_keys_nodup _ _ _ _ _ hs.f_nodup, hs.c_le, hs.c_nodup,
      hs.disjoint⟩
  | connected p hp =>
    refine ⟨hs.f_le, hs.f_nodup, Nat.le_trans (List.length_erase_le ..) hs.c_le, hs.c_nodup.erase _, ?_⟩
    intro q hq
    rw [List.Nodup.mem_erase_iff hs.c_nodup] at hq
    simp only [List.mem_cons, not_or]
    exact ⟨hq.1, hs.disjoint q hq.2⟩
  | failed now p den hp =>
    refine ⟨?_, ?_, Nat.le_trans (List.length_erase_le ..) hs.c_le, hs.c_nodup.erase _, ?_⟩
    · split
      · exact denyBack_length_le _ _ _ _ hs.f_le
      · exact backoff_length_le _ _ _ _ _ hs.f_le
    · split
      · exact denyBack_keys_nodup _ _ _ _ hs.f_nodup
      · exact backoff_keys_nodup _ _ _ _ _ hs.f_nodup
    · intro q hq
      exact hs.disjoint q ((List.erase_subset ..) hq)
  | shed now p =>
    refine ⟨backoff_length_le _ _ _ _ _ hs.f_le, backoff_keys_nodup _ _ _ _ _ hs.f_nodup,
      Nat.le_trans (List.length_erase_le ..) hs.c_le, hs.c_nodup.erase _, ?_⟩
    intro q hq
    exact hs.disjoint q ((List.erase_subset ..) hq)
  | closes now p opened den hp =>
    refine ⟨closed_length_le _ _ _ _ _ _ _ hs.f_le, closed_keys_nodup _ _ _ _ _ _ _ hs.f_nodup, hs.c_le, hs.c_nodup, ?_⟩
    intro q hq hm
    exact hs.disjoint q hq ((List.erase_subset ..) hm)
  | prunes now =>
    exact ⟨prune_length_le' _ _ _ hs.f_le, prune_keys_nodup _ _ hs.f_nodup, hs.c_le, hs.c_nodup, hs.disjoint⟩

/-- A run of steps from the empty node. -/
inductive Reach (max : Nat) (hub : Nat → Bool) (rev : List Nat) (lv : Bool) : St → Prop
  | start : Reach max hub rev lv { f := [], c := [], conn := [] }
  | step (s s' : St) : Reach max hub rev lv s → Step max hub rev lv s s' → Reach max hub rev lv s'

/-- Through any run of steps from the empty node, every table is within its bound. -/
theorem reach_inv {max : Nat} {hub : Nat → Bool} {rev : List Nat} {lv : Bool} {s : St}
    (h : Reach max hub rev lv s) : Inv max s := by
  induction h with
  | start => exact init_inv max
  | step s s' _ st ih => exact step_inv ih st

end Pinc.NodeBackoff

#audit_axioms Pinc.NodeBackoff.setFailed_length_le
#audit_axioms Pinc.NodeBackoff.setFailed_full
#audit_axioms Pinc.NodeBackoff.setFailed_get
#audit_axioms Pinc.NodeBackoff.setFailed_keeps
#audit_axioms Pinc.NodeBackoff.backoff_first
#audit_axioms Pinc.NodeBackoff.backoff_double
#audit_axioms Pinc.NodeBackoff.backoff_le_cap
#audit_axioms Pinc.NodeBackoff.denyBack_le
#audit_axioms Pinc.NodeBackoff.chain_wait
#audit_axioms Pinc.NodeBackoff.chain_hub
#audit_axioms Pinc.NodeBackoff.gate_no_window
#audit_axioms Pinc.NodeBackoff.window_no_gate
#audit_axioms Pinc.NodeBackoff.window_after_backoff
#audit_axioms Pinc.NodeBackoff.no_window_after
#audit_axioms Pinc.NodeBackoff.shed_waits
#audit_axioms Pinc.NodeBackoff.shed_redials
#audit_axioms Pinc.NodeBackoff.until_ge_back
#audit_axioms Pinc.NodeBackoff.closed_long
#audit_axioms Pinc.NodeBackoff.closed_short
#audit_axioms Pinc.NodeBackoff.prune_mem
#audit_axioms Pinc.NodeBackoff.prune_get
#audit_axioms Pinc.NodeBackoff.step_inv
#audit_axioms Pinc.NodeBackoff.reach_inv
