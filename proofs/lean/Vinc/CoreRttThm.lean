import Vinc.Axioms
import Vinc.CoreRtt

/-!
# The node's round trips: what the code promises

What the model proves about `NodeRtt` (`rtt.rs`), for any table size, any number of peers and any run of calls; the
quotes are the module documentation:

- "at most `PEER_RTTS` peers, none replaced once the table is full": the table never holds more than `cap` peers, each
  once (`Inv`, `run_inv`); a known peer takes the value in place, a new peer is stored exactly when there is room and
  otherwise refused with the table unchanged, no other peer's value moves, and no entry is ever removed or moved
  (`insertRoom_ok`, `insertRoom_find`, `insertRoom_refused`, `insertRoom_other`, `step_keys`);
- `lrtt`, "an exponentially weighted mean with weight 7/8 on the old value": the first sample is taken as it is; then
  `8 * new` lies in `(7 * old + sample - 8, 7 * old + sample]` when that fits a `u64` and is `u64::MAX / 8` when it
  does not; never above the larger of the old average and the sample; positive after a sample; zero only before the
  first; moved only by a handshake sample (`handshake_lrtt_first`, `handshake_lrtt_exact`, `handshake_lrtt_sat`,
  `handshake_lrtt_le`, `handshake_lrtt_pos`, `lrtt_moves_only_on_handshake`, `lrtt_never_zero_again`);
- `tgr`, "after every sample it becomes `max(sample, tgr - tgr / 32)`": never below the sample, never below 31/32 of
  the old peak, one of the two, never above the larger of the old peak and the sample, zero only when both are, moved
  only by a peak (`peak_ge`, `peak_decay`, `peak_cases`, `peak_le`, `peak_zero_iff`, `tgr_moves_only_on_peak`); the
  module doc promises no order between the peak and the average and none holds (`peak_zero_avg_positive`);
- the handshake floor "rises after a dial times out, `min(8 s, max(500 ms, 2 x floor))`, and falls to zero only when a
  handshake answered at its first flight gives a sample: a new round trip peak of a session does not reset it": a
  timeout takes it to 500 ms from zero and doubles it up to 8 s (`timeout_from_zero`, `timeout_doubles`,
  `timeout_rises`); it is always zero, 500 ms, 1 s, 2 s, 4 s or 8 s (`Inv`); a handshake with a sample sets it to zero
  and a handshake with no sample changes nothing (`handshake_floor`, `handshake_zero`); a restored peer and a peak
  leave it alone (`restore_keeps`, `peak_keeps`); it falls only on a handshake sample (`floor_falls_only_on_handshake`,
  `floor_moves_only`). That the endpoint calls `note_handshake` only for a handshake with no resend is read off
  `events.rs`, not modelled;
- the readers: the first resend is at least 500 ms, at least twice the base round trip and at least the floor, and one
  of the three (`firstResend_ge`, `firstResend_cases`); a connection built from the remembered round trip computes
  the same first resend as the node, because the floor is even (`connFirst_remembered`); the hub resend exists
  exactly for a peer with a positive round trip of its own and is at least 300 ms (`hub_iff`, `hub_ge`); a node is
  thin exactly when its peak or its average is at least 250 ms, a session when it has no sample, the node is thin, or
  its smallest round trip or half its smoothed one is (`thinNode_iff`, `thin_iff`);
- what the connection reads: a new connection gets the node's values; a running one that is pushed them holds them
  afterwards, and its handshake is thin, so its connect limit is 60 s, exactly when the node is thin, provided what it
  held before is not a value the node has since lost, which the average and the peak never do
  (`connThin_pushOf`, `pushOf_rtt`, `view_step`, `connThin_connConfig`).
-/

namespace Vinc.CoreRtt

/-! ## The table -/

theorem keys_update (tab : List (Nat × Nat)) (p v : Nat) :
    keys (tab.map fun e => if e.1 == p then (p, v) else e) = keys tab := by
  unfold keys
  rw [List.map_map]
  apply List.map_congr_left
  intro e _
  by_cases h : (e.1 == p) = true <;> simp_all [Function.comp]

theorem any_iff_find (tab : List (Nat × Nat)) (p : Nat) :
    tab.any (fun e => e.1 == p) = (find? tab p).isSome := by
  induction tab with
  | nil => rfl
  | cons e t ih =>
    by_cases h : e.1 = p
    · simp [find?, h]
    · simp [find?, h, ih]

theorem find_update (tab : List (Nat × Nat)) (p v q : Nat) :
    find? (tab.map fun e => if e.1 == p then (p, v) else e) q =
      if q = p then (if (find? tab p).isSome then some v else none) else find? tab q := by
  induction tab with
  | nil => simp [find?]
  | cons e t ih =>
    simp only [beq_iff_eq] at ih ⊢
    by_cases hp : e.1 = p
    · by_cases hq : q = p
      · subst hq; simp [find?, hp]
      · have hq' : p ≠ q := fun h => hq h.symm
        simp [find?, hp, hq, hq']
        simpa [hq] using ih
    · by_cases hq : q = p
      · subst hq
        simp [find?, hp]
        simpa using ih
      · simp [find?, hp, hq]
        split
        · rfl
        · simpa [hq] using ih

theorem find_append_single (tab : List (Nat × Nat)) (p v q : Nat) :
    find? (tab ++ [(p, v)]) q = match find? tab q with
      | some x => some x
      | none => if q = p then some v else none := by
  induction tab with
  | nil =>
    by_cases h : q = p
    · subst h; simp [find?]
    · have h' : p ≠ q := fun x => h x.symm
      simp [find?, h, h']
  | cons e t ih =>
    by_cases h : e.1 = q
    · simp [find?, h]
    · simp [find?, h, ih]

theorem find_none_iff (tab : List (Nat × Nat)) (q : Nat) : find? tab q = none ↔ q ∉ keys tab := by
  induction tab with
  | nil => simp [find?, keys]
  | cons e t ih =>
    have ih' : find? t q = none ↔ q ∉ t.map (·.1) := by simpa [keys] using ih
    by_cases h : e.1 = q
    · subst h; simp [find?, keys]
    · have h' : q ≠ e.1 := fun x => h x.symm
      simp [find?, keys, h, h', ih']

/-- The three ways `insertRoom` goes. -/
theorem insertRoom_cases (cap : Nat) (tab : List (Nat × Nat)) (p v : Nat) :
    ((find? tab p).isSome = true ∧
        insertRoom cap tab p v = (true, tab.map fun e => if e.1 == p then (p, v) else e)) ∨
    ((find? tab p).isSome = false ∧ tab.length < cap ∧ insertRoom cap tab p v = (true, tab ++ [(p, v)])) ∨
    ((find? tab p).isSome = false ∧ ¬tab.length < cap ∧ insertRoom cap tab p v = (false, tab)) := by
  unfold insertRoom
  rw [any_iff_find]
  by_cases hk : (find? tab p).isSome = true
  · left; simp [hk]
  · have hk' : (find? tab p).isSome = false := by simpa using hk
    by_cases hl : tab.length < cap
    · right; left; simp [hk', hl]
    · right; right; simp [hk', hl]

/-- The peers after `insertRoom`: the same, or the same and the new one at the end. -/
theorem insertRoom_keys (cap : Nat) (tab : List (Nat × Nat)) (p v : Nat) :
    keys (insertRoom cap tab p v).2 = keys tab ∨ keys (insertRoom cap tab p v).2 = keys tab ++ [p] := by
  rcases insertRoom_cases cap tab p v with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]
  · left; exact keys_update tab p v
  · right; simp [keys]
  · left; rfl

/-- A peer is stored exactly when it is known or there is room. -/
theorem insertRoom_ok (cap : Nat) (tab : List (Nat × Nat)) (p v : Nat) :
    (insertRoom cap tab p v).1 = true ↔ (find? tab p).isSome = true ∨ tab.length < cap := by
  rcases insertRoom_cases cap tab p v with ⟨hk, h⟩ | ⟨hk, hl, h⟩ | ⟨hk, hl, h⟩ <;> rw [h]
  · simp [hk]
  · simp [hk, hl]
  · simp [hk, hl]

/-- A refused peer changes nothing. -/
theorem insertRoom_refused (cap : Nat) (tab : List (Nat × Nat)) (p v : Nat)
    (h : (insertRoom cap tab p v).1 = false) : (insertRoom cap tab p v).2 = tab := by
  rcases insertRoom_cases cap tab p v with ⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h ⊢ <;> simp_all

/-- A stored peer has its new value. -/
theorem insertRoom_find (cap : Nat) (tab : List (Nat × Nat)) (p v : Nat)
    (h : (insertRoom cap tab p v).1 = true) : find? (insertRoom cap tab p v).2 p = some v := by
  rcases insertRoom_cases cap tab p v with ⟨hk, h2⟩ | ⟨hk, hl, h2⟩ | ⟨hk, hl, h2⟩
  · rw [h2]; show find? _ p = _; rw [find_update]; simp [hk]
  · rw [h2]; show find? _ p = _
    rw [find_append_single]
    have : find? tab p = none := by simpa using hk
    simp [this]
  · rw [h2] at h; simp at h

/-- No other peer's value moves. -/
theorem insertRoom_other (cap : Nat) (tab : List (Nat × Nat)) (p v q : Nat) (hq : q ≠ p) :
    find? (insertRoom cap tab p v).2 q = find? tab q := by
  rcases insertRoom_cases cap tab p v with ⟨hk, h2⟩ | ⟨hk, hl, h2⟩ | ⟨hk, hl, h2⟩ <;> rw [h2]
  · show find? _ q = _; rw [find_update]; simp [hq]
  · show find? _ q = _
    rw [find_append_single]
    cases hf : find? tab q <;> simp [hq]

theorem insertRoom_length (cap : Nat) (tab : List (Nat × Nat)) (p v : Nat) :
    (insertRoom cap tab p v).2.length = tab.length ∨
      ((insertRoom cap tab p v).2.length = tab.length + 1 ∧ tab.length < cap) := by
  rcases insertRoom_cases cap tab p v with ⟨_, h⟩ | ⟨_, hl, h⟩ | ⟨_, _, h⟩ <;> rw [h]
  · left; simp
  · right; simp [hl]
  · left; rfl

theorem insertRoom_bound (cap : Nat) (tab : List (Nat × Nat)) (p v : Nat) (h : tab.length ≤ cap) :
    (insertRoom cap tab p v).2.length ≤ cap := by
  rcases insertRoom_length cap tab p v with h1 | ⟨h1, h2⟩ <;> omega

theorem insertRoom_nodup (cap : Nat) (tab : List (Nat × Nat)) (p v : Nat) (h : (keys tab).Nodup) :
    (keys (insertRoom cap tab p v).2).Nodup := by
  rcases insertRoom_cases cap tab p v with ⟨_, h2⟩ | ⟨hk, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2]
  · show (keys _).Nodup
    rw [keys_update]; exact h
  · show (keys (tab ++ [(p, v)])).Nodup
    have hp : p ∉ keys tab := by
      have : find? tab p = none := by simpa using hk
      exact (find_none_iff tab p).mp this
    have : keys (tab ++ [(p, v)]) = keys tab ++ [p] := by simp [keys]
    rw [this, List.nodup_append]
    refine ⟨h, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
    intro a ha b hb
    simp at hb
    subst hb
    intro hab; subst hab; exact hp ha
  · exact h

theorem insertRoom_vals (cap : Nat) (tab : List (Nat × Nat)) (p v M : Nat) (h : ∀ e ∈ tab, e.2 ≤ M) (hv : v ≤ M) :
    ∀ e ∈ (insertRoom cap tab p v).2, e.2 ≤ M := by
  rcases insertRoom_cases cap tab p v with ⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2]
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    by_cases hh : x.1 = p
    · simpa [hh] using hv
    · simpa [hh] using h x hx
  · intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact h e he
    · exact hv
  · exact h

/-! ## The average, the peak and the floor -/

/-- The six values the handshake floor takes. -/
def floorOk (f : Nat) : Prop :=
  f = 0 ∨ f = 500000000 ∨ f = 1000000000 ∨ f = 2000000000 ∨ f = 4000000000 ∨ f = 8000000000

/-- The node is well formed: the table is within its bound with each peer once and `u64` values, and the numbers
are `u64` with the floor one of its six values. -/
structure Inv (cap : Nat) (r : R) : Prop where
  len : r.tab.length ≤ cap
  nodup : (keys r.tab).Nodup
  vals : ∀ e ∈ r.tab, e.2 ≤ maxU
  lrtt : r.lrtt ≤ maxU
  tgr : r.tgr ≤ maxU
  floor : floorOk r.floor

/-- A call whose arguments are `u64`. -/
def Op.wf : Op → Prop
  | .hs _ v => v ≤ maxU
  | .restore _ v => v ≤ maxU
  | .peak v => v ≤ maxU
  | .timeout => True

theorem init_inv (cap : Nat) : Inv cap ({} : R) :=
  ⟨by simp, by simp [keys], by simp, by simp, by simp, Or.inl rfl⟩

/-- A handshake with no sample changes nothing. -/
theorem handshake_zero (cap p : Nat) (r : R) : handshake cap p 0 r = r := by simp [handshake]

/-- A handshake with a sample sets the floor to zero (and leaves the peak alone). -/
theorem handshake_floor (cap p v : Nat) (r : R) (hv : 0 < v) :
    (handshake cap p v r).floor = 0 ∧ (handshake cap p v r).tgr = r.tgr := by
  simp [handshake, Nat.pos_iff_ne_zero.mp hv]

/-- The first sample is the average. -/
theorem handshake_lrtt_first (cap p v : Nat) (r : R) (hv : 0 < v) (hl : r.lrtt = 0) :
    (handshake cap p v r).lrtt = v := by
  simp [handshake, Nat.pos_iff_ne_zero.mp hv, hl]

/-- When `7 * old + sample` fits a `u64`, the new average is its eighth, rounded down. -/
theorem handshake_lrtt_exact (cap p v : Nat) (r : R) (hv : 0 < v) (hl : r.lrtt ≠ 0)
    (hfit : 7 * r.lrtt + v ≤ maxU) :
    8 * (handshake cap p v r).lrtt ≤ 7 * r.lrtt + v ∧ 7 * r.lrtt + v < 8 * (handshake cap p v r).lrtt + 8 := by
  simp only [handshake, Nat.pos_iff_ne_zero.mp hv, hl, ite_false, satAdd, satMul]
  unfold maxU at *
  omega

/-- When it does not, the new average is the eighth of `u64::MAX`. -/
theorem handshake_lrtt_sat (cap p v : Nat) (r : R) (hv : 0 < v) (hl : r.lrtt ≠ 0)
    (hfit : maxU < 7 * r.lrtt + v) : (handshake cap p v r).lrtt = maxU / 8 := by
  simp only [handshake, Nat.pos_iff_ne_zero.mp hv, hl, ite_false, satAdd, satMul]
  unfold maxU at *
  omega

/-- The new average is never above the larger of the old one and the sample. -/
theorem handshake_lrtt_le (cap p v : Nat) (r : R) (hv : 0 < v) :
    (handshake cap p v r).lrtt ≤ max r.lrtt v := by
  by_cases hl : r.lrtt = 0
  · simp [handshake, Nat.pos_iff_ne_zero.mp hv, hl]
  · simp only [handshake, Nat.pos_iff_ne_zero.mp hv, hl, ite_false, satAdd, satMul]
    omega

/-- After a sample the average is positive. -/
theorem handshake_lrtt_pos (cap p v : Nat) (r : R) (hv : 0 < v) : 0 < (handshake cap p v r).lrtt := by
  by_cases hl : r.lrtt = 0
  · simp [handshake, Nat.pos_iff_ne_zero.mp hv, hl, hv]
  · simp only [handshake, Nat.pos_iff_ne_zero.mp hv, hl, ite_false, satAdd, satMul]
    unfold maxU
    omega

/-- A restored peer touches the table only, and is stored exactly when it is known or there is room. -/
theorem restore_keeps (cap p v : Nat) (r : R) :
    (restore cap p v r).2.lrtt = r.lrtt ∧ (restore cap p v r).2.tgr = r.tgr ∧ (restore cap p v r).2.floor = r.floor := by
  simp [restore]

theorem restore_ok (cap p v : Nat) (r : R) :
    (restore cap p v r).1 = true ↔ (krtt r p).isSome = true ∨ r.tab.length < cap :=
  insertRoom_ok cap r.tab p v

/-- A peak leaves the table, the average and the floor alone. -/
theorem peak_keeps (pk : Nat) (r : R) :
    (peak pk r).tab = r.tab ∧ (peak pk r).lrtt = r.lrtt ∧ (peak pk r).floor = r.floor := by
  simp [peak]

theorem peak_ge (pk : Nat) (r : R) : pk ≤ (peak pk r).tgr := by
  simp only [peak]; omega

theorem peak_decay (pk : Nat) (r : R) : 31 * r.tgr ≤ 32 * (peak pk r).tgr := by
  simp only [peak]; omega

theorem peak_cases (pk : Nat) (r : R) :
    (peak pk r).tgr = pk ∨ (peak pk r).tgr = r.tgr - r.tgr / 32 := by
  simp only [peak]; omega

theorem peak_le (pk : Nat) (r : R) : (peak pk r).tgr ≤ max r.tgr pk := by
  simp only [peak]; omega

theorem peak_zero_iff (pk : Nat) (r : R) : (peak pk r).tgr = 0 ↔ r.tgr = 0 ∧ pk = 0 := by
  simp only [peak]; omega

/-- No order holds between the peak and the average: a peak of zero beside a positive average is reachable. -/
theorem peak_zero_avg_positive :
    (handshake 4 1 1000 ({} : R)).tgr = 0 ∧ (handshake 4 1 1000 ({} : R)).lrtt = 1000 := by
  simp [handshake]

/-- A timeout leaves the table, the average and the peak alone. -/
theorem timeout_keeps (r : R) :
    (timeout r).tab = r.tab ∧ (timeout r).lrtt = r.lrtt ∧ (timeout r).tgr = r.tgr := by
  simp [timeout]

theorem timeout_from_zero (r : R) (h : r.floor = 0) : (timeout r).floor = firstResendMin := by
  simp only [timeout, h, satMul, firstResendMin, floorMax, maxU]
  omega

theorem timeout_doubles (r : R) (h1 : firstResendMin ≤ r.floor) (h2 : r.floor ≤ floorMax) :
    (timeout r).floor = min floorMax (2 * r.floor) := by
  simp only [timeout, satMul, firstResendMin, floorMax, maxU] at *
  omega

theorem timeout_rises (r : R) (h : r.floor < floorMax) : r.floor < (timeout r).floor := by
  simp only [timeout, satMul, firstResendMin, floorMax, maxU] at *
  omega

theorem timeout_bounds (r : R) : firstResendMin ≤ (timeout r).floor ∧ (timeout r).floor ≤ floorMax := by
  simp only [timeout, satMul, firstResendMin, floorMax, maxU]
  omega

theorem timeout_floorOk (r : R) (h : floorOk r.floor) : floorOk (timeout r).floor := by
  unfold floorOk at *
  simp only [timeout, satMul, firstResendMin, floorMax, maxU]
  omega

/-! ## Every call -/

/-- What a call does to the table is `insertRoom`'s or nothing. -/
theorem step_keys (cap : Nat) (r : R) (op : Op) :
    ∃ l, keys (step cap r op).tab = keys r.tab ++ l ∧ l.length ≤ 1 := by
  cases op with
  | hs p v =>
    by_cases hv : v = 0
    · exact ⟨[], by simp [step, handshake, hv], by simp⟩
    · rcases insertRoom_keys cap r.tab p v with h | h
      · exact ⟨[], by simpa [step, handshake, hv] using h, by simp⟩
      · exact ⟨[p], by simpa [step, handshake, hv] using h, by simp⟩
  | restore p v =>
    rcases insertRoom_keys cap r.tab p v with h | h
    · exact ⟨[], by simpa [step, restore] using h, by simp⟩
    · exact ⟨[p], by simpa [step, restore] using h, by simp⟩
  | peak v => exact ⟨[], by simp [step, peak], by simp⟩
  | timeout => exact ⟨[], by simp [step, timeout], by simp⟩

/-- The average moves only on a handshake with a sample. -/
theorem lrtt_moves_only_on_handshake (cap : Nat) (r : R) (op : Op) (h : (step cap r op).lrtt ≠ r.lrtt) :
    ∃ p v, op = .hs p v ∧ 0 < v := by
  cases op with
  | hs p v =>
    by_cases hv : v = 0
    · simp [step, handshake, hv] at h
    · exact ⟨p, v, rfl, Nat.pos_of_ne_zero hv⟩
  | restore p v => simp [step, restore] at h
  | peak v => simp [step, peak] at h
  | timeout => simp [step, timeout] at h

/-- The peak moves only on a peak. -/
theorem tgr_moves_only_on_peak (cap : Nat) (r : R) (op : Op) (h : (step cap r op).tgr ≠ r.tgr) :
    ∃ v, op = .peak v := by
  cases op with
  | hs p v =>
    by_cases hv : v = 0 <;> simp [step, handshake, hv] at h
  | restore p v => simp [step, restore] at h
  | peak v => exact ⟨v, rfl⟩
  | timeout => simp [step, timeout] at h

/-- The floor moves only on a handshake with a sample or a timeout. -/
theorem floor_moves_only (cap : Nat) (r : R) (op : Op) (h : (step cap r op).floor ≠ r.floor) :
    (∃ p v, op = .hs p v ∧ 0 < v) ∨ op = .timeout := by
  cases op with
  | hs p v =>
    by_cases hv : v = 0
    · simp [step, handshake, hv] at h
    · exact Or.inl ⟨p, v, rfl, Nat.pos_of_ne_zero hv⟩
  | restore p v => simp [step, restore] at h
  | peak v => simp [step, peak] at h
  | timeout => exact Or.inr rfl

/-- The floor falls only on a handshake with a sample, and then to zero: not on a restored peer, not on a peak, and
a timeout only raises it (up to the ceiling). -/
theorem floor_falls_only_on_handshake (cap : Nat) (r : R) (op : Op) (hf : r.floor ≤ floorMax)
    (h : (step cap r op).floor < r.floor) :
    ∃ p v, op = .hs p v ∧ 0 < v ∧ (step cap r op).floor = 0 := by
  cases op with
  | hs p v =>
    by_cases hv : v = 0
    · simp [step, handshake, hv] at h
    · exact ⟨p, v, rfl, Nat.pos_of_ne_zero hv, by simp [step, handshake, hv]⟩
  | restore p v => simp [step, restore] at h
  | peak v => simp [step, peak] at h
  | timeout =>
    exfalso
    simp only [step, timeout, satMul, firstResendMin, floorMax, maxU] at h hf
    omega

/-- An average that is positive stays positive. -/
theorem lrtt_never_zero_again (cap : Nat) (r : R) (op : Op) (h : r.lrtt ≠ 0) : (step cap r op).lrtt ≠ 0 := by
  cases op with
  | hs p v =>
    by_cases hv : v = 0
    · simp [step, handshake, hv, h]
    · have := handshake_lrtt_pos cap p v r (Nat.pos_of_ne_zero hv)
      simp only [step]; omega
  | restore p v => simpa [step, restore] using h
  | peak v => simpa [step, peak] using h
  | timeout => simpa [step, timeout] using h

/-- A peak that is positive stays positive. -/
theorem tgr_never_zero_again (cap : Nat) (r : R) (op : Op) (h : r.tgr ≠ 0) : (step cap r op).tgr ≠ 0 := by
  cases op with
  | hs p v =>
    by_cases hv : v = 0 <;> simpa [step, handshake, hv] using h
  | restore p v => simpa [step, restore] using h
  | peak v => simp only [step, peak]; omega
  | timeout => simpa [step, timeout] using h

/-- Every call keeps the node well formed. -/
theorem step_inv (cap : Nat) (r : R) (op : Op) (hI : Inv cap r) (hw : op.wf) : Inv cap (step cap r op) := by
  cases op with
  | hs p v =>
    by_cases hv : v = 0
    · simpa [step, handshake, hv] using hI
    · simp only [Op.wf] at hw
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [step, handshake, hv]; exact insertRoom_bound cap r.tab p v hI.len
      · simp only [step, handshake, hv]; exact insertRoom_nodup cap r.tab p v hI.nodup
      · simp only [step, handshake, hv]; exact insertRoom_vals cap r.tab p v maxU hI.vals hw
      · simp only [step, handshake, hv, ite_false]
        by_cases hl : r.lrtt = 0
        · simpa [hl] using hw
        · simp only [hl, ite_false, satAdd, satMul]; unfold maxU; omega
      · simpa [step, handshake, hv] using hI.tgr
      · simp [step, handshake, hv, floorOk]
  | restore p v =>
    simp only [Op.wf] at hw
    exact ⟨insertRoom_bound cap r.tab p v hI.len, insertRoom_nodup cap r.tab p v hI.nodup,
      insertRoom_vals cap r.tab p v maxU hI.vals hw, hI.lrtt, hI.tgr, hI.floor⟩
  | peak v =>
    simp only [Op.wf] at hw
    refine ⟨hI.len, hI.nodup, hI.vals, hI.lrtt, ?_, hI.floor⟩
    simp only [step, peak]; have := hI.tgr; omega
  | timeout =>
    exact ⟨hI.len, hI.nodup, hI.vals, hI.lrtt, hI.tgr, timeout_floorOk r hI.floor⟩

/-- The arguments of a run are `u64`. -/
def Wf : List Op → Prop
  | [] => True
  | op :: ops => op.wf ∧ Wf ops

/-- Over any run of calls from an empty node: the table stays within its bound, each peer once, and the floor stays
one of its six values. -/
theorem run_inv (cap : Nat) : ∀ (ops : List Op) (r : R), Inv cap r → Wf ops → Inv cap (run cap ops r)
  | [], _, hI, _ => hI
  | op :: ops, r, hI, ⟨hw, hws⟩ => run_inv cap ops _ (step_inv cap r op hI hw) hws

/-! ## The readers -/

theorem base_zero (r : R) (p : Nat) (h : base r p = 0) : r.lrtt = 0 := by
  unfold base at h
  cases hk : krtt r p with
  | none => simpa [hk] using h
  | some k =>
    by_cases hk0 : k = 0
    · simpa [hk, hk0] using h
    · simp [hk, hk0] at h

/-- The first resend is at least 500 ms, at least twice the base round trip and at least the floor, and one of them. -/
theorem firstResend_ge (r : R) (p : Nat) :
    firstResendMin ≤ firstResend r p ∧ satMul (base r p) 2 ≤ firstResend r p ∧ r.floor ≤ firstResend r p := by
  simp only [firstResend]; omega

theorem firstResend_cases (r : R) (p : Nat) :
    firstResend r p = firstResendMin ∨ firstResend r p = satMul (base r p) 2 ∨ firstResend r p = r.floor := by
  simp only [firstResend]; omega

theorem remembered_none_iff (r : R) (p : Nat) : remembered r p = none ↔ base r p = 0 ∧ r.floor = 0 := by
  simp only [remembered]
  split <;> simp_all <;> omega

theorem remembered_some (r : R) (p x : Nat) (h : remembered r p = some x) :
    base r p ≤ x ∧ r.floor ≤ 2 * x ∧ (x = base r p ∨ 2 * x ≤ r.floor + 1) := by
  simp only [remembered] at h
  split at h
  · simp at h; omega
  · simp at h

/-- The connection's own formula gives the node's first resend, because the floor is even. -/
theorem connFirst_remembered (r : R) (p : Nat) (hf : floorOk r.floor) :
    connFirst (remembered r p) (opt r.lrtt) = firstResend r p := by
  by_cases hn : remembered r p = none
  · obtain ⟨hb, hz⟩ := (remembered_none_iff r p).mp hn
    have hl := base_zero r p hb
    simp [connFirst, hn, opt, hl, firstResend, hb, hz, satMul]
  · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hn
    have hxe : x = max (base r p) ((r.floor + 1) / 2) := by
      unfold remembered at hx
      by_cases h0 : max (base r p) ((r.floor + 1) / 2) ≠ 0
      · simp [h0] at hx; exact hx.symm
      · simp [h0] at hx
    rw [hx]
    simp only [connFirst, Option.getD_some, firstResend, satMul]
    rw [hxe]
    unfold floorOk at hf
    rcases hf with h | h | h | h | h | h <;> (rw [h]; unfold maxU firstResendMin; omega)

theorem hub_iff (r : R) (p : Nat) : (hub r p).isSome = true ↔ ∃ k, krtt r p = some k ∧ k ≠ 0 := by
  unfold hub
  cases hk : krtt r p with
  | none => simp
  | some k => by_cases h : k = 0 <;> simp [h]

theorem hub_ge (r : R) (p h : Nat) (hh : hub r p = some h) :
    hubResendMin ≤ h ∧ ∀ k, krtt r p = some k → 3 * (k / 2) + hubPad ≤ maxU → 3 * (k / 2) + hubPad ≤ h := by
  unfold hub at hh
  cases hk : krtt r p with
  | none => simp [hk] at hh
  | some k =>
    by_cases h0 : k = 0
    · simp [hk, h0] at hh
    · simp [hk, h0] at hh
      subst hh
      refine ⟨by omega, ?_⟩
      intro k' hk' hfit
      have : k' = k := by simpa [hk] using hk'.symm
      subst this
      simp only [satAdd, satMul]
      omega

theorem thinNode_iff (r : R) : thinNode r = true ↔ slowRtt ≤ r.tgr ∨ slowRtt ≤ r.lrtt := by
  simp only [thinNode, decide_eq_true_eq]; omega

theorem thin_iff (r : R) (s m : Nat) :
    thin r s m = true ↔ s = 0 ∨ thinNode r = true ∨ slowRtt ≤ m ∨ slowRtt ≤ s / 2 := by
  simp only [thin, thinNode_iff, decide_eq_true_eq]; omega

/-- A node that is thin makes every session thin. -/
theorem thin_of_node (r : R) (s m : Nat) (h : thinNode r = true) : thin r s m = true :=
  (thin_iff r s m).mpr (Or.inr (Or.inl h))

/-! ## What the connection reads -/

/-- The connection holds no value the node has since lost: where the node has no average (peak), the connection
holds none. -/
def Synced (r : R) (cv : Cv) : Prop := (r.lrtt = 0 → cv.rtt = none) ∧ (r.tgr = 0 → cv.peak = none)

theorem synced_init : Synced ({} : R) ⟨false, none, none⟩ := ⟨fun _ => rfl, fun _ => rfl⟩

theorem synced_connConfig (r : R) : Synced r (connConfig r) :=
  ⟨fun h => by simp [connConfig, opt, h], fun h => by simp [connConfig, opt, h]⟩

/-- The node's calls never take a positive average or peak back to zero, so what a connection holds stays a
value the node has. -/
theorem synced_step (cap : Nat) (r : R) (cv : Cv) (op : Op) (h : Synced r cv) : Synced (step cap r op) cv :=
  ⟨fun h0 => h.1 (Classical.byContradiction fun hn => lrtt_never_zero_again cap r op hn h0),
   fun h0 => h.2 (Classical.byContradiction fun hn => tgr_never_zero_again cap r op hn h0)⟩

theorem synced_pushOf (r : R) (cv : Cv) (h : Synced r cv) : Synced r (pushOf cv r) :=
  ⟨fun h0 => by simp [pushOf, h0, h.1 h0], fun h0 => by simp [pushOf, h0, h.2 h0]⟩

theorem pushOf_rtt (r : R) (cv : Cv) (h : Synced r cv) : (pushOf cv r).rtt = opt r.lrtt := by
  by_cases h0 : r.lrtt = 0
  · simp [pushOf, opt, h0, h.1 h0]
  · simp [pushOf, opt, h0]

theorem pushOf_peak (r : R) (cv : Cv) (h : Synced r cv) : (pushOf cv r).peak = opt r.tgr := by
  by_cases h0 : r.tgr = 0
  · simp [pushOf, opt, h0, h.2 h0]
  · simp [pushOf, opt, h0]

/-- A connection pushed the node's values holds them, and its handshake is thin (its connect limit 60 s) exactly
when the node is. -/
theorem connThin_pushOf (r : R) (cv : Cv) (h : Synced r cv) : connThin (pushOf cv r) = thinNode r := by
  have h1 := pushOf_rtt r cv h
  have h2 := pushOf_peak r cv h
  apply Bool.eq_iff_iff.mpr
  simp only [connThin, decide_eq_true_eq, h1, h2]
  have e1 : (opt r.lrtt).getD 0 = r.lrtt := by by_cases h0 : r.lrtt = 0 <;> simp [opt, h0]
  have e2 : (opt r.tgr).getD 0 = r.tgr := by by_cases h0 : r.tgr = 0 <;> simp [opt, h0]
  simp only [e1, e2]
  have : (pushOf cv r).thin = thinNode r := rfl
  rw [this, thinNode_iff]
  omega

/-- A new connection built from the node's values is thin exactly when the node is. -/
theorem connThin_connConfig (r : R) : connThin (connConfig r) = thinNode r := by
  apply Bool.eq_iff_iff.mpr
  simp only [connThin, connConfig]
  have e1 : (opt r.lrtt).getD 0 = r.lrtt := by by_cases h0 : r.lrtt = 0 <;> simp [opt, h0]
  have e2 : (opt r.tgr).getD 0 = r.tgr := by by_cases h0 : r.tgr = 0 <;> simp [opt, h0]
  simp only [e1, e2, thinNode_iff]
  simp only [decide_eq_true_eq]
  omega

end Vinc.CoreRtt

#audit_axioms Vinc.CoreRtt.init_inv
#audit_axioms Vinc.CoreRtt.step_inv
#audit_axioms Vinc.CoreRtt.run_inv
#audit_axioms Vinc.CoreRtt.insertRoom_ok
#audit_axioms Vinc.CoreRtt.insertRoom_find
#audit_axioms Vinc.CoreRtt.insertRoom_refused
#audit_axioms Vinc.CoreRtt.insertRoom_other
#audit_axioms Vinc.CoreRtt.insertRoom_nodup
#audit_axioms Vinc.CoreRtt.insertRoom_bound
#audit_axioms Vinc.CoreRtt.insertRoom_vals
#audit_axioms Vinc.CoreRtt.insertRoom_keys
#audit_axioms Vinc.CoreRtt.step_keys
#audit_axioms Vinc.CoreRtt.handshake_zero
#audit_axioms Vinc.CoreRtt.handshake_floor
#audit_axioms Vinc.CoreRtt.handshake_lrtt_first
#audit_axioms Vinc.CoreRtt.handshake_lrtt_exact
#audit_axioms Vinc.CoreRtt.handshake_lrtt_sat
#audit_axioms Vinc.CoreRtt.handshake_lrtt_le
#audit_axioms Vinc.CoreRtt.handshake_lrtt_pos
#audit_axioms Vinc.CoreRtt.restore_keeps
#audit_axioms Vinc.CoreRtt.restore_ok
#audit_axioms Vinc.CoreRtt.peak_keeps
#audit_axioms Vinc.CoreRtt.peak_ge
#audit_axioms Vinc.CoreRtt.peak_decay
#audit_axioms Vinc.CoreRtt.peak_cases
#audit_axioms Vinc.CoreRtt.peak_le
#audit_axioms Vinc.CoreRtt.peak_zero_iff
#audit_axioms Vinc.CoreRtt.peak_zero_avg_positive
#audit_axioms Vinc.CoreRtt.timeout_keeps
#audit_axioms Vinc.CoreRtt.timeout_from_zero
#audit_axioms Vinc.CoreRtt.timeout_doubles
#audit_axioms Vinc.CoreRtt.timeout_rises
#audit_axioms Vinc.CoreRtt.timeout_bounds
#audit_axioms Vinc.CoreRtt.timeout_floorOk
#audit_axioms Vinc.CoreRtt.lrtt_moves_only_on_handshake
#audit_axioms Vinc.CoreRtt.tgr_moves_only_on_peak
#audit_axioms Vinc.CoreRtt.floor_moves_only
#audit_axioms Vinc.CoreRtt.floor_falls_only_on_handshake
#audit_axioms Vinc.CoreRtt.lrtt_never_zero_again
#audit_axioms Vinc.CoreRtt.tgr_never_zero_again
#audit_axioms Vinc.CoreRtt.firstResend_ge
#audit_axioms Vinc.CoreRtt.firstResend_cases
#audit_axioms Vinc.CoreRtt.remembered_none_iff
#audit_axioms Vinc.CoreRtt.remembered_some
#audit_axioms Vinc.CoreRtt.connFirst_remembered
#audit_axioms Vinc.CoreRtt.hub_iff
#audit_axioms Vinc.CoreRtt.hub_ge
#audit_axioms Vinc.CoreRtt.thinNode_iff
#audit_axioms Vinc.CoreRtt.thin_iff
#audit_axioms Vinc.CoreRtt.thin_of_node
#audit_axioms Vinc.CoreRtt.synced_init
#audit_axioms Vinc.CoreRtt.synced_connConfig
#audit_axioms Vinc.CoreRtt.synced_step
#audit_axioms Vinc.CoreRtt.synced_pushOf
#audit_axioms Vinc.CoreRtt.pushOf_rtt
#audit_axioms Vinc.CoreRtt.pushOf_peak
#audit_axioms Vinc.CoreRtt.connThin_pushOf
#audit_axioms Vinc.CoreRtt.connThin_connConfig
