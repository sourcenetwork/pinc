import Vinc.Axioms

/-!
# Path MTU discovery

A model of `vinc-transport` `conn/mtu.rs` (the `Mtu` state of one path), call for call as `proofs/tla/MtuOps.tla` has
it, over unbounded times (saturating at `u64::MAX`), and what it proves, for every run of calls:

- the datagram size is never below the floor (`Inv`, `inv_*`);
- a probe is due only when discovery started, nothing is in flight, no lost probe still waits, the path is allowed,
  and it is above the datagram size (`target_spec`);
- the datagram size rises only to the size of a probe the peer confirmed (`raise_spec`) and falls only by the
  black-hole fallback, to the floor, leaving nothing in flight, the path marked probed and the jumbo probe done,
  and a retry 600 s away (`bhc_drop`, `bhc_keep`);
- a lost probe waits for a path event or 600 s (`lost_wait`, `event_reset`);
- a black-hole suspicion exists only above the floor (`Susp`, `susp_*`).

`Vinc.TraceMtu` replays the recorded calls of the real code through these functions.
-/

namespace Vinc.TransportMtu

def u64max : Nat := 2 ^ 64 - 1
def satAdd (a b : Nat) : Nat := min (a + b) u64max
def minMtu : Nat := 1200
def probeMtu : Nat := 1452
def jumboFloor : Nat := 2904
def jumboMtu : Nat := 8952
def reprobe : Nat := 600 * 1000000000

structure M where
  cur : Nat := minMtu
  infl : Option Nat := none
  probed : Bool := false
  jdone : Bool := false
  retry : Nat := 0
  started : Bool := false
  lbig : Option Nat := none
  backed : Option Nat := none
  pbig : Option Nat := none
  susp : Option (Nat × Nat) := none
  deriving BEq, Repr

/-- The next size to probe. -/
def target (m : M) (allowed : Bool) (imtu : Nat) (lowlat : Bool) (now : Nat) : Option Nat :=
  if !allowed || !m.started || m.infl.isSome || now < m.retry then none
  else if !m.probed then (if probeMtu ≤ imtu ∧ m.cur < probeMtu then some probeMtu else none)
  else if !m.jdone ∧ m.cur = probeMtu ∧ lowlat ∧ jumboFloor < min imtu jumboMtu then some (min imtu jumboMtu)
  else none

def probeSent (m : M) (size : Nat) : M :=
  if size = probeMtu ∧ !m.probed then { m with infl := some size, probed := true }
  else { m with infl := some size, jdone := true }

/-- The probe in flight, if it is the one that came back or was lost, is no longer in flight. -/
def clearInfl (m : M) (size : Nat) : M := if m.infl = some size then { m with infl := none } else m

/-- A probe of `size` was acknowledged or echoed: the state and the new datagram size if it rose. -/
def raise (m : M) (size : Nat) : M × Option Nat :=
  if m.cur < size then ({ clearInfl m size with cur := size }, some size) else (clearInfl m size, none)

def probeLost (m : M) (size now : Nat) : M :=
  if probeMtu < size then { clearInfl m size with retry := satAdd now reprobe, jdone := true }
  else { clearInfl m size with retry := satAdd now reprobe }

def event (m : M) : M := { m with probed := false, jdone := false, retry := 0 }

/-- The full-size packet sent before the last probe-timeout PING is not acknowledged. -/
def covered (backed : Option Nat) (big : Nat) : Bool := match backed with | some a => decide (big ≤ a) | none => false

def blackHole (m : M) (now rtt : Nat) : M :=
  match m.pbig with
  | none => m
  | some big =>
    if m.cur ≤ minMtu ∨ covered m.backed big = true then m
    else { m with susp := some (big, satAdd now rtt) }

/-- The suspicion settled: the state and whether the path dropped to the minimum size. -/
def blackHoleCheck (m : M) (now : Nat) : M × Bool :=
  match m.susp with
  | none => (m, false)
  | some (big, at_) =>
    if covered m.backed big = true ∨ m.cur ≤ minMtu then ({ m with susp := none }, false)
    else if now < at_ then (m, false)
    else ({ m with susp := none, cur := minMtu, infl := none, lbig := none, pbig := none,
                   retry := satAdd now reprobe, probed := true, jdone := true }, true)

def start (m : M) : M := { m with started := true }
def setBig (m : M) (lb ba pb : Option Nat) : M := { m with lbig := lb, backed := ba, pbig := pb }

theorem clearInfl_cur (m : M) (s : Nat) : (clearInfl m s).cur = m.cur ∧ (clearInfl m s).susp = m.susp ∧
    (clearInfl m s).retry = m.retry := by
  unfold clearInfl; split <;> exact ⟨rfl, rfl, rfl⟩

/-- The datagram size is at least the floor, and a suspicion exists only above it. -/
structure Inv (m : M) : Prop where
  floor : minMtu ≤ m.cur
  susp : m.susp.isSome = true → minMtu < m.cur

theorem inv_init : Inv ({} : M) := ⟨Nat.le_refl _, fun h => by simp at h⟩
theorem inv_start (m : M) (h : Inv m) : Inv (start m) := ⟨h.floor, h.susp⟩
theorem inv_setBig (m : M) (h : Inv m) (a b c : Option Nat) : Inv (setBig m a b c) := ⟨h.floor, h.susp⟩
theorem inv_event (m : M) (h : Inv m) : Inv (event m) := ⟨h.floor, h.susp⟩
theorem inv_sent (m : M) (h : Inv m) (s : Nat) : Inv (probeSent m s) := by
  unfold probeSent; split <;> exact ⟨h.floor, h.susp⟩

theorem inv_lost (m : M) (h : Inv m) (s now : Nat) : Inv (probeLost m s now) := by
  obtain ⟨c1, c2, _⟩ := clearInfl_cur m s
  unfold probeLost
  split
  · exact ⟨by show minMtu ≤ (clearInfl m s).cur; rw [c1]; exact h.floor,
      by show _ → minMtu < (clearInfl m s).cur; rw [c1, c2]; exact h.susp⟩
  · exact ⟨by show minMtu ≤ (clearInfl m s).cur; rw [c1]; exact h.floor,
      by show _ → minMtu < (clearInfl m s).cur; rw [c1, c2]; exact h.susp⟩

theorem inv_raise (m : M) (h : Inv m) (s : Nat) : Inv (raise m s).1 := by
  obtain ⟨c1, c2, _⟩ := clearInfl_cur m s
  unfold raise
  by_cases hlt : m.cur < s
  · rw [if_pos hlt]
    have := h.floor
    exact ⟨by show minMtu ≤ s; omega, fun _ => by show minMtu < s; omega⟩
  · rw [if_neg hlt]
    exact ⟨by show minMtu ≤ (clearInfl m s).cur; rw [c1]; exact h.floor,
      by show _ → minMtu < (clearInfl m s).cur; rw [c1, c2]; exact h.susp⟩

theorem inv_blackHole (m : M) (h : Inv m) (now rtt : Nat) : Inv (blackHole m now rtt) := by
  unfold blackHole
  split
  · exact h
  · rename_i big hb
    by_cases hc : m.cur ≤ minMtu ∨ covered m.backed big = true
    · rw [if_pos hc]; exact h
    · rw [if_neg hc]
      have : ¬ m.cur ≤ minMtu := fun a => hc (Or.inl a)
      exact ⟨h.floor, fun _ => by show minMtu < m.cur; omega⟩

theorem inv_bhc (m : M) (h : Inv m) (now : Nat) : Inv (blackHoleCheck m now).1 := by
  unfold blackHoleCheck
  split
  · exact h
  · rename_i big at_ hs
    by_cases hc : covered m.backed big = true ∨ m.cur ≤ minMtu
    · rw [if_pos hc]; exact ⟨h.floor, fun hh => by simp at hh⟩
    · rw [if_neg hc]
      by_cases hn : now < at_
      · rw [if_pos hn]; exact h
      · rw [if_neg hn]; exact ⟨Nat.le_refl _, fun hh => by simp at hh⟩

theorem target_spec (m : M) (allowed : Bool) (imtu : Nat) (lowlat : Bool) (now s : Nat)
    (h : target m allowed imtu lowlat now = some s) :
    allowed = true ∧ m.started = true ∧ m.infl = none ∧ m.retry ≤ now ∧ m.cur < s := by
  unfold target at h
  by_cases h0 : (!allowed || !m.started || m.infl.isSome || decide (now < m.retry)) = true
  · rw [if_pos h0] at h; simp at h
  · rw [if_neg h0] at h
    have ha : allowed = true := by cases hb : allowed <;> simp [hb] at h0 ⊢
    have hs : m.started = true := by cases hb : m.started <;> simp [hb, ha] at h0 ⊢
    have hi : m.infl = none := by cases hb : m.infl <;> simp [hb, ha, hs] at h0 ⊢
    have hn : m.retry ≤ now := by
      by_cases hh : now < m.retry
      · simp [hh, ha, hs, hi] at h0
      · omega
    refine ⟨ha, hs, hi, hn, ?_⟩
    by_cases hp : (!m.probed) = true
    · rw [if_pos hp] at h
      by_cases hc : probeMtu ≤ imtu ∧ m.cur < probeMtu
      · rw [if_pos hc] at h; simp at h; omega
      · rw [if_neg hc] at h; simp at h
    · rw [if_neg hp] at h
      by_cases hj : (!m.jdone) = true ∧ m.cur = probeMtu ∧ lowlat = true ∧ jumboFloor < min imtu jumboMtu
      · rw [if_pos hj] at h
        simp at h
        obtain ⟨_, hcur, _, hfl⟩ := hj
        unfold probeMtu at hcur; unfold jumboFloor at hfl; omega
      · rw [if_neg hj] at h; simp at h

theorem raise_spec (m : M) (size : Nat) :
    (∀ n, (raise m size).2 = some n → n = size ∧ (raise m size).1.cur = size ∧ m.cur < size) ∧
      ((raise m size).2 = none → (raise m size).1.cur = m.cur ∧ size ≤ m.cur) := by
  obtain ⟨c1, _, _⟩ := clearInfl_cur m size
  unfold raise
  by_cases hlt : m.cur < size
  · rw [if_pos hlt]
    exact ⟨fun n hn => by simp at hn; exact ⟨hn.symm, rfl, hlt⟩, fun hn => by simp at hn⟩
  · rw [if_neg hlt]
    exact ⟨fun n hn => by simp at hn, fun _ => ⟨c1, by omega⟩⟩

theorem lost_wait (m : M) (size now : Nat) : (probeLost m size now).retry = satAdd now reprobe := by
  unfold probeLost
  split <;> rfl

theorem event_reset (m : M) : (event m).retry = 0 ∧ (event m).probed = false ∧ (event m).jdone = false := ⟨rfl, rfl, rfl⟩

theorem bhc_drop (m : M) (now : Nat) (h : (blackHoleCheck m now).2 = true) :
    (blackHoleCheck m now).1.cur = minMtu ∧ (blackHoleCheck m now).1.infl = none ∧
      (blackHoleCheck m now).1.probed = true ∧ (blackHoleCheck m now).1.jdone = true ∧
      (blackHoleCheck m now).1.susp = none ∧ (blackHoleCheck m now).1.retry = satAdd now reprobe := by
  unfold blackHoleCheck at h ⊢
  split at h
  · simp at h
  · rename_i big at_ hs
    by_cases hc : covered m.backed big = true ∨ m.cur ≤ minMtu
    · rw [if_pos hc] at h; simp at h
    · by_cases hn : now < at_
      · rw [if_neg hc, if_pos hn] at h; simp at h
      · rw [if_neg hc, if_neg hn]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Without the fallback the datagram size does not change. -/
theorem bhc_keep (m : M) (now : Nat) (h : (blackHoleCheck m now).2 = false) : (blackHoleCheck m now).1.cur = m.cur := by
  unfold blackHoleCheck at h ⊢
  cases hsu : m.susp with
  | none => simp [hsu]
  | some p =>
    obtain ⟨big, at_⟩ := p
    by_cases hc : covered m.backed big = true ∨ m.cur ≤ minMtu
    · simp [hsu, hc]
    · by_cases hn : now < at_
      · simp [hsu, hc, hn]
      · simp [hsu, hc, hn] at h

end Vinc.TransportMtu
