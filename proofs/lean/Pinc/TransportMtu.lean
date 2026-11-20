import Pinc.Axioms

/-!
# Path MTU discovery

A model of `pinc-transport` `conn/mtu.rs` (the `Mtu` state of one path), call for call as `proofs/tla/MtuOps.tla` has
it, over unbounded times (saturating at `u64::MAX`), and what it proves, for every run of calls:

- the datagram size is never below the floor (`Inv`, `inv_*`);
- a probe is due only when discovery started, nothing is in flight, no lost probe still waits, the path is allowed,
  and it is above the datagram size (`target_spec`);
- the datagram size rises only to the size of a probe the peer confirmed, and every rise names exactly the probe in
  flight or the one a flush took (`raise_spec`, `acked_rises`, `flushed_acked_rises`) and falls only by the black-hole
  fallback, to the floor, leaving nothing in flight, the path marked probed and the jumbo probe done, and a retry
  600 s away (`bhc_drop`, `bhc_keep`);
- an outcome applies only when it names exactly the probe in flight: an acknowledgement, a loss or a flush of another
  probe changes nothing (`acked_refuses`, `lost_refuses`, `flush_refuses`), a flush keeps the probe's size and packet
  number for its acknowledgement (`flush_keeps`), and a lost probe waits for a path event or 600 s (`lost_wait`,
  `event_reset`);
- a black-hole suspicion exists only above the floor (`Susp`, `susp_*`).

`Pinc.TraceMtu` replays the recorded calls of the real code through these functions.
-/

namespace Pinc.TransportMtu

def u64max : Nat := 2 ^ 64 - 1
def satAdd (a b : Nat) : Nat := min (a + b) u64max
def minMtu : Nat := 1200
def probeMtu : Nat := 1452
def jumboFloor : Nat := 2904
def jumboMtu : Nat := 8952
def reprobe : Nat := 600 * 1000000000

structure M where
  cur : Nat := minMtu
  infl : Option (Nat × Nat) := none
  flushed : Option (Nat × Nat) := none
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

def probeSent (m : M) (size pn : Nat) : M :=
  { m with infl := some (size, pn), flushed := none,
           probed := (size = probeMtu ∧ (!m.probed)) || m.probed,
           jdone := if size = probeMtu ∧ (!m.probed) then m.jdone else true }

/-- The probe in flight, if it is the one that came back or was lost by size, is no longer in flight. -/
def clearInfl (m : M) (size : Nat) : M :=
  if m.infl.map Prod.fst = some size then { m with infl := none } else m

/-- A probe of `size` was acknowledged or echoed: the state and the new datagram size if it rose. -/
def raise (m : M) (size : Nat) : M × Option Nat :=
  if m.cur < size then ({ clearInfl m size with cur := size }, some size) else (clearInfl m size, none)

/-- The probe of `size` sent as `pn` was acknowledged: the state, and `none` when the acknowledgement names
another probe than the one in flight (a refusal), otherwise the new datagram size if it rose. -/
def acked (m : M) (size pn : Nat) : M × Option (Option Nat) :=
  ((if m.infl = some (size, pn) then { m with infl := none, cur := max m.cur size } else m),
   if m.infl = some (size, pn) then some (if m.cur < size then some size else none) else none)

/-- The probe of `size` sent as `pn` was declared lost: the state and whether the loss applied. -/
def probeLost (m : M) (size pn now : Nat) : M × Bool :=
  ((if m.infl = some (size, pn) then
      { m with infl := none, retry := satAdd now reprobe, jdone := probeMtu < size || m.jdone }
    else m),
   if m.infl = some (size, pn) then true else false)

/-- A flush took the probe of `size` sent as `pn`: its size and packet number are kept for its acknowledgement, and
the probe is owed again at once. -/
def flush (m : M) (size pn : Nat) : M × Bool :=
  ((if m.infl = some (size, pn) then { m with infl := none, flushed := some (size, pn) } else m),
   if m.infl = some (size, pn) then true else false)

/-- The probe a flush took, sent as `pn`, was acknowledged after all: the state and the size if it rose. -/
def flushedAcked (m : M) (pn : Nat) : M × Option Nat :=
  match m.flushed with
  | some (size, marked) =>
      ((if marked = pn then { m with flushed := none, cur := max m.cur size } else m),
       if marked = pn ∧ m.cur < size then some size else none)
  | none => (m, none)

def event (m : M) : M := { m with probed := false, jdone := false, retry := 0 }

/-- The full-size packet sent before the last probe-timeout PING is not acknowledged. -/
def covered (backed : Option Nat) (big : Nat) : Bool := match backed with | some a => decide (big ≤ a) | none => false

def blackHole (m : M) (now rtt : Nat) : M :=
  match m.pbig with
  | none => m
  | some big =>
    if m.cur ≤ minMtu ∨ covered m.backed big = true then m
    else { m with susp := some (big, satAdd now rtt) }

/-- The suspicion settled: the state and whether the path dropped to the minimum size. The drop forgets the mark
of the probe a flush took: the path was condemned for carrying small packets only, and the stale acknowledgement
of its probe is no evidence against that. -/
def blackHoleCheck (m : M) (now : Nat) : M × Bool :=
  match m.susp with
  | none => (m, false)
  | some (big, at_) =>
    if covered m.backed big = true ∨ m.cur ≤ minMtu then ({ m with susp := none }, false)
    else if now < at_ then (m, false)
    else ({ m with susp := none, cur := minMtu, infl := none, flushed := none, lbig := none, pbig := none,
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

theorem inv_sent (m : M) (h : Inv m) (s pn : Nat) : Inv (probeSent m s pn) := by
  unfold probeSent
  split <;> exact ⟨h.floor, h.susp⟩

theorem inv_lost (m : M) (h : Inv m) (s pn now : Nat) : Inv (probeLost m s pn now).1 := by
  unfold probeLost
  by_cases hm : m.infl = some (s, pn)
  · rw [if_pos hm]; exact ⟨h.floor, h.susp⟩
  · rw [if_neg hm]; exact ⟨h.floor, h.susp⟩

theorem inv_raise (m : M) (h : Inv m) (s : Nat) : Inv (raise m s).1 := by
  obtain ⟨c1, c2, _⟩ := clearInfl_cur m s
  unfold raise
  by_cases hlt : m.cur < s
  · rw [if_pos hlt]
    refine ⟨?_, ?_⟩
    · have hf := h.floor
      show minMtu ≤ s
      omega
    · intro hh
      dsimp only at hh
      rw [c2] at hh
      have h9 := h.susp hh
      have hf := h.floor
      show minMtu < s
      omega
  · rw [if_neg hlt]
    refine ⟨?_, ?_⟩
    · show minMtu ≤ (clearInfl m s).cur
      rw [c1]
      exact h.floor
    · intro hh
      dsimp only at hh
      rw [c2] at hh
      have h9 := h.susp hh
      show minMtu < (clearInfl m s).cur
      rw [c1]
      exact h9

theorem inv_acked (m : M) (h : Inv m) (s pn : Nat) : Inv (acked m s pn).1 := by
  unfold acked
  by_cases hm : m.infl = some (s, pn)
  · rw [if_pos hm]
    refine ⟨by have hf := h.floor; show minMtu ≤ max m.cur s; omega, ?_⟩
    intro hh
    have h9 := h.susp hh
    have hf := h.floor
    show minMtu < max m.cur s
    omega
  · rw [if_neg hm]
    exact ⟨h.floor, h.susp⟩

theorem inv_flush (m : M) (h : Inv m) (s pn : Nat) : Inv (flush m s pn).1 := by
  unfold flush
  by_cases hm : m.infl = some (s, pn)
  · rw [if_pos hm]; exact ⟨h.floor, h.susp⟩
  · rw [if_neg hm]; exact ⟨h.floor, h.susp⟩

theorem inv_flushedAcked (m : M) (h : Inv m) (pn : Nat) : Inv (flushedAcked m pn).1 := by
  unfold flushedAcked
  cases hfl : m.flushed with
  | none => exact ⟨h.floor, h.susp⟩
  | some p =>
    obtain ⟨size, marked⟩ := p
    simp only [hfl]
    by_cases hmk : marked = pn
    · rw [if_pos hmk]
      refine ⟨by have hf := h.floor; show minMtu ≤ max m.cur size; omega, ?_⟩
      intro hh
      have h9 := h.susp hh
      have hf := h.floor
      show minMtu < max m.cur size
      omega
    · rw [if_neg hmk]
      exact ⟨h.floor, h.susp⟩

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

/-- An acknowledgement of the probe in flight rises to its size, and leaves nothing in flight. -/
theorem acked_rises (m : M) (size pn : Nat) (h : m.infl = some (size, pn)) (hlt : m.cur < size) :
    (acked m size pn).2 = some (some size) ∧ (acked m size pn).1.cur = size ∧ (acked m size pn).1.infl = none := by
  unfold acked
  rw [if_pos h, if_pos h, if_pos hlt]
  refine ⟨rfl, ?_, rfl⟩
  show max m.cur size = size
  omega

/-- An acknowledgement of the probe in flight that does not raise the size still takes it out of flight, and is no
refusal. -/
theorem acked_keeps (m : M) (size pn : Nat) (h : m.infl = some (size, pn)) (hlt : ¬ m.cur < size) :
    (acked m size pn).2 = some none ∧ (acked m size pn).1.cur = m.cur ∧ (acked m size pn).1.infl = none := by
  unfold acked
  rw [if_pos h, if_pos h, if_neg hlt]
  refine ⟨rfl, ?_, rfl⟩
  show max m.cur size = m.cur
  omega

/-- The probe a flush took rises on its acknowledgement, to the size the flush kept, and the mark is gone. -/
theorem flushed_acked_rises (m : M) (pn size : Nat) (h : m.flushed = some (size, pn)) (hlt : m.cur < size) :
    (flushedAcked m pn).2 = some size ∧ (flushedAcked m pn).1.cur = size ∧ (flushedAcked m pn).1.flushed = none := by
  unfold flushedAcked
  simp only [h]
  split
  · split
    · refine ⟨rfl, ?_, rfl⟩
      show max m.cur size = size
      omega
    · exfalso; simp_all
  · exfalso; simp_all

/-- A flush mark that names another probe than `pn` is not consumed. -/
theorem flushed_acked_refuses (m : M) (pn size marked : Nat) (h : m.flushed = some (size, marked)) (hne : marked ≠ pn) :
    (flushedAcked m pn).1 = m ∧ (flushedAcked m pn).2 = none := by
  unfold flushedAcked
  simp only [h]
  split
  · rename_i hc
    exact absurd hc hne
  · rename_i hc
    split
    · rename_i hc2
      exact absurd hc2.1 hc
    · exact ⟨rfl, rfl⟩

/-- With no flush mark, an acknowledgement of a flush's probe changes nothing. -/
theorem flushed_acked_none (m : M) (pn : Nat) (h : m.flushed = none) :
    (flushedAcked m pn).1 = m ∧ (flushedAcked m pn).2 = none := by
  simp [flushedAcked, h]

/-- An acknowledgement of another probe than the one in flight changes nothing: the refusal. -/
theorem acked_refuses (m : M) (size pn : Nat) (h : m.infl ≠ some (size, pn)) :
    (acked m size pn).1 = m ∧ (acked m size pn).2 = none := by
  unfold acked
  rw [if_neg h, if_neg h]
  exact ⟨rfl, rfl⟩



/-- The loss of another probe than the one in flight changes nothing. -/
theorem lost_refuses (m : M) (size pn now : Nat) (h : m.infl ≠ some (size, pn)) :
    (probeLost m size pn now).1 = m ∧ (probeLost m size pn now).2 = false := by
  unfold probeLost
  rw [if_neg h]
  exact ⟨rfl, by simp [h]⟩

/-- The flush of another probe than the one in flight changes nothing. -/
theorem flush_refuses (m : M) (size pn : Nat) (h : m.infl ≠ some (size, pn)) :
    (flush m size pn).1 = m ∧ (flush m size pn).2 = false := by
  unfold flush
  rw [if_neg h]
  exact ⟨rfl, by simp [h]⟩

/-- A flush keeps the probe's size and packet number, and leaves nothing in flight. -/
theorem flush_keeps (m : M) (size pn : Nat) (h : (flush m size pn).2 = true) :
    (flush m size pn).1.infl = none ∧ (flush m size pn).1.flushed = some (size, pn) ∧ m.infl = some (size, pn) := by
  unfold flush at h ⊢
  split at h
  · rename_i hc
    rw [if_pos hc]
    exact ⟨rfl, rfl, hc⟩
  · simp at h

theorem lost_wait (m : M) (size pn now : Nat) (h : (probeLost m size pn now).2 = true) :
    (probeLost m size pn now).1.retry = satAdd now reprobe := by
  unfold probeLost at h ⊢
  split at h
  · rename_i hc
    rw [if_pos hc]
  · simp at h

theorem event_reset (m : M) : (event m).retry = 0 ∧ (event m).probed = false ∧ (event m).jdone = false := ⟨rfl, rfl, rfl⟩

/-- The fallback drops the path to the minimum, leaves nothing in flight, forgets the mark of the probe a flush
took (the stale acknowledgement of it is no evidence against a path condemned for small packets), and marks the
probes done. -/
theorem bhc_drop (m : M) (now : Nat) (h : (blackHoleCheck m now).2 = true) :
    (blackHoleCheck m now).1.cur = minMtu ∧ (blackHoleCheck m now).1.infl = none ∧
      (blackHoleCheck m now).1.flushed = none ∧ (blackHoleCheck m now).1.probed = true ∧
      (blackHoleCheck m now).1.jdone = true ∧ (blackHoleCheck m now).1.susp = none ∧
      (blackHoleCheck m now).1.retry = satAdd now reprobe := by
  unfold blackHoleCheck at h ⊢
  split at h
  · simp at h
  · rename_i big at_ hs
    by_cases hc : covered m.backed big = true ∨ m.cur ≤ minMtu
    · rw [if_pos hc] at h; simp at h
    · by_cases hn : now < at_
      · rw [if_neg hc, if_pos hn] at h; simp at h
      · rw [if_neg hc, if_neg hn]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

end Pinc.TransportMtu
