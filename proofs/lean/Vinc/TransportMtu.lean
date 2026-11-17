import Vinc.Axioms

/-!
# Path MTU discovery

A model of `vinc-transport` `conn/mtu.rs` (the `Mtu` state of one path), call for call as `proofs/tla/MtuOps.tla` has
it, over unbounded times (saturating at `u64::MAX`), and what it proves, for every run of calls:

- the datagram size is never below the floor (`Inv`, `inv_*`);
- a probe is due only when discovery started, nothing is in flight, no lost probe still waits, the path is allowed,
  and it is above the datagram size (`target_spec`);
- the datagram size rises only to the size of the probe in flight that the peer confirmed (`raise_spec`,
  `raise_other`, `raise_old_probe`), by an echo only within the bound of the interface and the jumbo size (`echo_spec`,
  `echo_noinfl`, `echo_over_bound`, `echo_ceiling`), and falls only by the black-hole fallback, to the floor,
  leaving nothing in flight, the path marked probed and the jumbo probe done, and a retry 600 s away (`bhc_drop`,
  `bhc_keep`);
- the acknowledgement and the loss of a probe are applied only while that probe, named by its size and the packet
  number it left in, is the one in flight; any other probe changes nothing (`raise_other`, `lost_other`), among them the
  probe of a path that was replaced by a new path in its slot (`raise_old_probe`, `lost_old_probe`);
- a lost probe waits for a path event or 600 s (`lost_wait`, `event_reset`);
- a black-hole suspicion exists only above the floor (`Susp`, `susp_*`);
- the acknowledgement, the loss and the echo of a probe change the state of the path they name and of no other
  (`ack_other_path`, `lost_other_path`, `echo_other_path`, `ack_this_path`, `lost_this_path`).

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

/-- The largest size a probe or an echo may name: the smaller of the jumbo size and what the interface carries (its
payload, `interface_payload` in the code). -/
def ceiling (imtu : Nat) : Nat := min imtu jumboMtu

structure M where
  cur : Nat := minMtu
  infl : Option Nat := none
  /-- The identity of the probe in flight (the packet number it left in). -/
  ptok : Option Nat := none
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
  else if !m.jdone ∧ m.cur = probeMtu ∧ lowlat ∧ jumboFloor < ceiling imtu then some (ceiling imtu)
  else none

def probeSent (m : M) (size tok : Nat) : M :=
  if size = probeMtu ∧ !m.probed then { m with infl := some size, ptok := some tok, probed := true }
  else { m with infl := some size, ptok := some tok, jdone := true }

/-- The probe of this size and identity is the one in flight. -/
abbrev Holds (m : M) (size tok : Nat) : Prop := m.infl = some size ∧ m.ptok = some tok

instance (m : M) (size tok : Nat) : Decidable (Holds m size tok) := inferInstanceAs (Decidable (_ ∧ _))

/-- The probe of `size` and identity `tok` was acknowledged: the state and the new datagram size if it rose. Only the
probe in flight is taken: any other probe (a path that never sent it, a mark already cleared, a path that took the slot
of the one that sent it) changes nothing. -/
def raise (m : M) (size tok : Nat) : M × Option Nat :=
  if Holds m size tok then
    (if m.cur < size then ({ m with infl := none, ptok := none, cur := size }, some size)
     else ({ m with infl := none, ptok := none }, none))
  else (m, none)

/-- A peer echoed `size` on the path: taken only if it is the size of the probe in flight and no larger than `bound`. -/
def echo (m : M) (size bound : Nat) : M × Option Nat :=
  if m.infl = some size ∧ size ≤ bound then raise m size (m.ptok.getD 0) else (m, none)

/-- The probe of `size` and identity `tok` was lost; any other probe changes nothing. -/
def probeLost (m : M) (size tok now : Nat) : M :=
  if Holds m size tok then
    (if probeMtu < size then { m with infl := none, ptok := none, retry := satAdd now reprobe, jdone := true }
     else { m with infl := none, ptok := none, retry := satAdd now reprobe })
  else m

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
                   retry := satAdd now reprobe, probed := true, jdone := true, ptok := none }, true)

def start (m : M) : M := { m with started := true }
def setBig (m : M) (lb ba pb : Option Nat) : M := { m with lbig := lb, backed := ba, pbig := pb }

/-- The datagram size is at least the floor, and a suspicion exists only above it. -/
structure Inv (m : M) : Prop where
  floor : minMtu ≤ m.cur
  susp : m.susp.isSome = true → minMtu < m.cur

theorem inv_init : Inv ({} : M) := ⟨Nat.le_refl _, fun h => by simp at h⟩
theorem inv_start (m : M) (h : Inv m) : Inv (start m) := ⟨h.floor, h.susp⟩
theorem inv_setBig (m : M) (h : Inv m) (a b c : Option Nat) : Inv (setBig m a b c) := ⟨h.floor, h.susp⟩
theorem inv_event (m : M) (h : Inv m) : Inv (event m) := ⟨h.floor, h.susp⟩
theorem inv_sent (m : M) (h : Inv m) (s tok : Nat) : Inv (probeSent m s tok) := by
  unfold probeSent; split <;> exact ⟨h.floor, h.susp⟩

theorem inv_lost (m : M) (h : Inv m) (s tok now : Nat) : Inv (probeLost m s tok now) := by
  unfold probeLost
  by_cases hh : Holds m s tok
  · rw [if_pos hh]
    by_cases hp : probeMtu < s
    · rw [if_pos hp]; exact ⟨h.floor, h.susp⟩
    · rw [if_neg hp]; exact ⟨h.floor, h.susp⟩
  · rw [if_neg hh]; exact h

theorem inv_raise (m : M) (h : Inv m) (s tok : Nat) : Inv (raise m s tok).1 := by
  unfold raise
  by_cases hi : Holds m s tok
  · rw [if_pos hi]
    by_cases hlt : m.cur < s
    · rw [if_pos hlt]
      have := h.floor
      exact ⟨by show minMtu ≤ s; omega, fun _ => by show minMtu < s; omega⟩
    · rw [if_neg hlt]
      exact ⟨h.floor, h.susp⟩
  · rw [if_neg hi]; exact h

theorem inv_echo (m : M) (h : Inv m) (s b : Nat) : Inv (echo m s b).1 := by
  unfold echo
  by_cases hb : m.infl = some s ∧ s ≤ b
  · rw [if_pos hb]; exact inv_raise m h s _
  · rw [if_neg hb]; exact h

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
      by_cases hj : (!m.jdone) = true ∧ m.cur = probeMtu ∧ lowlat = true ∧ jumboFloor < ceiling imtu
      · rw [if_pos hj] at h
        simp at h
        obtain ⟨_, hcur, _, hfl⟩ := hj
        unfold probeMtu at hcur; unfold jumboFloor at hfl; omega
      · rw [if_neg hj] at h; simp at h

theorem raise_spec (m : M) (size tok : Nat) :
    (∀ n, (raise m size tok).2 = some n →
      n = size ∧ (raise m size tok).1.cur = size ∧ m.cur < size ∧ Holds m size tok) ∧
      ((raise m size tok).2 = none → (raise m size tok).1.cur = m.cur ∧ (Holds m size tok → size ≤ m.cur)) := by
  unfold raise
  by_cases hi : Holds m size tok
  · rw [if_pos hi]
    by_cases hlt : m.cur < size
    · rw [if_pos hlt]
      exact ⟨fun n hn => by simp at hn; exact ⟨hn.symm, rfl, hlt, hi⟩, fun hn => by simp at hn⟩
    · rw [if_neg hlt]
      exact ⟨fun n hn => by simp at hn, fun _ => ⟨rfl, fun _ => by omega⟩⟩
  · rw [if_neg hi]
    exact ⟨fun n hn => by simp at hn, fun _ => ⟨rfl, fun h => absurd h hi⟩⟩

/-- The acknowledgement of a probe that is not the one in flight changes nothing. -/
theorem raise_other (m : M) (size tok : Nat) (h : ¬ Holds m size tok) : raise m size tok = (m, none) := by
  unfold raise; rw [if_neg h]

/-- The acknowledgement of the probe in flight clears the mark. -/
theorem raise_clears (m : M) (size tok : Nat) (h : Holds m size tok) :
    (raise m size tok).1.infl = none ∧ (raise m size tok).1.ptok = none := by
  unfold raise
  rw [if_pos h]
  by_cases hlt : m.cur < size
  · rw [if_pos hlt]; exact ⟨rfl, rfl⟩
  · rw [if_neg hlt]; exact ⟨rfl, rfl⟩

theorem probeSent_holds (m : M) (size tok : Nat) : Holds (probeSent m size tok) size tok := by
  unfold probeSent; split <;> exact ⟨rfl, rfl⟩

/-- The acknowledgement of a probe that left before the probe now in flight (the path was replaced and the new path
sent a probe of the same size) changes nothing. -/
theorem raise_old_probe (m : M) (size tok tok' : Nat) (h : tok ≠ tok') :
    raise (probeSent m size tok') size tok = (probeSent m size tok', none) := by
  apply raise_other
  intro ⟨_, h2⟩
  have h3 := (probeSent_holds m size tok').2
  rw [h2] at h3
  exact h (Option.some.inj h3)

/-- An echo with no probe in flight, or of another size than the probe in flight, changes nothing. -/
theorem echo_noinfl (m : M) (size bound : Nat) (h : m.infl ≠ some size) : echo m size bound = (m, none) := by
  unfold echo
  rw [if_neg (fun hh => h hh.1)]

/-- An echo above the bound changes nothing, whatever is in flight. -/
theorem echo_over_bound (m : M) (size bound : Nat) (h : bound < size) : echo m size bound = (m, none) := by
  unfold echo
  rw [if_neg (fun hh => absurd hh.2 (by omega))]

/-- An echo is taken only for the size of the probe in flight, within the bound, and only if it is above the datagram
size. -/
theorem echo_spec (m : M) (size bound n : Nat) (h : (echo m size bound).2 = some n) :
    n = size ∧ size ≤ bound ∧ m.infl = some size ∧ m.cur < size := by
  unfold echo at h
  by_cases hb : m.infl = some size ∧ size ≤ bound
  · rw [if_pos hb] at h
    obtain ⟨hn, _, hlt, _⟩ := (raise_spec m size (m.ptok.getD 0)).1 n h
    exact ⟨hn, hb.2, hb.1, hlt⟩
  · rw [if_neg hb] at h; simp at h

/-- The echo of a path never takes it above what its interface carries or the jumbo size. -/
theorem echo_ceiling (m : M) (size imtu n : Nat) (h : (echo m size (ceiling imtu)).2 = some n) :
    n ≤ imtu ∧ n ≤ jumboMtu := by
  obtain ⟨hn, hb, _, _⟩ := echo_spec m size (ceiling imtu) n h
  unfold ceiling at hb
  omega

/-- The loss of the probe in flight makes the path wait. -/
theorem lost_wait (m : M) (size tok now : Nat) (h : Holds m size tok) :
    (probeLost m size tok now).retry = satAdd now reprobe ∧ (probeLost m size tok now).infl = none := by
  unfold probeLost
  rw [if_pos h]
  by_cases hp : probeMtu < size
  · rw [if_pos hp]; exact ⟨rfl, rfl⟩
  · rw [if_neg hp]; exact ⟨rfl, rfl⟩

/-- The loss of a probe that is not the one in flight changes nothing. -/
theorem lost_other (m : M) (size tok now : Nat) (h : ¬ Holds m size tok) : probeLost m size tok now = m := by
  unfold probeLost; rw [if_neg h]

/-- The loss of a probe that left before the probe now in flight (the path was replaced) changes nothing. -/
theorem lost_old_probe (m : M) (size tok tok' now : Nat) (h : tok ≠ tok') :
    probeLost (probeSent m size tok') size tok now = probeSent m size tok' := by
  apply lost_other
  intro ⟨_, h2⟩
  have h3 := (probeSent_holds m size tok').2
  rw [h2] at h3
  exact h (Option.some.inj h3)

theorem event_reset (m : M) : (event m).retry = 0 ∧ (event m).probed = false ∧ (event m).jdone = false := ⟨rfl, rfl, rfl⟩

theorem bhc_drop (m : M) (now : Nat) (h : (blackHoleCheck m now).2 = true) :
    (blackHoleCheck m now).1.cur = minMtu ∧ (blackHoleCheck m now).1.infl = none ∧
      (blackHoleCheck m now).1.probed = true ∧ (blackHoleCheck m now).1.jdone = true ∧
      (blackHoleCheck m now).1.susp = none ∧ (blackHoleCheck m now).1.retry = satAdd now reprobe ∧
      (blackHoleCheck m now).1.ptok = none := by
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

/-! ### Two paths

The state of the two paths of a connection (`Mtu.tla` has them as `ms`). A probe leaves on a path, and the
acknowledgement and the loss of it go to that path, whichever path is active when they arrive. -/

/-- The datagram size state of the two paths, indexed by a flag. -/
structure W where
  a : M := {}
  b : M := {}
  deriving BEq, Repr

def W.get (w : W) (i : Bool) : M := if i then w.b else w.a
def W.put (w : W) (i : Bool) (m : M) : W := if i then { w with b := m } else { w with a := m }

/-- The acknowledgement of a probe that left on path `p`: the state of the paths and the new size of path `p`. -/
def ackOn (w : W) (p : Bool) (size tok : Nat) : W × Option Nat :=
  let r := raise (w.get p) size tok
  (w.put p r.1, r.2)

/-- The loss of a probe that left on path `p`. -/
def lostOn (w : W) (p : Bool) (size tok now : Nat) : W := w.put p (probeLost (w.get p) size tok now)

/-- An echo that arrived on path `p`. -/
def echoOn (w : W) (p : Bool) (size bound : Nat) : W × Option Nat :=
  let r := echo (w.get p) size bound
  (w.put p r.1, r.2)

theorem ack_other_path (w : W) (p q : Bool) (size tok : Nat) (h : q ≠ p) : (ackOn w p size tok).1.get q = w.get q := by
  cases p <;> cases q <;> simp_all [ackOn, W.get, W.put]

theorem lost_other_path (w : W) (p q : Bool) (size tok now : Nat) (h : q ≠ p) :
    (lostOn w p size tok now).get q = w.get q := by
  cases p <;> cases q <;> simp_all [lostOn, W.get, W.put]

theorem echo_other_path (w : W) (p q : Bool) (size bound : Nat) (h : q ≠ p) : (echoOn w p size bound).1.get q = w.get q := by
  cases p <;> cases q <;> simp_all [echoOn, W.get, W.put]

theorem ack_this_path (w : W) (p : Bool) (size tok : Nat) : (ackOn w p size tok).1.get p = (raise (w.get p) size tok).1 := by
  cases p <;> simp [ackOn, W.get, W.put]

theorem lost_this_path (w : W) (p : Bool) (size tok now : Nat) :
    (lostOn w p size tok now).get p = probeLost (w.get p) size tok now := by
  cases p <;> simp [lostOn, W.get, W.put]

end Vinc.TransportMtu
