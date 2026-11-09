import Vinc.TransportRecovery

/-!
# Loss recovery: the byte accounts

For recorded packets, bytes sent = bytes acknowledged + bytes in flight + bytes declared lost, always, with the
in-flight bytes and packets the sums over the slots in flight and the bytes of the ghosts counted in `lost`
(`Acct`). Every call of the engine (`send`, `ack`, `timeout`, `flush`) keeps it, for any ring size, any run of
calls and any times; the subtractions of the code (`in_flight -= size`, `lost -= size`, `in_flight_packets -= 1`)
never underflow because the sums bound them.
-/

namespace Vinc.TransportRecovery

def sumSt : List Slot → St → Nat
  | [], _ => 0
  | s :: t, st => (if s.st = st then s.size else 0) + sumSt t st

def cntSt : List Slot → St → Nat
  | [], _ => 0
  | s :: t, st => (if s.st = st then 1 else 0) + cntSt t st

/-- The accounts of a state: sent = acked + in flight + lost, and the in-flight counters are the sums over the ring. -/
def Acct (r : R) : Prop :=
  r.sent = r.acked + r.inf + r.lost ∧ r.inf = sumSt r.ring .fl ∧ r.infp = cntSt r.ring .fl ∧ sumSt r.ring .lost ≤ r.lost

theorem sumSt_upd (f : Slot → Slot) (st : St) :
    ∀ (l : List Slot) (i : Nat) (s0 : Slot), l[i]? = some s0 → (f s0).size = s0.size →
      sumSt (upd l i f) st + (if s0.st = st then s0.size else 0) = sumSt l st + (if (f s0).st = st then s0.size else 0)
  | [], i, s0, h, _ => by simp at h
  | x :: xs, 0, s0, h, hs => by
    simp at h
    subst h
    simp [upd, sumSt, hs]
    omega
  | x :: xs, i + 1, s0, h, hs => by
    simp at h
    have := sumSt_upd f st xs i s0 h hs
    simp [upd, sumSt]
    omega

theorem cntSt_upd (f : Slot → Slot) (st : St) :
    ∀ (l : List Slot) (i : Nat) (s0 : Slot), l[i]? = some s0 →
      cntSt (upd l i f) st + (if s0.st = st then 1 else 0) = cntSt l st + (if (f s0).st = st then 1 else 0)
  | [], i, s0, h => by simp at h
  | x :: xs, 0, s0, h => by
    simp at h
    subst h
    simp [upd, cntSt]
    omega
  | x :: xs, i + 1, s0, h => by
    simp at h
    have := cntSt_upd f st xs i s0 h
    simp [upd, cntSt]
    omega

theorem sumSt_le_of_get (st : St) : ∀ (l : List Slot) (i : Nat) (s0 : Slot), l[i]? = some s0 → s0.st = st →
    s0.size ≤ sumSt l st
  | [], i, s0, h, _ => by simp at h
  | x :: xs, 0, s0, h, hs => by
    simp at h
    subst h
    simp [sumSt, hs]
  | x :: xs, i + 1, s0, h, hs => by
    simp at h
    have := sumSt_le_of_get st xs i s0 h hs
    simp [sumSt]
    omega

theorem sumSt_append (a b : List Slot) (st : St) : sumSt (a ++ b) st = sumSt a st + sumSt b st := by
  induction a with
  | nil => simp [sumSt]
  | cons x xs ih => simp [sumSt, ih]; omega

theorem cntSt_append (a b : List Slot) (st : St) : cntSt (a ++ b) st = cntSt a st + cntSt b st := by
  induction a with
  | nil => simp [cntSt]
  | cons x xs ih => simp [cntSt, ih]; omega

/-- A slot in flight leaves the in-flight set to state 1 or 2 and its bytes move from in flight to lost. -/
theorem acct_move (r : R) (i : Nat) (sl : Slot) (h : r.ring[i]? = some sl) (hst : sl.st = .fl) (f : Slot → Slot)
    (hf : ∀ s, (f s).size = s.size) (hf1 : (f sl).st = .lost ∨ (f sl).st = .done) (late : List (Nat × Nat)) (a : Acct r) :
    Acct { r with ring := upd r.ring i f, inf := r.inf - sl.size, lost := r.lost + sl.size, infp := r.infp - 1,
                  late := late } := by
  obtain ⟨h1, h2, h3, h4⟩ := a
  have e0 := sumSt_upd f .fl r.ring i sl h (hf sl)
  have e1 := sumSt_upd f .lost r.ring i sl h (hf sl)
  have c0 := cntSt_upd f .fl r.ring i sl h
  rcases hf1 with h5 | h5 <;> simp [hst, h5] at e0 e1 c0 <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> omega

/-- A slot in flight is acknowledged: its bytes move from in flight to acknowledged. -/
theorem acct_ack (r : R) (i : Nat) (sl : Slot) (h : r.ring[i]? = some sl) (hst : sl.st = .fl) (f : Slot → Slot)
    (hf : ∀ s, (f s).size = s.size) (hf1 : (f sl).st = .done) (a : Acct r) :
    Acct { r with ring := upd r.ring i f, inf := r.inf - sl.size, acked := r.acked + sl.size, infp := r.infp - 1 } := by
  obtain ⟨h1, h2, h3, h4⟩ := a
  have e0 := sumSt_upd f .fl r.ring i sl h (hf sl)
  have e1 := sumSt_upd f .lost r.ring i sl h (hf sl)
  have c0 := cntSt_upd f .fl r.ring i sl h
  simp [hst, hf1] at e0 e1 c0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> omega

/-- A ghost is acknowledged late: its bytes move from lost to acknowledged. -/
theorem acct_late (r : R) (i : Nat) (sl : Slot) (h : r.ring[i]? = some sl) (hst : sl.st = .lost) (f : Slot → Slot)
    (hf : ∀ s, (f s).size = s.size) (hf1 : (f sl).st = .done) (a : Acct r) :
    Acct { r with ring := upd r.ring i f, lost := r.lost - sl.size, acked := r.acked + sl.size } := by
  obtain ⟨h1, h2, h3, h4⟩ := a
  have e0 := sumSt_upd f .fl r.ring i sl h (hf sl)
  have e1 := sumSt_upd f .lost r.ring i sl h (hf sl)
  have c0 := cntSt_upd f .fl r.ring i sl h
  simp [hst, hf1] at e0 e1 c0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> omega

/-- An expired ghost is forgotten: no counter moves. -/
theorem acct_expire (r : R) (i : Nat) (sl : Slot) (h : r.ring[i]? = some sl) (hst : sl.st = .lost) (f : Slot → Slot)
    (hf : ∀ s, (f s).size = s.size) (hf1 : (f sl).st = .done) (a : Acct r) :
    Acct { r with ring := upd r.ring i f } := by
  obtain ⟨h1, h2, h3, h4⟩ := a
  have e0 := sumSt_upd f .fl r.ring i sl h (hf sl)
  have e1 := sumSt_upd f .lost r.ring i sl h (hf sl)
  have c0 := cntSt_upd f .fl r.ring i sl h
  simp [hst, hf1] at e0 e1 c0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> omega

theorem lim_sum0 : ∀ (l : List Slot) (ex : Nat), sumSt (lim ex l) .fl = sumSt l .fl
  | [], ex => by simp [lim, sumSt]
  | s :: t, 0 => by simp [lim]
  | s :: t, ex + 1 => by
    by_cases h : s.st = .lost
    · simp [lim, h, sumSt, lim_sum0 t ex]
    · simp [lim, h, sumSt, lim_sum0 t (ex + 1)]

theorem lim_cnt0 : ∀ (l : List Slot) (ex : Nat), cntSt (lim ex l) .fl = cntSt l .fl
  | [], ex => by simp [lim, cntSt]
  | s :: t, 0 => by simp [lim]
  | s :: t, ex + 1 => by
    by_cases h : s.st = .lost
    · simp [lim, h, cntSt, lim_cnt0 t ex]
    · simp [lim, h, cntSt, lim_cnt0 t (ex + 1)]

theorem lim_sum1 : ∀ (l : List Slot) (ex : Nat), sumSt (lim ex l) .lost ≤ sumSt l .lost
  | [], ex => by simp [lim, sumSt]
  | s :: t, 0 => by simp [lim]
  | s :: t, ex + 1 => by
    by_cases h : s.st = .lost
    · have := lim_sum1 t ex
      simp [lim, h, sumSt]; omega
    · have := lim_sum1 t (ex + 1)
      simp [lim, h, sumSt]; omega

theorem acct_ring (r : R) (ring : List Slot) (h0 : sumSt ring .fl = sumSt r.ring .fl) (h1 : cntSt ring .fl = cntSt r.ring .fl)
    (h2 : sumSt ring .lost ≤ sumSt r.ring .lost) (a : Acct r) : Acct { r with ring := ring } := by
  obtain ⟨a1, a2, a3, a4⟩ := a
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> omega

theorem acct_limit (p : P) (r : R) (a : Acct r) : Acct { r with ring := limitGhosts p r.ring } :=
  acct_ring r _ (lim_sum0 _ _) (lim_cnt0 _ _) (lim_sum1 _ _) a

theorem trim_sums (p : P) (now : Nat) : ∀ l : List Slot,
    sumSt (trim p now l) .fl = sumSt l .fl ∧ cntSt (trim p now l) .fl = cntSt l .fl ∧ sumSt (trim p now l) .lost ≤ sumSt l .lost
  | [] => by simp [trim, sumSt, cntSt]
  | h :: t => by
    have ih := trim_sums p now t
    by_cases c : (h.st == .done || (h.st == .lost && decide (sadd p h.lostAt p.gret < now))) = true
    · have hne : h.st ≠ .fl := by
        intro e
        simp [e] at c
      simp only [trim, c, ↓reduceIte]
      simp [sumSt, cntSt, hne] at *
      try omega
    · simp only [trim, c]
      simp [sumSt, cntSt]

theorem acct_trim (p : P) (now : Nat) (r : R) (a : Acct r) : Acct { r with ring := trim p now r.ring } := by
  obtain ⟨x, y, z⟩ := trim_sums p now r.ring
  exact acct_ring r _ x y z a

theorem push_cases (p : P) (ring : List Slot) (sl : Slot) (ring' : List Slot) (hp : push p ring sl = some ring') :
    ring' = ring ++ [sl] ∨ ∃ h t, ring = h :: t ∧ h.st ≠ .fl ∧ ring' = t ++ [sl] := by
  unfold push at hp
  split at hp
  · cases ring with
    | nil => simp at hp; left; simp [hp]
    | cons h t =>
      by_cases hh : h.st = .fl
      · simp [hh] at hp
      · simp [hh] at hp
        right
        exact ⟨h, t, rfl, hh, hp.symm⟩
  · simp at hp
    left
    exact hp.symm

theorem acct_push (p : P) (r : R) (sl : Slot) (ring : List Slot) (hsl : sl.st = .fl) (hp : push p r.ring sl = some ring)
    (a : Acct r) :
    Acct { r with ring := ring, sent := r.sent + sl.size, inf := r.inf + sl.size, infp := r.infp + 1 } := by
  obtain ⟨a1, a2, a3, a4⟩ := a
  rcases push_cases p r.ring sl ring hp with e | ⟨h, t, e, hne, e'⟩
  · subst e
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sumSt_append, cntSt_append, sumSt, cntSt, hsl] <;> omega
  · subst e'
    rw [e] at a2 a3 a4
    simp [sumSt, cntSt, hne] at a2 a3 a4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sumSt_append, cntSt_append, sumSt, cntSt, hsl] <;> omega

/-- The fields the accounts read are the same. -/
def FEq (r r' : R) : Prop :=
  r'.ring = r.ring ∧ r'.sent = r.sent ∧ r'.acked = r.acked ∧ r'.lost = r.lost ∧ r'.inf = r.inf ∧ r'.infp = r.infp

theorem Acct.of_feq {r r' : R} (h : FEq r r') (a : Acct r) : Acct r' := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
  obtain ⟨a1, a2, a3, a4⟩ := a
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e1, e2, e3, e4, e5, e6] <;> assumption

theorem noteOvertaken_feq (p : P) (r : R) (now pn time path : Nat) : FEq r (noteOvertaken p r now pn time path) := by
  unfold noteOvertaken
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem loseAt_acct (p : P) (y : Y) (i now : Nat) (sl : Slot) (h : y.r.ring[i]? = some sl) (hst : sl.st = .fl)
    (a : Acct y.r) : Acct (loseAt p y i now).r := by
  unfold loseAt
  rw [h]
  refine acct_move y.r i sl h hst _ ?_ ?_ _ a
  · intro s; rfl
  · split <;> simp

theorem settle_acct (p : P) (y : Y) (a : Acct y.r) : Acct (settle p y).r := by
  unfold settle
  split
  · exact acct_limit p y.r a
  · exact a

theorem detectLoop_acct (p : P) (now largest : Nat) :
    ∀ (k i : Nat) (y : Y), Acct y.r → Acct (detectLoop p now largest k i y).r
  | 0, i, y, a => by simpa [detectLoop] using a
  | k + 1, i, y, a => by
    unfold detectLoop
    rcases hs : y.r.ring[i]? with _ | sl
    · simpa using a
    · try dsimp only
      split
      · exact a
      · split
        · exact detectLoop_acct p now largest k (i + 1) y a
        · rename_i h1 h2
          have hst : sl.st = .fl := by simpa using h2
          split
          · exact detectLoop_acct p now largest k (i + 1) _ a
          · exact detectLoop_acct p now largest k (i + 1) _ (loseAt_acct p y i now sl hs hst a)

theorem detect_acct (p : P) (y : Y) (now largest : Nat) (a : Acct y.r) : Acct (detect p y now largest).r :=
  settle_acct p _ (detectLoop_acct p now largest _ 0 _ a)

theorem ackRing_acct (p : P) (now b : Nat) :
    ∀ (k i : Nat) (x : X), Acct x.r → Acct (ackRing p now b k i x).r
  | 0, i, x, a => by simpa [ackRing] using a
  | k + 1, i, x, a => by
    unfold ackRing
    rcases hs : x.r.ring[i]? with _ | sl
    · simpa using a
    · try dsimp only
      split
      · exact a
      · split
        · exact ackRing_acct p now b k (i + 1) x a
        · rename_i h1 h2
          split
          · exact ackRing_acct p now b k (i + 1) x a
          · rename_i h3
            split
            · rename_i h4
              have hst : sl.st = .lost := by simp at h4; exact h4.1
              exact ackRing_acct p now b k (i + 1) _
                (acct_expire x.r i sl hs hst (fun s : Slot => { s with st := .done }) (fun _ => rfl) rfl a)
            · rename_i h4
              try dsimp only
              have hnd : sl.st ≠ .done := by simpa using h2
              have ho := noteOvertaken_feq p { x.r with ring := upd x.r.ring i fun s => { s with st := .done } } now sl.pn
                sl.time sl.path
              obtain ⟨o1, o2, o3, o4, o5, o6⟩ := ho
              cases hst : sl.st with
              | done => exact absurd hst hnd
              | lost =>
                simp only [beq_self_eq_true, ite_true]
                refine ackRing_acct p now b k (i + 1) _ (Acct.of_feq ?_
                  (acct_late x.r i sl hs hst (fun s : Slot => { s with st := .done }) (fun _ => rfl) rfl a))
                exact ⟨by simp [o1], by simp [o2], by simp [o3], by simp [o4], by simp [o5], by simp [o6]⟩
              | fl =>
                simp only [show (St.fl == St.lost) = false from by decide, Bool.false_eq_true, ↓reduceIte]
                refine ackRing_acct p now b k (i + 1) _ (Acct.of_feq ?_
                  (acct_ack x.r i sl hs hst (fun s : Slot => { s with st := .done }) (fun _ => rfl) rfl a))
                exact ⟨by simp [o1], by simp [o2], by simp [o3], by simp [o4], by simp [o5], by simp [o6]⟩

end Vinc.TransportRecovery
