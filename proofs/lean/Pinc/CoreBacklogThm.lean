import Pinc.CoreBacklog

/-!
# The accept room: the counter is exact, and every session a first flight makes finds a place

What the model proves, for any number of slots and any queue size:

- between calls the counter is the number of owed slots, and the waiting sessions and the owed ones together never
  pass the queue's size (`Inv`, kept by `init_inv`, `make_inv`, `release_inv`, `take_inv`, `sub_inv`, `pop_inv`);
- so the host never finds the queue full when it reads the `Incoming` of an owed session: no session a first flight
  made is closed as busy after its handshake (`take_not_busy`);
- a first flight refused for want of room changes nothing (`make_refused`);
- the half rule never raises the half-open cap (`halfCap_le_max`), admits a flight that does not resume only while the
  counted sessions are fewer than half of the room, rounded up (`halfCap_admits`), and so the sessions it admitted
  never fill an empty queue of two places or more: a peer that resumes finds room beside them (`resume_finds_room`).
-/

namespace Pinc.CoreBacklog

theorem count_replicate (k : Nat) : countOf (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, countOf, ih]

theorem count_put_true : ∀ (l : List Bool) (j : Nat), get l j = false → j < l.length →
    countOf (put l j true) = countOf l + 1
  | [], _, _, hl => by simp at hl
  | b :: t, 0, hg, _ => by
      simp only [get] at hg
      subst hg
      simp [put, countOf]
      omega
  | b :: t, n + 1, hg, hl => by
      simp only [get] at hg
      have h := count_put_true t n hg (by simp at hl; omega)
      simp only [put, countOf, h]
      omega

theorem count_put_false : ∀ (l : List Bool) (j : Nat), get l j = true → countOf (put l j false) + 1 = countOf l
  | [], _, hg => by simp [get] at hg
  | b :: t, 0, hg => by
      simp only [get] at hg
      subst hg
      simp [put, countOf]
      omega
  | b :: t, n + 1, hg => by
      simp only [get] at hg
      have h := count_put_false t n hg
      simp only [put, countOf]
      omega

/-- The counter is the number of owed slots, and the waiting sessions with the owed ones fit in the queue. -/
def Inv (cap : Nat) (b : B) : Prop := b.n = countOf b.owed ∧ b.q + b.n ≤ cap

theorem init_inv (cap k : Nat) : Inv cap (init k) := by
  simp [Inv, init, count_replicate]

/-- A made session is counted, and was made only while it had a place. -/
theorem make_inv (cap : Nat) (b : B) (j : Nat) (h : Inv cap b) : Inv cap (make cap b j) := by
  obtain ⟨hn, hq⟩ := h
  unfold make
  split
  · next hc =>
    obtain ⟨hr, hl, hg⟩ := hc
    have hc' := count_put_true b.owed j hg hl
    simp only [room] at hr
    exact ⟨by simp only; omega, by simp only; omega⟩
  · exact ⟨hn, hq⟩

/-- A refused first flight changes nothing. -/
theorem make_refused (cap : Nat) (b : B) (j : Nat) (h : ¬ b.n < room cap b) : make cap b j = b := by
  unfold make
  simp [h]

/-- An ended session is owed no more, and its place goes back. -/
theorem release_inv (cap : Nat) (b : B) (j : Nat) (h : Inv cap b) : Inv cap (release b j) := by
  obtain ⟨hn, hq⟩ := h
  unfold release
  split
  · next hg =>
    have hc := count_put_false b.owed j hg
    exact ⟨by simp only; omega, by simp only; omega⟩
  · exact ⟨hn, hq⟩

/-- The host queues an owed session in the place held for it. -/
theorem take_inv (cap : Nat) (b : B) (j : Nat) (h : Inv cap b) : Inv cap (take cap b j).1 := by
  obtain ⟨hn, hq⟩ := h
  unfold take
  split
  · next hg =>
    have hc := count_put_false b.owed j hg
    refine ⟨by simp only; omega, ?_⟩
    simp only
    split <;> omega
  · exact ⟨hn, hq⟩

/-- The `Incoming` of an owed session never finds the queue full: it is not closed as busy. -/
theorem take_not_busy (cap : Nat) (b : B) (j : Nat) (h : Inv cap b) (hg : get b.owed j = true) :
    (take cap b j).2 = false := by
  obtain ⟨hn, hq⟩ := h
  have hc := count_put_false b.owed j hg
  simp only [take, hg, ↓reduceIte, decide_eq_false_iff_not]
  omega

/-- A sub-session takes only a place no owed session holds. -/
theorem sub_inv (cap : Nat) (b : B) (h : Inv cap b) : Inv cap (sub cap b) := by
  obtain ⟨hn, hq⟩ := h
  unfold sub
  split
  · exact ⟨hn, by simp only; omega⟩
  · exact ⟨hn, hq⟩

theorem pop_inv (cap : Nat) (b : B) (h : Inv cap b) : Inv cap (pop b) := by
  obtain ⟨hn, hq⟩ := h
  exact ⟨hn, by simp only [pop]; omega⟩

/-- The half rule never raises the half-open cap. -/
theorem halfCap_le_max (m room : Nat) : halfCap m room ≤ m := by
  unfold halfCap
  exact Nat.min_le_left _ _

/-- A first flight that does not resume is admitted only while the counted sessions are fewer than half of the room,
rounded up. -/
theorem halfCap_admits (m room count : Nat) (h : count < halfCap m room) : 2 * count < room + 1 := by
  unfold halfCap at h
  have h2 : count < (room + 1) / 2 := Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)
  omega

/-- The sessions admitted under the half rule never fill an empty queue of two places or more, so a peer that resumes
finds room beside them. -/
theorem resume_finds_room (m cap counted : Nat) (hc : 2 ≤ cap) (h : counted ≤ halfCap m cap) : counted < cap := by
  unfold halfCap at h
  have h2 : counted ≤ (cap + 1) / 2 := Nat.le_trans h (Nat.min_le_right _ _)
  omega

end Pinc.CoreBacklog
