import Vinc.Axioms
import Vinc.TransportRecoveryCalls

/-!
# Loss recovery: the theorems

What the model proves about `vinc-transport` loss recovery, over unbounded rings, times and runs of calls (the
accounts, which hold after every call, are in `Vinc.TransportRecoveryCalls`):

- the sent ring never overflows and its room check guarantees progress: a ring without room is full and its head
  is in flight, and the packet the probe timeout declares lost is that head, which gives the room back
  (`push_len`, `no_room_shape`, `pto_frees_room`);
- the probe timeout declares the oldest packet in flight lost (`declareOldest_first`), backs off without bound
  of count but not of time (`ptoDur_mono`, `ptoDur_le_cap`), and a lost packet is reported with its frames and
  requeued unless it is a repair packet or a path MTU probe (`loseAt_event`); only a packet in flight is ever
  declared lost (`detectLoop_lost_inflight`, `declareOldest_first`; `loseAt` itself does not test the state, its callers do), a ghost is kept only for stream data (`loseAt_ghost`);
- at most `maxg` ghosts remain after a loss (`ghosts_limit`);
- the give-up decision needs 10 probe timeouts and the tell-the-endpoint decision 3 (`health_dead`,
  `health_degraded`);
- a packet number is sent once, strictly above every earlier one (`send_fresh`);
- the reorder lens only widens its extent while the evidence is fresh and the time rule it selects never waits
  longer than four round trips (`noteOvertaken_widens`, `reorder_threshold_le`);
- tail repair: a candidate exists only after a burst of exactly one packet (`TailInv`, kept by `tail_new`, `tail_packet`, `tail_drain`).
-/

namespace Vinc.TransportRecovery

/-! ### The ring -/

theorem push_none_iff (p : P) (hn : 1 ≤ p.n) (ring : List Slot) (sl : Slot) (hle : ring.length ≤ p.n) :
    push p ring sl = none ↔ hasRoom p ring = false := by
  cases ring with
  | nil => simp [push, hasRoom]; omega
  | cons h t =>
    by_cases hl : (h :: t).length = p.n
    · simp [push, hasRoom, hl]
    · have lt : (h :: t).length < p.n := by omega
      have hl' : ¬ (t.length + 1 = p.n) := by simpa using hl
      have lt' : t.length + 1 < p.n := by simpa using lt
      simp [push, hasRoom, hl', lt']

/-- A push never takes the ring past its capacity. -/
theorem push_len (p : P) (hn : 1 ≤ p.n) (ring ring' : List Slot) (sl : Slot) (hle : ring.length ≤ p.n)
    (hp : push p ring sl = some ring') : ring'.length ≤ p.n := by
  unfold push at hp
  split at hp
  · rename_i hfull
    cases ring with
    | nil => simp at hfull; omega
    | cons h t =>
      by_cases hh : h.st = .fl
      · simp [hh] at hp
      · simp [hh] at hp
        subst hp
        simp at hfull ⊢
        omega
  · rename_i hne
    simp at hp
    subst hp
    simp
    omega

/-- A ring with no room is full, and its head is in flight. -/
theorem no_room_shape (p : P) (hn : 1 ≤ p.n) (ring : List Slot) (hle : ring.length ≤ p.n)
    (h : hasRoom p ring = false) : ring.length = p.n ∧ ∃ hd t, ring = hd :: t ∧ hd.st = .fl := by
  cases ring with
  | nil => simp [hasRoom] at h; omega
  | cons hd t =>
    simp [hasRoom] at h hle
    exact ⟨by simp; omega, hd, t, rfl, h.2⟩

theorem lim_length : ∀ (l : List Slot) (ex : Nat), (lim ex l).length = l.length
  | [], ex => by simp [lim]
  | s :: t, 0 => by simp [lim]
  | s :: t, ex + 1 => by
    by_cases h : s.st = .lost
    · simp [lim, h, lim_length t ex]
    · simp [lim, h, lim_length t (ex + 1)]

theorem lim_head (ex : Nat) (h : Slot) (t : List Slot) :
    ∃ h' t', lim ex (h :: t) = h' :: t' ∧ (h'.st = .fl ↔ h.st = .fl) := by
  cases ex with
  | zero => exact ⟨h, t, by simp [lim], Iff.rfl⟩
  | succ ex =>
    by_cases hh : h.st = .lost
    · exact ⟨{ h with st := .done }, lim ex t, by simp [lim, hh], by simp [hh]⟩
    · exact ⟨h, lim (ex + 1) t, by simp [lim, hh], Iff.rfl⟩

theorem hasRoom_limit (p : P) (ring : List Slot) : hasRoom p (limitGhosts p ring) = hasRoom p ring := by
  unfold limitGhosts
  cases ring with
  | nil => simp [lim]
  | cons h t =>
    obtain ⟨h', t', e, hi⟩ := lim_head (ghosts (h :: t) - p.maxg) h t
    rw [e]
    have hl := lim_length (h :: t) (ghosts (h :: t) - p.maxg)
    rw [e] at hl
    have hb : (h'.st != St.fl) = (h.st != St.fl) := by
      apply Bool.eq_iff_iff.mpr
      simp only [bne_iff_ne, ne_eq]
      exact not_congr hi
    simp [hasRoom, hl, hb]

/-- The packet the probe timeout declares lost is the oldest one in flight. -/
theorem declareOldest_first (y : Y) (i : Nat) (hi : firstIF y.r.ring = some i) :
    ∃ sl, y.r.ring[i]? = some sl ∧ sl.st = .fl ∧ (∀ j < i, ∀ s, y.r.ring[j]? = some s → s.st ≠ .fl) := by
  have key : ∀ (l : List Slot) (n i : Nat), firstIFFrom l n = some i →
      ∃ sl, l[i - n]? = some sl ∧ sl.st = .fl ∧ (∀ j, j + n < i → ∀ s, l[j]? = some s → s.st ≠ .fl) := by
    intro l
    induction l with
    | nil => intro n i h; simp [firstIFFrom] at h
    | cons s t ih =>
      intro n i h
      unfold firstIFFrom at h
      by_cases hs : s.st = .fl
      · simp [hs] at h
        subst h
        refine ⟨s, by simp, hs, ?_⟩
        intro j hj; omega
      · simp [hs] at h
        obtain ⟨sl, h1, h2, h3⟩ := ih (n + 1) i h
        refine ⟨sl, ?_, h2, ?_⟩
        · have hle := (firstIFFrom_spec t (n + 1) i h).1
          have : i - n = (i - (n + 1)) + 1 := by omega
          rw [this]; simpa using h1
        · intro j hj s' hs'
          cases j with
          | zero => simp at hs'; subst hs'; exact hs
          | succ j => exact h3 j (by omega) s' (by simpa using hs')
  obtain ⟨sl, h1, h2, h3⟩ := key y.r.ring 0 i hi
  exact ⟨sl, by simpa using h1, h2, fun j hj s hs => h3 j (by omega) s hs⟩

/-- A ring with no room is given room by the probe timeout: it is full, so its head is the oldest packet in
flight, and declaring it lost leaves the head out of flight. The same holds after the ghosts are limited. -/
theorem pto_frees_room (p : P) (hn : 1 ≤ p.n) (y : Y) (now : Nat) (hle : y.r.ring.length ≤ p.n)
    (h : hasRoom p y.r.ring = false) : hasRoom p (declareOldest p y now).r.ring = true := by
  obtain ⟨_, hd, t, e, hst⟩ := no_room_shape p hn y.r.ring hle h
  have hf : firstIF y.r.ring = some 0 := by
    rw [e]; simp [firstIF, firstIFFrom, hst]
  have h0 : y.r.ring[0]? = some hd := by rw [e]; simp
  have key : ∀ y1 : Y, y1.r.ring = y.r.ring → hasRoom p (settle p (loseAt p y1 0 now)).r.ring = true := by
    intro y1 hr
    have h1 : y1.r.ring[0]? = some hd := by rw [hr]; exact h0
    have hring : y1.r.ring = hd :: t := by rw [hr]; exact e
    unfold settle loseAt
    rw [h1]
    dsimp only
    split
    · rw [hasRoom_limit]
      simp [hasRoom, hring, upd]
      split <;> simp
    · simp [hasRoom, hring, upd]
      split <;> simp
  unfold declareOldest
  rw [hf]
  simp only [h0]
  split
  · exact key _ rfl
  · exact key _ rfl

/-! ### The probe timer -/

/-- The timeout grows with the number of consecutive timeouts, and not past its cap. -/
theorem min_mono (a b c d : Nat) (h1 : a ≤ b) (h2 : c ≤ d) : min a c ≤ min b d := by omega

theorem ptoDur_mono (p : P) (r : R) (m : Nat) (h : r.pc ≤ m) : ptoDur p r ≤ ptoDur p { r with pc := m } := by
  unfold ptoDur
  dsimp only
  refine min_mono _ _ _ _ (min_mono _ _ _ _ ?_ (Nat.le_refl _)) (Nat.le_refl _)
  unfold smul sat
  exact min_mono _ _ _ _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega : min r.pc 6 ≤ min m 6))) (Nat.le_refl _)

theorem ptoDur_le_cap (p : P) (r : R) : ptoDur p r ≤ if ptoSlow p r then ptoWide p r else p.ptoCap := by
  unfold ptoDur
  dsimp only
  exact Nat.min_le_right _ _

theorem health_dead (p : P) (r : R) (now : Nat) (h : health p r now = "Dead") : 10 ≤ r.pc := by
  refine Classical.byContradiction fun hc => ?_
  have h10 : ¬ 10 ≤ r.pc := hc
  unfold health at h
  dsimp only at h
  simp [h10] at h
  split at h <;> simp at h

theorem health_degraded (p : P) (r : R) (now : Nat) (h : health p r now = "Degraded") : 3 ≤ r.pc := by
  refine Classical.byContradiction fun hc => ?_
  have h3 : ¬ 3 ≤ r.pc := hc
  have h10 : ¬ 10 ≤ r.pc := by omega
  unfold health at h
  dsimp only at h
  simp [h10, h3] at h

/-! ### Sending -/

theorem send_fresh (p : P) (r : R) (k : Pkt) :
    (send p r k).err = "ok" → (send p r k).r.ls = some k.pn ∧ ∀ l, r.ls = some l → l < k.pn := by
  unfold send
  split
  · intro h; simp [res] at h
  · split
    · intro h; simp [res] at h
    · dsimp only
      split
      · intro h; simp [res] at h
      · rename_i c1 c2 ring hp
        intro _
        refine ⟨by simp [res], ?_⟩
        intro l hl
        simp_all

theorem untracked_fresh (r : R) (pn : Nat) :
    (untracked r pn).err = "ok" → (untracked r pn).r.ls = some pn ∧ ∀ l, r.ls = some l → l < pn := by
  unfold untracked
  split
  · intro h; simp [res] at h
  · rename_i c1
    intro _
    refine ⟨by simp [res], ?_⟩
    intro l hl
    simp [hl] at c1
    omega

/-! ### Losing a packet -/

theorem upd_get_self {α β : Type} (f : α → α) (g : α → β) :
    ∀ (l : List α) (i : Nat), ((upd l i f)[i]?).map g = (l[i]?).map (fun a => g (f a))
  | [], i => by simp [upd]
  | x :: xs, 0 => by simp [upd]
  | x :: xs, i + 1 => by simpa [upd] using upd_get_self f g xs i

theorem upd_get_ne {α : Type} (f : α → α) : ∀ (l : List α) (i j : Nat), j ≠ i → (upd l i f)[j]? = l[j]?
  | [], i, j, _ => by simp [upd]
  | x :: xs, 0, j, h => by
    cases j with
    | zero => exact absurd rfl h
    | succ j => simp [upd]
  | x :: xs, i + 1, j, h => by
    cases j with
    | zero => simp [upd]
    | succ j => simpa [upd] using upd_get_ne f xs i j (by omega)

/-- A lost packet is reported with its frames, and requeued unless it is a repair packet or a path MTU probe. -/
theorem loseAt_event (p : P) (y : Y) (i now : Nat) (sl : Slot) (h : y.r.ring[i]? = some sl) :
    (loseAt p y i now).ev = y.ev ++ [⟨"lost", sl.pn, sl.size, sl.fr, !sl.rep && !sl.probe, sl.probe⟩] := by
  unfold loseAt
  rw [h]

/-- The packet declared lost keeps a ghost exactly when it counts and carries stream data with bytes and no end;
otherwise it is done at once, so a later acknowledgement of it acts on nothing. -/
theorem loseAt_ghost (p : P) (y : Y) (i now : Nat) (sl : Slot) (h : y.r.ring[i]? = some sl) :
    ((loseAt p y i now).r.ring[i]?).map (·.st) =
      some (if (!sl.rep && !sl.probe && sl.fr.any id) = true then St.lost else St.done) := by
  unfold loseAt
  rw [h]
  dsimp only
  rw [upd_get_self]
  simp [h]

/-- A packet declared lost by the loss rules was in flight when the call began: nothing done or already lost is
declared lost again. -/
theorem detectLoop_lost_inflight (p : P) (now largest : Nat) :
    ∀ (k i : Nat) (y : Y) (e : Ev), e ∈ (detectLoop p now largest k i y).ev → e ∈ y.ev ∨
      ∃ j, i ≤ j ∧ ∃ sl, y.r.ring[j]? = some sl ∧ sl.st = .fl ∧ e.k = "lost" ∧ e.pn = sl.pn
  | 0, i, y, e, h => by simp [detectLoop] at h; exact Or.inl h
  | k + 1, i, y, e, h => by
    unfold detectLoop at h
    rcases hs : y.r.ring[i]? with _ | sl
    · simp [hs] at h; exact Or.inl h
    · simp only [hs] at h
      split at h
      · exact Or.inl h
      · split at h
        · rcases detectLoop_lost_inflight p now largest k (i + 1) y e h with a | ⟨j, hj, sl', h1, h2, h3, h4⟩
          · exact Or.inl a
          · exact Or.inr ⟨j, by omega, sl', h1, h2, h3, h4⟩
        · rename_i c1 c2
          have hst : sl.st = .fl := by simpa using c2
          split at h
          · rcases detectLoop_lost_inflight p now largest k (i + 1) _ e h with a | ⟨j, hj, sl', h1, h2, h3, h4⟩
            · exact Or.inl a
            · exact Or.inr ⟨j, by omega, sl', h1, h2, h3, h4⟩
          · rcases detectLoop_lost_inflight p now largest k (i + 1) _ e h with a | ⟨j, hj, sl', h1, h2, h3, h4⟩
            · rw [loseAt_event p y i now sl hs] at a
              simp at a
              rcases a with a | a
              · exact Or.inl a
              · subst a
                exact Or.inr ⟨i, Nat.le_refl _, sl, hs, hst, rfl, rfl⟩
            · refine Or.inr ⟨j, by omega, sl', ?_, h2, h3, h4⟩
              have hne : j ≠ i := by omega
              unfold loseAt at h1
              rw [hs] at h1
              dsimp only at h1
              rw [upd_get_ne _ _ _ _ hne] at h1
              exact h1

/-! ### Ghosts -/

theorem ghosts_lim : ∀ (l : List Slot) (ex : Nat), ghosts (lim ex l) = ghosts l - ex
  | [], ex => by simp [ghosts, lim]
  | s :: t, 0 => by simp [lim]
  | s :: t, ex + 1 => by
    have ih := ghosts_lim t ex
    have ih' := ghosts_lim t (ex + 1)
    by_cases h : s.st = .lost
    · simp [lim, h, ghosts] at *
      omega
    · simp [lim, h, ghosts] at *
      omega

/-- After a loss at most `maxg` ghosts remain. -/
theorem ghosts_limit (p : P) (l : List Slot) : ghosts (limitGhosts p l) ≤ p.maxg := by
  unfold limitGhosts
  rw [ghosts_lim]
  omega

theorem settle_ghosts (p : P) (y : Y) (h : y.s.lp > 0) : ghosts (settle p y).r.ring ≤ p.maxg := by
  unfold settle
  simp only [h, ↓reduceIte]
  exact ghosts_limit p _

/-! ### The reorder lens -/

theorem reorder_threshold_le (p : P) (r : R) (sl : Slot) (largest now e : Nat) (hact : sl.path = r.act)
    (hrel : isRelay r sl.path = false) (hre : reoExtent p r sl.path now = some e) :
    (verdict p r sl largest now).2 ≤ smul p (lossRtt p r) 4 := by
  rw [hact] at hrel hre
  unfold verdict
  dsimp only
  simp [hact, hrel, hre]
  omega

theorem noteOvertaken_widens (p : P) (r : R) (now pn time path : Nat) (hh : 0 < reoHold p r)
    (hp : path < r.reo.length) (e : Nat) (he : reoExtent p r path now = some e) :
    ∃ e', reoExtent p (noteOvertaken p r now pn time path) path now = some e' ∧ e ≤ e' := by
  unfold noteOvertaken
  split
  · exact ⟨e, he, Nat.le_refl _⟩
  · split
    · exact ⟨e, he, Nat.le_refl _⟩
    · refine ⟨max ((reoExtent p r path now).getD 0) (r.lat - time), ?_, ?_⟩
      · unfold reoExtent
        simp [List.getD_eq_getElem?_getD, hp]
        exact Nat.pos_iff_ne_zero.mp hh
      · rw [he]
        exact Nat.le_max_left _ _

/-! ### Tail repair -/

/-- A candidate exists only after a burst of exactly one packet, and the burst count saturates at 2. -/
def TailInv (t : Tail) : Prop := t.burst ≤ 2 ∧ (t.cand.isSome → t.burst = 1)

theorem tail_new : TailInv Tail.new := by simp [TailInv, Tail.new]

theorem tail_packet (t : Tail) (pn : Nat) (plain inel : Bool) (h : TailInv t) : TailInv (tailPacket t pn plain inel) := by
  obtain ⟨h1, h2⟩ := h
  by_cases hi : inel = true
  · subst hi
    simp [tailPacket, TailInv]
  · have hi' : inel = false := by simpa using hi
    subst hi'
    by_cases hb : t.burst = 0
    · have hc : t.cand = none := by
        cases hcc : t.cand with
        | none => rfl
        | some _ => have := h2 (by simp [hcc]); omega
      cases plain <;> simp [tailPacket, TailInv, hb, hc]
    · have : 1 < min (t.burst + 1) 2 := by omega
      simp [tailPacket, TailInv, this]
      omega

theorem tail_drain (t : Tail) (h : TailInv t) : TailInv (tailDrain t).1 ∧ ((tailDrain t).2.isSome → t.burst = 1) := by
  obtain ⟨_, h2⟩ := h
  exact ⟨tail_new, by simpa [tailDrain] using h2⟩

end Vinc.TransportRecovery

#audit_axioms Vinc.TransportRecovery.send_acct
#audit_axioms Vinc.TransportRecovery.untracked_acct
#audit_axioms Vinc.TransportRecovery.ack_acct
#audit_axioms Vinc.TransportRecovery.timeout_acct
#audit_axioms Vinc.TransportRecovery.flush_acct
#audit_axioms Vinc.TransportRecovery.push_none_iff
#audit_axioms Vinc.TransportRecovery.push_len
#audit_axioms Vinc.TransportRecovery.no_room_shape
#audit_axioms Vinc.TransportRecovery.pto_frees_room
#audit_axioms Vinc.TransportRecovery.declareOldest_first
#audit_axioms Vinc.TransportRecovery.ptoDur_mono
#audit_axioms Vinc.TransportRecovery.ptoDur_le_cap
#audit_axioms Vinc.TransportRecovery.health_dead
#audit_axioms Vinc.TransportRecovery.health_degraded
#audit_axioms Vinc.TransportRecovery.send_fresh
#audit_axioms Vinc.TransportRecovery.untracked_fresh
#audit_axioms Vinc.TransportRecovery.loseAt_event
#audit_axioms Vinc.TransportRecovery.loseAt_ghost
#audit_axioms Vinc.TransportRecovery.detectLoop_lost_inflight
#audit_axioms Vinc.TransportRecovery.ghosts_limit
#audit_axioms Vinc.TransportRecovery.settle_ghosts
#audit_axioms Vinc.TransportRecovery.reorder_threshold_le
#audit_axioms Vinc.TransportRecovery.noteOvertaken_widens
#audit_axioms Vinc.TransportRecovery.tail_packet
#audit_axioms Vinc.TransportRecovery.tail_drain
