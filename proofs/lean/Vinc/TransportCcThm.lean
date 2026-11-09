import Vinc.Axioms
import Vinc.TransportCc

/-!
# Congestion control and pacing: the theorems

What the model proves about the controller and the pacer, over unbounded windows, times and runs of calls:

- the window is never below `minCwnd` and never above `maxCwnd` after any call, the filter streak never exceeds 4,
  and the Reno estimate never exceeds the cap (`Inv`, `onAcked_inv`, `onLoss_inv`, `newPath_inv`, `restore_inv`,
  `resume_inv`);
- in slow start every acknowledged byte is added to the window, up to the cap (`growSS_cwnd`); an acknowledgement
  never lowers the window except by the rate gate (`growCA_ge`, `applyGate_le`), and the gate never takes it below
  the floor (`gateCap_bounds`);
- a loss multiplies the window by 0.7 (0.85 below 48,000 bytes) and ends slow start, a loss with no queueing delay
  by 0.9 and keeps it; one reduction per episode: a loss of a packet sent before the last reduction changes nothing
  (`onLoss_reduce`, `onLoss_filtered`, `onLoss_same_episode`); a reduction never raises the window (`onLoss_le`);
  the filter streak stops at 4 and decays after four smoothed round trips (`streak_decay`);
- a restore never lowers the window (`restore_ge`);
- the pacer holds one to ten tokens, lets exactly the tokens out before a pause, and after the burst waits ten gaps;
  a pause starts only after a full burst, idle time adds nothing (`pacer_tokens`, `pacer_burst`, `pacer_pause`,
  `pacer_release`).
-/

namespace Vinc.TransportCc

theorem h40 : maxCwnd ≤ u64max := by unfold maxCwnd u64max; decide
theorem hmin : minCwnd ≤ maxCwnd := by unfold minCwnd maxCwnd; decide
theorem hini : initialCwnd ≤ maxCwnd := by unfold initialCwnd maxCwnd; decide
theorem hmin_ini : minCwnd ≤ initialCwnd := by unfold minCwnd initialCwnd; decide

theorem sat_le (v : Nat) : sat v ≤ u64max := Nat.min_le_right _ _
theorem satAdd_ge (a b : Nat) (h : a ≤ u64max) : a ≤ satAdd a b := Nat.le_min.2 ⟨by omega, h⟩

/-- The shape every controller keeps. -/
structure Inv (c : Cc) : Prop where
  lo : minCwnd ≤ c.cwnd
  hi : c.cwnd ≤ maxCwnd
  streak : c.streak ≤ 4
  west : c.wEst ≤ maxCwnd

theorem inv_init : Inv ({} : Cc) :=
  ⟨hmin_ini, hini, by decide, Nat.zero_le _⟩

theorem growSS_cwnd (c : Cc) (acked la np : Nat) (h : c.cwnd ≤ u64max) :
    (c.growSS acked la np).cwnd = min (c.cwnd + acked) maxCwnd ∨ (c.growSS acked la np).cwnd = min u64max maxCwnd := by
  unfold Cc.growSS satAdd sat
  simp only []
  omega

theorem growSS_ge (c : Cc) (hc : Inv c) (acked la np : Nat) : c.cwnd ≤ (c.growSS acked la np).cwnd ∧
    (c.growSS acked la np).cwnd ≤ maxCwnd := by
  unfold Cc.growSS
  simp only []
  exact ⟨Nat.le_min.2 ⟨satAdd_ge _ _ (Nat.le_trans hc.hi h40), hc.hi⟩, Nat.min_le_right _ _⟩

theorem caCw1_bounds (cwnd : Nat) (t : Int) (acked mss : Nat) (hc : cwnd ≤ maxCwnd) :
    cwnd ≤ caCw1 cwnd t acked mss ∧ caCw1 cwnd t acked mss ≤ maxCwnd := by
  unfold caCw1
  split
  · exact ⟨Nat.le_min.2 ⟨satAdd_ge _ _ (Nat.le_trans hc h40), hc⟩, Nat.min_le_right _ _⟩
  · exact ⟨Nat.le_refl _, hc⟩

theorem caWe_le (west mss acked cw1 : Nat) : caWe west mss acked cw1 ≤ maxCwnd := Nat.min_le_right _ _

theorem caFinish_bounds (c : Cc) (ep k we cw1 : Nat) (h1 : c.cwnd ≤ cw1) (h2 : cw1 ≤ maxCwnd) (h3 : we ≤ maxCwnd) :
    c.cwnd ≤ (c.caFinish ep k we cw1).cwnd ∧ (c.caFinish ep k we cw1).cwnd ≤ maxCwnd ∧
      (c.caFinish ep k we cw1).wEst ≤ maxCwnd := by
  unfold Cc.caFinish
  simp only []
  refine ⟨?_, ?_, h3⟩ <;> split <;> omega

theorem growCA_ge (c : Cc) (hc : Inv c) (now acked mss srtt : Nat) :
    c.cwnd ≤ (c.growCA now acked mss srtt).cwnd ∧ (c.growCA now acked mss srtt).cwnd ≤ maxCwnd ∧
      (c.growCA now acked mss srtt).wEst ≤ maxCwnd := by
  unfold Cc.growCA
  simp only []
  refine caFinish_bounds c _ _ _ _ ?_ ?_ (caWe_le _ _ _ _)
  · exact (caCw1_bounds _ _ _ _ hc.hi).1
  · exact (caCw1_bounds _ _ _ _ hc.hi).2

theorem grow_bounds (c : Cc) (hc : Inv c) (now acked la np mss srtt : Nat) :
    c.cwnd ≤ (c.grow now acked la np mss srtt).cwnd ∧ (c.grow now acked la np mss srtt).cwnd ≤ maxCwnd ∧
      (c.grow now acked la np mss srtt).wEst ≤ maxCwnd ∧ (c.grow now acked la np mss srtt).streak = c.streak := by
  unfold Cc.grow
  split
  · obtain ⟨a, b⟩ := growSS_ge c hc acked la np
    exact ⟨a, b, hc.west, rfl⟩
  · obtain ⟨a, b, d⟩ := growCA_ge c hc now acked mss srtt
    exact ⟨a, b, d, rfl⟩

theorem gateCap_bounds (c : Cc) (m cap : Nat) (h : c.gateCap m = some cap) : minCwnd ≤ cap ∧ cap ≤ maxCwnd := by
  unfold Cc.gateCap at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, Nat.min_le_right _ _⟩
    refine Nat.le_min.2 ⟨?_, hmin⟩
    have : minCwnd ≤ initialCwnd := hmin_ini
    split <;> (try split) <;> simp [minCwnd] at * <;> omega

theorem applyGate_inv (c : Cc) (hc : Inv c) (m : Nat) : Inv (c.applyGate m) ∧ (c.applyGate m).cwnd ≤ c.cwnd := by
  unfold Cc.applyGate
  cases hg : c.gateCap m with
  | none => exact ⟨hc, Nat.le_refl _⟩
  | some cap =>
    obtain ⟨g1, g2⟩ := gateCap_bounds c m cap hg
    simp only []
    split
    · rename_i h
      exact ⟨⟨g1, g2, hc.streak, hc.west⟩, Nat.le_of_lt h⟩
    · exact ⟨hc, Nat.le_refl _⟩

/-- The rate gate caps the window at the measured rate when it is known. -/
theorem applyGate_le (c : Cc) (m cap : Nat) (h : c.gateCap m = some cap) : (c.applyGate m).cwnd ≤ cap := by
  unfold Cc.applyGate
  rw [h]
  simp only []
  split
  · exact Nat.le_refl _
  · rename_i hn; omega

theorem feed_inv (c : Cc) (hc : Inv c) (a : Ack) : Inv (c.feed a) :=
  ⟨hc.lo, hc.hi, hc.streak, hc.west⟩

theorem decay_cases (c : Cc) (now srtt : Nat) : c.decay now srtt = c ∨ c.decay now srtt = { c with streak := 0 } := by
  unfold Cc.decay
  by_cases h : decayCond c now srtt = true
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

theorem decay_inv (c : Cc) (hc : Inv c) (now srtt : Nat) : Inv (c.decay now srtt) := by
  rcases decay_cases c now srtt with h | h
  · rw [h]; exact hc
  · rw [h]; exact ⟨hc.lo, hc.hi, by show 0 ≤ 4; decide, hc.west⟩

theorem onAcked_inv (c : Cc) (hc : Inv c) (a : Ack) : Inv (c.onAcked a) := by
  have h2 := decay_inv _ (feed_inv c hc a) a.now (a.srtt.getD initialRtt)
  obtain ⟨g1, g2, g3, g4⟩ := grow_bounds _ h2 a.now a.acked a.largestAcked a.nextPn a.mss (a.srtt.getD initialRtt)
  have hg : Inv (((c.feed a).decay a.now (a.srtt.getD initialRtt)).grow a.now a.acked a.largestAcked a.nextPn a.mss
      (a.srtt.getD initialRtt)) :=
    ⟨Nat.le_trans h2.lo g1, g2, by rw [g4]; exact h2.streak, g3⟩
  unfold Cc.onAcked
  simp only []
  split
  · split
    · exact hg
    · exact (applyGate_inv _ hg _).1
  · exact hg

theorem onRtt_inv (c : Cc) (hc : Inv c) (s : Nat) : Inv (c.onRtt s) :=
  ⟨hc.lo, hc.hi, hc.streak, hc.west⟩

theorem lossFiltered_cwnd (c : Cc) (now : Nat) : (c.lossFiltered now).cwnd = max (c.cwnd * 9 / 10) minCwnd := by
  unfold Cc.lossFiltered; split <;> rfl

theorem lossFiltered_streak (c : Cc) (now : Nat) : (c.lossFiltered now).streak = c.streak + 1 := by
  unfold Cc.lossFiltered; split <;> rfl

theorem lossFiltered_west (c : Cc) (now : Nat) : (c.lossFiltered now).wEst ≤ c.wEst := by
  unfold Cc.lossFiltered; split
  · exact Nat.min_le_left _ _
  · exact Nat.le_refl _

theorem lossFiltered_inv (c : Cc) (hc : Inv c) (hs : c.streak < 4) (now : Nat) :
    Inv (c.lossFiltered now) ∧ (c.lossFiltered now).cwnd ≤ c.cwnd := by
  have h1 : c.cwnd * 9 / 10 ≤ c.cwnd := by omega
  have h2 : max (c.cwnd * 9 / 10) minCwnd ≤ c.cwnd := Nat.max_le.2 ⟨h1, hc.lo⟩
  have hc' := lossFiltered_cwnd c now
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hc']; exact Nat.le_max_right _ _
  · rw [hc']; exact Nat.le_trans h2 hc.hi
  · rw [lossFiltered_streak]; omega
  · exact Nat.le_trans (lossFiltered_west c now) hc.west
  · rw [hc']; exact h2

theorem lossRegular_inv (c : Cc) (hc : Inv c) (now : Nat) : Inv (c.lossRegular now) ∧ (c.lossRegular now).cwnd ≤ c.cwnd := by
  have h2 : max (c.cwnd * (if c.cwnd < betaSmallLim then 85 else 7) / (if c.cwnd < betaSmallLim then 100 else 10)) minCwnd
      ≤ c.cwnd := by
    refine Nat.max_le.2 ⟨?_, hc.lo⟩
    split <;> omega
  unfold Cc.lossRegular
  exact ⟨⟨Nat.le_max_right _ _, Nat.le_trans h2 hc.hi, by show 0 ≤ 4; decide, Nat.le_trans h2 hc.hi⟩, h2⟩

theorem onLoss_le (c : Cc) (hc : Inv c) (now newest : Nat) (l m : Option Nat) :
    (c.onLoss now newest l m).1.cwnd ≤ c.cwnd := by
  unfold Cc.onLoss
  split
  · exact Nat.le_refl _
  · split
    · rename_i hf
      have : c.streak < 4 := by
        unfold isFiltered at hf
        split at hf <;> simp_all
      exact (lossFiltered_inv c hc this now).2
    · exact (lossRegular_inv c hc now).2

theorem onLoss_inv (c : Cc) (hc : Inv c) (now newest : Nat) (l m : Option Nat) : Inv (c.onLoss now newest l m).1 := by
  unfold Cc.onLoss
  split
  · exact hc
  · split
    · rename_i hf
      have : c.streak < 4 := by
        unfold isFiltered at hf
        split at hf <;> simp_all
      exact (lossFiltered_inv c hc this now).1
    · exact (lossRegular_inv c hc now).1

/-- One reduction per episode: a loss of a packet sent before the last reduction changes nothing. -/
theorem onLoss_same_episode (c : Cc) (now newest r : Nat) (l m : Option Nat) (hr : c.recovery = some r)
    (hn : newest ≤ r) : c.onLoss now newest l m = (c, false) := by
  unfold Cc.onLoss inEpisode
  rw [hr]
  simp [hn]

/-- A loss outside the episode that is not filtered: the window is 0.7 of itself (0.85 below 48,000 bytes), the
threshold follows it, the window it came from is kept, slow start ends. -/
theorem onLoss_reduce (c : Cc) (now newest : Nat) (l m : Option Nat) (he : inEpisode c newest = false)
    (hf : isFiltered c l m = false) :
    (c.onLoss now newest l m).2 = true ∧
      (c.onLoss now newest l m).1.cwnd =
        max (c.cwnd * (if c.cwnd < betaSmallLim then 85 else 7) / (if c.cwnd < betaSmallLim then 100 else 10)) minCwnd ∧
      (c.onLoss now newest l m).1.ssthresh = (c.onLoss now newest l m).1.cwnd ∧
      (c.onLoss now newest l m).1.wMax = c.cwnd ∧ (c.onLoss now newest l m).1.streak = 0 ∧
      (c.onLoss now newest l m).1.recovery = some now := by
  unfold Cc.onLoss
  rw [he, hf]
  simp [Cc.lossRegular]

/-- A filtered loss: 0.9 of the window, one more in the streak, slow start is not left. -/
theorem onLoss_filtered (c : Cc) (now newest : Nat) (l m : Option Nat) (he : inEpisode c newest = false)
    (hf : isFiltered c l m = true) :
    (c.onLoss now newest l m).2 = true ∧ (c.onLoss now newest l m).1.cwnd = max (c.cwnd * 9 / 10) minCwnd ∧
      (c.onLoss now newest l m).1.streak = c.streak + 1 ∧ c.streak < 4 := by
  have hs : c.streak < 4 := by
    unfold isFiltered at hf
    split at hf <;> simp_all
  unfold Cc.onLoss
  rw [he, hf]
  exact ⟨by simp, lossFiltered_cwnd c now, lossFiltered_streak c now, hs⟩

theorem newPath_inv (c : Cc) (hc : Inv c) (now np : Nat) : Inv (c.newPath now np) :=
  ⟨hmin_ini, hini, by show 0 ≤ 4; decide, hc.west⟩

theorem restore_ge (c : Cc) (hc : Inv c) (cw ss : Nat) : c.cwnd ≤ (c.restore cw ss).cwnd ∧ Inv (c.restore cw ss) := by
  unfold Cc.restore
  split
  · rename_i h
    simp only []
    have hm : min cw maxCwnd ≤ maxCwnd := Nat.min_le_right _ _
    have : c.cwnd ≤ min cw maxCwnd := Nat.le_min.2 ⟨Nat.le_of_lt h, hc.hi⟩
    exact ⟨this, ⟨Nat.le_trans hc.lo this, hm, hc.streak, Nat.max_le.2 ⟨hc.west, hm⟩⟩⟩
  · exact ⟨Nat.le_refl _, hc⟩

theorem resume_inv (c : Cc) (hc : Inv c) (m : Option Nat) : Inv (c.resume m) := by
  unfold Cc.resume
  split
  · exact (applyGate_inv c hc _).1
  · exact hc

theorem setSlack_inv (c : Cc) (hc : Inv c) (b : Nat) : Inv (c.setSlack b) :=
  ⟨hc.lo, hc.hi, hc.streak, hc.west⟩

theorem applyGate_streak (c : Cc) (m : Nat) : (c.applyGate m).streak = c.streak := by
  unfold Cc.applyGate
  cases c.gateCap m with
  | none => rfl
  | some cap => simp only []; split <;> rfl

theorem grow_streak (c : Cc) (now acked la np mss srtt : Nat) : (c.grow now acked la np mss srtt).streak = c.streak := by
  unfold Cc.grow
  split
  · simp [Cc.growSS]
  · simp [Cc.growCA, Cc.caFinish]

/-- The streak decays: four smoothed round trips after the last reduction an acknowledgement clears it. -/
theorem streak_decay (c : Cc) (a : Ack) (r : Nat) (hr : c.recovery = some r)
    (hs : c.streak ≠ 0) (hd : satMul 4 (a.srtt.getD initialRtt) < a.now - r) : (c.onAcked a).streak = 0 := by
  have hz : ((c.feed a).decay a.now (a.srtt.getD initialRtt)).streak = 0 := by
    have hcond : decayCond (c.feed a) a.now (a.srtt.getD initialRtt) = true := by
      unfold decayCond Cc.feed
      simp [hs, hr, hd]
    unfold Cc.decay
    rw [if_pos hcond]
  unfold Cc.onAcked
  simp only []
  split
  · split
    · rw [grow_streak]; exact hz
    · rw [applyGate_streak, grow_streak]; exact hz
  · rw [grow_streak]; exact hz

/-! ### The pacer -/

/-- The pacer holds one to ten tokens. -/
theorem pacer_tokens (p : Pacer) (h1 : 1 ≤ p.tokens) (h2 : p.tokens ≤ burst) (now mtu srtt cw : Nat) :
    1 ≤ (p.onSent now mtu srtt cw).tokens ∧ (p.onSent now mtu srtt cw).tokens ≤ burst := by
  unfold Pacer.onSent
  split
  · simp only []; omega
  · simp only []; unfold burst; omega

/-- A packet out of the burst takes one token and leaves the release where it was. -/
theorem pacer_burst (p : Pacer) (h : 1 < p.tokens) (now mtu srtt cw : Nat) :
    (p.onSent now mtu srtt cw).tokens = p.tokens - 1 ∧ (p.onSent now mtu srtt cw).next = p.next := by
  unfold Pacer.onSent
  simp [h]

/-- The last token starts the pause: ten gaps from the packet, and the burst is full again. -/
theorem pacer_pause (p : Pacer) (h : p.tokens ≤ 1) (now mtu srtt cw : Nat) :
    (p.onSent now mtu srtt cw).tokens = burst ∧ (p.onSent now mtu srtt cw).next = satAdd now (satMul (gap mtu srtt cw) burst) := by
  unfold Pacer.onSent
  have : ¬ 1 < p.tokens := by omega
  simp [this]

/-- Data leaves at the release time or later, never before the pause ends. -/
theorem pacer_release_ge (p : Pacer) (now : Nat) : now ≤ p.nextRelease now ∧ p.next ≤ p.nextRelease now := by
  unfold Pacer.nextRelease
  split <;> omega

/-- Calls of `on_sent`, each with the time and the datagram size, round trip and window it was made with. -/
def runSends (p : Pacer) (l : List (Nat × Nat × Nat × Nat)) : Pacer :=
  l.foldl (fun q a => q.onSent a.1 a.2.1 a.2.2.1 a.2.2.2) p

/-- Fewer packets than tokens leave back to back with no pause: the release does not move. -/
theorem runSends_no_pause : ∀ (l : List (Nat × Nat × Nat × Nat)) (p : Pacer), l.length < p.tokens →
    (runSends p l).tokens = p.tokens - l.length ∧ (runSends p l).next = p.next
  | [], p, _ => by simp [runSends]
  | a :: t, p, h => by
    have h1 : 1 < p.tokens := by simp at h; omega
    obtain ⟨b1, b2⟩ := pacer_burst p h1 a.1 a.2.1 a.2.2.1 a.2.2.2
    have ih := runSends_no_pause t (p.onSent a.1 a.2.1 a.2.2.1 a.2.2.2) (by simp at h; omega)
    simp only [runSends, List.foldl_cons] at ih ⊢
    obtain ⟨i1, i2⟩ := ih
    exact ⟨by simp at h ⊢; omega, by rw [i2, b2]⟩

end Vinc.TransportCc
