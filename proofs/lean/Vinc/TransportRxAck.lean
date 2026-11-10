import Vinc.Axioms
import Vinc.TransportRxRecv

/-!
# Received packets: the acknowledgement rules

What the model proves about the acknowledgement decision and the report of `ReceivedPackets`:

- a receive changes only the range set, the floor and, for an ack-eliciting new packet, the pending count and the
  deadline (`insert_keeps`);
- an acknowledgement is due no later than the delay after the oldest ack-eliciting packet it still owes: once the
  clock has passed that point the deadline has passed (`ack_due_after_delay`, from the invariant `Owed` that every
  call keeps: `owed_receive`, `owed_ackSent`, `owed_other`); a gap, or the count rule, makes the deadline the
  time of the packet (`receive_due_now`);
- the ranges reported are the newest, at most `maxack`, and at least one when anything was received
  (`ackRanges_length_le`, `ackRanges_ne_nil`);
- our acknowledgement table and the confirmation queue never exceed their bounds (`ackSent_tables`,
  `peerAck_tables`).
-/

namespace Vinc.TransportRx

theorem insert_keeps (x : X) (pn : Nat) :
    ∀ ok y, insert x pn = (ok, y) → y.pending = x.pending ∧ y.due = x.due ∧ y.mrtt = x.mrtt ∧ y.every = x.every ∧
      y.cap = x.cap := by
  intro ok y h
  unfold insert insertAB pushNew at h
  repeat' split at h
  all_goals (simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp)

/-- The earlier of the deadlines of the packets owed an acknowledgement, with the one just received. -/
def limNext (lim : Option Nat) (due2 : Nat) : Nat := match lim with | none => due2 | some l => min l due2

/-- The deadline bound after a call: it changes only for an ack-eliciting new packet. -/
def limAfter (lim : Option Nat) (out : String) (elic : Bool) (now : Nat) (m : Option Nat) : Option Nat :=
  if out = "New" ∧ elic = true then some (limNext lim (sadd now (delay m))) else lim

/-- If packets await an acknowledgement a deadline is set, and it is no later than the delay after the oldest of
them unless that point is already behind the clock `clk`. -/
def Owed (x : X) (lim : Option Nat) (clk : Nat) : Prop :=
  (x.pending = 0 → lim = none) ∧ (0 < x.pending → ∃ d l, x.due = some d ∧ lim = some l ∧ d ≤ max l clk)

theorem max_mono (l clk now : Nat) : max l clk ≤ max l (max clk now) :=
  Nat.max_le.2 ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)⟩

theorem due_step (now due2 clk p0 : Nat) (hn : now ≤ due2) (fire : Bool) (od lim : Option Nat)
    (h1 : p0 = 0 → lim = none) (h2 : 0 < p0 → ∃ d l, od = some d ∧ lim = some l ∧ d ≤ max l clk) :
    dueNext fire now due2 od ≤ max (limNext lim due2) (max clk now) := by
  unfold dueNext limNext
  by_cases hf : fire = true
  · rw [if_pos hf]
    exact Nat.le_trans (Nat.le_max_right clk now) (Nat.le_max_right _ _)
  · rw [if_neg hf]
    by_cases hp : p0 = 0
    · rw [h1 hp]
      cases od with
      | none => dsimp only; exact Nat.le_max_left _ _
      | some d0 =>
        dsimp only
        by_cases hlt : due2 < d0
        · rw [if_pos hlt]; exact Nat.le_max_left _ _
        · rw [if_neg hlt]; exact Nat.le_trans (Nat.le_of_not_lt hlt) (Nat.le_max_left _ _)
    · obtain ⟨d, l, e1, e2, e3⟩ := h2 (Nat.pos_of_ne_zero hp)
      rw [e1, e2]
      dsimp only
      by_cases hlt : due2 < d
      · rw [if_pos hlt]
        by_cases hl : due2 ≤ l
        · rw [Nat.min_eq_right hl]; exact Nat.le_max_left _ _
        · have hl' : l < due2 := Nat.lt_of_not_le hl
          have hdc : d ≤ clk := by
            rcases Nat.le_total l clk with h | h
            · rw [Nat.max_eq_right h] at e3; exact e3
            · rw [Nat.max_eq_left h] at e3; exact absurd (Nat.lt_of_lt_of_le hlt e3) (by omega)
          exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_lt_of_le hlt hdc))
            (Nat.le_trans (Nat.le_max_left clk now) (Nat.le_max_right _ _))
      · rw [if_neg hlt]
        have hge : d ≤ due2 := Nat.le_of_not_lt hlt
        rcases Nat.le_total l clk with h | h
        · rw [Nat.max_eq_right h] at e3
          exact Nat.le_trans e3 (Nat.le_trans (Nat.le_max_left clk now) (Nat.le_max_right _ _))
        · rw [Nat.max_eq_left h] at e3
          exact Nat.le_trans (Nat.le_min.2 ⟨e3, hge⟩) (Nat.le_max_left _ _)

theorem owed_receive (x : X) (p : Rx) (lim : Option Nat) (clk : Nat) (hnow : p.now ≤ top) (ho : Owed x lim clk) :
    ∀ out y, receive x p = (out, y) →
      Owed y (limAfter lim out p.elic p.now x.mrtt) (max clk p.now) := by
  intro out y h
  obtain ⟨o1, o2⟩ := ho
  have keep : ∀ (y : X), y.pending = x.pending → y.due = x.due → out ≠ "New" ∨ p.elic = false →
      Owed y (limAfter lim out p.elic p.now x.mrtt) (max clk p.now) := by
    intro y hp hd hn
    have : limAfter lim out p.elic p.now x.mrtt = lim := by
      unfold limAfter
      rcases hn with hn | hn
      · simp [hn]
      · simp [hn]
    rw [this]
    refine ⟨fun h0 => o1 (by omega), fun h0 => ?_⟩
    obtain ⟨d, l, e1, e2, e3⟩ := o2 (by omega)
    exact ⟨d, l, by rw [hd]; exact e1, e2, Nat.le_trans e3 (max_mono l clk p.now)⟩
  unfold receive at h
  by_cases hm : maxpn < p.pn
  · rw [if_pos hm] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact keep x rfl rfl (Or.inl (by decide))
  · rw [if_neg hm] at h
    rcases hins : insert x p.pn with ⟨ok, y0⟩
    simp only [hins] at h
    obtain ⟨k1, k2, k3, k4, k5⟩ := insert_keeps x p.pn ok y0 hins
    by_cases hok : ok = true
    · subst hok
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
      by_cases he : p.elic = true
      · simp only [he, Bool.not_true, Bool.false_eq_true, if_false] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [limAfter, he, and_self, if_true]
        have hd : p.now ≤ sadd p.now (delay x.mrtt) := by
          unfold sadd; exact Nat.le_min.2 ⟨Nat.le_add_right _ _, hnow⟩
        refine ⟨fun hp => ?_, fun _ => ?_⟩
        · exfalso
          have : 0 < min (y0.pending + 1) u32max := Nat.lt_min.2 ⟨Nat.succ_pos _, by unfold u32max; decide⟩
          exact absurd hp (Nat.ne_of_gt this)
        · refine ⟨_, _, rfl, rfl, ?_⟩
          rw [k3]
          rw [k2]
          exact due_step p.now (sadd p.now (delay x.mrtt)) clk x.pending hd _ x.due lim o1 o2
      · have : p.elic = false := by simpa using he
        simp only [this, Bool.not_false, if_true] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact keep _ k1 k2 (Or.inr this)
    · have : ok = false := by simpa using hok
      subst this
      simp only [Bool.not_false, if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact keep _ k1 k2 (Or.inl (by decide))

theorem owed_ackSent (x : X) (lim : Option Nat) (clk apn now : Nat) (ho : Owed x lim clk) :
    Owed (ackSent x apn now) (if (largest x).isSome then none else lim) clk := by
  unfold ackSent
  cases hl : largest x with
  | none => simpa [hl] using ho
  | some lg =>
    simp only [hl, Option.isSome_some, if_true]
    exact ⟨fun _ => rfl, fun h => by simp at h⟩

theorem peerAck_cases (x : X) (now : Nat) (rgs : List Iv) : ∀ r, peerAck x now rgs = r → r = x ∨ ∃ lg best, r =
      { x with sent := x.sent.filter (fun e => decide (lg < e.1)),
               conf := if x.conf.length < confn then x.conf ++ [(now, best)] else x.conf } := by
  intro r h
  unfold peerAck at h
  split at h
  · exact Or.inl h.symm
  · split at h
    · exact Or.inl h.symm
    · exact Or.inr ⟨_, _, h.symm⟩

theorem peerAck_keeps (x : X) (now : Nat) (rgs : List Iv) :
    (peerAck x now rgs).pending = x.pending ∧ (peerAck x now rgs).due = x.due := by
  rcases peerAck_cases x now rgs _ rfl with h | ⟨lg, best, h⟩
  · rw [h]; exact ⟨rfl, rfl⟩
  · rw [h]; exact ⟨rfl, rfl⟩

/-- Setting the round trip or the interval and taking the peer's acknowledgements leave the owed deadline alone. -/
theorem owed_other (x : X) (lim : Option Nat) (clk : Nat) (ho : Owed x lim clk) :
    (∀ m, Owed (setMinRtt x m) lim clk) ∧ (∀ e, Owed (setEvery x e) lim clk) ∧
      (∀ now rgs, Owed (peerAck x now rgs) lim clk) := by
  refine ⟨fun m => ho, fun e => ho, fun now rgs => ?_⟩
  obtain ⟨k1, k2⟩ := peerAck_keeps x now rgs
  obtain ⟨o1, o2⟩ := ho
  exact ⟨fun h => o1 (by omega), fun h => by
    obtain ⟨d, l, e1, e2, e3⟩ := o2 (by omega)
    exact ⟨d, l, by rw [k2]; exact e1, e2, e3⟩⟩

/-- An acknowledgement is due once the delay after the oldest packet it owes has passed. -/
theorem ack_due_after_delay (x : X) (lim : Option Nat) (clk T l : Nat) (ho : Owed x lim clk) (hp : 0 < x.pending)
    (hT : clk ≤ T) (hl : lim = some l) (hlT : l ≤ T) : ackDue x T = true := by
  obtain ⟨_, o2⟩ := ho
  obtain ⟨d, l', e1, e2, e3⟩ := o2 hp
  rw [hl] at e2
  simp at e2
  subst e2
  unfold ackDue ackDeadline
  have : (x.pending == 0) = false := by simp; omega
  simp only [this, Bool.false_eq_true, if_false, e1]
  simp only [decide_eq_true_eq]
  exact Nat.le_trans e3 (Nat.max_le.2 ⟨hlT, hT⟩)

theorem dueNext_fire (now due2 : Nat) (od : Option Nat) : dueNext true now due2 od = now := by simp [dueNext]

theorem ackRanges_length_le (x : X) (now : Nat) : (ackRanges x now).length ≤ maxack := by
  unfold ackRanges
  simp only [List.length_map, List.length_take]
  by_cases h : onlyNewest x now = true
  · rw [if_pos h]; unfold maxack; omega
  · rw [if_neg h]; exact Nat.min_le_left _ _

theorem ackRanges_ne_nil (x : X) (now : Nat) (h : x.items ≠ []) : ackRanges x now ≠ [] := by
  unfold ackRanges
  intro hnil
  have h1 := congrArg List.length hnil
  simp only [List.length_map, List.length_take, List.length_reverse, List.length_nil] at h1
  have hpos : 0 < x.items.length := Nat.pos_of_ne_zero (fun h0 => h (List.eq_nil_of_length_eq_zero h0))
  by_cases ho : onlyNewest x now = true
  · rw [if_pos ho] at h1; omega
  · rw [if_neg ho] at h1; unfold maxack at h1; omega

theorem sentTrim_len (s : List Iv) (h : s.length ≤ sentn) : (sentTrim s ++ [(0, 0)]).length ≤ sentn := by
  have hs : 0 < sentn := by unfold sentn; decide
  unfold sentTrim
  by_cases hh : (s.length == sentn) = true
  · rw [if_pos hh]
    simp only [beq_iff_eq] at hh
    simp only [List.length_append, List.length_drop, List.length_singleton]
    omega
  · rw [if_neg hh]
    simp only [beq_iff_eq] at hh
    simp only [List.length_append, List.length_singleton]
    omega

theorem ackSent_tables (x : X) (apn now : Nat) (h1 : x.sent.length ≤ sentn) (h2 : x.conf.length ≤ confn) :
    (ackSent x apn now).sent.length ≤ sentn ∧ (ackSent x apn now).conf.length ≤ confn := by
  unfold ackSent
  cases hl : largest x with
  | none => exact ⟨h1, h2⟩
  | some lg =>
    refine ⟨?_, ?_⟩
    · have := sentTrim_len x.sent h1
      simpa using this
    · show (x.conf.drop (aged x.conf now).length).length ≤ confn
      rw [List.length_drop]; omega

theorem peerAck_tables (x : X) (now : Nat) (rgs : List Iv) (h1 : x.sent.length ≤ sentn) (h2 : x.conf.length ≤ confn) :
    (peerAck x now rgs).sent.length ≤ sentn ∧ (peerAck x now rgs).conf.length ≤ confn := by
  rcases peerAck_cases x now rgs _ rfl with h | ⟨lg, best, h⟩
  · rw [h]; exact ⟨h1, h2⟩
  · rw [h]
    refine ⟨Nat.le_trans (List.length_filter_le _ _) h1, ?_⟩
    show (if x.conf.length < confn then x.conf ++ [(now, best)] else x.conf).length ≤ confn
    by_cases hc : x.conf.length < confn
    · rw [if_pos hc]; simp only [List.length_append, List.length_singleton]; omega
    · rw [if_neg hc]; exact h2

end Vinc.TransportRx
