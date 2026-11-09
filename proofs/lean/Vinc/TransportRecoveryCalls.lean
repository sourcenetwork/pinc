import Vinc.TransportRecoveryAcct

/-!
# Loss recovery: every call keeps the accounts

`Acct` (sent = acked + in flight + lost, the in-flight counters are the sums over the ring, the ghosts are counted
in `lost`) holds after `send`, `ack`, `timeout` and `flush` whatever the ring, the times and the earlier calls were.
The subtractions of the code (`in_flight -= size`, `lost -= size`, `in_flight_packets -= 1`) cannot underflow: the
sums bound them (`acct_move`, `acct_ack`, `acct_late`).
-/

namespace Vinc.TransportRecovery

theorem ackRange1_acct (p : P) (now a b : Nat) (x : X) (h : Acct x.r) : Acct (ackRange1 p now a b x).r := by
  unfold ackRange1
  exact ackRing_acct p now b _ _ _ h

theorem ackRanges_acct (p : P) (now : Nat) : ∀ (rgs : List (Nat × Nat)) (x : X), Acct x.r → Acct (ackRanges p now rgs x).r
  | [], x, a => by simpa [ackRanges] using a
  | (a0, b0) :: t, x, a => by
    unfold ackRanges
    split
    · exact a
    · split
      · exact a
      · split
        · exact a
        · exact ackRanges_acct p now t _ (ackRange1_acct p now a0 b0 x a)

theorem feq_ite (c : Prop) [Decidable c] (r a b : R) (ha : FEq r a) (hb : FEq r b) : FEq r (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem ackSeed_feq (p : P) (x : X) (now fl : Nat) : FEq x.r (ackSeed p x now fl).1 := by
  unfold ackSeed
  exact feq_ite _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ackSample_feq (p : P) (r4 : R) (npn ntime npath now fl : Nat) : FEq r4 (ackSample p r4 npn ntime npath now fl) := by
  unfold ackSample
  exact feq_ite _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ackFinish_acct (p : P) (x : X) (now fl : Nat) (a : Acct x.r) : Acct (ackFinish p x now fl).r := by
  have h1 := Acct.of_feq (ackSeed_feq p x now fl) a
  unfold ackFinish
  split
  · exact acct_trim p now _ h1
  · rename_i npn ntime npath _
    have h2 := Acct.of_feq (ackSample_feq p _ npn ntime npath now fl) h1
    exact acct_trim p now _ (detect_acct p _ now fl h2)

theorem ackStart_acct (p : P) (r : R) (now : Nat) (a : Acct r) : Acct (ackStart p r now).1 := by
  unfold ackStart
  dsimp only
  split <;> exact a

theorem ack_acct (p : P) (r : R) (now : Nat) (rgs : List (Nat × Nat)) (a : Acct r) : Acct (ack p r now rgs).r := by
  unfold ack
  dsimp only
  have a2 := ackRanges_acct p now rgs ⟨(ackStart p r now).1, [], {}, none, none, (ackStart p r now).2, "ok"⟩
    (ackStart_acct p r now a)
  split
  · exact a2
  · split
    · exact a2
    · exact ackFinish_acct p _ now _ a2

theorem send_acct (p : P) (r : R) (k : Pkt) (a : Acct r) : Acct (send p r k).r := by
  unfold send
  split
  · exact a
  · split
    · exact a
    · dsimp only
      have h1 : Acct { r with clock := max r.clock k.time, ring := trim p k.time r.ring } :=
        acct_trim p k.time { r with clock := max r.clock k.time } a
      split
      · exact h1
      · rename_i ring hp
        exact acct_push p _ _ ring rfl hp h1

theorem untracked_acct (r : R) (pn : Nat) (a : Acct r) : Acct (untracked r pn).r := by
  unfold untracked
  split <;> exact a

theorem flushLoop_acct (now : Nat) : ∀ (k i : Nat) (y : Y), Acct y.r → Acct (flushLoop now k i y).r
  | 0, i, y, a => by simpa [flushLoop] using a
  | k + 1, i, y, a => by
    unfold flushLoop
    rcases hs : y.r.ring[i]? with _ | sl
    · simpa using a
    · try dsimp only
      split
      · exact flushLoop_acct now k (i + 1) y a
      · rename_i h2
        have hst : sl.st = .fl := by simpa using h2
        refine flushLoop_acct now k (i + 1) _ ?_
        exact acct_move y.r i sl hs hst (fun s : Slot => { s with st := .lost, lostAt := now }) (fun _ => rfl)
          (Or.inl rfl) y.r.late a

theorem flush_acct (r : R) (now : Nat) (a : Acct r) : Acct (flush r now).r := by
  unfold flush
  dsimp only
  exact flushLoop_acct now _ 0 _ a

theorem firstIFFrom_spec : ∀ (l : List Slot) (n i : Nat), firstIFFrom l n = some i →
    n ≤ i ∧ ∃ sl, l[i - n]? = some sl ∧ sl.st = .fl
  | [], n, i, h => by simp [firstIFFrom] at h
  | s :: t, n, i, h => by
    unfold firstIFFrom at h
    split at h
    · rename_i hs
      simp at h
      subst h
      exact ⟨Nat.le_refl _, s, by simp, by simpa using hs⟩
    · obtain ⟨h1, sl, h2, h3⟩ := firstIFFrom_spec t (n + 1) i h
      refine ⟨by omega, sl, ?_, h3⟩
      have : i - n = (i - (n + 1)) + 1 := by omega
      rw [this]
      simpa using h2

theorem declareOldest_acct (p : P) (y : Y) (now : Nat) (a : Acct y.r) : Acct (declareOldest p y now).r := by
  unfold declareOldest
  split
  · exact a
  · rename_i i hi
    obtain ⟨_, sl0, h0, h1⟩ := firstIFFrom_spec _ 0 i hi
    simp at h0
    split
    · exact a
    · rename_i sl hs
      have e : sl = sl0 := by rw [h0] at hs; exact (Option.some.inj hs).symm
      subst e
      apply settle_acct
      dsimp only
      split
      · exact loseAt_acct p _ i now sl hs h1 a
      · exact loseAt_acct p _ i now sl hs h1 a

theorem timeoutLoss_acct (p : P) (r0 : R) (now : Nat) (a : Acct r0) : Acct (timeoutLoss p r0 now).r := by
  unfold timeoutLoss
  dsimp only
  split
  · split
    · exact detect_acct p _ now _ a
    · exact a
  · exact a

theorem timeout_acct (p : P) (r : R) (now : Nat) (a : Acct r) : Acct (timeout p r now).r := by
  unfold timeout
  dsimp only
  have h1 := timeoutLoss_acct p { r with clock := max r.clock now } now a
  repeat' split
  all_goals first | exact h1 | exact declareOldest_acct p _ now h1

end Vinc.TransportRecovery
