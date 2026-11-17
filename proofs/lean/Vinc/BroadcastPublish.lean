import Vinc.Axioms

/-!
# The publish timing arithmetic

The timing and sizing arithmetic of `vinc-broadcast/src/publish.rs` (`pub_retry`, `pending_deadline`,
`fallback_step`) with the constants of `consts.rs`, proved for general parameters and then for the real values.
All instants are `Nat` nanoseconds; `Nat` subtraction truncates at 0, which is `saturating_sub`.

A pending publish is `P`: its start `t0`, its `next` retry instant and its retry counter `idx`. The host runs the
timer exactly at `deadline` (`pending_deadline`: the earlier of `next` and `t0 + giveup + 1`). `fire` is `pub_retry`
at that instant: give up when the publish is strictly older than `giveup`, else retry when `next` is due, moving
`next` to `now + retry` and counting the retry. The model assumes a non-empty hub list and `retry > 0`; the empty
hub list gives up at once and a zero retry is not a configuration (`PUB_RETRY` is a constant).

`states` is the publish after `j` timer firings. Its closed form (`states_closed`) is the base of the theorems:
`giveup_first`, `giveup_scheduled` (given up at `t0 + giveup + 1` and not before), `retries_count` (exactly
`giveup / retry` retries, the last at `t0 + giveup` when `retry` divides `giveup`), `retry_hub` and `hub_reached`
(the retry `k` goes to hub `k mod n` and every hub is tried within `n` retries), `fallback_steps` and
`fallback_ceiling` (the member-to-member fallback sends at most `batch` per step, one step at publish and one per
retry), `pending_bounded`, and the floor arithmetic among the constants.
-/

namespace Vinc.BroadcastPublish

theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by simp [h]
theorem ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : (if c then a else b) = b := by simp [h]

/-! ## The retry schedule -/

structure P where
  t0 : Nat
  next : Nat
  idx : Nat

/-- `pending_deadline` for one publish. -/
def deadline (g : Nat) (p : P) : Nat := min p.next (p.t0 + g + 1)

/-- `pub_retry` for one publish at instant `now`: `none` is given up. -/
def step (r g : Nat) (p : P) (now : Nat) : Option P :=
  if now - p.t0 > g then none
  else if now ≥ p.next then some { p with next := now + r, idx := p.idx + 1 }
  else some p

/-- The host runs the timer exactly at the deadline. -/
def fire (r g : Nat) (p : P) : Option P := step r g p (deadline g p)

/-- The publish after `j` timer firings, from `publish` at `t0` (`next = t0 + retry`, `idx = 0`). -/
def states (r g t0 : Nat) : Nat → Option P
  | 0 => some ⟨t0, t0 + r, 0⟩
  | j + 1 => (states r g t0 j).bind (fire r g)

/-- The instants of the retries before the give-up: `t0 + k * retry` for `k = 1, 2, ...` while `k * retry <= giveup`. -/
def retryTimes (t0 r g : Nat) : List Nat := (List.range (g / r)).map fun i => t0 + (i + 1) * r

/-- Given up exactly when strictly older than `giveup`, from the first instant `t0 + giveup + 1`. -/
theorem giveup_first (r g : Nat) (p : P) :
    (∀ now, step r g p now = none ↔ p.t0 + g < now) ∧ step r g p (p.t0 + g + 1) = none ∧
      ∀ now ≤ p.t0 + g, step r g p now ≠ none := by
  have key : ∀ now, step r g p now = none ↔ p.t0 + g < now := by
    intro now
    unfold step
    split <;> (try split) <;> simp <;> omega
  exact ⟨key, (key _).2 (by omega), fun now h hn => by have := (key now).1 hn; omega⟩

theorem states_closed (r g t0 : Nat) (hr : 0 < r) (j : Nat) :
    states r g t0 j = if j * r ≤ g then some ⟨t0, t0 + (j + 1) * r, j⟩ else none := by
  induction j with
  | zero => simp [states]
  | succ j ih =>
    simp only [states, ih]
    have e : (j + 1) * r = j * r + r := Nat.succ_mul j r
    by_cases h : j * r ≤ g
    · rw [ite_t h, Option.bind_some]
      simp only [fire, step, deadline, e]
      by_cases h2 : j * r + r ≤ g
      · have : min (t0 + (j * r + r)) (t0 + g + 1) = t0 + (j * r + r) := by omega
        simp only [this, ite_t h2]
        rw [ite_f (by omega), ite_t (by omega)]
        simp only [Nat.add_mul, Nat.one_mul]
        congr 2; omega
      · have : min (t0 + (j * r + r)) (t0 + g + 1) = t0 + g + 1 := by omega
        rw [this, ite_f h2, ite_t (by omega)]
    · rw [ite_f h, Option.bind_none, ite_f (by omega)]

/-- The give-up is scheduled at `t0 + giveup + 1`: the last live state has that deadline, the next is given up. -/
theorem giveup_scheduled (r g t0 : Nat) (hr : 0 < r) :
    ∃ p, states r g t0 (g / r) = some p ∧ deadline g p = t0 + g + 1 ∧ states r g t0 (g / r + 1) = none := by
  have h1 : g / r * r ≤ g := Nat.div_mul_le_self g r
  have h2 : g < (g / r + 1) * r := by
    have := Nat.lt_div_mul_add (a := g) hr
    rw [Nat.succ_mul]; omega
  refine ⟨⟨t0, t0 + (g / r + 1) * r, g / r⟩, ?_, ?_, ?_⟩
  · rw [states_closed r g t0 hr, ite_t h1]
  · simp only [deadline]; omega
  · rw [states_closed r g t0 hr, ite_f (by omega)]

theorem mem_retryTimes (t0 r g x : Nat) (hr : 0 < r) :
    x ∈ retryTimes t0 r g ↔ ∃ k, 1 ≤ k ∧ k * r ≤ g ∧ x = t0 + k * r := by
  unfold retryTimes
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i + 1, by omega, (Nat.le_div_iff_mul_le hr).1 hi, rfl⟩
  · rintro ⟨k, hk, hkg, rfl⟩
    exact ⟨k - 1, by have := (Nat.le_div_iff_mul_le hr).2 hkg; omega, by congr 2; omega⟩

/-- Each scheduled retry is a firing of the timer at `t0 + k * retry` that counts retry `k`. -/
theorem retry_fires (r g t0 : Nat) (hr : 0 < r) (j : Nat) (hj : (j + 1) * r ≤ g) :
    ∃ p q, states r g t0 j = some p ∧ deadline g p = t0 + (j + 1) * r ∧ states r g t0 (j + 1) = some q ∧
      q.idx = j + 1 := by
  have e : (j + 1) * r = j * r + r := Nat.succ_mul j r
  refine ⟨⟨t0, t0 + (j + 1) * r, j⟩, ⟨t0, t0 + (j + 1 + 1) * r, j + 1⟩, ?_, ?_, ?_, rfl⟩
  · rw [states_closed r g t0 hr, ite_t (by omega)]
  · simp only [deadline]; omega
  · rw [states_closed r g t0 hr, ite_t hj]

/-- Exactly `giveup / retry` retries before the give-up, the last at `t0 + giveup` when `retry` divides `giveup`. -/
theorem retries_count (t0 r g : Nat) (hr : 0 < r) (hd : r ∣ g) (hg : 0 < g) :
    (retryTimes t0 r g).length = g / r ∧ (retryTimes t0 r g).getLast? = some (t0 + g) := by
  refine ⟨by simp [retryTimes], ?_⟩
  obtain ⟨q, rfl⟩ := hd
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · simp at hg
    · exact h
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp [retryTimes, List.range_succ, Nat.mul_div_cancel_left _ hr, Nat.mul_comm]

/-! ## Which hub -/

/-- The hub index of retry `k` (counted from 1): `p.idx % n` after `idx += 1`. -/
def hubOf (n k : Nat) : Nat := k % n

theorem retry_hub (n : Nat) (hn : 0 < n) (k0 i : Nat) (hi : i < n) :
    ∃ k, k0 < k ∧ k ≤ k0 + n ∧ hubOf n k = i := by
  unfold hubOf
  have hd := Nat.div_add_mod k0 n
  have hm := Nat.mod_lt k0 hn
  by_cases h : k0 % n < i
  · refine ⟨i + n * (k0 / n), by omega, by omega, ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  · refine ⟨i + n * (k0 / n) + n, by omega, by omega, ?_⟩
    rw [show i + n * (k0 / n) + n = i + n * (k0 / n + 1) by rw [Nat.mul_succ]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]

/-- A reachable hub gets a PUB within `n` retries, so within `retry * n` of the publish, if that is within `giveup`. -/
theorem hub_reached (t0 r g n i : Nat) (hn : 0 < n) (hi : i < n) (hng : n * r ≤ g) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ k * r ≤ g ∧ hubOf n k = i ∧ t0 + k * r ≤ t0 + r * n := by
  obtain ⟨k, h1, h2, h3⟩ := retry_hub n hn 0 i hi
  refine ⟨k, by omega, by omega, Nat.le_trans (Nat.mul_le_mul_right r (by omega)) hng, h3, ?_⟩
  rw [Nat.mul_comm r n]; have := Nat.mul_le_mul_right r (show k ≤ n by omega); omega

/-! ## The member-to-member fallback -/

/-- Subscribers sent after `s` steps when each step sends the next `batch` of the `total` reachable, none twice. -/
def fbIter (batch total : Nat) : Nat → Nat
  | 0 => 0
  | s + 1 => fbIter batch total s + min batch (total - fbIter batch total s)

/-- The `ceil(a / b)`. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The instant of fallback step `s` (counted from 1): step 1 at the publish, one more at each retry. -/
def fbTime (t0 r s : Nat) : Nat := t0 + r * (s - 1)

theorem fbIter_eq (batch total s : Nat) : fbIter batch total s = min total (batch * s) := by
  induction s with
  | zero => simp [fbIter]
  | succ s ih => rw [fbIter, ih, Nat.mul_succ]; omega

theorem fbStep_le (batch total s : Nat) : fbIter batch total (s + 1) - fbIter batch total s ≤ batch := by
  rw [fbIter]; omega

theorem ceilDiv_mul (a b : Nat) (hb : 0 < b) : a ≤ b * ceilDiv a b := by
  have := Nat.div_add_mod (a + b - 1) b
  have := Nat.mod_lt (a + b - 1) hb
  unfold ceilDiv; omega

/-- After `s` steps at most `batch * s` subscribers were sent (and never more than there are); with `total`
reachable subscribers all are sent after `ceil(total / batch)` steps, by `t0 + retry * (ceil - 1)`. -/
theorem fallback_steps (batch total s t0 r : Nat) (hb : 0 < batch) :
    fbIter batch total s ≤ batch * s ∧ fbIter batch total s ≤ total ∧
      fbIter batch total (ceilDiv total batch) = total ∧
      fbTime t0 r (ceilDiv total batch) = t0 + r * (ceilDiv total batch - 1) := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [fbIter_eq]; omega
  · rw [fbIter_eq]; omega
  · rw [fbIter_eq]; have := ceilDiv_mul total batch hb; omega

theorem fbTime_one (t0 r : Nat) : fbTime t0 r 1 = t0 := by simp [fbTime]

/-- Only the steps that fit before the give-up happen: at most `giveup / retry + 1`, so at most
`batch * (giveup / retry + 1)` subscribers are reached. -/
theorem fallback_ceiling (batch total t0 r g s : Nat) (hr : 0 < r) (hs : 1 ≤ s) (ht : fbTime t0 r s ≤ t0 + g) :
    s ≤ g / r + 1 ∧ fbIter batch total s ≤ batch * (g / r + 1) := by
  have h1 : s ≤ g / r + 1 := by
    have : (s - 1) * r ≤ g := by unfold fbTime at ht; rw [Nat.mul_comm]; omega
    have := (Nat.le_div_iff_mul_le hr).2 this; omega
  exact ⟨h1, by rw [fbIter_eq]; exact Nat.le_trans (by omega) (Nat.mul_le_mul_left batch h1)⟩

/-! ## The pending list -/

/-- A publish is tracked only below the bound (`self.pending.len() < PENDING_MAX`). -/
def push (cap : Nat) (l : List Nat) (x : Nat) : List Nat := if l.length < cap then x :: l else l

/-- An operation on the list: `some x` publishes, `none` removes the head (a hub ack or a give-up). -/
def run (cap : Nat) (l : List Nat) : Option Nat → List Nat
  | some x => push cap l x
  | none => l.tail

theorem push_bounded (cap : Nat) (l : List Nat) (x : Nat) (h : l.length ≤ cap) : (push cap l x).length ≤ cap := by
  unfold push; split <;> simp_all <;> omega

/-- `Topics::publish` on the list: `none` is `Refused::Backlog`, returned to the caller when the list is full;
`some` is the list with the new publish tracked. -/
def publish (cap : Nat) (l : List Nat) (x : Nat) : Option (List Nat) := if l.length < cap then some (x :: l) else none

/-- A publish the caller is answered for with an id is in the list, and the list stays within `cap`. -/
theorem publish_tracked (cap : Nat) (l l' : List Nat) (x : Nat) (hp : publish cap l x = some l') :
    x ∈ l' ∧ l'.length ≤ cap := by
  unfold publish at hp
  split at hp
  · cases hp; simp; omega
  · cases hp

/-- The caller is refused exactly when the list is full. -/
theorem publish_refused_iff (cap : Nat) (l : List Nat) (x : Nat) : publish cap l x = none ↔ cap ≤ l.length := by
  unfold publish; split <;> simp_all <;> omega

/-- The finding behind the fix: the old `push` with a full list leaves a new publish out of it, so the publish was
answered with an id and never retried, acknowledged or given up. -/
theorem push_drops (cap : Nat) (l : List Nat) (x : Nat) (hf : cap ≤ l.length) (hx : x ∉ l) : x ∉ push cap l x := by
  unfold push; split
  · omega
  · exact hx

/-- Starting empty, any sequence of publishes and removals keeps the list within `cap`. -/
theorem pending_bounded (cap : Nat) (ops : List (Option Nat)) : (ops.foldl (run cap) []).length ≤ cap := by
  suffices ∀ l, l.length ≤ cap → (ops.foldl (run cap) l).length ≤ cap from this [] (by simp)
  induction ops with
  | nil => intro l h; exact h
  | cons o ops ih =>
    intro l h
    apply ih
    cases o with
    | some x => exact push_bounded cap l x h
    | none => simp [run]; omega

/-! ## An acknowledgement is for the publisher's own message

`on_pack` ends the pending publish with the id it names, so the hub must name an id only for the message it stored
under it. A hub whose log holds the id for another message (`rival`) sends no acknowledgement (`acks`), so when every
hub holds the id for another message the publish is never acknowledged and ends in the give-up
(`taken_never_acked`, with the give-up instant `giveup_scheduled`). The old rule acknowledged any known id
(`acksById`): `old_rule_acks_rival` is its witness. -/

/-- A hub sends a PACK for the id when it stored this message: not when another message holds the id. -/
def acks (rival : Nat → Bool) (h : Nat) : Bool := !rival h

/-- The old rule: any known id was acknowledged. -/
def acksById (_rival : Nat → Bool) (_h : Nat) : Bool := true

theorem taken_never_acked (hubs : List Nat) (rival : Nat → Bool) (hall : ∀ h ∈ hubs, rival h = true) :
    ∀ h ∈ hubs, acks rival h = false := by
  intro h hh
  simp [acks, hall h hh]

theorem old_rule_acks_rival (rival : Nat → Bool) (h : Nat) (hr : rival h = true) :
    acksById rival h = true ∧ acks rival h = false := by
  simp [acksById, acks, hr]

/-! ## The constants of `consts.rs` -/

def S : Nat := 1000000000
def PUB_RETRY : Nat := 3 * S
def PUB_GIVEUP : Nat := 90 * S
def LOG_WINDOW : Nat := 120 * S
def LOG_CAP : Nat := 2048
def SEEN_TTL : Nat := 600 * S
def SEEN_CAP : Nat := 8192
def AE_FROM : Nat := 30 * S
def GAP_EVERY : Nat := 20 * S
def GAP_SPAN : Nat := 25 * S
def FHOLD_MAX : Nat := 256
def HELD_MAX : Nat := 64
def PENDING_MAX : Nat := 1024
def FALLBACK_BATCH : Nat := 8
def DEFAULT_MAX_SUBSCRIBERS : Nat := 256

theorem retry_divides_giveup : PUB_RETRY ∣ PUB_GIVEUP := ⟨30, by decide⟩
theorem retries_real : PUB_GIVEUP / PUB_RETRY = 30 := by decide

/-- With the real constants: 30 retries, the last at `t0 + 90 s`; given up at `t0 + 90 s + 1 ns`. -/
theorem retries_count_real (t0 : Nat) :
    (retryTimes t0 PUB_RETRY PUB_GIVEUP).length = 30 ∧
      (retryTimes t0 PUB_RETRY PUB_GIVEUP).getLast? = some (t0 + PUB_GIVEUP) := by
  have := retries_count t0 PUB_RETRY PUB_GIVEUP (by decide) retry_divides_giveup (by decide)
  rwa [retries_real] at this

theorem giveup_real (t0 : Nat) :
    ∃ p, states PUB_RETRY PUB_GIVEUP t0 30 = some p ∧ deadline PUB_GIVEUP p = t0 + PUB_GIVEUP + 1 ∧
      states PUB_RETRY PUB_GIVEUP t0 31 = none := by
  have := giveup_scheduled PUB_RETRY PUB_GIVEUP t0 (by decide)
  rwa [retries_real] at this

/-- At most `8 * (30 + 1) = 248` subscribers are reached before the give-up. -/
theorem fallback_ceiling_real : FALLBACK_BATCH * (PUB_GIVEUP / PUB_RETRY + 1) = 248 := by decide

theorem fallback_ceiling_lt_cap : FALLBACK_BATCH * (PUB_GIVEUP / PUB_RETRY + 1) < DEFAULT_MAX_SUBSCRIBERS := by decide

/-- With a full subscriber table the fallback still reaches exactly 248. -/
theorem fallback_full_table : fbIter FALLBACK_BATCH DEFAULT_MAX_SUBSCRIBERS (PUB_GIVEUP / PUB_RETRY + 1) = 248 := by
  decide

/-- The late publish (cut off from every hub, subscribers reachable): the first subscribers are sent at the publish
instant, and for up to 168 subscribers all are sent within `t0 + 60 s`. -/
theorem late_publish (t0 s : Nat) (hs : s ≤ 168) :
    fbTime t0 PUB_RETRY 1 = t0 ∧ fbIter FALLBACK_BATCH s (ceilDiv s FALLBACK_BATCH) = s ∧
      fbTime t0 PUB_RETRY (ceilDiv s FALLBACK_BATCH) ≤ t0 + 60 * S := by
  refine ⟨fbTime_one _ _, ?_, ?_⟩
  · have := (fallback_steps FALLBACK_BATCH s s t0 PUB_RETRY (by decide)).2.2.1; exact this
  · have h : ceilDiv s FALLBACK_BATCH ≤ 21 := by unfold ceilDiv FALLBACK_BATCH; omega
    unfold fbTime PUB_RETRY S
    have : PUB_RETRY * 1 ≤ PUB_RETRY * 1 := Nat.le_refl _
    omega

/-- Two consecutive periodic gap checks overlap: the span asked about exceeds the period. -/
theorem gap_span_covers_period : GAP_EVERY < GAP_SPAN := by decide
theorem ae_window_inside_log : AE_FROM < LOG_WINDOW := by decide
theorem seen_ttl_gt_log_window : LOG_WINDOW < SEEN_TTL := by decide
theorem seen_cap_ge_log_cap_times_two : 2 * LOG_CAP ≤ SEEN_CAP := by decide
theorem held_max_le_fhold_max : HELD_MAX ≤ FHOLD_MAX := by decide
theorem pending_max_value : PENDING_MAX = 1024 := rfl

end Vinc.BroadcastPublish
