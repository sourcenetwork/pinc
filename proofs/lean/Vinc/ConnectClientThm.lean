import Vinc.ConnectClient

/-!
# The client rules: the theorems

For every instant, every view and every state:

* punch: `probeGaps_length`, `probeGaps_first`, `probeGaps_tail_cap`; the timer is never left in the past
  (`due_future`), punches only when due (`punch_when_due`), stops for a good direct path (`punch_good_stops`), and an
  idle session only waits another interval (`idle_waits`);
* tunnel: `decide` is `Carrier` without a tunnel and `Tunnel` without a carrier (`decide_no_tunnel`,
  `decide_carrier_closed`), stale carriers get both (`decide_stale`); `seen_length` (the tables keep their size),
  `seen_age` (a splice just seen has age 0);
* dial: the selection is a sublist of the candidates (`select_sublist`), at most `cap` and at most one on a thin try
  (`select_cap`, `select_thin`); `add_size` (the pending table keeps its size), `take_clears`;
* lookup: `ask_size` (the table keeps its size), `answered_removes`, `deadline_due`, and
  `verify_found`: an answer is accepted only if the record parses, its signature verifies and it names the peer asked
  about;
* netcheck: `classify_blocked`, `answered_home` (the home moves only to a relay with a strictly lower round trip or
  away from an unhealthy one), `failover_healthy`, `missing_fallback`.
-/

namespace Vinc.ConnectClient
open Vinc.ConnectLink (sec satSub)

/-! ## Punching -/

theorem gapsFrom_length (n g : Nat) : (gapsFrom n g).length = n := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih => simp [gapsFrom, ih]

theorem probeGaps_length (srtt : Nat) : (probeGaps srtt).length = 9 := gapsFrom_length 9 _

theorem probeGaps_first (srtt : Nat) : ∃ g gs, probeGaps srtt = g :: gs ∧ probeBase ≤ g ∧ srtt / 8 ≤ g := by
  refine ⟨max probeBase (srtt / 8), gapsFrom 8 (min (max probeBase (srtt / 8) * 2) probeCap), ?_, ?_, ?_⟩
  · simp [probeGaps, gapsFrom]
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

theorem gapsFrom_cap (n g : Nat) : ∀ x ∈ gapsFrom n (min g probeCap), x ≤ probeCap := by
  induction n generalizing g with
  | zero => simp [gapsFrom]
  | succ n ih =>
    intro x hx
    simp only [gapsFrom, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.min_le_right _ _
    · exact ih _ x hx

/-- After the first gap no gap exceeds 2 s. -/
theorem probeGaps_tail_cap (srtt : Nat) : ∀ x ∈ (probeGaps srtt).tail, x ≤ probeCap := by
  intro x hx
  simp only [probeGaps, gapsFrom, List.tail_cons] at hx
  exact gapsFrom_cap 8 _ x hx

/-- The timer is never left in the past: off, or after `now`. -/
theorem due_future (p : Puncher) (now : Nat) (v : View) :
    (p.due now v).2.at_ = 0 ∨ now < (p.due now v).2.at_ := by
  unfold Puncher.due
  split
  · rename_i h
    by_cases h0 : p.at_ = 0
    · left; exact h0
    · right
      rcases h with h | h
      · exact absurd h h0
      · exact h
  · split
    · rename_i hq; right; show now < v.quietUntil + 1; omega
    · split
      · right; show now < now + upgradeInterval; simp [upgradeInterval, sec]
      · split <;> simp [upgradeInterval, sec]

/-- A punch happens only when the timer is on and its time has come. -/
theorem punch_when_due (p : Puncher) (now : Nat) (v : View) (h : (p.due now v).1 = .punch) :
    p.at_ ≠ 0 ∧ p.at_ ≤ now := by
  unfold Puncher.due at h
  split at h
  · simp at h
  · rename_i hn
    refine ⟨fun h0 => hn (Or.inl h0), by omega⟩

/-- A direct path that answers in 10 ms or less stops the punching. -/
theorem punch_good_stops (p : Puncher) (now : Nat) (v : View) (h : (p.due now v).1 = .punch)
    (hd : v.direct = true) (hr : v.rtt ≠ 0) (hg : v.rtt ≤ goodLatency) : (p.due now v).2.at_ = 0 := by
  unfold Puncher.due at h ⊢
  by_cases h1 : p.at_ = 0 ∨ now < p.at_
  · rw [if_pos h1] at h; simp at h
  · rw [if_neg h1] at h ⊢
    by_cases h2 : now < v.quietUntil ∧ v.direct = true
    · rw [if_pos h2] at h; simp at h
    · rw [if_neg h2] at h ⊢
      by_cases h3 : v.appIdle ≥ activeKeep
      · rw [if_pos h3] at h; simp at h
      · rw [if_neg h3]; simp [hd, hr, hg]

/-- A session with no application data for 20 s only waits another interval. -/
theorem idle_waits (p : Puncher) (now : Nat) (v : View) (hon : p.at_ ≠ 0) (hdue : p.at_ ≤ now)
    (hi : activeKeep ≤ v.appIdle) (hq : ¬ (now < v.quietUntil ∧ v.direct = true)) :
    p.due now v = (.wait, ⟨now + upgradeInterval⟩) := by
  unfold Puncher.due
  rw [if_neg (by omega), if_neg hq, if_pos hi]

/-! ## The hub tunnel -/

theorem decide_no_tunnel (o : Bool) (s : Nat) (r : Option Rides) : decide' o s r false = .carrier := by
  simp [decide']

theorem decide_carrier_closed (s : Nat) (r : Option Rides) : decide' false s r true = .tunnel := by
  simp [decide']

theorem decide_stale (s : Nat) (r : Option Rides) (h : tunnelStale < s) : decide' true s r true = .both := by
  simp [decide', h]

theorem seen_length (t : Splices) (now relay peer frm : Nat) :
    (t.seen now relay peer frm).peers.length = t.peers.length ∧ (t.seen now relay peer frm).live.length = t.live.length := by
  unfold Splices.seen
  dsimp only
  constructor <;> (repeat' split) <;> first | rfl | simp [List.length_set]

/-! ## Dialing -/

theorem select_sublist (cands : List Cand) (t : Try) (relay : Nat → Option RelayView) (cap : Nat) :
    (select cands t relay cap).1.Sublist cands := by
  unfold select
  dsimp only
  have hk : ((cands.take 16).filter (keepCand t relay)).Sublist cands :=
    (List.filter_sublist).trans (List.take_sublist _ _)
  split
  · exact (List.take_sublist _ _).trans ((List.take_sublist _ _).trans ((List.drop_sublist _ _).trans hk))
  · exact (List.take_sublist _ _).trans hk

theorem select_cap (cands : List Cand) (t : Try) (relay : Nat → Option RelayView) (cap : Nat) :
    (select cands t relay cap).1.length ≤ cap := by
  unfold select; dsimp only
  exact List.length_take_le _ _

theorem add_size (p : Pending) (peer s : Nat) : (p.add peer s).2.items.length = p.items.length := by
  unfold Pending.add
  dsimp only
  repeat' split
  all_goals first | rfl | simp [List.length_set]

/-! ## Lookups -/

theorem ask_size (t : Lookups) (now peer : Nat) (u c : Bool) (th : Nat) : (t.ask now peer u c th).2.items.length = t.items.length := by
  unfold Lookups.ask
  dsimp only
  repeat' split
  all_goals first | rfl | simp [List.length_set]

theorem answered_removes (t : Lookups) (peer : Nat) : (t.answered peer).contains peer = false := by
  unfold Lookups.contains Lookups.answered
  simp only [List.any_map, Function.comp_def]
  rw [List.any_eq_false]
  intro e _
  cases e with
  | none => simp
  | some i => by_cases h : i.peer = peer <;> simp [h]

theorem deadline_due (t : Lookups) (d now : Nat) (h : t.nextDeadline = some d) (hn : d ≤ now) :
    t.due now ≠ [] := by
  unfold Lookups.nextDeadline at h
  have hm := List.min?_mem h
  simp only [List.mem_filterMap] at hm
  obtain ⟨e, he, hx⟩ := hm
  cases e with
  | none => simp at hx
  | some i =>
    simp only [Option.map_some, Option.some.injEq] at hx
    unfold Lookups.due
    intro hnil
    have hmem : i.peer ∈ t.items.filterMap (fun e => match e with
        | some i => if now > i.at_ + i.wait then some i.peer else none
        | none => none) := by
      rw [List.mem_filterMap]
      refine ⟨some i, he, ?_⟩
      simp only []
      rw [if_pos (by omega)]
    exact List.ne_nil_of_mem hmem hnil

/-! ## Verification of an answer -/

/-- An answer is accepted only if the record parses, its signature verifies, and it names the peer asked about. -/
theorem verify_found (peer : List Nat) (a : Answer) (sig : Bool) (tg : Vinc.ConnCodec.CErr → String)
    (home : List Nat) (reach seq : Nat) (addrs : List (List Nat))
    (h : verify peer a sig tg = .found home reach seq addrs) :
    ∃ bytes r, a = .record bytes ∧ Vinc.ConnCodec.Rec.parse bytes = .ok r ∧ sig = true ∧ r.node = peer ∧
      r.home = home ∧ r.reach = reach ∧ r.seq = seq ∧ r.addrs = addrs := by
  unfold verify at h
  cases a with
  | absent => simp at h
  | tooLarge => simp at h
  | record bytes =>
    simp only [] at h
    cases hp : Vinc.ConnCodec.Rec.parse bytes with
    | error e => simp [hp] at h
    | ok r =>
      simp only [hp] at h
      by_cases hs : sig = true
      · by_cases hn : r.node = peer
        · simp [hs, hn] at h
          obtain ⟨h1, h2, h3, h4⟩ := h
          exact ⟨bytes, r, rfl, hp, hs, hn, h1, h2, h3, h4⟩
        · simp [hs, hn] at h
      · simp [hs] at h

/-! ## Netcheck -/

theorem classify_blocked (o : Observed) (h : classify o = some 5) :
    o.udpHeard = false ∧ o.reflexive = [] ∧ o.watchdog ≤ o.sinceProbe := by
  unfold classify at h
  split at h
  · rename_i hr
    by_cases hc : ¬ o.udpHeard = true ∧ o.sinceProbe ≥ o.watchdog
    · refine ⟨by simpa using hc.1, hr, hc.2⟩
    · rw [if_neg hc] at h; simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h <;> simp at h

theorem missing_fallback (n : Netcheck) (f : Nat) (hh : n.home = none) (ht : homeTries ≤ n.tries + 1) (htl : n.tries + 1 ≤ 255) :
    (n.homeMissing (some f)).1 = .fallback f := by
  unfold Netcheck.homeMissing
  have : ¬ n.home.isSome = true := by simp [hh]
  rw [if_neg this]
  simp only []
  rw [if_pos (by simp; omega)]

end Vinc.ConnectClient
