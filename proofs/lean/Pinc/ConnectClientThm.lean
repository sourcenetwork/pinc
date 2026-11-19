import Pinc.ConnectClient

/-!
# The client rules: the theorems

For every instant, every view and every state:

* punch: `probeGaps_length`, `probeGaps_first`, `probeGaps_tail_cap`; the timer is never left in the past
  (`due_future`), punches only when due (`punch_when_due`), stops for a good direct path (`punch_good_stops`), and an
  idle session only waits another interval (`idle_waits`);
* tunnel: `decide` is `Carrier` without a tunnel and `Tunnel` without a carrier (`decide_no_tunnel`,
  `decide_carrier_closed`), stale carriers get both (`decide_stale`); `seen_length` (the tables keep their size; that a splice just seen has age 0 is not proved in Lean yet);
* dial: the selection is a sublist of the candidates (`select_sublist`), at most `cap` (`select_cap`; at most one on a thin try
  is not proved in Lean yet); `add_size` (the pending table keeps its size; that `take` clears the entry of the peer is
  not proved in Lean yet);
* lookup: `ask_size` (the table keeps its size), `answered_removes`, `deadline_due`, and
  `verify_found`: an answer is accepted only if the record parses, its signature verifies and it names the peer asked
  about;
* netcheck: `classify_blocked`, `failover_healthy`, `missing_fallback`; after an answer a pinned relay that ever
  answered and is not unhealthy is the home (`answered_pin_home`, over `rehome_pin` and `rehome_only_home`), and
  otherwise (`answered_home_least`) the home is the relay with the lowest last round trip among those that ever answered
  and are not unhealthy, a tie to the one that answered first; `restart_keeps`: a link change keeps the home, that order
  and the rounds without a home.
-/

namespace Pinc.ConnectClient
open Pinc.ConnectLink (sec satSub)

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
theorem verify_found (peer : List Nat) (a : Answer) (sig : Bool) (tg : Pinc.ConnCodec.CErr → String)
    (home : List Nat) (reach seq : Nat) (addrs : List (List Nat))
    (h : verify peer a sig tg = .found home reach seq addrs) :
    ∃ bytes r, a = .record bytes ∧ Pinc.ConnCodec.Rec.parse bytes = .ok r ∧ sig = true ∧ r.node = peer ∧
      r.home = home ∧ r.reach = reach ∧ r.seq = seq ∧ r.addrs = addrs := by
  unfold verify at h
  cases a with
  | absent => simp at h
  | tooLarge => simp at h
  | record bytes =>
    simp only [] at h
    cases hp : Pinc.ConnCodec.Rec.parse bytes with
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

-- Choosing a home after an answer: when the pinned relay ever answered and is not unhealthy, it is the home, whatever
-- the round trips (the code's `pinned` short-cuts the round-trip comparison).
theorem rehome_pin (n : Netcheck) (p : Nat) (hp : n.pinOk = some p) : n.rehome.home = some p := by
  simp [Netcheck.rehome, hp]

-- Choosing a home changes nothing but the home: the probes, round trips, order, misses and the pin are left as they were.
theorem rehome_only_home (n : Netcheck) : ∃ h, n.rehome = { n with home := h } := by
  unfold Netcheck.rehome
  dsimp only
  repeat' split
  all_goals first | exact ⟨_, rfl⟩ | exact ⟨n.home, rfl⟩

-- Whether the pin is a candidate does not depend on the home.
theorem pinOk_home (n : Netcheck) (h : Option Nat) : ({ n with home := h } : Netcheck).pinOk = n.pinOk := rfl

-- An answer that was taken is a home choice over the state with the answer recorded.
theorem answered_rehome (n n' : Netcheck) (now relay addr rtt : Nat) (nonce : List Nat)
    (h : n.answered now relay nonce addr = (some rtt, n')) : ∃ n1 : Netcheck, n' = n1.rehome := by
  unfold Netcheck.answered at h
  split at h
  · split at h
    · simp at h
    · dsimp only at h
      exact ⟨_, (Prod.mk.inj h).2.symm⟩
  · simp at h

/-- After an answer, a pinned relay that ever answered a probe and is not unhealthy is the home. -/
theorem answered_pin_home (n n' : Netcheck) (now relay addr rtt p : Nat) (nonce : List Nat)
    (h : n.answered now relay nonce addr = (some rtt, n')) (hp : n'.pinOk = some p) : n'.home = some p := by
  obtain ⟨n1, rfl⟩ := answered_rehome n n' now relay addr rtt nonce h
  obtain ⟨hm, hq⟩ := rehome_only_home n1
  rw [hq, pinOk_home] at hp
  rw [← hq] at *
  exact rehome_pin n1 p hp

/-- The fold of `argMin` from a known best: the result is the best or a later element, and is least. -/
theorem argMin_fold (key : Nat → Nat) (l : List Nat) :
    ∀ (b x : Nat), l.foldl (fun acc i => match acc with
        | none => some i
        | some b => if key i < key b then some i else some b) (some b) = some x →
      (x = b ∨ x ∈ l) ∧ key x ≤ key b ∧ ∀ i ∈ l, key x ≤ key i := by
  induction l with
  | nil => intro b x h; simp at h; subst h; simp
  | cons a t ih =>
    intro b x h
    simp only [List.foldl_cons] at h
    by_cases hlt : key a < key b
    · rw [if_pos hlt] at h
      obtain ⟨h1, h2, h3⟩ := ih a x h
      refine ⟨?_, by omega, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inr (h1 ▸ List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · omega
        · exact h3 i hi
    · rw [if_neg hlt] at h
      obtain ⟨h1, h2, h3⟩ := ih b x h
      refine ⟨?_, h2, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · omega
        · exact h3 i hi

/-- `argMin` picks a member of the list, and one with the least key. -/
theorem argMin_spec (idx : List Nat) (key : Nat → Nat) (x : Nat) (h : argMin idx key = some x) :
    x ∈ idx ∧ ∀ i ∈ idx, key x ≤ key i := by
  unfold argMin at h
  cases idx with
  | nil => simp at h
  | cons a t =>
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2, h3⟩ := argMin_fold key t a x h
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · exact h1 ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ h1
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact h2
      · exact h3 i hi

/-- A missed count of zero is healthy (the miss limit is 3). -/
theorem unhealthy_zero (n : Netcheck) (i : Nat) (h : n.missed.getD i 0 = 0) : n.unhealthy i = false := by
  simp only [Netcheck.unhealthy, h, missLimit]; decide

/-- A step of the ring from an unhealthy home never lands on the home. -/
theorem ring_ne (home rn k : Nat) (hk1 : 1 ≤ k) (hk2 : k < rn) : (home + k) % rn ≠ home := by
  intro h
  by_cases hh : home < rn
  · have : (home + k) % rn = if home + k < rn then home + k else home + k - rn := by
      split
      · exact Nat.mod_eq_of_lt (by assumption)
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split at this <;> omega
  · have := Nat.mod_lt (home + k) (show rn > 0 by omega)
    omega

/-- A failover only moves away from an unhealthy home, to a configured relay that is not unhealthy and is known to work
(a probe answered since it last failed, or an open carrier), and changes nothing but the home. This needs no
hypothesis on the miss limit: it is the constant 3 in the model. -/
theorem failover_healthy (n n' : Netcheck) (usable isOpen : Nat → Bool) (x : Nat)
    (h : n.failover usable isOpen = (some x, n')) :
    (∃ home, n.home = some home ∧ n.unhealthy home = true ∧ x ≠ home) ∧
    usable x = true ∧ n.unhealthy x = false ∧
    ((n.missed.getD x 0 = 0 ∧ (n.refl.getD x none).isSome = true) ∨ isOpen x = true) ∧
    n' = { n with home := some x } := by
  unfold Netcheck.failover at h
  cases hh : n.home with
  | none => simp [hh] at h
  | some home =>
    simp only [hh] at h
    by_cases hu : n.unhealthy home = true
    · rw [if_neg (by simpa using hu)] at h
      generalize hm : argMin _ _ = m at h
      cases m with
      | some m =>
        simp only [] at h
        obtain ⟨rfl, rfl⟩ : m = x ∧ { n with home := some m } = n' := by
          simp only [Prod.mk.injEq, Option.some.injEq] at h; exact h
        have hs := (argMin_spec _ _ _ hm).1
        simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hs
        obtain ⟨_, ⟨⟨hne, hus⟩, hz⟩, hrf⟩ := hs
        exact ⟨⟨home, rfl, hu, hne⟩, hus, unhealthy_zero n _ hz, Or.inl ⟨hz, hrf⟩, rfl⟩
      | none =>
        simp only [] at h
        cases hf : (((List.range' 1 (n.probes.length - 1)).map fun k => (home + k) % n.probes.length).find?
            fun i => usable i && isOpen i && !n.unhealthy i) with
        | none => simp [hf] at h
        | some y =>
          simp only [hf, Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hp := List.find?_some hf
          have hmem := List.mem_of_find?_eq_some hf
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
          obtain ⟨⟨hus, hop⟩, hun⟩ := hp
          obtain ⟨k, hk, hky⟩ := List.mem_map.mp hmem
          rw [List.mem_range'_1] at hk
          exact ⟨⟨home, rfl, hu, hky ▸ ring_ne home _ k (by omega) (by omega)⟩, hus, hun, Or.inr hop, rfl⟩
    · rw [if_pos (by simpa using hu)] at h
      simp at h
  
/-- With no relay known to work the home stays (and nothing is returned). -/
theorem failover_none (n n' : Netcheck) (usable isOpen : Nat → Bool)
    (h : n.failover usable isOpen = (none, n')) : n' = n := by
  unfold Netcheck.failover at h
  cases hh : n.home with
  | none => simp [hh] at h; exact h.symm
  | some home =>
    simp only [hh] at h
    split at h
    · simp at h; exact h.symm
    · split at h
      · simp at h
      · simp at h; exact h.symm

/-- The measured candidate has the least round trip among the candidates: configured, not the home, with no miss since
its last answer and a known reflexive address. -/
theorem failover_measured_least (n : Netcheck) (usable : Nat → Bool) (home m : Nat)
    (h : argMin ((List.range n.probes.length).filter fun i =>
        i != home && usable i && n.missed.getD i 0 == 0 && (n.refl.getD i none).isSome) (fun i => n.rtt.getD i 0) = some m) :
    ∀ i, i < n.probes.length → i ≠ home → usable i = true → n.missed.getD i 0 = 0 →
      (n.refl.getD i none).isSome = true → n.rtt.getD m 0 ≤ n.rtt.getD i 0 := by
  intro i hi hne hus hz hrf
  apply (argMin_spec _ _ _ h).2
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  exact ⟨hi, ⟨⟨hne, hus⟩, hz⟩, hrf⟩

/-! ## Netcheck: the home after an answer -/

/-- The fold of `argMin2` from a known best: the result is the best or a later element, and none comes before it by
`key`, then by `key2`. -/
theorem argMin2_fold (key key2 : Nat → Nat) (l : List Nat) :
    ∀ (b x : Nat), l.foldl (fun acc i => match acc with
        | none => some i
        | some b => if lexLt key key2 i b then some i else some b) (some b) = some x →
      (x = b ∨ x ∈ l) ∧ (key x < key b ∨ (key x = key b ∧ key2 x ≤ key2 b)) ∧
        ∀ i ∈ l, key x < key i ∨ (key x = key i ∧ key2 x ≤ key2 i) := by
  induction l with
  | nil => intro b x h; simp at h; subst h; simp
  | cons a t ih =>
    intro b x h
    simp only [List.foldl_cons] at h
    by_cases hlt : lexLt key key2 a b = true
    · rw [if_pos hlt] at h
      obtain ⟨h1, h2, h3⟩ := ih a x h
      simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlt
      refine ⟨?_, by omega, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inr (h1 ▸ List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact h2
        · exact h3 i hi
    · rw [if_neg hlt] at h
      obtain ⟨h1, h2, h3⟩ := ih b x h
      simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlt
      refine ⟨?_, h2, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · omega
        · exact h3 i hi

/-- `argMin2` picks a member of the list, and none comes before it by `key`, then by `key2`. -/
theorem argMin2_spec (idx : List Nat) (key key2 : Nat → Nat) (x : Nat) (h : argMin2 idx key key2 = some x) :
    x ∈ idx ∧ ∀ i ∈ idx, key x < key i ∨ (key x = key i ∧ key2 x ≤ key2 i) := by
  unfold argMin2 at h
  cases idx with
  | nil => simp at h
  | cons a t =>
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2, h3⟩ := argMin2_fold key key2 t a x h
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · exact h1 ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ h1
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact h2
      · exact h3 i hi

/-- The fold of `argMin2` from a known best gives a result. -/
theorem argMin2_fold_some (key key2 : Nat → Nat) (l : List Nat) :
    ∀ b, ∃ x, l.foldl (fun acc i => match acc with
        | none => some i
        | some b => if lexLt key key2 i b then some i else some b) (some b) = some x := by
  induction l with
  | nil => intro b; exact ⟨b, rfl⟩
  | cons a t ih =>
    intro b
    simp only [List.foldl_cons]
    by_cases hlt : lexLt key key2 a b = true
    · rw [if_pos hlt]; exact ih a
    · rw [if_neg hlt]; exact ih b

/-- `argMin2` finds nothing only in an empty list. -/
theorem argMin2_none (idx : List Nat) (key key2 : Nat → Nat) (h : argMin2 idx key key2 = none) : idx = [] := by
  unfold argMin2 at h
  cases idx with
  | nil => rfl
  | cons a t =>
    simp only [List.foldl_cons] at h
    obtain ⟨x, hx⟩ := argMin2_fold_some key key2 t a
    exact absurd (hx.symm.trans h) (by simp)

/-- The home choice with the pin not a candidate, out of a state where some relay ever answered and is not unhealthy:
the relay with the lowest last round trip among those, a tie to the one that answered first. -/
theorem rehome_least (n : Netcheck) (hp : n.rehome.pinOk = none) (hne : n.answeredRelays ≠ []) :
    ∃ x, n.rehome.home = some x ∧ x ∈ n.rehome.answeredRelays ∧
      ∀ i ∈ n.rehome.answeredRelays, n.rehome.rtt.getD x 0 < n.rehome.rtt.getD i 0 ∨
        (n.rehome.rtt.getD x 0 = n.rehome.rtt.getD i 0 ∧ n.rehome.order.getD x 0 ≤ n.rehome.order.getD i 0) := by
  have hp' : n.pinOk = none := by
    obtain ⟨h, hq⟩ := rehome_only_home n
    rw [hq, pinOk_home] at hp
    exact hp
  cases hb : argMin2 n.answeredRelays (fun i => n.rtt.getD i 0) (fun i => n.order.getD i 0) with
  | none => exact absurd (argMin2_none _ _ _ hb) hne
  | some b =>
    have hr : n.rehome = { n with home := some b } := by simp only [Netcheck.rehome, hp', hb]
    rw [hr]
    exact ⟨b, rfl, argMin2_spec _ _ _ _ hb⟩

/-- After an accepted answer, unless the pinned relay ever answered and is not unhealthy (`answered_pin_home`), the home
is a relay that ever answered and is not unhealthy, and none of those has a lower last round trip, nor the same one with
an earlier first answer: a fallback home that never answered moves to the first relay that does. With no pin set this
holds after every answer. The order and miss lists have one entry per relay, as the code's arrays. -/
theorem answered_home_least (n n' : Netcheck) (now relay r : Nat) (nonce : List Nat) (addr : Nat)
    (ho : n.order.length = n.probes.length) (hm : n.missed.length = n.probes.length)
    (h : n.answered now relay nonce addr = (some r, n')) (hpin : n'.pinOk = none) :
    ∃ x, n'.home = some x ∧ x ∈ n'.answeredRelays ∧
      ∀ i ∈ n'.answeredRelays, n'.rtt.getD x 0 < n'.rtt.getD i 0 ∨
        (n'.rtt.getD x 0 = n'.rtt.getD i 0 ∧ n'.order.getD x 0 ≤ n'.order.getD i 0) := by
  unfold Netcheck.answered at h
  cases hp : n.probes.getD relay none with
  | none => (simp only [hp] at h) <;> simp at h
  | some p =>
    obtain ⟨nc, sent⟩ := p
    simp only [hp] at h
    split at h
    · simp at h
    · have hrl : relay < n.probes.length := by
        by_cases hc : relay < n.probes.length
        · exact hc
        · have hn : n.probes[relay]? = none := List.getElem?_eq_none (by omega)
          rw [List.getD_eq_getElem?_getD, hn] at hp
          simp at hp
      have hpos : 0 < (if n.order.getD relay 0 = 0 then n.order.foldl max 0 + 1 else n.order.getD relay 0) := by
        split <;> omega
      generalize (if n.order.getD relay 0 = 0 then n.order.foldl max 0 + 1 else n.order.getD relay 0) = place at h hpos
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine rehome_least _ hpin ?_
      intro hnil
      unfold Netcheck.answeredRelays at hnil
      rw [List.filter_eq_nil_iff] at hnil
      have hx := hnil relay (by simpa using hrl)
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_self, ho, hm, hrl, hpos, Netcheck.unhealthy, missLimit] at hx
        <;> omega

/-- A link change forgets the answers of the round and keeps the home, the order of first answers, the round trips, the
misses and the count of rounds without a home (a node that moved after two silent rounds takes the fallback at the
next). -/
theorem restart_keeps (n : Netcheck) :
    n.restart.home = n.home ∧ n.restart.order = n.order ∧ n.restart.tries = n.tries ∧ n.restart.rtt = n.rtt ∧
      n.restart.missed = n.missed ∧ n.restart.refl.all Option.isNone := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [Netcheck.restart, List.all_eq_true]


end Pinc.ConnectClient

#audit_axioms Pinc.ConnectClient.argMin_spec
#audit_axioms Pinc.ConnectClient.failover_healthy
#audit_axioms Pinc.ConnectClient.failover_none
#audit_axioms Pinc.ConnectClient.failover_measured_least
#audit_axioms Pinc.ConnectClient.answered_home_least
#audit_axioms Pinc.ConnectClient.answered_pin_home
#audit_axioms Pinc.ConnectClient.restart_keeps
