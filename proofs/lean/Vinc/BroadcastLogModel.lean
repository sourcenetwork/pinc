import Vinc.Axioms

/-!
# The broadcast hub log accounting

An unbounded model of the accounting of `HubLog` in `vinc-broadcast/src/log.rs`, the counterpart of
`BroadcastLogOps.tla` (`Pop`, `Write`, `Loop`, `Push`, `ExpireLoop`, checked by TLC on small instances). The byte ring
holds heads and bodies; the model keeps only the bookkeeping: the entry queue (`mid`, arrival time `born`, wall clock,
`off`, `len`, `cost`), the write position `wpos` and the bytes in use `used`. `ring` and `cap` are explicit
arguments over all of `Nat`. Time subtraction is saturating. The entry's arrival time is `born` (the TLA+ field `at`).

`write` pads to the ring start when the message would cross the ring end (`pad = ring - wpos`), so an entry never
wraps and its cost is `pad + n`. `push` refuses a message longer than the ring or an id already present, and
otherwise evicts from the front until the entry count and the bytes both have room, at most `length + 1` rounds; it
returns the new log, whether the message was stored and the evicted ids in order. `expire` pops while the front entry
is older than the window.

`Inv` is the accounting invariant: `used` is the sum of the costs, `used <= ring`, at most `cap` entries, an empty
queue has `used = 0` and `wpos = 0`, `wpos < ring`, every entry lies inside the ring, ids are unique. It is preserved
by `pop`, `push` (stored or refused) and `expire`. A valid message always fits (`push_ok`): this is what
`Limits::valid`, `max_body + MAX_HEAD <= log_bytes`, buys (`valid_limits_fit`). The evicted ids are exactly a prefix
of the old queue and the new queue is that queue with the prefix dropped followed by the new entry
(`push_evicted_prefix`); `expire` removes exactly a prefix of entries older than the window
(`expire_removes_exactly_old`). Overlap-freedom of the live entries is checked by TLC (`BroadcastLog.tla`) and is not
proven here.
-/

namespace Vinc.BroadcastLogModel

/-- One logged message: id, arrival time, wall clock, offset and length in the ring, and the bytes charged. -/
structure Ent where
  mid : Nat
  born : Nat
  wall : Nat
  off : Nat
  len : Nat
  cost : Nat

/-- The log bookkeeping: entry queue, write position, bytes in use. -/
structure Log where
  entries : List Ent
  wpos : Nat
  used : Nat

/-- The empty log. -/
def empty : Log := ⟨[], 0, 0⟩

/-- Whether the id is in the queue. -/
def has (L : Log) (mid : Nat) : Bool := L.entries.any (fun e => e.mid == mid)

/-- `pop`: the oldest entry leaves; an empty queue resets `used` and `wpos`. -/
def pop (L : Log) : Log :=
  match L.entries with
  | [] => L
  | e :: r =>
    { entries := r, wpos := if r = [] then 0 else L.wpos, used := if r = [] then 0 else L.used - e.cost }

/-- The padding a message of `n` bytes needs at the write position. -/
def pad (L : Log) (ring n : Nat) : Nat := if ring < L.wpos + n then ring - L.wpos else 0

/-- The entry `write` appends. -/
def mkEnt (L : Log) (ring mid born wall n : Nat) : Ent :=
  ⟨mid, born, wall, if 0 < pad L ring n then 0 else L.wpos, n, pad L ring n + n⟩

/-- `write`: append the entry, advance the write position, charge `pad + n`. -/
def write (L : Log) (ring mid born wall n : Nat) : Log :=
  { entries := L.entries ++ [mkEnt L ring mid born wall n],
    wpos := ((mkEnt L ring mid born wall n).off + n) % ring,
    used := L.used + pad L ring n + n }

/-- The eviction loop: write when there is room, else pop the front and record its id. -/
def pushLoop (ring cap mid born wall n : Nat) : Nat → Log → List Nat → Log × Bool × List Nat
  | 0, L, ev => (L, false, ev)
  | f + 1, L, ev =>
    if L.entries.length < cap ∧ L.used + pad L ring n + n ≤ ring then
      (write L ring mid born wall n, true, ev)
    else
      match L.entries with
      | [] => (L, false, ev)
      | e :: _ => pushLoop ring cap mid born wall n f (pop L) (ev ++ [e.mid])

/-- `push`: refuse an oversized message or a present id, else run the eviction loop. -/
def push (L : Log) (ring cap mid born wall n : Nat) : Log × Bool × List Nat :=
  if ring < n ∨ has L mid then (L, false, [])
  else pushLoop ring cap mid born wall n (L.entries.length + 1) L []

/-- The expire loop with a fuel bound. -/
def expireLoop (window now : Nat) : Nat → Log → List Nat → Log × List Nat
  | 0, L, ev => (L, ev)
  | f + 1, L, ev =>
    match L.entries with
    | [] => (L, ev)
    | e :: _ => if window < now - e.born then expireLoop window now f (pop L) (ev ++ [e.mid]) else (L, ev)

/-- `expire`: drop the messages older than the window; also returns their ids in order. -/
def expire (L : Log) (window now : Nat) : Log × List Nat := expireLoop window now L.entries.length L []

/-- The accounting invariant. -/
def Inv (ring cap : Nat) (L : Log) : Prop :=
  L.used = (L.entries.map Ent.cost).sum ∧ L.used ≤ ring ∧ L.entries.length ≤ cap ∧
  (L.entries = [] → L.used = 0 ∧ L.wpos = 0) ∧ L.wpos < ring ∧
  (∀ e ∈ L.entries, e.off + e.len ≤ ring) ∧ (L.entries.map Ent.mid).Nodup

/-- The configuration arithmetic: a message within `body + head` fits a ring that holds `body + head`. -/
theorem valid_limits_fit (body head ring n : Nat) (hv : body + head ≤ ring) (hn : n ≤ body + head) :
    n ≤ ring := Nat.le_trans hn hv

theorem has_eq_false (L : Log) (mid : Nat) : has L mid = false ↔ mid ∉ L.entries.map Ent.mid := by
  simp [has, List.any_eq_false]

@[simp] theorem pop_entries (L : Log) : (pop L).entries = L.entries.tail := by
  unfold pop; split <;> simp_all

theorem inv_empty (ring cap : Nat) (h : 0 < ring) : Inv ring cap empty := by
  simp [Inv, empty, h]

/-- `pop` preserves the invariant. -/
theorem pop_inv {ring cap : Nat} {L : Log} (h : Inv ring cap L) : Inv ring cap (pop L) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold pop
  split
  · rename_i hE
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · rename_i e r hE
    rw [hE] at h1 h3 h6 h7
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.mem_cons, List.nodup_cons] at h1 h3 h6 h7
    by_cases hr : r = []
    · subst hr; simp [Inv]; omega
    · simp only [Inv, hr, ite_false]
      refine ⟨by omega, by omega, by omega, fun h => h.elim, h5,
        fun x hx => h6 x (Or.inr hx), h7.2⟩

theorem write_inv {ring cap : Nat} {L : Log} (mid born wall n : Nat) (h : Inv ring cap L)
    (hlen : L.entries.length < cap) (hroom : L.used + pad L ring n + n ≤ ring) (hn : n ≤ ring)
    (hm : has L mid = false) : Inv ring cap (write L ring mid born wall n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [has_eq_false] at hm
  have hent : (mkEnt L ring mid born wall n).off + (mkEnt L ring mid born wall n).len ≤ ring := by
    simp only [mkEnt, pad]
    split <;> split <;> omega
  refine ⟨?_, ?_, ?_, fun h => ?_, ?_, ?_, ?_⟩
  · simp [write, mkEnt, h1, List.sum_append]; omega
  · simpa [write] using hroom
  · simp [write]; omega
  · simp [write] at h
  · simp only [write]; exact Nat.mod_lt _ (by omega)
  · intro e he
    simp only [write, List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · exact h6 e he
    · rw [he]; exact hent
  · simp only [write, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨h7, by simp [mkEnt], ?_⟩
    intro a ha b hb hab
    simp [mkEnt] at hb
    rw [hb] at hab; exact hm (hab ▸ ha)

theorem has_pop {L : Log} {mid : Nat} (h : has L mid = false) : has (pop L) mid = false := by
  rw [has_eq_false] at h ⊢
  intro hm; apply h
  rw [pop_entries] at hm
  cases hE : L.entries with
  | nil => simp [hE] at hm
  | cons e t => simp only [hE, List.tail_cons, List.map_cons, List.mem_cons] at hm ⊢; exact Or.inr hm

/-- The new entry lies inside the ring. -/
theorem new_entry_in_ring (L : Log) (ring mid born wall n : Nat) (hn : n ≤ ring) (hw : L.wpos < ring) :
    (mkEnt L ring mid born wall n).off + (mkEnt L ring mid born wall n).len ≤ ring := by
  simp only [mkEnt, pad]
  split <;> split <;> omega

/-- The eviction loop, whatever its fuel: the invariant holds, the evicted ids are a prefix of the queue, and
the queue is that prefix dropped (refused) or dropped followed by the new entry (stored). -/
theorem pushLoop_gen {ring cap : Nat} (mid born wall n : Nat) (hn : n ≤ ring) : ∀ (f : Nat) (L : Log)
    (ev : List Nat), Inv ring cap L → has L mid = false →
    Inv ring cap (pushLoop ring cap mid born wall n f L ev).1 ∧
    ∃ k, k ≤ L.entries.length ∧
      (pushLoop ring cap mid born wall n f L ev).2.2 = ev ++ (L.entries.take k).map Ent.mid ∧
      ((pushLoop ring cap mid born wall n f L ev).2.1 = true →
        ∃ e : Ent, (pushLoop ring cap mid born wall n f L ev).1.entries = L.entries.drop k ++ [e] ∧
          e.mid = mid ∧ e.len = n ∧ e.off + e.len ≤ ring) ∧
      ((pushLoop ring cap mid born wall n f L ev).2.1 = false →
        (pushLoop ring cap mid born wall n f L ev).1.entries = L.entries.drop k) := by
  intro f
  induction f with
  | zero => intro L ev hI hm; exact ⟨hI, 0, by simp, by simp [pushLoop], by simp [pushLoop], by simp [pushLoop]⟩
  | succ f ih =>
    intro L ev hI hm
    by_cases hc : L.entries.length < cap ∧ L.used + pad L ring n + n ≤ ring
    · have hw := write_inv mid born wall n hI hc.1 hc.2 hn hm
      refine ⟨by simpa [pushLoop, hc] using hw, 0, by simp, by simp [pushLoop, hc], ?_, by simp [pushLoop, hc]⟩
      intro _
      exact ⟨mkEnt L ring mid born wall n, by simp [pushLoop, hc, write],
        rfl, rfl, new_entry_in_ring L ring mid born wall n hn hI.2.2.2.2.1⟩
    · cases hE : L.entries with
      | nil =>
        have key : pushLoop ring cap mid born wall n (f + 1) L ev = (L, false, ev) := by
          simp only [pushLoop, hc, ite_false]; rw [hE]
        rw [key]
        exact ⟨hI, 0, by simp, by simp, by simp, by simp [hE]⟩
      | cons e t =>
        have hp := ih (pop L) (ev ++ [e.mid]) (pop_inv hI) (has_pop hm)
        obtain ⟨hI', k, hk, h2, h3, h4⟩ := hp
        have hpop : (pop L).entries = t := by simp [hE]
        rw [hpop] at hk h2 h3 h4
        have key : pushLoop ring cap mid born wall n (f + 1) L ev
            = pushLoop ring cap mid born wall n f (pop L) (ev ++ [e.mid]) := by
          simp only [pushLoop, hc, ite_false]; rw [hE]
        rw [key]
        refine ⟨hI', k + 1, by simp; omega, ?_, ?_, ?_⟩
        · rw [h2]; simp
        · intro ho; obtain ⟨x, hx⟩ := h3 ho; exact ⟨x, by simpa [hE] using hx.1, hx.2⟩
        · intro ho; simp [h4 ho]

theorem pushLoop_ok {ring cap : Nat} (mid born wall n : Nat) (hn : n ≤ ring) (hcap : 0 < cap) :
    ∀ (f : Nat) (L : Log) (ev : List Nat), Inv ring cap L → has L mid = false → L.entries.length < f →
    (pushLoop ring cap mid born wall n f L ev).2.1 = true := by
  intro f
  induction f with
  | zero => intro L ev _ _ hf; omega
  | succ f ih =>
    intro L ev hI hm hf
    by_cases hc : L.entries.length < cap ∧ L.used + pad L ring n + n ≤ ring
    · simp [pushLoop, hc]
    · cases hE : L.entries with
      | nil =>
        exfalso; apply hc
        obtain ⟨_, _, _, h4, _⟩ := hI
        obtain ⟨hu, hw⟩ := h4 hE
        have : pad L ring n = 0 := by simp only [pad, hw]; split <;> omega
        rw [hE]; simp only [List.length_nil]; omega
      | cons e t =>
        have key : pushLoop ring cap mid born wall n (f + 1) L ev
            = pushLoop ring cap mid born wall n f (pop L) (ev ++ [e.mid]) := by
          simp only [pushLoop, hc, ite_false]; rw [hE]
        rw [key]
        apply ih (pop L) _ (pop_inv hI) (has_pop hm)
        simp [hE]; rw [hE] at hf; simpa using hf

/-- `push` preserves the invariant, stored or refused. -/
theorem push_inv {ring cap : Nat} (L : Log) (mid born wall n : Nat) (h : Inv ring cap L) :
    Inv ring cap (push L ring cap mid born wall n).1 := by
  unfold push
  by_cases hr : ring < n ∨ has L mid = true
  · simpa [hr] using h
  · have hn : n ≤ ring := by omega
    have hm : has L mid = false := by simpa using (not_or.mp hr).2
    simp only [hr, ite_false]
    exact (pushLoop_gen mid born wall n hn _ L [] h hm).1

/-- A valid message always fits: with `0 < cap`, `n <= ring` and a fresh id the push is stored. -/
theorem push_ok {ring cap : Nat} (L : Log) (mid born wall n : Nat) (h : Inv ring cap L) (hcap : 0 < cap)
    (hn : n ≤ ring) (hm : has L mid = false) : (push L ring cap mid born wall n).2.1 = true := by
  unfold push
  have : ¬(ring < n ∨ has L mid = true) := by simp [hm]; omega
  simp only [this, ite_false]
  exact pushLoop_ok mid born wall n hn hcap _ L [] h hm (Nat.lt_succ_self _)

/-- A refusal happens only for an oversized message or an id already present. -/
theorem push_fails_only {ring cap : Nat} (L : Log) (mid born wall n : Nat) (h : Inv ring cap L) (hcap : 0 < cap)
    (hf : (push L ring cap mid born wall n).2.1 = false) : ring < n ∨ has L mid = true := by
  by_cases hc : ring < n ∨ has L mid = true
  · exact hc
  · exfalso
    have hn : n ≤ ring := by omega
    have hm : has L mid = false := by simpa using (not_or.mp hc).2
    have := push_ok L mid born wall n h hcap hn hm
    rw [hf] at this; exact absurd this (by simp)

/-- The evicted ids are the first `k` mids of the old queue in order; the new queue is the old one with that
prefix dropped, followed by the new entry (stored) or nothing (refused). -/
theorem push_evicted_prefix {ring cap : Nat} (L : Log) (mid born wall n : Nat) (h : Inv ring cap L) :
    ∃ k, k ≤ L.entries.length ∧
      (push L ring cap mid born wall n).2.2 = (L.entries.take k).map Ent.mid ∧
      ((push L ring cap mid born wall n).2.1 = true →
        ∃ e : Ent, (push L ring cap mid born wall n).1.entries = L.entries.drop k ++ [e] ∧
          e.mid = mid ∧ e.len = n ∧ e.off + e.len ≤ ring) ∧
      ((push L ring cap mid born wall n).2.1 = false →
        (push L ring cap mid born wall n).1.entries = L.entries.drop k) := by
  unfold push
  by_cases hr : ring < n ∨ has L mid = true
  · refine ⟨0, by simp, by simp [hr], by simp [hr], by simp [hr]⟩
  · have hn : n ≤ ring := by omega
    have hm : has L mid = false := by simpa using (not_or.mp hr).2
    simp only [hr, ite_false]
    obtain ⟨_, k, hk, h2, h3, h4⟩ := pushLoop_gen mid born wall n hn (L.entries.length + 1) L [] h hm
    exact ⟨k, hk, by simpa using h2, h3, h4⟩

/-- `Topics::room_to_store` (`behind.rs`), the guard `Topics::hub_store` puts over `push`. `room` is how many of the
oldest entries no subscriber that is behind and not held is still
owed (the index of the first owed entry; the queue length when nobody is behind). The push goes ahead only when it
evicts at most `room` entries, which `HubLog::evicts` counts before anything moves; otherwise nothing changes and
the message is refused, so the hub does not acknowledge it. -/
def pushOwed (L : Log) (ring cap mid born wall n room : Nat) : Log × Bool × List Nat :=
  if (push L ring cap mid born wall n).2.2.length ≤ room then push L ring cap mid born wall n else (L, false, [])

/-- The guarded push keeps the accounting invariant, stored or refused. -/
theorem pushOwed_inv {ring cap : Nat} (L : Log) (mid born wall n room : Nat) (h : Inv ring cap L) :
    Inv ring cap (pushOwed L ring cap mid born wall n room).1 := by
  unfold pushOwed; split
  · exact push_inv L mid born wall n h
  · exact h

/-- No owed entry is evicted: the entries from index `room` on are still in the queue, in order, with only the
unowed ones before them evicted and only the new entry after them. -/
theorem pushOwed_keeps_owed {ring cap : Nat} (L : Log) (mid born wall n room : Nat) (h : Inv ring cap L) :
    ∃ pre post, (pushOwed L ring cap mid born wall n room).1.entries = pre ++ L.entries.drop room ++ post := by
  unfold pushOwed
  split
  · rename_i hle
    obtain ⟨k, hk, hev, hok, hno⟩ := push_evicted_prefix L mid born wall n h
    have hkr : k ≤ room := by
      rw [hev, List.length_map, List.length_take] at hle; omega
    have hsplit : L.entries.drop k = (L.entries.drop k).take (room - k) ++ L.entries.drop room := by
      have hd : (L.entries.drop k).drop (room - k) = L.entries.drop room := by
        rw [List.drop_drop]; congr 1; omega
      rw [← hd, List.take_append_drop]
    cases hs : (push L ring cap mid born wall n).2.1
    · exact ⟨(L.entries.drop k).take (room - k), [], by rw [hno hs, List.append_nil]; exact hsplit⟩
    · obtain ⟨e, he, -⟩ := hok hs
      exact ⟨(L.entries.drop k).take (room - k), [e], by rw [he, ← hsplit]⟩
  · exact ⟨L.entries.take room, [], by simp⟩

/-- A refused guarded push leaves the log as it was: the message is not stored, so it is not acknowledged. -/
theorem pushOwed_refused {ring cap : Nat} (L : Log) (mid born wall n room : Nat)
    (hgt : room < (push L ring cap mid born wall n).2.2.length) :
    pushOwed L ring cap mid born wall n room = (L, false, []) := by
  unfold pushOwed; simp [Nat.not_le.mpr hgt]

/-- The expire loop, whatever the fuel at least the queue length: a prefix is removed, every removed entry is
older than the window, and the first remaining entry is not. -/
theorem expireLoop_gen {ring cap : Nat} (window now : Nat) : ∀ (f : Nat) (L : Log) (ev : List Nat),
    Inv ring cap L → L.entries.length ≤ f →
    Inv ring cap (expireLoop window now f L ev).1 ∧
    ∃ k, k ≤ L.entries.length ∧
      (expireLoop window now f L ev).2 = ev ++ (L.entries.take k).map Ent.mid ∧
      (expireLoop window now f L ev).1.entries = L.entries.drop k ∧
      (∀ e ∈ L.entries.take k, window < now - e.born) ∧
      (∀ e, (expireLoop window now f L ev).1.entries.head? = some e → now - e.born ≤ window) := by
  intro f
  induction f with
  | zero =>
    intro L ev hI hf
    have : L.entries = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨hI, 0, by simp, by simp [expireLoop], by simp [expireLoop, this], by simp,
      by simp [expireLoop, this]⟩
  | succ f ih =>
    intro L ev hI hf
    cases hE : L.entries with
    | nil => exact ⟨by simpa [expireLoop, hE] using hI, 0, by simp, by simp [expireLoop, hE],
        by simp [expireLoop, hE], by simp, by simp [expireLoop, hE]⟩
    | cons e t =>
      by_cases ho : window < now - e.born
      · have key : expireLoop window now (f + 1) L ev = expireLoop window now f (pop L) (ev ++ [e.mid]) := by
          simp only [expireLoop]; rw [hE]; simp only [ho, ite_true]
        have hp := ih (pop L) (ev ++ [e.mid]) (pop_inv hI) (by simp [hE]; rw [hE] at hf; simpa using hf)
        obtain ⟨hI', k, hk, h2, h3, h4, h5⟩ := hp
        have hpop : (pop L).entries = t := by simp [hE]
        rw [hpop] at hk h2 h3 h4
        rw [key]
        refine ⟨hI', k + 1, by simp; omega, ?_, ?_, ?_, h5⟩
        · rw [h2]; simp
        · simpa using h3
        · intro x hx
          simp only [List.take_succ_cons, List.mem_cons] at hx
          rcases hx with hx | hx
          · rw [hx]; exact ho
          · exact h4 x hx
      · have key : expireLoop window now (f + 1) L ev = (L, ev) := by
          simp only [expireLoop]; rw [hE]; simp only [ho, ite_false]
        rw [key]
        refine ⟨hI, 0, Nat.zero_le _, by simp, by simpa using hE, fun _ hm => by simp at hm, ?_⟩
        intro x hx
        rw [hE] at hx
        simp at hx; rw [← hx]; omega

/-- `expire` preserves the invariant. -/
theorem expire_inv {ring cap : Nat} (L : Log) (window now : Nat) (h : Inv ring cap L) :
    Inv ring cap (expire L window now).1 :=
  (expireLoop_gen window now _ L [] h (Nat.le_refl _)).1

/-- `expire` removes exactly a prefix of the queue, each removed entry older than the window, with the
removed ids reported in order; the first remaining entry is within the window. -/
theorem expire_removes_exactly_old {ring cap : Nat} (L : Log) (window now : Nat) (h : Inv ring cap L) :
    ∃ k, k ≤ L.entries.length ∧ (expire L window now).2 = (L.entries.take k).map Ent.mid ∧
      (expire L window now).1.entries = L.entries.drop k ∧
      (∀ e ∈ L.entries.take k, window < now - e.born) ∧
      (∀ e, (expire L window now).1.entries.head? = some e → now - e.born ≤ window) := by
  obtain ⟨_, k, hk, h2, h3, h4, h5⟩ := expireLoop_gen window now _ L [] h (Nat.le_refl _)
  exact ⟨k, hk, by simpa [expire] using h2, h3, h4, h5⟩

/-- With the queue ordered by arrival time, every entry left after `expire` is within the window. -/
theorem expire_left_young {ring cap : Nat} (L : Log) (window now : Nat) (h : Inv ring cap L)
    (hs : L.entries.Pairwise (fun a b => a.born ≤ b.born)) :
    ∀ e ∈ (expire L window now).1.entries, now - e.born ≤ window := by
  obtain ⟨k, _, _, h3, _, h5⟩ := expire_removes_exactly_old L window now h
  intro e he
  rw [h3] at he h5
  have hp : (L.entries.drop k).Pairwise (fun a b => a.born ≤ b.born) := hs.sublist (List.drop_sublist _ _)
  cases hd : L.entries.drop k with
  | nil => rw [hd] at he; simp at he
  | cons e0 t =>
    rw [hd] at he hp h5
    have h0 := h5 e0 (by simp)
    rw [List.pairwise_cons] at hp
    simp only [List.mem_cons] at he
    rcases he with he | he
    · rw [he]; exact h0
    · have := hp.1 e he; omega
