import Vinc.TicketsWire

/-!
# The client ticket store

`ClientTickets` of `vinc-security/src/tickets.rs`: `N` optional slots and a clock. It holds one ticket per peer (the
newest replaces the older, `insert`), at most `N` peers (a new peer takes an empty slot, else an expired one, else the
lowest stamp, `victim`). `accept_batch` is `insert` for each ticket of a batch, so the last ticket of a batch is the
one kept; `take` drops the expired tickets and then removes and returns the peer's ticket if its ALPN matches;
`export` writes the newest at most `max` unexpired tickets, oldest first; `restore` checks the whole input before it
stores anything and then inserts every entry that has not expired. The clock is a `wrapping_add` counter: the model
counts in `Nat`, which agrees with the code before 2^64 insertions (a documented ceiling, never reached).

The theorems are in the same namespace as the server store (`Vinc.Tickets`): `client_one_per_peer`, `client_len`,
`accept_batch_last_kept`, `take_once`, `take_twice`, `export_*`, `restore_export`, `restore_malformed`.
-/

namespace Vinc.Tickets

/-! ## The operations -/

/-- A slot holding a ticket of `p`. -/
def samePeer (p : Peer) (x : Option Slot) : Bool := x.any fun s => decide (s.peer = p)

/-- `ClientTickets::insert`: the clock advances; the ticket replaces the first slot of the same peer, else goes to the
victim slot (nothing is stored when there is no slot, `N = 0`). -/
def cInsert (st : Store) (tk : Tk) (now : Nat) : Store :=
  match (firstIdx (samePeer tk.peer) st.slots 0).or (victim st.slots now) with
  | some i => ⟨st.slots.set i (some ⟨tk, st.clock + 1⟩), st.clock + 1⟩
  | none => ⟨st.slots, st.clock + 1⟩

/-- `ClientTickets::accept_batch`: `insert` for each ticket in order. -/
def acceptBatch (st : Store) (tks : List Tk) (now : Nat) : Store := tks.foldl (fun s t => cInsert s t now) st

/-- The expired tickets are dropped. -/
def dropExpired (now : Nat) (l : Slots) : Slots :=
  l.map fun s => s.bind fun x => if x.expiry < now then none else some x

/-- A slot holding a ticket of `peer` for `alpn`. -/
def matchesKey (peer : Peer) (alpn : List Nat) (x : Option Slot) : Bool :=
  x.any fun s => decide (s.peer = peer ∧ s.alpn = alpn)

/-- The part of `take` after the expired tickets are dropped: `d` is the store without them. -/
def takeIn (d : Slots) (clock : Nat) (peer : Peer) (alpn : List Nat) : Store × Option Tk :=
  match firstIdx (matchesKey peer alpn) d 0 with
  | none => (⟨d, clock⟩, none)
  | some i => (⟨d.set i none, clock⟩, ((d[i]?).getD none).map (·.tk))

/-- `ClientTickets::take`: drop the expired tickets, then remove and return the first ticket of the peer if it is for
`alpn`. The expired tickets are dropped even when nothing matches. -/
def cTake (st : Store) (peer : Peer) (alpn : List Nat) (now : Nat) : Store × Option Tk :=
  takeIn (dropExpired now st.slots) st.clock peer alpn

/-- The stores reachable from empty with `insert` (which `accept_batch` and `restore` are built from) and `take`. -/
inductive CReach (N : Nat) : Store → Prop where
  | init : CReach N (Store.empty N)
  | insert {st : Store} (tk : Tk) (now : Nat) : CReach N st → CReach N (cInsert st tk now)
  | take {st : Store} (peer : Peer) (alpn : List Nat) (now : Nat) : CReach N st → CReach N (cTake st peer alpn now).1

/-- At most one ticket per peer. -/
def OnePerPeer (st : Store) : Prop :=
  ∀ (i j : Nat) (s t : Slot), st.slots[i]? = some (some s) → st.slots[j]? = some (some t) → s.peer = t.peer → i = j

theorem OnePerPeer.empty (n : Nat) : OnePerPeer (Store.empty n) := by
  intro i j s t hs; exact (replicate_none_get hs).elim

/-! ## insert -/

theorem cInsert_cases (st : Store) (tk : Tk) (now : Nat) :
    (∃ i, firstIdx (samePeer tk.peer) st.slots 0 = some i ∧ cInsert st tk now = ⟨st.slots.set i (some ⟨tk, st.clock + 1⟩), st.clock + 1⟩) ∨
    (firstIdx (samePeer tk.peer) st.slots 0 = none ∧ ∃ j, victim st.slots now = some j ∧
      cInsert st tk now = ⟨st.slots.set j (some ⟨tk, st.clock + 1⟩), st.clock + 1⟩) ∨
    (firstIdx (samePeer tk.peer) st.slots 0 = none ∧ victim st.slots now = none ∧
      cInsert st tk now = ⟨st.slots, st.clock + 1⟩) := by
  unfold cInsert
  cases h1 : firstIdx (samePeer tk.peer) st.slots 0 with
  | some i => exact Or.inl ⟨i, rfl, by simp⟩
  | none =>
    cases h2 : victim st.slots now with
    | some j => exact Or.inr (Or.inl ⟨rfl, j, rfl, by simp⟩)
    | none => exact Or.inr (Or.inr ⟨rfl, rfl, by simp⟩)

theorem cInsert_length (st : Store) (tk : Tk) (now : Nat) : (cInsert st tk now).slots.length = st.slots.length := by
  rcases cInsert_cases st tk now with ⟨i, _, h⟩ | ⟨_, j, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;> simp

theorem cInsert_clock (st : Store) (tk : Tk) (now : Nat) : (cInsert st tk now).clock = st.clock + 1 := by
  rcases cInsert_cases st tk now with ⟨i, _, h⟩ | ⟨_, j, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]

/-- Setting slot `i` to a ticket stamped with the next clock value keeps the stamps distinct and bounded. -/
theorem stamps_set {st : Store} (hs : StampInv st) (i : Nat) (tk : Tk) :
    StampInv ⟨st.slots.set i (some ⟨tk, st.clock + 1⟩), st.clock + 1⟩ := by
  constructor
  · intro a x hx
    simp only at hx ⊢
    rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩
    · cases hxs; exact Nat.le_refl _
    · have := hs.1 a x hx'; omega
  · intro a b x y hx hy hxy
    simp only at hx hy
    rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩ <;>
      rcases set_get_cases hy with ⟨rfl, hys, _⟩ | ⟨hne', hy'⟩
    · rfl
    · cases hxs
      have := hs.1 b y hy'; simp only at hxy; omega
    · cases hys
      have := hs.1 a x hx'; simp only at hxy; omega
    · exact hs.2 a b x y hx' hy' hxy

theorem cInsert_stamps {st : Store} (hs : StampInv st) (tk : Tk) (now : Nat) : StampInv (cInsert st tk now) := by
  rcases cInsert_cases st tk now with ⟨i, _, h⟩ | ⟨_, j, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]
  · exact stamps_set hs i tk
  · exact stamps_set hs j tk
  · constructor
    · intro a x hx; have := hs.1 a x hx; simp only; omega
    · exact hs.2

/-- Putting a ticket into slot `i` keeps one ticket per peer when no other slot holds its peer. -/
theorem onePerPeer_set {st : Store} (ho : OnePerPeer st) (i : Nat) (tk : Tk) (c : Nat)
    (hother : ∀ (k : Nat) (s : Slot), st.slots[k]? = some (some s) → s.peer = tk.peer → k = i) :
    OnePerPeer ⟨st.slots.set i (some ⟨tk, c⟩), c⟩ := by
  intro a b x y hx hy hxy
  simp only at hx hy
  rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩ <;>
    rcases set_get_cases hy with ⟨rfl, hys, _⟩ | ⟨hne', hy'⟩
  · rfl
  · cases hxs
    exact absurd (hother b y hy' (by simpa using hxy.symm)) hne'
  · cases hys
    exact absurd (hother a x hx' (by simpa using hxy)) hne
  · exact ho a b x y hx' hy' hxy

theorem cInsert_onePerPeer {st : Store} (ho : OnePerPeer st) (tk : Tk) (now : Nat) : OnePerPeer (cInsert st tk now) := by
  rcases cInsert_cases st tk now with ⟨i, hi, h⟩ | ⟨hn, j, _, h⟩ | ⟨hn, _, h⟩ <;> rw [h]
  · obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ hi
    cases x with
    | none => simp [samePeer] at hp
    | some s0 =>
      simp only [samePeer, Option.any_some, decide_eq_true_eq] at hp
      apply onePerPeer_set ho
      intro k s hk hpk
      simp only [Nat.sub_zero] at hx
      exact ho k i s s0 hk (by simpa using hx) (by rw [hpk, hp])
  · apply onePerPeer_set ho
    intro k s hk hpk
    have := (firstIdx_none_iff _ _ _).1 hn k (some s) hk
    simp [samePeer, hpk] at this
  · intro a b x y hx hy hxy; exact ho a b x y hx hy hxy

theorem cInsert_places {st : Store} (hne : st.slots ≠ []) (tk : Tk) (now : Nat) :
    ∃ i : Nat, (cInsert st tk now).slots[i]? = some (some (Slot.mk tk (st.clock + 1))) := by
  rcases cInsert_cases st tk now with ⟨i, hi, h⟩ | ⟨_, j, hj, h⟩ | ⟨_, hv, _⟩
  · obtain ⟨_, x, hx, _⟩ := firstIdx_some _ _ _ _ hi
    have := (List.getElem?_eq_some_iff.mp hx).1
    exact ⟨i, by rw [h]; simp [List.getElem?_set_self (by simpa using this)]⟩
  · exact ⟨j, by rw [h]; simp [List.getElem?_set_self (victim_lt hj)]⟩
  · exfalso
    exact hne ((victim_none_iff _ _).1 hv)

/-- `N = 0` stores nothing, whatever is inserted. -/
theorem cInsert_nil (tk : Tk) (now clock : Nat) : (cInsert ⟨[], clock⟩ tk now).slots = [] := by
  have := cInsert_length ⟨[], clock⟩ tk now
  simpa using this

/-- `Tickets.client_insert_same_peer`: a new ticket of a peer that already has one replaces it in its slot and
nothing else changes. -/
theorem client_insert_same_peer {st : Store} (ho : OnePerPeer st) {tk : Tk} {now i : Nat} {s : Slot}
    (hs : st.slots[i]? = some (some s)) (hp : s.peer = tk.peer) :
    cInsert st tk now = ⟨st.slots.set i (some ⟨tk, st.clock + 1⟩), st.clock + 1⟩ := by
  rcases cInsert_cases st tk now with ⟨i', hi', h⟩ | ⟨hn, _⟩ | ⟨hn, _⟩
  · rw [h]
    obtain ⟨_, x, hx, hpx⟩ := firstIdx_some _ _ _ _ hi'
    cases x with
    | none => simp [samePeer] at hpx
    | some s0 =>
      simp only [samePeer, Option.any_some, decide_eq_true_eq] at hpx
      simp only [Nat.sub_zero] at hx
      have : i' = i := ho i' i s0 s (by simpa using hx) hs (by rw [hpx, hp])
      rw [this]
  · have := (firstIdx_none_iff _ _ _).1 hn i (some s) hs
    simp [samePeer, hp] at this
  · have := (firstIdx_none_iff _ _ _).1 hn i (some s) hs
    simp [samePeer, hp] at this

/-- `Tickets.client_insert_new_peer`: a ticket of a peer without one goes to the victim slot: an empty slot if there
is one, else an expired one, else the one with the lowest stamp; every other slot is unchanged. -/
theorem client_insert_new_peer {st : Store} {tk : Tk} {now : Nat} (hn : ∀ (k : Nat) (s : Slot), st.slots[k]? = some (some s) → s.peer ≠ tk.peer)
    {j : Nat} (hv : victim st.slots now = some j) :
    cInsert st tk now = ⟨st.slots.set j (some ⟨tk, st.clock + 1⟩), st.clock + 1⟩ := by
  have h1 : firstIdx (samePeer tk.peer) st.slots 0 = none := by
    rw [firstIdx_none_iff]
    intro k x hx
    cases x with
    | none => rfl
    | some s => simp [samePeer, hn k s hx]
  unfold cInsert
  rw [h1, hv]
  rfl

/-- `Tickets.client_evicts_oldest`: a ticket of a new peer into a full store with nothing expired replaces exactly the
ticket stored longest, and keeps every other ticket. -/
theorem client_evicts_oldest {N : Nat} {st : Store} (h : CReach N st) (hs : StampInv st) {tk : Tk} {now : Nat}
    (hn : ∀ (k : Nat) (s : Slot), st.slots[k]? = some (some s) → s.peer ≠ tk.peer)
    (hfull : ∀ k : Nat, st.slots[k]? ≠ some none)
    (hfresh : ∀ (k : Nat) (s : Slot), st.slots[k]? = some (some s) → ¬ s.expiry < now)
    {j : Nat} (hv : victim st.slots now = some j) :
    ∃ old, st.slots[j]? = some (some old) ∧ (∀ (k : Nat) (t : Slot), st.slots[k]? = some (some t) → k ≠ j → old.stamp < t.stamp) ∧
      cInsert st tk now = ⟨st.slots.set j (some ⟨tk, st.clock + 1⟩), st.clock + 1⟩ := by
  obtain ⟨old, hold, hmin⟩ := victim_min hv hfull hfresh
  refine ⟨old, hold, fun k t hk hkj => ?_, client_insert_new_peer hn hv⟩
  refine Nat.lt_of_le_of_ne (hmin k t hk) fun heq => hkj ?_
  exact hs.2 k j t old hk hold heq.symm

/-! ## take -/

theorem dropExpired_get {now : Nat} {l : Slots} {j : Nat} {x : Slot}
    (h : (dropExpired now l)[j]? = some (some x)) : l[j]? = some (some x) ∧ ¬ x.expiry < now := by
  simp only [dropExpired, List.getElem?_map] at h
  cases hl : l[j]? with
  | none => rw [hl] at h; simp at h
  | some y =>
    rw [hl] at h
    cases y with
    | none => simp at h
    | some z =>
      simp only [Option.map_some, Option.some.injEq, Option.bind_some] at h
      by_cases hz : z.expiry < now
      · simp [hz] at h
      · simp only [hz, ite_false, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hz⟩

theorem dropExpired_length (now : Nat) (l : Slots) : (dropExpired now l).length = l.length := by
  simp [dropExpired]

theorem cTake_length (st : Store) (peer : Peer) (alpn : List Nat) (now : Nat) :
    (cTake st peer alpn now).1.slots.length = st.slots.length := by
  unfold cTake takeIn
  cases firstIdx (matchesKey peer alpn) (dropExpired now st.slots) 0 <;> simp [dropExpired_length]

/-- What `take` leaves is a subset of what it found: every remaining ticket is an unexpired ticket of the old store
in the same slot, and the clock is unchanged. -/
theorem cTake_sub (st : Store) (peer : Peer) (alpn : List Nat) (now : Nat) :
    (∀ (k : Nat) (s : Slot), (cTake st peer alpn now).1.slots[k]? = some (some s) →
      st.slots[k]? = some (some s) ∧ ¬ s.expiry < now) ∧ (cTake st peer alpn now).1.clock = st.clock := by
  unfold cTake takeIn
  cases hf : firstIdx (matchesKey peer alpn) (dropExpired now st.slots) 0 with
  | none => exact ⟨fun k s h => dropExpired_get h, rfl⟩
  | some i =>
    refine ⟨fun k s h => ?_, rfl⟩
    simp only at h
    rcases set_get_cases h with ⟨_, hs, _⟩ | ⟨_, h'⟩
    · cases hs
    · exact dropExpired_get h'

/-- `Tickets.take_unexpired`: after a `take`, no expired ticket is left, and the ticket returned was not expired. -/
theorem take_expired_dropped (st : Store) (peer : Peer) (alpn : List Nat) (now : Nat) :
    ∀ (k : Nat) (s : Slot), (cTake st peer alpn now).1.slots[k]? = some (some s) → ¬ s.expiry < now :=
  fun k s h => ((cTake_sub st peer alpn now).1 k s h).2

/-- A `take` that returns a ticket: it is the first slot of the (expired-dropped) store that holds the peer's ticket
for this ALPN, it was not expired, and the slot is emptied. -/
theorem take_some {st st' : Store} {peer : Peer} {alpn : List Nat} {now : Nat} {t : Tk}
    (h : cTake st peer alpn now = (st', some t)) :
    ∃ (i : Nat) (s : Slot), (dropExpired now st.slots)[i]? = some (some s) ∧ s.tk = t ∧ s.peer = peer ∧ s.alpn = alpn ∧
      ¬ s.expiry < now ∧ st'.slots = (dropExpired now st.slots).set i none ∧ st'.clock = st.clock := by
  unfold cTake takeIn at h
  cases hf : firstIdx (matchesKey peer alpn) (dropExpired now st.slots) 0 with
  | none => rw [hf] at h; simp at h
  | some i =>
    rw [hf] at h
    obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ hf
    simp only [Nat.sub_zero] at hx
    cases x with
    | none => simp [matchesKey] at hp
    | some s =>
      simp only [matchesKey, Option.any_some, decide_eq_true_eq] at hp
      simp only [hx, Option.getD_some, Option.map_some, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨i, s, hx, rfl, hp.1, hp.2, (dropExpired_get hx).2, rfl, rfl⟩

/-- A `take` that finds nothing: no unexpired ticket of the store is for this peer and ALPN, and only the expired
tickets were dropped. -/
theorem take_none {st st' : Store} {peer : Peer} {alpn : List Nat} {now : Nat}
    (h : cTake st peer alpn now = (st', none)) :
    st'.slots = dropExpired now st.slots ∧
      ∀ (k : Nat) (s : Slot), (dropExpired now st.slots)[k]? = some (some s) → ¬ (s.peer = peer ∧ s.alpn = alpn) := by
  unfold cTake takeIn at h
  cases hf : firstIdx (matchesKey peer alpn) (dropExpired now st.slots) 0 with
  | some i =>
    rw [hf] at h
    obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ hf
    simp only [Nat.sub_zero] at hx
    cases x with
    | none => simp [matchesKey] at hp
    | some s => simp [hx] at h
  | none =>
    rw [hf] at h
    simp only [Prod.mk.injEq, and_true] at h
    subst h
    refine ⟨rfl, fun k s hk => ?_⟩
    have := (firstIdx_none_iff _ _ _).1 hf k (some s) hk
    simpa [matchesKey] using this

/-- `Tickets.take_once`: a ticket that `take` returned is not returned again, at any later time: with one ticket per
peer, the second `take` for the same peer finds nothing. -/
theorem take_once {st st' : Store} (ho : OnePerPeer st) {peer : Peer} {alpn : List Nat} {now now' : Nat} {t : Tk}
    (h : cTake st peer alpn now = (st', some t)) : (cTake st' peer alpn now').2 = none := by
  obtain ⟨i, s, hi, hs, hsp, hsa, _, hst, _⟩ := take_some h
  cases h2 : cTake st' peer alpn now' with
  | mk st2 r =>
    cases r with
    | none => rfl
    | some t2 =>
      exfalso
      obtain ⟨j, s2, hj, _, hs2p, _⟩ := take_some h2
      have hj' := (dropExpired_get hj).1
      rw [hst] at hj'
      rcases set_get_cases hj' with ⟨_, hh, _⟩ | ⟨hne, hj''⟩
      · cases hh
      · have hi' := (dropExpired_get hi).1
        have hj3 := (dropExpired_get hj'').1
        exact hne (ho _ _ s2 s hj3 hi' (by rw [hs2p, hsp]))

/-- `Tickets.take_twice`: two successive takes that both return a ticket return tickets from two different slots. -/
theorem take_twice {st st₁ st₂ : Store} {peer : Peer} {alpn : List Nat} {now : Nat} {t t₂ : Tk}
    (h₁ : cTake st peer alpn now = (st₁, some t)) (h₂ : cTake st₁ peer alpn now = (st₂, some t₂)) :
    ∃ i j : Nat, i ≠ j ∧ ∃ s s₂ : Slot, (dropExpired now st.slots)[i]? = some (some s) ∧
      (dropExpired now st.slots)[j]? = some (some s₂) ∧ s.tk = t ∧ s₂.tk = t₂ := by
  obtain ⟨i, s, hi, hs, _, _, _, hl₁, _⟩ := take_some h₁
  obtain ⟨j, s₂, hj, hs₂, _, _, _, _, _⟩ := take_some h₂
  have hj' := (dropExpired_get hj).1
  rw [hl₁] at hj'
  rcases set_get_cases hj' with ⟨_, hh, _⟩ | ⟨hne, hj''⟩
  · cases hh
  · exact ⟨i, j, fun e => hne e.symm, s, s₂, hi, by
      have := (dropExpired_get hj'').1
      have hjd : (dropExpired now st.slots)[j]? = some (some s₂) := by
        have hsd := dropExpired_get (now := now) (l := st.slots) (j := j) (x := s₂)
        simp only [dropExpired, List.getElem?_map] at hsd ⊢
        rw [this]
        simp only [Option.map_some, Option.bind_some]
        have hz := (dropExpired_get hj).2
        simp [hz]
      exact hjd, hs, hs₂⟩

/-- `Tickets.take_wrong_alpn`: a ticket for another ALPN is not returned, and stays stored (if it is not expired). -/
theorem take_alpn {st st' : Store} {peer : Peer} {alpn : List Nat} {now : Nat} {t : Tk}
    (h : cTake st peer alpn now = (st', some t)) : t.peer = peer ∧ t.alpn = alpn ∧ ¬ t.expiry < now := by
  obtain ⟨i, s, _, hs, hsp, hsa, hne, _⟩ := take_some h
  subst hs
  exact ⟨hsp, hsa, hne⟩

theorem client_invariants {N : Nat} {st : Store} (h : CReach N st) :
    st.slots.length = N ∧ OnePerPeer st ∧ StampInv st := by
  induction h with
  | init => exact ⟨by simp [Store.empty], OnePerPeer.empty N, StampInv.empty N⟩
  | insert tk now _ ih => exact ⟨by rw [cInsert_length]; exact ih.1, cInsert_onePerPeer ih.2.1 tk now, cInsert_stamps ih.2.2 tk now⟩
  | @take st0 peer alpn now _ ih =>
    obtain ⟨hl, ho, hs⟩ := ih
    obtain ⟨hsub, hclock⟩ := cTake_sub st0 peer alpn now
    refine ⟨?_, ?_, ?_⟩
    · rw [cTake_length]; exact hl
    · intro i j s t hi hj hp
      exact ho i j s t (hsub i s hi).1 (hsub j t hj).1 hp
    · constructor
      · intro i s hi; rw [hclock]; exact hs.1 i s (hsub i s hi).1
      · intro i j s t hi hj hst
        exact hs.2 i j s t (hsub i s hi).1 (hsub j t hj).1 hst

/-! ## accept_batch -/

theorem acceptBatch_snoc (st : Store) (tks : List Tk) (t : Tk) (now : Nat) :
    acceptBatch st (tks ++ [t]) now = cInsert (acceptBatch st tks now) t now := by
  simp [acceptBatch, List.foldl_append]

theorem acceptBatch_invariants :
    ∀ (tks : List Tk) (st : Store) (n now : Nat), st.slots.length = n → OnePerPeer st → StampInv st →
      (acceptBatch st tks now).slots.length = n ∧ OnePerPeer (acceptBatch st tks now) ∧
      StampInv (acceptBatch st tks now) ∧ (acceptBatch st tks now).clock = st.clock + tks.length := by
  intro tks
  induction tks with
  | nil => intro st n now hl ho hs; exact ⟨hl, ho, hs, by simp [acceptBatch]⟩
  | cons t tks ih =>
    intro st n now hl ho hs
    have : acceptBatch st (t :: tks) now = acceptBatch (cInsert st t now) tks now := rfl
    rw [this]
    obtain ⟨h1, h2, h3, h4⟩ := ih (cInsert st t now) n now (by rw [cInsert_length]; exact hl)
      (cInsert_onePerPeer ho t now) (cInsert_stamps hs t now)
    exact ⟨h1, h2, h3, by rw [h4, cInsert_clock]; simp; omega⟩

/-- `Tickets.accept_batch_last_kept`: after a batch of tickets of one peer into a store with a slot, exactly one slot
holds a ticket of that peer, and it is the last ticket of the batch, stamped with the clock value of its insertion. -/
theorem accept_batch_last_kept {st : Store} {n : Nat} (hl : st.slots.length = n) (hn : n ≠ 0) (ho : OnePerPeer st)
    (hs : StampInv st) {p : Peer} {tks : List Tk} (hp : ∀ t ∈ tks, t.peer = p) {t : Tk} (htp : t.peer = p) (now : Nat) :
    ∃ i : Nat, (acceptBatch st (tks ++ [t]) now).slots[i]? = some (some (Slot.mk t (st.clock + tks.length + 1))) ∧
      ∀ (k : Nat) (s : Slot), (acceptBatch st (tks ++ [t]) now).slots[k]? = some (some s) → s.peer = p → k = i := by
  have _ := hp
  rw [acceptBatch_snoc]
  obtain ⟨h1, h2, h3, h4⟩ := acceptBatch_invariants tks st n now hl ho hs
  have hne : (acceptBatch st tks now).slots ≠ [] := by
    intro e; rw [e] at h1; simp at h1; exact hn h1.symm
  obtain ⟨i, hi⟩ := cInsert_places hne t now
  refine ⟨i, by rw [h4] at hi; exact hi, fun k s hk hsp => ?_⟩
  exact cInsert_onePerPeer h2 t now k i s _ hk hi (by rw [hsp]; exact htp.symm)

/-- `Tickets.client_len`: a client store has `N` slots, so it holds at most `N` tickets, one per peer; `N = 0` stores
nothing. -/
theorem client_len {N : Nat} {st : Store} (h : CReach N st) : st.slots.length = N ∧ occ st.slots ≤ N := by
  have := (client_invariants h).1
  exact ⟨this, by have := occ_le st.slots; omega⟩

theorem client_zero {st : Store} (h : CReach 0 st) : occ st.slots = 0 := by
  have := (client_len h).2; omega

/-- `Tickets.client_one_per_peer`: over every reachable client store, no two slots hold tickets of the same peer. -/
theorem client_one_per_peer {N : Nat} {st : Store} (h : CReach N st) : OnePerPeer st := (client_invariants h).2.1

theorem client_stamps {N : Nat} {st : Store} (h : CReach N st) : StampInv st := (client_invariants h).2.2

end Vinc.Tickets

#audit_axioms Vinc.Tickets.cInsert_onePerPeer
#audit_axioms Vinc.Tickets.cInsert_stamps
#audit_axioms Vinc.Tickets.cInsert_places
#audit_axioms Vinc.Tickets.cInsert_nil
#audit_axioms Vinc.Tickets.client_insert_same_peer
#audit_axioms Vinc.Tickets.client_insert_new_peer
#audit_axioms Vinc.Tickets.client_evicts_oldest
#audit_axioms Vinc.Tickets.take_expired_dropped
#audit_axioms Vinc.Tickets.take_some
#audit_axioms Vinc.Tickets.take_none
#audit_axioms Vinc.Tickets.take_once
#audit_axioms Vinc.Tickets.take_twice
#audit_axioms Vinc.Tickets.take_alpn
#audit_axioms Vinc.Tickets.accept_batch_last_kept
#audit_axioms Vinc.Tickets.client_len
#audit_axioms Vinc.Tickets.client_zero
#audit_axioms Vinc.Tickets.client_one_per_peer
#audit_axioms Vinc.Tickets.client_stamps
