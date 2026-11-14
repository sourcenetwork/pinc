import Vinc.Axioms
import Vinc.TransportEarly

/-!
# Packets that arrive before their keys: bounded, held only when documented, tried once, gone with the connection

What the model proves about the buffer of early packets, for any bound `cap` and any run of packets:

- the buffer holds at most `cap` packets, oldest first in the order of arrival, and only while the connection is
  handshaking; a 0-RTT packet is in it only on a server (`Inv`, `recv_inv`, `established_inv`, `shut_inv`);
- a packet is kept exactly when it is eligible (a 0-RTT packet on a server in its handshake without early keys, a
  1-RTT packet in a handshake before the 1-RTT keys exist: `eligible_iff`) and the buffer has a place and the pool
  has room, and then it goes last (`recv_held`); no other packet is held (`recv_held_eligible`);
- when the buffer is full the packet that arrives is the one lost and the packets held stay, counted as dropped
  (`recv_full`): an attacker who fills the buffer with junk first makes every later early packet, real ones too, be
  refused until the session is established; the handshake messages themselves are not held (they are Handshake
  packets, which `recv` never sees) and go on;
- a packet that does not open is lost; a 1-RTT one is counted as undecryptable and a 0-RTT one is not (`recv_nu`);
- establishing the session tries the packets held once each, oldest first, with the 1-RTT keys in place, and leaves
  none: the ids tried are a prefix of the ids held in order, all of them unless one of them closed the connection
  (`established_ids`, `established_all`, `established_once`); the counters of what was held and dropped and the
  bytes received are as they were (`established_count`);
- nothing held survives the close (`shut_q`, `recv_closed`);
- amplification: a datagram counts toward the bytes received on arrival, whether it is held, refused or opened, and
  trying the held packets later counts nothing (`recv_amp`, `established_count`);
- a 0-RTT packet that opens and carries a frame only an established session sends (ACK, CLOSE, REKEY, NEW_TICKETS or
  PATH_RESPONSE) is dropped whole: it is counted as refused and changes nothing else, and the connection stays open;
  no other packet is refused, and only a refusal moves the count (`direct_refused`, `recv_refused`); the drain
  refuses at most the 0-RTT packets held that carry such a frame, and none once the early keys are gone
  (`established_nr`).
-/

namespace Vinc.TransportEarly

/-- The buffer is well formed: within the bound, in the order of arrival, only in a handshake, a 0-RTT packet only on
a server. -/
structure Inv (cap : Nat) (c : C) : Prop where
  bound : c.q.length ≤ cap
  sorted : (c.q.map Pkt.id).Pairwise (· < ·)
  phase : c.q ≠ [] → c.ph = .hs
  kinds : ∀ p ∈ c.q, p.kind = .z → c.client = false

theorem eligible_iff (c : C) (p : Pkt) :
    eligible c p = true ↔
      c.ph = .hs ∧ ((p.kind = .z ∧ c.er = false ∧ c.client = false) ∨ (p.kind = .s ∧ c.rv = false)) := by
  rcases p with ⟨id, k, f⟩
  cases k <;> simp [eligible]

theorem shut_q (c : C) : (shut c).q = [] ∧ (shut c).ph = .closed := ⟨rfl, rfl⟩

theorem shut_inv (cap : Nat) (c : C) : Inv cap (shut c) :=
  ⟨by simp [shut], by simp [shut], by simp [shut], by simp [shut]⟩

theorem direct_shape (c : C) (p : Pkt) :
    (((direct c p).2.q = c.q ∧ (direct c p).2.ph = c.ph) ∨ ((direct c p).2.q = [] ∧ (direct c p).2.ph = .closed)) ∧
      (direct c p).2.client = c.client ∧ (direct c p).2.rv = c.rv ∧ (direct c p).2.rx = c.rx ∧
      (direct c p).2.nb = c.nb ∧ (direct c p).2.nd = c.nd := by
  rcases c with ⟨cl, ph, er, rv, q, nb, nd, nu, rx, nr⟩
  rcases p with ⟨id, k, f⟩
  cases k <;> cases f <;> cases er <;> simp [direct, shut]

theorem direct_nu (c : C) (p : Pkt) :
    (direct c p).2.nu = c.nu + (if p.kind = .s ∧ p.fate = .fails then 1 else 0) := by
  rcases c with ⟨cl, ph, er, rv, q, nb, nd, nu, rx, nr⟩
  rcases p with ⟨id, k, f⟩
  cases k <;> cases f <;> cases er <;> simp [direct, shut]

theorem direct_open (c : C) (p : Pkt) (h : p.fate ≠ .closes) : (direct c p).2.ph = c.ph ∧ (direct c p).2.q = c.q := by
  rcases c with ⟨cl, ph, er, rv, q, nb, nd, nu, rx, nr⟩
  rcases p with ⟨id, k, f⟩
  cases k <;> cases f <;> cases er <;> simp_all [direct]

/-- A 0-RTT packet that opens and carries a frame only an established session sends is refused, and the refusal
changes nothing but the count of refused packets; no other packet is refused. -/
theorem direct_refused (c : C) (p : Pkt) :
    ((direct c p).1 = .refused ↔ p.kind = .z ∧ c.er = true ∧ p.fate = .estOnly) ∧
      ((direct c p).1 = .refused → (direct c p).2 = { c with nr := c.nr + 1 }) := by
  rcases c with ⟨cl, ph, er, rv, q, nb, nd, nu, rx, nr⟩
  rcases p with ⟨id, k, f⟩
  cases k <;> cases f <;> cases er <;> simp [direct, shut]

/-- Only a refusal moves the count of refused packets. -/
theorem direct_nr (c : C) (p : Pkt) :
    (direct c p).2.nr = c.nr + (if (direct c p).1 = .refused then 1 else 0) := by
  rcases c with ⟨cl, ph, er, rv, q, nb, nd, nu, rx, nr⟩
  rcases p with ⟨id, k, f⟩
  cases k <;> cases f <;> cases er <;> simp [direct, shut]

/-- A packet tried adds at most one refusal, and only a 0-RTT one with a frame only an established session sends;
without early keys it adds none, and the early keys stay gone. -/
theorem direct_nr_le (c : C) (p : Pkt) :
    (direct c p).2.nr ≤ c.nr + (if p.kind = .z ∧ p.fate = .estOnly then 1 else 0) ∧
      (c.er = false → (direct c p).2.nr = c.nr ∧ (direct c p).2.er = false) := by
  rcases c with ⟨cl, ph, er, rv, q, nb, nd, nu, rx, nr⟩
  rcases p with ⟨id, k, f⟩
  cases k <;> cases f <;> cases er <;> simp [direct, shut] <;> omega

theorem live_rx (c : C) (cap : Nat) (room : Bool) (p : Pkt) : (live c cap room p).2.rx = c.rx := by
  unfold live
  split
  · unfold holdPkt; split <;> simp
  · split
    · simp
    · exact (direct_shape c p).2.2.2.1

theorem live_held (c : C) (cap : Nat) (room : Bool) (p : Pkt) (he : eligible c p = true) (hl : c.q.length < cap)
    (hr : room = true) :
    (live c cap room p).1 = .held ∧ (live c cap room p).2.q = c.q ++ [p] ∧
      (live c cap room p).2.nb = c.nb + 1 ∧ (live c cap room p).2.nd = c.nd := by
  simp [live, he, holdPkt, hl, hr]

theorem live_full (c : C) (cap : Nat) (room : Bool) (p : Pkt) (he : eligible c p = true)
    (hf : cap ≤ c.q.length ∨ room = false) :
    (live c cap room p).1 = .full ∧ (live c cap room p).2.q = c.q ∧
      (live c cap room p).2.nd = c.nd + 1 ∧ (live c cap room p).2.nb = c.nb := by
  have hn : ¬(c.q.length < cap ∧ room = true) := by
    rintro ⟨h1, h2⟩
    rcases hf with h3 | h3
    · omega
    · simp [h2] at h3
  simp [live, he, holdPkt, hn]

theorem live_held_eligible (c : C) (cap : Nat) (room : Bool) (p : Pkt) (h : (live c cap room p).1 = .held) :
    eligible c p = true := by
  unfold live at h
  by_cases he : eligible c p = true
  · exact he
  · rw [if_neg he] at h
    split at h
    · simp at h
    · rcases c with ⟨cl, ph, er, rv, q, nb, nd, nu, rx, nr⟩
      rcases p with ⟨id, k, f⟩
      cases k <;> cases f <;> cases er <;> simp [direct, shut] at h

theorem live_nu (c : C) (cap : Nat) (room : Bool) (p : Pkt) :
    (live c cap room p).2.nu = c.nu + (if p.kind = .s ∧ c.rv = true ∧ p.fate = .fails then 1 else 0) := by
  unfold live
  by_cases he : eligible c p = true
  · rw [if_pos he]
    have h := (eligible_iff _ _).1 he
    unfold holdPkt
    rcases h with ⟨-, ⟨hk, -, -⟩ | ⟨hk, hv⟩⟩
    · split <;> simp [hk]
    · split <;> simp [hk, hv]
  · rw [if_neg he]
    by_cases hs : p.kind = .s ∧ c.rv = false
    · rw [if_pos hs]
      simp [hs.1, hs.2]
    · rw [if_neg hs, direct_nu]
      by_cases hk : p.kind = .s
      · have hrv : c.rv = true := by
          cases hv : c.rv
          · exact absurd ⟨hk, hv⟩ hs
          · rfl
        simp [hk, hrv]
      · simp [hk]

theorem live_refused (c : C) (cap : Nat) (room : Bool) (p : Pkt) :
    ((live c cap room p).1 = .refused ↔ eligible c p = false ∧ p.kind = .z ∧ c.er = true ∧ p.fate = .estOnly) ∧
      ((live c cap room p).1 = .refused → (live c cap room p).2 = { c with nr := c.nr + 1 }) ∧
      (live c cap room p).2.nr = c.nr + (if (live c cap room p).1 = .refused then 1 else 0) := by
  unfold live
  by_cases he : eligible c p = true
  · rw [if_pos he]
    unfold holdPkt
    split <;> simp [he]
  · rw [if_neg he]
    have hf : eligible c p = false := by simpa using he
    by_cases hs : p.kind = .s ∧ c.rv = false
    · rw [if_pos hs]
      simp [hs.1]
    · rw [if_neg hs]
      obtain ⟨h1, h2⟩ := direct_refused c p
      refine ⟨?_, h2, direct_nr c p⟩
      rw [h1, hf]
      simp

theorem live_inv (cap : Nat) (c : C) (room : Bool) (p : Pkt) (hi : Inv cap c) (hfresh : ∀ x ∈ c.q, x.id < p.id) :
    Inv cap (live c cap room p).2 := by
  unfold live
  by_cases he : eligible c p = true
  · rw [if_pos he]
    unfold holdPkt
    split
    · rename_i hl
      have hel := (eligible_iff _ _).1 he
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp; omega
      · simp only [List.map_append, List.map_cons, List.map_nil]
        rw [List.pairwise_append]
        refine ⟨hi.sorted, by simp, ?_⟩
        intro a ha b hb
        simp at hb
        subst hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        exact hfresh x hx
      · simp [hel.1]
      · intro x hx hk
        simp at hx
        rcases hx with hx | rfl
        · exact hi.kinds x hx hk
        · rcases hel.2 with ⟨_, _, h3⟩ | ⟨h3, _⟩
          · exact h3
          · exact absurd hk (by simp [h3])
    · exact ⟨hi.bound, hi.sorted, hi.phase, hi.kinds⟩
  · rw [if_neg he]
    split
    · exact ⟨hi.bound, hi.sorted, hi.phase, hi.kinds⟩
    · obtain ⟨hq, hcl, -⟩ := direct_shape c p
      refine ⟨?_, ?_, ?_, ?_⟩
      · rcases hq with ⟨hq, -⟩ | ⟨hq, -⟩ <;> simp [hq]
        exact hi.bound
      · rcases hq with ⟨hq, -⟩ | ⟨hq, -⟩
        · simpa [hq] using hi.sorted
        · simp [hq]
      · intro hne
        rcases hq with ⟨hq, hp⟩ | ⟨hq, -⟩
        · rw [hp]
          exact hi.phase (by simpa [hq] using hne)
        · simp [hq] at hne
      · intro x hx hk
        rcases hq with ⟨hq, -⟩ | ⟨hq, -⟩
        · rw [hq] at hx
          simpa [hcl] using hi.kinds x hx hk
        · simp [hq] at hx

theorem recv_closed (c : C) (cap : Nat) (room : Bool) (p : Pkt) (dlen : Nat) (h : c.ph = .closed) :
    recv c cap room p dlen = (.closed, c) := by
  simp [recv, h]

theorem recv_live (c : C) (cap : Nat) (room : Bool) (p : Pkt) (dlen : Nat) (h : c.ph ≠ .closed) :
    recv c cap room p dlen = live { c with rx := c.rx + dlen } cap room p := by
  simp [recv, h]

/-- A datagram counts on arrival, held or not. -/
theorem recv_amp (c : C) (cap : Nat) (room : Bool) (p : Pkt) (dlen : Nat) (h : c.ph ≠ .closed) :
    (recv c cap room p dlen).2.rx = c.rx + dlen := by
  rw [recv_live c cap room p dlen h, live_rx]

theorem recv_held (c : C) (cap : Nat) (room : Bool) (p : Pkt) (dlen : Nat) (h : c.ph ≠ .closed)
    (he : eligible { c with rx := c.rx + dlen } p = true) (hl : c.q.length < cap) (hr : room = true) :
    (recv c cap room p dlen).1 = .held ∧ (recv c cap room p dlen).2.q = c.q ++ [p] ∧
      (recv c cap room p dlen).2.nb = c.nb + 1 ∧ (recv c cap room p dlen).2.nd = c.nd := by
  rw [recv_live c cap room p dlen h]
  exact live_held _ cap room p he hl hr

/-- A full buffer (or a pool without room) refuses the packet that arrives; the packets held stay. -/
theorem recv_full (c : C) (cap : Nat) (room : Bool) (p : Pkt) (dlen : Nat) (h : c.ph ≠ .closed)
    (he : eligible { c with rx := c.rx + dlen } p = true) (hf : cap ≤ c.q.length ∨ room = false) :
    (recv c cap room p dlen).1 = .full ∧ (recv c cap room p dlen).2.q = c.q ∧
      (recv c cap room p dlen).2.nd = c.nd + 1 ∧ (recv c cap room p dlen).2.nb = c.nb := by
  rw [recv_live c cap room p dlen h]
  exact live_full _ cap room p he hf

/-- Only a packet the documented rule makes eligible is ever held. -/
theorem recv_held_eligible (c : C) (cap : Nat) (room : Bool) (p : Pkt) (dlen : Nat)
    (h : (recv c cap room p dlen).1 = .held) :
    c.ph = .hs ∧ ((p.kind = .z ∧ c.er = false ∧ c.client = false) ∨ (p.kind = .s ∧ c.rv = false)) := by
  by_cases hc : c.ph = .closed
  · rw [recv_closed c cap room p dlen hc] at h
    simp at h
  · rw [recv_live c cap room p dlen hc] at h
    have he := live_held_eligible _ cap room p h
    exact (eligible_iff _ _).1 he

theorem recv_nu (c : C) (cap : Nat) (room : Bool) (p : Pkt) (dlen : Nat) (h : c.ph ≠ .closed) :
    (recv c cap room p dlen).2.nu =
      c.nu + (if p.kind = .s ∧ c.rv = true ∧ p.fate = .fails then 1 else 0) := by
  rw [recv_live c cap room p dlen h, live_nu]

/-- A 0-RTT packet that opens and carries a frame only an established session sends (ACK, CLOSE, REKEY, NEW_TICKETS
or PATH_RESPONSE) is dropped whole: it is counted as refused and nothing else changes but the bytes received, which
every datagram counts on arrival; the connection stays open. No other packet is refused so, and only a refusal moves
the count. -/
theorem recv_refused (c : C) (cap : Nat) (room : Bool) (p : Pkt) (dlen : Nat) (h : c.ph ≠ .closed) :
    ((recv c cap room p dlen).1 = .refused ↔
        eligible { c with rx := c.rx + dlen } p = false ∧ p.kind = .z ∧ c.er = true ∧ p.fate = .estOnly) ∧
      ((recv c cap room p dlen).1 = .refused →
        (recv c cap room p dlen).2 = { c with rx := c.rx + dlen, nr := c.nr + 1 }) ∧
      (recv c cap room p dlen).2.nr = c.nr + (if (recv c cap room p dlen).1 = .refused then 1 else 0) := by
  rw [recv_live c cap room p dlen h]
  exact live_refused _ cap room p

theorem recv_inv (cap : Nat) (c : C) (room : Bool) (p : Pkt) (dlen : Nat) (hi : Inv cap c)
    (hfresh : ∀ x ∈ c.q, x.id < p.id) : Inv cap (recv c cap room p dlen).2 := by
  by_cases hc : c.ph = .closed
  · rw [recv_closed c cap room p dlen hc]
    exact hi
  · rw [recv_live c cap room p dlen hc]
    exact live_inv cap _ room p ⟨hi.bound, hi.sorted, hi.phase, hi.kinds⟩ hfresh

theorem earlyKeys_inv (cap : Nat) (c : C) (hi : Inv cap c) : Inv cap (earlyKeys c) :=
  ⟨hi.bound, hi.sorted, hi.phase, hi.kinds⟩

/-- The packets tried by the drain: what is left in the buffer is nothing, the ids are a prefix of the ids held in
order, the counters of holds and the bytes received are as they were, and a drain none of whose packets closes the
connection tries them all and counts the 1-RTT ones that fail. -/
theorem drainQ_spec (l : List Pkt) : ∀ c : C, c.ph ≠ .closed →
    (drainQ c l).1.q = [] ∧ (∃ k, (drainQ c l).2 = (l.map Pkt.id).take k) ∧ (drainQ c l).1.rx = c.rx ∧
      (drainQ c l).1.nb = c.nb ∧ (drainQ c l).1.nd = c.nd ∧ (drainQ c l).1.rv = c.rv ∧
      (drainQ c l).1.client = c.client ∧
      ((∀ p ∈ l, p.fate ≠ .closes) →
        (drainQ c l).2 = l.map Pkt.id ∧ (drainQ c l).1.ph = c.ph ∧
          (drainQ c l).1.nu = c.nu + (l.filter (fun p => p.kind = .s ∧ p.fate = .fails)).length) := by
  induction l with
  | nil =>
    intro c _
    simp [drainQ]
  | cons p t ih =>
    intro c hc
    unfold drainQ
    obtain ⟨hq, hcl, hrv, hrx, hnb, hnd⟩ := direct_shape c p
    dsimp only
    split
    · rename_i hcl2
      rcases hq with ⟨-, hp⟩ | ⟨hq, -⟩
      · exact absurd (hp ▸ hcl2) hc
      · refine ⟨hq, ⟨1, by simp⟩, hrx, hnb, hnd, hrv, hcl, ?_⟩
        intro hall
        exact absurd (by simpa using hcl2) (by
          have := (direct_open c p (hall p (by simp))).1
          rw [this]; exact hc)
    · rename_i hncl
      obtain ⟨h1, ⟨k, hk⟩, h3, h4, h5, h6, h7, h8⟩ := ih (direct c p).2 hncl
      refine ⟨h1, ⟨k + 1, by simp [hk]⟩, by rw [h3, hrx], by rw [h4, hnb], by rw [h5, hnd], by rw [h6, hrv],
        by rw [h7, hcl], ?_⟩
      intro hall
      have hall' : ∀ q ∈ t, q.fate ≠ .closes := fun q hq => hall q (List.mem_cons_of_mem _ hq)
      obtain ⟨g1, g2, g3⟩ := h8 hall'
      have hop := direct_open c p (hall p (by simp))
      refine ⟨by simp [g1], by rw [g2, hop.1], ?_⟩
      rw [g3, direct_nu]
      by_cases hs : p.kind = .s ∧ p.fate = .fails
      · simp [hs]
        omega
      · simp [hs]

theorem established_ids (c : C) :
    ∃ k, (established c).2 = (c.q.map Pkt.id).take k := by
  exact (drainQ_spec c.q { c with ph := .up, rv := true } (by simp)).2.1

theorem established_all (c : C) (h : ∀ p ∈ c.q, p.fate ≠ .closes) :
    (established c).2 = c.q.map Pkt.id := by
  exact ((drainQ_spec c.q { c with ph := .up, rv := true } (by simp)).2.2.2.2.2.2.2 h).1

/-- Each packet held is tried at most once: with distinct ids in the buffer, the ids tried are distinct. -/
theorem established_once (c : C) (hn : (c.q.map Pkt.id).Nodup) :
    (established c).2.Nodup := by
  obtain ⟨k, hk⟩ := established_ids c
  rw [hk]
  exact hn.sublist (List.take_sublist _ _)

/-- Establishing the session leaves nothing held, with the 1-RTT keys in place, and counts nothing arriving. -/
theorem established_count (c : C) :
    (established c).1.q = [] ∧ (established c).1.rv = true ∧ (established c).1.rx = c.rx ∧
      (established c).1.nb = c.nb ∧ (established c).1.nd = c.nd := by
  obtain ⟨h1, -, h3, h4, h5, h6, -⟩ := drainQ_spec c.q { c with ph := .up, rv := true } (by simp)
  exact ⟨h1, h6, h3, h4, h5⟩

theorem established_nu (c : C) (h : ∀ p ∈ c.q, p.fate ≠ .closes) :
    (established c).1.nu = c.nu + (c.q.filter (fun p => p.kind = .s ∧ p.fate = .fails)).length := by
  exact ((drainQ_spec c.q { c with ph := .up, rv := true } (by simp)).2.2.2.2.2.2.2 h).2.2

/-- The drain refuses at most the 0-RTT packets held that carry a frame only an established session sends, and none
once the early keys are gone. -/
theorem drainQ_nr (l : List Pkt) : ∀ c : C,
    (drainQ c l).1.nr ≤ c.nr + (l.filter (fun p => p.kind = .z ∧ p.fate = .estOnly)).length ∧
      (c.er = false → (drainQ c l).1.nr = c.nr) := by
  induction l with
  | nil => intro c; simp [drainQ]
  | cons p t ih =>
    intro c
    obtain ⟨h1, h2⟩ := direct_nr_le c p
    have hf : ((p :: t).filter (fun p => p.kind = .z ∧ p.fate = .estOnly)).length =
        (if p.kind = .z ∧ p.fate = .estOnly then 1 else 0) +
          (t.filter (fun p => p.kind = .z ∧ p.fate = .estOnly)).length := by
      rcases p with ⟨id, k, f⟩
      cases k <;> cases f <;> simp [List.filter_cons] <;> omega
    unfold drainQ
    dsimp only
    split
    · dsimp only
      exact ⟨by rw [hf]; omega, fun he => (h2 he).1⟩
    · dsimp only
      obtain ⟨i1, i2⟩ := ih (direct c p).2
      exact ⟨by rw [hf]; omega, fun he => by rw [i2 (h2 he).2, (h2 he).1]⟩

/-- Establishing the session refuses at most the 0-RTT packets held that carry a frame only an established session
sends, and none when the Hello brought no early keys. -/
theorem established_nr (c : C) :
    (established c).1.nr ≤ c.nr + (c.q.filter (fun p => p.kind = .z ∧ p.fate = .estOnly)).length ∧
      (c.er = false → (established c).1.nr = c.nr) :=
  drainQ_nr c.q { c with ph := .up, rv := true }

theorem established_inv (cap : Nat) (c : C) : Inv cap (established c).1 := by
  have h := (established_count c).1
  have hcl := (drainQ_spec c.q { c with ph := .up, rv := true } (by simp)).2.2.2.2.2.2.1
  exact ⟨by simp [h], by simp [h], by simp [h], by simp [h]⟩

#audit_axioms Vinc.TransportEarly.eligible_iff
#audit_axioms Vinc.TransportEarly.live_inv
#audit_axioms Vinc.TransportEarly.recv_inv
#audit_axioms Vinc.TransportEarly.recv_held
#audit_axioms Vinc.TransportEarly.recv_full
#audit_axioms Vinc.TransportEarly.recv_held_eligible
#audit_axioms Vinc.TransportEarly.recv_nu
#audit_axioms Vinc.TransportEarly.recv_amp
#audit_axioms Vinc.TransportEarly.established_ids
#audit_axioms Vinc.TransportEarly.established_all
#audit_axioms Vinc.TransportEarly.established_once
#audit_axioms Vinc.TransportEarly.established_count
#audit_axioms Vinc.TransportEarly.established_inv
#audit_axioms Vinc.TransportEarly.direct_refused
#audit_axioms Vinc.TransportEarly.recv_refused
#audit_axioms Vinc.TransportEarly.established_nr

end Vinc.TransportEarly
