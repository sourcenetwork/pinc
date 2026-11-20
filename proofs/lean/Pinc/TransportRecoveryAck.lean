import Pinc.TransportRecoveryRing

/-!
# Loss recovery: what the acknowledgement loop reports, and two more conjuncts of `RingShape`

The counterpart of `detectLoop_lost_inflight` for the acknowledgement loop (`ackRing_events`, lifted through
`ackRange1_events` and `ackRanges_events`): every `acked` event the loop appends is for a slot that was in flight in
the state the loop found it in, with that slot's number, size, frames, probe and repair flags; every `late` event is
for a slot that was a ghost, with the frames of the ghost that carry data; no other event is appended.

The two conjuncts of `RingShape` of `Recovery.tla` not yet proved: every slot's path is below the path count
(`RingPath`), and the largest acknowledged number is not above the last one sent (`LaLs`); both are kept by `send`,
`untracked`, `ack`, `timeout` and `flush`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Pinc.TransportRecovery

/-! ### The events of the acknowledgement loop -/

/-- `e` is the event of a slot of `ring` at or after `i`: an `acked` event of one in flight, a `late` event of a
ghost. -/
def AckSrc (ring : List Slot) (i : Nat) (e : Ev) : Prop :=
  ∃ j, i ≤ j ∧ ∃ sl, ring[j]? = some sl ∧
    ((sl.st = .fl ∧ e = ⟨"acked", sl.pn, sl.size, sl.fr, sl.probe, sl.rep, 0, false⟩) ∨
     (sl.st = .lost ∧ e = ⟨"late", sl.pn, 0, sl.fr.filter id, sl.probe, false, sl.path, false⟩))

/-- The same without the place: `e` is the event of a slot of the ring. -/
def AckFrom (ring : List Slot) (e : Ev) : Prop :=
  ∃ sl ∈ ring,
    ((sl.st = .fl ∧ e = ⟨"acked", sl.pn, sl.size, sl.fr, sl.probe, sl.rep, 0, false⟩) ∨
     (sl.st = .lost ∧ e = ⟨"late", sl.pn, 0, sl.fr.filter id, sl.probe, false, sl.path, false⟩))

theorem AckSrc.mono {ring ring' : List Slot} {i : Nat} {e : Ev} (h : ∀ j, i + 1 ≤ j → ring'[j]? = ring[j]?)
    (a : AckSrc ring' (i + 1) e) : AckSrc ring i e := by
  obtain ⟨j, hj, sl, h1, h2⟩ := a
  exact ⟨j, by omega, sl, by rw [← h j hj]; exact h1, h2⟩

theorem AckSrc.from {ring : List Slot} {i : Nat} {e : Ev} (a : AckSrc ring i e) : AckFrom ring e := by
  obtain ⟨j, _, sl, h1, h2⟩ := a
  exact ⟨sl, List.mem_of_getElem? h1, h2⟩

theorem upd_get_at {α : Type} (f : α → α) : ∀ (l : List α) (i : Nat) (a : α), l[i]? = some a → (upd l i f)[i]? = some (f a)
  | [], i, a, h => by simp at h
  | x :: xs, 0, a, h => by simp at h; simp [upd, h]
  | x :: xs, i + 1, a, h => by simpa [upd] using upd_get_at f xs i a (by simpa using h)

theorem noteOvertaken_ring_upd (p : P) (r : R) (i now pn time path : Nat) :
    (noteOvertaken p { r with ring := upd r.ring i fun s => { s with st := .done } } now pn time path).ring =
      upd r.ring i fun s => { s with st := .done } :=
  (noteOvertaken_keep p _ now pn time path).1

/-- Every `acked` event the loop appends is for a slot that was in flight, every `late` event for a ghost, in the
ring the loop found at or after the place it started from; it appends no other event. -/
theorem ackRing_events (p : P) (now b : Nat) :
    ∀ (n i : Nat) (x : X) (e : Ev), e ∈ (ackRing p now b n i x).ev → e ∈ x.ev ∨ AckSrc x.r.ring i e
  | 0, i, x, e, h => by simp [ackRing] at h; exact Or.inl h
  | n + 1, i, x, e, h => by
    unfold ackRing at h
    rcases hs : x.r.ring[i]? with _ | sl
    · simp [hs] at h; exact Or.inl h
    · simp only [hs] at h
      split at h
      · exact Or.inl h
      · rename_i c1
        split at h
        · rcases ackRing_events p now b n (i + 1) x e h with a | a
          · exact Or.inl a
          · exact Or.inr (a.mono fun j _ => rfl)
        · rename_i c2
          split at h
          · rcases ackRing_events p now b n (i + 1) x e h with a | a
            · exact Or.inl a
            · exact Or.inr (a.mono fun j _ => rfl)
          · rename_i c3
            split at h
            · rcases ackRing_events p now b n (i + 1) _ e h with a | a
              · exact Or.inl a
              · exact Or.inr (a.mono fun j hj => upd_get_ne _ _ _ _ (by omega))
            · rename_i c4
              have ho := noteOvertaken_ring_upd p x.r i now sl.pn sl.time sl.path
              split at h
              · rename_i hl
                rcases ackRing_events p now b n (i + 1) _ e h with a | a
                · simp at a
                  rcases a with a | a
                  · exact Or.inl a
                  · exact Or.inr ⟨i, Nat.le_refl _, sl, hs, Or.inr ⟨by simpa using hl, by rw [a]⟩⟩
                · refine Or.inr (a.mono fun j hj => ?_)
                  simp only [ho]
                  exact upd_get_ne _ _ _ _ (by omega)
              · rename_i hl
                rcases ackRing_events p now b n (i + 1) _ e h with a | a
                · simp at a
                  rcases a with a | a
                  · exact Or.inl a
                  · have hfl : sl.st = .fl := by
                      cases hh : sl.st <;> simp_all
                    exact Or.inr ⟨i, Nat.le_refl _, sl, hs, Or.inl ⟨hfl, by rw [a]⟩⟩
                · refine Or.inr (a.mono fun j hj => ?_)
                  simp only [ho]
                  exact upd_get_ne _ _ _ _ (by omega)

/-- Slot by slot, the second ring is the first one with some slots done: the loop moves nothing else. -/
def Dn (a b : List Slot) : Prop :=
  ∀ j : Nat, b[j]? = a[j]? ∨ ∃ sl : Slot, a[j]? = some sl ∧ b[j]? = some { sl with st := .done }

theorem Dn.trans {a b c : List Slot} (h1 : Dn a b) (h2 : Dn b c) : Dn a c := by
  unfold Dn at *
  intro j
  rcases h2 j with e | ⟨s, hs, e⟩
  · rcases h1 j with e1 | ⟨s1, hs1, e1⟩
    · exact Or.inl (e.trans e1)
    · exact Or.inr ⟨s1, hs1, e.trans e1⟩
  · rcases h1 j with e1 | ⟨s1, hs1, e1⟩
    · exact Or.inr ⟨s, e1 ▸ hs, e⟩
    · rw [e1] at hs
      have := Option.some.inj hs
      subst this
      exact Or.inr ⟨s1, hs1, by simpa using e⟩

theorem Dn.refl (a : List Slot) : Dn a a := by
  unfold Dn
  exact fun _ => Or.inl rfl

theorem dn_upd (l : List Slot) (i : Nat) : Dn l (upd l i fun s => { s with st := .done }) := by
  unfold Dn
  intro j
  by_cases h : j = i
  · subst h
    rcases hs : l[j]? with _ | sl
    · left
      have := upd_get_self (fun s : Slot => { s with st := .done }) id l j
      rw [hs] at this
      simpa using this
    · exact Or.inr ⟨sl, rfl, upd_get_at _ l j sl hs⟩
  · exact Or.inl (upd_get_ne _ _ _ _ h)

theorem ackRing_dn (p : P) (now b : Nat) :
    ∀ (n i : Nat) (x : X), Dn x.r.ring (ackRing p now b n i x).r.ring
  | 0, i, x => by simpa [ackRing] using Dn.refl _
  | n + 1, i, x => by
    unfold ackRing
    rcases hs : x.r.ring[i]? with _ | sl
    · simpa using Dn.refl _
    · simp only [hs]
      have ho := noteOvertaken_ring_upd p x.r i now sl.pn sl.time sl.path
      have hd := dn_upd x.r.ring i
      have hd2 : Dn x.r.ring (noteOvertaken p { x.r with ring := upd x.r.ring i fun s => { s with st := .done } }
          now sl.pn sl.time sl.path).ring := by rw [ho]; exact hd
      split
      · exact Dn.refl _
      · split
        · exact ackRing_dn p now b n (i + 1) x
        · split
          · exact ackRing_dn p now b n (i + 1) x
          · split
            · exact Dn.trans hd (ackRing_dn p now b n (i + 1) _)
            · split
              · exact Dn.trans hd2 (ackRing_dn p now b n (i + 1) _)
              · exact Dn.trans hd2 (ackRing_dn p now b n (i + 1) _)

theorem ackRange1_dn (p : P) (now a b : Nat) (x : X) : Dn x.r.ring (ackRange1 p now a b x).r.ring := by
  unfold ackRange1
  dsimp only
  exact ackRing_dn p now b _ _ _

theorem ackRange1_events (p : P) (now a b : Nat) (x : X) (e : Ev) (h : e ∈ (ackRange1 p now a b x).ev) :
    e ∈ x.ev ∨ AckFrom x.r.ring e := by
  unfold ackRange1 at h
  dsimp only at h
  rcases ackRing_events p now b _ _ _ e h with a | a
  · exact Or.inl a
  · exact Or.inr a.from

theorem AckFrom.dn {a b : List Slot} {e : Ev} (d : Dn a b) (h : AckFrom b e) : AckFrom a e := by
  obtain ⟨sl, hm, hc⟩ := h
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  unfold Dn at d
  rcases d j with e1 | ⟨s0, h0, h1⟩
  · exact ⟨sl, List.mem_of_getElem? (e1 ▸ hj), hc⟩
  · rw [hj] at h1
    have := Option.some.inj h1
    subst this
    rcases hc with ⟨hst, _⟩ | ⟨hst, _⟩ <;> cases hst

/-- Every `acked` event of the acknowledgement of a list of ranges is for a slot that was in flight in the ring the
call began with, with its number, size, frames, probe and repair flags; every `late` event is for a ghost of that
ring; no other event is appended. -/
theorem ackRanges_events (p : P) (now : Nat) :
    ∀ (rgs : List (Nat × Nat)) (x : X) (e : Ev), e ∈ (ackRanges p now rgs x).ev → e ∈ x.ev ∨ AckFrom x.r.ring e
  | [], x, e, h => by simp [ackRanges] at h; exact Or.inl h
  | (a, b) :: t, x, e, h => by
    unfold ackRanges at h
    split at h
    · exact Or.inl h
    · split at h
      · exact Or.inl h
      · split at h
        · exact Or.inl h
        · rcases ackRanges_events p now t _ e h with c | c
          · exact ackRange1_events p now a b x e c
          · exact Or.inr (c.dn (ackRange1_dn p now a b x))


/-! ### Every slot's path is below the path count -/

/-- Every slot of the ring is on a path of the connection. -/
def RingPath (p : P) (ring : List Slot) : Prop := ∀ s ∈ ring, s.path < p.mp

theorem RingFwd.mem {r r' : List Slot} (h : RingFwd r r') : ∀ y ∈ r', ∃ x ∈ r, SlotFwd x y := by
  obtain ⟨k, hk⟩ := h
  intro y hy
  obtain ⟨x, hx, hs⟩ := hk.mem y hy
  exact ⟨x, List.mem_of_mem_drop hx, hs⟩

theorem RingFwd.path {p : P} {r r' : List Slot} (h : RingFwd r r') (ok : RingPath p r) : RingPath p r' := by
  intro y hy
  obtain ⟨x, hx, hs⟩ := h.mem y hy
  rw [hs.2.2.2.2.1]
  exact ok x hx

theorem Keep.path {p : P} {r0 r : R} (k : Keep r0 r) (ok : RingPath p r0.ring) : RingPath p r.ring :=
  k.ring.path ok

theorem path_init (p : P) : RingPath p (R.init p).ring := fun s hs => by cases hs

theorem timeout_path (p : P) (r : R) (now : Nat) (ok : RingPath p r.ring) : RingPath p (timeout p r now).r.ring :=
  (timeout_keep p r now).path ok

theorem flush_path (p : P) (r : R) (now : Nat) (ok : RingPath p r.ring) : RingPath p (flush r now).r.ring :=
  (flush_keep r now).path ok

theorem ack_path (p : P) (r : R) (now : Nat) (rgs : List (Nat × Nat)) (ok : RingPath p r.ring) :
    RingPath p (ack p r now rgs).r.ring :=
  (ack_keep p r now rgs).1.path ok

theorem untracked_path (p : P) (r : R) (pn : Nat) (ok : RingPath p r.ring) :
    RingPath p (untracked r pn).r.ring := by
  unfold untracked
  split <;> exact ok

/-- A send puts a slot on the path it was given, and `send` refuses a path at or above the path count. -/
theorem send_path (p : P) (r : R) (k : Pkt) (ok : RingPath p r.ring) : RingPath p (send p r k).r.ring := by
  unfold send
  split
  · exact ok
  · split
    · exact ok
    · rename_i hpn hpath
      dsimp only
      obtain ⟨j, hj⟩ := trim_drop p k.time r.ring
      have ht : RingPath p (trim p k.time r.ring) := by
        rw [hj]; exact fun s hs => ok s (List.mem_of_mem_drop hs)
      split
      · exact ht
      · rename_i ring hp
        have hk : k.path < p.mp := by omega
        rcases push_cases p _ _ ring hp with h | ⟨h, t, he, _, h⟩
        · rw [h]
          intro s hs
          rcases List.mem_append.1 hs with h3 | h3
          · exact ht s h3
          · have : s = ⟨k.pn, k.time, k.size, k.path, k.rep, k.probe, k.fr, .fl, 0⟩ := by simpa using h3
            rw [this]; exact hk
        · rw [h]
          intro s hs
          rcases List.mem_append.1 hs with h3 | h3
          · apply ht s
            rw [he]; exact List.mem_cons_of_mem _ h3
          · have : s = ⟨k.pn, k.time, k.size, k.path, k.rep, k.probe, k.fr, .fl, 0⟩ := by simpa using h3
            rw [this]; exact hk

/-! ### The largest acknowledged number is not above the last one sent -/

/-- The largest number acknowledged is not above the last one sent. -/
def LaLs (la ls : Option Nat) : Prop := ∀ a, la = some a → ∃ l, ls = some l ∧ a ≤ l

theorem laLs_init (p : P) : LaLs (R.init p).la (R.init p).ls := fun a h => by cases h

theorem Keep.laLs {r0 r : R} (k : Keep r0 r) (ok : LaLs r0.la r0.ls) : LaLs r.la r.ls := by
  rw [k.la, k.ls]; exact ok

theorem timeout_laLs (p : P) (r : R) (now : Nat) (ok : LaLs r.la r.ls) :
    LaLs (timeout p r now).r.la (timeout p r now).r.ls :=
  (timeout_keep p r now).laLs ok

theorem flush_laLs (r : R) (now : Nat) (ok : LaLs r.la r.ls) : LaLs (flush r now).r.la (flush r now).r.ls :=
  (flush_keep r now).laLs ok

theorem untracked_laLs (r : R) (pn : Nat) (ok : LaLs r.la r.ls) :
    LaLs (untracked r pn).r.la (untracked r pn).r.ls := by
  unfold untracked
  split
  · exact ok
  · rename_i hpn
    intro a ha
    obtain ⟨l, hl, hle⟩ := ok a ha
    rw [hl] at hpn
    simp at hpn
    exact ⟨pn, rfl, by omega⟩

theorem send_la (p : P) (r : R) (k : Pkt) : (send p r k).r.la = r.la := by
  unfold send
  dsimp only
  repeat' split
  all_goals rfl

theorem send_laLs (p : P) (r : R) (k : Pkt) (ok : LaLs r.la r.ls) :
    LaLs (send p r k).r.la (send p r k).r.ls := by
  rw [send_la]
  obtain ⟨ring0, _, h⟩ := send_ring p r k
  rcases h with ⟨_, h2⟩ | ⟨sl, _, _, h2, hgt⟩
  · rw [h2]; exact ok
  · intro a ha
    obtain ⟨l, hl, hle⟩ := ok a ha
    have := hgt l hl
    exact ⟨k.pn, h2, by omega⟩

/-- The acknowledged range loop leaves the largest number of the call as it found it. -/
theorem ackRing_fl (p : P) (now b : Nat) : ∀ (n i : Nat) (x : X), (ackRing p now b n i x).fl = x.fl
  | 0, i, x => by simp [ackRing]
  | n + 1, i, x => by
    unfold ackRing
    rcases hs : x.r.ring[i]? with _ | sl
    · simp
    · simp only [hs]
      repeat' split
      all_goals first
        | rfl
        | exact (ackRing_fl p now b n (i + 1) _).trans rfl

/-- What the ranges of a call have made of the largest number: never above the last one sent. -/
def FlOK (x : X) : Prop := ∀ f, x.fl = some f → ∃ l, x.r.ls = some l ∧ f ≤ l

theorem ackRange1_fl (p : P) (now a b : Nat) (x : X) : (ackRange1 p now a b x).fl = omax x.fl (some b) := by
  unfold ackRange1
  dsimp only
  exact ackRing_fl p now b _ _ _

theorem ackRanges_fl (p : P) (now : Nat) :
    ∀ (rgs : List (Nat × Nat)) (x : X), FlOK x → FlOK (ackRanges p now rgs x)
  | [], x, h => by simpa [ackRanges] using h
  | (a, b) :: t, x, h => by
    unfold ackRanges
    split
    · exact h
    · split
      · exact h
      · split
        · exact h
        · rename_i c1 c2 c3
          apply ackRanges_fl p now t
          have hls := (ackRange1_keep (r0 := x.r) p now a b x (Keep.refl _)).ls
          intro f hf
          rw [ackRange1_fl] at hf
          rw [hls]
          have hb : ∃ l, x.r.ls = some l ∧ b ≤ l := by
            cases hl : x.r.ls with
            | none => simp [hl] at c3
            | some l => exact ⟨l, rfl, by simpa [hl] using c3⟩
          obtain ⟨l, hl, hbl⟩ := hb
          cases hx : x.fl with
          | none => rw [hx] at hf; simp [omax] at hf; subst hf; exact ⟨l, hl, hbl⟩
          | some g =>
            rw [hx] at hf
            simp [omax] at hf
            subst hf
            obtain ⟨l', hl', hgl⟩ := h g hx
            rw [hl] at hl'
            cases hl'
            exact ⟨l, hl, by omega⟩

/-- A call of `ack` keeps the largest acknowledged number not above the last one sent: a range whose largest number
is above it is refused, and the call raises the largest acknowledged number only to the largest of its ranges. -/
theorem ack_laLs (p : P) (r : R) (now : Nat) (rgs : List (Nat × Nat)) (ok : LaLs r.la r.ls) :
    LaLs (ack p r now rgs).r.la (ack p r now rgs).r.ls := by
  unfold ack
  dsimp only
  have kx := ackRanges_keep (r0 := r) p now rgs
    ⟨(ackStart p r now).1, [], {}, none, none, (ackStart p r now).2, "ok"⟩ (ackStart_keep p r now)
  have hf := ackRanges_fl p now rgs ⟨(ackStart p r now).1, [], {}, none, none, (ackStart p r now).2, "ok"⟩
    (fun f h => by simp at h)
  generalize ackRanges p now rgs ⟨(ackStart p r now).1, [], {}, none, none, (ackStart p r now).2, "ok"⟩ = x at kx hf ⊢
  split
  · exact kx.laLs ok
  · split
    · rename_i hn
      intro a ha
      obtain ⟨l, hl, hle⟩ := ok a (by rw [← kx.la]; exact ha)
      exact ⟨l, by rw [kx.ls]; exact hl, hle⟩
    · rename_i fl hfl
      have kf := ackFinish_keep p x now fl
      have e := ackSeed_fields p x now fl
      intro a ha
      rw [kf.la, e.2.2, kx.la] at ha
      rw [kf.ls, e.2.1, kx.ls]
      obtain ⟨lf, hlf, hfle⟩ := hf fl hfl
      rw [kx.ls] at hlf
      cases hla : r.la with
      | none => rw [hla] at ha; simp [omax] at ha; subst ha; exact ⟨lf, hlf, hfle⟩
      | some g =>
        rw [hla] at ha
        simp [omax] at ha
        obtain ⟨l, hl, hgl⟩ := ok g hla
        rw [hl] at hlf
        cases hlf
        exact ⟨lf, hl, by omega⟩

#audit_axioms Pinc.TransportRecovery.ackRing_events
#audit_axioms Pinc.TransportRecovery.ackRange1_events
#audit_axioms Pinc.TransportRecovery.ackRanges_events
#audit_axioms Pinc.TransportRecovery.timeout_path
#audit_axioms Pinc.TransportRecovery.flush_path
#audit_axioms Pinc.TransportRecovery.ack_path
#audit_axioms Pinc.TransportRecovery.send_path
#audit_axioms Pinc.TransportRecovery.untracked_path
#audit_axioms Pinc.TransportRecovery.timeout_laLs
#audit_axioms Pinc.TransportRecovery.flush_laLs
#audit_axioms Pinc.TransportRecovery.ack_laLs
#audit_axioms Pinc.TransportRecovery.send_laLs
#audit_axioms Pinc.TransportRecovery.untracked_laLs

end Pinc.TransportRecovery
