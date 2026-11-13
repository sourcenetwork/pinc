import Vinc.TransportRecoveryThm

/-!
# Loss recovery: the order of the sent ring and the life of a slot

The unbounded counterpart of two properties of `proofs/tla/Recovery.tla` that TLC checks on small rings:

- `RingShape`, the order: the packet numbers of the ring are strictly increasing and none is above the last one
  sent (`RingOK`), after every call (`timeout_ok`, `flush_ok`, `ack_ok`, `send_ok`, `untracked_ok`);
- `DoneStays`: across a call a slot that is still in the ring is the same packet (number, size, frames, send time,
  path), a done slot is done, and no slot goes back to in flight (`timeout_doneStays`, `flush_doneStays`,
  `ack_doneStays`, `send_doneStays`).

Both follow from one relation, proved for every call and through every loop (`Keep`): the ring after a call is the
ring before it without some slots at its head, each remaining slot moved forward in place (`RingFwd`); a send then
appends one slot with a number above every earlier one (`send_ring`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Vinc.TransportRecovery

/-! ### A slot moved forward, and a ring of such slots -/

/-- `b` is the slot `a` later: the same packet, done if `a` was done, in flight only if `a` was. -/
def SlotFwd (a b : Slot) : Prop :=
  b.pn = a.pn ∧ b.size = a.size ∧ b.fr = a.fr ∧ b.time = a.time ∧ b.path = a.path ∧
    (a.st = .done → b.st = .done) ∧ (b.st = .fl → a.st = .fl)

theorem SlotFwd.refl (a : Slot) : SlotFwd a a := ⟨rfl, rfl, rfl, rfl, rfl, fun h => h, fun h => h⟩

theorem SlotFwd.trans {a b c : Slot} (h1 : SlotFwd a b) (h2 : SlotFwd b c) : SlotFwd a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, fun h => b6 (a6 h), fun h => a7 (b7 h)⟩

/-- Slot by slot, the second ring is the first one later. -/
inductive F2 : List Slot → List Slot → Prop where
  | nil : F2 [] []
  | cons {a b : Slot} {l l' : List Slot} : SlotFwd a b → F2 l l' → F2 (a :: l) (b :: l')

theorem F2.refl : ∀ l : List Slot, F2 l l
  | [] => .nil
  | a :: l => .cons (SlotFwd.refl a) (F2.refl l)

theorem F2.trans : ∀ {a b c : List Slot}, F2 a b → F2 b c → F2 a c := by
  intro a b c h1
  induction h1 generalizing c with
  | nil => intro h2; exact h2
  | cons s _ ih =>
    intro h2
    cases h2 with
    | cons s2 t2 => exact .cons (s.trans s2) (ih t2)

theorem F2.drop : ∀ {a b : List Slot}, F2 a b → ∀ j, F2 (a.drop j) (b.drop j) := by
  intro a b h
  induction h with
  | nil => intro j; simp; exact .nil
  | cons s t ih =>
    intro j
    cases j with
    | zero => exact .cons s t
    | succ j => simpa using ih j

theorem F2.pns : ∀ {a b : List Slot}, F2 a b → b.map (·.pn) = a.map (·.pn) := by
  intro a b h
  induction h with
  | nil => rfl
  | cons s _ ih => simp [s.1, ih]

theorem F2.mem : ∀ {a b : List Slot}, F2 a b → ∀ y ∈ b, ∃ x ∈ a, SlotFwd x y := by
  intro a b h
  induction h with
  | nil => intro y hy; cases hy
  | cons s _ ih =>
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact ⟨_, List.mem_cons_self, s⟩
    · obtain ⟨x, hx, hs⟩ := ih y hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hs⟩

theorem f2_upd (f : Slot → Slot) : ∀ (l : List Slot) (i : Nat) (sl : Slot), l[i]? = some sl → SlotFwd sl (f sl) →
    F2 l (upd l i f)
  | [], i, sl, h, _ => by simp at h
  | x :: xs, 0, sl, h, hs => by
    have : x = sl := by simpa using h
    subst this
    exact .cons hs (F2.refl xs)
  | x :: xs, i + 1, sl, h, hs => by
    have h' : xs[i]? = some sl := by simpa using h
    exact .cons (SlotFwd.refl x) (f2_upd f xs i sl h' hs)

theorem f2_lim : ∀ (l : List Slot) (ex : Nat), F2 l (lim ex l)
  | [], ex => by cases ex <;> exact .nil
  | s :: t, 0 => F2.refl _
  | s :: t, ex + 1 => by
    unfold lim
    split
    · exact .cons ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun h => by cases h⟩ (f2_lim t ex)
    · exact .cons (SlotFwd.refl s) (f2_lim t (ex + 1))

theorem trim_drop (p : P) (now : Nat) : ∀ l : List Slot, ∃ k, trim p now l = l.drop k
  | [] => ⟨0, rfl⟩
  | h :: t => by
    unfold trim
    split
    · obtain ⟨k, hk⟩ := trim_drop p now t
      exact ⟨k + 1, by simpa using hk⟩
    · exact ⟨0, rfl⟩

/-- The ring `r'` is the ring `r` later: some slots left its head, the others moved forward in place. -/
def RingFwd (r r' : List Slot) : Prop := ∃ k, F2 (r.drop k) r'

theorem RingFwd.refl (r : List Slot) : RingFwd r r := ⟨0, F2.refl _⟩

theorem RingFwd.step {r a b : List Slot} (h : RingFwd r a) (h2 : F2 a b) : RingFwd r b := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk.trans h2⟩

theorem RingFwd.dropk {r a : List Slot} (h : RingFwd r a) (j : Nat) : RingFwd r (a.drop j) := by
  obtain ⟨k, hk⟩ := h
  have e : ∃ k', (r.drop k).drop j = r.drop k' := ⟨_, List.drop_drop⟩
  obtain ⟨k', hk'⟩ := e
  exact ⟨k', hk' ▸ hk.drop j⟩

theorem RingFwd.pns {r r' : List Slot} (h : RingFwd r r') : (r'.map (·.pn)).Sublist (r.map (·.pn)) := by
  obtain ⟨k, hk⟩ := h
  rw [hk.pns, List.map_drop]
  exact List.drop_sublist _ _

/-! ### What every loop and call keeps -/

/-- The state `r` is `r0` later: the ring moved forward and the last number sent is the same. -/
structure Keep (r0 r : R) : Prop where
  ring : RingFwd r0.ring r.ring
  ls : r.ls = r0.ls
  la : r.la = r0.la

theorem Keep.refl (r : R) : Keep r r := ⟨RingFwd.refl _, rfl, rfl⟩

theorem Keep.next {r0 r : R} (k : Keep r0 r) (r' : R) (hr : F2 r.ring r'.ring) (hl : r'.ls = r.ls)
    (hla : r'.la = r.la := by rfl) : Keep r0 r' :=
  ⟨k.ring.step hr, hl.trans k.ls, hla.trans k.la⟩

theorem Keep.trim {r0 r : R} (k : Keep r0 r) (p : P) (now : Nat) (r' : R) (hr : r'.ring = trim p now r.ring)
    (hl : r'.ls = r.ls) (hla : r'.la = r.la := by rfl) : Keep r0 r' := by
  obtain ⟨j, hj⟩ := trim_drop p now r.ring
  exact ⟨by rw [hr, hj]; exact k.ring.dropk j, hl.trans k.ls, hla.trans k.la⟩

theorem Keep.ite {r0 : R} (c : Prop) [Decidable c] (a b : R) (ha : Keep r0 a) (hb : Keep r0 b) :
    Keep r0 (if c then a else b) := by
  split <;> assumption

theorem noteOvertaken_keep (p : P) (r : R) (now pn time path : Nat) :
    (noteOvertaken p r now pn time path).ring = r.ring ∧ (noteOvertaken p r now pn time path).ls = r.ls ∧
      (noteOvertaken p r now pn time path).la = r.la := by
  unfold noteOvertaken
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl⟩

theorem loseAt_keep {r0 : R} (p : P) (y : Y) (i now : Nat) (sl : Slot) (h : y.r.ring[i]? = some sl)
    (hst : sl.st = .fl) (k : Keep r0 y.r) : Keep r0 (loseAt p y i now).r := by
  unfold loseAt
  rw [h]
  refine k.next _ (f2_upd _ y.r.ring i sl h ?_) rfl
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun hd => (by rw [hst] at hd; cases hd), fun _ => hst⟩

theorem settle_keep {r0 : R} (p : P) (y : Y) (k : Keep r0 y.r) : Keep r0 (settle p y).r := by
  unfold settle
  split
  · exact k.next _ (f2_lim _ _) rfl
  · exact k

theorem detectLoop_keep {r0 : R} (p : P) (now largest : Nat) :
    ∀ (n i : Nat) (y : Y), Keep r0 y.r → Keep r0 (detectLoop p now largest n i y).r
  | 0, i, y, k => by simpa [detectLoop] using k
  | n + 1, i, y, k => by
    unfold detectLoop
    rcases hs : y.r.ring[i]? with _ | sl
    · simpa using k
    · try dsimp only
      split
      · exact k
      · split
        · exact detectLoop_keep p now largest n (i + 1) y k
        · rename_i h1 h2
          have hst : sl.st = .fl := by simpa using h2
          split
          · exact detectLoop_keep p now largest n (i + 1) _ (k.next _ (F2.refl _) rfl)
          · exact detectLoop_keep p now largest n (i + 1) _ (loseAt_keep p y i now sl hs hst k)

theorem detect_keep {r0 : R} (p : P) (y : Y) (now largest : Nat) (k : Keep r0 y.r) :
    Keep r0 (detect p y now largest).r := by
  unfold detect
  exact settle_keep p _ (detectLoop_keep p now largest _ 0 _ (k.next _ (F2.refl _) rfl))

theorem declareOldest_keep {r0 : R} (p : P) (y : Y) (now : Nat) (k : Keep r0 y.r) :
    Keep r0 (declareOldest p y now).r := by
  unfold declareOldest
  split
  · exact k
  · rename_i i hi
    obtain ⟨_, sl0, h0, h1⟩ := firstIFFrom_spec _ 0 i hi
    simp at h0
    split
    · exact k
    · rename_i sl hs
      have e : sl = sl0 := by rw [h0] at hs; exact (Option.some.inj hs).symm
      subst e
      apply settle_keep
      dsimp only
      split
      · exact loseAt_keep p _ i now sl hs h1 (k.next _ (F2.refl _) rfl)
      · exact loseAt_keep p _ i now sl hs h1 k

theorem timeoutLoss_keep {r0 : R} (p : P) (r : R) (now : Nat) (k : Keep r0 r) :
    Keep r0 (timeoutLoss p r now).r := by
  unfold timeoutLoss
  dsimp only
  split
  · split
    · exact detect_keep p _ now _ k
    · exact k
  · exact k

theorem timeout_keep (p : P) (r : R) (now : Nat) : Keep r (timeout p r now).r := by
  unfold timeout
  dsimp only
  have h1 := timeoutLoss_keep (r0 := r) p { r with clock := max r.clock now } now ⟨RingFwd.refl _, rfl, rfl⟩
  repeat' split
  all_goals first
    | exact h1
    | exact h1.next _ (F2.refl _) rfl
    | exact declareOldest_keep p _ now (h1.next _ (F2.refl _) rfl)

theorem flushLoop_keep {r0 : R} (now : Nat) : ∀ (n i : Nat) (y : Y), Keep r0 y.r → Keep r0 (flushLoop now n i y).r
  | 0, i, y, k => by simpa [flushLoop] using k
  | n + 1, i, y, k => by
    unfold flushLoop
    rcases hs : y.r.ring[i]? with _ | sl
    · simpa using k
    · try dsimp only
      split
      · exact flushLoop_keep now n (i + 1) y k
      · rename_i h2
        have hst : sl.st = .fl := by simpa using h2
        refine flushLoop_keep now n (i + 1) _ (k.next _ (f2_upd _ y.r.ring i sl hs ?_) rfl)
        exact ⟨rfl, rfl, rfl, rfl, rfl, fun hd => (by rw [hst] at hd; cases hd), fun _ => hst⟩

theorem flush_keep (r : R) (now : Nat) : Keep r (flush r now).r := by
  unfold flush
  dsimp only
  exact (flushLoop_keep (r0 := r) now _ 0 _ ⟨RingFwd.refl _, rfl, rfl⟩).next _ (F2.refl _) rfl

theorem ackRing_keep {r0 : R} (p : P) (now b : Nat) :
    ∀ (n i : Nat) (x : X), Keep r0 x.r → Keep r0 (ackRing p now b n i x).r
  | 0, i, x, k => by simpa [ackRing] using k
  | n + 1, i, x, k => by
    unfold ackRing
    rcases hs : x.r.ring[i]? with _ | sl
    · simpa using k
    · try dsimp only
      have hdone : F2 x.r.ring (upd x.r.ring i (fun s : Slot => { s with st := .done })) :=
        f2_upd _ x.r.ring i sl hs ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun h => by cases h⟩
      have ho := noteOvertaken_keep p { x.r with ring := upd x.r.ring i fun s => { s with st := .done } } now sl.pn
        sl.time sl.path
      have hno : F2 x.r.ring
          (noteOvertaken p { x.r with ring := upd x.r.ring i fun s => { s with st := .done } } now sl.pn
            sl.time sl.path).ring := by rw [ho.1]; exact hdone
      split
      · exact k
      · split
        · exact ackRing_keep p now b n (i + 1) x k
        · split
          · exact ackRing_keep p now b n (i + 1) x k
          · split
            · exact ackRing_keep p now b n (i + 1) _ (k.next _ hdone rfl)
            · try dsimp only
              split
              · exact ackRing_keep p now b n (i + 1) _ (k.next _ hno ho.2.1 ho.2.2)
              · exact ackRing_keep p now b n (i + 1) _ (k.next _ hno ho.2.1 ho.2.2)

theorem ackRange1_keep {r0 : R} (p : P) (now a b : Nat) (x : X) (k : Keep r0 x.r) :
    Keep r0 (ackRange1 p now a b x).r := by
  unfold ackRange1
  dsimp only
  exact ackRing_keep p now b _ _ _ (k.next _ (F2.refl _) rfl)

theorem ackRanges_keep {r0 : R} (p : P) (now : Nat) :
    ∀ (rgs : List (Nat × Nat)) (x : X), Keep r0 x.r → Keep r0 (ackRanges p now rgs x).r
  | [], x, k => by simpa [ackRanges] using k
  | (a, b) :: t, x, k => by
    unfold ackRanges
    split
    · exact k
    · split
      · exact k
      · split
        · exact k
        · exact ackRanges_keep p now t _ (ackRange1_keep p now a b x k)

theorem ackStart_keep (p : P) (r : R) (now : Nat) : Keep r (ackStart p r now).1 := by
  unfold ackStart
  dsimp only
  split <;> exact ⟨RingFwd.refl _, rfl, rfl⟩

theorem RingFwd.trans {r a b : List Slot} (h1 : RingFwd r a) (h2 : RingFwd a b) : RingFwd r b := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  refine ⟨k1 + k2, ?_⟩
  rw [← List.drop_drop]
  exact (hk1.drop k2).trans hk2

/-- What the seed of an acknowledgement leaves: the ring and the last number sent, and the largest acknowledged
number raised to `fl`. -/
theorem ackSeed_fields (p : P) (x : X) (now fl : Nat) :
    (ackSeed p x now fl).1.ring = x.r.ring ∧ (ackSeed p x now fl).1.ls = x.r.ls ∧
      (ackSeed p x now fl).1.la = omax x.r.la (some fl) := by
  unfold ackSeed
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

theorem ackSample_keep {r0 : R} (p : P) (r4 : R) (npn ntime npath now fl : Nat) (k : Keep r0 r4) :
    Keep r0 (ackSample p r4 npn ntime npath now fl) := by
  unfold ackSample
  dsimp only
  split
  · exact k.next _ (F2.refl _) rfl
  · exact k

/-- The end of an acknowledgement keeps what the seed left. -/
theorem ackFinish_keep (p : P) (x : X) (now fl : Nat) : Keep (ackSeed p x now fl).1 (ackFinish p x now fl).r := by
  unfold ackFinish
  split
  · exact (Keep.refl _).trim p now _ rfl rfl
  · rename_i npn ntime npath _
    have kd := detect_keep (r0 := (ackSeed p x now fl).1) p
      ⟨{ ackSample p (ackSeed p x now fl).1 npn ntime npath now fl with pc := 0 }, x.ev, x.s, none⟩ now fl
      ((ackSample_keep p _ npn ntime npath now fl (Keep.refl _)).next _ (F2.refl _) rfl)
    exact kd.trim p now _ rfl rfl

/-- A call of `ack`: the ring moved forward and the last number sent kept (the largest acknowledged one is raised,
see `Vinc.TransportRecovery.ack_la`). -/
theorem ack_keep (p : P) (r : R) (now : Nat) (rgs : List (Nat × Nat)) :
    RingFwd r.ring (ack p r now rgs).r.ring ∧ (ack p r now rgs).r.ls = r.ls := by
  unfold ack
  dsimp only
  have kx := ackRanges_keep (r0 := r) p now rgs
    ⟨(ackStart p r now).1, [], {}, none, none, (ackStart p r now).2, "ok"⟩ (ackStart_keep p r now)
  generalize ackRanges p now rgs ⟨(ackStart p r now).1, [], {}, none, none, (ackStart p r now).2, "ok"⟩ = x at kx ⊢
  split
  · exact ⟨kx.ring, kx.ls⟩
  · split
    · exact ⟨(kx.next _ (F2.refl _) rfl).ring, (kx.next _ (F2.refl _) rfl).ls⟩
    · rename_i fl _
      have kf := ackFinish_keep p x now fl
      have e := ackSeed_fields p x now fl
      exact ⟨by have := kf.ring; rw [e.1] at this; exact kx.ring.trans this,
        kf.ls.trans (e.2.1.trans kx.ls)⟩

/-- A send: the ring moved forward, and then nothing more or one new slot with a number above the last one sent,
which becomes the last one sent. -/
theorem send_ring (p : P) (r : R) (k : Pkt) :
    ∃ ring0, RingFwd r.ring ring0 ∧
      (((send p r k).r.ring = ring0 ∧ (send p r k).r.ls = r.ls) ∨
       (∃ sl : Slot, sl.pn = k.pn ∧ (send p r k).r.ring = ring0 ++ [sl] ∧ (send p r k).r.ls = some k.pn ∧
          ∀ l, r.ls = some l → l < k.pn)) := by
  unfold send
  split
  · exact ⟨r.ring, RingFwd.refl _, Or.inl ⟨rfl, rfl⟩⟩
  · rename_i hpn
    split
    · exact ⟨r.ring, RingFwd.refl _, Or.inl ⟨rfl, rfl⟩⟩
    · dsimp only
      obtain ⟨j, hj⟩ := trim_drop p k.time r.ring
      have ht : RingFwd r.ring (trim p k.time r.ring) := by rw [hj]; exact (RingFwd.refl _).dropk j
      have hgt : ∀ l, r.ls = some l → l < k.pn := by
        intro l hl
        rw [hl] at hpn
        simp at hpn
        omega
      split
      · exact ⟨_, ht, Or.inl ⟨rfl, rfl⟩⟩
      · rename_i ring hp
        rcases push_cases p _ _ ring hp with h | ⟨h, t, he, _, h⟩
        · exact ⟨_, ht, Or.inr ⟨_, rfl, h, rfl, hgt⟩⟩
        · have ht2 : RingFwd r.ring t := by
            have := ht.dropk 1
            rw [he] at this
            simpa using this
          exact ⟨t, ht2, Or.inr ⟨_, rfl, h, rfl, hgt⟩⟩

/-! ### The order of the ring -/

/-- The packet numbers of the ring are strictly increasing, and none is above the last one sent. -/
def RingOK (ls : Option Nat) (ring : List Slot) : Prop :=
  (ring.map (·.pn)).Pairwise (· < ·) ∧ ∀ s ∈ ring, ∃ l, ls = some l ∧ s.pn ≤ l

theorem RingFwd.ok {ls : Option Nat} {r r' : List Slot} (h : RingFwd r r') (ok : RingOK ls r) : RingOK ls r' := by
  refine ⟨List.Pairwise.sublist h.pns ok.1, fun s hs => ?_⟩
  have h1 : s.pn ∈ r'.map (·.pn) := List.mem_map.2 ⟨s, hs, rfl⟩
  have h2 : s.pn ∈ r.map (·.pn) := h.pns.subset h1
  obtain ⟨s0, hs0, e⟩ := List.mem_map.1 h2
  obtain ⟨l, hl, hle⟩ := ok.2 s0 hs0
  exact ⟨l, hl, by rw [← e]; exact hle⟩

theorem Keep.ok {r0 r : R} (k : Keep r0 r) (ok : RingOK r0.ls r0.ring) : RingOK r.ls r.ring := by
  rw [k.ls]; exact k.ring.ok ok

theorem ring_init (p : P) : RingOK (R.init p).ls (R.init p).ring :=
  ⟨List.Pairwise.nil, fun s hs => by cases hs⟩

theorem timeout_ok (p : P) (r : R) (now : Nat) (ok : RingOK r.ls r.ring) :
    RingOK (timeout p r now).r.ls (timeout p r now).r.ring := (timeout_keep p r now).ok ok

theorem flush_ok (r : R) (now : Nat) (ok : RingOK r.ls r.ring) : RingOK (flush r now).r.ls (flush r now).r.ring :=
  (flush_keep r now).ok ok

theorem ack_ok (p : P) (r : R) (now : Nat) (rgs : List (Nat × Nat)) (ok : RingOK r.ls r.ring) :
    RingOK (ack p r now rgs).r.ls (ack p r now rgs).r.ring := by
  have k := ack_keep p r now rgs
  rw [k.2]; exact k.1.ok ok

theorem send_ok (p : P) (r : R) (k : Pkt) (ok : RingOK r.ls r.ring) :
    RingOK (send p r k).r.ls (send p r k).r.ring := by
  obtain ⟨ring0, hf, h⟩ := send_ring p r k
  have ok0 := hf.ok ok
  rcases h with ⟨h1, h2⟩ | ⟨sl, hsl, h1, h2, hgt⟩
  · rw [h1, h2]; exact ok0
  · rw [h1, h2]
    refine ⟨?_, fun s hs => ?_⟩
    · rw [List.map_append, List.pairwise_append]
      refine ⟨ok0.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      obtain ⟨s0, hs0, e⟩ := List.mem_map.1 ha
      obtain ⟨l, hl, hle⟩ := ok0.2 s0 hs0
      have hb' : b = sl.pn := by simpa using hb
      have := hgt l hl
      omega
    · rcases List.mem_append.1 hs with h3 | h3
      · obtain ⟨l, hl, hle⟩ := ok0.2 s h3
        have := hgt l hl
        exact ⟨k.pn, rfl, by omega⟩
      · have : s = sl := by simpa using h3
        exact ⟨k.pn, rfl, by rw [this, hsl]; exact Nat.le_refl _⟩

theorem untracked_ok (r : R) (pn : Nat) (ok : RingOK r.ls r.ring) :
    RingOK (untracked r pn).r.ls (untracked r pn).r.ring := by
  unfold untracked
  split
  · exact ok
  · rename_i hpn
    refine ⟨ok.1, fun s hs => ?_⟩
    obtain ⟨l, hl, hle⟩ := ok.2 s hs
    rw [hl] at hpn
    simp at hpn
    exact ⟨pn, rfl, by omega⟩

/-! ### A done slot stays done -/

/-- In a ring in the order of its numbers, a number names one slot. -/
theorem pn_unique : ∀ {l : List Slot}, (l.map (·.pn)).Pairwise (· < ·) → ∀ x ∈ l, ∀ y ∈ l, x.pn = y.pn → x = y := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons a t ih =>
    intro hp x hx y hy e
    rw [List.map_cons] at hp
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hp
    rcases List.mem_cons.1 hx with rfl | hx'
    · rcases List.mem_cons.1 hy with rfl | hy'
      · rfl
      · have := hhead y.pn (List.mem_map.2 ⟨y, hy', rfl⟩); omega
    · rcases List.mem_cons.1 hy with rfl | hy'
      · have := hhead x.pn (List.mem_map.2 ⟨x, hx', rfl⟩); omega
      · exact ih htail x hx' y hy' e

/-- Across a ring moved forward, a slot found again by its number is the same packet later. -/
theorem RingFwd.doneStays {r r' : List Slot} (h : RingFwd r r') (hp : (r.map (·.pn)).Pairwise (· < ·)) :
    ∀ a ∈ r, ∀ b ∈ r', a.pn = b.pn → SlotFwd a b := by
  intro a ha b hb e
  obtain ⟨k, hk⟩ := h
  obtain ⟨x, hx, hs⟩ := hk.mem b hb
  have hxr : x ∈ r := List.mem_of_mem_drop hx
  have : a = x := pn_unique hp a ha x hxr (e.trans hs.1)
  rw [this]; exact hs

theorem timeout_doneStays (p : P) (r : R) (now : Nat) (ok : RingOK r.ls r.ring) :
    ∀ a ∈ r.ring, ∀ b ∈ (timeout p r now).r.ring, a.pn = b.pn → SlotFwd a b :=
  (timeout_keep p r now).ring.doneStays ok.1

theorem flush_doneStays (r : R) (now : Nat) (ok : RingOK r.ls r.ring) :
    ∀ a ∈ r.ring, ∀ b ∈ (flush r now).r.ring, a.pn = b.pn → SlotFwd a b :=
  (flush_keep r now).ring.doneStays ok.1

theorem ack_doneStays (p : P) (r : R) (now : Nat) (rgs : List (Nat × Nat)) (ok : RingOK r.ls r.ring) :
    ∀ a ∈ r.ring, ∀ b ∈ (ack p r now rgs).r.ring, a.pn = b.pn → SlotFwd a b :=
  (ack_keep p r now rgs).1.doneStays ok.1

theorem send_doneStays (p : P) (r : R) (k : Pkt) (ok : RingOK r.ls r.ring) :
    ∀ a ∈ r.ring, ∀ b ∈ (send p r k).r.ring, a.pn = b.pn → SlotFwd a b := by
  intro a ha b hb e
  obtain ⟨ring0, hf, h⟩ := send_ring p r k
  rcases h with ⟨h1, _⟩ | ⟨sl, hsl, h1, _, hgt⟩
  · rw [h1] at hb; exact hf.doneStays ok.1 a ha b hb e
  · rw [h1] at hb
    rcases List.mem_append.1 hb with h3 | h3
    · exact hf.doneStays ok.1 a ha b h3 e
    · exfalso
      have hbs : b = sl := by simpa using h3
      obtain ⟨l, hl, hle⟩ := ok.2 a ha
      have := hgt l hl
      rw [hbs, hsl] at e
      omega

#audit_axioms Vinc.TransportRecovery.timeout_ok
#audit_axioms Vinc.TransportRecovery.flush_ok
#audit_axioms Vinc.TransportRecovery.ack_ok
#audit_axioms Vinc.TransportRecovery.send_ok
#audit_axioms Vinc.TransportRecovery.untracked_ok
#audit_axioms Vinc.TransportRecovery.timeout_doneStays
#audit_axioms Vinc.TransportRecovery.flush_doneStays
#audit_axioms Vinc.TransportRecovery.ack_doneStays
#audit_axioms Vinc.TransportRecovery.send_doneStays

end Vinc.TransportRecovery
