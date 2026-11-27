import Pinc.CoreState

/-!
# The saved state: what is proved

Over unbounded counts and every byte string (`Pinc.CoreState` is the model):

- `enc_parse` the bytes of a state the encoder accepts read back as that state (round trip);
- `parse_canon` a byte string that is accepted is the encoding of the state it reads, and that state is one the
  encoder accepts: one reading per byte string, and `parse_injective`, one encoding per state;
- `parse_trailing`, `parse_prefix`: nothing may follow a state and no proper prefix of a state is a state;
- `parse_checks`: an accepted state has version 1, every identity tag in 1..4, every ALPN of 1 to 32 bytes, every
  AEAD tag 1 or 2, and counts that match what the input holds (`parse_sizes`: a count never exceeds the input);
- `restore_atomic`: a refused input leaves the three tables as they were; `restore_ok_iff`: a restore accepts exactly
  the inputs that `parse` reads;
- `restore_bounded`: the tables never pass their bounds, whatever they held and whatever is restored;
- `restore_fresh`: restoring what was written into an empty endpoint gives exactly the tables written (a state with
  one entry per peer, within the bounds, round trips above 0, tickets not expired), and reports the counts;
- `lazy_not_atomic`, `lax_not_canon`: the two wrong readers fail (the witnesses of the TLC configurations).
-/

namespace Pinc.CoreState
open Pinc.DtnCodec Pinc.DtnCodecWire

theorem tkDec_some (b : Bytes) (l : List TkT) (h : tkDec b = some l) :
    b = tkEnc l ∧ l.length < 256 ∧ ∀ t ∈ l, tkC.wf t := by
  unfold tkDec at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨v, n, l'⟩, hx, he⟩ := h
  simp only at he
  subst he
  have ⟨hb, hw⟩ := decodeAll_some _ _ _ hx
  simp only [tkSecC, pairD, verC, guardC, uC, listC, listWf] at hw
  obtain ⟨⟨_, hv⟩, hn, hl, hall⟩ := hw
  subst hv
  subst hl
  refine ⟨hb, ?_, hall⟩
  simpa using hn

theorem tkDec_enc (l : List TkT) (h1 : l.length < 256) (h2 : ∀ t ∈ l, tkC.wf t) : tkDec (tkEnc l) = some l := by
  unfold tkDec tkEnc
  have : tkSecC.wf (1, l.length, l) := by
    simp only [tkSecC, pairD, verC, guardC, uC, listC, listWf]
    exact ⟨⟨by decide, trivial⟩, by simpa using h1, trivial, h2⟩
  rw [decodeAll_emit _ _ this]
  rfl

theorem krDec_some (n : Nat) (b : Bytes) (l : List (Node × Nat)) (h : krDec n b = some l) :
    b = krEnc l ∧ l.length = n ∧ ∀ e ∈ l, krC.wf e := by
  have ⟨hb, hw⟩ := decodeAll_some _ _ _ h
  exact ⟨hb, hw⟩

theorem ekDec_some (n : Nat) (b : Bytes) (l : List (Node × Bytes)) (h : ekDec n b = some l) :
    b = ekEnc l ∧ l.length = n ∧ ∀ e ∈ l, ekC.wf e := by
  have ⟨hb, hw⟩ := decodeAll_some _ _ _ h
  exact ⟨hb, hw⟩

theorem krDec_enc (l : List (Node × Nat)) (h : ∀ e ∈ l, krC.wf e) : krDec l.length (krEnc l) = some l :=
  decodeAll_emit (listC krC l.length) l ⟨rfl, h⟩

theorem ekDec_enc (l : List (Node × Bytes)) (h : ∀ e ∈ l, ekC.wf e) : ekDec l.length (ekEnc l) = some l :=
  decodeAll_emit (listC ekC l.length) l ⟨rfl, h⟩

/-- Every round trip entry is 41 bytes, every prekey entry 65. -/
theorem krC_len (e : Node × Nat) (h : krC.wf e) : (krC.emit e).length = 41 := by
  obtain ⟨⟨a, b⟩, r⟩ := e
  simp [krC, nodeC, pair, pairD, guardC, uC, bytesC, toBE_length] at h ⊢
  omega

theorem ekC_len (e : Node × Bytes) (h : ekC.wf e) : (ekC.emit e).length = 65 := by
  obtain ⟨⟨a, b⟩, r⟩ := e
  simp [ekC, nodeC, pair, pairD, guardC, uC, bytesC, toBE_length] at h ⊢
  omega

theorem krEnc_len (l : List (Node × Nat)) (h : ∀ e ∈ l, krC.wf e) : (krEnc l).length = 41 * l.length := by
  induction l with
  | nil => simp [krEnc, listEmit]
  | cons e t ih =>
    have h1 := ih (fun x hx => h x (by simp [hx]))
    have h2 := krC_len e (h e (by simp))
    simp only [krEnc, listEmit, List.length_append, List.length_cons] at h1 ⊢
    rw [h1, h2]; omega

theorem ekEnc_len (l : List (Node × Bytes)) (h : ∀ e ∈ l, ekC.wf e) : (ekEnc l).length = 65 * l.length := by
  induction l with
  | nil => simp [ekEnc, listEmit]
  | cons e t ih =>
    have h1 := ih (fun x hx => h x (by simp [hx]))
    have h2 := ekC_len e (h e (by simp))
    simp only [ekEnc, listEmit, List.length_append, List.length_cons] at h1 ⊢
    rw [h1, h2]; omega

/-! ## Round trip and one reading -/

theorem hdrOf_wf (s : St) (w : WFs s) : hdrC.wf (hdrOf s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := w
  have hk := krEnc_len s.kr h5
  have he := ekEnc_len s.ek h7
  simp only [hdrC, hdrOf, pairD, verC, guardC, uC, bytesC]
  simp only [Nat.reducePow] at h3 h4 h6 ⊢
  exact ⟨⟨by decide, trivial⟩, h3, trivial, h4, hk, h6, he⟩

theorem hdrP_false (b : Bytes) : hdrP false b = decodeAll hdrC b := by
  unfold hdrP decodeAll
  cases hc : hdrC.parse b with
  | none => rfl
  | some x =>
    obtain ⟨h, r⟩ := x
    cases r <;> simp

/-- Round trip: the bytes of a state the encoder accepts read back as that state. -/
theorem enc_parse (s : St) (w : WFs s) : parse (enc s) = some s := by
  unfold parse
  rw [hdrP_false]
  have := decodeAll_emit hdrC (hdrOf s) (hdrOf_wf s w)
  unfold enc
  rw [this]
  dsimp only [stages, hTk, hNk, hKr, hNe, hEk, hdrOf]
  rw [tkDec_enc _ w.1 w.2.1, krDec_enc _ w.2.2.2.2.1, ekDec_enc _ w.2.2.2.2.2.2]

/-- One reading: a byte string that is accepted is the encoding of the state it reads, and that state is one the
encoder accepts. -/
theorem parse_canon (b : Bytes) (s : St) (h : parse b = some s) : enc s = b ∧ WFs s := by
  unfold parse at h
  rw [hdrP_false] at h
  cases hd : decodeAll hdrC b with
  | none => simp [hd] at h
  | some hh =>
    rw [hd] at h
    obtain ⟨hb, hw⟩ := decodeAll_some hdrC b hh hd
    obtain ⟨v, tl, tkb, nk, krb, ne, ekb⟩ := hh
    simp only [stages, hTk, hNk, hKr, hNe, hEk] at h
    cases t1 : tkDec tkb with
    | none => simp [t1] at h
    | some tk =>
      cases t2 : krDec nk krb with
      | none => simp [t1, t2] at h
      | some kr =>
        cases t3 : ekDec ne ekb with
        | none => simp [t1, t2, t3] at h
        | some ek =>
          simp only [t1, t2, t3, Option.some.injEq] at h
          subst h
          obtain ⟨e1, c1, w1⟩ := tkDec_some _ _ t1
          obtain ⟨e2, c2, w2⟩ := krDec_some _ _ _ t2
          obtain ⟨e3, c3, w3⟩ := ekDec_some _ _ _ t3
          simp only [hdrC, pairD, verC, guardC, uC, bytesC] at hw
          obtain ⟨⟨_, hv⟩, htl, hl1, hnk, hl2, hne, hl3⟩ := hw
          subst hv; subst e1; subst e2; subst e3; subst c2; subst c3; subst hl1
          refine ⟨hb.symm, c1, w1, ?_, ?_, w2, ?_, w3⟩
          · simpa using htl
          · simpa using hnk
          · simpa using hne

/-- One encoding per state: two byte strings that read as the same state are equal. -/
theorem parse_injective (a b : Bytes) (s : St) (ha : parse a = some s) (hb : parse b = some s) : a = b := by
  rw [← (parse_canon a s ha).1, ← (parse_canon b s hb).1]

/-- Nothing may follow a state. -/
theorem parse_trailing (b : Bytes) (s : St) (h : parse b = some s) (x : Bytes) (hx : x ≠ []) :
    parse (b ++ x) = none := by
  obtain ⟨he, w⟩ := parse_canon b s h
  unfold parse
  rw [hdrP_false, ← he]
  unfold enc
  rw [decodeAll_trailing hdrC (hdrOf s) (hdrOf_wf s w) x hx]

/-- No proper prefix of a state is a state. -/
theorem parse_prefix (b : Bytes) (s : St) (h : parse b = some s) (p q : Bytes) (hq : q ≠ []) (hpq : p ++ q = b) :
    parse p = none := by
  obtain ⟨he, w⟩ := parse_canon b s h
  unfold parse
  rw [hdrP_false]
  rw [decodeAll_prefix hdrC (hdrOf s) (hdrOf_wf s w) p q hq (by rw [hpq, ← he]; rfl)]

theorem enc_length (s : St) (w : WFs s) :
    (enc s).length = 9 + (tkEnc s.tk).length + 41 * s.kr.length + 65 * s.ek.length := by
  have hk := krEnc_len s.kr w.2.2.2.2.1
  have he := ekEnc_len s.ek w.2.2.2.2.2.2
  simp [enc, hdrC, hdrOf, pairD, verC, guardC, uC, bytesC, toBE_length, List.length_append, hk, he]
  omega

/-- Lengths and counts are bounded by the input before anything is read or stored: what an accepted input holds
is exactly the sum of its sections, so a count that claims more than the input holds is refused. -/
theorem parse_sizes (b : Bytes) (s : St) (h : parse b = some s) :
    b.length = 9 + (tkEnc s.tk).length + 41 * s.kr.length + 65 * s.ek.length ∧ s.tk.length < 256 ∧
      s.kr.length < 2 ^ 16 ∧ s.ek.length < 2 ^ 16 := by
  obtain ⟨he, w⟩ := parse_canon b s h
  refine ⟨?_, w.1, w.2.2.2.1, w.2.2.2.2.2.1⟩
  rw [← he]; exact enc_length s w

/-- What an accepted state satisfies: version 1, identity tags in 1..4, ALPNs of 1 to 32 bytes of the length
written, AEAD tags 1 or 2. -/
theorem parse_checks (b : Bytes) (s : St) (h : parse b = some s) :
    b.head? = some 1 ∧
    (∀ t ∈ s.tk, (1 ≤ t.1.1 ∧ t.1.1 ≤ 4) ∧ (1 ≤ t.2.1 ∧ t.2.1 ≤ 32) ∧ t.2.2.1.length = t.2.1 ∧
        (1 ≤ t.2.2.2.2.2.1 ∧ t.2.2.2.2.2.1 ≤ 2)) ∧
    (∀ e ∈ s.kr, 1 ≤ e.1.1 ∧ e.1.1 ≤ 4) ∧ (∀ e ∈ s.ek, 1 ≤ e.1.1 ∧ e.1.1 ≤ 4) := by
  obtain ⟨he, w⟩ := parse_canon b s h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← he]
    simp [enc, hdrC, hdrOf, pairD, verC, guardC, uC, toBE]
  · intro t ht
    have := w.2.1 t ht
    obtain ⟨⟨n0, nb⟩, l, a, i, p, ae, ex, cr⟩ := t
    simp only [tkC, pair, pairD, nodeC, guardC, alpnLenC, aeadC, uC, bytesC] at this ⊢
    obtain ⟨⟨_, h1, h2⟩, ⟨_, h3, h4⟩, h5, _, _, ⟨_, h6, h7⟩, _⟩ := this
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7⟩
  · intro e he
    obtain ⟨⟨n0, nb⟩, r⟩ := e
    have := w.2.2.2.2.1 _ he
    simp only [krC, pair, pairD, nodeC, guardC, uC, bytesC] at this ⊢
    exact this.1.2
  · intro e he
    obtain ⟨⟨n0, nb⟩, r⟩ := e
    have := w.2.2.2.2.2.2 _ he
    simp only [ekC, pair, pairD, nodeC, guardC, uC, bytesC] at this ⊢
    exact this.1.2

/-! ## The tables stay within their bounds -/

/-- The three tables within the bounds of `c`. -/
def Within (c : Cfg) (s : St) : Prop := s.tk.length ≤ c.ct ∧ s.kr.length ≤ c.kr ∧ s.ek.length ≤ c.ek

theorem setFirst_length {α : Type} (p : α → Bool) (v : α) : ∀ l : List α, (setFirst p v l).length = l.length
  | [] => rfl
  | x :: t => by
    unfold setFirst
    split <;> simp [setFirst_length p v t]

theorem tkIns_len (ct : Nat) (tk : List TkT) (t : TkT) (h : tk.length ≤ ct) : (tkIns ct tk t).length ≤ ct := by
  unfold tkIns
  split
  · exact h
  · split
    · rename_i _ ha
      obtain ⟨x, hx, _⟩ := List.any_eq_true.mp ha
      have := List.length_pos_of_mem hx
      simp only [List.length_append, List.length_singleton, List.length_eraseP, ha, ↓reduceIte]
      omega
    · split
      · simp only [List.length_append, List.length_singleton, List.length_tail]; omega
      · simp only [List.length_append, List.length_singleton]; omega

theorem apTk_len (ct now : Nat) : ∀ (es tk : List TkT), tk.length ≤ ct → (apTk ct now es tk).1.length ≤ ct
  | [], tk, h => by simpa [apTk] using h
  | e :: es, tk, h => by
    unfold apTk
    split
    · exact apTk_len ct now es _ (tkIns_len ct tk e h)
    · exact apTk_len ct now es tk h

theorem krIns_len (cap : Nat) (kr : List (Node × Nat)) (e : Node × Nat) (h : kr.length ≤ cap) :
    (krIns cap kr e).1.length ≤ cap := by
  unfold krIns
  split
  · exact h
  · split
    · simpa [setFirst_length] using h
    · split
      · simp only [List.length_append, List.length_singleton]; omega
      · exact h

theorem apKr_len (cap : Nat) : ∀ (es kr : List (Node × Nat)), kr.length ≤ cap → (apKr cap es kr).1.length ≤ cap
  | [], kr, h => by simpa [apKr] using h
  | e :: es, kr, h => by
    unfold apKr
    exact apKr_len cap es _ (krIns_len cap kr e h)

theorem ekIns_len (cap : Nat) (ek : List (Node × Bytes)) (e : Node × Bytes) (h : ek.length ≤ cap) :
    (ekIns cap ek e).length ≤ cap := by
  unfold ekIns
  split
  · simpa [setFirst_length] using h
  · split
    · exact h
    · split
      · simp only [List.length_append, List.length_singleton, List.length_tail]; omega
      · simp only [List.length_append, List.length_singleton]; omega

theorem apEk_len (cap : Nat) : ∀ (es ek : List (Node × Bytes)), ek.length ≤ cap → (apEk cap es ek).length ≤ cap
  | [], ek, h => by simpa [apEk] using h
  | e :: es, ek, h => by
    unfold apEk
    exact apEk_len cap es _ (ekIns_len cap ek e h)

/-- Whatever the tables held (within their bounds), whatever the bytes, and whichever reader: they are within their
bounds afterwards. A restore never needs room it does not have: an entry past the bound replaces the oldest or is
refused. -/
theorem restore_bounded (c : Cfg) (live : St) (b : Bytes) (now : Nat) (h : Within c live) :
    Within c (restore c live b now).1 := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold restore
  cases hh : hdrP c.lax b with
  | none => exact ⟨h1, h2, h3⟩
  | some hd =>
    simp only
    split
    · exact ⟨h1, h2, h3⟩
    · cases t1 : tkDec (hTk hd) with
      | none => exact ⟨h1, h2, h3⟩
      | some tl =>
        have ht := apTk_len c.ct now tl live.tk h1
        simp only []
        cases t2 : krDec (hNk hd) (hKr hd) with
        | none => exact ⟨ht, h2, h3⟩
        | some kl =>
          have hk := apKr_len c.kr kl live.kr h2
          simp only []
          cases t3 : ekDec (hNe hd) (hEk hd) with
          | none => exact ⟨ht, hk, h3⟩
          | some el => exact ⟨ht, hk, apEk_len c.ek el live.ek h3⟩

/-! ## A refusal changes nothing -/

/-- A refused input leaves the three tables as they were, for the code's order of stages: every check that can
refuse comes before the first write. -/
theorem restore_atomic (c : Cfg) (hl : c.lazy = false) (live : St) (b : Bytes) (now : Nat)
    (h : (restore c live b now).2 = none) : (restore c live b now).1 = live := by
  unfold restore at h ⊢
  cases hh : hdrP c.lax b with
  | none => rfl
  | some hd =>
    simp only [hh, hl] at h ⊢
    by_cases hp : ((krDec (hNk hd) (hKr hd)).isSome && (ekDec (hNe hd) (hEk hd)).isSome) = true
    · have hp' : (!false && !((krDec (hNk hd) (hKr hd)).isSome && (ekDec (hNe hd) (hEk hd)).isSome)) = false := by
        simp [hp]
      simp only [hp'] at h ⊢
      cases t1 : tkDec (hTk hd) with
      | none => rfl
      | some tl =>
        simp only [t1] at h ⊢
        simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hp
        obtain ⟨⟨kl, t2⟩, ⟨el, t3⟩⟩ := hp
        simp [t2, t3] at h
    · have hf : ((krDec (hNk hd) (hKr hd)).isSome && (ekDec (hNe hd) (hEk hd)).isSome) = false := by
        cases hq : ((krDec (hNk hd) (hKr hd)).isSome && (ekDec (hNe hd) (hEk hd)).isSome) <;> simp_all
      simp [hf]

/-! ## What a fresh endpoint holds after a restore -/

/-- One entry per peer. -/
def Uniq {β : Type} (l : List (Node × β)) : Prop := l.Pairwise (fun a b => a.1 ≠ b.1)

theorem not_any_of_uniq {β : Type} (acc es : List (Node × β)) (e : Node × β) (hu : Uniq (acc ++ e :: es)) :
    ¬ (acc.any (fun o => o.1 == e.1) = true) := by
  intro hany
  obtain ⟨x, hx1, hx2⟩ := List.any_eq_true.mp hany
  have := (List.pairwise_append.mp hu).2.2 x hx1 e (by simp)
  simp only [beq_iff_eq] at hx2
  exact this hx2

theorem apTk_fresh (ct now : Nat) : ∀ (es acc : List TkT), Uniq (acc ++ es) → acc.length + es.length ≤ ct →
    (∀ e ∈ es, now ≤ tkExp e) → apTk ct now es acc = (acc ++ es, es.length)
  | [], acc, _, _, _ => by simp [apTk]
  | e :: es, acc, hu, hl, hx => by
    have hne : now ≤ tkExp e := hx e (by simp)
    have hnot := not_any_of_uniq acc es e hu
    have hins : tkIns ct acc e = acc ++ [e] := by
      have h0 : ct ≠ 0 := by simp only [List.length_cons] at hl; omega
      have hlen : acc.length ≠ ct := by simp only [List.length_cons] at hl; omega
      unfold tkIns
      simp [h0, hnot, hlen]
    unfold apTk
    simp only [hne, ↓reduceIte, hins]
    have := apTk_fresh ct now es (acc ++ [e]) (by simpa [List.append_assoc] using hu)
      (by simp only [List.length_cons, List.length_append, List.length_nil] at hl ⊢; omega)
      (fun x hx' => hx x (by simp [hx']))
    simp [this, List.append_assoc]

theorem apKr_fresh (cap : Nat) : ∀ (es acc : List (Node × Nat)), Uniq (acc ++ es) → acc.length + es.length ≤ cap →
    (∀ e ∈ es, 0 < e.2) → apKr cap es acc = (acc ++ es, es.length)
  | [], acc, _, _, _ => by simp [apKr]
  | e :: es, acc, hu, hl, hx => by
    have hpos : 0 < e.2 := hx e (by simp)
    have hnot := not_any_of_uniq acc es e hu
    have hins : krIns cap acc e = (acc ++ [e], 1) := by
      have h0 : e.2 ≠ 0 := by omega
      have hlen : acc.length < cap := by simp only [List.length_cons] at hl; omega
      unfold krIns
      simp [h0, hnot, hlen]
    unfold apKr
    simp only [hins]
    have := apKr_fresh cap es (acc ++ [e]) (by simpa [List.append_assoc] using hu)
      (by simp only [List.length_cons, List.length_append, List.length_nil] at hl ⊢; omega)
      (fun x hx' => hx x (by simp [hx']))
    simp [this, List.append_assoc]

theorem apEk_fresh (cap : Nat) : ∀ (es acc : List (Node × Bytes)), Uniq (acc ++ es) → acc.length + es.length ≤ cap →
    apEk cap es acc = acc ++ es
  | [], acc, _, _ => by simp [apEk]
  | e :: es, acc, hu, hl => by
    have hnot := not_any_of_uniq acc es e hu
    have hins : ekIns cap acc e = acc ++ [e] := by
      have h0 : cap ≠ 0 := by simp only [List.length_cons] at hl; omega
      have hlen : acc.length ≠ cap := by simp only [List.length_cons] at hl; omega
      unfold ekIns
      simp [h0, hnot, hlen]
    unfold apEk
    simp only [hins]
    rw [apEk_fresh cap es (acc ++ [e]) (by simpa [List.append_assoc] using hu)
      (by simp only [List.length_cons, List.length_append, List.length_nil] at hl ⊢; omega)]
    simp [List.append_assoc]

/-- Every ticket of a store made of unexpired tickets of the state is counted. -/
theorem tkHeld_self (now : Nat) (tk : List TkT) (h : ∀ t ∈ tk, now ≤ tkExp t) : tkHeld now tk tk = tk.length := by
  unfold tkHeld
  rw [List.filter_eq_self.mpr]
  intro x hx
  exact List.any_eq_true.mpr ⟨x, hx, by simp [h x hx]⟩

/-- Restoring what was written into an empty endpoint gives exactly the tables written, and reports how many of each
(a state with one entry per peer, within the bounds, round trips above 0, tickets not expired by `now`). -/
theorem restore_fresh (c : Cfg) (hl : c.lazy = false) (hx : c.lax = false) (s : St) (now : Nat) (w : WFs s)
    (u1 : Uniq s.tk) (l1 : s.tk.length ≤ c.ct) (e1 : ∀ t ∈ s.tk, now ≤ tkExp t)
    (u2 : Uniq s.kr) (l2 : s.kr.length ≤ c.kr) (e2 : ∀ e ∈ s.kr, 0 < e.2)
    (u3 : Uniq s.ek) (l3 : s.ek.length ≤ c.ek) :
    restore c ⟨[], [], []⟩ (enc s) now = (s, some (s.tk.length, s.kr.length, s.ek.length)) := by
  unfold restore
  have hp : hdrP c.lax (enc s) = some (hdrOf s) := by
    rw [hx, hdrP_false]; exact decodeAll_emit hdrC _ (hdrOf_wf s w)
  rw [hp]
  dsimp only [hTk, hNk, hKr, hNe, hEk, hdrOf]
  simp only [tkDec_enc _ w.1 w.2.1, krDec_enc _ w.2.2.2.2.1, ekDec_enc _ w.2.2.2.2.2.2, hl, Option.isSome_some, Bool.and_self, Bool.not_true, Bool.not_false, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte]
  rw [apTk_fresh c.ct now s.tk [] (by simpa using u1) (by simpa using l1) e1,
    apKr_fresh c.kr s.kr [] (by simpa using u2) (by simpa using l2) e2,
    apEk_fresh c.ek s.ek [] (by simpa using u3) (by simpa using l3)]
  have ht := tkHeld_self now s.tk e1
  cases s
  simp [ht]

/-- A restore accepts exactly the inputs `parse` reads (the reader without the check that nothing follows is the
witness of why it is there). -/
theorem restore_ok_iff (c : Cfg) (hl : c.lazy = false) (hx : c.lax = false) (live : St) (b : Bytes) (now : Nat) :
    (restore c live b now).2.isSome = (parse b).isSome := by
  unfold restore parse
  simp only [hx, hl]
  cases hh : hdrP false b with
  | none => rfl
  | some hd =>
    simp only [stages]
    cases t1 : tkDec (hTk hd) with
    | none => simp
    | some tl =>
      cases t2 : krDec (hNk hd) (hKr hd) with
      | none => simp
      | some kl =>
        cases t3 : ekDec (hNe hd) (hEk hd) with
        | none => simp
        | some el => simp

/-! ## The wrong readers fail

`lazy` defers the check of the round trips and prekey peers to the stage that stores them; `lax` lets bytes follow
the state. A state whose tickets are fine and whose round trip names an unknown algorithm (tag 0): the lazy reader
refuses it but has already stored the ticket; the real reader refuses it and stores nothing. -/

def fin (xs : List Nat) : Bytes := xs.map (Fin.ofNat 256)

def zeros (n : Nat) : List Nat := List.replicate n 0

/-- One ticket: an Ed25519-tagged node of zeros, an ALPN of one byte (7), a zero id and key, AEAD 1. -/
def tk1 : List Nat := [1] ++ zeros 32 ++ [1, 7] ++ zeros 16 ++ zeros 32 ++ [1] ++ zeros 8 ++ zeros 6

/-- A round trip with the unknown algorithm tag 0. -/
def badKr : List Nat := [0] ++ zeros 32 ++ zeros 8

/-- A state: that ticket, then one round trip with tag 0, no prekey peers. -/
def lazyIn : Bytes := fin ([1, 0, 0, 0, 100] ++ [1, 1] ++ tk1 ++ [0, 1] ++ badKr ++ [0, 0])

def empty : St := ⟨[], [], []⟩

set_option maxRecDepth 100000 in
theorem lazy_not_atomic :
    (restore ⟨3, 4, 4, true, false⟩ empty lazyIn 0).2 = none ∧
      (restore ⟨3, 4, 4, true, false⟩ empty lazyIn 0).1.tk.length = 1 := by
  decide

set_option maxRecDepth 100000 in
/-- The real reader refuses the same bytes and stores no ticket. -/
theorem checked_is_atomic :
    (restore ⟨3, 4, 4, false, false⟩ empty lazyIn 0).2 = none ∧
      (restore ⟨3, 4, 4, false, false⟩ empty lazyIn 0).1.tk.length = 0 := by
  decide

/-- With bytes allowed after the state, the string `enc empty ++ [0]` is accepted, though it is the encoding of
no state: the check is what makes the encoding canonical. -/
theorem lax_not_canon :
    parse (enc empty ++ fin [0]) = none ∧
      (restore ⟨3, 4, 4, false, true⟩ empty (enc empty ++ fin [0]) 0).2.isSome = true := by
  decide

end Pinc.CoreState

#audit_axioms Pinc.CoreState.enc_parse
#audit_axioms Pinc.CoreState.parse_canon
#audit_axioms Pinc.CoreState.parse_injective
#audit_axioms Pinc.CoreState.parse_trailing
#audit_axioms Pinc.CoreState.parse_prefix
#audit_axioms Pinc.CoreState.parse_sizes
#audit_axioms Pinc.CoreState.parse_checks
#audit_axioms Pinc.CoreState.restore_bounded
#audit_axioms Pinc.CoreState.restore_atomic
#audit_axioms Pinc.CoreState.restore_ok_iff
#audit_axioms Pinc.CoreState.restore_fresh
#audit_axioms Pinc.CoreState.lazy_not_atomic
#audit_axioms Pinc.CoreState.checked_is_atomic
#audit_axioms Pinc.CoreState.lax_not_canon
