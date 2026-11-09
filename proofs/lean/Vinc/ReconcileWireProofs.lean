import Vinc.ReconcileWire

/-!
# Reconcile wire proofs: varint fields, readers and prefix-compressed bounds

Unbounded theorems about `Vinc.ReconcileWire` (the Lean model of `vinc-reconcile/src/wire.rs`), on top of the varint
theorems of `Vinc.Varint`. The TLA+ counterpart is `proofs/tla/ReconcileWire.tla`; the trace validation is
`TraceReconcileWire.lean` and `proofs/tla/TraceReconcileWire.tla`.

* `count_venc`, `count_canonical`: a length or a count round-trips and has one encoding.
* `readBound_putBound`: a bound encoded against the running `last` reads back, whatever the shared prefix length
  (including the cap at 255 and bounds longer than 255 bytes); `readBound_canonical`: a byte string is accepted
  only when it is the encoding the encoder writes, so a bound has exactly one encoding.
* The refusals of `readBound` are exact, in the order of the code: `readBound_nil`, `readBound_count_err`,
  `readBound_bound_err`, `readBound_short`, `readBound_noncanon`. `readBound` is a function of the previous bound: a
  refusal returns only the reason, so the caller's `last` is untouched.
-/

namespace Vinc.Reconcile
open Vinc.Varint (ValidBytes)

/-! ## Varints as fields -/

theorem venc_valid (v : Nat) : ValidBytes (venc v) := by
  unfold venc; rw [Varint.encodeBytes_eq]; exact Varint.encRec_valid v

theorem venc_length (v : Nat) : (venc v).length = Varint.encodedLen v := Varint.length_encodeBytes v

theorem count_venc (v : Nat) (rest : List Nat) (hv : v < 2 ^ 63) : count (venc v ++ rest) = .ok (v, rest) := by
  unfold count venc
  have hd : List.drop (Varint.encodeBytes v).length (Varint.encodeBytes v ++ rest) = rest := List.drop_left' rfl
  rw [Varint.decode_encode v rest hv]
  simp [hd]

theorem count_canonical (r : List Nat) (hr : ValidBytes r) (v : Nat) (r' : List Nat)
    (h : count r = .ok (v, r')) : v < 2 ^ 63 ∧ r = venc v ++ r' := by
  unfold count at h
  cases hd : Varint.decode r with
  | error e => simp [hd] at h
  | ok p =>
    obtain ⟨v', used⟩ := p
    simp only [hd, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, _⟩ := Varint.decode_canonical r hr v' used hd
    refine ⟨(Varint.decode_bounds r hr v' used hd).1, ?_⟩
    unfold venc; rw [← h1, List.take_append_drop]

/-- A count that does not decode is `Truncated`, and nothing else. -/
theorem count_err (r : List Nat) (e : Reason) (h : count r = .error e) : e = .truncated := by
  unfold count at h; split at h <;> simp_all

/-! ## The reader -/

theorem readU8_nil : readU8 [] = .error .truncated := rfl
theorem readU8_cons (b : Nat) (r : List Nat) : readU8 (b :: r) = .ok (b, r) := rfl

theorem readBytes_ok (n : Nat) (r : List Nat) (h : n ≤ r.length) : readBytes n r = .ok (r.take n, r.drop n) := by
  unfold readBytes; simp [h]

theorem readBytes_short (n : Nat) (r : List Nat) (h : r.length < n) : readBytes n r = .error .truncated := by
  unfold readBytes; simp; omega

/-- `readBytes` consumes exactly the bytes it returns. -/
theorem readBytes_consumes (n : Nat) (r x r' : List Nat) (h : readBytes n r = .ok (x, r')) :
    r = x ++ r' ∧ x.length = n := by
  unfold readBytes at h
  split at h
  · rename_i hn
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(List.take_append_drop n r).symm, by simp; omega⟩
  · simp at h

/-! ## The shared prefix length -/

theorem cpl_le_left : ∀ a b : List Nat, cpl a b ≤ a.length
  | [], _ => by simp [cpl]
  | _ :: _, [] => by simp [cpl]
  | x :: xs, y :: ys => by
    unfold cpl; split
    · have := cpl_le_left xs ys; simp; omega
    · simp

theorem cpl_le_right : ∀ a b : List Nat, cpl a b ≤ b.length
  | [], _ => by simp [cpl]
  | _ :: _, [] => by simp [cpl]
  | x :: xs, y :: ys => by
    unfold cpl; split
    · have := cpl_le_right xs ys; simp; omega
    · simp

theorem cpl_append : ∀ (p xs ys : List Nat), cpl (p ++ xs) (p ++ ys) = p.length + cpl xs ys
  | [], xs, ys => by simp
  | x :: p, xs, ys => by
    have := cpl_append p xs ys
    simp [cpl, this]; omega

/-- No shared prefix: the strings differ at once or one is empty. -/
theorem cpl_zero_heads : ∀ xs ys : List Nat, cpl xs ys = 0 →
    (match xs, ys with | x :: _, y :: _ => x == y | _, _ => false) = false
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | x :: xs, y :: ys, h => by
    unfold cpl at h
    split at h
    · omega
    · rename_i hne; simp [hne]

/-- The shared prefix of `a` and `b` is a prefix of both. -/
theorem cpl_take : ∀ a b : List Nat, a.take (cpl a b) = b.take (cpl a b)
  | [], _ => by simp [cpl]
  | _ :: _, [] => by simp [cpl]
  | x :: xs, y :: ys => by
    unfold cpl; split
    · rename_i h; subst h; simp [cpl_take xs ys]
    · simp

theorem cpl_take_le (a b : List Nat) (c : Nat) (h : c ≤ cpl a b) : a.take c = b.take c := by
  have h1 := cpl_take a b
  have h2 : (a.take (cpl a b)).take c = a.take c := by rw [List.take_take]; congr 1; omega
  have h3 : (b.take (cpl a b)).take c = b.take c := by rw [List.take_take]; congr 1; omega
  rw [← h2, ← h3, h1]

theorem cpl_ge_take (a s : List Nat) (c : Nat) (h : c ≤ a.length) : c ≤ cpl a (a.take c ++ s) := by
  have e : a = a.take c ++ a.drop c := (List.take_append_drop c a).symm
  have := cpl_append (a.take c) (a.drop c) s
  rw [← e] at this
  rw [this]; simp; omega

/-! ## Bounds -/

theorem putBound_snd (last b : Item) : (putBound last b).2 = b := rfl

theorem putBound_fst (last b : Item) :
    (putBound last b).1 = [min (cpl last b) cplMax] ++ venc (b.length - min (cpl last b) cplMax)
      ++ b.drop (min (cpl last b) cplMax) := rfl

/-- The exact size of an encoded bound. -/
theorem putBound_length (last b : Item) :
    (putBound last b).1.length =
      1 + Varint.encodedLen (b.length - min (cpl last b) cplMax) + (b.length - min (cpl last b) cplMax) := by
  rw [putBound_fst]; simp [venc_length]; have := cpl_le_right last b; omega

/-- Reading a bound: the order of the checks of `read_bound` -/
theorem readBound_nil (last : Item) (mx : Nat) : readBound last [] mx = .error .truncated := rfl

theorem readBound_count_err (last : Item) (c : Nat) (r : List Nat) (mx : Nat) (h : count r = .error .truncated) :
    readBound last (c :: r) mx = .error .truncated := by
  simp [readBound, readU8, h]

theorem readBound_bound_err (last : Item) (c n : Nat) (r r2 : List Nat) (mx : Nat)
    (h : count r = .ok (n, r2)) (hb : c > last.length ∨ c + n > mx) :
    readBound last (c :: r) mx = .error .bound := by
  simp [readBound, readU8, h]
  rcases hb with hb | hb
  · intro h'; omega
  · intro _; omega

theorem readBound_short (last : Item) (c n : Nat) (r r2 : List Nat) (mx : Nat)
    (h : count r = .ok (n, r2)) (hb : ¬(c > last.length ∨ c + n > mx)) (hs : r2.length < n) :
    readBound last (c :: r) mx = .error .truncated := by
  have hb' : ¬ c > last.length := fun h' => hb (Or.inl h')
  have hb'' : ¬ c + n > mx := fun h' => hb (Or.inr h')
  simp [readBound, readU8, h, hb', hb'', readBytes_short n r2 hs]

theorem readBound_noncanon (last : Item) (c n : Nat) (r r2 : List Nat) (mx : Nat)
    (h : count r = .ok (n, r2)) (hb : ¬(c > last.length ∨ c + n > mx)) (hs : n ≤ r2.length)
    (hn : c < cplMax) (hh : (match last.drop c, r2.take n with | x :: _, y :: _ => x == y | _, _ => false) = true) :
    readBound last (c :: r) mx = .error .bound := by
  have hb' : ¬ c > last.length := fun h' => hb (Or.inl h')
  have hb'' : ¬ c + n > mx := fun h' => hb (Or.inr h')
  simp [readBound, readU8, h, hb', hb'', readBytes_ok n r2 hs, hn]
  exact hh

/-- The success path. -/
theorem readBound_ok (last : Item) (c n : Nat) (r r2 : List Nat) (mx : Nat)
    (h : count r = .ok (n, r2)) (hb : ¬(c > last.length ∨ c + n > mx)) (hs : n ≤ r2.length)
    (hn : ¬(c < cplMax ∧ (match last.drop c, r2.take n with | x :: _, y :: _ => x == y | _, _ => false) = true)) :
    readBound last (c :: r) mx = .ok (last.take c ++ r2.take n, r2.drop n) := by
  have hb' : ¬ c > last.length := fun h' => hb (Or.inl h')
  have hb'' : ¬ c + n > mx := fun h' => hb (Or.inr h')
  have hn' : ¬ (c < cplMax ∧ (match last.drop c, r2.take n with | x :: _, y :: _ => x == y | _, _ => false) = true) := hn
  simp [readBound, readU8, h, hb', hb'', readBytes_ok n r2 hs]
  intro h1
  cases hx : (match List.drop c last, List.take n r2 with | x :: _, y :: _ => x == y | _, _ => false) with
  | false => exact hx
  | true => exact absurd ⟨h1, hx⟩ hn'

theorem readU8_err (r : List Nat) (e : Reason) (h : readU8 r = .error e) : e = .truncated := by
  cases r <;> simp [readU8] at h <;> exact h.symm

theorem readBytes_err (n : Nat) (r : List Nat) (e : Reason) (h : readBytes n r = .error e) : e = .truncated := by
  unfold readBytes at h; split at h <;> simp_all

/-- Every refusal of `readBound` is a `Truncated` or a `Bound`, and returns no bound: the previous bound is the
caller's and is replaced only on success. -/
theorem readBound_err_reason (last : Item) (r : List Nat) (mx : Nat) (e : Reason)
    (h : readBound last r mx = .error e) : e = .truncated ∨ e = .bound := by
  cases r with
  | nil => rw [readBound_nil] at h; simp at h; exact Or.inl h.symm
  | cons c r1 =>
    cases hc : count r1 with
    | error e2 =>
      have := count_err r1 _ hc
      subst this
      rw [readBound_count_err last c r1 mx hc] at h; simp at h; exact Or.inl h.symm
    | ok q =>
      obtain ⟨n, r2⟩ := q
      by_cases hb : c > last.length ∨ c + n > mx
      · rw [readBound_bound_err last c n r1 r2 mx hc hb] at h; simp at h; exact Or.inr h.symm
      · by_cases hs : n ≤ r2.length
        · by_cases hn : c < cplMax ∧ (match last.drop c, r2.take n with | x :: _, y :: _ => x == y | _, _ => false) = true
          · rw [readBound_noncanon last c n r1 r2 mx hc hb hs hn.1 hn.2] at h; simp at h; exact Or.inr h.symm
          · rw [readBound_ok last c n r1 r2 mx hc hb hs hn] at h; simp at h
        · rw [readBound_short last c n r1 r2 mx hc hb (by omega)] at h; simp at h; exact Or.inl h.symm

/-- A bound encoded against `last` reads back, with the rest untouched. -/
theorem readBound_putBound (last b rest : Item) (mx : Nat) (hb : b.length ≤ mx) (hv : b.length < 2 ^ 63) :
    readBound last ((putBound last b).1 ++ rest) mx = .ok (b, rest) := by
  obtain ⟨c, hc⟩ : ∃ c, c = min (cpl last b) cplMax := ⟨_, rfl⟩
  have hcl : c ≤ last.length := by have := cpl_le_left last b; omega
  have hcb : c ≤ b.length := by have := cpl_le_right last b; omega
  have htk : last.take c = b.take c := cpl_take_le last b c (by omega)
  have hlen : (b.drop c).length = b.length - c := by simp
  rw [putBound_fst, ← hc]
  have e : [c] ++ venc (b.length - c) ++ b.drop c ++ rest = c :: (venc (b.length - c) ++ (b.drop c ++ rest)) := by
    simp
  rw [e]
  have hcnt := count_venc (b.length - c) (b.drop c ++ rest) (by omega)
  have htake : (b.drop c ++ rest).take (b.length - c) = b.drop c := by
    rw [← hlen]; exact List.take_left' rfl
  have hdrop : (b.drop c ++ rest).drop (b.length - c) = rest := by
    rw [← hlen]; exact List.drop_left' rfl
  have hs : b.length - c ≤ (b.drop c ++ rest).length := by simp only [List.length_append, List.length_drop]; omega
  have hnc : ¬(c < cplMax ∧ (match last.drop c, (b.drop c ++ rest).take (b.length - c) with
      | x :: _, y :: _ => x == y | _, _ => false) = true) := by
    rintro ⟨h1, h2⟩
    rw [htake] at h2
    have hcp : cpl last b = c := by omega
    have e1 : last = last.take c ++ last.drop c := (List.take_append_drop c last).symm
    have e2 : b = last.take c ++ b.drop c := by rw [htk]; exact (List.take_append_drop c b).symm
    have h3 := cpl_append (last.take c) (last.drop c) (b.drop c)
    rw [← e1, ← e2, hcp] at h3
    simp [hcl] at h3
    have := cpl_zero_heads _ _ (by simpa using h3)
    rw [this] at h2; simp at h2
  rw [readBound_ok last c _ _ _ mx hcnt (by omega) hs hnc, htake, hdrop, htk]
  simp [List.take_append_drop]

/-- The cap and the canonical check pin the shared prefix length of a bound built from `last.take c` and a suffix. -/
theorem canon_cpl (last sfx : Item) (c : Nat) (hc : c ≤ last.length) (hcm : c ≤ cplMax)
    (hn : ¬(c < cplMax ∧ (match last.drop c, sfx with | x :: _, y :: _ => x == y | _, _ => false) = true)) :
    min (cpl last (last.take c ++ sfx)) cplMax = c := by
  have hge := cpl_ge_take last sfx c hc
  by_cases hc255 : c < cplMax
  · have e1 : last = last.take c ++ last.drop c := (List.take_append_drop c last).symm
    have h3 := cpl_append (last.take c) (last.drop c) sfx
    have hclen : (last.take c).length = c := by simp; omega
    rw [← e1, hclen] at h3
    have hz : cpl (last.drop c) sfx = 0 := by
      cases hl : last.drop c with
      | nil => simp [cpl]
      | cons x xs =>
        cases ht : sfx with
        | nil => simp [cpl]
        | cons y ys =>
          cases hxy : decide (x = y) with
          | true => exact absurd ⟨hc255, by simp at hxy; simp [hl, ht, hxy]⟩ hn
          | false => simp at hxy; simp [cpl, hxy]
    omega
  · omega

/-- The encoding of a bound read from `c` and a suffix is the bytes it was read from. -/
theorem putBound_of_parts (last sfx : Item) (c : Nat) (hc : c ≤ last.length) (hcm : c ≤ cplMax)
    (hn : ¬(c < cplMax ∧ (match last.drop c, sfx with | x :: _, y :: _ => x == y | _, _ => false) = true)) :
    (putBound last (last.take c ++ sfx)).1 = [c] ++ venc sfx.length ++ sfx := by
  have hclen : (last.take c).length = c := by simp; omega
  have hk := canon_cpl last sfx c hc hcm hn
  rw [putBound_fst, hk]
  have hl : (last.take c ++ sfx).length - c = sfx.length := by simp [hclen]
  have hd : (last.take c ++ sfx).drop c = sfx := by
    have := List.drop_left' (l₁ := last.take c) (l₂ := sfx) hclen
    exact this
  rw [hl, hd]

/-- One encoding per bound: an accepted byte string is the encoding the encoder writes for the bound it yields. -/
theorem readBound_canonical (last : Item) (r : List Nat) (mx : Nat) (hv : ValidBytes r) (b rest : Item)
    (h : readBound last r mx = .ok (b, rest)) : r = (putBound last b).1 ++ rest ∧ b.length ≤ mx := by
  cases r with
  | nil => simp [readBound_nil] at h
  | cons c r1 =>
    cases hc : count r1 with
    | error e => simp [readBound, readU8, hc] at h
    | ok p =>
      obtain ⟨n, r2⟩ := p
      by_cases hb : c > last.length ∨ c + n > mx
      · rw [readBound_bound_err last c n r1 r2 mx hc hb] at h; simp at h
      · by_cases hs : n ≤ r2.length
        · have hb' : ¬ c > last.length := fun h' => hb (Or.inl h')
          have hb'' : ¬ c + n > mx := fun h' => hb (Or.inr h')
          by_cases hn : c < cplMax ∧ (match last.drop c, r2.take n with | x :: _, y :: _ => x == y | _, _ => false) = true
          · rw [readBound_noncanon last c n r1 r2 mx hc hb hs hn.1 hn.2] at h; simp at h
          · rw [readBound_ok last c n r1 r2 mx hc hb hs hn] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hv1 : ValidBytes r1 := fun x hx => hv x (List.mem_cons_of_mem _ hx)
            obtain ⟨_, hr1⟩ := count_canonical r1 hv1 n r2 hc
            have hlen : (r2.take n).length = n := by simp; omega
            have hc256 : c < 256 := hv c (List.mem_cons_self ..)
            rw [putBound_of_parts last (r2.take n) c (by omega) (by unfold cplMax; omega) hn, hlen, hr1]
            refine ⟨?_, by simp; omega⟩
            simp [List.append_assoc]
        · rw [readBound_short last c n r1 r2 mx hc hb (by omega)] at h; simp at h

end Vinc.Reconcile
