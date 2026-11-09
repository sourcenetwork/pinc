import Vinc.Ranges
import Vinc.DtnLayout

/-!
# The reception of a bundle (`Reception` in `vinc-dtn/src/bundle.rs`)

Unbounded in the number of symbols, the symbol size and the capacity of the held set.

**Imported, as hypotheses and never as declarations.**
- The tree verifier (`Vinc.Tree`, `Vinc.VerifyBytes`, `VerifiedRanges`): a group of a proof stream is delivered only
  if it hashes to the signed root, so it equals the sender's symbol `ct s`. The sink below receives exactly the
  longest prefix of the stream whose groups equal `ct`; collision resistance of the hash is what lets the code
  accept a group on that evidence.
- The signature of the head (`resume` checks it first): a boolean the caller computes.
- The erasure code (`Rs::reconstruct`, proved in `Vinc.DtnRs`): `RsSpec` is its specification, namely that the
  output is a code word, and that it is the code word that agrees with the held symbols whenever at least `k` of them
  are held and the sender's content is a code word.

**Modelled as the code does it.** `feed` copies each delivered group into the buffer and then records its
interval in the capacity-`W` set (`insertState`, whose failure leaves the set unchanged), keeps going after a full
set, and reports the stream fault before the full-set fault (`verdict.and_then(|()| fault)`); an empty range is
`Ok` and changes nothing. The held set is a `Reach` set of `Vinc.Ranges`, so it is sorted, disjoint and within
capacity. `finish` is stated per block, because the code's reconstruction of a block reads and writes only that
block's region of the buffer and the regions are disjoint (`Vinc.DtnLayout.blockStart_spec`); the TLC model
(`DtnReception.tla`) runs the blocks in order on a real code.
-/

namespace Vinc.DtnReception
open Vinc.Ranges Vinc.DtnLayout

variable {V : Type}

/-- Overwrite one symbol of the buffer. -/
def put (buf : Nat → V) (a : Nat) (v : V) : Nat → V := fun u => if u = a then v else buf u

/-- The sink with the verifier in front: groups are taken in order while they equal the sender's symbols; each is
copied into the buffer and its interval recorded (a failed record sets `full` and the loop goes on). The last
component says whether a group failed to verify. -/
def feedGo [DecidableEq V] (ct : Nat → V) (W G : Nat) :
    (Nat → V) → List Interval → Bool → Nat → List V → (Nat → V) × List Interval × Bool × Bool
  | buf, h, full, _, [] => (buf, h, full, false)
  | buf, h, full, a, v :: vs =>
    if v = ct a then
      feedGo ct W G (put buf a v) (insertState W h (a * G, (a + 1) * G))
        (full || (insertFixed W h (a * G, (a + 1) * G)).isNone) (a + 1) vs
    else (buf, h, full, true)

theorem feedGo_nil [DecidableEq V] (ct : Nat → V) (W G : Nat) (buf : Nat → V) (h : List Interval) (full : Bool)
    (a : Nat) : feedGo ct W G buf h full a [] = (buf, h, full, false) := rfl

theorem feedGo_cons [DecidableEq V] (ct : Nat → V) (W G : Nat) (buf : Nat → V) (h : List Interval) (full : Bool)
    (a : Nat) (v : V) (vs : List V) :
    feedGo ct W G buf h full a (v :: vs) =
      if v = ct a then
        feedGo ct W G (put buf a v) (insertState W h (a * G, (a + 1) * G))
          (full || (insertFixed W h (a * G, (a + 1) * G)).isNone) (a + 1) vs
      else (buf, h, full, true) := rfl

/-- The number of groups of the stream that verify. -/
def nverified [DecidableEq V] (ct : Nat → V) : Nat → List V → Nat
  | _, [] => 0
  | a, v :: vs => if v = ct a then nverified ct (a + 1) vs + 1 else 0

/-- Every write of a feed is a verified symbol: only the sender's bytes enter the buffer. -/
theorem feedGo_buf [DecidableEq V] (ct : Nat → V) (W G : Nat) (vs : List V) :
    ∀ (buf : Nat → V) (h : List Interval) (full : Bool) (a : Nat) (u : Nat),
      (feedGo ct W G buf h full a vs).1 u ≠ buf u → (feedGo ct W G buf h full a vs).1 u = ct u := by
  induction vs with
  | nil => intro buf h full a u hu; exact absurd rfl hu
  | cons v vs ih =>
    intro buf h full a u hu
    rw [feedGo_cons] at hu ⊢
    by_cases hv : v = ct a
    · rw [if_pos hv] at hu ⊢
      by_cases hua : u = a
      · subst hua
        by_cases hc : (feedGo ct W G (put buf u v) (insertState W h (u * G, (u + 1) * G))
            (full || (insertFixed W h (u * G, (u + 1) * G)).isNone) (u + 1) vs).1 u = put buf u v u
        · simp [put] at hc; rw [hc]; exact hv
        · exact ih _ _ _ _ u hc
      · exact ih _ _ _ _ u (by simpa [put, hua] using hu)
    · rw [if_neg hv] at hu; exact absurd rfl hu

/-- The held set stays a reachable set (sorted, disjoint, within capacity). -/
theorem feedGo_reach [DecidableEq V] (ct : Nat → V) (W G : Nat) (vs : List V) :
    ∀ (buf : Nat → V) (h : List Interval) (full : Bool) (a : Nat), Reach W h →
      Reach W (feedGo ct W G buf h full a vs).2.1 := by
  induction vs with
  | nil => intro buf h full a hr; exact hr
  | cons v vs ih =>
    intro buf h full a hr
    rw [feedGo_cons]
    by_cases hv : v = ct a
    · rw [if_pos hv]
      exact ih _ _ _ _ (Reach.step _ hr)
    · rw [if_neg hv]; exact hr

/-- The held set only grows, whatever fails: an offset held before is held after. -/
theorem feedGo_mono [DecidableEq V] (ct : Nat → V) (W G : Nat) (vs : List V) :
    ∀ (buf : Nat → V) (h : List Interval) (full : Bool) (a : Nat), Reach W h → ∀ x, Covers h x →
      Covers (feedGo ct W G buf h full a vs).2.1 x := by
  induction vs with
  | nil => intro buf h full a hr x hx; exact hx
  | cons v vs ih =>
    intro buf h full a hr x hx
    rw [feedGo_cons]
    by_cases hv : v = ct a
    · rw [if_pos hv]
      exact ih _ _ _ _ (Reach.step _ hr) x (reach_mono hr _ x hx)
    · rw [if_neg hv]; exact hx

/-- What a feed adds: an offset covered afterwards was covered before or lies in a verified group's symbol. -/
theorem feedGo_new [DecidableEq V] (ct : Nat → V) (W G : Nat) (vs : List V) :
    ∀ (buf : Nat → V) (h : List Interval) (full : Bool) (a : Nat), Reach W h → ∀ x,
      Covers (feedGo ct W G buf h full a vs).2.1 x →
        Covers h x ∨ (a * G ≤ x ∧ x < (a + nverified ct a vs) * G) := by
  induction vs with
  | nil => intro buf h full a hr x hx; exact Or.inl hx
  | cons v vs ih =>
    intro buf h full a hr x hx
    rw [feedGo_cons] at hx
    unfold nverified
    by_cases hv : v = ct a
    · rw [if_pos hv] at hx
      simp only [hv, ite_true]
      have hs : Sound h := (canon_iff h).1 (reach_inv hr).1
      rcases ih _ _ _ _ (Reach.step _ hr) x hx with h1 | h1
      · -- covered by the set after recording the first interval
        by_cases hn : insertFixed W h (a * G, (a + 1) * G) = none
        · rw [insertState_of_none W h _ hn] at h1; exact Or.inl h1
        · rw [insertState_of_some W h hs _ hn, insertVec_covers h hs] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · right; constructor
            · exact h1.1
            · have : (a + 1) * G ≤ (a + (nverified ct (a + 1) vs + 1)) * G := Nat.mul_le_mul_right _ (by omega)
              omega
      · right
        constructor
        · have : a * G ≤ (a + 1) * G := Nat.mul_le_mul_right _ (by omega)
          omega
        · have e : a + 1 + nverified ct (a + 1) vs = a + (nverified ct (a + 1) vs + 1) := by omega
          rw [e] at h1; exact h1.2
    · rw [if_neg hv] at hx
      exact Or.inl hx

/-- Once a record has failed the flag stays set. -/
theorem feedGo_full_sticky [DecidableEq V] (ct : Nat → V) (W G : Nat) (vs : List V) :
    ∀ (buf : Nat → V) (h : List Interval) (a : Nat),
      (feedGo ct W G buf h true a vs).2.2.1 = true := by
  induction vs with
  | nil => intro buf h a; rfl
  | cons w ws ih =>
    intro buf h a
    rw [feedGo_cons]
    by_cases hw : w = ct a
    · rw [if_pos hw]; simpa using ih _ _ _
    · rw [if_neg hw]

/-- A feed that records every verified interval (no failed record) leaves the whole verified run held. -/
theorem feedGo_cover [DecidableEq V] (ct : Nat → V) (W G : Nat) (vs : List V) :
    ∀ (buf : Nat → V) (h : List Interval) (a : Nat), Reach W h →
      (feedGo ct W G buf h false a vs).2.2.1 = false → ∀ x, a * G ≤ x → x < (a + nverified ct a vs) * G →
        Covers (feedGo ct W G buf h false a vs).2.1 x := by
  induction vs with
  | nil =>
    intro buf h a hr hf x h1 h2
    have : a + nverified ct a [] = a := by simp [nverified]
    rw [this] at h2; omega
  | cons v vs ih =>
    intro buf h a hr hf x h1 h2
    unfold nverified at h2
    rw [feedGo_cons] at hf ⊢
    by_cases hv : v = ct a
    · rw [if_pos hv] at hf ⊢
      simp only [hv, ite_true] at h2
      have hs : Sound h := (canon_iff h).1 (reach_inv hr).1
      have hnone : (insertFixed W h (a * G, (a + 1) * G)).isNone = false := by
        cases hc : (insertFixed W h (a * G, (a + 1) * G)).isNone with
        | false => rfl
        | true =>
          rw [Bool.false_or, hc] at hf
          rw [feedGo_full_sticky] at hf; exact absurd hf (by simp)
      have hsome : ∃ l', insertFixed W h (a * G, (a + 1) * G) = some l' := by
        cases hh : insertFixed W h (a * G, (a + 1) * G) with
        | none => simp [hh] at hnone
        | some l' => exact ⟨l', rfl⟩
      obtain ⟨l', hl'⟩ := hsome
      by_cases hxa : x < (a + 1) * G
      · have hc1 : Covers (insertState W h (a * G, (a + 1) * G)) x := by
          have : insertState W h (a * G, (a + 1) * G) = l' := by simp [insertState, hl']
          rw [this, insertFixed_covers W h hs _ l' hl']
          exact Or.inr ⟨h1, hxa⟩
        exact feedGo_mono ct W G vs _ _ _ _ (Reach.step _ hr) x hc1
      · simp only [Bool.false_or, hnone]
        have hf' : (feedGo ct W G (put buf a v) (insertState W h (a * G, (a + 1) * G)) false (a + 1) vs).2.2.1
            = false := by
          simpa [hnone] using hf
        have e : a + 1 + nverified ct (a + 1) vs = a + (nverified ct (a + 1) vs + 1) := by omega
        exact ih (put buf a v) (insertState W h (a * G, (a + 1) * G)) (a + 1) (Reach.step _ hr) hf' x
          (by omega) (by rw [e]; exact h2)
    · rw [if_neg hv] at hf ⊢
      simp only [hv, ite_false, Nat.add_zero] at h2; omega

/-! ## Held symbols -/

/-- `Reception::holds`. -/
def holds (G total : Nat) (h : List Interval) (s : Nat) : Bool :=
  decide (s < total) && containsRange h (s * G, (s + 1) * G)

theorem holds_iff (G total : Nat) (h : List Interval) (hs : Sound h) (s : Nat) :
    holds G total h s = true ↔ s < total ∧ ∀ x, s * G ≤ x → x < (s + 1) * G → Covers h x := by
  unfold holds
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [containsRange_iff h hs]

/-- Every held symbol of a reception built only by feeds carries the sender's bytes: if every covered offset lies in a
symbol whose buffer entry is the sender's, so does every offset covered after a feed. -/
theorem feedGo_verified [DecidableEq V] (ct : Nat → V) (W G : Nat) (hG : 0 < G) (vs : List V) :
    ∀ (buf : Nat → V) (h : List Interval) (full : Bool) (a : Nat), Reach W h →
      (∀ x, Covers h x → buf (x / G) = ct (x / G)) →
      ∀ x, Covers (feedGo ct W G buf h full a vs).2.1 x →
        (feedGo ct W G buf h full a vs).1 (x / G) = ct (x / G) := by
  intro buf h full a hr hinv x hx
  rcases feedGo_new ct W G vs buf h full a hr x hx with h1 | h1
  · have := hinv x h1
    by_cases hc : (feedGo ct W G buf h full a vs).1 (x / G) = buf (x / G)
    · rw [hc]; exact this
    · exact feedGo_buf ct W G vs buf h full a _ hc
  · -- x lies in a delivered symbol t: its buffer entry is the sender's
    obtain ⟨t, ht⟩ : ∃ t, t = x / G := ⟨_, rfl⟩
    have hge : a ≤ t := by
      rw [ht]; exact (Nat.le_div_iff_mul_le hG).2 h1.1
    have hlt : t < a + nverified ct a vs := by
      rw [ht]; exact (Nat.div_lt_iff_lt_mul hG).2 h1.2
    -- the symbol was written with the sender's value
    have hw : ∀ (vs : List V) (buf : Nat → V) (h : List Interval) (full : Bool) (a : Nat),
        a ≤ t → t < a + nverified ct a vs → (feedGo ct W G buf h full a vs).1 t = ct t := by
      intro vs
      induction vs with
      | nil =>
        intro buf h full a h1 h2
        have : a + nverified ct a [] = a := by simp [nverified]
        rw [this] at h2; omega
      | cons v vs ih =>
        intro buf h full a h1 h2
        rw [feedGo_cons]; unfold nverified at h2
        by_cases hv : v = ct a
        · rw [if_pos hv]; simp only [hv, ite_true] at h2
          by_cases hta : t = a
          · subst hta
            by_cases hc : (feedGo ct W G (put buf t v) (insertState W h (t * G, (t + 1) * G))
                (full || (insertFixed W h (t * G, (t + 1) * G)).isNone) (t + 1) vs).1 t = put buf t v t
            · simp [put] at hc; rw [hc]; exact hv
            · exact feedGo_buf ct W G vs _ _ _ _ t hc
          · exact ih _ _ _ _ (by omega) (by omega)
        · simp only [hv, ite_false] at h2; omega
    rw [← ht]; exact hw vs buf h full a hge hlt

/-! ## Streams and verdicts -/

/-- The error of a feed: the stream fault (a group that does not verify, a stream that stops early, trailing bytes)
first, then the full set. `true` is `Ok`. -/
def feedOk (n : Nat) (nv : Nat) (extra full : Bool) : Bool := decide (nv = n) && !extra && !full

/-- `Reception::feed` on the symbols `[a, b)` with the stream's groups `vals` and a flag for trailing bytes: the new
buffer, the new held set and whether it returned `Ok`. An empty range returns before anything is read. -/
def feed [DecidableEq V] (ct : Nat → V) (W G : Nat) (buf : Nat → V) (h : List Interval) (a b : Nat) (vals : List V)
    (extra : Bool) : (Nat → V) × List Interval × Bool :=
  if a = b then (buf, h, true)
  else
    let r := feedGo ct W G buf h false a vals
    (r.1, r.2.1, feedOk (b - a) (nverified ct a vals) extra r.2.2.1)

/-- An empty range is `Ok` and nothing changes (`if bytes.is_empty() { return Ok(()) }`). -/
theorem feed_empty [DecidableEq V] (ct : Nat → V) (W G : Nat) (buf : Nat → V) (h : List Interval) (a : Nat)
    (vals : List V) (extra : Bool) : feed ct W G buf h a a vals extra = (buf, h, true) := by
  simp [feed]

/-- `Ok` means: every group of the range verified, no bytes trail and every record succeeded. -/
theorem feed_ok_iff [DecidableEq V] (ct : Nat → V) (W G : Nat) (buf : Nat → V) (h : List Interval) (a b : Nat)
    (hab : a ≠ b) (vals : List V) (extra : Bool) :
    (feed ct W G buf h a b vals extra).2.2 = true ↔
      nverified ct a vals = b - a ∧ extra = false ∧ (feedGo ct W G buf h false a vals).2.2.1 = false := by
  simp [feed, hab, feedOk, and_assoc]

/-- A feed that returns `Ok` holds every symbol of its range afterwards. -/
theorem feed_ok_holds [DecidableEq V] (ct : Nat → V) (W G total : Nat) (hG : 0 < G) (vs : List V)
    (buf : Nat → V) (h : List Interval) (a b : Nat) (hr : Reach W h) (hn : b - a = vs.length) (hab : a ≤ b)
    (hok : nverified ct a vs = vs.length) (hf : (feedGo ct W G buf h false a vs).2.2.1 = false)
    (t : Nat) (h1 : a ≤ t) (h2 : t < b) (ht : t < total) :
    holds G total (feedGo ct W G buf h false a vs).2.1 t = true := by
  have hrr := feedGo_reach ct W G vs buf h false a hr
  have hs : Sound (feedGo ct W G buf h false a vs).2.1 := (canon_iff _).1 (reach_inv hrr).1
  rw [holds_iff G total _ hs]
  refine ⟨ht, fun x hx1 hx2 => feedGo_cover ct W G vs buf h a hr hf x ?_ ?_⟩
  · have : a * G ≤ t * G := Nat.mul_le_mul_right _ h1
    omega
  · rw [hok]
    have : (t + 1) * G ≤ (a + vs.length) * G := Nat.mul_le_mul_right _ (by omega)
    omega

/-! ## Completeness, decodability -/

/-- `Reception::is_complete`: every symbol is held. -/
theorem isComplete_iff (G total : Nat) (hG : 0 < G) (h : List Interval) (hs : Sound h) :
    containsRange h (0, total * G) = true ↔ ∀ s, s < total → holds G total h s = true := by
  rw [containsRange_iff h hs]
  constructor
  · intro H s hst
    rw [holds_iff G total h hs]
    refine ⟨hst, fun x h1 h2 => H x (by omega) ?_⟩
    have : (s + 1) * G ≤ total * G := Nat.mul_le_mul_right _ hst
    omega
  · intro H x h1 h2
    have hxs : x / G < total := (Nat.div_lt_iff_lt_mul hG).2 h2
    have := (holds_iff G total h hs (x / G)).1 (H _ hxs)
    exact this.2 x ((Nat.le_div_iff_mul_le hG).1 (Nat.le_refl _)) (by
      have := Nat.lt_div_mul_add (a := x) hG
      rw [Nat.add_mul, Nat.one_mul]; omega)

/-- The symbols of block `b` that are held. -/
def heldIn (G total : Nat) (h : List Interval) (start n : Nat) : Nat :=
  ((List.range n).filter fun i => holds G total h (start + i)).length

/-- `Reception::is_decodable`: every block holds at least `k` of its symbols. -/
def isDecodable (l : L) (G total : Nat) (h : List Interval) : Prop :=
  ∀ b, b < l.blocks → l.blockK b ≤ heldIn G total h (b * (l.k + l.m)) (l.blockN b)

/-! ## Finish -/

/-- The specification of `Rs::reconstruct` as the reception uses it: on a block vector (index 0 to `k + m - 1`)
with present flags, the output is a code word, and it is the code word that agrees with the present symbols
whenever at least `k` are present and the sender's block is a code word. -/
structure RsSpec (V : Type) where
  cw : Nat → Nat → (Nat → V) → Prop
  recon : Nat → Nat → (Nat → V) → (Nat → Bool) → (Nat → V)
  cw_congr : ∀ k m f g, (∀ i, i < k + m → f i = g i) → (cw k m f ↔ cw k m g)
  recon_cw : ∀ k m buf pres, cw k m (recon k m buf pres)
  recon_ext : ∀ k m c buf pres, cw k m c → k ≤ ((List.range (k + m)).filter fun i => pres i).length →
    (∀ i, i < k + m → pres i = true → buf i = c i) → ∀ i, i < k + m → recon k m buf pres i = c i

/-- The buffer after `finish` rebuilt the block of `blockK` data symbols that starts at `start`, from the held
flags `pres` of its symbols. -/
def blockOut (rs : RsSpec V) (k m start : Nat) (pres : Nat → Bool) (buf : Nat → V) (i : Nat) : V :=
  rs.recon k m (fun j => buf (start + j)) pres i

/-- `finish` accepts a block exactly when the rebuilt block equals the sender's. With the held symbols verified and
at least `k` of them held, that is exactly when the sender's block is a code word: an honest sender is never
reported `Inconsistent`, and a sender whose parity is not a code word is reported `Inconsistent` unless the block is
fully held (then it is skipped). -/
theorem block_consistent_iff (rs : RsSpec V) (k m start : Nat) (pres : Nat → Bool) (buf ct : Nat → V)
    (hv : ∀ i, i < k + m → pres i = true → buf (start + i) = ct (start + i))
    (hk : k ≤ ((List.range (k + m)).filter fun i => pres i).length) :
    (∀ i, i < k + m → blockOut rs k m start pres buf i = ct (start + i)) ↔ rs.cw k m (fun i => ct (start + i)) := by
  constructor
  · intro H
    have hc : rs.cw k m (blockOut rs k m start pres buf) := rs.recon_cw k m (fun j => buf (start + j)) pres
    exact (rs.cw_congr k m _ _ (fun i hi => (H i hi).symm)).2 hc
  · intro hcw i hi
    exact rs.recon_ext k m (fun j => ct (start + j)) (fun j => buf (start + j)) pres hcw hk
      (fun j hj hp => hv j hj hp) i hi

/-- The honest case: a sender whose block is a code word is never reported inconsistent. -/
theorem honest_never_inconsistent (rs : RsSpec V) (k m start : Nat) (pres : Nat → Bool) (buf ct : Nat → V)
    (hv : ∀ i, i < k + m → pres i = true → buf (start + i) = ct (start + i))
    (hk : k ≤ ((List.range (k + m)).filter fun i => pres i).length)
    (hcw : rs.cw k m (fun i => ct (start + i))) :
    ∀ i, i < k + m → blockOut rs k m start pres buf i = ct (start + i) :=
  (block_consistent_iff rs k m start pres buf ct hv hk).2 hcw

/-- A block short of `k` held symbols is the `Incomplete` case: it is not fully held either (`k <= k + m`). -/
theorem short_block_not_full (k m : Nat) (pres : Nat → Bool)
    (hshort : ((List.range (k + m)).filter fun i => pres i).length < k) :
    ¬ ∀ i, i < k + m → pres i = true := by
  intro hall
  have : (List.range (k + m)).filter (fun i => pres i) = List.range (k + m) := by
    apply List.filter_eq_self.2
    intro i hi
    simpa using hall i (List.mem_range.1 hi)
  rw [this] at hshort
  simp at hshort
  omega

/-! ## Resume -/

/-- `Reception::resume`: the signature, then the lifetime, then the layout, then the buffer size; on success the
reception is the one passed in, with the same buffer and the same held set. -/
def resume (sigOk : Bool) (expired : Bool) (layoutOk : Bool) (sizeOk : Bool) (buf : Nat → V) (h : List Interval) :
    Except String ((Nat → V) × List Interval) :=
  if !sigOk then .error "crypto" else if expired then .error "expired" else if !layoutOk then .error "params"
  else if !sizeOk then .error "buffer" else .ok (buf, h)

theorem resume_spec (sigOk expired layoutOk sizeOk : Bool) (buf : Nat → V) (h : List Interval) :
    (∀ r, resume sigOk expired layoutOk sizeOk buf h = .ok r → r = (buf, h) ∧ sigOk = true ∧ expired = false ∧
      layoutOk = true ∧ sizeOk = true) ∧
    (sigOk = false → resume sigOk expired layoutOk sizeOk buf h = .error "crypto") ∧
    (sigOk = true → expired = true → resume sigOk expired layoutOk sizeOk buf h = .error "expired") ∧
    (sigOk = true → expired = false → layoutOk = true → sizeOk = false →
      resume sigOk expired layoutOk sizeOk buf h = .error "buffer") := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    unfold resume at hr
    cases sigOk <;> cases expired <;> cases layoutOk <;> cases sizeOk <;> simp at hr ⊢ <;> simp [hr]
  · intro h1; simp [resume, h1]
  · intro h1 h2; simp [resume, h1, h2]
  · intro h1 h2 h3 h4; simp [resume, h1, h2, h3, h4]

/-- A concrete witness of the one place the contract is weaker than "held bytes are the verified bytes": the code of one
data symbol and two repetition parity symbols, the sender's second parity symbol is wrong (7, not 1), the receiver holds
only the two parity symbols; `finish` solves the data symbol from the first present parity row and re-encodes, so the
held, verified parity symbol 2 is overwritten with 1. Only a sender whose parity is not a code word reaches this. -/
def rep3 (buf : Nat → Nat) (pres : Nat → Bool) : Nat → Nat :=
  let d0 := if pres 0 then buf 0 else if pres 1 then buf 1 else buf 2
  fun _ => d0

theorem overwrite_example :
    let ct : Nat → Nat := fun i => if i = 2 then 7 else 1
    let pres : Nat → Bool := fun i => decide (i ≠ 0)
    pres 2 = true ∧ ct 2 = 7 ∧ rep3 ct pres 2 = 1 := by decide

#print axioms feedGo_buf
#print axioms feedGo_mono
#print axioms feedGo_verified
#print axioms feed_ok_holds
#print axioms block_consistent_iff
#print axioms resume_spec

end Vinc.DtnReception
