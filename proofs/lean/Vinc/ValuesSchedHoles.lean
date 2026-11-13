import Vinc.Axioms
import Vinc.ValuesSchedList

/-!
# `holes`, `align`, `extend`, `retain_missing`, `split`

`holes` of `span.rs` against the contract of `ValueStore::verified_from` (the first verified interval that ends after
`from`), `retain_missing` / `missing` / `extend` as folds of `push`, `align`, and `RangeList::split`.

`holes_spec`: the pieces `holes` emits are exactly the unverified bytes of the span, in increasing order, each
non-empty and inside the span, no byte twice. `retainMissing_cov` and `extend_cov`: they never lose an unverified byte
(also when a push widens). `align_spec`: the span rounded out to whole groups and clamped to the value.
The contract of `split` is in `ValuesSchedSplit` and `ValuesSchedSplitOnce` (`split_cov`, `split_aligned`, `split_once`,
`split_order`): the shares are contiguous pieces of the list in order, cover it exactly and, for lists of whole groups,
every cut is at a group boundary.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Vinc.ValuesSched

/-- What the fetch assumes of `ValueStore::verified_from`: `vf c` is the first verified interval that ends after
`c` (it may start before `c`), and `V` is the verified set. -/
structure Store where
  V : Nat → Bool
  vf : Nat → Option (Nat × Nat)
  none_ok : ∀ c, vf c = none → ∀ x, c ≤ x → ¬ V x
  some_ok : ∀ c a b, vf c = some (a, b) →
    c < b ∧ a < b ∧ (∀ x, a ≤ x → x < b → V x) ∧ (∀ x, c ≤ x → x < a → ¬ V x)

/-- `holes`: the unverified parts of `[cur, e)`, in order. -/
def holes (st : Store) (e cur : Nat) : List Span :=
  if h : cur < e then
    match hv : st.vf cur with
    | none => [⟨cur, e - cur⟩]
    | some (a, b) =>
      if a ≤ cur then holes st e b
      else if a < e then ⟨cur, a - cur⟩ :: holes st e b
      else [⟨cur, e - cur⟩]
  else []
termination_by e - cur
decreasing_by all_goals (have := (st.some_ok cur a b hv).1; omega)

/-- `holes` of a span. -/
def holesOf (st : Store) (s : Span) : List Span := holes st (s.off + s.len) s.off

theorem holes_spec (st : Store) (e : Nat) : ∀ k cur, e - cur = k →
    (∀ x, mult (holes st e cur) x = if cur ≤ x ∧ x < e ∧ ¬ st.V x then 1 else 0) ∧
    Sorted (holes st e cur) ∧
    (∀ p ∈ holes st e cur, 0 < p.len ∧ cur ≤ p.off ∧ p.off + p.len ≤ e) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro cur hk
    by_cases hc : cur < e
    · rw [holes, dif_pos hc]
      split
      · rename_i hv
        refine ⟨fun x => ?_, ?_, ?_⟩
        · simp only [mult]
          by_cases hxr : cur ≤ x ∧ x < e
          · have hnv := st.none_ok cur hv x hxr.1
            rw [if_pos (show Span.Mem ⟨cur, e - cur⟩ x by simp only [Span.Mem]; omega),
              if_pos (⟨hxr.1, hxr.2, hnv⟩ : cur ≤ x ∧ x < e ∧ ¬ st.V x = true)]
          · rw [if_neg (show ¬ Span.Mem ⟨cur, e - cur⟩ x by simp only [Span.Mem]; omega), if_neg (fun h => hxr ⟨h.1, h.2.1⟩)]
        · simp [Sorted]
        · intro p hp; simp at hp; subst hp; simp; omega
      · rename_i a b hv
        obtain ⟨hcb, hab, hV, hN⟩ := st.some_ok cur a b hv
        by_cases h1 : a ≤ cur
        · rw [if_pos h1]
          obtain ⟨m, so, bd⟩ := ih (e - b) (by omega) b rfl
          refine ⟨fun x => ?_, so, fun p hp => ?_⟩
          · rw [m x]
            by_cases hxb : b ≤ x
            · by_cases hq : x < e ∧ ¬ st.V x = true
              · rw [if_pos ⟨hxb, hq.1, hq.2⟩, if_pos ⟨by omega, hq.1, hq.2⟩]
              · rw [if_neg (fun h => hq ⟨h.2.1, h.2.2⟩), if_neg (fun h => hq ⟨h.2.1, h.2.2⟩)]
            · rw [if_neg (fun h => hxb h.1)]
              by_cases hxc : cur ≤ x
              · have hvx := hV x (by omega) (by omega)
                rw [if_neg (fun h => h.2.2 hvx)]
              · rw [if_neg (fun h => hxc h.1)]
          · have := bd p hp; omega
        · rw [if_neg h1]
          by_cases h2 : a < e
          · rw [if_pos h2]
            obtain ⟨m, so, bd⟩ := ih (e - b) (by omega) b rfl
            refine ⟨fun x => ?_, ?_, fun p hp => ?_⟩
            · rw [mult_cons, m x]
              by_cases hxa : cur ≤ x ∧ x < a
              · have hn := hN x hxa.1 hxa.2
                rw [if_pos (show Span.Mem ⟨cur, a - cur⟩ x by simp only [Span.Mem]; omega)]
                rw [if_neg (fun h => by have := h.1; omega : ¬ (b ≤ x ∧ x < e ∧ ¬ st.V x = true))]
                rw [if_pos (⟨hxa.1, by omega, hn⟩ : cur ≤ x ∧ x < e ∧ ¬ st.V x = true)]
              · rw [if_neg (show ¬ Span.Mem ⟨cur, a - cur⟩ x by simp only [Span.Mem]; omega)]
                by_cases hxb : b ≤ x
                · by_cases hq : x < e ∧ ¬ st.V x = true
                  · rw [if_pos ⟨hxb, hq.1, hq.2⟩, if_pos ⟨by omega, hq.1, hq.2⟩]
                  · rw [if_neg (fun h => hq ⟨h.2.1, h.2.2⟩), if_neg (fun h => hq ⟨h.2.1, h.2.2⟩)]
                · rw [if_neg (fun h => hxb h.1)]
                  by_cases hxa2 : a ≤ x
                  · have hvx := hV x hxa2 (by omega)
                    rw [if_neg (fun h => h.2.2 hvx)]
                  · rw [if_neg (fun h => by have := h.1; omega)]
            · refine List.pairwise_cons.2 ⟨fun y hy => ?_, so⟩
              have := (bd y hy).2.1; show cur + (a - cur) ≤ y.off; omega
            · rcases List.mem_cons.1 hp with rfl | hp
              · simp; omega
              · have := bd p hp; omega
          · rw [if_neg h2]
            refine ⟨fun x => ?_, by simp [Sorted], fun p hp => ?_⟩
            · simp only [mult]
              by_cases hxr : cur ≤ x ∧ x < e
              · have hnv := hN x hxr.1 (by omega)
                rw [if_pos (show Span.Mem ⟨cur, e - cur⟩ x by simp only [Span.Mem]; omega),
                  if_pos (⟨hxr.1, hxr.2, hnv⟩ : cur ≤ x ∧ x < e ∧ ¬ st.V x = true)]
              · rw [if_neg (show ¬ Span.Mem ⟨cur, e - cur⟩ x by simp only [Span.Mem]; omega), if_neg (fun h => hxr ⟨h.1, h.2.1⟩)]
            · simp at hp; subst hp; simp; omega
    · rw [holes, dif_neg hc]
      refine ⟨fun x => ?_, by simp [Sorted], by simp⟩
      rw [if_neg (fun h => by have := h.1; have := h.2.1; omega)]
      rfl

theorem holesOf_mult (st : Store) (s : Span) (x : Nat) :
    mult (holesOf st s) x = if s.Mem x ∧ ¬ st.V x then 1 else 0 := by
  have := (holes_spec st (s.off + s.len) _ s.off rfl).1 x
  unfold holesOf; rw [this]; simp only [Span.Mem]
  by_cases h : s.off ≤ x ∧ x < s.off + s.len <;> by_cases h2 : st.V x <;> simp [h, h2]

theorem holesOf_cov (st : Store) (s : Span) (x : Nat) : cov (holesOf st s) x ↔ s.Mem x ∧ ¬ st.V x := by
  rw [cov_iff_mult, holesOf_mult]; split <;> simp_all

theorem holesOf_sorted (st : Store) (s : Span) : Sorted (holesOf st s) :=
  (holes_spec st (s.off + s.len) _ s.off rfl).2.1

theorem holesOf_bounds (st : Store) (s : Span) : ∀ p ∈ holesOf st s, 0 < p.len ∧ s.off ≤ p.off ∧ p.off + p.len ≤ s.off + s.len :=
  (holes_spec st (s.off + s.len) _ s.off rfl).2.2

/-! ## `extend`, `retain_missing`, `missing` -/

/-- `RangeList::extend`: push every span of `o`. -/
def extend (n : Nat) (l o : List Span) : List Span := o.foldl (push n) l

theorem foldl_push_length {n : Nat} (hn : 0 < n) (ps : List Span) :
    ∀ {l : List Span}, l.length ≤ n → (ps.foldl (push n) l).length ≤ n := by
  induction ps with
  | nil => intro l hl; exact hl
  | cons p t ih => intro l hl; exact ih (push_length_le hn hl p)

/-- `extend` never loses a byte of either list. -/
theorem extend_cov {n : Nat} (hn : 0 < n) {l : List Span} (hl : l.length ≤ n) (o : List Span) (x : Nat) :
    cov l x ∨ cov o x → cov (extend n l o) x := by
  unfold extend
  induction o generalizing l with
  | nil => intro h; rcases h with h | h; exact h; exact absurd h (cov_nil x)
  | cons p t ih =>
    intro h
    simp only [List.foldl_cons]
    apply ih (push_length_le hn hl p)
    rcases h with h | h
    · exact Or.inl (push_cov hn hl p x (Or.inl h))
    · rw [cov_cons] at h
      rcases h with h | h
      · exact Or.inl (push_cov hn hl p x (Or.inr h))
      · exact Or.inr h

theorem extend_length_le {n : Nat} (hn : 0 < n) {l : List Span} (hl : l.length ≤ n) (o : List Span) :
    (extend n l o).length ≤ n := foldl_push_length hn o hl

theorem extend_bounded {n : Nat} {l o : List Span} (hl : Bounded l) (ho : Bounded o) : Bounded (extend n l o) := by
  unfold extend
  induction o generalizing l with
  | nil => exact hl
  | cons p t ih =>
    simp only [List.foldl_cons]
    exact ih (push_bounded hl p (ho p (by simp))) (fun s hs => ho s (by simp [hs]))

/-- Exact accounting of a run of pushes: if the list has room for all of them and they overlap neither the list nor each
other, the multiplicities add. -/
theorem foldl_push_mult {n : Nat} (ps : List Span) :
    ∀ {l : List Span}, l.length + ps.length ≤ n → (∀ x, mult l x + mult ps x ≤ 1) →
      ∀ x, mult (ps.foldl (push n) l) x = mult l x + mult ps x := by
  induction ps with
  | nil => intro l _ _ x; simp [mult]
  | cons p t ih =>
    intro l hroom hd x
    simp only [List.foldl_cons, List.length_cons] at *
    have hdp : ∀ y, p.Mem y → mult l y = 0 := by
      intro y hy
      have := hd y
      simp only [mult, hy, if_true] at this
      omega
    have hpm : ∀ y, mult (push n l p) y = mult l y + (if p.Mem y then 1 else 0) :=
      push_mult (by omega) p hdp
    have hlen := push_length_succ (n := n) l p
    rw [ih (by omega) (fun y => by rw [hpm y]; have := hd y; simp only [mult] at this; omega) x, hpm x]
    simp only [mult]; omega

/-- `retain_missing` / `missing`: the unverified parts of every span, pushed in order. -/
def retainMissing (st : Store) (n : Nat) (l : List Span) : List Span :=
  l.foldl (fun out s => (holesOf st s).foldl (push n) out) []

/-- The number of pieces `retain_missing` produces. -/
def pieces (st : Store) (l : List Span) : Nat := (l.map fun s => (holesOf st s).length).sum

theorem rm_aux_cov (st : Store) {n : Nat} (hn : 0 < n) (x : Nat) (hx : ¬ st.V x) (l : List Span) :
    ∀ {acc : List Span}, acc.length ≤ n → (cov acc x ∨ cov l x) →
      cov (l.foldl (fun out s => (holesOf st s).foldl (push n) out) acc) x := by
  induction l with
  | nil => intro acc _ h; rcases h with h | h; exact h; exact absurd h (cov_nil x)
  | cons s t ih =>
    intro acc hacc h
    simp only [List.foldl_cons]
    have hlen := foldl_push_length hn (holesOf st s) hacc
    apply ih hlen
    rcases h with h | h
    · left
      have := extend_cov hn hacc (holesOf st s) x (Or.inl h)
      exact this
    · rw [cov_cons] at h
      rcases h with h | h
      · left
        have hh : cov (holesOf st s) x := (holesOf_cov st s x).2 ⟨h, hx⟩
        exact extend_cov hn hacc (holesOf st s) x (Or.inr hh)
      · exact Or.inr h

/-- Resume and `retain_missing` never lose an unverified byte, also when a push widens. -/
theorem retainMissing_cov (st : Store) {n : Nat} (hn : 0 < n) (l : List Span) (x : Nat)
    (hx : ¬ st.V x) (h : cov l x) : cov (retainMissing st n l) x :=
  rm_aux_cov st hn x hx l (by simp) (Or.inr h)

theorem rm_aux_mult (st : Store) {n : Nat} (hn : 0 < n) (l : List Span) :
    ∀ {acc : List Span}, acc.length + pieces st l ≤ n →
      (∀ x, mult acc x + (if st.V x then 0 else mult l x) ≤ 1) →
      ∀ x, mult (l.foldl (fun out s => (holesOf st s).foldl (push n) out) acc) x =
        mult acc x + (if st.V x then 0 else mult l x) := by
  induction l with
  | nil => intro acc _ _ x; simp [mult]
  | cons s t ih =>
    intro acc hroom hd x
    simp only [List.foldl_cons, pieces, List.map_cons, List.sum_cons] at *
    have hdisj : ∀ y, mult acc y + mult (holesOf st s) y ≤ 1 := by
      intro y
      have := hd y
      rw [holesOf_mult]
      simp only [mult] at this
      by_cases hv : st.V y = true <;> by_cases hm : s.Mem y <;> simp [hv, hm] at this ⊢ <;> omega
    have hm1 := foldl_push_mult (n := n) (holesOf st s) (l := acc) (by omega) hdisj
    have hlen := foldl_push_length (n := n) hn (holesOf st s) (l := acc)
    have hlen2 : ((holesOf st s).foldl (push n) acc).length ≤ acc.length + (holesOf st s).length := by
      clear hm1 hlen hdisj hd hroom ih
      induction (holesOf st s) generalizing acc with
      | nil => simp
      | cons p q ihq =>
        simp only [List.foldl_cons, List.length_cons]
        have := push_length_succ (n := n) acc p
        have := @ihq (push n acc p)
        omega
    rw [ih (acc := (holesOf st s).foldl (push n) acc) (by omega) ?_ x, hm1 x, holesOf_mult]
    · simp only [mult]
      by_cases hv : st.V x = true <;> by_cases hm : s.Mem x <;> simp [hv, hm] <;> omega
    · intro y
      rw [hm1 y, holesOf_mult]
      have := hd y
      simp only [mult] at this
      by_cases hv : st.V y = true <;> by_cases hm : s.Mem y <;> simp [hv, hm] at this ⊢ <;> omega

/-- Without widening (room for every hole piece, no overlap in the list) `retain_missing` keeps exactly the
unverified bytes, each once. -/
theorem retainMissing_mult (st : Store) {n : Nat} (hn : 0 < n) (l : List Span) (hroom : pieces st l ≤ n)
    (hd : ∀ x, mult l x ≤ 1) (x : Nat) :
    mult (retainMissing st n l) x = if st.V x then 0 else mult l x := by
  have := rm_aux_mult (n := n) st hn l (acc := []) (by simpa using hroom)
    (fun y => by simp [mult]; have := hd y; split <;> omega) x
  simpa [retainMissing, mult] using this

/-! ## `align` -/

/-- `align`: round a non-empty span out to whole groups, clamped to a value of `total` bytes. `u64::div_ceil` is
`(x + G - 1) / G`; the `saturating_mul` is `min _ M`. -/
def align (s : Span) (total : Nat) : Option Span :=
  let a := s.off / G * G
  let b := min (min ((s.off + s.len + G - 1) / G * G) M) total
  if s.len > 0 ∧ b > a then some ⟨a, b - a⟩ else none

theorem align_empty (s : Span) (total : Nat) (h : s.len = 0) : align s total = none := by
  simp [align, h]

/-- A span inside the value, however near `u64::MAX`, aligns to the whole groups around it: starts and ends on a
group boundary (the end of the value excepted), covers the span, and is the tightest such. -/
theorem align_spec (s : Span) (total : Nat) (htot : total ≤ M) (hin : s.off + s.len ≤ total) (hlen : 0 < s.len) :
    ∃ a, align s total = some a ∧ a.off % G = 0 ∧ a.off ≤ s.off ∧ s.off < a.off + G ∧
      s.off + s.len ≤ a.off + a.len ∧ a.off + a.len ≤ total ∧
      ((a.off + a.len) % G = 0 ∨ a.off + a.len = total) := by
  have hc : s.len > 0 ∧ min (min ((s.off + s.len + G - 1) / G * G) M) total > s.off / G * G := by
    simp only [G, M] at *; omega
  unfold align
  rw [if_pos hc]
  refine ⟨_, rfl, ?_⟩
  simp only [G, M] at *
  omega

end Vinc.ValuesSched

#audit_axioms Vinc.ValuesSched.holes_spec
#audit_axioms Vinc.ValuesSched.holesOf_cov
#audit_axioms Vinc.ValuesSched.holesOf_mult
#audit_axioms Vinc.ValuesSched.holesOf_sorted
#audit_axioms Vinc.ValuesSched.holesOf_bounds
#audit_axioms Vinc.ValuesSched.extend_cov
#audit_axioms Vinc.ValuesSched.extend_length_le
#audit_axioms Vinc.ValuesSched.extend_bounded
#audit_axioms Vinc.ValuesSched.foldl_push_mult
#audit_axioms Vinc.ValuesSched.retainMissing_cov
#audit_axioms Vinc.ValuesSched.retainMissing_mult
#audit_axioms Vinc.ValuesSched.align_empty
#audit_axioms Vinc.ValuesSched.align_spec
