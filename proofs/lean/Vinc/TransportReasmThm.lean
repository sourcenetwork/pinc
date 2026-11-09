import Vinc.Axioms
import Vinc.TransportRxThm
import Vinc.TransportReasm

/-!
# Handshake fragments: reassembly is exact and bounded

What the model proves about `Reassembly`, over unbounded messages and any run of fragments:

- the runs stay sorted, disjoint, non-adjacent and non-empty, inside `[0, total)`, at most `nr` of them, and the
  message length stays within `mx` (`Inv`, `add_inv`);
- reassembly is exact: a fragment that is kept makes the runs cover exactly what they covered plus the fragment
  (cut at the end of the message); a fragment that finds no free run changes nothing; a fragment of a message of
  another length starts from nothing (`add_cover`);
- a message is handed over only when every byte `0 .. total - 1` is covered, and then the reassembly is fresh
  (`add_complete`).
-/

namespace Vinc.TransportReasm
open Vinc.TransportRx (WF Cov wf_append wf_cons cov_append cov_cons cov_nil)

theorem insertRun_mem (iv v : Iv) : ∀ (l : List Iv), v ∈ insertRun l iv ↔ v = iv ∨ v ∈ l
  | [] => by simp [insertRun]
  | x :: t => by
    unfold insertRun
    split
    · simp [insertRun_mem iv v t]; tauto
    · simp

theorem insertRun_length (iv : Iv) : ∀ (l : List Iv), (insertRun l iv).length = l.length + 1
  | [] => by simp [insertRun]
  | x :: t => by
    unfold insertRun
    split
    · simp [insertRun_length iv t]
    · simp

theorem insertRun_cov (iv : Iv) : ∀ (l : List Iv) (n : Nat), Cov (insertRun l iv) n ↔ Cov l n ∨ (iv.1 ≤ n ∧ n < iv.2)
  | [], n => by
    simp [insertRun]
    constructor
    · rintro ⟨u, h, hn⟩; simp at h; subst h; exact Or.inr hn
    · rintro (h | h); exact absurd h cov_nil; exact ⟨iv, by simp, h⟩
  | x :: t, n => by
    unfold insertRun
    split
    · rw [cov_cons, cov_cons, insertRun_cov iv t n]
      constructor
      · rintro (h | h | h) <;> tauto
      · rintro ((h | h) | h) <;> tauto
    · rw [cov_cons, cov_cons]
      constructor
      · rintro (h | h | h) <;> tauto
      · rintro ((h | h) | h) <;> tauto

theorem insertRun_wf (iv : Iv) (hiv : iv.1 < iv.2) : ∀ (l : List Iv), WF l → (∀ k ∈ l, k.2 < iv.1 ∨ iv.2 < k.1) →
    WF (insertRun l iv)
  | [], _, _ => by
    simp only [insertRun]
    exact Vinc.TransportRx.wf_single iv hiv
  | x :: t, hw, hs => by
    obtain ⟨hx, hwt, hxt⟩ := wf_cons.1 hw
    have hxs := hs x (by simp)
    unfold insertRun
    split
    · rename_i hlt
      have hxb : x.2 < iv.1 := by omega
      refine wf_cons.2 ⟨hx, insertRun_wf iv hiv t hwt (fun k hk => hs k (List.mem_cons_of_mem _ hk)), ?_⟩
      intro v hv
      rcases (insertRun_mem iv v t).1 hv with rfl | hv
      · exact hxb
      · exact hxt v hv
    · rename_i hge
      have hxa : iv.2 < x.1 := by omega
      refine wf_cons.2 ⟨hiv, wf_cons.2 ⟨hx, hwt, hxt⟩, ?_⟩
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hxa
      · have := hxt v hv; omega

theorem cov_single (iv : Iv) (n : Nat) : Cov [iv] n ↔ iv.1 ≤ n ∧ n < iv.2 := by
  rw [show [iv] = iv :: [] from rfl, cov_cons]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h cov_nil
  · exact fun h => Or.inl h

/-- The merge: what it keeps stays apart from the run it builds, in order, and the coverage is the union. -/
theorem mergeRuns_spec (rs : List Iv) : ∀ (keep : List Iv) (lo hi : Nat) (keep' : List Iv) (lo' hi' : Nat),
    lo < hi → WF rs → (∀ k ∈ keep, k.1 < k.2 ∧ (k.2 < lo ∨ hi < k.1)) → (∀ k ∈ keep, ∀ r ∈ rs, k.2 < r.1) →
    keep.Pairwise (fun a b => a.2 < b.1) → mergeRuns rs lo hi keep = (keep', lo', hi') →
    lo' ≤ lo ∧ hi ≤ hi' ∧ lo' < hi' ∧ keep'.Pairwise (fun a b => a.2 < b.1) ∧
      (∀ k ∈ keep', k.1 < k.2 ∧ (k.2 < lo' ∨ hi' < k.1)) ∧
      (∀ n, (Cov keep' n ∨ (lo' ≤ n ∧ n < hi')) ↔ (Cov keep n ∨ Cov rs n ∨ (lo ≤ n ∧ n < hi))) ∧
      keep'.length ≤ keep.length + rs.length ∧ (∀ k ∈ keep', k ∈ keep ∨ k ∈ rs) ∧
      (∀ B, hi ≤ B → (∀ r ∈ rs, r.2 ≤ B) → hi' ≤ B) := by
  induction rs with
  | nil =>
    intro keep lo hi keep' lo' hi' h1 _ h3 _ h5 h
    simp only [mergeRuns, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨Nat.le_refl _, Nat.le_refl _, h1, h5, h3, fun n => ?_, by simp, fun k hk => Or.inl hk, fun B hB _ => hB⟩
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl h
      · exact absurd h cov_nil
      · exact Or.inr h
  | cons x t ih =>
    obtain ⟨s, e⟩ := x
    intro keep lo hi keep' lo' hi' h1 hw h3 h4 h5 h
    obtain ⟨hse, hwt, hxt⟩ := wf_cons.1 hw
    simp only at hse hxt
    have hks : ∀ k ∈ keep, k.2 < s := fun k hk => h4 k hk (s, e) (by simp)
    unfold mergeRuns at h
    by_cases hk : e < lo ∨ hi < s
    · rw [if_pos hk] at h
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := ih (keep ++ [(s, e)]) lo hi keep' lo' hi' h1 hwt
        (fun k hk' => by
          rcases List.mem_append.1 hk' with h | h
          · exact h3 k h
          · simp at h; subst h; exact ⟨hse, by omega⟩)
        (fun k hk' r hr => by
          rcases List.mem_append.1 hk' with h | h
          · exact h4 k h r (List.mem_cons_of_mem _ hr)
          · simp at h; subst h; exact hxt r hr)
        (by
          rw [List.pairwise_append]
          refine ⟨h5, List.pairwise_singleton _ _, ?_⟩
          intro a ha b hb; simp at hb; subst hb; exact hks a ha) h
      refine ⟨c1, c2, c3, c4, c5, fun n => ?_, ?_, fun k hk' => ?_,
        fun B hB hr => c9 B hB (fun r hr' => hr r (List.mem_cons_of_mem _ hr'))⟩
      · have := c6 n
        simp only [cov_append, cov_single, cov_cons] at this ⊢
        grind
      · simp at c7 ⊢; omega
      · rcases c8 k hk' with h | h
        · rcases List.mem_append.1 h with h | h
          · exact Or.inl h
          · simp at h; subst h; exact Or.inr (by simp)
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · rw [if_neg hk] at h
      have hk2 : lo ≤ e ∧ s ≤ hi := by omega
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := ih keep (min lo s) (max hi e) keep' lo' hi' (by omega) hwt
        (fun k hk' => by
          obtain ⟨a, b⟩ := h3 k hk'
          refine ⟨a, ?_⟩
          rcases b with b | b
          · left; have := hks k hk'; omega
          · exfalso; have := hks k hk'; omega)
        (fun k hk' r hr => h4 k hk' r (List.mem_cons_of_mem _ hr)) h5 h
      refine ⟨by omega, by omega, c3, c4, c5, fun n => ?_, by simp at c7 ⊢; omega, fun k hk' => ?_,
        fun B hB hr => c9 B (by have := hr (s, e) (by simp); simp only at this; omega)
          (fun r hr' => hr r (List.mem_cons_of_mem _ hr'))⟩
      · have := c6 n
        have heq : (min lo s ≤ n ∧ n < max hi e) ↔ ((lo ≤ n ∧ n < hi) ∨ (s ≤ n ∧ n < e)) := by omega
        rw [heq] at this
        simp only [cov_cons] at this ⊢
        grind
      · rcases c8 k hk' with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The shape every reassembly keeps. -/
def Inv (mx nr : Nat) (r : R) : Prop :=
  WF r.runs ∧ r.runs.length ≤ nr ∧ (∀ iv ∈ r.runs, iv.2 ≤ r.total) ∧ r.total ≤ mx

theorem inv_empty (mx nr : Nat) : Inv mx nr {} :=
  ⟨⟨fun iv h => by simp [R.runs] at h, List.Pairwise.nil⟩, by simp, fun iv h => by simp at h, Nat.zero_le _⟩

/-- A fragment outside the lengths a message may have changes nothing. -/
theorem add_refused (r : R) (mx nr total off dlen : Nat) (h : total = 0 ∨ mx < total) :
    add r mx nr total off dlen = (none, r) := by
  unfold add; simp [h]

/-- What `add` does, in the case it does something: the state after the length check (a message of another length
starts from nothing), the run the fragment makes, and the merge. -/
theorem add_inv (r : R) (mx nr total off dlen : Nat) (hr : Inv mx nr r) :
    ∀ out r', add r mx nr total off dlen = (out, r') → Inv mx nr r' := by
  intro out r' h
  unfold add at h
  by_cases h0 : total = 0 ∨ mx < total
  · rw [if_pos h0] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hr
  · rw [if_neg h0] at h
    have h0' : 0 < total ∧ total ≤ mx := by omega
    have hr1 : Inv mx nr (if total ≠ r.total then ({ runs := [], total } : R) else r) := by
      split
      · exact ⟨⟨fun iv h => by simp at h, List.Pairwise.nil⟩, by simp, fun iv h => by simp at h, h0'.2⟩
      · exact hr
    generalize hr1def : (if total ≠ r.total then ({ runs := [], total } : R) else r) = r1 at hr1 h
    by_cases h1 : min (off + dlen) total ≤ off
    · rw [if_pos h1] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact hr1
    · rw [if_neg h1] at h
      obtain ⟨hw1, hl1, hb1, ht1⟩ := hr1
      generalize hm : mergeRuns r1.runs off (min (off + dlen) total) [] = m at h
      obtain ⟨keep', lo', hi'⟩ := m
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := mergeRuns_spec r1.runs [] off (min (off + dlen) total) keep' lo' hi'
        (by omega) hw1 (fun k hk => by simp at hk) (fun k hk => by simp at hk) List.Pairwise.nil hm
      simp only at h
      by_cases h2 : keep'.length = nr
      · rw [if_pos h2] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨hw1, hl1, hb1, ht1⟩
      · rw [if_neg h2] at h
        have hlen : keep'.length < nr := by simp at c7; omega
        by_cases h3 : (insertRun keep' (lo', hi')).length = 1 ∧ lo' = 0 ∧ hi' = total
        · rw [if_pos h3] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact inv_empty mx nr
        · rw [if_neg h3] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          have hwf : WF (insertRun keep' (lo', hi')) := by
            refine insertRun_wf (lo', hi') c3 keep' ⟨fun k hk => (c5 k hk).1, c4⟩ (fun k hk => ?_)
            exact (c5 k hk).2
          refine ⟨hwf, by rw [insertRun_length]; omega, fun iv hiv => ?_, ht1⟩
          rcases (insertRun_mem (lo', hi') iv keep').1 hiv with rfl | hiv
          · exact c9 r1.total (by omega) hb1
          · rcases c8 iv hiv with h | h
            · simp at h
            · exact hb1 iv h

/-- Reassembly is exact. A fragment the reassembly keeps adds exactly its bytes (cut at the end of the message) to
what the runs cover; one that finds no free run changes no run; a fragment of a message of another length starts
from nothing. -/
theorem add_cover (r : R) (mx nr total off dlen : Nat) (hr : Inv mx nr r) (h0 : ¬ (total = 0 ∨ mx < total))
    (h1 : ¬ (min (off + dlen) total ≤ off)) :
    let r1 : R := if total ≠ r.total then { runs := [], total } else r
    ∀ r', add r mx nr total off dlen = (none, r') →
      (r'.runs = r1.runs ∧ r'.total = r1.total) ∨
      (∀ n, Cov r'.runs n ↔ (Cov r1.runs n ∨ (off ≤ n ∧ n < min (off + dlen) total))) := by
  intro r1 r' h
  unfold add at h
  rw [if_neg h0] at h
  simp only [r1] at h ⊢
  have hr1 : Inv mx nr (if total ≠ r.total then ({ runs := [], total } : R) else r) := by
    have h0' : 0 < total ∧ total ≤ mx := by omega
    split
    · exact ⟨⟨fun iv h => by simp at h, List.Pairwise.nil⟩, by simp, fun iv h => by simp at h, h0'.2⟩
    · exact hr
  generalize (if total ≠ r.total then ({ runs := [], total } : R) else r) = r2 at hr1 h ⊢
  rw [if_neg h1] at h
  obtain ⟨hw1, hl1, hb1, ht1⟩ := hr1
  generalize hm : mergeRuns r2.runs off (min (off + dlen) total) [] = m at h
  obtain ⟨keep', lo', hi'⟩ := m
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := mergeRuns_spec r2.runs [] off (min (off + dlen) total) keep' lo' hi'
    (by omega) hw1 (fun k hk => by simp at hk) (fun k hk => by simp at hk) List.Pairwise.nil hm
  simp only at h
  by_cases h2 : keep'.length = nr
  · rw [if_pos h2] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · rw [if_neg h2] at h
    by_cases h3 : (insertRun keep' (lo', hi')).length = 1 ∧ lo' = 0 ∧ hi' = total
    · rw [if_pos h3] at h
      simp at h
    · rw [if_neg h3] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine Or.inr (fun n => ?_)
      rw [insertRun_cov]
      have := c6 n
      simp only [Vinc.TransportRx.cov_nil, false_or] at this
      simpa using this

/-- A message is handed over only when its every byte is covered, and then the reassembly is fresh. -/
theorem add_complete (r : R) (mx nr total off dlen t : Nat) (hr : Inv mx nr r) (h0 : ¬ (total = 0 ∨ mx < total))
    (r' : R) (h : add r mx nr total off dlen = (some t, r')) :
    t = total ∧ r' = {} ∧
      ∀ n, n < total → (Cov (if total ≠ r.total then ({ runs := [], total } : R) else r).runs n ∨
        (off ≤ n ∧ n < min (off + dlen) total)) := by
  unfold add at h
  rw [if_neg h0] at h
  have hr1 : Inv mx nr (if total ≠ r.total then ({ runs := [], total } : R) else r) := by
    have h0' : 0 < total ∧ total ≤ mx := by omega
    split
    · exact ⟨⟨fun iv h => by simp at h, List.Pairwise.nil⟩, by simp, fun iv h => by simp at h, h0'.2⟩
    · exact hr
  generalize (if total ≠ r.total then ({ runs := [], total } : R) else r) = r2 at hr1 h ⊢
  by_cases h1 : min (off + dlen) total ≤ off
  · rw [if_pos h1] at h; simp at h
  · rw [if_neg h1] at h
    obtain ⟨hw1, hl1, hb1, ht1⟩ := hr1
    generalize hm : mergeRuns r2.runs off (min (off + dlen) total) [] = m at h
    obtain ⟨keep', lo', hi'⟩ := m
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := mergeRuns_spec r2.runs [] off (min (off + dlen) total) keep' lo' hi'
      (by omega) hw1 (fun k hk => by simp at hk) (fun k hk => by simp at hk) List.Pairwise.nil hm
    simp only at h
    by_cases h2 : keep'.length = nr
    · rw [if_pos h2] at h; simp at h
    · rw [if_neg h2] at h
      by_cases h3 : (insertRun keep' (lo', hi')).length = 1 ∧ lo' = 0 ∧ hi' = total
      · rw [if_pos h3] at h
        simp only [Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, rfl, fun n hn => ?_⟩
        have hk : keep' = [] := by
          have := insertRun_length (lo', hi') keep'
          cases keep' with
          | nil => rfl
          | cons x y => simp at this h3; omega
        subst hk
        have := (c6 n).1 (Or.inr ⟨by omega, by rw [h3.2.2]; omega⟩)
        simp only [Vinc.TransportRx.cov_nil, false_or] at this
        exact this
      · rw [if_neg h3] at h; simp at h

end Vinc.TransportReasm
