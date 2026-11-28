import Pinc.TransportReasmThm

/-!
# Handshake fragments: a complete set of fragments is handed over

`Pinc.TransportReasmThm.add_complete` proves that a message is handed over only when every byte is covered. This
file proves the converse, which `Reasm.tla` and the trace check only on the runs they explore:

- `add_hands_over`: when the fragments kept so far together with the one that arrives cover every byte of the
  message, `add` hands the message over and the reassembly is fresh, whatever the order and overlap of the
  fragments (for a reassembly with at least one run);
- `add_inc`: a reassembly under way always lacks a byte (`Inc`), so the hypothesis of `add_hands_over` on the
  state is an invariant and not an assumption: a message that was complete has been handed over.

Together with `add_complete`: `add` returns the message exactly at the fragment that completes it.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Pinc.TransportReasm
open Pinc.TransportRx (WF Cov cov_nil)

/-- A reassembly under way lacks a byte of its message (or holds no message). -/
def Inc (r : R) : Prop := r.total = 0 ∨ ∃ n, n < r.total ∧ ¬ Cov r.runs n

theorem inc_empty : Inc {} := Or.inl rfl

/-- In runs kept apart, the end of a run is inside no run. -/
theorem end_apart : ∀ {l : List Iv}, l.Pairwise (fun a b => a.2 < b.1) → (∀ k ∈ l, k.1 < k.2) →
    ∀ k ∈ l, ∀ k2 ∈ l, k2.1 ≤ k.2 → k.2 < k2.2 → False := by
  intro l
  induction l with
  | nil => intro _ _ k hk; cases hk
  | cons a t ih =>
    intro hp hne k hk k2 hk2 h1 h2
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hp
    rcases List.mem_cons.1 hk with rfl | hk'
    · rcases List.mem_cons.1 hk2 with rfl | hk2'
      · omega
      · have := hhead k2 hk2'; omega
    · rcases List.mem_cons.1 hk2 with rfl | hk2'
      · have := hhead k hk'
        have := hne k hk
        omega
      · exact ih htail (fun x hx => hne x (List.mem_cons_of_mem _ hx)) k hk' k2 hk2' h1 h2

/-- The state `add` works on after the length check lacks a byte. -/
theorem inc_start {r : R} {total : Nat} (h0 : 0 < total) (hinc : Inc r) :
    (if total ≠ r.total then ({ runs := [], total } : R) else r).total = total ∧
    ∃ n, n < total ∧ ¬ Cov (if total ≠ r.total then ({ runs := [], total } : R) else r).runs n := by
  by_cases ht : total ≠ r.total
  · rw [if_pos ht]; exact ⟨rfl, 0, h0, cov_nil⟩
  · rw [if_neg ht]
    have ht' : total = r.total := by omega
    refine ⟨ht'.symm, ?_⟩
    rcases hinc with h | ⟨n, hn, hc⟩
    · omega
    · exact ⟨n, by omega, hc⟩

/-- A complete set of fragments is handed over: when what the reassembly holds and the fragment that arrives cover
every byte of the message, and the fragment is not of another length while runs are held, `add` returns the
message and starts afresh. -/
theorem add_hands_over (r : R) (mx nr total off dlen : Nat) (hnr : 0 < nr) (hr : Inv mx nr r)
    (h0 : ¬ (total = 0 ∨ mx < total)) (hk : ¬ (total ≠ r.total ∧ r.runs ≠ [])) (hinc : Inc r)
    (hall : ∀ n, n < total → (Cov (if total ≠ r.total then ({ runs := [], total } : R) else r).runs n ∨
      (off ≤ n ∧ n < min (off + dlen) total))) :
    add r mx nr total off dlen = (some total, {}) := by
  have h0' : 0 < total ∧ total ≤ mx := by omega
  unfold add
  rw [if_neg h0, if_neg hk]
  have hr1 : Inv mx nr (if total ≠ r.total then ({ runs := [], total } : R) else r) := by
    split
    · exact ⟨⟨fun iv h => by simp at h, List.Pairwise.nil⟩, by simp, fun iv h => by simp at h, h0'.2⟩
    · exact hr
  obtain ⟨hr1t, n0, hn0, hc0⟩ := inc_start h0'.1 hinc
  generalize (if total ≠ r.total then ({ runs := [], total } : R) else r) = r2 at hr1 hr1t hc0 hall ⊢
  have h1 : ¬ (min (off + dlen) total ≤ off) := by
    intro h1
    rcases hall n0 hn0 with h | h
    · exact hc0 h
    · omega
  dsimp only
  rw [if_neg h1]
  obtain ⟨hw1, hl1, hb1, ht1⟩ := hr1
  generalize hm : mergeRuns r2.runs off (min (off + dlen) total) [] = m
  obtain ⟨keep', lo', hi'⟩ := m
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := mergeRuns_spec r2.runs [] off (min (off + dlen) total) keep' lo' hi'
    (by omega) hw1 (fun k hk => by simp at hk) (fun k hk => by simp at hk) List.Pairwise.nil hm
  have hhi : hi' ≤ total := c9 total (Nat.min_le_right _ _) (fun x hx => by have := hb1 x hx; omega)
  have hcl : ∀ n, n < total → Cov keep' n ∨ (lo' ≤ n ∧ n < hi') := by
    intro n hn
    refine (c6 n).2 ?_
    rcases hall n hn with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hk : keep' = [] := by
    cases hkeep : keep' with
    | nil => rfl
    | cons k ks =>
      exfalso
      have hkm : k ∈ keep' := by rw [hkeep]; exact List.mem_cons_self
      obtain ⟨hk1, hk2⟩ := c5 k hkm
      have hkt : k.2 ≤ total := by
        rcases c8 k hkm with h | h
        · simp at h
        · have := hb1 k h; omega
      rcases hk2 with hk2 | hk2
      · rcases hcl k.2 (by omega) with ⟨k2, hk2m, ha, hb⟩ | h
        · exact end_apart c4 (fun x hx => (c5 x hx).1) k hkm k2 hk2m ha hb
        · omega
      · rcases hcl hi' (by omega) with ⟨k2, hk2m, ha, hb⟩ | h
        · have := (c5 k2 hk2m).2; omega
        · omega
  subst hk
  have hlo : lo' = 0 := by
    rcases hcl 0 h0'.1 with h | h
    · exact absurd h cov_nil
    · omega
  have hhi' : hi' = total := by
    rcases hcl (total - 1) (by omega) with h | h
    · exact absurd h cov_nil
    · omega
  dsimp only
  rw [if_neg (by simp; omega), if_pos ⟨by simp [insertRun], hlo, hhi'⟩]

/-- A fragment that hands nothing over, and is not of another length while runs are held, leaves a reassembly of the
message's length. -/
theorem add_none_total (r : R) (mx nr total off dlen : Nat) (h0 : ¬ (total = 0 ∨ mx < total))
    (hk : ¬ (total ≠ r.total ∧ r.runs ≠ [])) (r' : R)
    (h : add r mx nr total off dlen = (none, r')) : r'.total = total := by
  unfold add at h
  rw [if_neg h0, if_neg hk] at h
  have ht : (if total ≠ r.total then ({ runs := [], total } : R) else r).total = total := by
    split
    · rfl
    · rename_i hh; omega
  generalize (if total ≠ r.total then ({ runs := [], total } : R) else r) = r2 at h ht
  dsimp only at h
  split at h
  · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ht
  · split at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ht
    · split at h
      · simp at h
      · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ht

/-- A reassembly under way lacks a byte, after every fragment. -/
theorem add_inc (r : R) (mx nr total off dlen : Nat) (hnr : 0 < nr) (hr : Inv mx nr r) (hinc : Inc r) :
    ∀ out r', add r mx nr total off dlen = (out, r') → Inc r' := by
  intro out r' h
  by_cases h0 : total = 0 ∨ mx < total
  · rw [add_refused r mx nr total off dlen h0] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hinc
  · have h0' : 0 < total := by omega
    by_cases hk : total ≠ r.total ∧ r.runs ≠ []
    · unfold add at h
      rw [if_neg h0, if_pos hk] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact hinc
    cases out with
    | some t =>
      obtain ⟨_, rfl, _⟩ := add_complete r mx nr total off dlen t hr h0 r' h
      exact inc_empty
    | none =>
      have ht := add_none_total r mx nr total off dlen h0 hk r' h
      refine Classical.byContradiction fun hni => ?_
      have hfull : ∀ n, n < total → Cov r'.runs n := by
        intro n hn
        refine Classical.byContradiction fun hcov => ?_
        exact hni (Or.inr ⟨n, by rw [ht]; exact hn, hcov⟩)
      obtain ⟨hr1t, n0, hn0, hc0⟩ := inc_start h0' hinc
      by_cases h1 : min (off + dlen) total ≤ off
      · -- an empty fragment changes nothing
        have he : r' = (if total ≠ r.total then ({ runs := [], total } : R) else r) := by
          unfold add at h
          rw [if_neg h0, if_neg hk] at h
          dsimp only at h
          rw [if_pos h1] at h
          simp only [Prod.mk.injEq] at h
          exact h.2.symm
        rw [he] at hfull
        exact hc0 (hfull n0 hn0)
      · rcases add_cover r mx nr total off dlen hr h0 h1 r' h with ⟨hruns, _⟩ | hcov | hc
        · rw [hruns] at hfull
          exact hc0 (hfull n0 hn0)
        · have := add_hands_over r mx nr total off dlen hnr hr h0 hk hinc (fun n hn => (hcov n).1 (hfull n hn))
          rw [this] at h
          simp at h
        · exact absurd ⟨hc.1, hc.2.1⟩ hk

#audit_axioms Pinc.TransportReasm.add_hands_over
#audit_axioms Pinc.TransportReasm.add_inc

end Pinc.TransportReasm
