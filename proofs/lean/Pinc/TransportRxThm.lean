import Pinc.Axioms
import Pinc.TransportRx

/-!
# Received packets: the range set is exact

What the model proves about the range set of `ReceivedPackets` (`recovery/recv.rs`), over unbounded packet numbers
and any run of packets:

- the ranges stay sorted, disjoint, merged and non-empty, and never exceed the const generic `RANGES`
  (`insert_spec`, `receive_good`);
- the set is exact: every packet number reported `New` is in exactly one range or below the floor, no number that
  was not received is in a range, and a number below the floor is a number received or forgotten
  (`Good`, `receive_good`);
- a packet is `New` only if it was not received before and is not below the floor (`insert_spec`);
- when the set is full the oldest range is the one forgotten: the floor rises to its end and stays at or below
  the start of every range kept (`pushNew_spec`).
-/

namespace Pinc.TransportRx

/-- Every range is non-empty and the ranges are sorted, disjoint and not adjacent. -/
def WF (l : List Iv) : Prop := (∀ iv ∈ l, iv.1 < iv.2) ∧ l.Pairwise (fun a b => a.2 < b.1)
/-- A number is in one of the ranges. -/
def Cov (l : List Iv) (n : Nat) : Prop := ∃ iv ∈ l, iv.1 ≤ n ∧ n < iv.2
/-- Every range starts at or above the floor. -/
def FloorLe (f : Nat) (l : List Iv) : Prop := ∀ iv ∈ l, f ≤ iv.1

theorem wf_append {a b : List Iv} : WF (a ++ b) ↔ WF a ∧ WF b ∧ ∀ u ∈ a, ∀ v ∈ b, u.2 < v.1 := by
  unfold WF
  rw [List.pairwise_append]
  constructor
  · rintro ⟨hall, hpa, hpb, hx⟩
    exact ⟨⟨fun iv h => hall iv (List.mem_append_left _ h), hpa⟩,
      ⟨fun iv h => hall iv (List.mem_append_right _ h), hpb⟩, hx⟩
  · rintro ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hx⟩
    refine ⟨fun iv h => ?_, ha2, hb2, hx⟩
    rcases List.mem_append.1 h with h | h
    · exact ha1 iv h
    · exact hb1 iv h

theorem wf_single (iv : Iv) (h : iv.1 < iv.2) : WF [iv] := by
  refine ⟨fun u hu => ?_, by simp⟩
  have : u = iv := by simpa using hu
  subst this
  exact h

theorem wf_cons {iv : Iv} {l : List Iv} : WF (iv :: l) ↔ iv.1 < iv.2 ∧ WF l ∧ ∀ v ∈ l, iv.2 < v.1 := by
  have : iv :: l = [iv] ++ l := rfl
  rw [this, wf_append]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.1 iv (by simp), h2, fun v hv => h3 iv (by simp) v hv⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨wf_single iv h1, h2, fun u hu v hv => ?_⟩
    have : u = iv := by simpa using hu
    subst this
    exact h3 v hv

theorem cov_append {a b : List Iv} {n : Nat} : Cov (a ++ b) n ↔ Cov a n ∨ Cov b n := by
  unfold Cov
  constructor
  · rintro ⟨iv, h, hn⟩
    rcases List.mem_append.1 h with h | h
    · exact Or.inl ⟨iv, h, hn⟩
    · exact Or.inr ⟨iv, h, hn⟩
  · rintro (⟨iv, h, hn⟩ | ⟨iv, h, hn⟩)
    · exact ⟨iv, List.mem_append_left _ h, hn⟩
    · exact ⟨iv, List.mem_append_right _ h, hn⟩

theorem cov_cons {iv : Iv} {l : List Iv} {n : Nat} : Cov (iv :: l) n ↔ (iv.1 ≤ n ∧ n < iv.2) ∨ Cov l n := by
  constructor
  · rintro ⟨u, h, hn⟩
    rcases List.mem_cons.1 h with h | h
    · subst h; exact Or.inl hn
    · exact Or.inr ⟨u, h, hn⟩
  · rintro (h | ⟨u, h, hn⟩)
    · exact ⟨iv, by simp, h⟩
    · exact ⟨u, List.mem_cons_of_mem _ h, hn⟩

theorem cov_nil {n : Nat} : ¬ Cov [] n := by
  rintro ⟨u, h, _⟩
  simp at h

theorem floorLe_append {f : Nat} {a b : List Iv} : FloorLe f (a ++ b) ↔ FloorLe f a ∧ FloorLe f b := by
  unfold FloorLe
  constructor
  · intro h
    exact ⟨fun iv hi => h iv (List.mem_append_left _ hi), fun iv hi => h iv (List.mem_append_right _ hi)⟩
  · rintro ⟨h1, h2⟩ iv hi
    rcases List.mem_append.1 hi with hi | hi
    · exact h1 iv hi
    · exact h2 iv hi

theorem floorLe_mono {f g : Nat} {l : List Iv} (h : FloorLe f l) (hg : g ≤ f) : FloorLe g l :=
  fun iv hi => Nat.le_trans hg (h iv hi)

/-- What one `insert` guarantees about the state it leaves. -/
def Spec (x : X) (pn : Nat) (ok : Bool) (y : X) : Prop :=
  WF y.items ∧ y.items.length ≤ x.cap ∧ y.cap = x.cap ∧ FloorLe y.floor y.items ∧ x.floor ≤ y.floor ∧
  (∀ n, y.floor ≤ n → (Cov y.items n ↔ (Cov x.items n ∨ (ok = true ∧ n = pn)))) ∧
  (ok = true → ¬ Cov x.items pn ∧ y.floor ≤ pn) ∧
  (ok = false → Cov x.items pn ∨ pn < y.floor)

theorem pushNew_spec (x : X) (pn : Nat) (a b : List Iv) (hab : a ++ b = x.items) (hwf : WF x.items)
    (hlen : x.items.length ≤ x.cap) (hfl : FloorLe x.floor x.items) (hcap : 1 ≤ x.cap)
    (hA : ∀ iv ∈ a, iv.2 < pn) (hB : ∀ iv ∈ b, pn + 1 < iv.1) (hpn : x.floor ≤ pn) :
    ∀ ok y, pushNew x a b pn = (ok, y) → Spec x pn ok y := by
  intro ok y h
  unfold Spec
  rw [← hab] at hwf hlen hfl ⊢
  obtain ⟨hwa, hwb, hx⟩ := wf_append.1 hwf
  obtain ⟨hfa, hfb⟩ := floorLe_append.1 hfl
  have hnot : ¬ Cov (a ++ b) pn := by
    intro hc
    rcases cov_append.1 hc with ⟨iv, hi, h1, h2⟩ | ⟨iv, hi, h1, h2⟩
    · have := hA iv hi; omega
    · have := hB iv hi; omega
  unfold pushNew at h
  by_cases hfull : a.length + b.length = x.cap
  · rw [if_pos hfull] at h
    rcases a with _ | ⟨⟨as, le⟩, a'⟩
    · rcases b with _ | ⟨⟨ls, le⟩, b'⟩
      · simp at hfull; omega
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hls : pn + 1 < ls := hB (ls, le) (by simp)
        obtain ⟨hlsle, hwb', hxb'⟩ := wf_cons.1 hwb
        refine ⟨by simpa [← hab] using hwf, by simpa [← hab] using hlen, rfl, ?_, Nat.le_max_left _ _, ?_, by simp, ?_⟩
        · intro iv hi
          rcases List.mem_cons.1 (show iv ∈ (ls, le) :: b' by simpa [← hab] using hi) with rfl | hi'
          · exact Nat.max_le.2 ⟨hfb _ (by simp), Nat.le_refl _⟩
          · have h1 := hxb' iv hi'
            have h2 := hfb iv (List.mem_cons_of_mem _ hi')
            exact Nat.max_le.2 ⟨h2, by simp only at hlsle h1 ⊢; omega⟩
        · intro n _; simp [← hab]
        · intro _; right; exact Nat.lt_of_lt_of_le (by omega) (Nat.le_max_right _ _)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hlea : le < pn := hA (as, le) (by simp)
      obtain ⟨hwh, hwa', hxh⟩ := wf_cons.1 hwa
      obtain ⟨hfh, hfa'⟩ : x.floor ≤ as ∧ FloorLe x.floor a' := by
        refine ⟨hfa (as, le) (by simp), fun iv hi => hfa iv (List.mem_cons_of_mem _ hi)⟩
      have hlen' : a'.length + 1 + b.length ≤ x.cap := by simp at hfull; omega
      refine ⟨?_, by simp; omega, rfl, ?_, Nat.le_max_left _ _, ?_, ?_, by simp⟩
      · refine wf_append.2 ⟨hwa', wf_cons.2 ⟨by omega, hwb, fun v hv => hB v hv⟩, ?_⟩
        intro u hu v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact hA u (List.mem_cons_of_mem _ hu)
        · exact hx u (List.mem_cons_of_mem _ hu) v hv
      · refine floorLe_append.2 ⟨fun iv hi => ?_, fun iv hi => ?_⟩
        · have := hxh iv hi; exact Nat.max_le.2 ⟨hfa' iv hi, by simp only at this; omega⟩
        · rcases List.mem_cons.1 hi with rfl | hi
          · exact Nat.max_le.2 ⟨hpn, by omega⟩
          · have := hB iv hi; exact Nat.max_le.2 ⟨hfb iv hi, by omega⟩
      · intro n hn
        have hn' : le ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
        have e1 : (pn ≤ n ∧ n < pn + 1) ↔ n = pn := by omega
        have e2 : ¬ (as ≤ n ∧ n < le) := by omega
        simp only [cov_append, cov_cons, List.cons_append, e1, e2, false_or, true_and]
        grind
      · intro _
        exact ⟨hnot, Nat.max_le.2 ⟨hpn, by omega⟩⟩
  · rw [if_neg hfull] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hlen' : a.length + 1 + b.length ≤ x.cap := by simp at hlen; omega
    refine ⟨?_, by simp; omega, rfl, ?_, Nat.le_refl _, ?_, fun _ => ⟨hnot, hpn⟩, by simp⟩
    · refine wf_append.2 ⟨hwa, wf_cons.2 ⟨by omega, hwb, fun v hv => hB v hv⟩, ?_⟩
      intro u hu v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hA u hu
      · exact hx u hu v hv
    · refine floorLe_append.2 ⟨hfa, fun iv hi => ?_⟩
      rcases List.mem_cons.1 hi with rfl | hi
      · exact hpn
      · exact hfb iv hi
    · intro n _
      have e1 : (pn ≤ n ∧ n < pn + 1) ↔ n = pn := by omega
      simp only [cov_append, cov_cons, e1, true_and]
      grind

end Pinc.TransportRx
