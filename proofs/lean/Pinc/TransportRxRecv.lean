import Pinc.Axioms
import Pinc.TransportRxThm

/-!
# Received packets: an insertion keeps the set exact

`insertAB_spec` is the case analysis of `insert` (a duplicate, a number that extends the range below it, the range
above it, joins two ranges, or opens a new one, forgetting the lowest when the set is full); `insert_spec` adds the
split at the partition point and the numbers below the floor; `receive_good` carries the invariant `Good` through
`on_packet_received`: the ranges are exactly the numbers received at or above the floor.
-/

namespace Pinc.TransportRx

theorem split_append (pn : Nat) : ∀ l : List Iv, (split pn l).1 ++ (split pn l).2 = l
  | [] => by simp [split]
  | iv :: t => by
    unfold split
    split
    · simp [split_append pn t]
    · simp

theorem split_lt (pn : Nat) : ∀ l : List Iv, ∀ iv ∈ (split pn l).1, iv.2 < pn
  | [] => by simp [split]
  | u :: t => by
    unfold split
    split
    · rename_i h
      intro iv hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact h
      · exact split_lt pn t iv hi
    · simp

theorem split_head (pn : Nat) : ∀ (l : List Iv) (s e : Nat) (b' : List Iv), (split pn l).2 = (s, e) :: b' → pn ≤ e
  | [], s, e, b', h => by simp [split] at h
  | u :: t, s, e, b', h => by
    unfold split at h
    split at h
    · exact split_head pn t s e b' h
    · rename_i hn
      simp at h
      obtain ⟨⟨rfl, rfl⟩, _⟩ := h
      omega

theorem insertAB_spec (x : X) (pn : Nat) (a b : List Iv) (hab : a ++ b = x.items) (hwf : WF x.items)
    (hlen : x.items.length ≤ x.cap) (hfl : FloorLe x.floor x.items) (hcap : 1 ≤ x.cap)
    (hA : ∀ iv ∈ a, iv.2 < pn) (hB : ∀ s e b', b = (s, e) :: b' → pn ≤ e) (hpn : x.floor ≤ pn) :
    ∀ ok y, insertAB x pn a b = (ok, y) → Spec x pn ok y := by
  intro ok y h
  have hps := pushNew_spec x pn
  unfold Spec at hps ⊢
  have hab' := hab
  rw [← hab] at hwf hlen hfl
  obtain ⟨hwa, hwb, hx⟩ := wf_append.1 hwf
  obtain ⟨hfa, hfb⟩ := floorLe_append.1 hfl
  cases b with
  | nil =>
    unfold insertAB at h
    exact hps a [] hab (by rw [← hab]; exact hwf) (by rw [← hab]; exact hlen) (by rw [← hab]; exact hfl) hcap hA (by simp) hpn ok y h
  | cons u b' =>
    obtain ⟨s, e⟩ := u
    have hen : pn ≤ e := hB s e b' rfl
    obtain ⟨hse, hwb', hxe⟩ := wf_cons.1 hwb
    have hmem : (s, e) ∈ a ++ (s, e) :: b' := by simp
    have hxs : ∀ u ∈ a, u.2 < s := fun u hu => hx u hu (s, e) (by simp)
    have hfs : x.floor ≤ s := hfb (s, e) (by simp)
    unfold insertAB at h
    dsimp only at h
    by_cases hd : s ≤ pn ∧ pn < e
    · rw [if_pos hd] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [← hab]
      refine ⟨hwf, hlen, rfl, hfl, Nat.le_refl _, ?_, by simp, ?_⟩
      · intro n _; simp
      · intro _; left; exact ⟨(s, e), hmem, hd⟩
    · rw [if_neg hd] at h
      by_cases he : e = pn
      · rw [if_pos he] at h
        have hnot : ¬ Cov (a ++ (s, e) :: b') pn := by
          intro hc
          rcases cov_append.1 hc with ⟨iv, hi, h1, h2⟩ | hc
          · have := hA iv hi; omega
          · rcases cov_cons.1 hc with h1 | hc
            · omega
            · rcases hc with ⟨iv, hi, h1, h2⟩
              have := hxe iv hi; omega
        rcases b' with _ | ⟨⟨ns, ne⟩, b''⟩
        case cons =>
          dsimp only at h
          obtain ⟨hne, hwb'', hxn⟩ := wf_cons.1 hwb'
          have hens : e < ns := hxe (ns, ne) (by simp)
          by_cases hns : ns = pn + 1
          · rw [if_pos hns] at h
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [← hab]
            have hfb'' : FloorLe x.floor b'' := fun iv hi => hfb iv (by simp [hi])
            refine ⟨?_, ?_, rfl, ?_, Nat.le_refl _, ?_, fun _ => ⟨hnot, hpn⟩, by simp⟩
            · refine wf_append.2 ⟨hwa, wf_cons.2 ⟨by simp at hne ⊢; omega, hwb'', hxn⟩, ?_⟩
              intro u hu v hv
              rcases List.mem_cons.1 hv with rfl | hv
              · exact hxs u hu
              · exact hx u hu v (by simp [hv])
            · dsimp only
              simp only [List.length_append, List.length_cons] at hlen ⊢
              omega
            · refine floorLe_append.2 ⟨hfa, fun iv hi => ?_⟩
              rcases List.mem_cons.1 hi with rfl | hi
              · exact hfs
              · exact hfb'' iv hi
            · intro n _
              simp only [cov_append, cov_cons, List.cons_append, cov_nil, or_false, true_and]
              grind
          · rw [if_neg hns] at h
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [← hab]
            have hfb' : FloorLe x.floor ((ns, ne) :: b'') := fun iv hi => hfb iv (List.mem_cons_of_mem _ hi)
            refine ⟨?_, ?_, rfl, ?_, Nat.le_refl _, ?_, fun _ => ⟨hnot, hpn⟩, by simp⟩
            · refine wf_append.2 ⟨hwa, wf_cons.2 ⟨by omega, wf_cons.2 ⟨hne, hwb'', hxn⟩, ?_⟩, ?_⟩
              · intro v hv
                rcases List.mem_cons.1 hv with rfl | hv
                · simp only; omega
                · have := hxn v hv; have := hxe v (List.mem_cons_of_mem _ hv); simp only at *; omega
              · intro u hu v hv
                rcases List.mem_cons.1 hv with rfl | hv
                · exact hxs u hu
                · exact hx u hu v (List.mem_cons_of_mem _ hv)
            · dsimp only; simp only [List.length_append, List.length_cons] at hlen ⊢; omega
            · refine floorLe_append.2 ⟨hfa, fun iv hi => ?_⟩
              rcases List.mem_cons.1 hi with rfl | hi
              · exact hfs
              · exact hfb' iv hi
            · intro n _
              simp only [cov_append, cov_cons, List.cons_append, cov_nil, or_false, true_and]
              grind
        case nil =>
          dsimp only at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [← hab]
          refine ⟨?_, ?_, rfl, ?_, Nat.le_refl _, ?_, fun _ => ⟨hnot, hpn⟩, by simp⟩
          · refine wf_append.2 ⟨hwa, wf_single (s, pn + 1) (by omega), ?_⟩
            intro u hu v hv
            have : v = (s, pn + 1) := by simpa using hv
            subst this
            exact hxs u hu
          · dsimp only; simp only [List.length_append, List.length_cons] at hlen ⊢; omega
          · refine floorLe_append.2 ⟨hfa, fun iv hi => ?_⟩
            have : iv = (s, pn + 1) := by simpa using hi
            subst this
            exact hfs
          · intro n _
            simp only [cov_append, cov_cons, List.cons_append, cov_nil, or_false, true_and]
            grind
      · rw [if_neg he] at h
        have hep : pn < e := by omega
        have hsp : pn < s := by
          apply Classical.byContradiction; intro hc
          exact hd ⟨by omega, hep⟩
        by_cases hs : s = pn + 1
        · rw [if_pos hs] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [← hab]
          have hnot : ¬ Cov (a ++ (s, e) :: b') pn := by
            intro hc
            rcases cov_append.1 hc with ⟨iv, hi, h1, h2⟩ | hc
            · have := hA iv hi; omega
            · rcases cov_cons.1 hc with h1 | hc
              · omega
              · rcases hc with ⟨iv, hi, h1, h2⟩
                have := hxe iv hi; omega
          refine ⟨?_, ?_, rfl, ?_, Nat.le_refl _, ?_, fun _ => ⟨hnot, hpn⟩, by simp⟩
          · refine wf_append.2 ⟨hwa, wf_cons.2 ⟨hep, hwb', hxe⟩, ?_⟩
            intro u hu v hv
            rcases List.mem_cons.1 hv with rfl | hv
            · exact hA u hu
            · exact hx u hu v (List.mem_cons_of_mem _ hv)
          · simpa using hlen
          · refine floorLe_append.2 ⟨hfa, fun iv hi => ?_⟩
            rcases List.mem_cons.1 hi with rfl | hi
            · exact hpn
            · exact hfb iv (List.mem_cons_of_mem _ hi)
          · intro n _
            simp only [cov_append, cov_cons, List.cons_append, cov_nil, or_false, true_and]
            grind
        · rw [if_neg hs] at h
          refine hps a ((s, e) :: b') hab (by rw [← hab]; exact hwf) (by rw [← hab]; exact hlen) (by rw [← hab]; exact hfl) hcap hA ?_ hpn ok y h
          intro iv hi
          rcases List.mem_cons.1 hi with rfl | hi
          · simp only; omega
          · have := hxe iv hi; simp only at *; omega

theorem insert_spec (x : X) (pn : Nat) (hwf : WF x.items) (hlen : x.items.length ≤ x.cap)
    (hfl : FloorLe x.floor x.items) (hcap : 1 ≤ x.cap) :
    ∀ ok y, insert x pn = (ok, y) → Spec x pn ok y := by
  intro ok y h
  unfold insert at h
  by_cases h0 : pn < x.floor
  · rw [if_pos h0] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hwf, hlen, rfl, hfl, Nat.le_refl _, ?_, by simp, fun _ => Or.inr h0⟩
    intro n _; simp
  · rw [if_neg h0] at h
    exact insertAB_spec x pn _ _ (split_append pn x.items) hwf hlen hfl hcap (split_lt pn x.items)
      (fun s e b' hb => split_head pn x.items s e b' hb) (by omega) ok y h

/-- The ranges are the numbers of `seen` at or above the floor. -/
def Good (x : X) (seen : Nat → Prop) : Prop :=
  WF x.items ∧ x.items.length ≤ x.cap ∧ FloorLe x.floor x.items ∧ ∀ n, Cov x.items n ↔ (seen n ∧ x.floor ≤ n)

theorem insert_good (x : X) (seen : Nat → Prop) (pn : Nat) (hcap : 1 ≤ x.cap) (hg : Good x seen) :
    ∀ ok y, insert x pn = (ok, y) →
      Good y (fun n => seen n ∨ (ok = true ∧ n = pn)) ∧ y.cap = x.cap ∧ (ok = true → ¬ seen pn ∧ x.floor ≤ pn) := by
  intro ok y h
  obtain ⟨hwf, hlen, hfl, hiff⟩ := hg
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := insert_spec x pn hwf hlen hfl hcap ok y h
  refine ⟨⟨s1, by rw [s3]; exact s2, s4, ?_⟩, s3, ?_⟩
  · intro n
    by_cases hn : y.floor ≤ n
    · rw [s6 n hn, hiff n]
      constructor
      · rintro (⟨h1, _⟩ | h1)
        · exact ⟨Or.inl h1, hn⟩
        · exact ⟨Or.inr h1, hn⟩
      · rintro ⟨h1 | h1, _⟩
        · exact Or.inl ⟨h1, Nat.le_trans s5 hn⟩
        · exact Or.inr h1
    · constructor
      · rintro ⟨iv, hi, h1, h2⟩
        have := s4 iv hi; omega
      · rintro ⟨_, h1⟩; exact absurd h1 hn
  · intro hok
    obtain ⟨n1, n2⟩ := s7 hok
    refine ⟨fun hs => n1 ?_, Nat.le_trans s5 n2⟩
    exact (hiff pn).2 ⟨hs, Nat.le_trans s5 n2⟩

theorem good_congr {x y : X} {s s' : Nat → Prop} (hi : y.items = x.items) (hf : y.floor = x.floor)
    (hc : y.cap = x.cap) (hs : ∀ n, s n ↔ s' n) (g : Good x s) : Good y s' := by
  obtain ⟨a, b, c, d⟩ := g
  refine ⟨by rw [hi]; exact a, by rw [hi, hc]; exact b, by rw [hi, hf]; exact c, fun n => ?_⟩
  rw [hi, hf, ← hs n]
  exact d n

theorem receive_good (x : X) (seen : Nat → Prop) (p : Rx) (hcap : 1 ≤ x.cap) (hg : Good x seen) :
    ∀ out y, receive x p = (out, y) →
      Good y (fun n => seen n ∨ (out = "New" ∧ n = p.pn)) ∧ y.cap = x.cap ∧ (out = "New" → ¬ seen p.pn ∧ x.floor ≤ p.pn) := by
  intro out y h
  unfold receive at h
  by_cases hm : maxpn < p.pn
  · rw [if_pos hm] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, rfl, by simp⟩
    have hne : ¬ ("PacketNumberOutOfRange" = "New") := by decide
    have : (fun n => seen n ∨ ("PacketNumberOutOfRange" = "New" ∧ n = p.pn)) = seen := by
      funext n; simp [hne]
    rw [this]; exact hg
  · rw [if_neg hm] at h
    rcases hins : insert x p.pn with ⟨ok, y0⟩
    simp only [hins] at h
    obtain ⟨g, hc, hn⟩ := insert_good x seen p.pn hcap hg ok y0 hins
    by_cases hok : ok = true
    · subst hok
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
      split at h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨good_congr rfl rfl rfl (fun n => by simp) g, hc, by simpa using hn⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨good_congr rfl rfl rfl (fun n => by simp) g, hc, by simpa using hn⟩
    · have : ok = false := by simpa using hok
      subst this
      simp only [Bool.not_false, if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, hc, by simp⟩
      have hne : ¬ ("Duplicate" = "New") := by decide
      have : (fun n => seen n ∨ ("Duplicate" = "New" ∧ n = p.pn)) = (fun n => seen n ∨ (false = true ∧ n = p.pn)) := by
        funext n; simp [hne]
      rw [this]; exact g

end Pinc.TransportRx
