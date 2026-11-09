import Vinc.ReconcileApsCount

/-!
# Reconcile APS, part 7: the potentials

For a fan bound `f` (2 for any split, 16 when no leaf is ever narrowed) every part `p` has

* a rank `psi p` that bounds the depth still ahead of it: `2 (lg f nA + lg f nB)` for the counts of the two sets in its
  interval, plus 3 for a fingerprint part, 2 for an ids part or a full part sent by the initiator, 0 otherwise;
* a potential `pot p`: 1 for a fingerprint part with equal fingerprints, `1 + 17 delta psi` for a differing one,
  `17 + 17 delta psi` for an ids part or an initiator full part, 1 otherwise (`delta` = the difference items in its
  interval).

`Proc.cost`: every new part has a smaller rank (`psi k + 1 <= psi p`) and `1 + sum of the potentials of the new parts <=
pot p`. Summed over the run this bounds the number of steps (ReconcileApsBounds).
-/

namespace Vinc.Reconcile

def Cfg.psi (c : Cfg) (f : Nat) (p : Part) : Nat :=
  2 * (lg f (cnt c.A p.iv) + lg f (cnt c.B p.iv)) +
    (match p.kind with | .fp => 3 | .ids => 2 | .full => if p.toInit then 0 else 2 | .reply _ => 0)

def Cfg.pot (c : Cfg) (f : Nat) (p : Part) : Nat :=
  match p.kind with
  | .fp => if c.delta p.iv = 0 then 1 else 1 + 17 * (c.delta p.iv * c.psi f p)
  | .ids => 17 + 17 * (c.delta p.iv * c.psi f p)
  | .full => if p.toInit then 1 else 17 + 17 * (c.delta p.iv * c.psi f p)
  | .reply _ => 1

theorem Cfg.pot_pos (c : Cfg) (f : Nat) (p : Part) : 1 ≤ c.pot f p := by
  unfold Cfg.pot
  split <;> (try split) <;> omega

/-- The potentials of the pieces of a split of a differing interval. -/
theorem split_pot (c : Cfg) (f : Nat) (kids : List Part) (I : Iv) (ψ' : Nat)
    (hk : ∀ k ∈ kids, k.kind = .fp ∧ c.psi f k ≤ ψ') (hlen : kids.length ≤ 16)
    (hd : kids.Pairwise (fun k l => k.iv.Disj l.iv)) (hs : ∀ k ∈ kids, ∀ z, k.iv.has z = true → I.has z = true) :
    lsum (c.pot f) kids ≤ 16 + 17 * (c.delta I * ψ') := by
  have h1 : lsum (c.pot f) kids ≤ lsum (fun k => 1 + (17 * ψ') * c.delta k.iv) kids := by
    apply lsum_le
    intro k hkk
    obtain ⟨hkind, hps⟩ := hk k hkk
    unfold Cfg.pot
    rw [hkind]
    simp only
    split
    · omega
    · have h2 : c.delta k.iv * c.psi f k ≤ c.delta k.iv * ψ' := Nat.mul_le_mul_left _ hps
      have h3 : (17 * ψ') * c.delta k.iv = 17 * (c.delta k.iv * ψ') := by
        rw [Nat.mul_assoc, Nat.mul_comm ψ']
      omega
  have h4 : lsum (fun k => 1 + (17 * ψ') * c.delta k.iv) kids =
      kids.length * 1 + (17 * ψ') * lsum (fun k => c.delta k.iv) kids := by
    rw [lsum_add (g := fun (_ : Part) => 1) (h := fun (k : Part) => (17 * ψ') * c.delta k.iv), lsum_const,
      lsum_mul (fun (k : Part) => c.delta k.iv)]
  have h5 : lsum (fun k => c.delta k.iv) kids ≤ c.delta I := by
    have := c.delta_sum_le I (kids.map (·.iv)) (by rw [List.pairwise_map]; exact hd)
      (by intro J hJ; obtain ⟨k, hkk, rfl⟩ := List.mem_map.mp hJ; exact hs k hkk)
    rw [lsum_map] at this; exact this
  have h6 : (17 * ψ') * lsum (fun k => c.delta k.iv) kids ≤ (17 * ψ') * c.delta I := Nat.mul_le_mul_left _ h5
  have h7 : (17 * ψ') * c.delta I = 17 * (c.delta I * ψ') := by rw [Nat.mul_assoc, Nat.mul_comm ψ']
  omega

/-- A split lowers the splitter's `lg` by one and never raises the other side's. -/
theorem split_lg (f fan : Nat) (hf : 2 ≤ f) (hfan : f ≤ fan) (I : Iv) (T U : List Item) (hT : Sorted T)
    (hc : 2 ≤ cnt T I) (J : Iv) (hJ : J ∈ splitIvs T I fan) :
    lg f (cnt T J) + 1 ≤ lg f (cnt T I) ∧ lg f (cnt U J) ≤ lg f (cnt U I) := by
  obtain ⟨_, hsub, _, _, hstep, _⟩ := splitIvs_spec hT I (fan := fan) (by omega) hc
  exact ⟨lg_dec hf hfan hc (hstep J hJ), lg_mono hf _ _ (cnt_mono (hsub J hJ))⟩


theorem pot_fp (c : Cfg) (f : Nat) (t : Bool) (I : Iv) (d : Nat) (h : 1 ≤ c.delta I) :
    c.pot f ⟨.fp, t, I, d⟩ = 1 + 17 * (c.delta I * c.psi f ⟨.fp, t, I, d⟩) := by
  unfold Cfg.pot; simp only; rw [if_neg (by omega)]

theorem mul_succ_eq (a b : Nat) : a * (b + 1) = a * b + a := Nat.mul_succ a b

section lemmas
variable (c : Cfg) (f : Nat) (t : Bool) (I : Iv) (d : Nat)

theorem psi_fp : c.psi f ⟨.fp, t, I, d⟩ = 2 * (lg f (cnt c.A I) + lg f (cnt c.B I)) + 3 := rfl
theorem psi_ids : c.psi f ⟨.ids, t, I, d⟩ = 2 * (lg f (cnt c.A I) + lg f (cnt c.B I)) + 2 := rfl
theorem psi_fullF : c.psi f ⟨.full, false, I, d⟩ = 2 * (lg f (cnt c.A I) + lg f (cnt c.B I)) + 2 := rfl
theorem psi_fullT : c.psi f ⟨.full, true, I, d⟩ = 2 * (lg f (cnt c.A I) + lg f (cnt c.B I)) + 0 := rfl
theorem psi_reply (v : Bool) : c.psi f ⟨.reply v, t, I, d⟩ = 2 * (lg f (cnt c.A I) + lg f (cnt c.B I)) + 0 := rfl
theorem pot_ids : c.pot f ⟨.ids, t, I, d⟩ = 17 + 17 * (c.delta I * c.psi f ⟨.ids, t, I, d⟩) := rfl
theorem pot_fullF : c.pot f ⟨.full, false, I, d⟩ = 17 + 17 * (c.delta I * c.psi f ⟨.full, false, I, d⟩) := rfl
theorem pot_fullT : c.pot f ⟨.full, true, I, d⟩ = 1 := rfl
theorem pot_reply (v : Bool) : c.pot f ⟨.reply v, t, I, d⟩ = 1 := rfl
end lemmas

/-- One step: every new part has a smaller rank, and the potential pays for the step and for the new parts. -/
theorem Proc.cost {c : Cfg} {ex : Bool} {p : Part} {kids : List Part} {ha ta : List Item} {lf : Bool}
    (hp : Proc c ex p kids ha ta lf) {f : Nat} (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) :
    (∀ k ∈ kids, c.psi f k + 1 ≤ c.psi f p) ∧ 1 + lsum (c.pot f) kids ≤ c.pot f p := by
  have hmin := c.hmin
  cases hp with
  | @fpEq d toInit I h =>
    refine ⟨by simp, ?_⟩
    have := c.pot_pos f ⟨.fp, toInit, I, d⟩
    simp only [lsum]; omega
  | @fpLeafResp d I hne hcnt hf =>
    have hδ := c.delta_pos_of_not_fpEq hne
    rw [pot_fp c f _ _ _ hδ]
    have h4 : 1 ≤ c.delta I * c.psi f ⟨.fp, false, I, d⟩ :=
      Nat.mul_pos hδ (by rw [psi_fp]; omega)
    refine ⟨?_, ?_⟩
    · intro k hk; simp at hk; subst hk; rw [psi_fullT, psi_fp]; omega
    · simp only [lsum, pot_fullT]; omega
  | @fpLeafInit d I hne hcnt hf =>
    have hδ := c.delta_pos_of_not_fpEq hne
    rw [pot_fp c f _ _ _ hδ]
    rw [psi_fp]
    have e := mul_succ_eq (c.delta I) (2 * (lg f (cnt c.A I) + lg f (cnt c.B I)) + 2)
    cases ex
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · intro k hk; simp at hk; subst hk; rw [psi_ids]; omega
      · simp only [lsum, pot_ids, psi_ids]
        generalize c.delta I * (2 * (lg f (cnt c.A I) + lg f (cnt c.B I)) + 2) = X at *
        generalize c.delta I * (2 * (lg f (cnt c.A I) + lg f (cnt c.B I)) + 2 + 1) = Y at *
        omega
    · simp only [↓reduceIte]
      refine ⟨?_, ?_⟩
      · intro k hk; simp at hk; subst hk; rw [psi_fullF]; omega
      · simp only [lsum, pot_fullF, psi_fullF]
        generalize c.delta I * (2 * (lg f (cnt c.A I) + lg f (cnt c.B I)) + 2) = X at *
        generalize c.delta I * (2 * (lg f (cnt c.A I) + lg f (cnt c.B I)) + 2 + 1) = Y at *
        omega
  | @fpSplit d toInit I fan hne hno hf1 hf2 =>
    have hδ := c.delta_pos_of_not_fpEq hne
    have hc := two_le_of_no_leaf c hno
    have hT : Sorted (c.set toInit) := by cases toInit <;> simp [Cfg.set, c.hA, c.hB]
    obtain ⟨hsub, hdisj, hlen⟩ := split_kids c _ hT I (fan := fan) (by omega) hf2 hc (!toInit) d
    have hlg : ∀ J ∈ splitIvs (c.set toInit) I fan,
        lg f (cnt c.A J) + lg f (cnt c.B J) + 1 ≤ lg f (cnt c.A I) + lg f (cnt c.B I) := by
      intro J hJ
      cases toInit
      · have := split_lg f fan hfl (by omega) I c.B c.A hT hc J hJ; simp [Cfg.set] at *; omega
      · have := split_lg f fan hfl (by omega) I c.A c.B hT hc J hJ; simp [Cfg.set] at *; omega
    have hpsi : ∀ k ∈ (splitIvs (c.set toInit) I fan).map (fun J => (⟨.fp, !toInit, J, d + 1⟩ : Part)),
        c.psi f k + 2 ≤ c.psi f ⟨.fp, toInit, I, d⟩ := by
      intro k hk
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hk
      have := hlg J hJ
      rw [psi_fp, psi_fp]; omega
    refine ⟨fun k hk => by have := hpsi k hk; omega, ?_⟩
    have hsp := split_pot c f ((splitIvs (c.set toInit) I fan).map (fun J => (⟨.fp, !toInit, J, d + 1⟩ : Part))) I
      (c.psi f ⟨.fp, toInit, I, d⟩ - 1)
      (fun k hk => ⟨by obtain ⟨J, _, rfl⟩ := List.mem_map.mp hk; rfl, by have := hpsi k hk; omega⟩) hlen hdisj hsub
    rw [pot_fp c f _ _ _ hδ]
    have h3 : 3 ≤ c.psi f ⟨.fp, toInit, I, d⟩ := by rw [psi_fp]; omega
    obtain ⟨m, hm⟩ : ∃ m, c.psi f ⟨.fp, toInit, I, d⟩ = m + 1 := ⟨c.psi f ⟨.fp, toInit, I, d⟩ - 1, by omega⟩
    rw [hm] at hsp ⊢
    have e := mul_succ_eq (c.delta I) m
    simp only [Nat.add_sub_cancel] at hsp
    generalize c.delta I * m = X at *
    generalize c.delta I * (m + 1) = Y at *
    omega
  | @respLeaf d I k hk hcnt hf =>
    refine ⟨?_, ?_⟩
    · intro k' hk'; simp at hk'; subst hk'
      rcases hk with rfl | rfl
      · rw [psi_reply, psi_ids]; omega
      · rw [psi_reply, psi_fullF]; omega
    · simp only [lsum, pot_reply]
      rcases hk with rfl | rfl
      · rw [pot_ids]; omega
      · rw [pot_fullF]; omega
  | @respNarrow d I k fan hk hno hf1 hf2 =>
    have hc := two_le_of_no_leaf' c hno
    obtain ⟨hsub, hdisj, hlen⟩ := split_kids c _ c.hB I (fan := fan) (by omega) hf2 hc true d
    have hlg : ∀ J ∈ splitIvs c.B I fan,
        lg f (cnt c.A J) + lg f (cnt c.B J) + 1 ≤ lg f (cnt c.A I) + lg f (cnt c.B I) := by
      intro J hJ
      have := split_lg f fan hfl (by omega) I c.B c.A c.hB hc J hJ; omega
    have hpk : c.psi f ⟨k, false, I, d⟩ = 2 * (lg f (cnt c.A I) + lg f (cnt c.B I)) + 2 := by
      rcases hk with rfl | rfl
      · exact psi_ids c f false I d
      · exact psi_fullF c f I d
    have hpsi : ∀ k' ∈ (splitIvs c.B I fan).map (fun J => (⟨.fp, true, J, d + 1⟩ : Part)),
        c.psi f k' + 1 ≤ c.psi f ⟨k, false, I, d⟩ := by
      intro k' hk'
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hk'
      have := hlg J hJ
      rw [psi_fp, hpk]; omega
    refine ⟨hpsi, ?_⟩
    have hsp := split_pot c f ((splitIvs c.B I fan).map (fun J => (⟨.fp, true, J, d + 1⟩ : Part))) I
      (c.psi f ⟨k, false, I, d⟩ - 1)
      (fun k' hk' => ⟨by obtain ⟨J, _, rfl⟩ := List.mem_map.mp hk'; rfl, by have := hpsi k' hk'; omega⟩)
      hlen hdisj hsub
    have hpot : c.pot f ⟨k, false, I, d⟩ = 17 + 17 * (c.delta I * c.psi f ⟨k, false, I, d⟩) := by
      rcases hk with rfl | rfl
      · exact pot_ids c f false I d
      · exact pot_fullF c f I d
    have h5 : c.delta I * (c.psi f ⟨k, false, I, d⟩ - 1) ≤ c.delta I * c.psi f ⟨k, false, I, d⟩ :=
      Nat.mul_le_mul_left _ (by omega)
    rw [hpot]
    omega
  | fullInit => simp only [lsum, pot_fullT]; exact ⟨by simp, by omega⟩
  | replyExact => simp only [lsum, pot_reply]; exact ⟨by simp, by omega⟩
  | replyIds => simp only [lsum, pot_reply]; exact ⟨by simp, by omega⟩

end Vinc.Reconcile
