import Vinc.ReconcileMachine

/-!
# Reconcile algebra: the order, the rank, the slices and the XOR fingerprint of a sorted index

The facts the correctness proofs of the session use about the model's index: `lexLt` is a strict total order (the byte
order of the items), the items of a range `lo..hi` are the slice `a..b` of the ranks of its bounds, a separator `q[..cpl p q + 1]`
of `p < q` cuts between them, and the XOR of item hashes is a linear map (`xorH`), so under the one assumption that the
hashes are XOR-independent (`Indep`), equal fingerprints mean equal parity sets.
-/

namespace Vinc.Reconcile

/-! ## The byte order -/

theorem lexLt_nil_right : ∀ a : List Nat, lexLt a [] = false
  | [] => rfl
  | _ :: _ => rfl

theorem lexLt_irrefl : ∀ a : List Nat, lexLt a a = false
  | [] => rfl
  | x :: xs => by simp [lexLt, lexLt_irrefl xs]

theorem lexLt_trans : ∀ a b c : List Nat, lexLt a b = true → lexLt b c = true → lexLt a c = true
  | [], [], _, h, _ => by simp [lexLt] at h
  | [], _ :: _, [], _, h => by simp [lexLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [lexLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLt] at h
  | a :: as, b :: bs, c :: cs, h1, h2 => by
    simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact Or.inl (Nat.lt_trans h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, lexLt_trans as bs cs h1 h2⟩

theorem lexLt_total : ∀ a b : List Nat, lexLt a b = true ∨ a = b ∨ lexLt b a = true
  | [], [] => Or.inr (Or.inl rfl)
  | [], _ :: _ => Or.inl rfl
  | _ :: _, [] => Or.inr (Or.inr rfl)
  | a :: as, b :: bs => by
    simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, List.cons.injEq]
    rcases Nat.lt_trichotomy a b with h | rfl | h
    · exact Or.inl (Or.inl h)
    · rcases lexLt_total as bs with h | rfl | h
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
    · exact Or.inr (Or.inr (Or.inl h))

theorem lexLt_asymm (a b : List Nat) (h : lexLt a b = true) : lexLt b a = false := by
  cases h' : lexLt b a with
  | false => rfl
  | true => have := lexLt_trans _ _ _ h h'; simp [lexLt_irrefl] at this

theorem lexLt_ne (a b : List Nat) (h : lexLt a b = true) : a ≠ b := by
  rintro rfl; simp [lexLt_irrefl] at h

/-- `¬ a < b` is `b ≤ a`. -/
theorem lexLt_false_iff (a b : List Nat) : lexLt a b = false ↔ (a = b ∨ lexLt b a = true) := by
  constructor
  · intro h
    rcases lexLt_total a b with h' | h' | h'
    · simp [h] at h'
    · exact Or.inl h'
    · exact Or.inr h'
  · rintro (rfl | h)
    · exact lexLt_irrefl _
    · exact lexLt_asymm _ _ h

/-! ## The shared prefix and the separator -/

theorem cpl_le_left : ∀ p q : List Nat, cpl p q ≤ p.length
  | [], _ => by simp [cpl]
  | _ :: _, [] => by simp [cpl]
  | a :: as, b :: bs => by
    simp only [cpl]; split
    · have := cpl_le_left as bs; simp; omega
    · simp

theorem cpl_le_right : ∀ p q : List Nat, cpl p q ≤ q.length
  | [], _ => by simp [cpl]
  | _ :: _, [] => by simp [cpl]
  | a :: as, b :: bs => by
    simp only [cpl]; split
    · have := cpl_le_right as bs; simp; omega
    · simp

theorem take_cpl_eq : ∀ p q : List Nat, p.take (cpl p q) = q.take (cpl p q)
  | [], _ => by simp [cpl]
  | _ :: _, [] => by simp [cpl]
  | a :: as, b :: bs => by
    simp only [cpl]; split
    · next h => subst h; simp [take_cpl_eq as bs]
    · simp

/-- If `p < q` the shared prefix is shorter than `q`. -/
theorem cpl_lt_right : ∀ p q : List Nat, lexLt p q = true → cpl p q < q.length
  | [], [], h => by simp [lexLt] at h
  | [], _ :: _, _ => by simp [cpl]
  | _ :: _, [], h => by simp [lexLt] at h
  | a :: as, b :: bs, h => by
    simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
    simp only [cpl]; split
    · next hab =>
      subst hab
      rcases h with h | ⟨_, h⟩
      · omega
      · have := cpl_lt_right as bs h; simp; omega
    · simp

/-- The separator `q[..cpl p q + 1]` of `p < q` has `p < sep ≤ q`. -/
theorem sep_between : ∀ p q : List Nat, lexLt p q = true →
    lexLt p (q.take (cpl p q + 1)) = true ∧ lexLt q (q.take (cpl p q + 1)) = false
  | [], [], h => by simp [lexLt] at h
  | [], b :: bs, _ => by simp [cpl, lexLt, lexLt_nil_right]
  | _ :: _, [], h => by simp [lexLt] at h
  | a :: as, b :: bs, h => by
    simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
    simp only [cpl]; split
    · next hab =>
      subst hab
      rcases h with h | ⟨_, h⟩
      · omega
      · obtain ⟨h1, h2⟩ := sep_between as bs h
        simp only [List.take_succ_cons, lexLt]
        constructor <;> simp_all
    · next hab =>
      rcases h with h | ⟨rfl, _⟩
      · simp [lexLt, h, lexLt_nil_right]
      · exact absurd rfl hab


/-! ## Sorted indexes: rank and range slices -/

/-- A strictly ascending index. -/
def Sorted (S : List Item) : Prop := S.Pairwise (fun x y => lexLt x y = true)

theorem Sorted.tail {x : Item} {S : List Item} (h : Sorted (x :: S)) : Sorted S := (List.pairwise_cons.mp h).2

theorem Sorted.head_lt {x : Item} {S : List Item} (h : Sorted (x :: S)) : ∀ y ∈ S, lexLt x y = true :=
  (List.pairwise_cons.mp h).1

theorem Sorted.nodup {S : List Item} (h : Sorted S) : S.Nodup :=
  h.imp (fun {a b} hab => lexLt_ne a b hab)

/-- Items at or above a bound stay at or above it up the index. -/
theorem not_lt_of_lt {x y b : Item} (hxy : lexLt x y = true) (hx : lexLt x b = false) : lexLt y b = false := by
  cases h : lexLt y b with
  | false => rfl
  | true => have := lexLt_trans _ _ _ hxy h; simp [hx] at this

theorem rankOf_cons (x : Item) (S : List Item) (b : Item) :
    rankOf (x :: S) b = if lexLt x b = true then rankOf S b + 1 else (S.filter (fun y => lexLt y b)).length := by
  unfold rankOf
  by_cases h : lexLt x b = true <;> simp [h]

theorem rankOf_cons_ge {x : Item} {S : List Item} {b : Item} (hs : Sorted (x :: S)) (h : lexLt x b = false) :
    rankOf (x :: S) b = 0 := by
  rw [rankOf_cons]; simp only [h]; simp only [Bool.false_eq_true, ↓reduceIte]
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro y hy; simp [not_lt_of_lt (hs.head_lt y hy) h]

theorem rankOf_cons_lt {x : Item} {S : List Item} {b : Item} (h : lexLt x b = true) :
    rankOf (x :: S) b = rankOf S b + 1 := by
  rw [rankOf_cons]; simp [h]

theorem rankOf_le (S : List Item) (b : Item) : rankOf S b ≤ S.length := List.length_filter_le _ _

/-- Membership of a range `lo..hi` (`hi = none` is infinity). -/
def inRange (lo : Item) (hi : Option Item) (x : Item) : Bool :=
  !lexLt x lo && (match hi with | none => true | some h => lexLt x h)

/-- The rank of the upper bound (the item count for infinity). -/
def rankHi (S : List Item) (hi : Option Item) : Nat :=
  match hi with | none => S.length | some h => rankOf S h

/-- The items of a range are the slice between the ranks of its bounds. -/
theorem slice_eq_filter (lo : Item) (hi : Option Item) :
    ∀ S : List Item, Sorted S →
      (S.drop (rankOf S lo)).take (rankHi S hi - rankOf S lo) = S.filter (inRange lo hi)
  | [], _ => by cases hi <;> simp [rankOf, rankHi]
  | x :: S, hs => by
    have ih := slice_eq_filter lo hi S hs.tail
    by_cases hxl : lexLt x lo = true
    · rw [rankOf_cons_lt hxl]
      have hin : inRange lo hi x = false := by simp [inRange, hxl]
      rw [List.filter_cons_of_neg (by simp [hin])]
      cases hi with
      | none =>
        simp only [rankHi, List.length_cons] at ih ⊢
        simpa using ih
      | some h =>
        by_cases hxh : lexLt x h = true
        · simp only [rankHi] at ih ⊢
          rw [rankOf_cons_lt hxh]
          simpa using ih
        · have hxh' : lexLt x h = false := by simpa using hxh
          simp only [rankHi]
          rw [rankOf_cons_ge hs hxh']
          have : S.filter (inRange lo (some h)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro y hy
            simp [inRange, not_lt_of_lt (hs.head_lt y hy) hxh']
          simp [this]
    · have hxl' : lexLt x lo = false := by simpa using hxl
      rw [rankOf_cons_ge hs hxl']
      have hS : rankOf S lo = 0 := by
        unfold rankOf
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro y hy; simp [not_lt_of_lt (hs.head_lt y hy) hxl']
      rw [hS] at ih
      cases hi with
      | none =>
        have hin : inRange lo none x = true := by simp [inRange, hxl']
        rw [List.filter_cons_of_pos (by simp [hin])]
        simp only [rankHi, List.length_cons, Nat.sub_zero, List.drop_zero] at ih ⊢
        rw [List.take_succ_cons]; simpa using ih
      | some h =>
        by_cases hxh : lexLt x h = true
        · have hin : inRange lo (some h) x = true := by simp [inRange, hxl', hxh]
          rw [List.filter_cons_of_pos (by simp [hin])]
          simp only [rankHi, Nat.sub_zero, List.drop_zero] at ih ⊢
          rw [rankOf_cons_lt hxh, List.take_succ_cons]; simpa using ih
        · have hxh' : lexLt x h = false := by simpa using hxh
          simp only [rankHi]
          rw [rankOf_cons_ge hs hxh']
          have hin : inRange lo (some h) x = false := by simp [inRange, hxh']
          rw [List.filter_cons_of_neg (by simp [hin])]
          have : S.filter (inRange lo (some h)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro y hy
            simp [inRange, not_lt_of_lt (hs.head_lt y hy) hxh']
          simp [this]

end Vinc.Reconcile
