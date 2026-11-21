import Pinc.ReconcileApsSplit
import Pinc.ReconcileSession

/-!
# Reconcile refinement, part 1: the split loop of the byte machine writes exactly `splitIvs`

`splitParts` (the Lean mirror of `split` in core.rs) cuts the receiver's index slice `a..b` with the index loop
`x, y = min b (x + step)`, a separator `q[..cpl p q + 1]` between `S[y-1]` and `S[y]`, and the fingerprint of the slice
`x..y`. `splitParts_spec` proves that, for a sorted index whose items fit the item limit, the loop succeeds and its
output is the concatenation of the part encodings of the intervals of the abstract part system (`ivsOf` over the
blocks of the slice, the interval logic `splitIvs` of ReconcileApsSplit) with the fingerprint of each block, and that
it counts exactly those parts. This is the link of the split arm to the abstract part system; the other arms of the
refinement (leaf decisions, merges, replies, frames, handlers and the driver) are NOT proved here: they are covered
by TLC and trace validation only.
-/

namespace Pinc.Reconcile

/-- The part encodings of a list of intervals with their fingerprint bytes, threading the previous bound. -/
def encFps : Item → List (Iv × List Nat) → List Nat × Item
  | last, [] => ([], last)
  | last, (J, f) :: r =>
    let (bs, l1) := putHead last tFP J.lo J.hi
    let (rest, l2) := encFps l1 r
    (bs ++ f ++ rest, l2)

theorem chunkBy_fuel (step : Nat) (hs : 1 ≤ step) :
    ∀ (f g : Nat) (L : List Item), L.length ≤ f → L.length ≤ g → chunkBy step f L = chunkBy step g L
  | 0, g, L, hf, hg => by
    have : L = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; cases g <;> simp [chunkBy]
  | f + 1, 0, L, hf, hg => by
    have : L = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; simp [chunkBy]
  | f + 1, g + 1, L, hf, hg => by
    unfold chunkBy
    by_cases hL : L = []
    · simp [hL]
    · simp only [hL, ↓reduceIte]
      rw [chunkBy_fuel step hs f g (L.drop step) (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega)]

theorem drop_take_slice (S : List Item) (x b s : Nat) (h : x + s ≤ b) :
    ((S.drop x).take (b - x)).drop s = (S.drop (x + s)).take (b - (x + s)) := by
  rw [List.drop_take, List.drop_drop]
  congr 1 <;> omega

theorem take_take_slice (S : List Item) (x b s : Nat) :
    ((S.drop x).take (b - x)).take s = (S.drop x).take (min s (b - x)) := by
  rw [List.take_take]

theorem readItem_ok (lim : Limits) (S : List Item) (hlen : ∀ x ∈ S, x.length ≤ lim.maxItem) (i : Nat)
    (h : i < S.length) : readItem lim S i = .ok (S[i]'h) := by
  have hm := hlen _ (List.getElem_mem (h := h))
  simp [readItem, List.getElem?_eq_getElem h, hm]

theorem ivsOf_two (hi : Option Item) (l : Item) (b1 : List Item) (bl' : List (List Item)) (p q : Item)
    (hp : b1.getLast? = some p) (hq : (bl'.head?).bind List.head? = some q) :
    ivsOf hi l (b1 :: bl') = ⟨l, some (q.take (cpl p q + 1))⟩ :: ivsOf hi (q.take (cpl p q + 1)) bl' := by
  cases bl' with
  | nil => simp at hq
  | cons b2 rest =>
    simp at hq
    simp [ivsOf, hp, hq]

theorem chunkBy_cons (step : Nat) (L : List Item) (hL : L ≠ []) :
    chunkBy step L.length L = L.take step :: chunkBy step (L.length - 1) (L.drop step) := by
  obtain ⟨n, hn⟩ : ∃ n, L.length = n + 1 := ⟨L.length - 1, by have := List.length_pos_iff.mpr hL; omega⟩
  rw [hn, Nat.add_sub_cancel, chunkBy]; simp [hL]

theorem getLast_take_slice (S : List Item) (x step : Nat) (h : x + step ≤ S.length) (hs : 1 ≤ step) :
    ((S.drop x).take step).getLast? = S[x + step - 1]? := by
  have hl : ((S.drop x).take step).length = step := by
    simp only [List.length_take, List.length_drop]; omega
  rw [List.getLast?_eq_getElem?, hl, List.getElem?_take_of_lt (by omega), List.getElem?_drop]
  congr 1; omega

theorem head_take_slice (S : List Item) (y m : Nat) (hm : 1 ≤ m) :
    ((S.drop y).take m).head? = S[y]? := by
  rw [List.head?_take, if_neg (by omega), List.head?_drop]

theorem splitGo_spec (o : Oracle) (lim : Limits) (S : List Item) (hS : Sorted S)
    (hlen : ∀ x ∈ S, x.length ≤ lim.maxItem) (hi : Option Item) (b step : Nat) (hb : b ≤ S.length) (hs : 1 ≤ step) :
    ∀ (fuel x : Nat) (l : Item) (out : Out) (cnt : Nat), x ≤ b → b - x + 1 ≤ fuel →
      splitParts.go o lim S hi b step x l out cnt fuel = .ok
        ({ out with
            body := out.body ++ (encFps out.last ((ivsOf hi l (chunkBy step ((S.drop x).take (b - x)).length ((S.drop x).take (b - x)))).zip
              ((chunkBy step ((S.drop x).take (b - x)).length ((S.drop x).take (b - x))).map fun B => fpBytes (o.enc (sumH B) B.length)))).1,
            last := (encFps out.last ((ivsOf hi l (chunkBy step ((S.drop x).take (b - x)).length ((S.drop x).take (b - x)))).zip
              ((chunkBy step ((S.drop x).take (b - x)).length ((S.drop x).take (b - x))).map fun B => fpBytes (o.enc (sumH B) B.length)))).2 },
         cnt + (chunkBy step ((S.drop x).take (b - x)).length ((S.drop x).take (b - x))).length) := by
  intro fuel
  induction fuel with
  | zero => intro x l out cnt hx hf; omega
  | succ f ih =>
    intro x l out cnt hx hf
    by_cases hxb : x < b
    · have hLlen : ((S.drop x).take (b - x)).length = b - x := by
        simp only [List.length_take, List.length_drop]; omega
      have hLne : (S.drop x).take (b - x) ≠ [] := by intro h; rw [h] at hLlen; simp at hLlen; omega
      by_cases hy : x + step < b
      · have hy' : min b (x + step) = x + step := by omega
        have h1 : x + step - 1 < S.length := by omega
        have h2 : x + step < S.length := by omega
        have hpq : lexLt (S[x + step - 1]'h1) (S[x + step]'h2) = true :=
          List.pairwise_iff_getElem.mp hS (x + step - 1) (x + step) h1 h2 (by omega)
        have hk : cpl (S[x + step - 1]'h1) (S[x + step]'h2) + 1 ≤ (S[x + step]'h2).length := by
          have := alg_cpl_lt_right _ _ hpq; omega
        have hL' : ((S.drop x).take (b - x)).drop step = (S.drop (x + step)).take (b - (x + step)) :=
          drop_take_slice S x b step (by omega)
        have hL'ne : (S.drop (x + step)).take (b - (x + step)) ≠ [] := by
          intro h
          have : ((S.drop (x + step)).take (b - (x + step))).length = 0 := by rw [h]; rfl
          simp only [List.length_take, List.length_drop] at this; omega
        have hfuel := chunkBy_fuel step hs (((S.drop x).take (b - x)).length - 1)
          (((S.drop (x + step)).take (b - (x + step))).length)
          (((S.drop x).take (b - x)).drop step) (by rw [List.length_drop]; omega)
          (Nat.le_of_eq (by rw [hL']))
        rw [hL'] at hfuel
        have hbl' := chunkBy_cons step _ hL'ne
        have htake : ((S.drop x).take (b - x)).take step = (S.drop x).take step := by
          rw [List.take_take]; congr 1; omega
        have hlast : (((S.drop x).take (b - x)).take step).getLast? = some (S[x + step - 1]'h1) := by
          rw [htake, getLast_take_slice S x step (by omega) hs, List.getElem?_eq_getElem h1]
        have hhead : ((chunkBy step ((S.drop (x + step)).take (b - (x + step))).length
            ((S.drop (x + step)).take (b - (x + step)))).head?).bind List.head? = some (S[x + step]'h2) := by
          rw [hbl']
          simp only [List.head?_cons, Option.bind_some]
          have : ((S.drop (x + step)).take (b - (x + step))).take step = (S.drop (x + step)).take (min step (b - (x + step))) := by
            rw [List.take_take, Nat.min_comm]
          rw [this, head_take_slice S (x + step) _ (by omega), List.getElem?_eq_getElem h2]
        rw [chunkBy_cons step _ hLne, hL', hfuel]
        rw [ivsOf_two hi l _ _ _ _ hlast hhead]
        have hfp : fpRange o S x (x + step) = o.enc (sumH (((S.drop x).take (b - x)).take step)) (((S.drop x).take (b - x)).take step).length := by
          rw [htake, fpRange_eq o S (by omega), Nat.add_sub_cancel_left]
        rw [splitParts.go]
        simp only [hxb, if_true, hy', hy, readItem_ok lim S hlen _ h1, readItem_ok lim S hlen _ h2,
          show ¬ (cpl (S[x + step - 1]'h1) (S[x + step]'h2) + 1 > (S[x + step]'h2).length) from by omega, if_false]
        rw [ih (x + step) _ _ _ (by omega) (by omega)]
        simp [encFps, Out.head, hfp, List.zip_cons_cons, List.append_assoc]
        omega
      · have hy' : min b (x + step) = b := by omega
        have hDrop : ((S.drop x).take (b - x)).drop step = [] := by
          rw [List.drop_eq_nil_iff]; simp only [List.length_take, List.length_drop]; omega
        have hTake : ((S.drop x).take (b - x)).take step = (S.drop x).take (b - x) :=
          List.take_of_length_le (by omega)
        have hcb : ∀ n, chunkBy step n ([] : List Item) = [] := fun n => by cases n <;> simp [chunkBy]
        rw [chunkBy_cons step _ hLne, hDrop, hcb, hTake]
        have hfp : fpRange o S x b = o.enc (sumH ((S.drop x).take (b - x))) ((S.drop x).take (b - x)).length :=
          fpRange_eq o S (by omega)
        rw [splitParts.go]
        simp only [hxb, if_true, hy', show ¬ (b < b) from by omega, if_false]
        have hf1 : 1 ≤ f := by omega
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rw [splitParts.go]
        simp [hxb, ivsOf, encFps, Out.head, hfp, List.append_assoc]
    · have hxe : x = b := by omega
      subst hxe
      rw [splitParts.go]
      simp [hxb, chunkBy, ivsOf, encFps]

/-- `splitParts` over the rank range of an interval writes exactly the parts of `splitIvs`, each with the fingerprint
of its block, and counts the blocks. -/
theorem splitParts_spec (o : Oracle) (lim : Limits) (S : List Item) (hS : Sorted S)
    (hlen : ∀ x ∈ S, x.length ≤ lim.maxItem) (I : Iv) (out : Out) (fan : Nat) (hfan : 1 ≤ fan)
    (hab : rankOf S I.lo ≤ rankHi S I.hi) (hb : rankHi S I.hi ≤ S.length) :
    splitParts o lim S out I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) fan = .ok
      ({ out with
          body := out.body ++ (encFps out.last ((splitIvs S I fan).zip
            ((blocksOf S I fan).map fun B => fpBytes (o.enc (sumH B) B.length)))).1,
          last := (encFps out.last ((splitIvs S I fan).zip
            ((blocksOf S I fan).map fun B => fpBytes (o.enc (sumH B) B.length)))).2 },
       (blocksOf S I fan).length) := by
  have hsl := slice_eq_filter I.lo I.hi S hS
  have hL : (S.drop (rankOf S I.lo)).take (rankHi S I.hi - rankOf S I.lo) = I.items S := hsl
  have hcnt : (I.items S).length = rankHi S I.hi - rankOf S I.lo := by
    rw [← hL]; simp only [List.length_take, List.length_drop]; omega
  have hstep : max 1 ((rankHi S I.hi - rankOf S I.lo + fan - 1) / fan) = stepOf (I.items S).length fan := by
    unfold stepOf; rw [hcnt]
  unfold splitParts
  simp only []
  rw [hstep]
  have := splitGo_spec o lim S hS hlen I.hi (rankHi S I.hi) (stepOf (I.items S).length fan) hb
    (by unfold stepOf; omega) (rankHi S I.hi - rankOf S I.lo + 1) (rankOf S I.lo) I.lo out 0 hab (by omega)
  rw [hL] at this
  simpa [splitIvs, blocksOf] using this

/-! ## The leaf decision -/

theorem leafOk_small (lim : Limits) (S : List Item) (lo : Item) (hi : Option Item) (a b : Nat) (items : Bool)
    (h : b - a ≤ 1) : leafOk lim S lo hi a b items = .ok true := by
  unfold leafOk; simp [h]

/-- The concrete `leaf_ok` as a predicate on an interval of a sorted index whose items fit the item limit. -/
def fitsM (lim : Limits) (S : List Item) (items : Bool) (I : Iv) : Prop :=
  leafOk lim S I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) items = .ok true

/-- A range with at most one receiver item always fits: the hypothesis `fits_small` of the abstract system. -/
theorem fitsM_small (lim : Limits) (S : List Item) (hS : Sorted S) (items : Bool) (I : Iv) (h : cnt S I ≤ 1) :
    fitsM lim S items I := by
  have hsl : (S.drop (rankOf S I.lo)).take (rankHi S I.hi - rankOf S I.lo) = I.items S :=
    slice_eq_filter I.lo I.hi S hS
  have hcnt : cnt S I = rankHi S I.hi - rankOf S I.lo := by
    unfold cnt; rw [← hsl]; simp only [List.length_take, List.length_drop]
    have := rankOf_le S I.lo
    have h2 : rankHi S I.hi ≤ S.length := by
      unfold rankHi; cases I.hi <;> simp [rankOf_le]
    omega
  exact leafOk_small lim S I.lo I.hi _ _ items (by omega)

/-- On an index whose items fit the item limit, `leaf_ok` never fails: it answers yes or no. -/
theorem leafOk_total (lim : Limits) (S : List Item) (hlen : ∀ x ∈ S, x.length ≤ lim.maxItem) (lo : Item)
    (hi : Option Item) (a b : Nat) (items : Bool) (hb : b ≤ S.length) :
    ∃ v, leafOk lim S lo hi a b items = .ok v := by
  unfold leafOk
  by_cases h : b - a ≤ 1
  · exact ⟨true, by simp [h]⟩
  · simp only [h, ite_false]
    cases items
    · exact ⟨_, rfl⟩
    · simp only [ite_true]
      have key : ∀ (fuel j size : Nat), j + fuel ≤ S.length → ∃ v, leafOk.go lim S j fuel size = .ok v := by
        intro fuel
        induction fuel with
        | zero => intro j size _; exact ⟨size, by simp [leafOk.go]⟩
        | succ f ih =>
          intro j size hj
          have hj' : j < S.length := by omega
          rw [leafOk.go, readItem_ok lim S hlen j hj']
          exact ih _ _ (by omega)
      have key' : ∀ sz, ∃ v, leafOk.go lim S a (b - a) sz = .ok v := fun sz => key _ _ sz (by omega)
      have key2 : ∀ sz, ∃ v, (match leafOk.go lim S a (b - a) sz with
          | .error e => Except.error e | .ok size => Except.ok (decide (size ≤ lim.cap))) = Except.ok v := fun sz => by
        obtain ⟨w, hw⟩ := key' sz
        exact ⟨decide (w ≤ lim.cap), by rw [hw]⟩
      exact key2 _

end Pinc.Reconcile
