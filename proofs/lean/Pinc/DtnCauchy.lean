import Pinc.Axioms

/-!
# The Cauchy matrix of the Reed-Solomon code and its closed-form inverse

Over any field `K` of characteristic 2 (the bytes of GF(2^8) are one, see `DtnGfField`): for distinct nodes
`x_0 .. x_{e-1}` and `y_0 .. y_{e-1}` with no `x` equal to a `y`, the matrix `A[t][s] = 1 / (x_t + y_s)` has the inverse
`B[s][t] = F_s G_t / (x_t + y_s)` with `F_s = prod_l (y_s + x_l) / prod_{l != s} (y_s + y_l)` and
`G_t = prod_l (x_t + y_l) / prod_{l != t} (x_t + x_l)`: the closed form `reconstruct` in `rs.rs` evaluates (`prodSum` is
`prod_sum`, `prodSkip` is `prod_sum_skip`, `fF` is `f_factor`, `gF` is `g_factor`). Both `B A = I` and `A B = I` are
proved, for every size `e`, by a partial-fraction identity (`pf`) shown by induction on the nodes.
-/

open Lean.Grind
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace Pinc.DtnCauchy
variable {K : Type} [Field K] [IsCharP K 2]

theorem add_self' (a : K) : a + a = 0 := by grind
theorem eq_of_add_zero {a b : K} (h : a + b = 0) : a = b := by grind
theorem ne_of_add_ne {a b : K} (h : a ≠ b) : a + b ≠ 0 := fun h' => h (eq_of_add_zero h')
theorem mul_ne_zero' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by grind

/-- `prod_l (v + a_l)`: `prod_sum` of `rs.rs`. -/
def prodSum (v : K) (l : List K) : K := l.foldl (fun acc x => acc * (v + x)) 1

theorem foldl_acc (v : K) (r : List K) : ∀ c : K, r.foldl (fun acc x => acc * (v + x)) c = c * prodSum v r := by
  induction r with
  | nil => intro c; simp [prodSum]; grind
  | cons a r ih =>
    intro c
    simp only [prodSum, List.foldl_cons] at *
    rw [ih, ih (1 * (v + a))]; grind

theorem prodSum_nil (v : K) : prodSum v [] = 1 := rfl
theorem prodSum_cons (v a : K) (r : List K) : prodSum v (a :: r) = (v + a) * prodSum v r := by
  show List.foldl _ (1 * (v + a)) r = _
  rw [foldl_acc]; grind

/-- The fold of `prod_sum_skip` from index `n`. -/
def ps (v : K) (l : List (K × Nat)) : K := l.foldl (fun acc p => acc * (v + p.1)) 1

/-- `prod_{l != skip} (v + a_l)`: `prod_sum_skip` of `rs.rs` (enumerate, filter, fold). -/
def prodSkip (v : K) (a : List K) (skip : Nat) : K := ps v ((a.zipIdx).filter fun p => p.2 ≠ skip)

theorem ps_cons (v : K) (p : K × Nat) (l : List (K × Nat)) : ps v (p :: l) = (v + p.1) * ps v l := by
  simp only [ps, List.foldl_cons]
  have : ∀ c : K, l.foldl (fun acc p => acc * (v + p.1)) c = c * ps v l := by
    induction l with
    | nil => intro c; simp [ps]; grind
    | cons q l ih => intro c; simp only [ps, List.foldl_cons] at *; rw [ih, ih (1 * (v + q.1))]; grind
  rw [this]; grind

theorem ps_nil (v : K) : ps v ([] : List (K × Nat)) = 1 := rfl

/-- The skip product of a list from index `n`. -/
def pk (v : K) (l : List K) (n s : Nat) : K := ps v ((l.zipIdx n).filter fun p => p.2 ≠ s)

theorem pk_nil (v : K) (n s : Nat) : pk v [] n s = 1 := by simp [pk, ps_nil]

theorem pk_cons (v a : K) (l : List K) (n s : Nat) :
    pk v (a :: l) n s = if n = s then pk v l (n + 1) s else (v + a) * pk v l (n + 1) s := by
  by_cases h : n = s
  · simp [pk, List.zipIdx_cons, List.filter_cons, h]
  · simp [pk, List.zipIdx_cons, List.filter_cons, h, ps_cons]

theorem pk_gt (v : K) (l : List K) : ∀ n s, s < n → pk v l n s = prodSum v l := by
  induction l with
  | nil => intro n s _; simp [pk_nil, prodSum_nil]
  | cons a l ih =>
    intro n s h
    rw [pk_cons, if_neg (by omega), ih (n + 1) s (by omega), prodSum_cons]

theorem pk_shift (v : K) (l : List K) : ∀ n s, pk v l (n + 1) (s + 1) = pk v l n s := by
  induction l with
  | nil => intro n s; simp [pk_nil]
  | cons a l ih =>
    intro n s
    rw [pk_cons, pk_cons]
    by_cases h : n = s
    · simp [h, ih]
    · have : ¬ (n + 1 = s + 1) := by omega
      simp [h, this, ih]

theorem prodSkip_eq (v : K) (a : List K) (s : Nat) : prodSkip v a s = pk v a 0 s := rfl

theorem prodSkip_cons_zero (v a : K) (l : List K) : prodSkip v (a :: l) 0 = prodSum v l := by
  rw [prodSkip_eq, pk_cons, if_pos rfl, pk_gt v l 1 0 (by omega)]

theorem prodSkip_cons_succ (v a : K) (l : List K) (t : Nat) :
    prodSkip v (a :: l) (t + 1) = (v + a) * prodSkip v l t := by
  rw [prodSkip_eq, pk_cons, if_neg (by omega), pk_shift, ← prodSkip_eq]

/-- Removing the factor of index `s` from the full product. -/
theorem prodSum_eq_skip (v : K) (a : List K) : ∀ s, s < a.length → prodSum v a = (v + a.getD s 0) * prodSkip v a s := by
  induction a with
  | nil => intro s h; simp at h
  | cons x l ih =>
    intro s h
    cases s with
    | zero => rw [prodSum_cons, prodSkip_cons_zero]; simp
    | succ s =>
      rw [prodSum_cons, prodSkip_cons_succ, ih s (by simpa using h)]
      simp; grind

theorem prodSkip_eraseIdx (v : K) (a : List K) : ∀ s, s < a.length → prodSkip v a s = prodSum v (a.eraseIdx s) := by
  induction a with
  | nil => intro s h; simp at h
  | cons x l ih =>
    intro s h
    cases s with
    | zero => rw [prodSkip_cons_zero]; simp
    | succ s => rw [prodSkip_cons_succ, ih s (by simpa using h)]; simp [prodSum_cons]

theorem prodSum_mem (v : K) (l : List K) (h : v ∈ l) : prodSum v l = 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [prodSum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · grind
    · rw [ih h]; grind

theorem prodSum_ne (v : K) (l : List K) (h : ∀ x ∈ l, v + x ≠ 0) : prodSum v l ≠ 0 := by
  induction l with
  | nil => rw [prodSum_nil]; grind
  | cons a l ih =>
    rw [prodSum_cons]
    exact mul_ne_zero' (h a (by simp)) (ih fun x hx => h x (by simp [hx]))


/-! ### Sums over indices and the partial-fraction identity -/

/-- `sum_{t < n} f t`, peeled from the front. -/
def sumTo : Nat → (Nat → K) → K
  | 0, _ => 0
  | n + 1, f => f 0 + sumTo n fun t => f (t + 1)

theorem sumTo_zero (f : Nat → K) : sumTo 0 f = 0 := rfl
theorem sumTo_succ (n : Nat) (f : Nat → K) : sumTo (n + 1) f = f 0 + sumTo n fun t => f (t + 1) := rfl

theorem sumTo_congr (n : Nat) : ∀ (f g : Nat → K), (∀ t, t < n → f t = g t) → sumTo n f = sumTo n g := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro f g h
    rw [sumTo_succ, sumTo_succ, h 0 (by omega), ih (fun t => f (t + 1)) (fun t => g (t + 1)) fun t ht => h (t + 1) (by omega)]

theorem sumTo_add (n : Nat) : ∀ (f g : Nat → K), sumTo n (fun t => f t + g t) = sumTo n f + sumTo n g := by
  induction n with
  | zero => intros; simp [sumTo_zero]; grind
  | succ n ih => intro f g; rw [sumTo_succ, sumTo_succ, sumTo_succ, ih (fun t => f (t + 1)) (fun t => g (t + 1))]; grind

theorem sumTo_mul (n : Nat) : ∀ (c : K) (f : Nat → K), sumTo n (fun t => c * f t) = c * sumTo n f := by
  induction n with
  | zero => intros; simp [sumTo_zero]; grind
  | succ n ih => intro c f; rw [sumTo_succ, sumTo_succ, ih c (fun t => f (t + 1))]; grind

/-- `D_u(t) = prod_{l != t} (u_t + u_l)`. -/
def dd (u : List K) (t : Nat) : K := prodSkip (u.getD t 0) u t

theorem dd_cons_zero (a : K) (u : List K) : dd (a :: u) 0 = prodSum a u := by
  simp [dd, prodSkip_cons_zero]

theorem dd_cons_succ (a : K) (u : List K) (t : Nat) : dd (a :: u) (t + 1) = (u.getD t 0 + a) * dd u t := by
  simp [dd, prodSkip_cons_succ]

theorem dd_ne (u : List K) (hu : u.Nodup) : ∀ t, t < u.length → dd u t ≠ 0 := by
  induction u with
  | nil => intro t h; simp at h
  | cons a u ih =>
    have hnd := List.nodup_cons.mp hu
    intro t ht
    cases t with
    | zero =>
      rw [dd_cons_zero]
      exact prodSum_ne _ _ fun x hx => ne_of_add_ne (fun h => hnd.1 (h ▸ hx))
    | succ t =>
      rw [dd_cons_succ]
      have hm : u.getD t 0 ∈ u := by
        have h' : t < u.length := by simpa using ht
        simp [List.getD_eq_getElem?_getD, h']
      exact mul_ne_zero' (ne_of_add_ne (fun h => hnd.1 (h ▸ hm))) (ih hnd.2 t (by simpa using ht))

/-- One term of the partial-fraction sum: `P_v(u_t) / (D_u(t) (z + u_t))`. -/
def tt (u v : List K) (z : K) (t : Nat) : K := prodSum (u.getD t 0) v / dd u t / (z + u.getD t 0)

/-- `sum_t P_v(u_t) / (D_u(t) (z + u_t))`. -/
def T (u v : List K) (z : K) : K := sumTo u.length (tt u v z)

/-- The moment sum `sum_t P_v(u_t) / D_u(t)`. -/
def M (u v : List K) : K := sumTo u.length fun t => prodSum (u.getD t 0) v / dd u t

theorem T_cons (a : K) (u v : List K) (z : K) :
    T (a :: u) v z = prodSum a v / prodSum a u / (z + a) + sumTo u.length (fun t => tt (a :: u) v z (t + 1)) := by
  simp only [T, List.length_cons, sumTo_succ, tt, dd_cons_zero, List.getD_cons_zero]

theorem M_cons (a : K) (u v : List K) :
    M (a :: u) v = prodSum a v / prodSum a u + sumTo u.length (fun t => prodSum (u.getD t 0) v / ((u.getD t 0 + a) * dd u t)) := by
  simp only [M, List.length_cons, sumTo_succ, dd_cons_zero, List.getD_cons_zero, dd_cons_succ, List.getD_cons_succ]


theorem getD_mem (u : List K) (t : Nat) (h : t < u.length) : u.getD t 0 ∈ u := by
  simp [List.getD_eq_getElem?_getD, h]

/-- `z` is not a node. -/
def Away (z : K) (u : List K) : Prop := ∀ x ∈ u, z + x ≠ 0

theorem Away_of_nodup {a : K} {u : List K} (h : (a :: u).Nodup) : Away a u := by
  have hn := List.nodup_cons.mp h
  intro x hx
  exact ne_of_add_ne (fun e => hn.1 (by rw [e]; exact hx))

theorem pf_term (P d w z a : K) (h1 : z + a ≠ 0) (h2 : w + a ≠ 0) (h3 : z + w ≠ 0) (h4 : d ≠ 0) (h5 : a + w ≠ 0) :
    P / ((w + a) * d) / (z + w) = 1 / (z + a) * (P / d / (z + w) + P / d / (a + w)) := by grind

theorem T_step (a : K) (u v : List K) (z : K) (hnd : (a :: u).Nodup) (hz : Away z u) (hza : z + a ≠ 0) :
    T (a :: u) v z = prodSum a v / prodSum a u / (z + a) + 1 / (z + a) * (T u v z + T u v a) := by
  have hnd' := List.nodup_cons.mp hnd
  have haw := Away_of_nodup hnd
  rw [T_cons]
  congr 1
  have : sumTo u.length (fun t => tt (a :: u) v z (t + 1)) =
      sumTo u.length (fun t => 1 / (z + a) * (tt u v z t + tt u v a t)) := by
    apply sumTo_congr
    intro t ht
    have hm := getD_mem u t ht
    simp only [tt, dd_cons_succ, List.getD_cons_succ]
    exact pf_term _ _ _ _ _ hza (ne_of_add_ne (fun e => hnd'.1 (by rw [← e]; exact hm)))
      (hz _ hm) (dd_ne u hnd'.2 t ht) (haw _ hm)
  rw [this, sumTo_mul, T, T, sumTo_add]

theorem M_step (a : K) (u v : List K) (hnd : (a :: u).Nodup) :
    M (a :: u) v = prodSum a v / prodSum a u + T u v a := by
  have hnd' := List.nodup_cons.mp hnd
  have haw := Away_of_nodup hnd
  rw [M_cons]
  congr 1
  apply sumTo_congr
  intro t ht
  have hm := getD_mem u t ht
  have h1 := dd_ne u hnd'.2 t ht
  have h2 : u.getD t 0 + a ≠ 0 := ne_of_add_ne (fun e => hnd'.1 (by rw [← e]; exact hm))
  have h3 : a + u.getD t 0 ≠ 0 := haw _ hm
  simp only [tt]
  grind

theorem tt_cons_v (u : List K) (v0 : K) (v : List K) (z : K) (t : Nat) (h1 : z + u.getD t 0 ≠ 0) (h2 : dd u t ≠ 0) :
    tt u (v0 :: v) z t = (z + v0) * tt u v z t + prodSum (u.getD t 0) v / dd u t := by
  simp only [tt, prodSum_cons]
  grind

/-- The partial-fraction identity: for distinct nodes `u` and `z` away from them, `sum_t P_v(u_t)/(D_u(t)(z+u_t))`
is `P_v(z)/P_u(z)` when `v` has fewer factors than `u` has nodes, and that plus 1 when it has as many. -/
theorem pf : ∀ (u : List K), u.Nodup → ∀ (v : List K) (z : K), Away z u →
    (v.length < u.length → T u v z = prodSum z v / prodSum z u) ∧
    (v.length = u.length → T u v z = prodSum z v / prodSum z u + 1) := by
  intro u
  induction u with
  | nil =>
    intro _ v z _
    constructor
    · intro h; simp at h
    · intro h
      have : v = [] := List.length_eq_zero_iff.mp (by simpa using h)
      subst this
      simp [T, sumTo_zero, prodSum_nil]; grind
  | cons a u ih =>
    intro hnd v z hz
    have hnd' := List.nodup_cons.mp hnd
    have hzu : Away z u := fun x hx => hz x (List.mem_cons_of_mem _ hx)
    have hza : z + a ≠ 0 := hz a (by simp)
    have haw : Away a u := Away_of_nodup hnd
    have hPa : prodSum a u ≠ 0 := prodSum_ne _ _ haw
    have hPz : prodSum z u ≠ 0 := prodSum_ne _ _ hzu
    have proper : ∀ v : List K, v.length < u.length + 1 → T (a :: u) v z = prodSum z v / prodSum z (a :: u) := by
      intro v hv
      rw [T_step a u v z hnd hzu hza, prodSum_cons]
      rcases Nat.lt_or_ge v.length u.length with hl | hl
      · rw [((ih hnd'.2 v z hzu).1 hl), ((ih hnd'.2 v a haw).1 hl)]
        grind
      · have hl' : v.length = u.length := by omega
        rw [((ih hnd'.2 v z hzu).2 hl'), ((ih hnd'.2 v a haw).2 hl')]
        grind
    refine ⟨fun h => proper v (by simpa using h), fun h => ?_⟩
    cases v with
    | nil => simp at h
    | cons v0 v' =>
      have hv' : v'.length = u.length := by simpa using h
      have hsplit : T (a :: u) (v0 :: v') z = (z + v0) * T (a :: u) v' z + M (a :: u) v' := by
        rw [T, T, M, ← sumTo_mul, ← sumTo_add]
        apply sumTo_congr
        intro t ht
        have hm : (a :: u).getD t 0 ∈ a :: u := getD_mem _ t ht
        exact tt_cons_v (a :: u) v0 v' z t (hz _ hm) (dd_ne _ hnd t ht)
      have hM : M (a :: u) v' = 1 := by
        rw [M_step a u v' hnd, (ih hnd'.2 v' a haw).2 hv']
        grind
      rw [hsplit, hM, proper v' (by omega), prodSum_cons z v0 v', prodSum_cons z a u]
      grind


/-! ### The closed-form inverse of a Cauchy matrix -/

/-- `G_j = prod_l (x_j + y_l) / prod_{l != j} (x_j + x_l)`: `g_factor` of `rs.rs`. -/
def gF (xs ys : List K) (t : Nat) : K := prodSum (xs.getD t 0) ys / prodSkip (xs.getD t 0) xs t

/-- `F_i = prod_l (y_i + x_l) / prod_{l != i} (y_i + y_l)`: `f_factor` of `rs.rs`. -/
def fF (xs ys : List K) (s : Nat) : K := prodSum (ys.getD s 0) xs / prodSkip (ys.getD s 0) ys s

/-- The Cauchy matrix `A[t][s] = 1 / (x_t + y_s)`. -/
def cA (xs ys : List K) (t s : Nat) : K := 1 / (xs.getD t 0 + ys.getD s 0)

/-- The closed-form inverse `B[s][t] = F_s G_t / (x_t + y_s)`. -/
def cB (xs ys : List K) (s t : Nat) : K := fF xs ys s * gF xs ys t / (xs.getD t 0 + ys.getD s 0)

/-- The nodes are distinct inside each list and no `x` equals a `y`. -/
structure Nodes (xs ys : List K) : Prop where
  nx : xs.Nodup
  ny : ys.Nodup
  disj : ∀ x ∈ xs, ∀ y ∈ ys, x + y ≠ 0
  len : xs.length = ys.length

theorem Nodes.swap {xs ys : List K} (h : Nodes xs ys) : Nodes ys xs :=
  ⟨h.ny, h.nx, fun y hy x hx => by have := h.disj x hx y hy; grind, h.len.symm⟩

theorem getD_ne (u : List K) (hu : u.Nodup) (i j : Nat) (hi : i < u.length) (hj : j < u.length) (hij : i ≠ j) :
    u.getD i 0 + u.getD j 0 ≠ 0 := by
  apply ne_of_add_ne
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some]
  intro h
  exact hij ((List.Nodup.getElem_inj hu).mp h)

theorem Nodes.xy {xs ys : List K} (h : Nodes xs ys) (t s : Nat) (ht : t < xs.length) (hs : s < ys.length) :
    xs.getD t 0 + ys.getD s 0 ≠ 0 := h.disj _ (getD_mem _ _ ht) _ (getD_mem _ _ hs)

/-- `sum_t G_t / (x_t + y_s) = 1`. -/
theorem row_sum {xs ys : List K} (h : Nodes xs ys) (s : Nat) (hs : s < ys.length) :
    sumTo xs.length (fun t => gF xs ys t / (xs.getD t 0 + ys.getD s 0)) = 1 := by
  have hys : ys.getD s 0 ∈ ys := getD_mem _ _ hs
  have key := (pf xs h.nx ys (ys.getD s 0) (fun x hx => by
    have := h.disj x hx _ hys; grind)).2 h.len.symm
  have h0 : prodSum (ys.getD s 0) ys = 0 := prodSum_mem _ _ hys
  have : T xs ys (ys.getD s 0) = 1 := by rw [key, h0]; grind
  rw [← this, T]
  apply sumTo_congr
  intro t ht
  have h1 := h.xy t s ht hs
  have hd : dd xs t ≠ 0 := dd_ne xs h.nx t ht
  simp only [tt, gF, dd]
  have : ys.getD s 0 + xs.getD t 0 = xs.getD t 0 + ys.getD s 0 := by grind
  rw [this]

theorem diag_sum {xs ys : List K} (h : Nodes xs ys) (s : Nat) (hs : s < ys.length) :
    fF xs ys s * sumTo xs.length (fun t => gF xs ys t / ((xs.getD t 0 + ys.getD s 0) * (xs.getD t 0 + ys.getD s 0))) = 1 := by
  have hys : ys.getD s 0 ∈ ys := getD_mem _ _ hs
  have hlen : (ys.eraseIdx s).length < xs.length := by
    rw [List.length_eraseIdx_of_lt hs]; have := h.len; omega
  have key := (pf xs h.nx (ys.eraseIdx s) (ys.getD s 0) (fun x hx => by
    have := h.disj x hx _ hys; grind)).1 hlen
  have hsum : sumTo xs.length (fun t => gF xs ys t / ((xs.getD t 0 + ys.getD s 0) * (xs.getD t 0 + ys.getD s 0))) =
      T xs (ys.eraseIdx s) (ys.getD s 0) := by
    rw [T]
    apply sumTo_congr
    intro t ht
    have h1 := h.xy t s ht hs
    have hd : dd xs t ≠ 0 := dd_ne xs h.nx t ht
    simp only [tt, gF, dd] at *
    have e1 := prodSum_eq_skip (xs.getD t 0) ys s hs
    have e2 := prodSkip_eraseIdx (xs.getD t 0) ys s hs
    have e3 : ys.getD s 0 + xs.getD t 0 = xs.getD t 0 + ys.getD s 0 := by grind
    rw [e3, e1, ← e2]; grind
  rw [hsum, key]
  have e2 := prodSkip_eraseIdx (ys.getD s 0) ys s hs
  have hd : prodSkip (ys.getD s 0) ys s ≠ 0 := dd_ne ys h.ny s hs
  have hp : prodSum (ys.getD s 0) xs ≠ 0 := prodSum_ne _ _ (fun x hx => by
    have := h.disj x hx _ hys; grind)
  simp only [fF]
  rw [← e2]
  grind

theorem offdiag_sum {xs ys : List K} (h : Nodes xs ys) (s r : Nat) (hs : s < ys.length) (hr : r < ys.length) (hsr : s ≠ r) :
    sumTo xs.length (fun t => gF xs ys t / ((xs.getD t 0 + ys.getD s 0) * (xs.getD t 0 + ys.getD r 0))) = 0 := by
  have hy := getD_ne ys h.ny s r hs hr hsr
  have : sumTo xs.length (fun t => gF xs ys t / ((xs.getD t 0 + ys.getD s 0) * (xs.getD t 0 + ys.getD r 0))) =
      sumTo xs.length (fun t => 1 / (ys.getD s 0 + ys.getD r 0) *
        (gF xs ys t / (xs.getD t 0 + ys.getD s 0) + gF xs ys t / (xs.getD t 0 + ys.getD r 0))) := by
    apply sumTo_congr
    intro t ht
    have h1 := h.xy t s ht hs
    have h2 := h.xy t r ht hr
    grind
  rw [this, sumTo_mul, sumTo_add, row_sum h s hs, row_sum h r hr]
  grind

/-- `B A = I`: the closed form of `reconstruct` is a left inverse of the Cauchy matrix. -/
theorem cauchy_BA {xs ys : List K} (h : Nodes xs ys) (s r : Nat) (hs : s < ys.length) (hr : r < ys.length) :
    sumTo xs.length (fun t => cB xs ys s t * cA xs ys t r) = if s = r then 1 else 0 := by
  have hf : sumTo xs.length (fun t => cB xs ys s t * cA xs ys t r) =
      fF xs ys s * sumTo xs.length (fun t => gF xs ys t / ((xs.getD t 0 + ys.getD s 0) * (xs.getD t 0 + ys.getD r 0))) := by
    rw [← sumTo_mul]
    apply sumTo_congr
    intro t ht
    have h1 := h.xy t s ht hs
    have h2 := h.xy t r ht hr
    simp only [cB, cA]
    grind
  rw [hf]
  by_cases hsr : s = r
  · subst hsr; rw [if_pos rfl]; exact diag_sum h s hs
  · rw [if_neg hsr, offdiag_sum h s r hs hr hsr]; grind

/-- `A B = I`: and a right inverse, by the same identity with the roles of `x` and `y` exchanged. -/
theorem cauchy_AB {xs ys : List K} (h : Nodes xs ys) (t u : Nat) (ht : t < xs.length) (hu : u < xs.length) :
    sumTo ys.length (fun s => cA xs ys t s * cB xs ys s u) = if t = u then 1 else 0 := by
  have hs := h.swap
  have e := cauchy_BA hs u t (by simpa using hu) (by simpa using ht)
  have hf : sumTo ys.length (fun s => cA xs ys t s * cB xs ys s u) =
      sumTo ys.length (fun s => cB ys xs u s * cA ys xs s t) := by
    apply sumTo_congr
    intro s hs'
    have h1 := h.xy t s ht (by simpa using hs')
    have h2 := h.xy u s hu (by simpa using hs')
    have h3 : ys.getD s 0 + xs.getD t 0 = xs.getD t 0 + ys.getD s 0 := by grind
    have h4 : ys.getD s 0 + xs.getD u 0 = xs.getD u 0 + ys.getD s 0 := by grind
    have d1 : prodSkip (xs.getD t 0) xs t ≠ 0 := dd_ne xs h.nx t ht
    have d2 : prodSkip (xs.getD u 0) xs u ≠ 0 := dd_ne xs h.nx u hu
    have d3 : prodSkip (ys.getD s 0) ys s ≠ 0 := dd_ne ys h.ny s (by simpa using hs')
    simp only [cB, cA, fF, gF, h3, h4]
    grind
  rw [hf, e]
  by_cases htu : t = u
  · subst htu; simp
  · rw [if_neg htu, if_neg (fun e => htu e.symm)]


#audit_axioms Pinc.DtnCauchy.pf
#audit_axioms Pinc.DtnCauchy.cauchy_BA
#audit_axioms Pinc.DtnCauchy.cauchy_AB

end Pinc.DtnCauchy
