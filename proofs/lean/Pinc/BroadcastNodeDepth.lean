import Pinc.BroadcastNodeSwept

/-!
# Broadcast node: how deep a record sits in the dedupe set

The dedupe set drops records from the front only: on expiry, and to make room when a forced insert finds it full. So
whether a record survives the next inserts depends on how many records sit behind it. This file measures that.

* `depth r l`: the number of entries of `l` behind the first `r`.
* `SeenG`: the invariant of the dedupe set this needs beyond `SeenInv` and `SeenT`: no record twice, and every
  entry of the order belongs to an id whose current record is not older than it. It holds as long as an id is
  recorded only while the set does not hold it, which is what the guard of `SInsertAll` and `SweepIds` and the
  duplicate check of `on_msg` give.
* `D p S now x`: the depth of the live record of `x`, or `none` when `x` is not held.
* `InsRel`: what one insert of an id that was not held does to `D`: the new id is at depth 0, every other id is one
  deeper, an id stays as long as its depth was at most the capacity less two, and nothing else appears
  (`SInsert_rel`).

The second half is arithmetic on `D` alone (`KeepInv`, `DoneInv`): the accounting that `BroadcastNodeEvict` carries
through the eviction loop of the hub log.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Pinc.BroadcastNode

/-! ## Depth in a list -/

/-- The number of entries behind the first `r`. -/
def depth (r : Nat × Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | a :: l => if a = r then some l.length else depth r l

theorem depth_cons_ne {r a : Nat × Nat} {l : List (Nat × Nat)} (h : a ≠ r) : depth r (a :: l) = depth r l := by
  simp [depth, h]

theorem depth_cons_eq (r : Nat × Nat) (l : List (Nat × Nat)) : depth r (r :: l) = some l.length := by
  simp [depth]

theorem depth_lt {r : Nat × Nat} : ∀ {l : List (Nat × Nat)} {d : Nat}, depth r l = some d → d < l.length := by
  intro l
  induction l with
  | nil => intro d h; simp [depth] at h
  | cons a l ih =>
    intro d h
    by_cases ha : a = r
    · subst ha; rw [depth_cons_eq] at h; cases h; simp
    · rw [depth_cons_ne ha] at h; have := ih h; simp; omega

theorem depth_mem {r : Nat × Nat} : ∀ {l : List (Nat × Nat)} {d : Nat}, depth r l = some d → r ∈ l := by
  intro l
  induction l with
  | nil => intro d h; simp [depth] at h
  | cons a l ih =>
    intro d h
    by_cases ha : a = r
    · subst ha; exact List.mem_cons_self
    · rw [depth_cons_ne ha] at h; exact List.mem_cons_of_mem _ (ih h)

theorem depth_of_mem {r : Nat × Nat} : ∀ {l : List (Nat × Nat)}, r ∈ l → ∃ d, depth r l = some d := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons a l ih =>
    intro h
    by_cases ha : a = r
    · subst ha; exact ⟨_, depth_cons_eq _ _⟩
    · rw [depth_cons_ne ha]
      rcases List.mem_cons.1 h with h1 | h1
      · exact absurd h1.symm ha
      · exact ih h1

theorem depth_snoc_mem {r a : Nat × Nat} :
    ∀ {l : List (Nat × Nat)} {d : Nat}, depth r l = some d → depth r (l ++ [a]) = some (d + 1) := by
  intro l
  induction l with
  | nil => intro d h; simp [depth] at h
  | cons b l ih =>
    intro d h
    by_cases hb : b = r
    · subst hb; rw [depth_cons_eq] at h; cases h
      rw [List.cons_append, depth_cons_eq]; simp
    · rw [depth_cons_ne hb] at h
      rw [List.cons_append, depth_cons_ne hb]; exact ih h

theorem depth_snoc_new {r : Nat × Nat} : ∀ {l : List (Nat × Nat)}, r ∉ l → depth r (l ++ [r]) = some 0 := by
  intro l
  induction l with
  | nil => intro _; simp [depth]
  | cons b l ih =>
    intro h
    have hb : b ≠ r := fun e => h (by rw [e]; exact List.mem_cons_self)
    rw [List.cons_append, depth_cons_ne hb]
    exact ih (fun hm => h (List.mem_cons_of_mem _ hm))

theorem depth_snoc_back {r a : Nat × Nat} (h : r ≠ a) :
    ∀ {l : List (Nat × Nat)} {d' : Nat}, depth r (l ++ [a]) = some d' → ∃ d, depth r l = some d ∧ d' = d + 1 := by
  intro l
  induction l with
  | nil => intro d' hd; simp [depth, Ne.symm h] at hd
  | cons b l ih =>
    intro d' hd
    by_cases hb : b = r
    · subst hb
      rw [List.cons_append, depth_cons_eq] at hd; cases hd
      exact ⟨l.length, depth_cons_eq _ _, by simp⟩
    · rw [List.cons_append, depth_cons_ne hb] at hd
      rw [depth_cons_ne hb]; exact ih hd

/-- In a list ordered by `R`, an entry is related to every entry behind it. -/
theorem depth_order {R : Nat × Nat → Nat × Nat → Prop} :
    ∀ {l : List (Nat × Nat)}, l.Pairwise R → ∀ {r r' : Nat × Nat} {d d' : Nat},
      depth r l = some d → depth r' l = some d' → d' < d → R r r' := by
  intro l
  induction l with
  | nil => intro _ r r' d d' h; simp [depth] at h
  | cons a l ih =>
    intro hp r r' d d' h h' hlt
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hp
    by_cases ha : a = r
    · subst ha
      rw [depth_cons_eq] at h; cases h
      by_cases ha' : a = r'
      · subst ha'; rw [depth_cons_eq] at h'; cases h'; omega
      · rw [depth_cons_ne ha'] at h'; exact hhead r' (depth_mem h')
    · rw [depth_cons_ne ha] at h
      by_cases ha' : a = r'
      · subst ha'; rw [depth_cons_eq] at h'; cases h'
        have := depth_lt h; omega
      · rw [depth_cons_ne ha'] at h'; exact ih htail h h' hlt

/-! ## The invariant of the dedupe set -/

/-- The invariant of the dedupe set under guarded recording: within capacity and every map entry an order entry
(`SeenInv`), in the order of the times and not ahead of the clock (`SeenT`), no record twice, and every order entry
belongs to an id whose current record is not older. -/
structure SeenG (p : Params) (S : Seen) (now : Nat) : Prop where
  inv : SeenInv p S
  t : SeenT S now
  nodup : S.order.Nodup
  cur : ∀ m t, (m, t) ∈ S.order → ∃ t', S.map m = some t' ∧ t ≤ t'

theorem SeenEmpty_G (p : Params) (now : Nat) : SeenG p SeenEmpty now :=
  ⟨SeenEmpty_inv p, ⟨List.Pairwise.nil, fun e he => by cases he⟩, List.nodup_nil, fun m t h => by cases h⟩

theorem SeenG.mono {p : Params} {S : Seen} {now now' : Nat} (h : SeenG p S now) (hle : now ≤ now') :
    SeenG p S now' := ⟨h.inv, h.t.mono hle, h.nodup, h.cur⟩

theorem SPopFront_map3 {S : Seen} {a : Nat × Nat} {rest : List (Nat × Nat)} (hS : S.order = a :: rest) (x : Nat) :
    (SPopFront S).map x = if x = a.1 ∧ S.map a.1 = some a.2 then none else S.map x := by
  unfold SPopFront
  simp only [hS]
  by_cases hc : S.map a.1 = some a.2
  · simp only [hc, ite_true, and_true]
    by_cases hx : x = a.1
    · simp [mapSet, hx]
    · simp [mapSet, hx]
  · simp [hc]

theorem SPopFront_G {p : Params} {S : Seen} {now : Nat} (h : SeenG p S now) : SeenG p (SPopFront S) now := by
  rcases hS : S.order with _ | ⟨a, rest⟩
  · have : SPopFront S = S := by unfold SPopFront; simp [hS]
    rw [this]; exact h
  · have ho : (SPopFront S).order = rest := by rw [SPopFront_order, hS]; rfl
    have hnd : (a :: rest).Nodup := hS ▸ h.nodup
    have hpw : (a :: rest).Pairwise (fun x y => x.2 ≤ y.2) := hS ▸ h.t.1
    refine ⟨SPopFront_inv h.inv, (SeenEv.pop SeenEv.refl).seenT h.t, ?_, ?_⟩
    · rw [ho]; exact (List.nodup_cons.1 hnd).2
    · intro m t hm
      rw [ho] at hm
      obtain ⟨t', ht', hle⟩ := h.cur m t (by rw [hS]; exact List.mem_cons_of_mem _ hm)
      rw [SPopFront_map3 hS]
      by_cases hc : m = a.1 ∧ S.map a.1 = some a.2
      · exfalso
        obtain ⟨hm1, hm2⟩ := hc
        subst hm1
        rw [hm2] at ht'; cases ht'
        have h1 : a.2 ≤ t := (List.pairwise_cons.1 hpw).1 (a.1, t) hm
        have h2 : t = a.2 := Nat.le_antisymm hle h1
        subst h2
        exact (List.nodup_cons.1 hnd).1 hm
      · rw [if_neg hc]; exact ⟨t', ht', hle⟩

/-- An id the set does not hold has no record made at `now` in the order. -/
theorem not_mem_now {p : Params} {S : Seen} {now i : Nat} (h : SeenG p S now)
    (hnc : SContains p S i now = false) : (i, now) ∉ S.order := by
  intro hm
  obtain ⟨t', ht', hle⟩ := h.cur i now hm
  have h1 : t' ≤ now := h.t.2 (i, t') (h.inv.map i t' ht')
  have h2 : t' = now := Nat.le_antisymm h1 hle
  subst h2
  have : SContains p S i t' = true := by
    rw [SContains_iff]; exact ⟨t', ht', by simp⟩
  rw [this] at hnc; cases hnc

theorem SPush_G {p : Params} {S : Seen} {now i : Nat} (h : SeenG p S now) (hl : S.order.length < p.seenCap)
    (hnc : SContains p S i now = false) : SeenG p (SPush S i now) now := by
  refine ⟨SPush_inv h.inv hl, (SeenEv.push i SeenEv.refl).seenT h.t, ?_, ?_⟩
  · exact nodup_snoc h.nodup (not_mem_now h hnc)
  · intro m t hm
    have hm' : (m, t) ∈ S.order ++ [(i, now)] := hm
    rw [SPush_map]
    rcases List.mem_append.1 hm' with h1 | h1
    · by_cases hmi : m = i
      · rw [if_pos hmi]; exact ⟨now, rfl, h.t.2 (m, t) h1⟩
      · rw [if_neg hmi]; exact h.cur m t h1
    · rw [List.mem_singleton] at h1
      have e1 : m = i := (Prod.ext_iff.1 h1).1
      have e2 : t = now := (Prod.ext_iff.1 h1).2
      rw [if_pos e1]; exact ⟨now, rfl, by rw [e2]; exact Nat.le_refl _⟩

/-! ## The depth of the live record of an id -/

/-- The depth of the live record of `x` in the dedupe set, `none` when the set does not hold `x` at `now`. -/
def D (p : Params) (S : Seen) (now : Nat) (x : Nat) : Option Nat :=
  match S.map x with
  | some t => if now - t ≤ p.ttl then depth (x, t) S.order else none
  | none => none

theorem D_some {p : Params} {S : Seen} {now x d : Nat} (h : D p S now x = some d) :
    ∃ t, S.map x = some t ∧ now - t ≤ p.ttl ∧ depth (x, t) S.order = some d := by
  unfold D at h
  rcases hm : S.map x with _ | t
  · simp [hm] at h
  · simp only [hm] at h
    by_cases hl : now - t ≤ p.ttl
    · rw [if_pos hl] at h; exact ⟨t, rfl, hl, h⟩
    · rw [if_neg hl] at h; cases h

theorem D_of {p : Params} {S : Seen} {now x t d : Nat} (hm : S.map x = some t) (hl : now - t ≤ p.ttl)
    (hd : depth (x, t) S.order = some d) : D p S now x = some d := by
  unfold D; simp only [hm]; rw [if_pos hl]; exact hd

theorem D_map {p : Params} {S : Seen} {now x d : Nat} (h : D p S now x = some d) : S.map x ≠ none := by
  obtain ⟨t, ht, _⟩ := D_some h; rw [ht]; simp

theorem D_contains {p : Params} {S : Seen} {now x d : Nat} (h : D p S now x = some d) :
    SContains p S x now = true := by
  obtain ⟨t, ht, hl, _⟩ := D_some h
  rw [SContains_iff]; exact ⟨t, ht, hl⟩

theorem D_of_contains {p : Params} {S : Seen} {now x : Nat} (hI : SeenInv p S)
    (h : SContains p S x now = true) : ∃ d, D p S now x = some d := by
  rw [SContains_iff] at h
  obtain ⟨t, ht, hl⟩ := h
  obtain ⟨d, hd⟩ := depth_of_mem (hI.map x t ht)
  exact ⟨d, D_of ht hl hd⟩

theorem D_none {p : Params} {S : Seen} {now x : Nat} (h : SContains p S x now = false) : D p S now x = none := by
  cases hd : D p S now x with
  | none => rfl
  | some d => rw [D_contains hd] at h; cases h

theorem D_bound {p : Params} {S : Seen} {now x d : Nat} (hI : SeenInv p S) (h : D p S now x = some d) :
    d + 1 ≤ p.seenCap := by
  obtain ⟨t, _, _, hd⟩ := D_some h
  have := depth_lt hd
  have := hI.len
  omega

/-- A record that was made behind a live record is live. -/
theorem D_later {p : Params} {S : Seen} {now now' e f d df : Nat} (hT : SeenT S now)
    (he : D p S now' e = some d) (hf : D p S now f = some df) (hlt : df < d) : D p S now' f = some df := by
  obtain ⟨te, hme, hle, hde⟩ := D_some he
  obtain ⟨tf, hmf, hlf, hdf⟩ := D_some hf
  have : te ≤ tf := depth_order (R := fun a b => a.2 ≤ b.2) hT.1 hde hdf hlt
  exact D_of hmf (by omega) hdf

theorem D_earlier {p : Params} {S : Seen} {now now' x d : Nat} (hle : now ≤ now') (h : D p S now' x = some d) :
    D p S now x = some d := by
  obtain ⟨t, hm, hl, hd⟩ := D_some h
  exact D_of hm (by omega) hd

/-! ## What a drop of the front and a record at the back do to the depths -/

/-- A record that is not at the front, or whose front is expired, keeps its depth when the front is dropped. -/
theorem D_pop_keep {p : Params} {S : Seen} {now x d : Nat} {a : Nat × Nat} {rest : List (Nat × Nat)}
    (hS : S.order = a :: rest) (h : D p S now x = some d) (hk : d < rest.length ∨ p.ttl < now - a.2) :
    D p (SPopFront S) now x = some d := by
  obtain ⟨t, hm, hl, hd⟩ := D_some h
  have ho : (SPopFront S).order = rest := by rw [SPopFront_order, hS]; rfl
  have hne : a ≠ (x, t) := by
    intro e
    rw [hS, e, depth_cons_eq] at hd
    cases hd
    rcases hk with hk | hk
    · omega
    · rw [e] at hk; simp at hk; omega
  have hm' : (SPopFront S).map x = some t := by
    rw [SPopFront_map3 hS]
    have : ¬(x = a.1 ∧ S.map a.1 = some a.2) := by
      intro ⟨h1, h2⟩
      apply hne
      subst h1
      rw [hm] at h2; cases h2; rfl
    rw [if_neg this]; exact hm
  refine D_of hm' hl ?_
  rw [ho]
  rw [hS, depth_cons_ne hne] at hd
  exact hd

/-- A drop of the front makes no id held and moves no record. -/
theorem D_pop_back {p : Params} {S : Seen} {now x d : Nat} (h : D p (SPopFront S) now x = some d) :
    D p S now x = some d := by
  rcases hS : S.order with _ | ⟨a, rest⟩
  · have : SPopFront S = S := by unfold SPopFront; simp [hS]
    rw [this] at h; exact h
  · obtain ⟨t, hm, hl, hd⟩ := D_some h
    have ho : (SPopFront S).order = rest := by rw [SPopFront_order, hS]; rfl
    rw [SPopFront_map3 hS] at hm
    by_cases hc : x = a.1 ∧ S.map a.1 = some a.2
    · rw [if_pos hc] at hm; cases hm
    · rw [if_neg hc] at hm
      have hne : a ≠ (x, t) := by
        intro e
        apply hc
        have e1 : a.1 = x := by rw [e]
        have e2 : a.2 = t := by rw [e]
        exact ⟨e1.symm, by rw [e1, e2]; exact hm⟩
      refine D_of hm hl ?_
      rw [hS, depth_cons_ne hne]
      rw [ho] at hd; exact hd

theorem D_push_self {p : Params} {S : Seen} {now i : Nat} (h : SeenG p S now)
    (hnc : SContains p S i now = false) : D p (SPush S i now) now i = some 0 := by
  refine D_of (t := now) (by rw [SPush_map]; simp) (by simp) ?_
  show depth (i, now) (S.order ++ [(i, now)]) = some 0
  exact depth_snoc_new (not_mem_now h hnc)

theorem D_push_keep {p : Params} {S : Seen} {now i x d : Nat} (hx : x ≠ i) (h : D p S now x = some d) :
    D p (SPush S i now) now x = some (d + 1) := by
  obtain ⟨t, hm, hl, hd⟩ := D_some h
  refine D_of (t := t) (by rw [SPush_map, if_neg hx]; exact hm) hl ?_
  show depth (x, t) (S.order ++ [(i, now)]) = some (d + 1)
  exact depth_snoc_mem hd

theorem D_push_back {p : Params} {S : Seen} {now i x d' : Nat} (hx : x ≠ i)
    (h : D p (SPush S i now) now x = some d') : ∃ d, D p S now x = some d ∧ d' = d + 1 := by
  obtain ⟨t, hm, hl, hd⟩ := D_some h
  rw [SPush_map, if_neg hx] at hm
  have hd' : depth (x, t) (S.order ++ [(i, now)]) = some d' := hd
  have hne : (x, t) ≠ (i, now) := fun e => hx (Prod.ext_iff.1 e).1
  obtain ⟨d, h1, h2⟩ := depth_snoc_back hne hd'
  exact ⟨d, D_of hm hl h1, h2⟩

/-! ## One insert, seen through the depths -/

/-- What an insert of `i`, which was not held, does to the depths of a set of capacity `cap`. -/
structure InsRel (cap : Nat) (D D' : Nat → Option Nat) (i : Nat) : Prop where
  self : D' i = some 0
  keep : ∀ x d, x ≠ i → D x = some d → d + 2 ≤ cap → D' x = some (d + 1)
  back : ∀ x d', x ≠ i → D' x = some d' → ∃ d, D x = some d ∧ d' = d + 1
  bound : ∀ x d', D' x = some d' → d' + 1 ≤ cap

/-- An insert that records (forced, or into a set with room) of an id the set does not hold. -/
theorem SInsert_rel {p : Params} {S : Seen} {now i : Nat} {f : Bool} (hcap : 0 < p.seenCap) (h : SeenG p S now)
    (hnc : SContains p S i now = false) (hf : f = true ∨ S.order.length < p.seenCap) :
    SeenG p (SInsert p S i now f) now ∧ InsRel p.seenCap (D p S now) (D p (SInsert p S i now f) now) i := by
  unfold SInsert
  by_cases hfull : p.seenCap ≤ S.order.length
  · have hft : f = true := by
      rcases hf with hf | hf
      · exact hf
      · omega
    rw [if_pos hfull, if_pos hft]
    have hlen : S.order.length = p.seenCap := Nat.le_antisymm h.inv.len hfull
    have hG1 : SeenG p (SPopFront S) now := SPopFront_G h
    have hl1 : (SPopFront S).order.length < p.seenCap := by rw [SPopFront_len]; omega
    have hnc1 : SContains p (SPopFront S) i now = false := by
      cases hc : SContains p (SPopFront S) i now with
      | false => rfl
      | true =>
        obtain ⟨d, hd⟩ := D_of_contains hG1.inv hc
        rw [D_contains (D_pop_back hd)] at hnc; cases hnc
    have hG2 := SPush_G hG1 hl1 hnc1
    refine ⟨hG2, D_push_self hG1 hnc1, ?_, ?_, fun x d' hd => D_bound hG2.inv hd⟩
    · intro x d hx hd hd2
      rcases hS : S.order with _ | ⟨a, rest⟩
      · rw [hS] at hlen; simp at hlen; omega
      · have hr : rest.length + 1 = p.seenCap := by rw [hS] at hlen; simpa using hlen
        exact D_push_keep hx (D_pop_keep hS hd (Or.inl (by omega)))
    · intro x d' hx hd
      obtain ⟨d, h1, h2⟩ := D_push_back hx hd
      exact ⟨d, D_pop_back h1, h2⟩
  · rw [if_neg hfull]
    have hl : S.order.length < p.seenCap := by omega
    have hG2 := SPush_G h hl hnc
    exact ⟨hG2, D_push_self h hnc, fun x d hx hd _ => D_push_keep hx hd, fun x d' hx hd => D_push_back hx hd,
      fun x d' hd => D_bound hG2.inv hd⟩

/-- An expiry keeps the invariant, and the depth of every id the set holds. -/
theorem SExpireAux_G {p : Params} {now : Nat} (f : Nat) :
    ∀ {S : Seen}, SeenG p S now → SeenG p (SExpireAux p now f S) now ∧
      ∀ x, D p (SExpireAux p now f S) now x = D p S now x := by
  induction f with
  | zero => intro S h; exact ⟨h, fun _ => rfl⟩
  | succ f ih =>
    intro S h
    unfold SExpireAux
    rcases hS : S.order with _ | ⟨a, rest⟩
    · exact ⟨h, fun _ => rfl⟩
    · by_cases hc : p.ttl < now - a.2
      · simp only [hc, ite_true]
        obtain ⟨h1, h2⟩ := ih (SPopFront_G h)
        refine ⟨h1, fun x => ?_⟩
        rw [h2 x]
        cases hd : D p S now x with
        | some d => exact D_pop_keep hS hd (Or.inr hc)
        | none =>
          cases hd' : D p (SPopFront S) now x with
          | none => rfl
          | some d => rw [D_pop_back hd'] at hd; cases hd
      · simp only [hc, ite_false]
        first | exact ⟨h, fun _ => rfl⟩ | exact ⟨h, fun _ => trivial⟩ | exact h

/-! ## The accounting on the depths -/

/-- `f` has a live record behind depth `d`. -/
def behind (D : Nat → Option Nat) (d : Nat) (f : Nat) : Bool :=
  match D f with
  | some d' => decide (d' < d)
  | none => false

/-- The ids of `l` with no live record behind depth `d`: each may still cost one insert. -/
def NB (D : Nat → Option Nat) (d : Nat) (l : List Nat) : Nat := l.countP (fun f => !behind D d f)

theorem NB_nil (D : Nat → Option Nat) (d : Nat) : NB D d [] = 0 := rfl

theorem NB_cons (D : Nat → Option Nat) (d x : Nat) (l : List Nat) :
    NB D d (x :: l) = NB D d l + (if behind D d x = true then 0 else 1) := by
  unfold NB
  rw [List.countP_cons]
  cases behind D d x <;> simp

theorem NB_append (D : Nat → Option Nat) (d : Nat) (l l' : List Nat) : NB D d (l ++ l') = NB D d l + NB D d l' := by
  unfold NB; exact List.countP_append

theorem NB_le_length (D : Nat → Option Nat) (d : Nat) (l : List Nat) : NB D d l ≤ l.length := by
  unfold NB; exact List.countP_le_length

theorem NB_mono {D D' : Nat → Option Nat} {d d' : Nat} :
    ∀ {l : List Nat}, (∀ f ∈ l, behind D d f = true → behind D' d' f = true) → NB D' d' l ≤ NB D d l := by
  intro l
  induction l with
  | nil => intro _; exact Nat.le_refl _
  | cons x l ih =>
    intro h
    have h1 := ih (fun f hf => h f (List.mem_cons_of_mem _ hf))
    have h2 := h x List.mem_cons_self
    rw [NB_cons, NB_cons]
    cases hb : behind D d x with
    | false => split <;> simp <;> omega
    | true => rw [h2 hb]; simpa using h1

theorem behind_ins {cap : Nat} {D D' : Nat → Option Nat} {i d f : Nat} (h : InsRel cap D D' i) (hf : f ≠ i)
    (hd : d + 2 ≤ cap) (hb : behind D d f = true) : behind D' (d + 1) f = true := by
  unfold behind at hb ⊢
  rcases hDf : D f with _ | df
  · simp [hDf] at hb
  · simp only [hDf, decide_eq_true_eq] at hb
    rw [h.keep f df hf hDf (by omega)]
    simp; omega

/-- The accounting of the log against the dedupe set. `E` is the ids of the log, oldest first; `cap` is the log's
capacity. For every logged id the set holds, the records behind its own, the newer logged ids that have none
there, and twice its place in the log stay within the capacity plus the length. -/
def KeepInv (cap : Nat) (D : Nat → Option Nat) (E : List Nat) : Prop :=
  ∀ pre e post, E = pre ++ e :: post → ∀ d, D e = some d → d + NB D d post + 2 * pre.length + 2 ≤ cap + E.length

/-- The ids evicted so far in this step are held, each with room for the inserts the rest of the log can still
cause. `cap` is the capacity of the dedupe set. -/
def DoneInv (cap : Nat) (D : Nat → Option Nat) (done E : List Nat) : Prop :=
  ∀ y ∈ done, ∃ d, D y = some d ∧ d + NB D d E + 2 ≤ cap

theorem KeepInv_nil (cap : Nat) (D : Nat → Option Nat) : KeepInv cap D [] := by
  intro pre e post h; cases pre <;> cases h

/-- The oldest logged id leaves the log and the set is not touched. -/
theorem KeepInv.evict_skip {cap : Nat} {D : Nat → Option Nat} {x : Nat} {E : List Nat}
    (h : KeepInv cap D (x :: E)) : KeepInv cap D E := by
  intro pre e post hE d hd
  have := h (x :: pre) e post (by rw [hE]; rfl) d hd
  simp at this ⊢
  omega

/-- The oldest logged id leaves the log and is recorded. -/
theorem KeepInv.evict_push {cap c : Nat} {D D' : Nat → Option Nat} {x : Nat} {E : List Nat}
    (hI : InsRel c D D' x) (hx : x ∉ E) (h : KeepInv cap D (x :: E)) : KeepInv cap D' E := by
  intro pre e post hE d' hd'
  have hee : e ∈ E := by rw [hE]; simp
  have hex : e ≠ x := fun e1 => hx (e1 ▸ hee)
  obtain ⟨d, hd, rfl⟩ := hI.back e d' hex hd'
  have hb := hI.bound e _ hd'
  have hold := h (x :: pre) e post (by rw [hE]; rfl) d hd
  have hnb : NB D' (d + 1) post ≤ NB D d post := by
    apply NB_mono
    intro f hf hbf
    have hfE : f ∈ E := by rw [hE]; simp [hf]
    exact behind_ins hI (fun e1 => hx (e1 ▸ hfE)) (by omega) hbf
  simp at hold ⊢
  omega

theorem snoc_split {α : Type} {l pre post : List α} {m e : α} (h : l ++ [m] = pre ++ e :: post) :
    (post = [] ∧ e = m ∧ pre = l) ∨ ∃ post0, post = post0 ++ [m] ∧ l = pre ++ e :: post0 := by
  rcases List.eq_nil_or_concat post with rfl | ⟨post0, b, rfl⟩
  · left
    have := List.append_inj' h (by simp)
    exact ⟨rfl, by simpa using this.2.symm, this.1.symm⟩
  · right
    have h' : l ++ [m] = (pre ++ e :: post0) ++ [b] := by rw [h]; simp
    have := List.append_inj' h' (by simp)
    have hb : m = b := by simpa using this.2
    exact ⟨post0, by rw [hb, List.concat_eq_append], this.1⟩

/-- A message is stored at the back of the log and recorded. -/
theorem KeepInv.store_rec {cap c : Nat} {D D' : Nat → Option Nat} {m : Nat} {E : List Nat}
    (hI : InsRel c D D' m) (hm : m ∉ E) (hl : E.length < cap) (h : KeepInv cap D E) :
    KeepInv cap D' (E ++ [m]) := by
  intro pre e post hE d' hd'
  rcases snoc_split hE with ⟨rfl, rfl, rfl⟩ | ⟨post0, rfl, hE0⟩
  · rw [hI.self] at hd'; cases hd'
    simp [NB_nil]; omega
  · have hee : e ∈ E := by rw [hE0]; simp
    have hem : e ≠ m := fun e1 => hm (e1 ▸ hee)
    obtain ⟨d, hd, rfl⟩ := hI.back e d' hem hd'
    have hb := hI.bound e _ hd'
    have hold := h pre e post0 hE0 d hd
    have hnb : NB D' (d + 1) post0 ≤ NB D d post0 := by
      apply NB_mono
      intro f hf hbf
      have hfE : f ∈ E := by rw [hE0]; simp [hf]
      exact behind_ins hI (fun e1 => hm (e1 ▸ hfE)) (by omega) hbf
    have hlast : NB D' (d + 1) [m] = 0 := by
      rw [NB_cons, NB_nil]
      have : behind D' (d + 1) m = true := by unfold behind; rw [hI.self]; simp
      rw [this]; simp
    rw [NB_append, hlast]
    simp at hold ⊢
    omega

/-- A message is stored at the back of the log and not recorded. -/
theorem KeepInv.store_unrec {cap : Nat} {D : Nat → Option Nat} {m : Nat} {E : List Nat}
    (hm : D m = none) (h : KeepInv cap D E) : KeepInv cap D (E ++ [m]) := by
  intro pre e post hE d hd
  rcases snoc_split hE with ⟨rfl, rfl, rfl⟩ | ⟨post0, rfl, hE0⟩
  · rw [hm] at hd; cases hd
  · have hold := h pre e post0 hE0 d hd
    have hlast : NB D d [m] ≤ 1 := by
      have := NB_le_length D d [m]; simpa using this
    rw [NB_append]
    simp at hold ⊢
    omega

theorem DoneInv.evict_skip {cap : Nat} {D : Nat → Option Nat} {done : List Nat} {x : Nat} {E : List Nat}
    (h : DoneInv cap D done (x :: E)) : DoneInv cap D done E := by
  intro y hy
  obtain ⟨d, hd, hle⟩ := h y hy
  refine ⟨d, hd, ?_⟩
  rw [NB_cons] at hle
  omega

theorem DoneInv.evict_push {cap : Nat} {D D' : Nat → Option Nat} {done : List Nat} {x : Nat} {E : List Nat}
    (hI : InsRel cap D D' x) (hx : D x = none) (hxE : x ∉ E) (hdis : ∀ y ∈ done, y ≠ x)
    (h : DoneInv cap D done (x :: E)) : DoneInv cap D' done E := by
  intro y hy
  obtain ⟨d, hd, hle⟩ := h y hy
  have hbx : behind D d x = false := by unfold behind; rw [hx]
  rw [NB_cons, hbx] at hle
  simp at hle
  refine ⟨d + 1, hI.keep y d (hdis y hy) hd (by omega), ?_⟩
  have hnb : NB D' (d + 1) E ≤ NB D d E := by
    apply NB_mono
    intro f hf hbf
    exact behind_ins hI (fun e1 => hxE (e1 ▸ hf)) (by omega) hbf
  omega

/-- An id evicted in this step is still held after one more insert. -/
theorem DoneInv.after_ins {cap : Nat} {D D' : Nat → Option Nat} {done E : List Nat} {m : Nat}
    (hI : InsRel cap D D' m) (hdis : ∀ y ∈ done, y ≠ m) (h : DoneInv cap D done E) :
    ∀ y ∈ done, D' y ≠ none := by
  intro y hy
  obtain ⟨d, hd, hle⟩ := h y hy
  rw [hI.keep y d (hdis y hy) hd (by omega)]
  simp

end Pinc.BroadcastNode
