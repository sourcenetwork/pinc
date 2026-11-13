import Vinc.Axioms
import Vinc.CoreTable

/-!
# The connection-id table: bounded, every key found, duplicates only by `insert_dup`, the oldest evicted

What the model proves about `Table`, for any capacity `n`, any bucket function `bk` (so any collisions) and any run of
calls (`Inv` is kept by every operation, so the statements hold for every table a run of calls reaches):

- the table never holds more than `n` entries: `len` is the length of the order list and at most `n` (`Inv`, and
  `insert_inv`, `insertRoom_inv`, `insertDup_inv`, `remove_inv`, `removePair_inv`, `touch_inv`, `clear_inv`);
- every entry held is found: the entries of a key are exactly those of its bucket's chain with that key, newest push
  first (`holders_iff`, `holders_desc`); `find` gives the newest push (`find_eq_head`), `findable` finds every entry
  held, whatever the other keys of the chain and whatever was removed before (`remove_found`, `removePair_found`);
- `matches::<M>` gives the first `M` of the holders in order of push, newest first, as many as there are when fewer
  (`matches_eq`, `matches_len`, `matches_desc`); with more than `M` holders it leaves out exactly the oldest pushes
  (`matches_cut`) and the touch order does not matter (`touch_chain`);
- a removal takes the newest push of the key, the order list loses that entry and no other, and every other entry is
  still found (`remove_some`, `remove_none`, `remove_found`; the same for `removePair`);
- a key has two holders only through `insert_dup`: `insert`, `insertRoom`, `remove`, `removePair` and `touch` keep a
  table in which every key has at most one entry such a table (`Uniq`, `insert_uniq`, `insertRoom_uniq`,
  `remove_uniq`, `removePair_uniq`, `touch_uniq`), while `insert_dup` puts a second holder in front of the first
  (`insertDup_holders`);
- `insert` of a held key sets the value of the newest push and nothing moves (`insert_held`); of a new key it
  appends it as the newest and, only when the table holds `n` entries, evicts exactly the head of the order list, the
  oldest (`insert_full`, `insert_room`, `insert_evicts`);
- `insert_dup`, and `insert_room` of a new key, on a table that holds `n` entries answer false and change nothing
  (`insertDup_full`, `insertRoom_full`).
-/

namespace Vinc.CoreTable

/-- The table is well formed. -/
structure Inv (bk : Nat → Nat) (n : Nat) (t : T) : Prop where
  chain_iff : ∀ (b : Nat) (e : E), e ∈ t.chain b ↔ e ∈ t.order ∧ bk e.k = b
  chain_desc : ∀ b, (t.chain b).Pairwise fun x y => y.s < x.s
  ord_nodup : t.order.Pairwise fun x y => x.s ≠ y.s
  ord_lt : ∀ e ∈ t.order, e.s < t.ctr
  len_eq : t.len = t.order.length
  len_le : t.len ≤ n

/-- Every key has at most one entry. -/
def Uniq (t : T) : Prop := ∀ x ∈ t.order, ∀ y ∈ t.order, x.k = y.k → x = y

/-! ### Helpers -/

theorem eq_of_s {l : List E} (h : l.Pairwise fun x y => x.s ≠ y.s) {x y : E} (hx : x ∈ l) (hy : y ∈ l)
    (hs : x.s = y.s) : x = y := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd hs (h1 y hy)
    · exact absurd hs.symm (h1 x hx)
    · exact ih h2 hx hy

theorem length_filter_s {l : List E} (h : l.Pairwise fun x y => x.s ≠ y.s) {e : E} (he : e ∈ l) :
    (l.filter fun x => x.s != e.s).length + 1 = l.length := by
  induction l with
  | nil => simp at he
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨h1, h2⟩ := h
    by_cases hae : a.s = e.s
    · have : a = e := eq_of_s (List.pairwise_cons.2 ⟨h1, h2⟩) (List.mem_cons_self) he hae
      subst this
      have hn : ∀ x ∈ l, x.s ≠ a.s := fun x hx => (h1 x hx).symm
      have : (l.filter fun x => x.s != a.s) = l := by
        apply List.filter_eq_self.2
        intro x hx; simpa using hn x hx
      simp [this]
    · have hel : e ∈ l := by
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact absurd rfl hae
        · exact he
      have := ih h2 hel
      simp [hae, this]

theorem find_eq_head (l : List E) (p : E → Bool) : l.find? p = (l.filter p).head? := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a
    · rw [List.find?_cons_of_neg (by simp [hp]), List.filter_cons_of_neg (by simp [hp]), ih]
    · rw [List.find?_cons_of_pos (by simp [hp]), List.filter_cons_of_pos (by simp [hp])]; rfl

theorem find_some_k {bk : Nat → Nat} {t : T} {k : Nat} {e : E} (h : find bk t k = some e) :
    e ∈ t.chain (bk k) ∧ e.k = k := by
  unfold find at h
  have := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  exact ⟨this, by simpa using h2⟩

theorem find_none {bk : Nat → Nat} {t : T} {k : Nat} (h : find bk t k = none) :
    ∀ e ∈ t.chain (bk k), e.k ≠ k := by
  unfold find at h
  intro e he hk
  have := List.find?_eq_none.1 h e he
  simp [hk] at this

/-! ### What a table holds -/

theorem holders_iff {bk n t} (h : Inv bk n t) (k : Nat) (e : E) :
    e ∈ holders bk t k ↔ e ∈ t.order ∧ e.k = k := by
  unfold holders
  rw [List.mem_filter, h.chain_iff]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, by simpa using h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]⟩, by simpa using h3⟩

theorem holders_desc {bk n t} (h : Inv bk n t) (k : Nat) : (holders bk t k).Pairwise fun x y => y.s < x.s :=
  (h.chain_desc (bk k)).sublist (List.filter_sublist)

theorem find_eq_holders {bk t} (k : Nat) : find bk t k = (holders bk t k).head? := by
  unfold find holders; exact find_eq_head _ _

/-- `find` gives the newest push among the entries of the key. -/
theorem find_newest {bk n t} (h : Inv bk n t) {k : Nat} {e : E} (he : find bk t k = some e) :
    e ∈ t.order ∧ e.k = k ∧ ∀ x ∈ t.order, x.k = k → x.s ≤ e.s := by
  have hd := holders_desc h k
  rw [find_eq_holders] at he
  cases hh : holders bk t k with
  | nil => simp [hh] at he
  | cons a l =>
    simp only [hh, List.head?_cons, Option.some.injEq] at he
    subst he
    rw [hh] at hd
    rw [List.pairwise_cons] at hd
    have hmem : ∀ x, x ∈ t.order ∧ x.k = k ↔ x = a ∨ x ∈ l := by
      intro x; rw [← holders_iff h, hh]; simp
    refine ⟨((hmem a).2 (Or.inl rfl)).1, ((hmem a).2 (Or.inl rfl)).2, ?_⟩
    intro x hx hk
    rcases (hmem x).1 ⟨hx, hk⟩ with rfl | hl
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (hd.1 x hl)

/-- Every entry held is found, and what is found has the same key and is at least as new. -/
theorem findable {bk n t} (h : Inv bk n t) {e : E} (he : e ∈ t.order) :
    ∃ e', find bk t e.k = some e' ∧ e'.k = e.k ∧ e.s ≤ e'.s := by
  cases hf : find bk t e.k with
  | some e' =>
    have := find_newest h hf
    exact ⟨e', rfl, this.2.1, this.2.2 e he rfl⟩
  | none =>
    exfalso
    have := find_eq_holders (bk := bk) (t := t) e.k
    rw [hf] at this
    have hm : e ∈ holders bk t e.k := (holders_iff h _ _).2 ⟨he, rfl⟩
    cases hh : holders bk t e.k with
    | nil => simp [hh] at hm
    | cons a l => simp [hh] at this

theorem find_none_iff {bk n t} (h : Inv bk n t) (k : Nat) :
    find bk t k = none ↔ ∀ x ∈ t.order, x.k ≠ k := by
  constructor
  · intro hn x hx hk
    obtain ⟨e', hf, _⟩ := findable h hx
    rw [hk] at hf; rw [hf] at hn; simp at hn
  · intro hn
    cases hf : find bk t k with
    | none => rfl
    | some e => exact absurd (find_newest h hf).2.1 (hn e (find_newest h hf).1)

/-! ### `matches` -/

/-- The entries `matches::<M>` returns are the first `M` holders, in order of push, newest first. -/
theorem matches_eq (bk : Nat → Nat) (t : T) (k m : Nat) :
    (matchesOf bk t k m).1 = ((holders bk t k).take m).map (·.v) := rfl

theorem matches_len (bk : Nat → Nat) (t : T) (k m : Nat) :
    (matchesOf bk t k m).2 = min m (holders bk t k).length := by
  simp [matchesOf, List.length_take]

/-- Every entry returned holds the key, and is held. -/
theorem matches_mem {bk n t} (h : Inv bk n t) (k m : Nat) (e : E) (he : e ∈ (holders bk t k).take m) :
    e ∈ t.order ∧ e.k = k := (holders_iff h k e).1 (List.mem_of_mem_take he)

/-- With at most `M` holders, every holder is returned. -/
theorem matches_all {bk n t} (h : Inv bk n t) {k m : Nat} (hm : (holders bk t k).length ≤ m) {e : E}
    (he : e ∈ t.order) (hk : e.k = k) : e ∈ (holders bk t k).take m := by
  rw [List.take_of_length_le hm]; exact (holders_iff h k e).2 ⟨he, hk⟩

theorem matches_desc {bk n t} (h : Inv bk n t) (k m : Nat) :
    ((holders bk t k).take m).Pairwise fun x y => y.s < x.s :=
  (holders_desc h k).sublist (List.take_sublist _ _)

/-- With more than `M` holders, a holder that is not returned was pushed before every holder that is. -/
theorem matches_cut {bk n t} (h : Inv bk n t) (k m : Nat) :
    ∀ x ∈ (holders bk t k).drop m, ∀ y ∈ (holders bk t k).take m, x.s < y.s := by
  have hd := holders_desc h k
  rw [← List.take_append_drop m (holders bk t k), List.pairwise_append] at hd
  intro x hx y hy
  exact hd.2.2 y hy x hx

/-- The order of the order list (a `touch`) is not the order of the chain: the chains never change. -/
theorem touch_chain (bk : Nat → Nat) (t : T) (k : Nat) : (touch bk t k).chain = t.chain := by
  unfold touch; split <;> (try split) <;> rfl

/-! ### The invariant is kept -/

theorem new_inv (bk : Nat → Nat) (n : Nat) : Inv bk n T.new where
  chain_iff := by intro b e; simp [T.new]
  chain_desc := by intro b; simp [T.new]
  ord_nodup := by simp [T.new]
  ord_lt := by simp [T.new]
  len_eq := rfl
  len_le := Nat.zero_le _

theorem push_inv {bk n t} (h : Inv bk n t) (k v : Nat) : Inv bk n (push bk n t k v).1 := by
  unfold push
  by_cases hl : t.len < n
  · simp only [hl, ite_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b e
      by_cases hb : b = bk k
      · subst hb
        simp only [ite_true, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, h.chain_iff]
        constructor
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨Or.inr rfl, rfl⟩
          · exact ⟨Or.inl h1, h2⟩
        · rintro ⟨h1 | rfl, h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact Or.inl rfl
      · simp only [hb, ite_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, h.chain_iff]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
        · rintro ⟨h1 | rfl, h2⟩
          · exact ⟨h1, h2⟩
          · exact absurd h2.symm hb
    · intro b
      by_cases hb : b = bk k
      · subst hb
        simp only [ite_true, List.pairwise_cons]
        refine ⟨?_, h.chain_desc _⟩
        intro y hy
        exact h.ord_lt y (((h.chain_iff _ y).1 hy).1)
      · simp only [hb, ite_false]; exact h.chain_desc b
    · rw [List.pairwise_append]
      refine ⟨h.ord_nodup, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact Nat.ne_of_lt (h.ord_lt x hx)
    · intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact Nat.lt_succ_of_lt (h.ord_lt e he)
      · exact Nat.lt_succ_self _
    · simp [h.len_eq]
    · show t.len + 1 ≤ n; omega
  · simpa [hl] using h

theorem pop_inv {bk n t} (h : Inv bk n t) {e : E} (he : e ∈ t.order) : Inv bk n (pop t e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b x
    simp only [pop, List.mem_filter, h.chain_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
  · intro b; exact (h.chain_desc b).filter _
  · exact h.ord_nodup.filter _
  · intro x hx
    simp only [pop, List.mem_filter] at hx
    exact h.ord_lt x hx.1
  · have := length_filter_s h.ord_nodup he
    have := h.len_eq
    simp only [pop]; omega
  · simp only [pop]; have := h.len_le; omega

theorem setV_inv {bk n t} (h : Inv bk n t) (s v : Nat) : Inv bk n (setV t s v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b x
    simp only [setV, List.mem_map, h.chain_iff]
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨a, h1, rfl⟩, ?_⟩
      by_cases hs : a.s = s <;> simp [hs, h2]
    · rintro ⟨⟨a, h1, rfl⟩, h2⟩
      refine ⟨a, ⟨h1, ?_⟩, rfl⟩
      by_cases hs : a.s = s <;> simpa [hs] using h2
  · intro b
    simp only [setV]
    rw [List.pairwise_map]
    refine (h.chain_desc b).imp ?_
    intro x y hxy
    by_cases hx : x.s = s <;> by_cases hy : y.s = s <;> simp [hx, hy] <;> omega
  · simp only [setV]
    rw [List.pairwise_map]
    refine h.ord_nodup.imp ?_
    intro x y hxy
    by_cases hx : x.s = s <;> by_cases hy : y.s = s <;> simp [hx, hy] <;> omega
  · intro x hx
    simp only [setV, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have : a.s < t.ctr := h.ord_lt a ha
    show _ < t.ctr
    by_cases hs : a.s = s <;> simpa [hs] using this
  · simp [setV, h.len_eq]
  · exact h.len_le

theorem touch_inv {bk n t} (h : Inv bk n t) (k : Nat) : Inv bk n (touch bk t k) := by
  unfold touch
  split
  · rename_i e hf
    have he := (find_newest h hf).1
    split
    · exact h
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro b x
        simp only [List.mem_append, List.mem_filter, List.mem_singleton]
        rw [h.chain_iff]
        constructor
        · rintro ⟨h1, h2⟩; refine ⟨?_, h2⟩
          by_cases hx : x = e
          · exact Or.inr hx
          · left; exact ⟨h1, by simpa using fun hs => hx (eq_of_s h.ord_nodup h1 he hs)⟩
        · rintro ⟨h1 | rfl, h2⟩
          · exact ⟨h1.1, h2⟩
          · exact ⟨he, h2⟩
      · exact h.chain_desc
      · rw [List.pairwise_append]
        refine ⟨h.ord_nodup.filter _, by simp, ?_⟩
        intro x hx y hy
        simp only [List.mem_filter, List.mem_singleton] at hx hy
        subst hy
        simpa using hx.2
      · intro x hx
        simp only [List.mem_append, List.mem_filter, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact h.ord_lt x hx.1
        · exact h.ord_lt _ he
      · have := length_filter_s h.ord_nodup he
        have := h.len_eq
        simp only [List.length_append, List.length_singleton]; omega
      · exact h.len_le
  · exact h

theorem insert_inv {bk n t} (h : Inv bk n t) (k v : Nat) : Inv bk n (insert bk n t k v).1 := by
  unfold insert
  split
  · rename_i e hf; exact setV_inv h _ _
  · split
    · rename_i hfull
      split
      · rename_i o rest ho
        have hmem : o ∈ t.order := by rw [ho]; exact List.mem_cons_self
        exact push_inv (pop_inv h hmem) k v
      · exact push_inv h k v
    · exact push_inv h k v

theorem insertRoom_inv {bk n t} (h : Inv bk n t) (k v : Nat) : Inv bk n (insertRoom bk n t k v).1 := by
  unfold insertRoom
  split
  · exact setV_inv h _ _
  · exact push_inv h k v

theorem insertDup_inv {bk n t} (h : Inv bk n t) (k v : Nat) : Inv bk n (insertDup bk n t k v).1 :=
  push_inv h k v

theorem remove_inv {bk n t} (h : Inv bk n t) (k : Nat) : Inv bk n (remove bk t k).1 := by
  unfold remove
  split
  · rename_i e hf; exact pop_inv h (find_newest h hf).1
  · exact h

theorem removePair_inv {bk n t} (h : Inv bk n t) (k v : Nat) : Inv bk n (removePair bk t k v).1 := by
  unfold removePair
  split
  · rename_i e hf
    have := ((h.chain_iff _ e).1 (List.mem_of_find?_eq_some hf)).1
    exact pop_inv h this
  · exact h

theorem clear_inv (bk : Nat → Nat) (n : Nat) : Inv bk n T.new := new_inv bk n

/-- The table never holds more than `n` entries, after any call. -/
theorem len_le {bk n t} (h : Inv bk n t) : t.order.length ≤ n := by
  have := h.len_le; have := h.len_eq; omega

/-! ### Removal -/

/-- A removal that finds the key takes the newest push of it: the entry `find` gives. The order list loses that entry
and no other; the entry is gone from every chain. -/
theorem remove_some {bk n t} (h : Inv bk n t) {k : Nat} {e : E} (hf : find bk t k = some e) :
    (remove bk t k).2 = some e.v ∧ (remove bk t k).1.order = t.order.filter (fun x => x.s != e.s)
    ∧ e ∈ t.order ∧ (∀ x ∈ t.order, x.k = k → x.s ≤ e.s)
    ∧ (∀ b, e ∉ (remove bk t k).1.chain b) ∧ e ∉ (remove bk t k).1.order
    ∧ ∀ x ∈ t.order, x ≠ e → x ∈ (remove bk t k).1.order := by
  have hn := find_newest h hf
  have hr : remove bk t k = (pop t e, some e.v) := by simp [remove, hf]
  rw [hr]
  refine ⟨rfl, rfl, hn.1, hn.2.2, ?_, ?_, ?_⟩
  · intro b hb; simp [pop, List.mem_filter] at hb
  · simp [pop, List.mem_filter]
  · intro x hx hne
    simp only [pop, List.mem_filter]
    refine ⟨hx, ?_⟩
    simpa using fun hs => hne (eq_of_s h.ord_nodup hx hn.1 hs)

/-- A removal of a key nobody holds changes nothing. -/
theorem remove_none {bk n t} (h : Inv bk n t) {k : Nat} (hf : find bk t k = none) :
    (remove bk t k).2 = none ∧ (remove bk t k).1 = t ∧ ∀ x ∈ t.order, x.k ≠ k := by
  refine ⟨?_, ?_, (find_none_iff h k).1 hf⟩ <;> simp [remove, hf]

/-- After a removal every other entry is still found (the table is well formed, so `findable` applies to it). -/
theorem remove_found {bk n t} (h : Inv bk n t) (k : Nat) {x : E} (hx : x ∈ (remove bk t k).1.order) :
    ∃ e', find bk (remove bk t k).1 x.k = some e' ∧ e'.k = x.k ∧ x.s ≤ e'.s :=
  findable (remove_inv h k) hx

theorem removePair_some {bk n t} (h : Inv bk n t) {k v : Nat} {e : E}
    (hf : (t.chain (bk k)).find? (fun x => x.k == k && x.v == v) = some e) :
    (removePair bk t k v).2 = true ∧ e.k = k ∧ e.v = v ∧ e ∈ t.order
    ∧ (removePair bk t k v).1.order = t.order.filter (fun x => x.s != e.s)
    ∧ (∀ b, e ∉ (removePair bk t k v).1.chain b) ∧ e ∉ (removePair bk t k v).1.order
    ∧ ∀ x ∈ t.order, x ≠ e → x ∈ (removePair bk t k v).1.order := by
  have hm := ((h.chain_iff _ e).1 (List.mem_of_find?_eq_some hf)).1
  have hp := List.find?_some hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have hr : removePair bk t k v = (pop t e, true) := by simp [removePair, hf]
  rw [hr]
  refine ⟨rfl, hp.1, hp.2, hm, rfl, ?_, ?_, ?_⟩
  · intro b hb; simp [pop, List.mem_filter] at hb
  · simp [pop, List.mem_filter]
  · intro x hx hne
    simp only [pop, List.mem_filter]
    refine ⟨hx, ?_⟩
    simpa using fun hs => hne (eq_of_s h.ord_nodup hx hm hs)

theorem removePair_none {bk t} {k v : Nat}
    (hf : (t.chain (bk k)).find? (fun x => x.k == k && x.v == v) = none) :
    removePair bk t k v = (t, false) := by
  simp [removePair, hf]

theorem removePair_found {bk n t} (h : Inv bk n t) (k v : Nat) {x : E} (hx : x ∈ (removePair bk t k v).1.order) :
    ∃ e', find bk (removePair bk t k v).1 x.k = some e' ∧ e'.k = x.k ∧ x.s ≤ e'.s :=
  findable (removePair_inv h k v) hx

/-! ### Duplicates -/

theorem new_uniq : Uniq T.new := by intro x hx; simp [T.new] at hx

theorem pop_uniq {t : T} (h : Uniq t) (e : E) : Uniq (pop t e) := by
  intro x hx y hy hk
  simp only [pop, List.mem_filter] at hx hy
  exact h x hx.1 y hy.1 hk

theorem setV_uniq {t : T} (h : Uniq t) (s v : Nat) : Uniq (setV t s v) := by
  intro x hx y hy hk
  simp only [setV, List.mem_map] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hk' : a.k = b.k := by
    by_cases h1 : a.s = s <;> by_cases h2 : b.s = s <;> simpa [h1, h2] using hk
  rw [h a ha b hb hk']

/-- A push of a key nobody holds keeps every key at one entry. -/
theorem push_uniq {bk n t} {k v : Nat} (h : Uniq t) (hn : ∀ x ∈ t.order, x.k ≠ k) :
    Uniq (push bk n t k v).1 := by
  unfold push
  by_cases hl : t.len < n
  · simp only [hl, ite_true]
    intro x hx y hy hk
    simp only [List.mem_append, List.mem_singleton] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact h x hx y hy hk
    · subst hy; exact absurd hk (hn x hx)
    · subst hx; exact absurd hk.symm (hn y hy)
    · rw [hx, hy]
  · simpa [hl] using h

theorem insert_uniq {bk n t} (h : Inv bk n t) (hu : Uniq t) (k v : Nat) : Uniq (insert bk n t k v).1 := by
  unfold insert
  split
  · exact setV_uniq hu _ _
  · rename_i hf
    have hn := (find_none_iff h k).1 hf
    split
    · split
      · rename_i o rest ho
        exact push_uniq (pop_uniq hu o) (by
          intro x hx; simp only [pop, List.mem_filter] at hx; exact hn x hx.1)
      · exact push_uniq hu hn
    · exact push_uniq hu hn

theorem insertRoom_uniq {bk n t} (h : Inv bk n t) (hu : Uniq t) (k v : Nat) :
    Uniq (insertRoom bk n t k v).1 := by
  unfold insertRoom
  split
  · exact setV_uniq hu _ _
  · rename_i hf; exact push_uniq hu ((find_none_iff h k).1 hf)

theorem remove_uniq {bk t} (hu : Uniq t) (k : Nat) : Uniq (remove bk t k).1 := by
  unfold remove; split
  · exact pop_uniq hu _
  · exact hu

theorem removePair_uniq {bk t} (hu : Uniq t) (k v : Nat) : Uniq (removePair bk t k v).1 := by
  unfold removePair; split
  · exact pop_uniq hu _
  · exact hu

theorem touch_uniq {bk n t} (h : Inv bk n t) (hu : Uniq t) (k : Nat) : Uniq (touch bk t k) := by
  unfold touch
  split
  · rename_i e hf
    split
    · exact hu
    · intro x hx y hy hk
      simp only [List.mem_append, List.mem_filter, List.mem_singleton] at hx hy
      have hm : e ∈ t.order := (find_newest h hf).1
      rcases hx with hx | rfl <;> rcases hy with hy | rfl
      · exact hu x hx.1 y hy.1 hk
      · exact hu x hx.1 y hm hk
      · exact hu x hm y hy.1 hk
      · rfl
  · exact hu

/-- `insert_dup` of a key puts a second holder in front of the first: the holders are the new entry, then the old
ones. -/
theorem insertDup_holders {bk n t} {k v : Nat} (hl : t.len < n) :
    holders bk (insertDup bk n t k v).1 k = (⟨k, v, t.ctr⟩ : E) :: holders bk t k := by
  simp [insertDup, push, hl, holders]

theorem insertDup_ok {bk n t} {k v : Nat} (hl : t.len < n) : (insertDup bk n t k v).2 = true := by
  simp [insertDup, push, hl]

/-! ### Insert and eviction -/

/-- An insert of a held key sets the value of the newest push and moves nothing: the keys of the order list are the
same in the same places, and nothing is evicted. -/
theorem insert_held {bk n t} {k v : Nat} {e : E} (hf : find bk t k = some e) :
    (insert bk n t k v).2 = none ∧ (insert bk n t k v).1.order = t.order.map (fun x => if x.s = e.s then { x with v := v } else x)
    ∧ (insert bk n t k v).1.order.map (·.k) = t.order.map (·.k) := by
  have hr : insert bk n t k v = (setV t e.s v, none) := by simp [insert, hf]
  rw [hr]
  refine ⟨rfl, rfl, ?_⟩
  simp only [setV]
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  by_cases hs : x.s = e.s <;> simp [hs]

/-- An insert of a new key into a table of `n` entries evicts exactly the head of the order list, the oldest, and
appends the new entry as the newest. -/
theorem insert_full {bk n t} {k v : Nat} {o : E} {rest : List E} (hf : find bk t k = none) (hfull : t.len = n)
    (ho : t.order = o :: rest) (hn : 0 < n) (h : Inv bk n t) :
    (insert bk n t k v).2 = some (o.k, o.v) ∧ (insert bk n t k v).1.order = rest ++ [⟨k, v, t.ctr⟩] := by
  have hlen : t.len = rest.length + 1 := by rw [h.len_eq, ho]; rfl
  have hpo : (pop t o).order = rest := by
    simp only [pop, ho, List.filter_cons]
    have hr : ∀ x ∈ rest, x.s ≠ o.s := by
      have := h.ord_nodup; rw [ho, List.pairwise_cons] at this
      exact fun x hx => (this.1 x hx).symm
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact List.filter_eq_self.2 (fun x hx => by simpa using hr x hx)
  have hl : (pop t o).len < n := by simp only [pop]; omega
  have hr : insert bk n t k v = ((push bk n (pop t o) k v).1, some (o.k, o.v)) := by
    simp [insert, hf, hfull, ho]
  rw [hr]
  refine ⟨rfl, ?_⟩
  simp only [push, hl, ite_true, hpo]
  rfl

/-- An insert of a new key into a table with room appends it and evicts nothing. -/
theorem insert_room {bk n t} {k v : Nat} (hf : find bk t k = none) (hl : t.len < n) :
    (insert bk n t k v).2 = none ∧ (insert bk n t k v).1.order = t.order ++ [⟨k, v, t.ctr⟩] := by
  have hne : t.len ≠ n := by omega
  simp [insert, hf, hne, push, hl]

/-- Something is evicted only when the key is new and the table holds `n` entries. -/
theorem insert_evicts {bk n t} {k v : Nat} {p : Nat × Nat} (h : (insert bk n t k v).2 = some p) :
    find bk t k = none ∧ t.len = n := by
  unfold insert at h
  split at h
  · simp at h
  · rename_i hf
    refine ⟨hf, ?_⟩
    split at h
    · assumption
    · simp at h

/-! ### Refusal on a full table -/

theorem insertDup_full {bk n t} {k v : Nat} (hfull : t.len = n) : insertDup bk n t k v = (t, false) := by
  simp [insertDup, push, hfull]

theorem insertRoom_full {bk n t} {k v : Nat} (hf : find bk t k = none) (hfull : t.len = n) :
    insertRoom bk n t k v = (t, false) := by
  simp [insertRoom, hf, push, hfull]

/-- `insert_room` of a held key succeeds on a full table and sets the value. -/
theorem insertRoom_held {bk n t} {k v : Nat} {e : E} (hf : find bk t k = some e) :
    (insertRoom bk n t k v).2 = true := by
  simp [insertRoom, hf]

/-! ### Axioms -/

end Vinc.CoreTable

#audit_axioms Vinc.CoreTable.new_inv
#audit_axioms Vinc.CoreTable.insert_inv
#audit_axioms Vinc.CoreTable.insertRoom_inv
#audit_axioms Vinc.CoreTable.insertDup_inv
#audit_axioms Vinc.CoreTable.remove_inv
#audit_axioms Vinc.CoreTable.removePair_inv
#audit_axioms Vinc.CoreTable.touch_inv
#audit_axioms Vinc.CoreTable.len_le
#audit_axioms Vinc.CoreTable.findable
#audit_axioms Vinc.CoreTable.holders_iff
#audit_axioms Vinc.CoreTable.matches_cut
#audit_axioms Vinc.CoreTable.matches_all
#audit_axioms Vinc.CoreTable.remove_some
#audit_axioms Vinc.CoreTable.remove_none
#audit_axioms Vinc.CoreTable.remove_found
#audit_axioms Vinc.CoreTable.removePair_some
#audit_axioms Vinc.CoreTable.insert_uniq
#audit_axioms Vinc.CoreTable.insertRoom_uniq
#audit_axioms Vinc.CoreTable.remove_uniq
#audit_axioms Vinc.CoreTable.removePair_uniq
#audit_axioms Vinc.CoreTable.touch_uniq
#audit_axioms Vinc.CoreTable.insertDup_holders
#audit_axioms Vinc.CoreTable.insert_held
#audit_axioms Vinc.CoreTable.insert_full
#audit_axioms Vinc.CoreTable.insert_room
#audit_axioms Vinc.CoreTable.insert_evicts
#audit_axioms Vinc.CoreTable.insertDup_full
#audit_axioms Vinc.CoreTable.insertRoom_full
