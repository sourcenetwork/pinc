import Vinc.Axioms

/-!
# Components of the adjacency records: the labels a hub uses are exactly connectivity

The unbounded counterpart of `proofs/tla/BroadcastReach.tla` for `vinc-broadcast` `reach.rs` (`Reach::rebuild`,
`Reach::class`, `reaches`). Each member's record names its peers (`peers : Nat → List Nat`); a hub keeps an edge only
when both ends name each other (`edge`, symmetric: `edge_symm`). The hub labels the members by joining, edge by edge,
the classes of the two ends (`union`, the quick-find form of the code's union-find; the Rust test
`the_hub_components_equal_breadth_first_search_on_random_graphs_with_one_sided_claims` checks the code against a
breadth-first search). Facts, for every set of records:

- `labels_iff`: two members get the same label exactly when a chain of edges links them (the component invariant);
- `one_sided_no_edge`: a record that names a peer that does not name it back makes no edge;
- `reach_mono`, `split_narrows`: records that only drop peers (a session that ended) never link two members that
  were not linked before, so a split never widens anyone's reach.
-/

namespace Vinc.BroadcastReach

/-- An edge of the hub's graph: each end's record names the other. -/
def edge (peers : Nat → List Nat) (u v : Nat) : Prop := v ∈ peers u ∧ u ∈ peers v

instance (peers : Nat → List Nat) (u v : Nat) : Decidable (edge peers u v) := by
  unfold edge; infer_instance

/-- The graph is undirected. -/
theorem edge_symm {peers : Nat → List Nat} {u v : Nat} (h : edge peers u v) : edge peers v u := ⟨h.2, h.1⟩

/-- A record naming a peer whose own record does not name it back makes no edge: one end's word is not enough. -/
theorem one_sided_no_edge {peers : Nat → List Nat} {u v : Nat} (h : u ∉ peers v) : ¬ edge peers u v :=
  fun e => h e.2

/-- `u` and `v` are linked by a chain of `E` edges (the reflexive, transitive closure, read left to right). -/
inductive Linked (E : Nat → Nat → Prop) : Nat → Nat → Prop
  | refl (u : Nat) : Linked E u u
  | step {u w v : Nat} : Linked E u w → E w v → Linked E u v

theorem Linked.trans {E : Nat → Nat → Prop} {u w v : Nat} (h1 : Linked E u w) (h2 : Linked E w v) :
    Linked E u v := by
  induction h2 with
  | refl => exact h1
  | step _ e ih => exact Linked.step ih e

theorem Linked.single {E : Nat → Nat → Prop} {u v : Nat} (e : E u v) : Linked E u v :=
  Linked.step (Linked.refl u) e

/-- Over a symmetric relation, a chain read backwards is a chain. -/
theorem Linked.symm {E : Nat → Nat → Prop} (hs : ∀ a b, E a b → E b a) {u v : Nat} (h : Linked E u v) :
    Linked E v u := by
  induction h with
  | refl => exact Linked.refl _
  | step _ e ih => exact Linked.trans (Linked.single (hs _ _ e)) ih

/-- More edges link at least as much. -/
theorem reach_mono {E F : Nat → Nat → Prop} (hEF : ∀ a b, E a b → F a b) {u v : Nat} (h : Linked E u v) :
    Linked F u v := by
  induction h with
  | refl => exact Linked.refl _
  | step _ e ih => exact Linked.step ih (hEF _ _ e)

/-- Records that only drop peers (`peers' u ⊆ peers u` for every member) link no pair the old records did not:
a session that ends narrows the components, never widens them. -/
theorem split_narrows {peers peers' : Nat → List Nat} (hsub : ∀ u x, x ∈ peers' u → x ∈ peers u) {u v : Nat}
    (h : Linked (edge peers') u v) : Linked (edge peers) u v :=
  reach_mono (fun _ _ e => ⟨hsub _ _ e.1, hsub _ _ e.2⟩) h

/-- A function equal on the two ends of every edge is equal on the two ends of every chain. -/
theorem const_on_linked {E : Nat → Nat → Prop} {f : Nat → Nat} (hf : ∀ a b, E a b → f a = f b) {u v : Nat}
    (h : Linked E u v) : f u = f v := by
  induction h with
  | refl => rfl
  | step _ e ih => exact ih.trans (hf _ _ e)

/-- The edges of a list of pairs, both ways round. -/
def rel (es : List (Nat × Nat)) (a b : Nat) : Prop := (a, b) ∈ es ∨ (b, a) ∈ es

theorem rel_symm (es : List (Nat × Nat)) : ∀ a b, rel es a b → rel es b a := fun _ _ h => h.symm

/-- Join the classes of `a` and `b`: every member labelled as `a` or as `b` takes the smaller of the two labels. -/
def union (lab : Nat → Nat) (a b : Nat) (x : Nat) : Nat :=
  if lab x = lab a ∨ lab x = lab b then min (lab a) (lab b) else lab x

/-- The labels after joining along every pair of `es`, in order, from every member alone (`lab x = x`). -/
def labels (es : List (Nat × Nat)) : Nat → Nat := es.foldl (fun lab e => union lab e.1 e.2) id

/-- The invariant: the labels say exactly which members the edges link. -/
def Inv (es : List (Nat × Nat)) (lab : Nat → Nat) : Prop := ∀ u v, lab u = lab v ↔ Linked (rel es) u v

theorem inv_nil : Inv [] id := by
  intro u v
  constructor
  · intro h; simp only [id] at h; subst h; exact Linked.refl _
  · intro h
    exact const_on_linked (f := id) (fun a b hab => by simp [rel] at hab) h

theorem rel_append {es : List (Nat × Nat)} {a b x y : Nat} (h : rel es x y) : rel (es ++ [(a, b)]) x y := by
  rcases h with h | h
  · exact Or.inl (List.mem_append_left _ h)
  · exact Or.inr (List.mem_append_left _ h)

theorem rel_new (es : List (Nat × Nat)) (a b : Nat) : rel (es ++ [(a, b)]) a b :=
  Or.inl (List.mem_append_right _ (List.mem_singleton.mpr rfl))

theorem rel_append_cases {es : List (Nat × Nat)} {a b x y : Nat} (h : rel (es ++ [(a, b)]) x y) :
    rel es x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  rcases h with h | h
  · rcases List.mem_append.mp h with h | h
    · exact Or.inl (Or.inl h)
    · simp at h; exact Or.inr (Or.inl ⟨h.1, h.2⟩)
  · rcases List.mem_append.mp h with h | h
    · exact Or.inl (Or.inr h)
    · simp at h; exact Or.inr (Or.inr ⟨h.2, h.1⟩)

/-- Joining along one more edge keeps the invariant. -/
theorem inv_union {es : List (Nat × Nat)} {lab : Nat → Nat} (hi : Inv es lab) (a b : Nat) :
    Inv (es ++ [(a, b)]) (union lab a b) := by
  have mono : ∀ {x y}, Linked (rel es) x y → Linked (rel (es ++ [(a, b)])) x y :=
    fun h => reach_mono (fun _ _ e => rel_append e) h
  have ab : Linked (rel (es ++ [(a, b)])) a b := Linked.single (rel_new es a b)
  have symm : ∀ {x y}, Linked (rel (es ++ [(a, b)])) x y → Linked (rel (es ++ [(a, b)])) y x :=
    fun h => Linked.symm (rel_symm _) h
  -- A member relabelled to the joined class is linked to `a`.
  have toA : ∀ x, (lab x = lab a ∨ lab x = lab b) → Linked (rel (es ++ [(a, b)])) x a := by
    intro x hx
    rcases hx with hx | hx
    · exact mono ((hi x a).mp hx)
    · exact Linked.trans (mono ((hi x b).mp hx)) (symm ab)
  intro u v
  constructor
  · intro h
    unfold union at h
    by_cases hu : lab u = lab a ∨ lab u = lab b <;> by_cases hv : lab v = lab a ∨ lab v = lab b <;>
      simp only [hu, hv, ite_true, ite_false] at h
    · exact Linked.trans (toA u hu) (symm (toA v hv))
    · exfalso; apply hv
      rcases Nat.le_total (lab a) (lab b) with hle | hle
      · rw [Nat.min_eq_left hle] at h; exact Or.inl h.symm
      · rw [Nat.min_eq_right hle] at h; exact Or.inr h.symm
    · exfalso; apply hu
      rcases Nat.le_total (lab a) (lab b) with hle | hle
      · rw [Nat.min_eq_left hle] at h; exact Or.inl h
      · rw [Nat.min_eq_right hle] at h; exact Or.inr h
    · exact mono ((hi u v).mp h)
  · intro h
    refine const_on_linked (f := union lab a b) (fun x y hxy => ?_) h
    rcases rel_append_cases hxy with hxy | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have heq : lab x = lab y := (hi x y).mpr (Linked.single hxy)
      unfold union; rw [heq]
    · unfold union; simp
    · unfold union; simp

/-- Folding the joins over a list keeps the invariant. -/
theorem inv_foldl (es : List (Nat × Nat)) :
    ∀ (done : List (Nat × Nat)) (lab : Nat → Nat), Inv done lab →
      Inv (done ++ es) (es.foldl (fun lab e => union lab e.1 e.2) lab) := by
  induction es with
  | nil => intro done lab h; simpa using h
  | cons e rest ih =>
    intro done lab h
    have h1 := inv_union h e.1 e.2
    have h2 := ih (done ++ [(e.1, e.2)]) (union lab e.1 e.2) h1
    simpa [List.foldl, List.append_assoc] using h2

/-- The component invariant over any list of edges: same label exactly when linked. -/
theorem labels_rel (es : List (Nat × Nat)) (u v : Nat) : labels es u = labels es v ↔ Linked (rel es) u v := by
  have h := inv_foldl es [] id inv_nil
  simpa [labels] using h u v

/-- The pairs of members of `ns` that the records join: the edge list `Reach::rebuild` walks. -/
def edges (ns : List Nat) (peers : Nat → List Nat) : List (Nat × Nat) :=
  ns.flatMap fun u => (ns.filter fun v => decide (edge peers u v)).map fun v => (u, v)

theorem mem_edges {ns : List Nat} {peers : Nat → List Nat} {a b : Nat} :
    (a, b) ∈ edges ns peers ↔ a ∈ ns ∧ b ∈ ns ∧ edge peers a b := by
  simp [edges]

/-- The edges of the hub's graph among the members it holds records of. -/
def hubEdge (ns : List Nat) (peers : Nat → List Nat) (a b : Nat) : Prop := a ∈ ns ∧ b ∈ ns ∧ edge peers a b

theorem rel_edges_iff {ns : List Nat} {peers : Nat → List Nat} {a b : Nat} :
    rel (edges ns peers) a b ↔ hubEdge ns peers a b := by
  unfold rel hubEdge
  rw [mem_edges, mem_edges]
  constructor
  · rintro (h | ⟨hb, ha, e⟩)
    · exact h
    · exact ⟨ha, hb, edge_symm e⟩
  · intro h; exact Or.inl h

/-- The labels a hub computes from its records give the same label to two members exactly when a chain of edges,
both ends of each naming the other, links them. -/
theorem labels_iff (ns : List Nat) (peers : Nat → List Nat) (u v : Nat) :
    labels (edges ns peers) u = labels (edges ns peers) v ↔ Linked (hubEdge ns peers) u v := by
  rw [labels_rel]
  constructor
  · exact reach_mono (fun _ _ h => rel_edges_iff.mp h)
  · exact reach_mono (fun _ _ h => rel_edges_iff.mpr h)

/-- The decision `reaches` takes: a hub hands a message from `o` to `s` when their labels are equal. It does so
exactly when the hub's graph links them. -/
theorem reaches_iff (ns : List Nat) (peers : Nat → List Nat) (o s : Nat) :
    labels (edges ns peers) o = labels (edges ns peers) s ↔ Linked (hubEdge ns peers) o s :=
  labels_iff ns peers o s

/-- After a split (records that only dropped peers, over the same members), a pair the hub now hands messages
between was already handed them before: a component never grows when sessions end. -/
theorem split_never_widens (ns : List Nat) {peers peers' : Nat → List Nat}
    (hsub : ∀ u x, x ∈ peers' u → x ∈ peers u) (o s : Nat)
    (h : labels (edges ns peers') o = labels (edges ns peers') s) :
    labels (edges ns peers) o = labels (edges ns peers) s := by
  rw [labels_iff] at h ⊢
  exact reach_mono (fun _ _ e => ⟨e.1, e.2.1, hsub _ _ e.2.2.1, hsub _ _ e.2.2.2⟩) h

/-! ## The class of a node, with a bounded table (`Reach::class`)

The hub keeps at most `Limits::max_reach` records. A node it holds a record of is in its component (`label`). A
node it holds none of is unscoped while the table is open, and alone once the table refused a record and closed:
the refused node may be any node without a record, so each of them must be alone. -/

/-- What a hub hands messages by: a component's label, a node alone, or the unscoped class. -/
inductive Cls
  -- in the component labelled by this id
  | label (l : Nat)
  -- alone: no record here, and the table is closed
  | alone (n : Nat)
  -- never named its peers, and the table is open
  | unscoped
  deriving DecidableEq

/-- The class of `n` at a hub: `rec n` says whether the hub holds its record, `lab` is the labels of the records,
`closed` whether the table refused a record. -/
def cls (closed : Bool) (rec : Nat → Bool) (lab : Nat → Nat) (n : Nat) : Cls :=
  -- a record: its component; none: alone once closed, unscoped otherwise
  if rec n then .label (lab n) else if closed then .alone n else .unscoped

/-- Once the table is closed, a node without a record shares its class with no other node: a refused newcomer
hears nobody it is not linked to. -/
theorem closed_unknown_alone {rec : Nat → Bool} {lab : Nat → Nat} {a b : Nat} (ha : rec a = false)
    (hab : a ≠ b) : cls true rec lab a ≠ cls true rec lab b := by
  -- unfold the class and split on whether `b` has a record; `alone a` is neither `label _` nor `alone b`
  unfold cls
  cases hb : rec b <;> simp [ha, hab]

/-- The fallback the closed table avoids: while it is open, any two nodes without a record share the unscoped
class, so a refused newcomer would hear every other one (the `BroadcastReach_full` RED configuration). -/
theorem open_unknown_shared {rec : Nat → Bool} {lab : Nat → Nat} {a b : Nat} (ha : rec a = false)
    (hb : rec b = false) : cls false rec lab a = cls false rec lab b := by
  -- both are `unscoped`
  simp [cls, ha, hb]

/-- A node with a record is never unscoped, whether the table is open or closed. -/
theorem recorded_scoped {closed : Bool} {rec : Nat → Bool} {lab : Nat → Nat} {n : Nat} (h : rec n = true) :
    cls closed rec lab n = .label (lab n) := by
  -- the first branch of `cls`
  simp [cls, h]

/-- Two nodes with records share a class exactly when they share a label, which `labels_iff` makes connectivity. -/
theorem recorded_iff {closed : Bool} {rec : Nat → Bool} {lab : Nat → Nat} {a b : Nat} (ha : rec a = true)
    (hb : rec b = true) : cls closed rec lab a = cls closed rec lab b ↔ lab a = lab b := by
  -- both are `label _`, and `label` is injective
  simp [cls, ha, hb]

end Vinc.BroadcastReach

#audit_axioms Vinc.BroadcastReach.labels_iff
#audit_axioms Vinc.BroadcastReach.reaches_iff
#audit_axioms Vinc.BroadcastReach.split_never_widens
#audit_axioms Vinc.BroadcastReach.closed_unknown_alone
#audit_axioms Vinc.BroadcastReach.recorded_iff
