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
  were not linked before, so a split never widens anyone's reach;
- `closed_unknown_alone`, `reopened_refused_iff`: a closed table keeps a node without a record alone, and a table
  opened again once every refused node has a record keeps each of them in its component;
- `log_push_inv`, `log_pop_inv`, `log_holds_iff`: the per-origin counts of a hub's log stay equal to its entries,
  so `HubLog::holds` answers whether any message of an origin is logged;
- `running_charge`, `take_within`, `shrink_le`: the table's running count of bytes stays the sum of its records'
  charges, and within `Limits::reach_bytes`.
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

The hub keeps records up to `Limits::reach_bytes`. A node it holds a record of is in its component (`label`). A
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

/-! ## Opening a closed table again (`Reach::reopen`)

The table opens again only when no refused node waits for a record: every node it refused has one now (or was
revoked, or left with nothing of it in the logs, so it is neither an origin nor a subscriber here). A refused node
then keeps its component's reach exactly: it shares a class with another node only when both have records and the
same label. Opening while one still waits is the `open_unknown_shared` fallback again (`BroadcastReach_reopen`). -/

/-- Once open again, a node with a record, as every refused node has, shares a class with `b` exactly when `b` has a
record too and the same label: never with a node without one. -/
theorem reopened_refused_iff {rec : Nat → Bool} {lab : Nat → Nat} {a b : Nat} (ha : rec a = true) :
    cls false rec lab a = cls false rec lab b ↔ rec b = true ∧ lab a = lab b := by
  -- split on whether `b` has a record: `label _` is never `unscoped`, and `label` is injective
  cases hb : rec b <;> simp [cls, ha, hb]

/-! ## The count of each origin in a hub's log (`HubLog::push`, `HubLog::pop`, `HubLog::holds`)

A hub drops a released member's tombstone, and forgets a refused member that left, once no log holds a message of
it. The log keeps a count of its messages by origin beside its entries, raised when it pushes one and lowered when it
pops one, so the question is a lookup and not a walk over every message. The counts stay equal to the entries. -/

/-- A log: the origins of its entries, oldest first, and the count kept for each origin. -/
structure Log where
  -- the origin of each logged message, oldest first
  entries : List Nat
  -- the count the log keeps for each origin
  cnt : Nat → Nat

/-- The counts are those of the entries. -/
def Log.Inv (l : Log) : Prop := ∀ o, l.cnt o = l.entries.count o

/-- Push a message of `o`: it goes last, and the count of `o` goes up by one. -/
def Log.push (l : Log) (o : Nat) : Log :=
  -- the entries with `o` appended, and the count of `o` raised
  { entries := l.entries ++ [o], cnt := fun x => if x = o then l.cnt x + 1 else l.cnt x }

/-- Pop the oldest message: the count of its origin goes down by one. An empty log stays as it is. -/
def Log.pop (l : Log) : Log :=
  match l.entries with
  -- nothing to pop
  | [] => l
  -- the oldest goes, and its origin's count is lowered
  | o :: rest => { entries := rest, cnt := fun x => if x = o then l.cnt x - 1 else l.cnt x }

/-- An empty log with no counts keeps the invariant. -/
theorem log_empty_inv : (Log.mk [] (fun _ => 0)).Inv := by
  -- no entry counts anything
  intro o; simp

/-- A push keeps the counts equal to the entries. -/
theorem log_push_inv {l : Log} (h : l.Inv) (o : Nat) : (l.push o).Inv := by
  -- the appended entry adds one to the count of `o` and nothing to the others
  intro x
  by_cases hx : x = o
  · subst hx; simp [Log.push, h x]
  · simp [Log.push, hx, h x, Ne.symm hx]

/-- A pop keeps the counts equal to the entries. -/
theorem log_pop_inv {l : Log} (h : l.Inv) : l.pop.Inv := by
  -- split on the entries; the popped origin's count was at least one, so lowering it is exact
  intro x
  have hx := h x
  unfold Log.pop
  split
  · exact hx
  · rename_i o rest he
    rw [he, List.count_cons] at hx
    by_cases hxo : x = o
    · subst hxo; simp at hx ⊢; omega
    · have : (o == x) = false := by simp [Ne.symm hxo]
      simp [hxo, hx, this]

/-- Under the invariant, a log holds a message of `o` exactly when its count of `o` is not zero (`HubLog::holds`,
which keeps no origin at zero). -/
theorem log_holds_iff {l : Log} (h : l.Inv) (o : Nat) : l.cnt o ≠ 0 ↔ o ∈ l.entries := by
  -- the count of `o` in the entries is positive exactly when `o` is one of them
  rw [h o, ← List.count_pos_iff]
  omega

/-! ## The table's bytes (`Reach::take`, `Reach::expire`, `Reach::drop_gone`, `Reach::forget`)

The hub charges each record a fixed share, its peers and its signature (`record_cost`), keeps the sum as a running
count (`Reach::bytes`), and takes a record only when the count minus the record it replaces plus the new one fits
`Limits::reach_bytes`. Here `c n` is what member `n`'s record is charged (0 for none) and `ns` lists every member
once. Changing one member's charge moves the sum by exactly the difference (`total_setc`), so the running count stays
the sum (`running_charge`); a record taken only when it fits keeps the sum within the bytes (`take_within`); and
leaving a tombstone, expiring, dropping or forgetting a record never raises it (`shrink_le`). -/

/-- The charges of the members in `ns`, added up. -/
def total (c : Nat → Nat) : List Nat → Nat
  -- nobody: nothing
  | [] => 0
  -- the first member's charge and the rest's
  | n :: ns => c n + total c ns

/-- The charges `c` with member `n`'s set to `k` (a record taken, a tombstone left, or 0 for a record gone). -/
def setc (c : Nat → Nat) (n k : Nat) : Nat → Nat :=
  -- `n` is charged `k`, everyone else as before
  fun x => if x = n then k else c x

/-- A member that is not in the list does not change its sum. -/
theorem total_setc_notin {c : Nat → Nat} {n k : Nat} : ∀ {ns : List Nat}, n ∉ ns → total (setc c n k) ns = total c ns
  -- no member: both sums are 0
  | [], _ => rfl
  -- the first member is not `n`, so it keeps its charge, and the rest follows by induction
  | a :: ns, h => by
    have ha : a ≠ n := fun e => h (by simp [e])
    have hr : n ∉ ns := fun m => h (by simp [m])
    show (if a = n then k else c a) + total (setc c n k) ns = c a + total c ns
    simp only [ha, ↓reduceIte]
    rw [total_setc_notin hr]

/-- One member's charge is at most the sum it is part of. -/
theorem charge_le_total {c : Nat → Nat} {n : Nat} : ∀ {ns : List Nat}, n ∈ ns → c n ≤ total c ns
  -- the empty list holds nobody
  | [], h => by simp at h
  -- `n` is the first member, or is in the rest
  | a :: ns, h => by
    show c n ≤ c a + total c ns
    rcases List.mem_cons.mp h with e | m
    · subst e; omega
    · have := charge_le_total (c := c) m; omega

/-- Setting the charge of a member listed once to `k` moves the sum by exactly `k` minus its old charge. -/
theorem total_setc {c : Nat → Nat} {n k : Nat} : ∀ {ns : List Nat}, ns.Nodup → n ∈ ns →
    total (setc c n k) ns + c n = total c ns + k
  -- the empty list holds nobody
  | [], _, h => by simp at h
  -- either the first member is `n` (and the rest does not hold it again), or `n` is in the rest
  | a :: ns, hd, h => by
    have hd' := List.nodup_cons.mp hd
    show (if a = n then k else c a) + total (setc c n k) ns + c n = c a + total c ns + k
    by_cases ha : a = n
    · subst ha
      simp only [eq_self, ↓reduceIte]
      rw [total_setc_notin hd'.1]
      omega
    · have hm : n ∈ ns := by
        rcases List.mem_cons.mp h with e | m
        · exact absurd e.symm ha
        · exact m
      have ih := total_setc (c := c) (k := k) hd'.2 hm
      simp only [ha, ↓reduceIte]
      omega

/-- The running count the code keeps (`bytes - held + cost`) is the sum after the change, when it was the sum
before. -/
theorem running_charge {c : Nat → Nat} {ns : List Nat} {n k b : Nat} (hd : ns.Nodup) (hn : n ∈ ns)
    (hb : b = total c ns) : total (setc c n k) ns = b - c n + k := by
  -- the exact difference, and the old charge is part of the old sum, so the subtraction does not saturate
  have h1 := total_setc (c := c) (k := k) hd hn
  have h2 := charge_le_total (c := c) hn
  omega

/-- A record taken only when the running count minus the record it replaces plus its own charge fits the bytes keeps
the table within them; a newcomer is the case `c n = 0`. -/
theorem take_within {c : Nat → Nat} {ns : List Nat} {n k budget : Nat} (hd : ns.Nodup) (hn : n ∈ ns)
    (fits : total c ns - c n + k ≤ budget) : total (setc c n k) ns ≤ budget := by
  -- the new sum is exactly what was checked
  rw [running_charge hd hn rfl]
  exact fits

/-- Lowering a charge (a refused record left a tombstone of the fixed share, a record expired, or one dropped or
forgotten, charged 0) never raises the sum: a table within its bytes stays within them. -/
theorem shrink_le {c : Nat → Nat} {ns : List Nat} {n k : Nat} (hd : ns.Nodup) (hn : n ∈ ns) (hk : k ≤ c n) :
    total (setc c n k) ns ≤ total c ns := by
  -- the exact difference is not positive
  have := total_setc (c := c) (k := k) hd hn
  omega

end Vinc.BroadcastReach

#audit_axioms Vinc.BroadcastReach.labels_iff
#audit_axioms Vinc.BroadcastReach.reaches_iff
#audit_axioms Vinc.BroadcastReach.split_never_widens
#audit_axioms Vinc.BroadcastReach.closed_unknown_alone
#audit_axioms Vinc.BroadcastReach.recorded_iff
#audit_axioms Vinc.BroadcastReach.reopened_refused_iff
#audit_axioms Vinc.BroadcastReach.log_push_inv
#audit_axioms Vinc.BroadcastReach.log_pop_inv
#audit_axioms Vinc.BroadcastReach.log_holds_iff
#audit_axioms Vinc.BroadcastReach.running_charge
#audit_axioms Vinc.BroadcastReach.take_within
#audit_axioms Vinc.BroadcastReach.shrink_le
