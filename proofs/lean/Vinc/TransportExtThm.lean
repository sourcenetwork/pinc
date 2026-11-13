import Vinc.Axioms
import Vinc.TransportExt

/-!
# The extension frame registry and its dispatch: the theorems

For the model of `TransportExt.lean`:

* **The table** (`table_uniq`, `uniq_sound`, `owner_unique`): the const check of `ext.rs` accepts the table, and any
  table it accepts has well-formed ranges at or above the base that are pairwise disjoint, so a type has at most one
  entry and one layer.
* **The decoder** (`registered_decodes`, `registered_sendable`, `decodes_iff`, `unregistered_decodes`): every
  registered type is one the decoder takes as an extension frame and `send_extension` accepts; the decoder takes
  every type from the base up, registered or not (the registry names the types the library sends, it is not a filter).
* **The dispatch** (`route_sub_iff`, `route_reach_iff`, `route_ring_iff`, `route_drop_iff`, `route_exclusive`,
  `ring_not_core`): a frame goes to the sub-session layer exactly when it has that type and a body, to the `REACH_OUT`
  ring exactly with its type and a body of 1 to `REACH_BODY_MAX` bytes, to the application ring exactly with another
  type, a body and an allowed session, and is dropped otherwise; the application ring never takes the type of either
  endpoint layer, and a session not allowed gets nothing in it (`route_gate`).
* **Total over the table** (`route_table`): for each registered type there is an input that reaches the layer that
  registered it, and for the types of the values layer and the transport tests that is the application ring.
* **Unregistered types** (`unregistered_ring`, `unregistered_untaken`): a type at or above the base nobody registered
  goes to the application ring (with a body, on an allowed session) and neither values handler takes it: it is
  ignored, no route closes the connection.
* **The values layer** (`values_no_cross`, `serve_registered`, `fetch_registered`, `values_ring`): the server takes
  `PROOF_REQ` and the fetch takes `PROOF`, no type is taken by both, and each takes only the type registered to it.
-/

namespace Vinc.TransportExt

/-- Split every `if` of the goal, then settle each case by arithmetic or by simplification. -/
local macro "cases_close" : tactic =>
  `(tactic| (repeat' split) <;> first | omega | (simp_all; done) | (simp_all <;> omega))

/-! ## The table -/

theorem table_uniq : uniq table = true := by decide

theorem uniq_sound : ∀ l : List Entry, uniq l = true →
    (∀ e ∈ l, base ≤ e.lo ∧ e.lo ≤ e.hi) ∧ l.Pairwise (fun a b => overlap a b = false)
  | [], _ => ⟨by simp, List.Pairwise.nil⟩
  | e :: es, h => by
    simp only [uniq, Bool.and_eq_true, List.all_eq_true, wf, Bool.not_eq_true', Bool.or_eq_false_iff,
      decide_eq_false_iff_not, Bool.not_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨ih1, ih2⟩ := uniq_sound es h4
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact ih1 x hx
    · refine List.Pairwise.cons ?_ ih2
      intro f hf
      simpa using h3 f hf

/-- At most one entry holds a type, in any table the check accepts. -/
theorem owner_unique_of : ∀ l : List Entry, l.Pairwise (fun a b => overlap a b = false) →
    ∀ e₁ ∈ l, ∀ e₂ ∈ l, ∀ t, covers e₁ t = true → covers e₂ t = true → e₁ = e₂
  | [], _, e, he, _, _, _, _, _ => by simp at he
  | x :: xs, hp, e₁, h₁, e₂, h₂, t, c₁, c₂ => by
    rcases List.pairwise_cons.mp hp with ⟨hx, hxs⟩
    have no : ∀ y ∈ xs, covers x t = true → covers y t = true → False := by
      intro y hy cx cy
      have := hx y hy
      simp only [overlap, covers, Bool.and_eq_true, decide_eq_true_eq] at this cx cy
      simp at this
      omega
    rcases List.mem_cons.mp h₁ with p₁ | m₁ <;> rcases List.mem_cons.mp h₂ with p₂ | m₂
    · rw [p₁, p₂]
    · rw [p₁] at c₁
      exact (no e₂ m₂ c₁ c₂).elim
    · rw [p₂] at c₂
      exact (no e₁ m₁ c₂ c₁).elim
    · exact owner_unique_of xs hxs e₁ m₁ e₂ m₂ t c₁ c₂

theorem owner_unique : ∀ e₁ ∈ table, ∀ e₂ ∈ table, ∀ t, covers e₁ t = true → covers e₂ t = true → e₁ = e₂ :=
  owner_unique_of table (uniq_sound table table_uniq).2

/-- The layer of a type, in full. -/
theorem owner_eq (t : Nat) : owner t =
    if t = 0x40 then some .sub
    else if 0x41 ≤ t ∧ t ≤ 0x43 then some .test
    else if t = 0x44 then some .reach
    else if t = 0x49 then some .serve
    else if t = 0x4f then some .fetch
    else none := by
  unfold owner table covers subOpen testFirst testLast reachOut proofReq proofFrame
  simp only [List.find?]
  by_cases h1 : t = 0x40
  · subst h1; simp
  by_cases h2 : 0x41 ≤ t ∧ t ≤ 0x43
  · have e1 : (decide (0x40 ≤ t) && decide (t ≤ 0x40)) = false := by simp; omega
    simp [e1, h2.1, h2.2]
    omega
  by_cases h3 : t = 0x44
  · subst h3; simp
  by_cases h4 : t = 0x49
  · subst h4; simp
  by_cases h5 : t = 0x4f
  · subst h5; simp
  have h2' : ¬ (0x41 ≤ t ∧ t ≤ 0x43) := h2
  simp only [h1, h2', h3, h4, h5, if_false]
  have e1 : (decide (0x40 ≤ t) && decide (t ≤ 0x40)) = false := by simp; omega
  have e2 : (decide (0x41 ≤ t) && decide (t ≤ 0x43)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  have e3 : (decide (0x44 ≤ t) && decide (t ≤ 0x44)) = false := by simp; omega
  have e4 : (decide (0x49 ≤ t) && decide (t ≤ 0x49)) = false := by simp; omega
  have e5 : (decide (0x4f ≤ t) && decide (t ≤ 0x4f)) = false := by simp; omega
  simp [e1, e2, e3, e4, e5]

theorem owner_sub (t : Nat) : owner t = some .sub ↔ t = subOpen := by
  rw [owner_eq]; unfold subOpen; cases_close

theorem owner_reach (t : Nat) : owner t = some .reach ↔ t = reachOut := by
  rw [owner_eq]; unfold reachOut; cases_close

theorem owner_serve (t : Nat) : owner t = some .serve ↔ t = proofReq := by
  rw [owner_eq]; unfold proofReq; cases_close

theorem owner_fetch (t : Nat) : owner t = some .fetch ↔ t = proofFrame := by
  rw [owner_eq]; unfold proofFrame; cases_close

theorem owner_test (t : Nat) : owner t = some .test ↔ testFirst ≤ t ∧ t ≤ testLast := by
  rw [owner_eq]; unfold testFirst testLast; cases_close

/-! ## The decoder -/

theorem decodes_iff (t : Nat) : decodesExt t = true ↔ base ≤ t := by simp [decodesExt]

theorem registered_decodes (t : Nat) (w : Who) (h : owner t = some w) : decodesExt t = true := by
  have : base ≤ t := by
    rw [owner_eq] at h
    unfold base
    repeat' split at h
    all_goals (first | omega | simp at h)
  exact (decodes_iff t).2 this

theorem registered_sendable (t : Nat) (w : Who) (h : owner t = some w) : sendOk t = true := by
  simpa [sendOk, decodesExt] using registered_decodes t w h

theorem unregistered_decodes (t : Nat) (hb : base ≤ t) (h : owner t = none) :
    decodesExt t = true ∧ ∀ w, owner t ≠ some w := by
  refine ⟨(decodes_iff t).2 hb, fun w hw => ?_⟩
  rw [h] at hw
  simp at hw

/-! ## The dispatch -/

theorem route_sub_iff (ty len : Nat) (a : Bool) : route ty len a = .sub ↔ ty = subOpen ∧ 0 < len := by
  unfold route subOpen reachOut reachMax; cases_close

theorem route_reach_iff (ty len : Nat) (a : Bool) :
    route ty len a = .reach ↔ ty = reachOut ∧ 0 < len ∧ len ≤ reachMax := by
  unfold route subOpen reachOut reachMax; cases_close

theorem route_ring_iff (ty len : Nat) (a : Bool) :
    route ty len a = .ring ↔ ty ≠ subOpen ∧ ty ≠ reachOut ∧ 0 < len ∧ a = true := by
  unfold route subOpen reachOut reachMax; cases_close

theorem route_drop_iff (ty len : Nat) (a : Bool) :
    route ty len a = .drop ↔ route ty len a ≠ .sub ∧ route ty len a ≠ .reach ∧ route ty len a ≠ .ring := by
  unfold route subOpen reachOut reachMax; cases_close

/-- Each frame goes to exactly one place, and only a frame of its type goes to an endpoint layer. -/
theorem route_exclusive (ty len : Nat) (a : Bool) :
    (route ty len a = .sub → ty = subOpen) ∧ (route ty len a = .reach → ty = reachOut) ∧
    (route ty len a = .ring → ty ≠ subOpen ∧ ty ≠ reachOut) := by
  refine ⟨fun h => ((route_sub_iff ..).1 h).1, fun h => ((route_reach_iff ..).1 h).1, fun h => ?_⟩
  have := (route_ring_iff ..).1 h
  exact ⟨this.1, this.2.1⟩

/-- The application ring never takes the type of an endpoint layer. -/
theorem ring_not_core (ty len : Nat) (a : Bool) (h : route ty len a = .ring) :
    owner ty ≠ some .sub ∧ owner ty ≠ some .reach := by
  have := (route_ring_iff ..).1 h
  exact ⟨fun e => this.1 ((owner_sub ty).1 e), fun e => this.2.1 ((owner_reach ty).1 e)⟩

/-- A session the access check has not allowed gets nothing in the application ring. -/
theorem route_gate (ty len : Nat) : route ty len false ≠ .ring := by
  intro h
  have := (route_ring_iff ..).1 h
  simp at this

/-- Every type, length and answer has a place: `route` is a total function. -/
theorem route_cases (ty len : Nat) (a : Bool) :
    route ty len a = .sub ∨ route ty len a = .reach ∨ route ty len a = .ring ∨ route ty len a = .drop := by
  unfold route; cases_close

/-- The same through the lookup: a type with a layer reaches that layer. -/
theorem route_owner (t : Nat) (w : Who) (h : owner t = some w) : route t 1 true = destOf w := by
  rw [owner_eq] at h
  repeat' split at h
  all_goals (first | (simp at h; done) | skip)
  all_goals (injection h with h; subst h; unfold route destOf subOpen reachOut reachMax; cases_close)

/-- The dispatch is total over the table: every type of every entry, with a body of one byte on an allowed session,
reaches the layer that registered it. -/
theorem route_table : ∀ e ∈ table, ∀ t, covers e t = true → route t 1 true = destOf e.who := by
  intro e he t ht
  simp only [table, List.mem_cons, List.not_mem_nil, or_false] at he
  have ho : owner t = some e.who := by
    rw [owner_eq]
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp [covers, subOpen, testFirst, testLast, reachOut, proofReq, proofFrame] at ht <;>
      (obtain ⟨ha, hb⟩ := ht
       have ha' := of_decide_eq_true ha
       have hb' := of_decide_eq_true hb
       cases_close)
  exact route_owner t e.who ho

/-! ## Unregistered types -/

theorem unregistered_ring (t len : Nat) (a : Bool) (h : owner t = none) :
    route t len a = .ring ↔ 0 < len ∧ a = true := by
  rw [route_ring_iff]
  constructor
  · intro h'; exact ⟨h'.2.2.1, h'.2.2.2⟩
  · intro h'
    refine ⟨fun e => ?_, fun e => ?_, h'.1, h'.2⟩
    · have : owner t = some .sub := (owner_sub t).2 e
      rw [h] at this; simp at this
    · have : owner t = some .reach := (owner_reach t).2 e
      rw [h] at this; simp at this

theorem unregistered_untaken (t : Nat) (h : owner t = none) : serveTakes t = false ∧ fetchTakes t = false := by
  constructor
  · rcases hs : serveTakes t with _ | _
    · rfl
    · have : t = proofReq := by simpa [serveTakes] using hs
      have := (owner_serve t).2 this
      rw [h] at this; simp at this
  · rcases hs : fetchTakes t with _ | _
    · rfl
    · have : t = proofFrame := by simpa [fetchTakes] using hs
      have := (owner_fetch t).2 this
      rw [h] at this; simp at this

/-! ## The values layer -/

theorem values_no_cross (t : Nat) : ¬ (serveTakes t = true ∧ fetchTakes t = true) := by
  simp only [serveTakes, fetchTakes, proofReq, proofFrame, beq_iff_eq]
  omega

theorem serve_registered (t : Nat) : serveTakes t = true ↔ owner t = some .serve := by
  simp [serveTakes, (owner_serve t)]

theorem fetch_registered (t : Nat) : fetchTakes t = true ↔ owner t = some .fetch := by
  simp [fetchTakes, (owner_fetch t)]

/-- A frame of the values layer reaches it through the application ring: with a body on an allowed session, and
dropped otherwise. -/
theorem values_ring (t len : Nat) (a : Bool) (h : owner t = some .serve ∨ owner t = some .fetch) :
    route t len a = .ring ↔ 0 < len ∧ a = true := by
  rw [route_ring_iff]
  constructor
  · intro h'; exact ⟨h'.2.2.1, h'.2.2.2⟩
  · intro h'
    refine ⟨fun e => ?_, fun e => ?_, h'.1, h'.2⟩
    · have : owner t = some .sub := (owner_sub t).2 e
      rcases h with h | h <;> rw [h] at this <;> simp at this
    · have : owner t = some .reach := (owner_reach t).2 e
      rcases h with h | h <;> rw [h] at this <;> simp at this

end Vinc.TransportExt

#audit_axioms Vinc.TransportExt.table_uniq
#audit_axioms Vinc.TransportExt.uniq_sound
#audit_axioms Vinc.TransportExt.owner_unique
#audit_axioms Vinc.TransportExt.registered_decodes
#audit_axioms Vinc.TransportExt.registered_sendable
#audit_axioms Vinc.TransportExt.unregistered_decodes
#audit_axioms Vinc.TransportExt.route_exclusive
#audit_axioms Vinc.TransportExt.ring_not_core
#audit_axioms Vinc.TransportExt.route_gate
#audit_axioms Vinc.TransportExt.route_table
#audit_axioms Vinc.TransportExt.route_owner
#audit_axioms Vinc.TransportExt.unregistered_ring
#audit_axioms Vinc.TransportExt.unregistered_untaken
#audit_axioms Vinc.TransportExt.values_no_cross
#audit_axioms Vinc.TransportExt.serve_registered
#audit_axioms Vinc.TransportExt.fetch_registered
#audit_axioms Vinc.TransportExt.values_ring
