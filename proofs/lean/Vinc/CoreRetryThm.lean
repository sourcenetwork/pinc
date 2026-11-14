import Vinc.Axioms
import Vinc.CoreRetry

/-!
# The retry ring and the retry token: the bound, the order, the age, and what the tag binds

What the model proves about `retry.rs`, for any ring size and any run of pushes and pops:

- the ring never grows past `cap` and its head stays below `cap` (`rpush_len`, `rpop_len`, `rpop_head`);
- with no key or with a full ring a push keeps nothing and changes nothing (`rpush_nokey`, `rpush_full`); otherwise
  the retry is appended and nothing else moves (`rpush_room`);
- retries leave oldest first: a pop gives the head of the order and keeps the rest in order (`rpop_cons`), so what is
  pushed into a ring with room leaves after everything that waited before it (`push_then_pop`);
- a token opens exactly from the second it was made to `life` seconds later, and not at a second before it (a clock
  that stepped back), while the second has not wrapped (`opens_iff`);
- the tag's message binds every field: two messages that are equal come from the same second, family, address, port
  and id (`msg_inj`), so a token made for one flight is a tag over another message than any other flight's.
-/

namespace Vinc.CoreRetry

theorem rpush_nokey {α : Type} (cap : Nat) (r : R α) (x : α) (h : r.keyed = false) : rpush cap r x = (false, r) := by
  simp [rpush, h]

theorem rpush_full {α : Type} (cap : Nat) (r : R α) (x : α) (h : cap ≤ r.q.length) : rpush cap r x = (false, r) := by
  simp [rpush, Nat.not_lt.2 h]

theorem rpush_room {α : Type} (cap : Nat) (r : R α) (x : α) (hk : r.keyed = true) (h : r.q.length < cap) :
    rpush cap r x = (true, { r with q := r.q ++ [x] }) := by
  simp [rpush, hk, h]

theorem rpush_len {α : Type} (cap : Nat) (r : R α) (x : α) (h : r.q.length ≤ cap) :
    (rpush cap r x).2.q.length ≤ cap := by
  unfold rpush
  by_cases hc : r.keyed = true ∧ r.q.length < cap
  · obtain ⟨hk, hl⟩ := hc
    simp [hk, hl]; omega
  · have : (r.keyed && decide (r.q.length < cap)) = false := by
      cases hk : r.keyed <;> simp_all
    simp [this]; exact h

theorem rpop_len {α : Type} (cap : Nat) (r : R α) (h : r.q.length ≤ cap) : (rpop cap r).2.q.length ≤ cap := by
  unfold rpop
  split
  · exact h
  · next x t hq => simp [hq] at h ⊢; omega

theorem rpop_head {α : Type} (cap : Nat) (r : R α) (hc : 0 < cap) (h : r.head < cap) : (rpop cap r).2.head < cap := by
  unfold rpop
  split
  · exact h
  · exact Nat.mod_lt _ hc

theorem rpop_cons {α : Type} (cap : Nat) (r : R α) (x : α) (t : List α) (h : r.q = x :: t) :
    rpop cap r = (some x, { r with head := (r.head + 1) % cap, q := t }) := by
  simp [rpop, h]

theorem rpop_nil {α : Type} (cap : Nat) (r : R α) (h : r.q = []) : rpop cap r = (none, r) := by
  simp [rpop, h]

/-- A retry pushed into a keyed ring with room waits behind everything already there: the first pop gives the oldest
retry that waited, and only an empty ring gives the new one at once. -/
theorem push_then_pop {α : Type} (cap : Nat) (r : R α) (x : α) (hk : r.keyed = true) (h : r.q.length < cap) :
    (rpop cap (rpush cap r x).2).1 = (r.q ++ [x]).head? := by
  rw [rpush_room cap r x hk h]
  cases hq : r.q with
  | nil => simp [rpop]
  | cons y t => simp [rpop]

theorem opens_iff (life now at_ : Nat) (hn : now < 4294967296) (ha : at_ < 4294967296)
    (hl : at_ + life < 4294967296) : opens life now at_ = true ↔ at_ ≤ now ∧ now ≤ at_ + life := by
  unfold opens
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    by_cases hle : at_ ≤ now
    · have : (now + 4294967296 - at_) % 4294967296 = now - at_ := by omega
      omega
    · have : (now + 4294967296 - at_) % 4294967296 = now + 4294967296 - at_ := by omega
      omega
  · intro ⟨h1, h2⟩
    have : (now + 4294967296 - at_) % 4294967296 = now - at_ := by omega
    omega

theorem msg_inj (a1 a2 ip1 ip2 p1 p2 id1 id2 : List Nat) (f1 f2 : Nat) (ha : a1.length = 4) (ha2 : a2.length = 4)
    (hi : ip1.length = 16) (hi2 : ip2.length = 16) (hp : p1.length = 2) (hp2 : p2.length = 2)
    (h : msg a1 f1 ip1 p1 id1 = msg a2 f2 ip2 p2 id2) :
    a1 = a2 ∧ f1 = f2 ∧ ip1 = ip2 ∧ p1 = p2 ∧ id1 = id2 := by
  unfold msg at h
  obtain ⟨e1, h⟩ := List.append_inj h (by omega)
  simp only [List.singleton_append, List.cons.injEq] at h
  obtain ⟨e2, h⟩ := h
  obtain ⟨e3, h⟩ := List.append_inj h (by omega)
  obtain ⟨e4, h⟩ := List.append_inj h (by omega)
  simp only [List.cons.injEq] at h
  exact ⟨e1, e2, e3, e4, h.2⟩

#audit_axioms Vinc.CoreRetry.rpush_nokey
#audit_axioms Vinc.CoreRetry.rpush_full
#audit_axioms Vinc.CoreRetry.rpush_room
#audit_axioms Vinc.CoreRetry.rpush_len
#audit_axioms Vinc.CoreRetry.rpop_len
#audit_axioms Vinc.CoreRetry.rpop_head
#audit_axioms Vinc.CoreRetry.rpop_cons
#audit_axioms Vinc.CoreRetry.rpop_nil
#audit_axioms Vinc.CoreRetry.push_then_pop
#audit_axioms Vinc.CoreRetry.opens_iff
#audit_axioms Vinc.CoreRetry.msg_inj

end Vinc.CoreRetry
