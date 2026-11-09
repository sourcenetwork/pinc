import Vinc.BroadcastNodeLemmas2

/-!
# Broadcast node: transitions of the offer chain

`TransSpec` relates two results of a chain of offers (a `Bind` of `Offer` or `OfferHeld` onto a result): the roles
and floors stay, the node invariant is kept, what is appended to the records is offer-shaped, the deliveries are a
sub-list of the offered ids, and the `held + delivered` count of an id grows by one only when the id passes from
not contained in the dedupe set to contained (the epoch bound). It is reflexive and transitive, holds for one
offer and therefore for `OfferAll`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Vinc.BroadcastNode

/-- A chain step from result `r` to `r'` that offers the ids `ms` at `now`. -/
structure TransSpec (p : Params) (now : Nat) (ms : List Nat) (r r' : Res) : Prop where
  core : Core r.n r'.n
  lg : r'.n.lg = r.n.lg
  req : r'.n.req = r.n.req
  inv : 0 < p.seenCap → NodeInv p r.n → NodeInv p r'.n
  outs : ∃ ex, r'.outs = r.outs ++ ex ∧ (∀ o ∈ ex, OfferRec o) ∧ CacheGood r.n.acp now ex ∧ FreshDel p r.n ex
  ack : r'.ack = r.ack
  dl : ∃ ex, r'.dl = r.dl ++ ex ∧ ex.Sublist ms
  acc : ∃ ex, r'.acc = r.acc ++ ex
  mono : ∀ x, SContains p r.n.seen x now = true → SContains p r'.n.seen x now = true
  delta : ∀ x, r'.dl.count x + hc r'.n x ≤ r.dl.count x + hc r.n x +
      (if x ∈ ms ∧ SContains p r.n.seen x now = false ∧ SContains p r'.n.seen x now = true then 1 else 0)
  accN : p.heldFullKeepsUnseen = true → ∀ x, r'.n.seen.map x ≠ none → r.n.seen.map x ≠ none ∨ x ∈ r'.acc

theorem TransSpec.refl (p : Params) (now : Nat) (ms : List Nat) (r : Res) : TransSpec p now ms r r :=
  ⟨Core.refl _, rfl, rfl, fun _ h => h, ⟨[], by simp, by simp, by simp [CacheGood], by simp [FreshDel]⟩, rfl,
   ⟨[], by simp, List.nil_sublist _⟩, ⟨[], by simp⟩, fun x h => h,
   fun x => by split <;> omega, fun _ x hx => Or.inl hx⟩

theorem CacheGood_append {acp : List (Nat × AcpE)} {now : Nat} {a b : List TraceRec}
    (ha : CacheGood acp now a) (hb : CacheGood acp now b) : CacheGood acp now (a ++ b) := by
  intro mid org ts h
  rcases List.mem_append.1 h with h | h
  · exact ha mid org ts h
  · exact hb mid org ts h

theorem TransSpec.trans {p : Params} {now : Nat} {ms1 ms2 : List Nat} {r r1 r2 : Res}
    (T1 : TransSpec p now ms1 r r1) (T2 : TransSpec p now ms2 r1 r2) : TransSpec p now (ms1 ++ ms2) r r2 := by
  refine ⟨T1.core.trans T2.core, T2.lg.trans T1.lg, T2.req.trans T1.req,
    fun hc h => T2.inv hc (T1.inv hc h), ?_, T2.ack.trans T1.ack, ?_, ?_, fun x h => T2.mono x (T1.mono x h), ?_, ?_⟩
  · obtain ⟨e1, h1, o1, c1, f1⟩ := T1.outs
    obtain ⟨e2, h2, o2, c2, f2⟩ := T2.outs
    refine ⟨e1 ++ e2, by rw [h2, h1, List.append_assoc], ?_, ?_, ?_⟩
    · intro o ho; rcases List.mem_append.1 ho with h | h; exact o1 o h; exact o2 o h
    · exact CacheGood_append c1 (by rw [← T1.core.acp]; exact c2)
    · intro mid org ts via h
      rcases List.mem_append.1 h with h | h
      · exact f1 mid org ts via h
      · rw [← T1.core.isOld]; exact f2 mid org ts via h
  · obtain ⟨e1, h1, s1⟩ := T1.dl
    obtain ⟨e2, h2, s2⟩ := T2.dl
    exact ⟨e1 ++ e2, by rw [h2, h1, List.append_assoc], s1.append s2⟩
  · obtain ⟨e1, h1⟩ := T1.acc
    obtain ⟨e2, h2⟩ := T2.acc
    exact ⟨e1 ++ e2, by rw [h2, h1, List.append_assoc]⟩
  · intro x
    have d1 := T1.delta x
    have d2 := T2.delta x
    have m1 := T1.mono x
    have m2 := T2.mono x
    simp only [List.mem_append] at *
    generalize SContains p r.n.seen x now = a at *
    generalize SContains p r1.n.seen x now = b at *
    generalize SContains p r2.n.seen x now = c at *
    by_cases h1 : x ∈ ms1 <;> by_cases h2 : x ∈ ms2 <;> cases a <;> cases b <;> cases c <;> simp_all <;> omega
  · intro hk x hx
    rcases T2.accN hk x hx with h | h
    · rcases T1.accN hk x h with h' | h'
      · exact Or.inl h'
      · obtain ⟨e2, h2⟩ := T2.acc; exact Or.inr (by rw [h2]; exact List.mem_append_left _ h')
    · exact Or.inr h


theorem hc_eq {N N' : Node} (h : N'.held = N.held) (x : Nat) : hc N' x = hc N x := by unfold hc; rw [h]

theorem count_single (x a : Nat) : [a].count x = if x = a then 1 else 0 := by
  by_cases h : x = a
  · subst h; simp
  · have h' : ¬ a = x := fun e => h e.symm
    simp [List.count_cons, h, h']

theorem hc_snoc {N N' : Node} (m : Ent) (h : N'.held = N.held ++ [m]) (x : Nat) :
    hc N' x = hc N x + (if x = m.mid then 1 else 0) := by
  unfold hc; rw [h]; simp [List.count_append, count_single]

theorem bind_eq (r : Res) (F : Node → Res) :
    Bind r F = ⟨(F r.n).n, r.outs ++ (F r.n).outs, r.dl ++ (F r.n).dl, r.ack + (F r.n).ack, r.acc ++ (F r.n).acc⟩ := rfl

/-- One offer onto a result: the id must not be contained when it is offered. -/
theorem offerTrans (p : Params) (now : Nat) (r : Res) (m : Ent) (hf : SContains p r.n.seen m.mid now = false) :
    TransSpec p now [m.mid] r (Bind r (fun x => Offer p x now m)) := by
  have S := Offer_spec p r.n now m
  rw [bind_eq]
  generalize Offer p r.n now m = r2 at S ⊢
  have hdl : r2.dl = [] ∨ r2.dl = [m.mid] := by
    rcases S.held with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨S.core, S.lg, S.req, S.inv, ⟨r2.outs, rfl, S.outs, S.cache, S.fresh⟩, by simp [S.ack], ⟨r2.dl, rfl, ?_⟩,
    ⟨r2.acc, rfl⟩, S.mono, ?_, ?_⟩
  · rcases hdl with h | h <;> rw [h]
    · exact List.nil_sublist _
    · exact List.Sublist.refl _
  · intro x
    simp only [List.count_append]
    rcases S.held with ⟨hd, hh | hh⟩ | ⟨hd, hh⟩
    · rw [hd, hc_eq hh x]; simp
    · have hs := hc_snoc m hh x
      by_cases hx : x = m.mid
      · subst hx
        have := S.hit (Or.inl (by rw [hh]; simp))
        simp [hd, hs, hf, this] <;> omega
      · simp [hd, hs, hx]
    · rw [hc_eq hh x, hd]
      by_cases hx : x = m.mid
      · subst hx
        have := S.hit (Or.inr (by rw [hd]; simp))
        simp [hf, this, count_single] <;> omega
      · simp [hx, count_single]
  · intro hk x hx
    rcases (S.acc hk).1 x hx with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_append_right _ h)

theorem offerHeldTrans (p : Params) (now : Nat) (r : Res) (e : Ent) :
    TransSpec p now [e.mid] r (Bind r (fun x => OfferHeld p x now e)) := by
  by_cases hd : IsDup p r.n e.mid now = true
  · have : Bind r (fun x => OfferHeld p x now e) = r := by
      simp [bind_eq, OfferHeld, hd, Plain]
    rw [this]; exact TransSpec.refl _ _ _ _
  · have hd' : IsDup p r.n e.mid now = false := by simpa using hd
    have hf : SContains p r.n.seen e.mid now = false := by
      simp [IsDup] at hd'; simpa using hd'.1
    have : Bind r (fun x => OfferHeld p x now e) = Bind r (fun x => Offer p x now e) := by
      simp [bind_eq, OfferHeld, hd']
    rw [this]; exact offerTrans p now r e hf

theorem offerAllTrans (p : Params) (now : Nat) (es : List Ent) :
    ∀ r : Res, TransSpec p now (es.map (·.mid)) r (OfferAll p now r es) := by
  induction es with
  | nil => intro r; exact TransSpec.refl _ _ _ _
  | cons e es ih =>
    intro r
    exact (offerHeldTrans p now r e).trans (ih _)

end Vinc.BroadcastNode
