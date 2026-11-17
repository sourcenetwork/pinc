import Vinc.BroadcastNodeThm

/-!
# Broadcast node: what an operator does to the records of the dedupe set

`MapStep now S S'`: every record of `S'` is the one `S` had, a record made at `now`, or none. It holds for every
operator of the receive path and the timer (`OnMsg_mapStep`, `OnTimer_mapStep`, `AcpAnswer_mapStep`,
`FloorsSettled_mapStep`), so the epoch spacing of `BroadcastNodeSpacing` can follow the records of an id through a
run.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Vinc.BroadcastNode

/-- Every record of `S'` is one of `S`, one made at `now`, or none. -/
def MapStep (now : Nat) (S S' : Seen) : Prop := ∀ x, S'.map x = S.map x ∨ S'.map x = some now ∨ S'.map x = none

theorem MapStep.refl (now : Nat) (S : Seen) : MapStep now S S := fun _ => Or.inl rfl

theorem MapStep.trans {now : Nat} {A B C : Seen} (h1 : MapStep now A B) (h2 : MapStep now B C) : MapStep now A C := by
  intro x
  rcases h2 x with h | h | h
  · rcases h1 x with h' | h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (Or.inl (h.trans h'))
    · exact Or.inr (Or.inr (h.trans h'))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem SPush_mapStep (S : Seen) (mid now : Nat) : MapStep now S (SPush S mid now) := by
  intro x; rw [SPush_map]; by_cases h : x = mid <;> simp [h]

theorem SPopFront_mapStep (S : Seen) (now : Nat) : MapStep now S (SPopFront S) := by
  intro x
  rcases SPopFront_map2 S x with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem SInsert_mapStep (p : Params) (S : Seen) (mid now : Nat) (f : Bool) : MapStep now S (SInsert p S mid now f) := by
  unfold SInsert
  split
  · split
    · exact (SPopFront_mapStep S now).trans (SPush_mapStep _ mid now)
    · exact MapStep.refl now S
  · exact SPush_mapStep S mid now

theorem SInsertAll_mapStep (p : Params) (now : Nat) (ids : List Nat) : ∀ S : Seen, MapStep now S (SInsertAll p S now ids) := by
  induction ids with
  | nil => intro S; exact MapStep.refl now S
  | cons i ids ih =>
    intro S
    unfold SInsertAll
    refine MapStep.trans ?_ (ih _)
    split
    · exact MapStep.refl now S
    · exact SInsert_mapStep p S i now true

theorem SweepIds_mapStep (p : Params) (now : Nat) (ids : List Nat) : ∀ S : Seen, MapStep now S (SweepIds p S now ids) := by
  induction ids with
  | nil => intro S; exact MapStep.refl now S
  | cons i ids ih =>
    intro S
    unfold SweepIds
    refine MapStep.trans ?_ (ih _)
    split
    · exact MapStep.refl now S
    · exact SInsert_mapStep p S i now true

theorem SExpire_mapStep (p : Params) (S : Seen) (now : Nat) : MapStep now S (SExpire p S now) := by
  intro x
  rcases SExpireAux_map p now x S.order.length S with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem Sweep_mapStep (p : Params) (N : Node) (now : Nat) : MapStep now N.seen (Sweep p N now).seen := by
  unfold Sweep
  exact (SExpire_mapStep p N.seen now).trans (SweepIds_mapStep p now _ _)

theorem Offer_mapStep (p : Params) (N : Node) (now : Nat) (m : Ent) : MapStep now N.seen (Offer p N now m).n.seen := by
  have F := Offer_form p N now m
  generalize Offer p N now m = r at F
  cases F with
  | topic _ => exact MapStep.refl now _
  | seenFull _ _ => exact MapStep.refl now _
  | floor _ _ _ _ => exact (HoldFloor_frame p N m).2.1 ▸ MapStep.refl now _
  | full _ _ _ _ _ => exact (HoldAndAsk_frame p N m).2.1 ▸ MapStep.refl now _
  | skip _ _ _ => exact SInsert_mapStep p N.seen m.mid now false
  | deliver _ _ _ _ _ _ _ _ _ => exact SInsert_mapStep p N.seen m.mid now false
  | deny _ _ _ => exact SInsert_mapStep p N.seen m.mid now false
  | ask _ _ _ _ =>
    have := (HoldAndAsk_frame p (N1of p N now m) m).2.1
    show MapStep now N.seen (HoldAndAsk p (N1of p N now m) m).n.seen
    rw [this]
    exact SInsert_mapStep p N.seen m.mid now false

theorem Bind_mapStep {now : Nat} {p : Params} (r : Res) (F : Node → Res) (A : Seen)
    (h0 : MapStep now A r.n.seen) (h : MapStep now r.n.seen (F r.n).n.seen) : MapStep now A (Bind r F).n.seen :=
  h0.trans h

theorem OfferHeld_mapStep (p : Params) (N : Node) (now : Nat) (e : Ent) : MapStep now N.seen (OfferHeld p N now e).n.seen := by
  unfold OfferHeld
  split
  · exact MapStep.refl now _
  · exact Offer_mapStep p N now e

theorem OfferAll_mapStep (p : Params) (now : Nat) (es : List Ent) :
    ∀ (r : Res) (A : Seen), MapStep now A r.n.seen → MapStep now A (OfferAll p now r es).n.seen := by
  induction es with
  | nil => intro r A h; exact h
  | cons e es ih =>
    intro r A h
    exact ih _ A (h.trans (OfferHeld_mapStep p r.n now e))

theorem FloorsSettled_mapStep (p : Params) (N : Node) (now : Nat) (used : Bool) (rf : Option Nat)
    (of_ : Option (Nat → Option Nat)) (nh : Bool) :
    MapStep now N.seen (FloorsSettled p N now used rf of_ nh).n.seen := by
  unfold FloorsSettled
  exact OfferAll_mapStep p now _ _ N.seen (MapStep.refl now _)

theorem OnTimer_mapStep (p : Params) (N : Node) (now : Nat) : MapStep now N.seen (OnTimer p N now).n.seen := by
  unfold OnTimer
  dsimp only
  split
  · exact (Sweep_mapStep p N now).trans (FloorsSettled_mapStep p _ now _ _ _ _)
  · exact Sweep_mapStep p N now

theorem AcpAnswer_mapStep (p : Params) (N : Node) (now id : Nat) (allow : Bool) :
    MapStep now N.seen (AcpAnswer p N now id allow).n.seen := by
  unfold AcpAnswer
  rcases hf : N.checks.find? (fun c => c.id == id) with _ | c
  · simp only [hf]; exact MapStep.refl now _
  · simp only [hf]; exact MapStep.refl now _

theorem HubStore_mapStep (p : Params) (N : Node) (now wall : Nat) (fanned : Bool) (m : Msg) :
    MapStep now N.seen (HubStore p N now wall fanned m).n.seen := by
  unfold HubStore
  by_cases htf : p.topicFull = true
  · rw [if_pos htf]; exact MapStep.refl now _
  · rw [if_neg htf]
    dsimp only
    generalize LPush p N.lg m.mid now wall m.n = rr
    have h1 := SInsertAll_mapStep p now rr.ev N.seen
    by_cases hok : rr.ok = true
    · rw [if_neg (by simp [hok])]
      by_cases hsub : (N.sub && m.origin != p.me) = true
      · rw [if_pos hsub]
        exact h1.trans (Offer_mapStep p {N with seen := SInsertAll p N.seen now rr.ev, lg := rr.log} now m.ent)
      · rw [if_neg hsub]
        exact h1.trans (SInsert_mapStep p _ m.mid now true)
    · rw [if_pos (by simpa using hok)]
      exact h1

theorem OnMsg_mapStep (p : Params) (N : Node) (now wall : Nat) (t : Frame) (b : Bool) (m : Msg) :
    MapStep now N.seen (OnMsg p N now wall t b m).n.seen := by
  unfold OnMsg
  by_cases h1 : (!Allowed p t b) = true
  · rw [if_pos h1]; exact MapStep.refl now _
  rw [if_neg h1]
  by_cases h2 : m.kind = .badhead
  · rw [if_pos h2]; exact MapStep.refl now _
  rw [if_neg h2]
  by_cases h3 : m.kind = .big
  · rw [if_pos h3]; exact MapStep.refl now _
  rw [if_neg h3]
  dsimp only
  by_cases h4 : IsDup p N m.mid now = true
  · rw [if_pos h4]; exact MapStep.refl now _
  rw [if_neg h4]
  by_cases h5 : p.revoked.contains m.origin = true
  · rw [if_pos h5]; exact MapStep.refl now _
  rw [if_neg h5]
  by_cases h6 : m.kind = .badsig
  · rw [if_pos h6]; exact MapStep.refl now _
  rw [if_neg h6]
  by_cases hhub : p.isHub = true
  · rw [if_pos hhub, NoteStored_seen]
    exact HubStore_mapStep p {N with req := N.req.filter (fun x => x != m.mid)} now wall _ m
  · rw [if_neg hhub]
    exact Offer_mapStep p {N with req := N.req.filter (fun x => x != m.mid)} now m.ent

end Vinc.BroadcastNode
