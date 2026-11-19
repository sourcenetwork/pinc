import Pinc.DtnForwardThm

/-!
# Copies are conserved

The copies of a bundle at one node are `held` (the copies in its bundle slots) plus `handed` (the copies given to
peers in its transfers, acknowledged or not, never taken back). `total` is their sum. This file proves, for every
state and every capacity, how each operation changes `total` of each bundle:

* `advance_total`, `retr_total`, `step_other_total`: advancing the clock, the retransmission scan, a refused input,
  a link change, an acknowledgement do not change any total.
* `spray_total`: a handover moves `copies / 2` from held to handed (and a delivery moves none): the total of every
  bundle is unchanged, so binary spray neither creates nor loses a copy.
* `hold_total`: an accepted hold adds exactly the offered copies to that bundle's total; a repeated hold (`Duplicate`),
  a hold of a finished bundle (`Finished`), a hold that finds a table full and a hold of no copies change nothing: the offered copies are lost, never added (`hold_refused_total`).
* `drop_total`: dropping a bundle (forget, or the release of a delivered or expired one) changes no other bundle's
  total and leaves no handed copy of the dropped one.
* `spray_keeps_one`: a handover to anyone but the destination leaves the holder at least one copy, and hands at
  least one.

`DtnForwardInv.lean` turns these into the invariant of a whole run: copies held plus copies handed equal the copies
received, for every bundle, and a node never holds more than it received.
-/

namespace Pinc.DtnForward

/-- The weight of a bundle slot for bundle `x`: its copies. -/
def wB (x : Nat) (b : Bundle) : Nat := if b.id == x then b.copies else 0
/-- The weight of a transfer slot for bundle `x`: the copies it handed. -/
def wT (x : Nat) (t : Transfer) : Nat := if t.bundle == x then t.given else 0

/-- The copies held at this node. -/
def heldSum (f : F) (x : Nat) : Nat := wsum (wB x) f.bs
/-- The copies handed to peers by this node (`copies_handed`). -/
def handedSum (f : F) (x : Nat) : Nat := wsum (wT x) f.ts
/-- Held plus handed. -/
def total (f : F) (x : Nat) : Nat := heldSum f x + handedSum f x

theorem handed_eq (f : F) (x : Nat) : handed f x = handedSum f x := by
  unfold handed handedSum wsum wT
  congr 1
  apply List.map_congr_left
  intro o _
  cases o <;> rfl

theorem wsum_eq_of_slots {α : Type} (w : α → Nat) :
    ∀ (l l' : List (Option α)), l.length = l'.length →
      (∀ i, (slot l i).elim 0 w = (slot l' i).elim 0 w) → wsum w l = wsum w l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: r, b :: r', h, hs => by
    have h0 := hs 0
    simp only [slot_cons_zero] at h0
    have := wsum_eq_of_slots w r r' (by simpa using h) (fun i => by simpa [slot_cons_succ] using hs (i + 1))
    simp [wsum_cons, h0, this]

/-- Clearing an occupied slot removes its weight. -/
theorem wsum_upd_clear {α : Type} (w : α → Nat) (l : List (Option α)) (i : Nat) {x : α} (h : slot l i = some x) :
    wsum w (upd l i fun _ => none) + w x = wsum w l := by
  induction l generalizing i with
  | nil => simp at h
  | cons o r ih =>
    cases i with
    | zero => simp [slot_cons_zero] at h; subst h; simp [upd, wsum_cons]; omega
    | succ n =>
      have := ih n (by simpa [slot_cons_succ] using h)
      simp only [upd, wsum_cons]; omega

theorem advance_total (f : F) (n x : Nat) : total (advance f n) x = total f x := by
  unfold total heldSum handedSum
  congr 1
  apply wsum_eq_of_slots
  · simp [advance]
  · intro i
    simp only [advance]
    rw [slot_map _ _ rfl]
    cases h : slot f.ts i with
    | none => simp
    | some t =>
      cases hp : t.phase <;> simp [hp, wT] <;> split <;> simp [wT]

theorem retr_handed (f : F) (ts' : List (Option Transfer)) (a : Option Act)
    (h : retr (upLink f.ls) f.retry f.maxSends f.ts = (ts', a)) (x : Nat) :
    wsum (wT x) ts' = wsum (wT x) f.ts := by
  have hrel := (retr_rel (upLink f.ls) f.retry f.maxSends f.ts)
  rw [h] at hrel
  obtain ⟨hl, hs⟩ := hrel
  symm
  apply wsum_eq_of_slots _ _ _ (by simpa using hl.symm)
  intro i
  have := hs i
  cases ho : slot f.ts i with
  | none => rw [ho] at this; cases ho' : slot ts' i <;> simp_all [TRel]
  | some t =>
    rw [ho] at this
    cases ho' : slot ts' i with
    | none => simp_all [TRel]
    | some t' =>
      rw [ho'] at this
      simp only [TRel] at this
      simp [wT, this.1, this.2.2.1]

theorem wsum_zero_of_slots {α : Type} (w : α → Nat) :
    ∀ (l : List (Option α)), (∀ i, (slot l i).elim 0 w = 0) → wsum w l = 0
  | [], _ => rfl
  | a :: r, hs => by
    have h0 := hs 0
    simp only [slot_cons_zero] at h0
    have := wsum_zero_of_slots w r (fun i => by simpa [slot_cons_succ] using hs (i + 1))
    simp [wsum_cons, h0, this]

/-- A handover moves copies from held to handed and loses none: every total is unchanged. -/
theorem spray_total (f f' : F) (a : Act) (h : spray f = (f', a)) (x : Nat) : total f' x = total f x := by
  rcases spray_cases f with hs | ⟨f1, p, id, c, hs⟩
  · rw [hs] at h; cases h; rfl
  · rw [hs] at h
    obtain ⟨hf1, _⟩ := Prod.mk.inj h
    subst hf1
    obtain ⟨_, li, bi, s, l, b, _, _, hb, hfs, _, _, hcc, hf⟩ := spray_unfold hs
    obtain ⟨hsn, hsl⟩ := freeIdx_some hfs
    have e1 := wsum_upd_some (wB x) f.bs bi (fun b => { b with copies := b.copies - c }) hb
    have e2 := wsum_upd_fill (wT x) f.ts s ⟨b.id, l.peer, c, l.peer == b.dest, .sent f.retry 1⟩ hsn hsl
    have hc : c ≤ b.copies := by
      rw [hcc]; split <;> omega
    unfold total heldSum handedSum
    rw [hf]
    by_cases hx : (b.id == x) = true
    · simp only [wB, wT, hx, if_true] at e1 e2 ⊢
      omega
    · simp only [wB, wT, hx] at e1 e2 ⊢
      simp at e1 e2 ⊢
      omega

/-- A handover to a non-destination hands at least one copy and the holder keeps at least one. -/
theorem spray_keeps_one {f f' : F} {p id c : Nat} (h : spray f = (f', .send p id c false)) :
    ∃ bi b, slot f.bs bi = some b ∧ b.id = id ∧ slot f'.bs bi = some { b with copies := b.copies - c } ∧
      (p = b.dest → c = 0) ∧ (p ≠ b.dest → 1 ≤ c ∧ 1 ≤ b.copies - c ∧ c = b.copies / 2) := by
  obtain ⟨_, _, _, _, _, bi, b, hb, hid, hb', hcase⟩ := spray_send_spec h
  refine ⟨bi, b, hb, hid, hb', fun hp => ?_, fun hp => ?_⟩
  · rcases hcase with ⟨_, h0⟩ | ⟨hne, _⟩
    · exact h0
    · exact absurd hp hne
  · rcases hcase with ⟨hd, _⟩ | ⟨_, h1, h2, h3⟩
    · exact absurd hd hp
    · exact ⟨h2, h3, h1⟩

theorem retr_total (f : F) (ts' : List (Option Transfer)) (a : Option Act)
    (h : retr (upLink f.ls) f.retry f.maxSends f.ts = (ts', a)) (x : Nat) :
    total { f with ts := ts' } x = total f x := by
  unfold total heldSum handedSum
  simp only
  rw [retr_handed f ts' a h x]

/-- Dropping a bundle changes no other bundle's total and leaves nothing handed for it. -/
theorem drop_total (f : F) (id x : Nat) (hx : x ≠ id) : total (dropB f id) x = total f x := by
  unfold total heldSum handedSum dropB
  simp only
  have hts : wsum (wT x) (f.ts.map fun o => if o.any (·.bundle == id) then none else o) = wsum (wT x) f.ts := by
    apply wsum_eq_of_slots
    · simp
    · intro i
      rw [slot_map _ _ (by simp)]
      cases hs : slot f.ts i with
      | none => simp
      | some t =>
        by_cases hb : (t.bundle == id) = true
        · have : (t.bundle == x) = false := by
            simp at hb ⊢; omega
          simp [hb, wT, this]
        · simp [hb]
  rw [hts]
  cases hf : firstIdx (·.id == id) f.bs with
  | none => rfl
  | some i =>
    obtain ⟨b, hb, hp, _⟩ := firstIdx_some hf
    have := wsum_upd_clear (wB x) f.bs i hb
    have hz : wB x b = 0 := by
      simp at hp; simp [wB]; omega
    simp only
    omega

theorem drop_handed (f : F) (id : Nat) : handedSum (dropB f id) id = 0 := by
  unfold handedSum dropB
  simp only
  apply wsum_zero_of_slots
  intro i
  rw [slot_map _ _ (by simp)]
  cases hs : slot f.ts i with
  | none => simp
  | some t =>
    by_cases hb : (t.bundle == id) = true
    · simp [hb]
    · simp [hb, wT]

/-! ### One step -/

theorem hold_total (f0 : F) (n id d ex c : Nat) (f' : F) (e : Err) (h : step f0 n (.hold id d ex c) = (f', e))
    (x : Nat) :
    (e ≠ .ok ∧ f' = advance f0 n) ∨
    (e = .ok ∧ c ≠ 0 ∧ anyS (·.id == id) (advance f0 n).bs = false ∧
      total f' x = total f0 x + (if id = x then c else 0) ∧
      ∃ i, freeIdx (advance f0 n).bs = some i ∧ ∃ k, freeD (advance f0 n).now (advance f0 n).ds = some k ∧
        f' = { advance f0 n with bs := upd (advance f0 n).bs i fun _ => some ⟨id, d, ex, c, false⟩
                                 ds := upd (advance f0 n).ds k fun _ => some ⟨id, ex⟩ }) := by
  unfold step at h
  simp only at h
  by_cases hc : c = 0
  · subst hc; simp at h; left; exact ⟨by rw [← h.2]; simp, by rw [← h.1]⟩
  · by_cases ha : anyS (·.id == id) (advance f0 n).bs = true
    · simp [hc, ha] at h; left; exact ⟨by rw [← h.2]; simp, by rw [← h.1]⟩
    · have ha' : anyS (·.id == id) (advance f0 n).bs = false := by simpa using ha
      by_cases hs : anyS (fun d => d.id == id && decide ((advance f0 n).now < d.exp)) (advance f0 n).ds = true
      · simp [hc, ha', hs] at h; left; exact ⟨by rw [← h.2]; simp, by rw [← h.1]⟩
      · have hs' : anyS (fun d => d.id == id && decide ((advance f0 n).now < d.exp)) (advance f0 n).ds = false := by
          simpa using hs
        cases hk : freeD (advance f0 n).now (advance f0 n).ds with
        | none =>
          cases hf : freeIdx (advance f0 n).bs <;> simp [hc, ha', hs', hk, hf] at h <;>
            (left; exact ⟨by rw [← h.2]; simp, by rw [← h.1]⟩)
        | some k =>
          cases hf : freeIdx (advance f0 n).bs with
          | none => simp [hc, ha', hs', hk, hf] at h; left; exact ⟨by rw [← h.2]; simp, by rw [← h.1]⟩
          | some i =>
            simp [hc, ha', hs', hk, hf] at h
            obtain ⟨hf', he⟩ := h
            right
            refine ⟨he.symm, hc, ha', ?_, i, rfl, k, rfl, hf'.symm⟩
            obtain ⟨hsn, hsl⟩ := freeIdx_some hf
            have e2 := wsum_upd_fill (wB x) (advance f0 n).bs i ⟨id, d, ex, c, false⟩ hsn hsl
            have hadv := advance_total f0 n x
            have hb : (advance f0 n).bs = f0.bs := rfl
            unfold total heldSum handedSum at hadv ⊢
            rw [← hf']
            simp only
            rw [hb] at e2 hadv ⊢
            by_cases hx : id = x
            · simp [wB, hx] at e2 ⊢; omega
            · have : (id == x) = false := by simpa using hx
              simp [wB, this, hx] at e2 ⊢; omega

theorem wsum_upd_map {α : Type} (w : α → Nat) (g : α → α) (hg : ∀ a, w (g a) = w a) :
    ∀ (l : List (Option α)) (i : Nat), wsum w (upd l i (Option.map g)) = wsum w l
  | [], _ => rfl
  | o :: r, i => by
    cases i with
    | zero => cases o <;> simp [upd, wsum_cons, hg]
    | succ n => simp [upd, wsum_cons, wsum_upd_map w g hg r n]

theorem step_forget (f0 : F) (n id : Nat) (f' : F) (e : Err) (h : step f0 n (.forget id) = (f', e)) :
    (e = .unknown ∧ f' = advance f0 n ∧ anyS (·.id == id) (advance f0 n).bs = false) ∨
    (e = .ok ∧ f' = dropB (advance f0 n) id ∧ anyS (·.id == id) (advance f0 n).bs = true) := by
  unfold step at h
  simp only at h
  by_cases ha : anyS (·.id == id) (advance f0 n).bs = true
  · simp [ha] at h; right; exact ⟨h.2.symm, h.1.symm, ha⟩
  · have ha' : anyS (·.id == id) (advance f0 n).bs = false := by simpa using ha
    simp [ha'] at h; left; exact ⟨h.2.symm, h.1.symm, ha'⟩

/-- Every input but a hold or a forget leaves every total unchanged. -/
theorem step_other_total (f0 : F) (n : Nat) (inp : Input) (f' : F) (e : Err) (h : step f0 n inp = (f', e))
    (hn : ∀ id d ex c, inp ≠ .hold id d ex c) (hf : ∀ id, inp ≠ .forget id) (x : Nat) :
    total f' x = total f0 x := by
  have hadv := advance_total f0 n x
  cases inp with
  | tick => simp [step] at h; rw [← h.1]; exact hadv
  | hold id d ex c => exact absurd rfl (hn id d ex c)
  | forget id => exact absurd rfl (hf id)
  | linkUp peer | linkDown peer =>
    unfold step at h
    simp only at h
    split at h
    · rename_i i hi
      simp only [Prod.mk.injEq] at h
      rw [← h.1]; exact hadv
    · split at h
      · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact hadv
      · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact hadv
  | acked peer id =>
    unfold step at h
    simp only at h
    split at h
    · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact hadv
    · rename_i i hi
      have hts : wsum (wT x) (upd (advance f0 n).ts i (Option.map fun t => { t with phase := .acked })) =
          wsum (wT x) (advance f0 n).ts := wsum_upd_map (wT x) (fun t => { t with phase := .acked }) (fun _ => rfl) _ _
      split at h
      · split at h
        · simp only [Prod.mk.injEq] at h
          rw [← h.1]
          unfold total heldSum handedSum at hadv ⊢
          simp only
          rw [hts, wsum_upd_map (wB x) (fun b => { b with delivered := true }) (fun _ => rfl)]
          exact hadv
        · simp only [Prod.mk.injEq] at h
          rw [← h.1]
          unfold total heldSum handedSum at hadv ⊢
          simp only
          rw [hts]; exact hadv
      · simp only [Prod.mk.injEq] at h
        rw [← h.1]
        unfold total heldSum handedSum at hadv ⊢
        simp only
        rw [hts]; exact hadv

/-- Not a hold, a forget or a delivered or expired release: a poll leaves every total unchanged. -/
theorem poll_total (f f' : F) (a : Act) (h : poll f = (f', a)) (hr : ∀ id, a ≠ .release id) (x : Nat) :
    total f' x = total f x := by
  unfold poll at h
  cases hd : doneIdx f with
  | some i => simp only [hd, Prod.mk.injEq] at h; exact absurd h.2.symm (hr _)
  | none =>
    simp only [hd] at h
    cases hq : retr (upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a0 =>
      cases a0 with
      | some y => simp only [hq, Prod.mk.injEq] at h; rw [← h.1]; exact retr_total f ts' _ hq x
      | none =>
        simp only [hq] at h
        rw [spray_total _ f' a h x]
        exact retr_total f ts' _ hq x

/-- A release drops one bundle: no other total changes and nothing stays handed for it. -/
theorem poll_release_total (f f' : F) (id : Nat) (h : poll f = (f', .release id)) :
    (∀ x, x ≠ id → total f' x = total f x) ∧ handedSum f' id = 0 := by
  obtain ⟨i, b, hd, hb, hid, _⟩ := poll_release_only_done f f' id h
  obtain ⟨b', hb', _, hp⟩ := poll_release_done f i hd
  rw [hp] at h
  have hf : f' = dropB f b'.id := (Prod.mk.inj h).1.symm
  have : b'.id = id := by
    have := (Prod.mk.inj h).2; simpa using this
  subst hf
  exact ⟨fun x hx => drop_total f _ x (by rw [this]; exact hx), by rw [this] at *; exact drop_handed f id⟩

/-- A link change leaves bundles and transfers as the advance made them. -/
theorem step_link_shape (f0 : F) (n peer : Nat) (up : Bool) (f' : F) (e : Err)
    (h : step f0 n (if up then .linkUp peer else .linkDown peer) = (f', e)) :
    f'.bs = (advance f0 n).bs ∧ f'.ts = (advance f0 n).ts := by
  cases up <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h <;>
  · unfold step at h
    simp only at h
    split at h
    · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact ⟨rfl, rfl⟩
    · split at h <;> (simp only [Prod.mk.injEq] at h; rw [← h.1]; exact ⟨rfl, rfl⟩)

/-- An acknowledgement marks one transfer acked and perhaps the bundle delivered; nothing else changes. -/
theorem step_ack_shape (f0 : F) (n peer id : Nat) (f' : F) (e : Err) (h : step f0 n (.acked peer id) = (f', e)) :
    (f'.bs = (advance f0 n).bs ∧ f'.ts = (advance f0 n).ts) ∨
    (∃ i, f'.ts = upd (advance f0 n).ts i (Option.map fun t => { t with phase := .acked }) ∧
      (f'.bs = (advance f0 n).bs ∨
        ∃ j, f'.bs = upd (advance f0 n).bs j (Option.map fun b => { b with delivered := true }))) := by
  unfold step at h
  simp only at h
  split at h
  · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact Or.inl ⟨rfl, rfl⟩
  · rename_i i hi
    split at h
    · split at h
      · rename_i j hj
        simp only [Prod.mk.injEq] at h; rw [← h.1]; exact Or.inr ⟨i, rfl, Or.inr ⟨j, rfl⟩⟩
      · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact Or.inr ⟨i, rfl, Or.inl rfl⟩
    · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact Or.inr ⟨i, rfl, Or.inl rfl⟩

end Pinc.DtnForward
