import Vinc.DtnForwardCons

/-!
# Invariants of a run, and the balance of copies

Two structural invariants hold in every state reachable from `F.new` by `step` and `poll`:

* `Uniq`: no two bundle slots hold the same bundle id (`Hold` of a held id is refused as `Duplicate`);
* `Live`: every transfer belongs to a bundle that is held (transfers are created by the handover of a held
  bundle and removed with it).

`Reach f g` is the set of states reachable from a new forwarder, with the ghost `g x`: the copies of bundle `x`
received by the accepted `Hold` that is still in force (0 once the bundle was forgotten or released). The headline
`balance` says that in every reachable state, for every bundle, copies held plus copies handed equal `g x`; so a
node never holds more than it received, handed copies are never taken back, and a repeated hold (refused as
`Duplicate`, `hold_refused_total`) adds nothing.
-/

namespace Vinc.DtnForward

/-- No two slots hold the same bundle id. -/
def Uniq : List (Option Bundle) → Prop
  | [] => True
  | o :: r => (∀ b, o = some b → anyS (·.id == b.id) r = false) ∧ Uniq r

/-- Every transfer belongs to a held bundle. -/
def Live (f : F) : Prop := ∀ i t, slot f.ts i = some t → anyS (·.id == t.bundle) f.bs = true

theorem anyS_cons {α : Type} (p : α → Bool) (o : Option α) (r : List (Option α)) :
    anyS p (o :: r) = (o.any p || anyS p r) := by simp [anyS]

theorem anyS_upd_map {α : Type} (p : α → Bool) (g : α → α) (hg : ∀ a, p (g a) = p a) :
    ∀ (l : List (Option α)) (i : Nat), anyS p (upd l i (Option.map g)) = anyS p l
  | [], _ => rfl
  | o :: r, i => by
    cases i with
    | zero => cases o <;> simp [upd, anyS_cons, hg]
    | succ n => simp [upd, anyS_cons, anyS_upd_map p g hg r n]

theorem anyS_upd_clear {α : Type} (p : α → Bool) :
    ∀ (l : List (Option α)) (i : Nat), anyS p (upd l i fun _ => none) = true → anyS p l = true
  | [], _, h => by simpa [upd] using h
  | o :: r, i, h => by
    cases i with
    | zero => simp [upd, anyS_cons] at h; simp [anyS_cons, h]
    | succ n =>
      simp only [upd, anyS_cons, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (anyS_upd_clear p r n h)

theorem anyS_upd_fill {α : Type} (p : α → Bool) (y : α) :
    ∀ (l : List (Option α)) (i : Nat), anyS p (upd l i fun _ => some y) = true → anyS p l = true ∨ p y = true
  | [], _, h => by simp [upd, anyS] at h
  | o :: r, i, h => by
    cases i with
    | zero =>
      simp only [upd, anyS_cons, Bool.or_eq_true] at h
      rcases h with h | h
      · right; simpa using h
      · left; simp [anyS_cons, h]
    | succ n =>
      simp only [upd, anyS_cons, Bool.or_eq_true] at h
      rcases h with h | h
      · left; simp [anyS_cons, h]
      · rcases anyS_upd_fill p y r n h with h2 | h2
        · left; simp [anyS_cons, h2]
        · right; exact h2

/-- Filling a free slot keeps every id that was held. -/
theorem anyS_upd_fill_mono {α : Type} (p : α → Bool) (y : α) :
    ∀ (l : List (Option α)) (i : Nat), slot l i = none → anyS p l = true →
      anyS p (upd l i fun _ => some y) = true
  | [], _, _, h => by simp [anyS] at h
  | o :: r, i, hs, h => by
    cases i with
    | zero =>
      simp [slot_cons_zero] at hs; subst hs
      simp only [upd, anyS_cons, Option.any_none, Bool.false_or] at h ⊢
      simp [h]
    | succ n =>
      simp only [upd, anyS_cons, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (anyS_upd_fill_mono p y r n (by simpa [slot_cons_succ] using hs) h)

theorem uniq_new (n : Nat) : Uniq (List.replicate n (none : Option Bundle)) := by
  induction n with
  | zero => trivial
  | succ n ih => simp [List.replicate_succ, Uniq, ih]

theorem uniq_map (g : Bundle → Bundle) (hg : ∀ b, (g b).id = b.id) :
    ∀ (l : List (Option Bundle)) (i : Nat), Uniq l → Uniq (upd l i (Option.map g))
  | [], _, _ => trivial
  | o :: r, i, ⟨h1, h2⟩ => by
    cases i with
    | zero =>
      refine ⟨fun b hb => ?_, h2⟩
      cases o with
      | none => simp [upd] at hb
      | some b0 => simp [upd] at hb; subst hb; simpa [hg] using h1 b0 rfl
    | succ n =>
      refine ⟨fun b hb => ?_, uniq_map g hg r n h2⟩
      rw [anyS_upd_map _ g (fun a => by simp [hg])]
      exact h1 b hb

theorem uniq_clear : ∀ (l : List (Option Bundle)) (i : Nat), Uniq l → Uniq (upd l i fun _ => none)
  | [], _, _ => trivial
  | o :: r, i, ⟨h1, h2⟩ => by
    cases i with
    | zero => exact ⟨fun b hb => by simp [upd] at hb, h2⟩
    | succ n =>
      refine ⟨fun b hb => ?_, uniq_clear r n h2⟩
      have := h1 b hb
      cases h : anyS (·.id == b.id) (upd r n fun _ => none) with
      | false => rfl
      | true => rw [anyS_upd_clear _ r n h] at this; simp at this

theorem uniq_fill (y : Bundle) : ∀ (l : List (Option Bundle)) (i : Nat), Uniq l → slot l i = none →
    anyS (·.id == y.id) l = false → Uniq (upd l i fun _ => some y)
  | [], _, _, _, _ => trivial
  | o :: r, i, ⟨h1, h2⟩, hs, hy => by
    cases i with
    | zero =>
      simp [slot_cons_zero] at hs; subst hs
      simp only [anyS_cons, Option.any_none, Bool.false_or] at hy
      refine ⟨fun b hb => ?_, h2⟩
      simp [upd] at hb; subst hb; exact hy
    | succ n =>
      simp only [anyS_cons, Bool.or_eq_false_iff] at hy
      refine ⟨fun b hb => ?_, uniq_fill y r n h2 (by simpa [slot_cons_succ] using hs) hy.2⟩
      cases h : anyS (·.id == b.id) (upd r n fun _ => some y) with
      | false => rfl
      | true =>
        rcases anyS_upd_fill _ y r n h with h3 | h3
        · have := h1 b hb; rw [h3] at this; simp at this
        · subst hb
          have := hy.1
          simp at h3 this
          simp [h3] at this

theorem live_advance {f : F} (hL : Live f) (n : Nat) : Live (advance f n) := by
  intro i t ht
  have hb : (advance f n).bs = f.bs := rfl
  rw [hb]
  simp only [advance] at ht
  rw [slot_map _ _ rfl] at ht
  cases hs : slot f.ts i with
  | none => simp [hs] at ht
  | some t0 =>
    rw [hs] at ht
    have := hL i t0 hs
    cases hp : t0.phase <;> simp only [hp, Option.map_some] at ht
    · split at ht <;> (cases ht; exact this)
    · cases ht; exact this
    · cases ht; exact this

theorem live_dropB {f : F} (hL : Live f) (id : Nat) : Live (dropB f id) := by
  intro i t ht
  simp only [dropB] at ht ⊢
  rw [slot_map _ _ (by simp)] at ht
  cases hs : slot f.ts i with
  | none => simp [hs] at ht
  | some t0 =>
    rw [hs] at ht
    by_cases hb : (t0.bundle == id) = true
    · simp [hb] at ht
    · simp only [Option.any_some, hb, ite_false, Bool.false_eq_true] at ht
      cases ht
      have := hL i _ hs
      cases hf : firstIdx (·.id == id) f.bs with
      | none => simpa [hf] using this
      | some i0 =>
        obtain ⟨b0, hb0, hp, _⟩ := firstIdx_some hf
        obtain ⟨j, b, hj, hbp⟩ := (anyS_iff _ _).mp this
        have hne : j ≠ i0 := by
          intro e; subst e
          rw [hb0] at hj; cases hj
          simp at hp hbp hb; omega
        simp only [hf]
        rw [anyS_iff]
        exact ⟨j, b, by rw [slot_upd_ne _ _ _ _ hne]; exact hj, hbp⟩

theorem uniq_dropB {f : F} (hU : Uniq f.bs) (id : Nat) : Uniq (dropB f id).bs := by
  simp only [dropB]
  cases firstIdx (·.id == id) f.bs with
  | none => exact hU
  | some i => exact uniq_clear _ _ hU

theorem wsum_absent (id : Nat) : ∀ (l : List (Option Bundle)), anyS (·.id == id) l = false → wsum (wB id) l = 0
  | [], _ => rfl
  | o :: r, h => by
    simp only [anyS_cons, Bool.or_eq_false_iff] at h
    have := wsum_absent id r h.2
    cases o with
    | none => simp [wsum_cons, this]
    | some b => simp [wsum_cons, this, wB] at h ⊢; simp [h.1]

/-- The held sum of an id is the copies of the only slot that holds it. -/
theorem uniq_wsum : ∀ (l : List (Option Bundle)) (i : Nat) (b : Bundle), Uniq l → slot l i = some b →
    wsum (wB b.id) l = b.copies
  | [], _, _, _, h => by simp at h
  | o :: r, i, b, ⟨h1, h2⟩, hs => by
    cases i with
    | zero =>
      simp only [slot_cons_zero] at hs; subst hs
      have := wsum_absent _ r (h1 b rfl)
      simp [wsum_cons, this, wB]
    | succ n =>
      have ih := uniq_wsum r n b h2 (by simpa [slot_cons_succ] using hs)
      cases o with
      | none => simp [wsum_cons, ih]
      | some b0 =>
        have hne : (b0.id == b.id) = false := by
          cases hh : (b0.id == b.id) with
          | false => rfl
          | true =>
            have h3 := h1 b0 rfl
            have : anyS (·.id == b0.id) r = true := (anyS_iff _ _).mpr ⟨n, b, by simpa [slot_cons_succ] using hs, by simp at hh ⊢; omega⟩
            rw [h3] at this; simp at this
        simp [wsum_cons, ih, wB, hne]

theorem inv_spray {g : F} (hU : Uniq g.bs) (hL : Live g) : Uniq (spray g).1.bs ∧ Live (spray g).1 := by
  rcases spray_cases g with hs | ⟨f1, p, id, c, hs⟩
  · rw [hs]; exact ⟨hU, hL⟩
  · obtain ⟨_, li, bi, s, l, b, _, _, hb, hfs, _, _, _, hf⟩ := spray_unfold hs
    obtain ⟨hsn, hsl⟩ := freeIdx_some hfs
    rw [hs]
    show Uniq f1.bs ∧ Live f1
    rw [hf]
    have hany : ∀ y, anyS (·.id == y) (upd g.bs bi (Option.map fun b => { b with copies := b.copies - c })) =
        anyS (·.id == y) g.bs := fun y => anyS_upd_map (fun x : Bundle => x.id == y) (fun b : Bundle => { b with copies := b.copies - c }) (fun _ => rfl) _ _
    refine ⟨uniq_map (fun b : Bundle => { b with copies := b.copies - c }) (fun _ => rfl) _ _ hU, fun j t ht => ?_⟩
    simp only at ht ⊢
    rw [hany]
    by_cases hj : j = s
    · subst hj
      rw [slot_upd_same _ _ _ hsl] at ht
      cases ht
      exact (anyS_iff _ _).mpr ⟨bi, b, hb, by simp⟩
    · rw [slot_upd_ne _ _ _ _ hj] at ht
      exact hL j t ht

theorem inv_poll {f f' : F} {a : Act} (h : poll f = (f', a)) (hU : Uniq f.bs) (hL : Live f) :
    Uniq f'.bs ∧ Live f' := by
  unfold poll at h
  cases hd : doneIdx f with
  | some i =>
    simp only [hd, Prod.mk.injEq] at h
    rw [← h.1]; exact ⟨uniq_dropB hU _, live_dropB hL _⟩
  | none =>
    simp only [hd] at h
    cases hq : retr (upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a0 =>
      have hrel := (retr_rel (upLink f.ls) f.retry f.maxSends f.ts).2
      simp only [hq] at hrel
      have hL' : Live { f with ts := ts' } := by
        intro i t ht
        have := hrel i
        simp only at ht
        cases ho : slot f.ts i with
        | none => rw [ho] at this; cases hs : slot ts' i <;> simp_all [TRel]
        | some t0 =>
          rw [ho, ht] at this
          simp only [TRel] at this
          rw [this.1]; exact hL i t0 ho
      cases a0 with
      | some y => simp only [hq, Prod.mk.injEq] at h; rw [← h.1]; exact ⟨hU, hL'⟩
      | none =>
        simp only [hq] at h
        rw [← show (spray { f with ts := ts' }).1 = f' from congrArg Prod.fst h]
        exact inv_spray hU hL'

/-- The step keeps both invariants. -/
theorem inv_step {f0 f' : F} {n : Nat} {inp : Input} {e : Err} (h : step f0 n inp = (f', e)) (hU : Uniq f0.bs)
    (hL : Live f0) : Uniq f'.bs ∧ Live f' := by
  have hLa := live_advance hL n
  have hUa : Uniq (advance f0 n).bs := hU
  cases inp with
  | tick => simp [step] at h; rw [← h.1]; exact ⟨hUa, hLa⟩
  | hold id d ex c =>
    rcases hold_total f0 n id d ex c f' e h 0 with ⟨_, hf⟩ | ⟨_, hc, ha, _, i, hfi, k, _, hf⟩
    · rw [hf]; exact ⟨hUa, hLa⟩
    · obtain ⟨hsn, _⟩ := freeIdx_some hfi
      rw [hf]
      refine ⟨uniq_fill _ _ _ hUa hsn ha, fun j t ht => ?_⟩
      exact anyS_upd_fill_mono _ _ _ _ hsn (hLa j t ht)
  | forget id =>
    rcases step_forget f0 n id f' e h with ⟨_, hf, _⟩ | ⟨_, hf, _⟩
    · rw [hf]; exact ⟨hUa, hLa⟩
    · rw [hf]; exact ⟨uniq_dropB hUa _, live_dropB hLa _⟩
  | linkUp peer =>
    obtain ⟨hb, ht⟩ := step_link_shape f0 n peer true f' e (by simpa using h)
    refine ⟨by rw [hb]; exact hUa, fun j t hj => ?_⟩
    rw [hb]; rw [ht] at hj; exact hLa j t hj
  | linkDown peer =>
    obtain ⟨hb, ht⟩ := step_link_shape f0 n peer false f' e (by simpa using h)
    refine ⟨by rw [hb]; exact hUa, fun j t hj => ?_⟩
    rw [hb]; rw [ht] at hj; exact hLa j t hj
  | acked peer id =>
    have hlive : ∀ ts' bs', (bs' = (advance f0 n).bs ∨ ∃ jj, bs' = upd (advance f0 n).bs jj (Option.map fun b => { b with delivered := true })) →
        (ts' = (advance f0 n).ts ∨ ∃ ii, ts' = upd (advance f0 n).ts ii (Option.map fun t => { t with phase := .acked })) →
        Uniq bs' ∧ ∀ j t, slot ts' j = some t → anyS (·.id == t.bundle) bs' = true := by
      intro ts' bs' hb ht
      have hany : ∀ y, anyS (·.id == y) bs' = anyS (·.id == y) (advance f0 n).bs := by
        intro y
        rcases hb with hb | ⟨jj, hb⟩
        · rw [hb]
        · rw [hb]; exact anyS_upd_map (fun x : Bundle => x.id == y) (fun b : Bundle => { b with delivered := true }) (fun _ => rfl) _ _
      refine ⟨?_, fun j t hj => ?_⟩
      · rcases hb with hb | ⟨jj, hb⟩
        · rw [hb]; exact hUa
        · rw [hb]; exact uniq_map (fun b => { b with delivered := true }) (fun _ => rfl) _ _ hUa
      · rw [hany]
        rcases ht with ht | ⟨ii, ht⟩
        · rw [ht] at hj; exact hLa j t hj
        · rw [ht, slot_upd_map] at hj
          by_cases hji : j = ii
          · rw [if_pos hji] at hj
            cases hs : slot (advance f0 n).ts j with
            | none => rw [hs] at hj; simp at hj
            | some t0 =>
              rw [hs] at hj
              simp only [Option.map_some, Option.some.injEq] at hj
              rw [← hj]; exact hLa j t0 hs
          · rw [if_neg hji] at hj; exact hLa j t hj
    rcases step_ack_shape f0 n peer id f' e h with ⟨hb, ht⟩ | ⟨i, ht, hb⟩
    · exact hlive f'.ts f'.bs (Or.inl hb) (Or.inl ht)
    · exact hlive f'.ts f'.bs (by rcases hb with hb | ⟨j, hb⟩; exact Or.inl hb; exact Or.inr ⟨j, hb⟩) (Or.inr ⟨i, ht⟩)

/-! ### Runs and the balance of copies -/

/-- The states reachable from a new forwarder by `step` and `poll`, with the ghost `g x`: the copies of bundle `x`
received by the accepted hold in force (0 when no bundle `x` is held). Refused inputs and quiet or sending polls
leave the ghost alone. -/
inductive Reach : F → (Nat → Nat) → Prop where
  | init (r m now b l t d : Nat) : Reach (F.new r m now b l t d) fun _ => 0
  | holdOk {f f' : F} {g : Nat → Nat} (n id d ex c : Nat) :
      Reach f g → step f n (.hold id d ex c) = (f', .ok) → Reach f' fun x => if x = id then c else g x
  | forgetOk {f f' : F} {g : Nat → Nat} (n id : Nat) :
      Reach f g → step f n (.forget id) = (f', .ok) → Reach f' fun x => if x = id then 0 else g x
  | stepKeep {f f' : F} {g : Nat → Nat} (n : Nat) (inp : Input) (e : Err) :
      Reach f g → step f n inp = (f', e) → (∀ id d ex c, inp = .hold id d ex c → e ≠ .ok) →
        (∀ id, inp = .forget id → e ≠ .ok) → Reach f' g
  | release {f f' : F} {g : Nat → Nat} (id : Nat) :
      Reach f g → poll f = (f', .release id) → Reach f' fun x => if x = id then 0 else g x
  | pollKeep {f f' : F} {g : Nat → Nat} (a : Act) :
      Reach f g → poll f = (f', a) → (∀ id, a ≠ .release id) → Reach f' g

theorem slot_replicate_none {α : Type} (n i : Nat) : slot (List.replicate n (none : Option α)) i = none := by
  induction n generalizing i with
  | zero => simp
  | succ n ih => cases i <;> simp [List.replicate_succ, slot_cons_zero, slot_cons_succ, ih]

theorem wsum_replicate_none {α : Type} (w : α → Nat) (n : Nat) : wsum w (List.replicate n (none : Option α)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, wsum_cons, ih]

theorem held_absent {f : F} {id : Nat} (h : anyS (fun x : Bundle => x.id == id) f.bs = false) : heldSum f id = 0 := wsum_absent id _ h

theorem handed_absent {f : F} (hL : Live f) {id : Nat} (h : anyS (fun x : Bundle => x.id == id) f.bs = false) : handedSum f id = 0 := by
  apply wsum_zero_of_slots
  intro i
  cases hs : slot f.ts i with
  | none => rfl
  | some t =>
    have := hL i t hs
    by_cases hb : t.bundle = id
    · subst hb; rw [h] at this; simp at this
    · simp [wT, hb]

theorem total_absent {f : F} (hL : Live f) {id : Nat} (h : anyS (fun x : Bundle => x.id == id) f.bs = false) :
    total f id = 0 := by
  unfold total; rw [held_absent h, handed_absent hL h]

/-- Under unique ids, dropping an id leaves nothing held for it. -/
theorem held_dropB {f : F} (hU : Uniq f.bs) (id : Nat) : heldSum (dropB f id) id = 0 := by
  unfold heldSum dropB
  simp only
  cases hf : firstIdx (·.id == id) f.bs with
  | none =>
    apply wsum_absent
    rw [anyS_eq, hf]; rfl
  | some i =>
    change wsum (wB id) (upd f.bs i fun _ => none) = 0
    obtain ⟨b, hb, hp, _⟩ := firstIdx_some hf
    have hbid : b.id = id := by simpa using hp
    have h1 := wsum_upd_clear (wB id) f.bs i hb
    have h2 := uniq_wsum f.bs i b hU hb
    subst hbid
    simp [wB] at h1
    omega

theorem poll_release_shape {f f' : F} {id : Nat} (h : poll f = (f', .release id)) : f' = dropB f id := by
  obtain ⟨i, b, hd, hb, hid, _⟩ := poll_release_only_done f f' id h
  obtain ⟨b', hb', _, hp⟩ := poll_release_done f i hd
  rw [hp] at h
  rw [hb] at hb'; cases hb'
  have := (Prod.mk.inj h).2
  simp at this
  rw [← (Prod.mk.inj h).1, this]

/-- **Balance.** In every reachable state, for every bundle, the copies held plus the copies handed equal the
copies received by the hold in force; the ids are unique and every transfer belongs to a held bundle. -/
theorem balance {f : F} {g : Nat → Nat} (h : Reach f g) :
    Uniq f.bs ∧ Live f ∧ ∀ x, total f x = g x := by
  induction h with
  | init r m now b l tt dd =>
    refine ⟨uniq_new _, fun i t ht => ?_, fun x => ?_⟩
    · have : slot (F.new r m now b l tt dd).ts i = none := slot_replicate_none _ _
      rw [this] at ht; cases ht
    · simp [total, heldSum, handedSum, F.new, wsum_replicate_none]
  | holdOk n id d ex c hr hs ih =>
    obtain ⟨hU, hL, ht⟩ := ih
    obtain ⟨hU', hL'⟩ := inv_step hs hU hL
    refine ⟨hU', hL', fun x => ?_⟩
    rcases hold_total _ n id d ex c _ _ hs x with ⟨he, _⟩ | ⟨_, _, ha, htot, _⟩
    · exact absurd rfl he
    · have h0 := total_absent (live_advance hL n) ha
      rw [advance_total] at h0
      by_cases hx : x = id
      · subst hx; simp only [htot, if_true]; omega
      · have hx' : ¬ id = x := fun e => hx e.symm
        simp only [htot, hx', hx, if_false]; exact ht x
  | forgetOk n id hr hs ih =>
    obtain ⟨hU, hL, ht⟩ := ih
    obtain ⟨hU', hL'⟩ := inv_step hs hU hL
    refine ⟨hU', hL', fun x => ?_⟩
    rcases step_forget _ n id _ _ hs with ⟨he, _⟩ | ⟨_, hf, _⟩
    · exact absurd he (by simp)
    · rw [hf]
      by_cases hx : x = id
      · subst hx; simp only [if_true]; unfold total; rw [held_dropB (f := advance _ n) hU, drop_handed]
      · simp only [hx, if_false]
        rw [drop_total _ _ _ hx, advance_total]; exact ht x
  | stepKeep n inp e hr hs hh hfg ih =>
    obtain ⟨hU, hL, ht⟩ := ih
    obtain ⟨hU', hL'⟩ := inv_step hs hU hL
    refine ⟨hU', hL', fun x => ?_⟩
    rw [← ht x]
    cases inp with
    | hold id d ex c =>
      rcases hold_total _ n id d ex c _ _ hs x with ⟨_, hf⟩ | ⟨he, _⟩
      · rw [hf]; exact advance_total _ n x
      · exact absurd he (hh id d ex c rfl)
    | forget id =>
      rcases step_forget _ n id _ _ hs with ⟨_, hf, _⟩ | ⟨he, _⟩
      · rw [hf]; exact advance_total _ n x
      · exact absurd he (hfg id rfl)
    | tick => exact step_other_total _ n _ _ _ hs (by intros; simp) (by intros; simp) x
    | linkUp p => exact step_other_total _ n _ _ _ hs (by intros; simp) (by intros; simp) x
    | linkDown p => exact step_other_total _ n _ _ _ hs (by intros; simp) (by intros; simp) x
    | acked p i => exact step_other_total _ n _ _ _ hs (by intros; simp) (by intros; simp) x
  | release id hr hs ih =>
    obtain ⟨hU, hL, ht⟩ := ih
    obtain ⟨hU', hL'⟩ := inv_poll hs hU hL
    refine ⟨hU', hL', fun x => ?_⟩
    have hf := poll_release_shape hs
    subst hf
    by_cases hx : x = id
    · subst hx; simp only [if_true]; unfold total; rw [held_dropB hU, drop_handed]
    · simp only [hx, if_false]
      rw [drop_total _ _ _ hx]; exact ht x
  | pollKeep a hr hs hn ih =>
    obtain ⟨hU, hL, ht⟩ := ih
    obtain ⟨hU', hL'⟩ := inv_poll hs hU hL
    refine ⟨hU', hL', fun x => ?_⟩
    rw [← ht x]
    exact poll_total _ _ a hs hn x

/-- A node never holds more copies of a bundle than it received. -/
theorem held_le_received {f : F} {g : Nat → Nat} (h : Reach f g) (x : Nat) : heldSum f x ≤ g x := by
  have := (balance h).2.2 x
  unfold total at this
  omega

/-- Copies handed are never more than received either, so held plus handed never exceed what came in. -/
theorem handed_le_received {f : F} {g : Nat → Nat} (h : Reach f g) (x : Nat) : handedSum f x ≤ g x := by
  have := (balance h).2.2 x
  unfold total at this
  omega

/-- A hold that is refused (a repeated hold, no copies, no room) adds nothing: the offered copies are lost. -/
theorem hold_refused_total (f0 : F) (n id d ex c : Nat) (f' : F) (e : Err) (h : step f0 n (.hold id d ex c) = (f', e))
    (he : e ≠ .ok) (x : Nat) : total f' x = total f0 x := by
  rcases hold_total f0 n id d ex c f' e h x with ⟨_, hf⟩ | ⟨he', _⟩
  · rw [hf]; exact advance_total f0 n x
  · exact absurd he' he

/-- The `u8` send counter never wraps. -/
theorem sat8_le (x : Nat) : sat8 x ≤ 255 := Nat.min_le_right _ _

#print axioms balance
#print axioms spray_total
#print axioms hold_total
#print axioms poll_serves_ready
#print axioms poll_gives_up_only

end Vinc.DtnForward
