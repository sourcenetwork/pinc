import Vinc.DtnForwardLib

/-!
# The retransmission scan

`poll_retransmit` walks the transfers in slot order: a due transfer on a link that is up gives up (and the scan goes
on) when its sends are used, else it sends again and the scan stops. `retr_rel` is the slot-by-slot account of what
one scan does, for every list of transfers; the timer and give-up theorems of `DtnForwardThm.lean` are read off it.
-/

namespace Vinc.DtnForward

/-- What the scan may do to one slot: nothing, give up (a due transfer, link up, sends used), or send again (a due
transfer, link up, sends left: the timer restarts, the counter goes up by one, and the action is the send). The
bundle, peer, copies and kind of a transfer never change. -/
def TRel (up : Nat → Bool) (retry maxS : Nat) (a : Option Act) : Option Transfer → Option Transfer → Prop
  | none, none => True
  | some t, some t' =>
    t'.bundle = t.bundle ∧ t'.peer = t.peer ∧ t'.given = t.given ∧ t'.deliver = t.deliver ∧
      (t' = t ∨
        (∃ s, t.phase = .sent 0 s ∧ up t.peer = true ∧ maxS ≤ s ∧ t' = { t with phase := .gaveUp }) ∨
        (∃ s, t.phase = .sent 0 s ∧ up t.peer = true ∧ s < maxS ∧
          t' = { t with phase := .sent retry (sat8 (s + 1)) } ∧ a = some (.send t.peer t.bundle t.given true)))
  | _, _ => False

theorem trel_refl (up : Nat → Bool) (retry maxS : Nat) (a : Option Act) (o : Option Transfer) :
    TRel up retry maxS a o o := by
  cases o <;> simp [TRel]

theorem tRel_cons {up : Nat → Bool} {retry maxS : Nat} {a : Option Act} {o o' : Option Transfer}
    {r r' : List (Option Transfer)} (hh : TRel up retry maxS a o o') (hl : r'.length = r.length)
    (hs : ∀ i, TRel up retry maxS a (slot r i) (slot r' i)) :
    (o' :: r').length = (o :: r).length ∧ ∀ i, TRel up retry maxS a (slot (o :: r) i) (slot (o' :: r') i) := by
  refine ⟨by simpa using hl, fun i => ?_⟩
  cases i with
  | zero => simpa [slot_cons_zero] using hh
  | succ n => simpa [slot_cons_succ] using hs n

theorem retr_rel (up : Nat → Bool) (retry maxS : Nat) :
    ∀ (ts : List (Option Transfer)),
      (retr up retry maxS ts).1.length = ts.length ∧
      ∀ i, TRel up retry maxS (retr up retry maxS ts).2 (slot ts i) (slot (retr up retry maxS ts).1 i) := by
  intro ts
  induction ts with
  | nil => exact ⟨rfl, fun i => by simp [retr, TRel]⟩
  | cons o r ih =>
    obtain ⟨ihl, ihs⟩ := ih
    generalize hr : retr up retry maxS r = res at ihl ihs
    obtain ⟨r', a'⟩ := res
    simp only at ihl ihs
    cases o with
    | none => simp only [retr, hr]; exact tRel_cons (trel_refl _ _ _ _ _) ihl ihs
    | some t =>
      cases hph : t.phase with
      | acked => simp only [retr, hph, hr]; exact tRel_cons (trel_refl _ _ _ _ _) ihl ihs
      | gaveUp => simp only [retr, hph, hr]; exact tRel_cons (trel_refl _ _ _ _ _) ihl ihs
      | sent rem s =>
        cases rem with
        | succ n => simp only [retr, hph, hr]; exact tRel_cons (trel_refl _ _ _ _ _) ihl ihs
        | zero =>
          by_cases hup : up t.peer = true
          · by_cases hm : maxS ≤ s
            · simp only [retr, hph, hr, hup, hm, ↓reduceIte]
              refine tRel_cons ?_ ihl ihs
              exact ⟨rfl, rfl, rfl, rfl, Or.inr (Or.inl ⟨s, hph, hup, hm, rfl⟩)⟩
            · simp only [retr, hph, hup, hm, ↓reduceIte]
              refine tRel_cons ?_ rfl (fun i => trel_refl _ _ _ _ _)
              exact ⟨rfl, rfl, rfl, rfl, Or.inr (Or.inr ⟨s, hph, hup, by omega, rfl, rfl⟩)⟩
          · simp only [retr, hph, hr, hup]
            exact tRel_cons (trel_refl _ _ _ _ _) ihl ihs

/-- A scan that sends found a due transfer on a link that is up with sends left, and restarted it. -/
theorem retr_send_slot {up : Nat → Bool} {retry maxS : Nat} :
    ∀ {ts : List (Option Transfer)} {x : Act}, (retr up retry maxS ts).2 = some x →
      ∃ i t s, slot ts i = some t ∧ t.phase = .sent 0 s ∧ up t.peer = true ∧ s < maxS ∧
        slot (retr up retry maxS ts).1 i = some { t with phase := .sent retry (sat8 (s + 1)) } ∧
        x = .send t.peer t.bundle t.given true := by
  intro ts
  induction ts with
  | nil => intro x h; simp [retr] at h
  | cons o r ih =>
    intro x h
    have shift : ∀ (o' : Option Transfer), (retr up retry maxS (o :: r)).1 = o' :: (retr up retry maxS r).1 →
        (retr up retry maxS (o :: r)).2 = (retr up retry maxS r).2 →
        ∃ i t s, slot (o :: r) i = some t ∧ t.phase = .sent 0 s ∧ up t.peer = true ∧ s < maxS ∧
          slot (retr up retry maxS (o :: r)).1 i = some { t with phase := .sent retry (sat8 (s + 1)) } ∧
          x = .send t.peer t.bundle t.given true := by
      intro o' h1 h2
      rw [h2] at h
      obtain ⟨i, t, s, a, b, c, d, e, f⟩ := ih h
      exact ⟨i + 1, t, s, by simpa [slot_cons_succ] using a, b, c, d, by rw [h1]; simpa [slot_cons_succ] using e, f⟩
    cases o with
    | none => exact shift none (by simp [retr]) (by simp [retr])
    | some t =>
      cases hph : t.phase with
      | acked => exact shift (some t) (by simp [retr, hph]) (by simp [retr, hph])
      | gaveUp => exact shift (some t) (by simp [retr, hph]) (by simp [retr, hph])
      | sent rem s =>
        cases rem with
        | succ n => exact shift (some t) (by simp [retr, hph]) (by simp [retr, hph])
        | zero =>
          by_cases hup : up t.peer = true
          · by_cases hm : maxS ≤ s
            · exact shift (some { t with phase := .gaveUp }) (by simp [retr, hph, hup, hm]) (by simp [retr, hph, hup, hm])
            · simp only [retr, hph, hup, hm, ↓reduceIte, Option.some.injEq] at h
              refine ⟨0, t, s, by simp [slot_cons_zero], hph, hup, by omega, ?_, h.symm⟩
              simp [retr, hph, hup, hm, slot_cons_zero]
          · exact shift (some t) (by simp [retr, hph, hup]) (by simp [retr, hph, hup])

theorem retr_act {up : Nat → Bool} {retry maxS : Nat} {ts : List (Option Transfer)} {x : Act}
    (h : (retr up retry maxS ts).2 = some x) : ∃ p b c, x = .send p b c true := by
  obtain ⟨_, t, _, _, _, _, _, _, hx⟩ := retr_send_slot h
  exact ⟨_, _, _, hx⟩

end Vinc.DtnForward
