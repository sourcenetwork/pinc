import Vinc.DtnScenarioInv

/-!
# How one forwarder operation moves the copies held

`heldOf f` is the copies of the scenario's bundle that forwarder `f` holds. This file proves, for the operations the
host glue applies, exactly how `heldOf` moves, and that the forwarder invariant (`FwdOk`: no bundle slot twice, every
transfer belongs to a held bundle, every bundle is the scenario's, the clock is not ahead of the system's) is kept:

* a hold that is accepted adds the offered copies; a refused one adds nothing (`held_hold_ok`, `held_hold_err`);
* a forget, and the release of a delivered or expired bundle, leave nothing held (`held_forget`, `held_poll_release`);
* a handover moves `copies / 2` out of the holder (`held_poll_send`); a retransmission, a quiet poll, a link change,
  a tick and an acknowledgement change nothing (`held_poll_keep`, `held_step_keep`).
-/

namespace Vinc.DtnScenario

open Vinc.DtnForward (F Bundle slot upd step poll advance dropB heldSum handedSum total wB wsum)

theorem step_now (f0 : F) (n : Nat) (inp : DtnForward.Input) : (step f0 n inp).1.now = max f0.now n := by
  cases inp <;> simp only [step] <;> (repeat' split) <;> simp [dropB, DtnForward.advance_now]

theorem poll_now (f : F) : (poll f).1.now = f.now := by
  unfold poll
  cases hd : DtnForward.doneIdx f with
  | some i => simp [dropB]
  | none =>
    simp only
    cases hq : DtnForward.retr (DtnForward.upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a0 =>
      cases a0 with
      | some y => simp
      | none =>
        simp only
        rcases DtnForward.spray_cases { f with ts := ts' } with hs | ⟨f1, p, id, c, hs⟩
        · rw [hs]
        · rw [hs]
          exact (DtnForward.spray_send_spec hs).2.2.2.2.1

/-- What the system proofs need of every forwarder. -/
structure FwdOk (c : Cfg) (t : Nat) (f : F) : Prop where
  uniq : DtnForward.Uniq f.bs
  live : DtnForward.Live f
  bok : BOk c.exp c.dest f.bs
  now : f.now ≤ t

theorem fwdOk_step {c : Cfg} {t t' : Nat} (ht : t ≤ t') {f0 f' : F} {inp : DtnForward.Input} {er : DtnForward.Err}
    (hs : step f0 t' inp = (f', er)) (h : FwdOk c t f0)
    (hh : ∀ id d ex c', inp = .hold id d ex c' → id = bid ∧ ex = c.exp ∧ d = c.dest) : FwdOk c t' f' := by
  obtain ⟨hU, hL⟩ := DtnForward.inv_step hs h.uniq h.live
  refine ⟨hU, hL, bok_step hs h.bok hh, ?_⟩
  have := step_now f0 t' inp
  rw [hs] at this
  simp only at this
  rw [this]; exact Nat.max_le.2 ⟨Nat.le_trans h.now ht, Nat.le_refl _⟩

theorem fwdOk_poll {c : Cfg} {t : Nat} {f f' : F} {a : DtnForward.Act} (hp : poll f = (f', a)) (h : FwdOk c t f) :
    FwdOk c t f' := by
  obtain ⟨hU, hL⟩ := DtnForward.inv_poll hp h.uniq h.live
  refine ⟨hU, hL, bok_poll hp h.bok, ?_⟩
  have := poll_now f
  rw [hp] at this
  simp only at this
  rw [this]; exact h.now

/-! ### The copies held -/

/-- The copies of the scenario's bundle that `f` holds. -/
def heldOf' (f : F) : Nat := heldSum f bid

theorem handed_advance (f : F) (n : Nat) : handedSum (advance f n) bid = handedSum f bid := by
  have h1 := DtnForward.advance_total f n bid
  have h2 : heldSum (advance f n) bid = heldSum f bid := rfl
  unfold total at h1
  omega

theorem held_step_keep {f0 f' : F} {n : Nat} {inp : DtnForward.Input} {er : DtnForward.Err}
    (hs : step f0 n inp = (f', er)) (h1 : ∀ id d ex c, inp ≠ .hold id d ex c) (h2 : ∀ id, inp ≠ .forget id) :
    heldSum f' bid = heldSum f0 bid := by
  cases inp with
  | tick => simp [step] at hs; rw [← hs.1]; rfl
  | hold id d ex c => exact absurd rfl (h1 id d ex c)
  | forget id => exact absurd rfl (h2 id)
  | linkUp peer =>
    obtain ⟨hb, _⟩ := DtnForward.step_link_shape f0 n peer true f' er (by simpa using hs)
    unfold heldSum; rw [hb]; rfl
  | linkDown peer =>
    obtain ⟨hb, _⟩ := DtnForward.step_link_shape f0 n peer false f' er (by simpa using hs)
    unfold heldSum; rw [hb]; rfl
  | acked peer id =>
    rcases DtnForward.step_ack_shape f0 n peer id f' er hs with ⟨hb, _⟩ | ⟨i, _, hb⟩
    · unfold heldSum; rw [hb]; rfl
    · rcases hb with hb | ⟨j, hb⟩
      · unfold heldSum; rw [hb]; rfl
      · unfold heldSum; rw [hb]
        exact DtnForward.wsum_upd_map (wB bid) (fun b => { b with delivered := true }) (fun _ => rfl) _ j

theorem held_hold_ok {f0 f' : F} {n d ex c : Nat} (hs : step f0 n (.hold bid d ex c) = (f', .ok)) :
    heldSum f' bid = heldSum f0 bid + c := by
  rcases DtnForward.hold_total f0 n bid d ex c f' .ok hs bid with ⟨he, _⟩ | ⟨_, _, _, htot, i, _, k, _, hf⟩
  · exact absurd rfl he
  · have h2 := handed_advance f0 n
    have h3 : handedSum f' bid = handedSum (advance f0 n) bid := by
      unfold handedSum; rw [hf]
    unfold total at htot
    have h4 : heldSum (advance f0 n) bid = heldSum f0 bid := rfl
    have h5 : handedSum (advance f0 n) bid = handedSum f0 bid := h2
    simp only [if_true] at htot
    omega

theorem held_hold_err {f0 f' : F} {n id d ex c : Nat} {er : DtnForward.Err}
    (hs : step f0 n (.hold id d ex c) = (f', er)) (he : er ≠ .ok) : heldSum f' bid = heldSum f0 bid := by
  rcases DtnForward.hold_total f0 n id d ex c f' er hs 0 with ⟨_, hf⟩ | ⟨he', _⟩
  · rw [hf]; rfl
  · exact absurd he' he

theorem held_forget {f0 f' : F} {n : Nat} {er : DtnForward.Err} (hs : step f0 n (.forget bid) = (f', er))
    (hU : DtnForward.Uniq f0.bs) : heldSum f' bid = 0 := by
  rcases DtnForward.step_forget f0 n bid f' er hs with ⟨_, hf, ha⟩ | ⟨_, hf, _⟩
  · rw [hf]; exact DtnForward.wsum_absent bid _ ha
  · rw [hf]; exact DtnForward.held_dropB (f := advance f0 n) hU bid

theorem held_poll_release {e d : Nat} {f f' : F} {id : Nat} (hp : poll f = (f', .release id)) (hU : DtnForward.Uniq f.bs)
    (hb : BOk e d f.bs) : heldSum f' bid = 0 := by
  obtain ⟨i, b, hd, hb', hid, _⟩ := DtnForward.poll_release_only_done f f' id hp
  have hidb : id = bid := by rw [← hid]; exact ((hb i b hb').1).symm ▸ rfl
  rw [DtnForward.poll_release_shape hp, hidb]
  exact DtnForward.held_dropB hU bid

/-- A retransmission, a quiet poll: the bundle slots are those of the state before. -/
theorem poll_keep_bs {f f' : F} {a : DtnForward.Act} (hp : poll f = (f', a)) (hr : ∀ id, a ≠ .release id)
    (hs : ∀ p id c, a ≠ .send p id c false) : f'.bs = f.bs := by
  unfold poll at hp
  cases hd : DtnForward.doneIdx f with
  | some i => simp only [hd, Prod.mk.injEq] at hp; exact absurd hp.2.symm (hr _)
  | none =>
    simp only [hd] at hp
    cases hq : DtnForward.retr (DtnForward.upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a0 =>
      cases a0 with
      | some y => simp only [hq, Prod.mk.injEq] at hp; rw [← hp.1]
      | none =>
        simp only [hq] at hp
        rcases DtnForward.spray_cases { f with ts := ts' } with hs0 | ⟨f1, p, id, c, hs0⟩
        · rw [hs0] at hp; simp only [Prod.mk.injEq] at hp; rw [← hp.1]
        · rw [hs0] at hp; simp only [Prod.mk.injEq] at hp
          exact absurd hp.2.symm (hs p id c)

theorem held_poll_keep {f f' : F} {a : DtnForward.Act} (hp : poll f = (f', a)) (hr : ∀ id, a ≠ .release id)
    (hs : ∀ p id c, a ≠ .send p id c false) : heldSum f' bid = heldSum f bid := by
  unfold heldSum; rw [poll_keep_bs hp hr hs]

/-- A fresh handover takes `c` copies out of the holder. -/
theorem held_poll_send {e d : Nat} {f f' : F} {p id c : Nat} (hp : poll f = (f', .send p id c false))
    (hb : BOk e d f.bs) : heldSum f' bid + c = heldSum f bid := by
  unfold poll at hp
  cases hd : DtnForward.doneIdx f with
  | some i => simp only [hd, Prod.mk.injEq] at hp; cases hp.2
  | none =>
    simp only [hd] at hp
    cases hq : DtnForward.retr (DtnForward.upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a0 =>
      cases a0 with
      | some y =>
        simp only [hq, Prod.mk.injEq] at hp
        obtain ⟨p', bb, c', hx⟩ := DtnForward.retr_act (x := y) (by rw [hq])
        rw [hx] at hp
        cases hp.2
      | none =>
        simp only [hq] at hp
        obtain ⟨_, li, bi, s, l, b, _, _, hbi, _, _, _, hcc, hf⟩ := DtnForward.spray_unfold hp
        have hid := (hb bi b hbi).1
        have e1 := DtnForward.wsum_upd_some (wB bid) f.bs bi (fun b => { b with copies := b.copies - c }) hbi
        have hc : c ≤ b.copies := by rw [hcc]; split <;> omega
        unfold heldSum
        rw [hf]
        simp only [wB, hid, beq_self_eq_true, if_true] at e1 ⊢
        omega

end Vinc.DtnScenario
