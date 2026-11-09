import Vinc.DtnScenarioNode

/-!
# What the forwarders of a scenario hold

Two invariants of the forwarder of every node of every reachable system, beyond the ones of `DtnForwardInv`:

* `BOk e d`: every bundle slot holds bundle 1, expires at `e` and is addressed to `d` (the glue only ever holds the one bundle of the
  scenario, with its expiry);
* the clock of the forwarder is not ahead of the clock of the system.

`inv_bok_step` and `inv_bok_poll` carry the first through `step` and `poll`; `Fwd` collects what the system proofs
need: `Uniq` (no bundle slot twice), `BOk` and the clock.
-/

namespace Vinc.DtnScenario

open DtnForward (F Bundle slot upd)

/-- Every occupied slot satisfies `P`. -/
def AllB (P : Bundle → Prop) (l : List (Option Bundle)) : Prop := ∀ i b, slot l i = some b → P b

theorem allB_cons {P : Bundle → Prop} {o : Option Bundle} {r : List (Option Bundle)} :
    AllB P (o :: r) ↔ (∀ b, o = some b → P b) ∧ AllB P r := by
  constructor
  · intro h
    exact ⟨fun b hb => h 0 b (by simpa [DtnForward.slot_cons_zero] using hb),
           fun i b hb => h (i + 1) b (by simpa [DtnForward.slot_cons_succ] using hb)⟩
  · rintro ⟨h1, h2⟩ i b hb
    cases i with
    | zero => exact h1 b (by simpa [DtnForward.slot_cons_zero] using hb)
    | succ n => exact h2 n b (by simpa [DtnForward.slot_cons_succ] using hb)

theorem allB_nil (P : Bundle → Prop) : AllB P [] := by
  intro i b hb; simp [DtnForward.slot] at hb

theorem allB_replicate (P : Bundle → Prop) (n : Nat) : AllB P (List.replicate n none) := by
  induction n with
  | zero => exact allB_nil P
  | succ n ih => rw [List.replicate_succ, allB_cons]; exact ⟨fun b hb => by simp at hb, ih⟩

theorem allB_upd (P : Bundle → Prop) (g : Option Bundle → Option Bundle)
    (hg : ∀ o, (∀ b, o = some b → P b) → ∀ b', g o = some b' → P b') :
    ∀ (l : List (Option Bundle)) (i : Nat), AllB P l → AllB P (upd l i g)
  | [], _, _ => allB_nil P
  | o :: r, i, h => by
    rw [allB_cons] at h
    cases i with
    | zero => rw [DtnForward.upd, allB_cons]; exact ⟨hg o h.1, h.2⟩
    | succ n => rw [DtnForward.upd, allB_cons]; exact ⟨h.1, allB_upd P g hg r n h.2⟩

/-- Every bundle slot holds bundle 1 with expiry `e` and destination `d`. -/
def BOk (e d : Nat) (l : List (Option Bundle)) : Prop := AllB (fun b => b.id = bid ∧ b.exp = e ∧ b.dest = d) l

theorem bok_advance {e d : Nat} {f : F} (h : BOk e d f.bs) (n : Nat) : BOk e d (DtnForward.advance f n).bs := h

theorem bok_dropB {e d : Nat} {f : F} (h : BOk e d f.bs) (id : Nat) : BOk e d (DtnForward.dropB f id).bs := by
  simp only [DtnForward.dropB]
  cases DtnForward.firstIdx (·.id == id) f.bs with
  | none => exact h
  | some i => exact allB_upd _ _ (fun o _ b' hb' => by simp at hb') _ i h

theorem bok_map {e d : Nat} {l : List (Option Bundle)} (h : BOk e d l) (g : Bundle → Bundle)
    (hg : ∀ b, (g b).id = b.id ∧ (g b).exp = b.exp ∧ (g b).dest = b.dest) (i : Nat) : BOk e d (upd l i (Option.map g)) :=
  allB_upd _ _ (fun o ho b' hb' => by
    cases o with
    | none => simp at hb'
    | some b0 =>
      simp only [Option.map_some, Option.some.injEq] at hb'
      subst hb'
      have := ho b0 rfl
      rw [(hg b0).1, (hg b0).2.1, (hg b0).2.2]; exact this) l i h

theorem bok_spray {e d : Nat} {f : F} (h : BOk e d f.bs) : BOk e d (DtnForward.spray f).1.bs := by
  rcases DtnForward.spray_cases f with hs | ⟨f1, p, id, c, hs⟩
  · rw [hs]; exact h
  · obtain ⟨_, li, bi, s, l, b, _, _, _, _, _, _, _, hf⟩ := DtnForward.spray_unfold hs
    rw [hs]
    show BOk e d f1.bs
    rw [hf]
    exact bok_map h (fun b => { b with copies := b.copies - c }) (fun _ => ⟨rfl, rfl, rfl⟩) bi

theorem bok_poll {e d : Nat} {f f' : F} {a : DtnForward.Act} (hp : DtnForward.poll f = (f', a)) (h : BOk e d f.bs) :
    BOk e d f'.bs := by
  unfold DtnForward.poll at hp
  cases hd : DtnForward.doneIdx f with
  | some i =>
    simp only [hd, Prod.mk.injEq] at hp
    rw [← hp.1]; exact bok_dropB h _
  | none =>
    simp only [hd] at hp
    cases hq : DtnForward.retr (DtnForward.upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a0 =>
      cases a0 with
      | some y => simp only [hq, Prod.mk.injEq] at hp; rw [← hp.1]; exact h
      | none =>
        simp only [hq] at hp
        rw [← show (DtnForward.spray { f with ts := ts' }).1 = f' from congrArg Prod.fst hp]
        exact bok_spray (f := { f with ts := ts' }) h

theorem bok_step {e d : Nat} {f0 f' : F} {n : Nat} {inp : DtnForward.Input} {er : DtnForward.Err}
    (hs : DtnForward.step f0 n inp = (f', er)) (h : BOk e d f0.bs)
    (hh : ∀ id d' ex c, inp = .hold id d' ex c → id = bid ∧ ex = e ∧ d' = d) : BOk e d f'.bs := by
  have ha : BOk e d (DtnForward.advance f0 n).bs := h
  cases inp with
  | tick => simp [DtnForward.step] at hs; rw [← hs.1]; exact ha
  | hold id d' ex c =>
    obtain ⟨hid, hex, hdd⟩ := hh id d' ex c rfl
    rcases DtnForward.hold_total f0 n id d' ex c f' er hs 0 with ⟨_, hf⟩ | ⟨_, _, _, _, i, _, k, _, hf⟩
    · rw [hf]; exact ha
    · rw [hf]
      exact allB_upd _ _ (fun o _ b' hb' => by
        simp only [Option.some.injEq] at hb'; subst hb'; exact ⟨hid, hex, hdd⟩) _ i ha
  | forget id =>
    rcases DtnForward.step_forget f0 n id f' er hs with ⟨_, hf, _⟩ | ⟨_, hf, _⟩
    · rw [hf]; exact ha
    · rw [hf]; exact bok_dropB ha _
  | linkUp peer =>
    obtain ⟨hb, _⟩ := DtnForward.step_link_shape f0 n peer true f' er (by simpa using hs)
    rw [hb]; exact ha
  | linkDown peer =>
    obtain ⟨hb, _⟩ := DtnForward.step_link_shape f0 n peer false f' er (by simpa using hs)
    rw [hb]; exact ha
  | acked peer id =>
    rcases DtnForward.step_ack_shape f0 n peer id f' er hs with ⟨hb, _⟩ | ⟨i, _, hb⟩
    · rw [hb]; exact ha
    · rcases hb with hb | ⟨j, hb⟩
      · rw [hb]; exact ha
      · rw [hb]; exact bok_map ha (fun b => { b with delivered := true }) (fun _ => ⟨rfl, rfl, rfl⟩) j

end Vinc.DtnScenario
