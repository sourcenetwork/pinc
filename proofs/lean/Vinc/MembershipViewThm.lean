import Vinc.MembershipViewFrame

/-!
# Membership view: the theorems of the member view (`view.rs`)
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

/-! ## `remove_from_view` -/

/-- What `remove_from_view` leaves alone. -/
def Keeps (n n' : N) : Prop :=
  n'.hv = n.hv ∧ n'.epoch = n.epoch ∧ n'.revoked = n.revoked ∧ n'.me = n.me ∧ n'.isHub = n.isHub ∧
  n'.boot = n.boot ∧ n'.roster = n.roster ∧ n'.up = n.up ∧ n'.heard = n.heard ∧ n'.primary = n.primary ∧ n'.homeOk = n.homeOk ∧
  n'.quietUntil = n.quietUntil

theorem Keeps.refl (n : N) : Keeps n n := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem removeFromView_keeps (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (x : Bool) :
    Keeps n (N.removeFromView e n now m cur src x).1 := by
  unfold N.removeFromView
  split
  · exact Keeps.refl n
  · split
    · split <;> simp [Keeps]
    · split
      · simp [Keeps]
      · by_cases hh : n.isHub = true <;> by_cases hg : (n.goneVer.len < MAX_TABLE ∨ n.goneVer.has m = true) <;>
          by_cases hl : n.left.has m = true <;> by_cases hx : x = true <;> simp [Keeps, hh, hg, hl, hx]


/-! ## `recompute_one`, in the three pieces of the code -/

/-- The arm for a member the view already lists. -/
def rcKnown (e : Env) (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : N × Bool × Bool :=
  if best.inc / 65536 ≤ c.rc.inc / 65536 then
    if best.inc / 65536 == c.rc.inc / 65536 && decide (c.rc.inc ≤ best.inc) then
      let n := { n with members := n.members.modify m (fun x => { x with rc := { x.rc with inc := best.inc } }) }
      let (n, ch1) := if best.ver != c.rc.ver then
          (({ n with members := n.members.modify m (fun x => { x with rc := { x.rc with ver := best.ver } }) }).emit (.stack m best.ver), true)
        else (n, false)
      let (n, ch2) := if best.th != c.rc.th then
          (({ n with members := n.members.modify m (fun x => { x with rc := { x.rc with th := best.th } }) }).emit (.addr m), true)
        else (n, false)
      (n, ch1 || ch2, false)
    else (n, false, false)
  else
    let n := { n with members := n.members.insert m ⟨best⟩ }
    let n := n.emit (.joined m)
    let old := (some (c.rc.ver, c.rc.th)).orElse (fun _ => n.goneVer.get? m)
    let n := { n with goneVer := n.goneVer.erase m }
    let n := match old with
      | some (ver, th) => if ver != best.ver then n.emit (.stack m best.ver) else n
      | none => n
    (n, true, false)

/-- The arm for a member the view does not list. -/
def rcNew (e : Env) (n : N) (m : Nat) (best : Rec) : N × Bool × Bool :=
  if n.members.len ≥ MAX_TABLE then (n, false, true)
  else
    let n := { n with members := n.members.insert m ⟨best⟩ }
    let n := n.emit (.joined m)
    let old := n.goneVer.get? m
    let n := { n with goneVer := n.goneVer.erase m }
    let n := match old with
      | some (ver, th) =>
        let n := if ver != best.ver then n.emit (.stack m best.ver) else n
        if th != best.th then n.emit (.addr m) else n
      | none => n
    (n, true, false)

/-- The view keeps no suspicion flag and reports no suspicion (c26385e): after the arm there is nothing left to do. -/
def rcTail (n : N) (_m : Nat) (_absent : Bool) (changed : Bool) : N × Bool :=
  (n, changed)

theorem recomputeOne_eq_v (e : Env) (n : N) (now m : Nat) :
    N.recomputeOne e n now m =
      (let src := n.source now
       let (best, expired) := n.candidates now src m
       let cur := n.members.get? m
       match best with
       | none => N.removeFromView e n now m cur src expired
       | some (best, absent) =>
         let n := if n.isHub && (match cur with | none => true | some c => decide (c.rc ≠ best)) then
             N.homeDelta e n m best .alive else n
         let (n, changed, early) : N × Bool × Bool :=
           match cur with
           | some c => rcKnown e n m best c
           | none => rcNew e n m best
         if early then (n, false) else rcTail n m absent changed) := rfl

theorem rcKnown_keeps (e : Env) (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : Keeps n (rcKnown e n m best c).1 := by
  unfold rcKnown
  by_cases h1 : best.inc / 65536 ≤ c.rc.inc / 65536 <;> by_cases h2 : (best.inc / 65536 == c.rc.inc / 65536 && decide (c.rc.inc ≤ best.inc)) = true <;>
    by_cases h3 : (best.ver != c.rc.ver) = true <;> by_cases h4 : (best.th != c.rc.th) = true <;>
    by_cases h5 : (match (some (c.rc.ver, c.rc.th)).orElse (fun _ => (n.emit (.joined m)).goneVer.get? m) with | some (ver, th) => ver != best.ver | none => false) = true <;>
    simp [Keeps, h1, h2, h3, h4, h5] <;> split <;> simp_all


/-- `Keeps`, and no member other than `m` changed. -/
def Keeps2 (m : Nat) (n n' : N) : Prop := Keeps n n' ∧ ∀ k, k ≠ m → n'.members.get? k = n.members.get? k

theorem Keeps2.refl (m : Nat) (n : N) : Keeps2 m n n := ⟨Keeps.refl n, fun _ _ => rfl⟩

theorem Keeps.trans {a b c : N} (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7, b8.trans a8,
    b9.trans a9, b10.trans a10, b11.trans a11, b12.trans a12⟩

theorem removeFromView_keeps2 (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (x : Bool) :
    Keeps2 m n (N.removeFromView e n now m cur src x).1 := by
  refine ⟨removeFromView_keeps e n now m cur src x, ?_⟩
  intro k hk
  unfold N.removeFromView
  split
  · rfl
  · split
    · split <;> simp
    · split
      · simp
      · simp [AMap.get?_erase_ne _ _ _ hk]
        by_cases hh : n.isHub = true <;> by_cases hg : (n.goneVer.len < MAX_TABLE ∨ n.goneVer.has m = true) <;>
          by_cases hl : n.left.has m = true <;> by_cases hx : x = true <;> simp [hh, hg, hl, hx, AMap.get?_erase_ne _ _ _ hk]

theorem rcKnown_keeps2 (e : Env) (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : Keeps2 m n (rcKnown e n m best c).1 := by
  refine ⟨rcKnown_keeps e n m best c, ?_⟩
  intro k hk
  unfold rcKnown
  by_cases h1 : best.inc / 65536 ≤ c.rc.inc / 65536 <;> by_cases h2 : (best.inc / 65536 == c.rc.inc / 65536 && decide (c.rc.inc ≤ best.inc)) = true <;>
    by_cases h3 : (best.ver != c.rc.ver) = true <;> by_cases h4 : (best.th != c.rc.th) = true <;>
    by_cases h5 : (match (some (c.rc.ver, c.rc.th)).orElse (fun _ => (n.emit (.joined m)).goneVer.get? m) with | some (ver, th) => ver != best.ver | none => false) = true <;>
    simp [h1, h2, h3, h4, h5, AMap.get?_modify_ne _ _ _ _ hk, AMap.get?_insert_ne _ _ _ _ hk] <;> split <;> simp_all [AMap.get?_modify_ne _ _ _ _ hk, AMap.get?_insert_ne _ _ _ _ hk]

theorem rcNew_keeps2 (e : Env) (n : N) (m : Nat) (best : Rec) : Keeps2 m n (rcNew e n m best).1 := by
  unfold rcNew
  by_cases h1 : n.members.len ≥ MAX_TABLE
  · simp [h1]; exact Keeps2.refl m n
  · refine ⟨?_, ?_⟩
    · simp [h1, Keeps]
      repeat' split
      all_goals simp_all
    · intro k hk
      simp [h1, AMap.get?_insert_ne _ _ _ _ hk]
      repeat' split
      all_goals simp_all [AMap.get?_insert_ne _ _ _ _ hk]

theorem rcTail_keeps2 (n : N) (m : Nat) (absent changed : Bool) : Keeps2 m n (rcTail n m absent changed).1 := by
  unfold rcTail
  refine ⟨?_, ?_⟩
  · repeat' split
    all_goals simp_all [Keeps, Keeps.refl]
  · intro k hk
    repeat' split
    all_goals simp_all [AMap.get?_modify_ne _ _ _ _ hk]


theorem Keeps2.trans {m : Nat} {a b c : N} (h1 : Keeps2 m a b) (h2 : Keeps2 m b c) : Keeps2 m a c :=
  ⟨Keeps.trans h1.1 h2.1, fun k hk => (h2.2 k hk).trans (h1.2 k hk)⟩

theorem OutOnly.keeps2 {m : Nat} {a b : N} (h : OutOnly a b) : Keeps2 m a b := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

theorem hdIf_keeps2 (e : Env) (n : N) (m : Nat) (b0 : Rec) (c : Bool) :
    Keeps2 m n (if c = true then N.homeDelta e n m b0 .alive else n) := by
  by_cases h : c = true
  · simp only [h, if_true]; exact OutOnly.keeps2 (homeDelta_out e n m b0 .alive)
  · simp only [h, if_false]; exact Keeps2.refl m n

theorem recomputeOne_keeps2 (e : Env) (n : N) (now m : Nat) : Keeps2 m n (N.recomputeOne e n now m).1 := by
  rw [recomputeOne_eq_v]
  dsimp only
  split
  · exact removeFromView_keeps2 _ _ _ _ _ _ _
  · rename_i b0 a0 hb
    have h1 := hdIf_keeps2 e n m b0 (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0)))
    generalize (if (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true then
        N.homeDelta e n m b0 .alive else n) = n1 at h1 ⊢
    have h2 : ∀ (r : N × Bool × Bool), Keeps2 m n1 r.1 → Keeps2 m n
        (if r.2.2 = true then (r.1, false) else rcTail r.1 m a0 r.2.1).1 := by
      intro r hr
      by_cases he : r.2.2 = true
      · simp only [he, if_true]; exact h1.trans hr
      · simp only [he, if_false]; exact (h1.trans hr).trans (rcTail_keeps2 _ _ a0 _)
    split
    · rename_i c hc
      exact h2 _ (rcKnown_keeps2 _ _ _ _ _)
    · exact h2 _ (rcNew_keeps2 _ _ _ _)

end Vinc.Membership
