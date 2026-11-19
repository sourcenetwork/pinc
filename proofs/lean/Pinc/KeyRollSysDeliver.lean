import Pinc.KeyRollSysStep
import Pinc.KeyRollSysRecv

namespace Pinc.KeyRollSys
open Pinc.KeyRoll

/-! ## `Deliver`, first half: the keys layer keeps the invariant -/

theorem Bool.eq_or_not (a n : Bool) : a = n ∨ a = !n := by cases a <;> cases n <;> simp

theorem inv_recv {P : Params} {S : Sys} {n : Bool} {p : Pkt} {f : Bool} (h : Inv P S) (hp : p ∈ S.net)
    (hsrc : p.src = !n) :
    Inv P (S.setNode n ((S.nd n).afterRecv P p f S.now).1) := by
  have hnn := (h.node n).afterRecv p f S.now
  have rf := afterRecv_facts (h.node n) p f S.now
  have hla := afterRecv_lastAns P (S.nd n) p f S.now
  generalize ((S.nd n).afterRecv P p f S.now).1 = s1 at hnn rf hla ⊢
  have hne : ∀ m, m ≠ n → (S.setNode n s1).nd m = S.nd m := fun m hm => Sys.setNode_ne S n m _ hm
  have hsame : (S.setNode n s1).nd n = s1 := Sys.setNode_same _ _ _
  have fr : ∀ m, (S.setNode n s1).nd m = S.nd m ∨ (m = n ∧ (S.setNode n s1).nd m = s1) := by
    intro m; by_cases hm : m = n
    · subst hm; exact Or.inr ⟨rfl, hsame⟩
    · exact Or.inl (hne m hm)
  have eCtr : ∀ m, ((S.setNode n s1).nd m).ctr = (S.nd m).ctr := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]; exact rf.ctr
  have eDers : ∀ m, ((S.setNode n s1).nd m).ders = (S.nd m).ders := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]; exact rf.ders
  have eRoll : ∀ m, ((S.setNode n s1).nd m).roll = (S.nd m).roll := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]; exact rf.roll
  have eOut : ∀ m, ((S.setNode n s1).nd m).out = (S.nd m).out := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]; exact rf.out
  have eNpn : ∀ m, ((S.setNode n s1).nd m).npn = (S.nd m).npn := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]; exact rf.npn
  have eChg : ∀ m, ((S.setNode n s1).nd m).chg = (S.nd m).chg := by
    intro m; simp [Node.chg, eDers m]
  -- the generations only move forward
  have skMono : ∀ m, (S.nd m).sk.g ≤ ((S.setNode n s1).nd m).sk.g := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
    · exact Nat.le_refl _
    · rcases rf.keys with k | ⟨k, _⟩
      · exact Nat.le_of_eq k.1.symm
      · by_cases hst : (S.nd m).stg.isSome = true
        · have := k.2.2.2.2.1 hst; omega
        · have : (S.nd m).stg = none := by simpa using hst
          have := k.2.2.2.2.2 this; omega
  have curMono : ∀ m, (S.nd m).cur.g ≤ ((S.setNode n s1).nd m).cur.g := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
    · exact Nat.le_refl _
    · rcases rf.keys with k | ⟨k, _⟩
      · exact Nat.le_of_eq k.2.1.symm
      · have := k.2.1; omega
  inv_mk
  all_goals try dsimp only
  case node =>
    intro m
    rcases fr m with e | ⟨rfl, e⟩
    · rw [e]; exact h.node m
    · rw [e]; exact hnn
  case netPh => exact h.netPh
  case netDep =>
    intro q hq
    obtain ⟨a1, a2⟩ := h.netDep q hq
    exact ⟨Nat.le_trans a1 (skMono _), by rw [eNpn]; exact a2⟩
  case netMsg => intro q hq m hm; rw [eCtr]; exact h.netMsg q hq m hm
  case netSlog => exact h.netSlog
  case netReq => exact h.netReq
  case netAns => exact h.netAns
  case slogOK =>
    intro x hx
    obtain ⟨a1, a2, a3, a4⟩ := h.slogOK x hx
    exact ⟨by rw [eNpn]; exact a1, a2, Nat.le_trans a3 (skMono _), a4⟩
  case slogOrd => exact h.slogOrd
  case slogUniq => exact h.slogUniq
  case breqOK =>
    intro b hb
    obtain ⟨⟨k, k1, k2⟩, b2, b3⟩ := h.breqOK b hb
    refine ⟨⟨k, k1, by rw [eCtr]; exact k2⟩, by rw [eChg]; exact b2, ?_⟩
    rw [eChg, eRoll]; exact b3
  case breqPend =>
    intro m rq hrq
    rw [eRoll] at hrq
    obtain ⟨j, hj, hc⟩ := h.breqPend m rq hrq
    exact ⟨j, hj, by rw [eChg]; exact hc⟩
  case breqFun => exact h.breqFun
  case breqF3 =>
    intro b hb hd hj
    rw [eRoll] at hd; rw [eChg] at hj; rw [eDers]
    exact h.breqF3 b hb hd hj
  case derBreq =>
    intro m q e he hs
    rw [eDers] at he
    exact h.derBreq m q e he hs
  case stlOK =>
    intro c hc
    obtain ⟨s1', s2, s3, s4, s5, s6, s7⟩ := h.stlOK c hc
    refine ⟨s1', by rw [eCtr]; exact s2, by rw [eDers]; exact s3, Nat.le_trans s4 (curMono _),
      by rw [eNpn]; exact s5, s6, s7⟩
  case outAns => intro m a ho ha; rw [eOut] at ho; exact h.outAns m a ho ha
  case lastAnsStl => intro m sh a hl; rw [eRoll] at hl; exact h.lastAnsStl m sh a hl
  case ansLastStl =>
    intro m a hl
    rcases fr m with e | ⟨rfl, e⟩
    · rw [e] at hl; exact h.ansLastStl m a hl
    · rw [e, hla] at hl; exact h.ansLastStl _ a hl
  case unsent => intro m mm ho ha; rw [eOut] at ho; exact h.unsent m mm ho ha
  case compOK =>
    intro c hc
    obtain ⟨⟨k, k1, k2⟩, k3⟩ := h.compOK c hc
    refine ⟨⟨k, k1, by rw [eCtr]; exact k2⟩, ?_⟩
    rw [eRoll]; exact k3
  case compUniq => exact h.compUniq
  case agree => exact h.agree
  case pp => simp only [eDers]; exact h.pp
  case qq =>
    intro m rq hrq c hc hcn hto
    rw [eRoll] at hrq
    rw [eChg]; exact h.qq m rq hrq c hc hcn hto
  case nxtFloor =>
    intro m x hx
    by_cases hmn : m = n
    · subst hmn
      rw [hsame] at hx
      rcases rf.keys with k | ⟨k, _⟩
      · obtain ⟨y, hy, hfl⟩ := k.2.2.2.2 x hx
        rcases h.nxtFloor m y hy with h0 | ⟨c, hc, hcn, hpos, hspn⟩
        · exact Or.inl (by rw [hfl]; exact h0)
        · refine Or.inr ⟨c, hc, hcn, ?_, by rw [hfl]; exact hspn⟩
          rw [hsame, k.2.1]; exact hpos
      · rw [k.2.2.1] at hx; simp at hx
    · rw [hne m hmn] at hx ⊢
      exact h.nxtFloor m x hx
  case d1 =>
    intro X
    have hd1n := h.d1 n
    have hd1b := h.d1 (!n)
    rw [Bool.not_not] at hd1b
    have cA := (h.node n).cn
    have cB := (h.node (!n)).cn
    have hBn : (S.setNode n s1).nd (!n) = S.nd (!n) := Sys.setNode_not S n s1
    rcases Bool.eq_or_not X n with hX | hX
    · subst hX
      rw [hBn, hsame]
      rcases rf.keys with k | ⟨k, hdep⟩
      · obtain ⟨k1, k2, k3, k4, _⟩ := k
        rw [k1]; exact hd1n
      · obtain ⟨k1, k2, k3, k4, k5, k6⟩ := k
        by_cases hst : (S.nd X).stg.isSome = true
        · have e1 := k5 hst
          have hnx : (S.nd X).nxt.isSome = true := cA.2.2.2.2 hst
          have hpd := (h.netDep p hp).1
          rw [hsrc] at hpd
          rw [hdep] at hpd
          -- B holds the key at the new level and has staged
          have a1 := cA.1 hst
          have a2 := cA.2.2.1 hnx
          have b1 : (S.nd (!X)).stg.isSome = true ∨ (S.nd (!X)).stg.isSome = false := by cases (S.nd (!X)).stg <;> simp
          by_cases hnB : (S.nd (!X)).nxt.isSome = true
          · have c1 := cB.2.2.1 hnB
            have c2 : (S.nd (!X)).chg ≥ (S.nd (!X)).sk.g := by
              rcases b1 with b | b
              · have := cB.1 b; omega
              · have := cB.2.1 b; omega
            exact ⟨by omega, by omega, fun _ => hnB⟩
          · have hnB' : (S.nd (!X)).nxt.isSome = false := by simpa using hnB
            have c1 := cB.2.2.2.1 hnB'
            have c2 : (S.nd (!X)).chg ≥ (S.nd (!X)).sk.g := by
              rcases b1 with b | b
              · have := cB.1 b; omega
              · have := cB.2.1 b; omega
            exfalso; omega
        · have hst' : (S.nd X).stg = none := by simpa using hst
          rw [k6 hst']; exact hd1n
    · have hXn : X = !n := hX
      subst hXn
      rw [Bool.not_not, hBn, hsame]
      rcases rf.keys with k | ⟨k, hdep⟩
      · obtain ⟨k1, k2, k3, k4, _⟩ := k
        rw [k2, k3]; exact hd1b
      · obtain ⟨k1, k2, k3, k4, k5, k6⟩ := k
        have hpd := (h.netDep p hp).1
        rw [hsrc, hdep] at hpd
        rw [k2, k3]
        refine ⟨by omega, by omega, by intro; omega⟩

/-! ## `Deliver`, second half: what the REKEY body does -/

theorem Sys.setNode_cases (S : Sys) (n m : Bool) (s' : Node) :
    (S.setNode n s').nd m = S.nd m ∨ (m = n ∧ (S.setNode n s').nd m = s') := by
  by_cases hm : m = n
  · subst hm; exact Or.inr ⟨rfl, Sys.setNode_same _ _ _⟩
  · exact Or.inl (Sys.setNode_ne S n m s' hm)

theorem Sys.setNode_self (S : Sys) (n : Bool) : S.setNode n (S.nd n) = S := by
  cases S with
  | mk nd net now slog comp stl breq =>
    simp only [Sys.setNode, Sys.mk.injEq, and_true]
    funext m
    by_cases hm : m = n
    · subst hm; simp [upd]
    · simp [upd, hm]

theorem Sys.setNode_setNode (S : Sys) (n : Bool) (a b : Node) : (S.setNode n a).setNode n b = S.setNode n b := by
  cases S with
  | mk nd net now slog comp stl breq =>
    simp only [Sys.setNode, Sys.mk.injEq, and_true]
    funext m
    by_cases hm : m = n <;> simp [upd, hm]

/-- Changing only the message waiting of a node and the time of the last send. -/
theorem inv_setOut {P : Params} {S : Sys} {n : Bool} (h : Inv P S) (o : Option Msg) (r : Option Nat)
    (hnn : NodeInv P n { S.nd n with out := o, reqAt := r })
    (hA : ∀ a, o = some a → a.answer = true → ∃ c ∈ S.stl, c.ans = a ∧ c.n = n)
    (hU : ∀ a, o = some a → a.answer = false → ∀ p ∈ S.net, p.pl ≠ some a) :
    Inv P (S.setNode n { S.nd n with out := o, reqAt := r }) := by
  have fr : ∀ m, (S.setNode n { S.nd n with out := o, reqAt := r }).nd m = S.nd m ∨
      (m = n ∧ (S.setNode n { S.nd n with out := o, reqAt := r }).nd m = { S.nd n with out := o, reqAt := r }) :=
    fun m => Sys.setNode_cases S n m _
  have hsame : (S.setNode n { S.nd n with out := o, reqAt := r }).nd n = { S.nd n with out := o, reqAt := r } := Sys.setNode_same _ _ _
  have hne : ∀ m, m ≠ n → (S.setNode n { S.nd n with out := o, reqAt := r }).nd m = S.nd m :=
    fun m hm => Sys.setNode_ne S n m _ hm
  have eSk : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r }).nd m).sk = (S.nd m).sk := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eCtr : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r }).nd m).ctr = (S.nd m).ctr := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eCur : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r }).nd m).cur = (S.nd m).cur := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eNxt : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r }).nd m).nxt = (S.nd m).nxt := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eDers : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r }).nd m).ders = (S.nd m).ders := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eRoll : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r }).nd m).roll = (S.nd m).roll := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eNpn : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r }).nd m).npn = (S.nd m).npn := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eChg : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r }).nd m).chg = (S.nd m).chg := by
    intro m; simp [Node.chg, eDers m]
  inv_mk
  all_goals try dsimp only
  case node =>
    intro m; rcases fr m with e | ⟨rfl, e⟩
    · rw [e]; exact h.node m
    · rw [e]; exact hnn
  case netPh => exact h.netPh
  case netDep => intro q hq; rw [eSk, eNpn]; exact h.netDep q hq
  case netMsg => intro q hq m hm; rw [eCtr]; exact h.netMsg q hq m hm
  case netSlog => exact h.netSlog
  case netReq => exact h.netReq
  case netAns => exact h.netAns
  case slogOK =>
    intro x hx
    obtain ⟨a1, a2, a3, a4⟩ := h.slogOK x hx
    exact ⟨by rw [eNpn]; exact a1, a2, by rw [eSk]; exact a3, a4⟩
  case slogOrd => exact h.slogOrd
  case slogUniq => exact h.slogUniq
  case breqOK =>
    intro b hb
    obtain ⟨⟨k, k1, k2⟩, b2, b3⟩ := h.breqOK b hb
    refine ⟨⟨k, k1, by rw [eCtr]; exact k2⟩, by rw [eChg]; exact b2, ?_⟩
    rw [eChg, eRoll]; exact b3
  case breqPend =>
    intro m rq hrq
    rw [eRoll] at hrq
    obtain ⟨j, hj, hc⟩ := h.breqPend m rq hrq
    exact ⟨j, hj, by rw [eChg]; exact hc⟩
  case breqFun => exact h.breqFun
  case breqF3 =>
    intro b hb hd hj
    rw [eRoll] at hd; rw [eChg] at hj; rw [eDers]
    exact h.breqF3 b hb hd hj
  case derBreq => intro m q e he hs; rw [eDers] at he; exact h.derBreq m q e he hs
  case stlOK =>
    intro c hc
    obtain ⟨s1', s2, s3, s4, s5, s6, s7⟩ := h.stlOK c hc
    exact ⟨s1', by rw [eCtr]; exact s2, by rw [eDers]; exact s3, by rw [eCur]; exact s4,
      by rw [eNpn]; exact s5, s6, s7⟩
  case outAns =>
    intro m a ho ha
    by_cases hmn : m = n
    · subst hmn; rw [hsame] at ho; exact hA a ho ha
    · rw [hne m hmn] at ho; exact h.outAns m a ho ha
  case ansLastStl =>
    intro m a hl
    rcases fr m with e | ⟨rfl, e⟩
    · rw [e] at hl; exact h.ansLastStl m a hl
    · rw [e] at hl; exact h.ansLastStl _ a hl
  case lastAnsStl => intro m sh a hl; rw [eRoll] at hl; exact h.lastAnsStl m sh a hl
  case unsent =>
    intro m mm ho ha p hp heq
    by_cases hmn : m = n
    · subst hmn; rw [hsame] at ho; exact hU mm ho ha p hp heq
    · rw [hne m hmn] at ho; exact h.unsent m mm ho ha p hp heq
  case compOK =>
    intro c hc
    obtain ⟨⟨k, k1, k2⟩, k3⟩ := h.compOK c hc
    refine ⟨⟨k, k1, by rw [eCtr]; exact k2⟩, ?_⟩
    rw [eRoll]; exact k3
  case compUniq => exact h.compUniq
  case agree => exact h.agree
  case d1 => intro m; simp only [eSk, eCur, eNxt]; exact h.d1 m
  case pp => simp only [eDers]; exact h.pp
  case qq =>
    intro m rq hrq c hc hcn hto
    rw [eRoll] at hrq
    rw [eChg]; exact h.qq m rq hrq c hc hcn hto
  case nxtFloor =>
    intro m x hx
    rw [eNxt] at hx
    rw [eCur]; exact h.nxtFloor m x hx

/-- A duplicate request is answered again: only the message waiting changes. -/
theorem inv_dup {P : Params} {S : Sys} {n : Bool} (h : Inv P S) (sh : T) (ans : Msg)
    (hl : (S.nd n).roll.last = some (sh, ans)) :
    Inv P (S.setNode n { S.nd n with out := some ans }) := by
  have ans_true := NodeInv.lastAns (h.node n) sh ans hl
  refine inv_setOut h (some ans) (S.nd n).reqAt ((h.node n).dupOut sh ans hl) ?_ ?_
  · intro a ha _; simp only [Option.some.injEq] at ha; subst ha; exact h.lastAnsStl n sh _ hl
  · intro a ha hq; simp only [Option.some.injEq] at ha; subst ha; rw [ans_true] at hq; simp at hq

end Pinc.KeyRollSys
