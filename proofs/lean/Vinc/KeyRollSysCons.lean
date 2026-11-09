import Vinc.KeyRollSysDeliver

namespace Vinc.KeyRollSys
open Vinc.KeyRoll

/-! ## Taking an answer (the requester switches its sending key) -/

theorem PP.comm {α : Type} {a b : List α} (h : PP a b) : PP b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem Inv.ppn {P : Params} {S : Sys} (h : Inv P S) (n : Bool) :
    PP ((S.nd n).ders.map Der.core) ((S.nd (!n)).ders.map Der.core) := by
  cases n with
  | false => exact h.pp
  | true => exact h.pp.comm

theorem Sys.pp_iff {S : Sys} (n : Bool) :
    PP ((S.nd n).ders.map Der.core) ((S.nd (!n)).ders.map Der.core) ↔
      PP ((S.nd false).ders.map Der.core) ((S.nd true).ders.map Der.core) := by
  cases n with
  | false => exact Iff.rfl
  | true => exact ⟨PP.comm, PP.comm⟩

theorem prefix_snoc_of_get {α : Type} {x y : List α} (hp : x <+: y) (a : α) (hg : y[x.length]? = some a) :
    (x ++ [a]) <+: y := by
  obtain ⟨t, rfl⟩ := hp
  cases t with
  | nil => simp at hg
  | cons b t =>
    simp at hg
    subst hg
    exact ⟨t, by simp⟩

theorem prefix_of_shorter {α : Type} {x y : List α} (h : PP x y) (hl : x.length ≤ y.length) : x <+: y := by
  rcases h with h | h
  · exact h
  · have := h.length_le
    have e : y = x := List.IsPrefix.eq_of_length h (by omega)
    rw [e]; exact List.prefix_refl x

theorem inv_consume {P : Params} {S : Sys} {n : Bool} (h : Inv P S) {p : Pkt} (hp : p ∈ S.net) (hsrc : p.src = !n)
    {m : Msg} (hpl : p.pl = some m) (hm : m.answer = true) (seed : Atom) (rq : Msg) (b : Atom)
    (hst : (S.nd n).roll.st = .req seed rq) (hsh : m.share = .pub b) (hto : m.to = rq.share) :
    Inv P { (S.setNode n ((S.nd n).consumed (S.nd n).roll.completed (Dh seed b) m.spn rq.share)) with
            comp := ⟨n, Dh seed b, m.gdh, m.to, rq.share⟩ :: S.comp } := by
  have hpend : (S.nd n).roll.pending = some rq := by simp [Roll.pending, hst]
  obtain ⟨c, hc, hcm, hcn⟩ := h.netAns p hp m hpl hm
  rw [hsrc] at hcn
  have hq := h.qq n rq hpend c hc hcn (by rw [hcm]; exact hto)
  obtain ⟨a1, a2, ⟨lv, a3⟩, a4, a5, a6, a7⟩ := h.stlOK c hc
  rw [hcn] at a2 a3 a4 a5 a6
  have hcm' : c.ans = m := hcm
  rw [hcm'] at a2 a3
  have hchg := (h.node n).pending_chg hpend
  obtain ⟨hps1, k0, hps2, hps3⟩ := (h.node n).pendSeed seed rq hst
  -- the answer was made for this request
  obtain ⟨kY, kYn, hkY1, hkY2, hkY3, hkY4⟩ := a2.ans hm
  simp only [Bool.not_not] at hkY3 hkY4
  have hb : b = atomOf (!n) kY := by rw [hsh] at hkY1; exact T.pub.inj hkY1
  have hdh : Dh seed b = m.gdh := by
    have hrq : rq.share = .pub seed := by rw [hps1]; rfl
    rw [hto, hrq] at hkY3
    have e1 := T.pub.inj hkY3
    rw [hkY4, e1, ← hb]
    exact Dh_comm _ _
  -- no request waits in the message slot
  have hnoreq : ∀ m', (S.nd n).out = some m' → m'.answer = true := by
    intro m' hm'
    by_cases hq' : m'.answer = true
    · exact hq'
    exfalso
    have hq'' : m'.answer = false := by simpa using hq'
    have hpd := (h.node n).outReq m' hm' hq''
    rw [hpend] at hpd
    have hmm : m' = rq := (Option.some.inj hpd).symm
    obtain ⟨p', hp', r, hr1, hr2, hr3⟩ := a7
    have hrm := (h.netMsg p' hp' r hr1).req hr2
    have hrr : r = Msg.req r.share := hrm.1
    have hmq : rq = Msg.req rq.share := by rw [hps1]; rfl
    have hreq : r = rq := by rw [hrr, hr3, hcm', hto, ← hmq]
    exact h.unsent n m' hm' hq'' p' hp' (by rw [hr1, hreq, hmm])
  have hnn := (h.node n).consumed seed rq b m.spn hst hnoreq
  generalize hs' : (S.nd n).consumed (S.nd n).roll.completed (Dh seed b) m.spn rq.share = s' at hnn ⊢
  have fr := fun m' => Sys.setNode_cases S n m' s'
  have hsame : (S.setNode n s').nd n = s' := Sys.setNode_same _ _ _
  have hne : ∀ m', m' ≠ n → (S.setNode n s').nd m' = S.nd m' := fun m' hm' => Sys.setNode_ne S n m' _ hm'
  have s'ctr : s'.ctr = (S.nd n).ctr := by rw [← hs']; rfl
  have s'ders : s'.ders = (S.nd n).ders ++ [⟨false, rq.share, Dh seed b, 0⟩] := by rw [← hs']; rfl
  have s'roll : s'.roll = (S.nd n).roll.completed := by rw [← hs']; rfl
  have s'sk : s'.sk = PK.new (.roll (S.nd n).sk.sec (Dh seed b)) ((S.nd n).sk.g + 1) := by rw [← hs']; rfl
  have s'cur : s'.cur = (S.nd n).cur := by rw [← hs']; rfl
  have s'nxt : s'.nxt = some ⟨PK.new (.roll (S.nd n).cur.sec (Dh seed b)) ((S.nd n).cur.g + 1), m.spn⟩ := by
    rw [← hs']; rfl
  have s'out : s'.out = (S.nd n).out := by rw [← hs']; rfl
  have s'npn : s'.npn = (S.nd n).npn := by rw [← hs']; rfl
  have s'pend : s'.roll.pending = none := by rw [s'roll]; simp [Roll.pending, Roll.completed]
  have s'last : s'.roll.last = none := by rw [s'roll]; simp [Roll.completed]
  have s'dial : s'.roll.dialer = (S.nd n).roll.dialer := by rw [s'roll]; simp [Roll.completed]
  have eCtr : ∀ m', ((S.setNode n s').nd m').ctr = (S.nd m').ctr := by
    intro m'; rcases fr m' with e | ⟨rfl, e⟩ <;> rw [e]; exact s'ctr
  have eCur : ∀ m', ((S.setNode n s').nd m').cur = (S.nd m').cur := by
    intro m'; rcases fr m' with e | ⟨rfl, e⟩ <;> rw [e]; exact s'cur
  have eNpn : ∀ m', ((S.setNode n s').nd m').npn = (S.nd m').npn := by
    intro m'; rcases fr m' with e | ⟨rfl, e⟩ <;> rw [e]; exact s'npn
  have eOut : ∀ m', ((S.setNode n s').nd m').out = (S.nd m').out := by
    intro m'; rcases fr m' with e | ⟨rfl, e⟩ <;> rw [e]; exact s'out
  have skMono : ∀ m', (S.nd m').sk.g ≤ ((S.setNode n s').nd m').sk.g := by
    intro m'; rcases fr m' with e | ⟨rfl, e⟩ <;> rw [e]
    · exact Nat.le_refl _
    · rw [s'sk]; exact Nat.le_succ _
  have lenS' : s'.ders.length = (S.nd n).ders.length + 1 := by rw [s'ders]; simp
  have chgS' : s'.chg = (S.nd n).chg + 1 := by simp [Node.chg, lenS']
  have hnx_Y : (S.nd (!n)).nxt.isSome = true := by
    have cY := (h.node (!n)).cn
    have hcY : (S.nd (!n)).chg ≥ c.pos + 1 := by
      have := (List.getElem?_eq_some_iff.1 a3).1
      simp only [Node.chg]; omega
    have d1n := h.d1 n
    by_cases hY : (S.nd (!n)).nxt.isSome = true
    · exact hY
    · have hY' : (S.nd (!n)).nxt.isSome = false := by simpa using hY
      have := cY.2.2.2.1 hY'
      omega
  have eqpos : (S.nd n).sk.g = (S.nd (!n)).cur.g := by
    have d1n := h.d1 n
    omega
  have eChgGe : ∀ m', (S.nd m').chg ≤ ((S.setNode n s').nd m').chg := by
    intro m'; rcases fr m' with e | ⟨rfl, e⟩ <;> rw [e]
    · exact Nat.le_refl _
    · omega
  have eChgNe : ∀ m', m' ≠ n → ((S.setNode n s').nd m').chg = (S.nd m').chg := by
    intro m' hm'; rw [hne m' hm']
  have app_get : ∀ (l : List Der) (i : Nat) (e d : Der), l[i]? = some e → (l ++ [d])[i]? = some e := by
    intro l i e d hl
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hl).1]; exact hl
  have hrq : rq.share = .pub (atomOf n k0) := by rw [hps1, ← hps2]; rfl
  inv_mk
  all_goals try dsimp only
  case node =>
    intro m'; rcases fr m' with e | ⟨rfl, e⟩
    · rw [e]; exact h.node m'
    · rw [e]; exact hnn
  case netPh => exact h.netPh
  case netDep =>
    intro q hq
    obtain ⟨a, b'⟩ := h.netDep q hq
    exact ⟨Nat.le_trans a (skMono _), by rw [eNpn]; exact b'⟩
  case netMsg => intro q hq mm hmm; rw [eCtr]; exact h.netMsg q hq mm hmm
  case netSlog => exact h.netSlog
  case netReq => exact h.netReq
  case netAns => exact h.netAns
  case slogOK =>
    intro x hx
    obtain ⟨b1, b2, b3, b4⟩ := h.slogOK x hx
    exact ⟨by rw [eNpn]; exact b1, b2, Nat.le_trans b3 (skMono _), b4⟩
  case slogOrd => exact h.slogOrd
  case slogUniq => exact h.slogUniq
  case breqOK =>
    intro b0 hb0
    obtain ⟨⟨k, k1, k2⟩, b2, b3⟩ := h.breqOK b0 hb0
    refine ⟨⟨k, k1, by rw [eCtr]; exact k2⟩, Nat.le_trans b2 (eChgGe _), ?_⟩
    intro hc
    by_cases hbn : b0.n = n
    · exfalso
      rw [hbn, hsame, chgS'] at hc
      rw [hbn] at b2
      omega
    · rw [hne _ hbn] at hc ⊢; exact b3 hc
  case breqPend =>
    intro m' rq' hp'
    rcases fr m' with e | ⟨rfl, e⟩
    · rw [e] at hp'
      obtain ⟨j, hj, hc⟩ := h.breqPend m' rq' hp'
      exact ⟨j, hj, by rw [e]; exact hc⟩
    · rw [e, s'pend] at hp'; simp at hp'
  case breqFun => exact h.breqFun
  case breqF3 =>
    intro b0 hb0 hd hj
    by_cases hbn : b0.n = n
    · rw [hbn, hsame, s'dial] at hd
      rw [hbn, hsame, chgS'] at hj
      rw [hbn, hsame, s'ders]
      by_cases hlt : b0.j < (S.nd n).chg
      · obtain ⟨e, he1, he2, he3⟩ := h.breqF3 b0 hb0 (by rw [hbn]; exact hd) (by rw [hbn]; exact hlt)
        rw [hbn] at he1
        exact ⟨e, app_get _ _ _ _ he1, he2, he3⟩
      · have hjc : b0.j = (S.nd n).chg := by omega
        have := (h.breqOK b0 hb0).2.2 (by rw [hbn]; exact hjc.symm)
        rw [hbn, hpend] at this
        simp at this
        refine ⟨⟨false, rq.share, Dh seed b, 0⟩, ?_, rfl, ?_⟩
        · rw [hjc]; simp [Node.chg]
        · exact this
    · rw [hne _ hbn] at hd hj ⊢; exact h.breqF3 b0 hb0 hd hj
  case derBreq =>
    intro m' q e he hs
    rcases fr m' with e' | ⟨rfl, e'⟩
    · rw [e'] at he; exact h.derBreq m' q e he hs
    · rw [e', s'ders] at he
      by_cases hq : q < (S.nd m').ders.length
      · rw [List.getElem?_append_left hq] at he; exact h.derBreq m' q e he hs
      · rw [List.getElem?_append_right (by omega)] at he
        by_cases hq0 : q - (S.nd m').ders.length = 0
        · simp [hq0] at he; subst he; simp at hs
        · simp [List.getElem?_eq_none (show [(⟨false, rq.share, Dh seed b, 0⟩ : Der)].length ≤ q - (S.nd m').ders.length by
            simp; omega)] at he
  case stlOK =>
    intro c' hc'
    obtain ⟨a1', a2', ⟨lv', a3'⟩, a4', a5', a6', a7'⟩ := h.stlOK c' hc'
    refine ⟨a1', by rw [eCtr]; exact a2', ⟨lv', ?_⟩, by rw [eCur]; exact a4', by rw [eNpn]; exact a5', a6', a7'⟩
    rcases fr c'.n with e' | ⟨e0, e'⟩
    · rw [e']; exact a3'
    · rw [e', s'ders]; rw [e0] at a3'; exact app_get _ _ _ _ a3'
  case outAns => intro m' a ho ha; rw [eOut] at ho; exact h.outAns m' a ho ha
  case lastAnsStl =>
    intro m' sh a hl
    rcases fr m' with e | ⟨rfl, e⟩
    · rw [e] at hl; exact h.lastAnsStl m' sh a hl
    · rw [e, s'last] at hl; simp at hl
  case unsent => intro m' mm ho ha; rw [eOut] at ho; exact h.unsent m' mm ho ha
  case compOK =>
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · refine ⟨⟨k0, hrq, ?_⟩, ?_⟩
      · rw [eCtr]; exact hps3
      · simp only [hsame, s'pend]; simp
    · obtain ⟨⟨k, k1, k2⟩, k3⟩ := h.compOK c' hc'
      refine ⟨⟨k, k1, by rw [eCtr]; exact k2⟩, ?_⟩
      by_cases hcn' : c'.n = n
      · rw [hcn', hsame, s'pend]; simp
      · rw [hne _ hcn']; exact k3
  case compUniq =>
    intro c1 h1 c2 h2 heq
    rcases List.mem_cons.1 h1 with rfl | h1 <;> rcases List.mem_cons.1 h2 with rfl | h2
    · rfl
    · exfalso
      obtain ⟨⟨k, k1, k2⟩, k3⟩ := h.compOK c2 h2
      simp only at heq
      have e1 : c2.req = rq.share := heq.symm
      rw [e1, hrq] at k1
      have := (pub_atom_inj k1).1
      apply k3
      rw [← this, hpend]; simp [e1]
    · exfalso
      obtain ⟨⟨k, k1, k2⟩, k3⟩ := h.compOK c1 h1
      simp only at heq
      rw [heq, hrq] at k1
      have := (pub_atom_inj k1).1
      apply k3
      rw [← this, hpend]; simp [heq]
    · exact h.compUniq c1 h1 c2 h2 heq
  case agree =>
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact hdh
    · exact h.agree c' hc'
  case d1 =>
    intro X
    rcases Bool.eq_or_not X n with hX | hX
    · subst hX
      have d1n := h.d1 X
      have hnY : (S.setNode X s').nd (!X) = S.nd (!X) := Sys.setNode_not S X s'
      rw [hnY, hsame, s'sk]
      simp only [PK.new]
      exact ⟨by omega, by omega, fun _ => hnx_Y⟩
    · have hXn : X = !n := hX
      subst hXn
      have d1b := h.d1 (!n)
      rw [Bool.not_not] at d1b ⊢
      have hnY : (S.setNode n s').nd (!n) = S.nd (!n) := Sys.setNode_not S n s'
      rw [hnY, hsame, s'cur]
      refine ⟨d1b.1, d1b.2.1, fun _ => ?_⟩
      rw [s'nxt]; rfl
  case pp =>
    refine (Sys.pp_iff n).1 ?_
    have hnY : (S.setNode n s').nd (!n) = S.nd (!n) := Sys.setNode_not S n s'
    rw [hnY, hsame, s'ders]
    have hpp := h.ppn n
    have hlen : ((S.nd n).ders.map Der.core).length ≤ ((S.nd (!n)).ders.map Der.core).length := by
      have := (List.getElem?_eq_some_iff.1 a3).1
      simp only [List.length_map, Node.chg] at hq ⊢
      omega
    have hpre := prefix_of_shorter hpp hlen
    have hget : ((S.nd (!n)).ders.map Der.core)[((S.nd n).ders.map Der.core).length]? = some (rq.share, Dh seed b) := by
      have : ((S.nd n).ders.map Der.core).length = c.pos := by simp [hq, Node.chg]
      rw [this, List.getElem?_map, a3]
      simp [Der.core, hto, hdh]
    have := prefix_snoc_of_get hpre _ hget
    left
    simpa [Der.core] using this
  case qq =>
    intro m' rq' hrq' c' hc' hcn' hto'
    rcases fr m' with e | ⟨rfl, e⟩
    · rw [e] at hrq' ⊢; exact h.qq m' rq' hrq' c' hc' hcn' hto'
    · rw [e, s'pend] at hrq'; simp at hrq'
  case nxtFloor =>
    intro m' x hx
    rcases fr m' with e | ⟨rfl, e⟩
    · rw [e] at hx ⊢; exact h.nxtFloor m' x hx
    · rw [e, s'nxt] at hx
      simp only [Option.some.injEq] at hx
      subst hx
      refine Or.inr ⟨c, hc, hcn, ?_, ?_⟩
      · rw [e, s'cur, hq]; exact hchg.2
      · simp [hcm']

end Vinc.KeyRollSys
