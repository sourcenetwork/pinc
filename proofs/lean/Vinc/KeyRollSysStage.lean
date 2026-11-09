import Vinc.KeyRollSysCons

namespace Vinc.KeyRollSys
open Vinc.KeyRoll

/-! ## Answering a request (the answerer stages new keys)

The heart of agreement: a node never stages a roll at a position the other node has already filled. -/

theorem own_excl {n : Bool} {t : T} (h1 : own n t) (h2 : own (!n) t) : False := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨k', hk'⟩ := h2
  have := (pub_atom_inj (hk.symm.trans hk')).1
  cases n <;> simp at this

theorem prefix_get {α : Type} {x y : List α} (hp : x <+: y) {i : Nat} (hi : i < x.length) : x[i]? = y[i]? := by
  obtain ⟨t, rfl⟩ := hp
  rw [List.getElem?_append_left hi]

theorem ders_core_get {x y : List Der} (hp : (x.map Der.core) <+: (y.map Der.core)) {i : Nat} (hi : i < x.length)
    {e : Der} (he : x[i]? = some e) : ∃ e', y[i]? = some e' ∧ e'.core = e.core := by
  have := prefix_get hp (i := i) (by simpa using hi)
  rw [List.getElem?_map, List.getElem?_map, he] at this
  cases hy : y[i]? with
  | none => simp [hy] at this
  | some e' => rw [hy] at this; exact ⟨e', rfl, by simpa using this.symm⟩

theorem ders_core_get' {x y : List Der} (hp : (x.map Der.core) <+: (y.map Der.core)) {i : Nat} (hi : i < x.length)
    {e : Der} (he : y[i]? = some e) : ∃ e', x[i]? = some e' ∧ e'.core = e.core := by
  have := prefix_get hp (i := i) (by simpa using hi)
  rw [List.getElem?_map, List.getElem?_map, he] at this
  cases hx : x[i]? with
  | none => simp [hx] at this
  | some e' => rw [hx] at this; exact ⟨e', rfl, by simpa using this⟩

theorem pending_not_idle (r : Roll) {m : Msg} (h : r.pending = some m) : r.isIdle = false := by
  unfold Roll.pending at h
  cases hst : r.st with
  | idle => simp [hst] at h
  | req sd rq => simp [Roll.isIdle, hst]

theorem getLast?_idx {α : Type} {l : List α} {e : α} (h : l.getLast? = some e) : l[l.length - 1]? = some e := by
  rw [← List.getLast?_eq_getElem?]; exact h

/-- The node that stages a roll is never behind the number of derivations of the other node. -/
theorem stage_chg_le {P : Params} {S : Sys} {n : Bool} (h : Inv P S) {p : Pkt} (hp : p ∈ S.net) (hsrc : p.src = !n)
    {m : Msg} (hpl : p.pl = some m) (hm : m.answer = false) (hnx : (S.nd n).nxt = none)
    (hn : (S.nd n).roll.isDup m = false) (hc : (!(S.nd n).roll.isIdle && (S.nd n).roll.dialer) = false)
    (hdep : p.sec.depth = (S.nd n).cur.g ∨ p.sec.depth + 1 = (S.nd n).cur.g) :
    (S.nd (!n)).chg ≤ (S.nd n).chg := by
  by_cases hle : (S.nd (!n)).chg ≤ (S.nd n).chg
  · exact hle
  exfalso
  have hlt : (S.nd n).chg < (S.nd (!n)).chg := Nat.lt_of_not_le hle
  have cn := (h.node n).cn
  have cY := (h.node (!n)).cn
  have hnxs : (S.nd n).nxt.isSome = false := by simp [hnx]
  have hc0 := cn.2.2.2.1 hnxs
  have d1Y := h.d1 (!n)
  rw [Bool.not_not] at d1Y
  have hskY : (S.nd (!n)).sk.g = (S.nd n).chg := by
    have : ¬ ((S.nd (!n)).sk.g = (S.nd n).cur.g + 1) := fun hh => by
      have := d1Y.2.2 hh; simp [hnx] at this
    omega
  have hstgY : (S.nd (!n)).stg.isSome = true := by
    by_cases hh : (S.nd (!n)).stg.isSome = true
    · exact hh
    · have hh' : (S.nd (!n)).stg.isSome = false := by simpa using hh
      have := cY.2.1 hh'
      omega
  have hchgY : (S.nd (!n)).chg = (S.nd n).chg + 1 := by have := cY.1 hstgY; omega
  -- the last derivation of the other node is the staging of an answer
  obtain ⟨e, he1, he2⟩ := (h.node (!n)).stgLast hstgY
  have eP : (S.nd (!n)).ders[(S.nd n).chg]? = some e := by
    have := getLast?_idx he1
    have hl : (S.nd (!n)).ders.length - 1 = (S.nd n).chg := by simp [Node.chg] at hchgY ⊢; omega
    rw [hl] at this; exact this
  have eOwn := (h.node (!n)).derOK e (List.mem_of_getElem? eP)
  rw [Bool.not_not] at eOwn
  have eOwn' : own n e.rid := by
    rcases eOwn with ⟨_, hh⟩ | ⟨hh, _⟩
    · exact hh
    · rw [he2] at hh; simp at hh
  have eBr := h.derBreq (!n) _ e eP he2
  rw [Bool.not_not] at eBr
  have eLvl := (h.node (!n)).derLvl _ e eP he2
  have hppn := h.ppn n
  have hlenle : ((S.nd n).ders.map Der.core).length ≤ ((S.nd (!n)).ders.map Der.core).length := by
    simp only [List.length_map]; simp [Node.chg] at hlt ⊢; omega
  have hpre := prefix_of_shorter hppn hlenle
  have hdial : (S.nd n).roll.dialer = !n := (h.node n).dialer
  have hdialY : (S.nd (!n)).roll.dialer = !!n := (h.node (!n)).dialer
  rw [Bool.not_not] at hdialY
  by_cases hYd : (S.nd (!n)).roll.dialer = true
  · -- the other node is the dialer: the request it sent is one of its own, answered earlier
    obtain ⟨j, hj, hjd⟩ := h.netReq p hp m hpl hm
    rw [hsrc] at hj
    have hjp : j ≤ (S.nd n).chg := by
      have := (h.netDep p hp).1
      rw [hsrc, hjd] at this; omega
    have hmok := h.netMsg p hp m hpl
    rw [hsrc] at hmok
    obtain ⟨_, kY, hkY, _⟩ := hmok.req hm
    obtain ⟨e', he'1, he'2, he'3⟩ := h.breqF3 ⟨!n, m.share, j⟩ hj hYd (by simp only; omega)
    simp only at he'1 he'2 he'3
    have hjw : j = (S.nd n).chg ∨ j + 1 = (S.nd n).chg := by omega
    rcases hjw with hjc | hjc
    · rw [hjc] at he'1
      rw [eP] at he'1
      have := Option.some.inj he'1
      rw [← this, he2] at he'2; simp at he'2
    · -- the request was answered at position j, the last position of this node
      have hjl : j < ((S.nd n).ders.map Der.core).length := by simp [Node.chg] at hjc ⊢; omega
      obtain ⟨e'', he''1, he''2⟩ := ders_core_get' hpre (by simpa using hjl) he'1
      have hrid : e''.rid = m.share := by
        have := congrArg Prod.fst he''2
        simp only [Der.core] at this; rw [this, he'3]
      have hmem := (h.node n).derOK e'' (List.mem_of_getElem? he''1)
      have hstgs : e''.stg = true := by
        rcases hmem with ⟨hh, _⟩ | ⟨hh, ho⟩
        · exact hh
        · exfalso
          apply own_excl (n := n) (t := e''.rid) ho
          rw [hrid]; exact ⟨kY, hkY⟩
      have hlast : (S.nd n).ders.getLast? = some e'' := by
        rw [List.getLast?_eq_getElem?]
        have : (S.nd n).ders.length - 1 = j := by simp [Node.chg] at hjc; omega
        rw [this]; exact he''1
      have hli := (h.node n).lastInv
      have : (S.nd n).lastRid = some e''.rid := by simp [Node.lastRid, hlast, hstgs]
      rw [this, hrid] at hli
      have hdup : ∃ a, (S.nd n).roll.last = some (m.share, a) := by
        cases hl : (S.nd n).roll.last with
        | none => rw [hl] at hli; simp at hli
        | some y =>
          obtain ⟨y1, y2⟩ := y
          rw [hl] at hli
          simp at hli
          exact ⟨y2, by rw [hli]⟩
      exact absurd ((isDup_iff _ _).2 hdup) (by simp [hn])
  · -- the other node is the acceptor, this node is the dialer
    have hnn : n = false := by
      cases n with
      | false => rfl
      | true => rw [hdialY] at hYd; simp at hYd
    have hnd : (S.nd n).roll.dialer = true := by rw [hdial, hnn]; rfl
    have hidle : (S.nd n).roll.isIdle = true := by
      have : (!(S.nd n).roll.isIdle) = false := by simpa [hnd] using hc
      simpa using this
    rcases eLvl with hl | hl
    · -- the request it answered is still pending here: the dialer ignores requests
      have := (h.breqOK _ eBr).2.2
      simp only at this
      have hp0 := this (by omega)
      simp at hp0
      cases hpd : (S.nd n).roll.pending with
      | none => rw [hpd] at hp0; simp at hp0
      | some rq' => rw [pending_not_idle _ hpd] at hidle; simp at hidle
    · -- it was a roll of this node, finished at position lvl: answered twice
      obtain ⟨e', he'1, he'2, he'3⟩ := h.breqF3 ⟨n, e.rid, e.lvl⟩ eBr hnd (by simp only; omega)
      simp only at he'1 he'2 he'3
      have hil : e.lvl < ((S.nd n).ders.map Der.core).length := by simp [Node.chg] at hl ⊢; omega
      obtain ⟨e2, he2a, he2b⟩ := ders_core_get hpre (by simpa using hil) he'1
      have hrid2 : e2.rid = e.rid := by
        have := congrArg Prod.fst he2b
        simp only [Der.core] at this; rw [this, he'3]
      have hmem := (h.node (!n)).derOK e2 (List.mem_of_getElem? he2a)
      rw [Bool.not_not] at hmem
      have hstg2 : e2.stg = true := by
        rcases hmem with ⟨hh, _⟩ | ⟨hh, ho⟩
        · exact hh
        · exfalso
          apply own_excl (n := n) (t := e.rid) eOwn'
          rw [← hrid2]; exact ho
      have hnext : (S.nd (!n)).ders[e.lvl + 1]? = some e := by rw [hl]; exact eP
      exact (h.node (!n)).noDup e.lvl e2 e he2a hnext hstg2 he2 (by rw [hrid2])

theorem inv_stage {P : Params} {S : Sys} {n : Bool} (h : Inv P S) {p : Pkt} (hp : p ∈ S.net) (hsrc : p.src = !n)
    {m : Msg} (hpl : p.pl = some m) (hm : m.answer = false) (b : Atom) (hsh : m.share = .pub b)
    (hg : gated P (S.nd n) m = false) (hn : (S.nd n).roll.isDup m = false)
    (hc : (!(S.nd n).roll.isIdle && (S.nd n).roll.dialer) = false)
    (hdep : p.sec.depth = (S.nd n).cur.g ∨ p.sec.depth + 1 = (S.nd n).cur.g) :
    Inv P { (S.setNode n ((S.nd n).staged ((S.nd n).roll.answeredWith m.share
        (answerTo n (S.nd n).ctr (S.nd n).npn m.share b))
        (answerTo n (S.nd n).ctr (S.nd n).npn m.share b) (Dh (atomOf n (S.nd n).ctr) b) m.share p.sec.depth)) with
        stl := ⟨n, answerTo n (S.nd n).ctr (S.nd n).npn m.share b, (S.nd n).ders.length⟩ :: S.stl } := by
  have hnx : (S.nd n).nxt = none := gated_nodup P _ m hm hn hg
  have cn := (h.node n).cn
  have hstg : (S.nd n).stg = none := by
    cases hs : (S.nd n).stg with
    | none => rfl
    | some k => have := cn.2.2.2.2 (by simp [hs]); simp [hnx] at this
  have hnxs : (S.nd n).nxt.isSome = false := by simp [hnx]
  have hstgs : (S.nd n).stg.isSome = false := by simp [hstg]
  have hc1 := cn.2.1 hstgs
  have hc2 := cn.2.2.2.1 hnxs
  have hc1' : (S.nd n).ders.length = (S.nd n).sk.g := by simpa [Node.chg] using hc1
  have hc2' : (S.nd n).ders.length = (S.nd n).cur.g := by simpa [Node.chg] using hc2
  have hmok := h.netMsg p hp m hpl
  rw [hsrc] at hmok
  have hlvl : p.sec.depth = (S.nd n).ders.length ∨ p.sec.depth + 1 = (S.nd n).ders.length := by
    simp only [Node.chg] at hc2; omega
  have hnn := (h.node n).staged m p.sec.depth b hmok hm hsh hnx hn hlvl
  have hchgle := stage_chg_le h hp hsrc hpl hm hnx hn hc hdep
  have ans_to : (answerTo n (S.nd n).ctr (S.nd n).npn m.share b).to = m.share := rfl
  have ans_ans : (answerTo n (S.nd n).ctr (S.nd n).npn m.share b).answer = true := rfl
  have ans_spn : (answerTo n (S.nd n).ctr (S.nd n).npn m.share b).spn = (S.nd n).npn := rfl
  have ans_gdh : (answerTo n (S.nd n).ctr (S.nd n).npn m.share b).gdh = Dh (atomOf n (S.nd n).ctr) b := rfl
  generalize hA : answerTo n (S.nd n).ctr (S.nd n).npn m.share b = ans at *
  generalize hs' : (S.nd n).staged ((S.nd n).roll.answeredWith m.share ans) ans (Dh (atomOf n (S.nd n).ctr) b) m.share
    p.sec.depth = s' at hnn ⊢
  have fr := fun m' => Sys.setNode_cases S n m' s'
  have hsame : (S.setNode n s').nd n = s' := Sys.setNode_same _ _ _
  have hne : ∀ m', m' ≠ n → (S.setNode n s').nd m' = S.nd m' := fun m' hm' => Sys.setNode_ne S n m' _ hm'
  have hnY : (S.setNode n s').nd (!n) = S.nd (!n) := Sys.setNode_not S n s'
  have s'ctr : s'.ctr = (S.nd n).ctr + 1 := by rw [← hs']; rfl
  have s'ders : s'.ders = (S.nd n).ders ++ [⟨true, m.share, Dh (atomOf n (S.nd n).ctr) b, p.sec.depth⟩] := by
    rw [← hs']; rfl
  have s'roll : s'.roll = (S.nd n).roll.answeredWith m.share ans := by rw [← hs']; rfl
  have s'sk : s'.sk = (S.nd n).sk := by rw [← hs']; rfl
  have s'cur : s'.cur = (S.nd n).cur := by rw [← hs']; rfl
  have s'nxt : s'.nxt.isSome = true := by rw [← hs']; rfl
  have s'nxt' : s'.nxt = some ⟨PK.new (.roll (S.nd n).cur.sec (Dh (atomOf n (S.nd n).ctr) b)) ((S.nd n).cur.g + 1), 0⟩ := by
    rw [← hs']; rfl
  have s'out : s'.out = some ans := by rw [← hs']; rfl
  have s'npn : s'.npn = (S.nd n).npn := by rw [← hs']; rfl
  have s'pend : s'.roll.pending = none := by rw [s'roll]; simp [Roll.pending, Roll.answeredWith]
  have s'last : s'.roll.last = some (m.share, ans) := by rw [s'roll]; simp [Roll.answeredWith]
  have s'dial : s'.roll.dialer = (S.nd n).roll.dialer := by rw [s'roll]; simp [Roll.answeredWith]
  have lenS' : s'.ders.length = (S.nd n).ders.length + 1 := by rw [s'ders]; simp
  have chgS' : s'.chg = (S.nd n).chg + 1 := by simp [Node.chg, lenS']
  have eCtr : ∀ m', (S.nd m').ctr ≤ ((S.setNode n s').nd m').ctr := by
    intro m'; rcases fr m' with e | ⟨rfl, e⟩ <;> rw [e]
    · exact Nat.le_refl _
    · rw [s'ctr]; exact Nat.le_succ _
  have eSk : ∀ m', ((S.setNode n s').nd m').sk = (S.nd m').sk := by
    intro m'; rcases fr m' with e | ⟨rfl, e⟩ <;> rw [e]; exact s'sk
  have eCur : ∀ m', ((S.setNode n s').nd m').cur = (S.nd m').cur := by
    intro m'; rcases fr m' with e | ⟨rfl, e⟩ <;> rw [e]; exact s'cur
  have eNpn : ∀ m', ((S.setNode n s').nd m').npn = (S.nd m').npn := by
    intro m'; rcases fr m' with e | ⟨rfl, e⟩ <;> rw [e]; exact s'npn
  have eChgGe : ∀ m', (S.nd m').chg ≤ ((S.setNode n s').nd m').chg := by
    intro m'; rcases fr m' with e | ⟨rfl, e⟩ <;> rw [e]
    · exact Nat.le_refl _
    · omega
  have app_get : ∀ (l : List Der) (i : Nat) (e d : Der), l[i]? = some e → (l ++ [d])[i]? = some e := by
    intro l i e d hl
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hl).1]; exact hl
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
    exact ⟨by rw [eSk]; exact a, by rw [eNpn]; exact b'⟩
  case netMsg => intro q hq mm hmm; exact (h.netMsg q hq mm hmm).mono (eCtr _)
  case netSlog => exact h.netSlog
  case netReq => exact h.netReq
  case netAns =>
    intro q hq mm hmm ha
    obtain ⟨c', hc', e1, e2⟩ := h.netAns q hq mm hmm ha
    exact ⟨c', List.mem_cons_of_mem _ hc', e1, e2⟩
  case slogOK =>
    intro x hx
    obtain ⟨b1, b2, b3, b4⟩ := h.slogOK x hx
    exact ⟨by rw [eNpn]; exact b1, b2, by rw [eSk]; exact b3, b4⟩
  case slogOrd => exact h.slogOrd
  case slogUniq => exact h.slogUniq
  case breqOK =>
    intro b0 hb0
    obtain ⟨⟨k, k1, k2⟩, b2, b3⟩ := h.breqOK b0 hb0
    refine ⟨⟨k, k1, Nat.lt_of_lt_of_le k2 (eCtr _)⟩, Nat.le_trans b2 (eChgGe _), ?_⟩
    intro hc'
    by_cases hbn : b0.n = n
    · exfalso
      rw [hbn, hsame, chgS'] at hc'
      rw [hbn] at b2
      omega
    · rw [hne _ hbn] at hc' ⊢; exact b3 hc'
  case breqPend =>
    intro m' rq' hp'
    rcases fr m' with e | ⟨rfl, e⟩
    · rw [e] at hp'
      obtain ⟨j, hj, hc'⟩ := h.breqPend m' rq' hp'
      exact ⟨j, hj, by rw [e]; exact hc'⟩
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
      · exfalso
        have hjc : b0.j = (S.nd n).chg := by omega
        have := (h.breqOK b0 hb0).2.2 (by rw [hbn]; exact hjc.symm)
        rw [hbn] at this
        cases hpd : (S.nd n).roll.pending with
        | none => rw [hpd] at this; simp at this
        | some rq' =>
          have hid := pending_not_idle _ hpd
          rw [hid, hd] at hc; simp at hc
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
        · simp [hq0] at he; subst he
          obtain ⟨j, hj, hjd⟩ := h.netReq p hp m hpl hm
          rw [hsrc] at hj
          rw [← hjd] at hj
          exact hj
        · simp [List.getElem?_eq_none (show [(⟨true, m.share, Dh (atomOf m' (S.nd m').ctr) b, p.sec.depth⟩ : Der)].length ≤
            q - (S.nd m').ders.length by simp; omega)] at he
  case stlOK =>
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · refine ⟨ans_ans, ?_, ⟨p.sec.depth, ?_⟩, ?_, ?_, ?_, p, hp, m, hpl, hm, ?_⟩
      · simp only [hsame]; exact hnn.outMsg ans s'out
      · simp only [hsame, s'ders, ans_to, ans_gdh]
        rw [List.getElem?_append_right (Nat.le_refl _)]; simp
      · simp only [hsame, s'cur]; exact Nat.le_of_eq hc2'
      · simp only [hsame, s'npn, ans_spn]; exact Nat.le_refl _
      · intro x hx hxn hpos
        exfalso
        have hxg := (h.slogOK x hx).2.2.1
        rw [hxn] at hxg
        simp only at hpos hxn hxg
        omega
      · exact ans_to.symm
    · obtain ⟨a1', a2', ⟨lv', a3'⟩, a4', a5', a6', a7'⟩ := h.stlOK c' hc'
      refine ⟨a1', a2'.mono (eCtr _), ⟨lv', ?_⟩, by rw [eCur]; exact a4', by rw [eNpn]; exact a5', a6', a7'⟩
      rcases fr c'.n with e' | ⟨e0, e'⟩
      · rw [e']; exact a3'
      · rw [e', s'ders]; rw [e0] at a3'; exact app_get _ _ _ _ a3'
  case outAns =>
    intro m' a ho ha
    by_cases hmn : m' = n
    · subst hmn
      rw [hsame, s'out] at ho
      simp only [Option.some.injEq] at ho
      subst ho
      exact ⟨_, List.mem_cons_self .., rfl, rfl⟩
    · rw [hne m' hmn] at ho
      obtain ⟨c', hc', e1, e2⟩ := h.outAns m' a ho ha
      exact ⟨c', List.mem_cons_of_mem _ hc', e1, e2⟩
  case lastAnsStl =>
    intro m' sh a hl
    rcases fr m' with e | ⟨rfl, e⟩
    · rw [e] at hl
      obtain ⟨c', hc', e1, e2⟩ := h.lastAnsStl m' sh a hl
      exact ⟨c', List.mem_cons_of_mem _ hc', e1, e2⟩
    · rw [e, s'last] at hl
      simp only [Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨_, rfl⟩ := hl
      exact ⟨_, List.mem_cons_self .., rfl, rfl⟩
  case unsent =>
    intro m' mm ho ha q hq heq
    by_cases hmn : m' = n
    · subst hmn
      rw [hsame, s'out] at ho
      simp only [Option.some.injEq] at ho
      subst ho
      rw [ans_ans] at ha; simp at ha
    · rw [hne m' hmn] at ho
      exact h.unsent m' mm ho ha q hq heq
  case compOK =>
    intro c' hc'
    obtain ⟨⟨k, k1, k2⟩, k3⟩ := h.compOK c' hc'
    refine ⟨⟨k, k1, Nat.lt_of_lt_of_le k2 (eCtr _)⟩, ?_⟩
    by_cases hcn' : c'.n = n
    · rw [hcn', hsame, s'pend]; simp
    · rw [hne _ hcn']; exact k3
  case compUniq => exact h.compUniq
  case agree => exact h.agree
  case d1 =>
    intro X
    have d1X := h.d1 X
    simp only [eSk, eCur]
    refine ⟨d1X.1, d1X.2.1, fun hh => ?_⟩
    have := d1X.2.2 hh
    rcases fr (!X) with e | ⟨e0, e⟩
    · rw [e]; exact this
    · rw [e]; exact s'nxt
  case pp =>
    refine (Sys.pp_iff n).1 ?_
    rw [hnY, hsame, s'ders]
    right
    have hlen : ((S.nd (!n)).ders.map Der.core).length ≤ ((S.nd n).ders.map Der.core).length := by
      simp only [List.length_map]; exact hchgle
    have hpre : ((S.nd (!n)).ders.map Der.core) <+: ((S.nd n).ders.map Der.core) := by
      rcases (h.ppn n).comm with hh | hh
      · exact hh
      · have := hh.length_le
        have e : (S.nd n).ders.map Der.core = (S.nd (!n)).ders.map Der.core :=
          List.IsPrefix.eq_of_length hh (by omega)
        rw [e]; exact List.prefix_refl _
    obtain ⟨t, ht⟩ := hpre
    exact ⟨t ++ [Der.core ⟨true, m.share, Dh (atomOf n (S.nd n).ctr) b, p.sec.depth⟩], by
      rw [List.map_append, ← ht, List.append_assoc]; rfl⟩
  case qq =>
    intro m' rq' hrq' c' hc' hcn' hto'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · -- the new staging answers the request of the other node, which is pending there
      have hm'n : m' = !n := by
        simp only at hcn'
        rw [hcn', Bool.not_not]
      subst hm'n
      rw [hnY] at hrq' ⊢
      have hcc := (h.node (!n)).pending_chg hrq'
      have d1Y := h.d1 (!n)
      rw [Bool.not_not] at d1Y
      have : ¬ ((S.nd (!n)).sk.g = (S.nd n).cur.g + 1) := fun hh => by
        have := d1Y.2.2 hh; simp [hnx] at this
      simp only
      omega
    · rcases fr m' with e | ⟨rfl, e⟩
      · rw [e] at hrq' ⊢; exact h.qq m' rq' hrq' c' hc' hcn' hto'
      · rw [e, s'pend] at hrq'; simp at hrq'
  case nxtFloor =>
    intro m' x hx
    rcases fr m' with e | ⟨rfl, e⟩
    · rw [e] at hx ⊢
      rcases h.nxtFloor m' x hx with h0 | ⟨c', hc', e1, e2, e3⟩
      · exact Or.inl h0
      · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', e1, e2, e3⟩
    · rw [e, s'nxt'] at hx
      simp only [Option.some.injEq] at hx
      subst hx
      exact Or.inl rfl

end Vinc.KeyRollSys
