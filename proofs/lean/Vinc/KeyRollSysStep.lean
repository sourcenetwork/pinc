import Vinc.KeyRollSysGlobal

namespace Vinc.KeyRollSys
open Vinc.KeyRoll

/-! ## Time and `Begin` keep the invariant -/

/-- Close a field of `Inv` from the same field of the hypothesis. -/
macro "inv_close " h:ident : tactic => `(tactic| first | (have t := Inv.node $h; exact t) | (have t := Inv.netPh $h; exact t) | (have t := Inv.netDep $h; exact t) | (have t := Inv.netMsg $h; exact t) | (have t := Inv.netSlog $h; exact t) | (have t := Inv.netReq $h; exact t) | (have t := Inv.netAns $h; exact t) | (have t := Inv.slogOK $h; exact t) | (have t := Inv.slogOrd $h; exact t) | (have t := Inv.slogUniq $h; exact t) | (have t := Inv.breqOK $h; exact t) | (have t := Inv.breqPend $h; exact t) | (have t := Inv.breqFun $h; exact t) | (have t := Inv.breqF3 $h; exact t) | (have t := Inv.derBreq $h; exact t) | (have t := Inv.stlOK $h; exact t) | (have t := Inv.outAns $h; exact t) | (have t := Inv.lastAnsStl $h; exact t) | (have t := Inv.unsent $h; exact t) | (have t := Inv.compOK $h; exact t) | (have t := Inv.compUniq $h; exact t) | (have t := Inv.agree $h; exact t) | (have t := Inv.d1 $h; exact t) | (have t := Inv.pp $h; exact t) | (have t := Inv.qq $h; exact t) | (have t := Inv.nxtFloor $h; exact t) | (have t := Inv.ansLastStl $h; exact t))

/-- `Inv` is unchanged by a step that changes none of the things it reads. -/
macro "inv_same " h:ident : tactic => `(tactic| (inv_mk <;> inv_close $h))

theorem inv_tick {P : Params} {S : Sys} (h : Inv P S) : Inv P (tickUpd S) := by
  inv_same h

theorem beginOk_spec {P : Params} {S : Sys} {n : Bool} (h : beginOk P S n = true) :
    (S.nd n).stg = none ∧ (S.nd n).nxt = none ∧ (S.nd n).roll.isIdle = true := by
  simp only [beginOk, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

/-- The node after `Begin`. -/
def beginNode (s : Node) (n : Bool) : Node :=
  { s with roll := { s.roll with st := .req (atomOf n s.ctr) (Msg.req (.pub (atomOf n s.ctr))) },
           out := some (Msg.req (.pub (atomOf n s.ctr))), reqAt := none, ctr := s.ctr + 1 }

theorem beginUpd_eq {P : Params} {S : Sys} {n : Bool} (h : beginOk P S n = true) :
    beginUpd S n = { (S.setNode n (beginNode (S.nd n) n)) with
        breq := ⟨n, .pub (atomOf n (S.nd n).ctr), (S.nd n).chg⟩ :: S.breq } := by
  obtain ⟨_, _, hid⟩ := beginOk_spec h
  have := start_spec (S.nd n).roll (atomOf n (S.nd n).ctr) hid
  simp only [beginUpd, this.1, this.2, beginNode]

theorem NodeInv.beginNode {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (hnx : s.nxt = none)
    (hst : s.stg = none) : NodeInv P n (beginNode s n) := NodeInv.begin h hnx hst

theorem inv_begin {P : Params} {S : Sys} {n : Bool} (h : Inv P S) (hok : beginOk P S n = true) :
    Inv P (beginUpd S n) := by
  obtain ⟨hstg, hnxt, hid⟩ := beginOk_spec hok
  rw [beginUpd_eq hok]
  have hpend : (S.nd n).roll.pending = none := by
    have := (isIdle_st _).1 hid; simp [Roll.pending, this]
  have hnn := (h.node n).beginNode hnxt hstg
  -- frame facts
  have hne : ∀ m, m ≠ n → (S.setNode n (beginNode (S.nd n) n)).nd m = S.nd m := fun m hm => Sys.setNode_ne S n m _ hm
  have hsame : (S.setNode n (beginNode (S.nd n) n)).nd n = beginNode (S.nd n) n := Sys.setNode_same _ _ _
  have fr : ∀ m, (S.setNode n (beginNode (S.nd n) n)).nd m = S.nd m ∨
      (m = n ∧ (S.setNode n (beginNode (S.nd n) n)).nd m = beginNode (S.nd n) n) := by
    intro m; by_cases hm : m = n
    · subst hm; exact Or.inr ⟨rfl, hsame⟩
    · exact Or.inl (hne m hm)
  -- fields of the new node that equal the old ones
  have eSk : ∀ m, ((S.setNode n (beginNode (S.nd n) n)).nd m).sk = (S.nd m).sk := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e] <;> first | rfl | exact le_refl _ | simp [beginNode]
  have eNpn : ∀ m, ((S.setNode n (beginNode (S.nd n) n)).nd m).npn = (S.nd m).npn := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e] <;> first | rfl | exact le_refl _ | simp [beginNode]
  have eCur : ∀ m, ((S.setNode n (beginNode (S.nd n) n)).nd m).cur = (S.nd m).cur := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e] <;> first | rfl | exact le_refl _ | simp [beginNode]
  have eNxt : ∀ m, ((S.setNode n (beginNode (S.nd n) n)).nd m).nxt = (S.nd m).nxt := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e] <;> first | rfl | exact le_refl _ | simp [beginNode]
  have eDers : ∀ m, ((S.setNode n (beginNode (S.nd n) n)).nd m).ders = (S.nd m).ders := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e] <;> first | rfl | exact le_refl _ | simp [beginNode]
  have eDial : ∀ m, ((S.setNode n (beginNode (S.nd n) n)).nd m).roll.dialer = (S.nd m).roll.dialer := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e] <;> first | rfl | exact le_refl _ | simp [beginNode]
  have eCtr : ∀ m, (S.nd m).ctr ≤ ((S.setNode n (beginNode (S.nd n) n)).nd m).ctr := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e] <;> first | rfl | exact le_refl _ | simp [beginNode]
  have eChg : ∀ m, ((S.setNode n (beginNode (S.nd n) n)).nd m).chg = (S.nd m).chg := by
    intro m; simp [Node.chg, eDers m]
  inv_mk
  all_goals try dsimp only
  case node =>
    intro m
    rcases fr m with e | ⟨rfl, e⟩
    · rw [e]; exact h.node m
    · rw [e]; exact hnn
  case netPh => exact h.netPh
  case netDep => intro p hp; have := h.netDep p hp; rw [eSk, eNpn]; exact this
  case netMsg => intro p hp m hm; exact (h.netMsg p hp m hm).mono (eCtr p.src)
  case netSlog => exact h.netSlog
  case netReq =>
    intro p hp m hm ha; obtain ⟨j, hj, hd⟩ := h.netReq p hp m hm ha
    exact ⟨j, List.mem_cons_of_mem _ hj, hd⟩
  case netAns => exact h.netAns
  case slogOK =>
    intro x hx; obtain ⟨a1, a2, a3, a4⟩ := h.slogOK x hx
    refine ⟨?_, a2, ?_, a4⟩
    · rw [eNpn]; exact a1
    · rw [eSk]; exact a3
  case slogOrd => exact h.slogOrd
  case slogUniq => exact h.slogUniq
  case breqOK =>
    intro b hb
    try dsimp only at hb
    rcases List.mem_cons.1 hb with rfl | hb
    · refine ⟨⟨(S.nd n).ctr, rfl, ?_⟩, ?_, ?_⟩
      · simp [hsame, beginNode]
      · simp [hsame, beginNode, Node.chg]
      · intro _; simp [hsame, beginNode, Roll.pending, Msg.req]
    · obtain ⟨⟨k, hk1, hk2⟩, b2, b3⟩ := h.breqOK b hb
      refine ⟨⟨k, hk1, Nat.lt_of_lt_of_le hk2 (eCtr _)⟩, by rw [eChg]; exact b2, ?_⟩
      intro hc
      rw [eChg] at hc
      by_cases hbn : b.n = n
      · exfalso
        have := b3 hc
        rw [hbn, hpend] at this; simp at this
      · rw [hne _ hbn]; exact b3 hc
  case breqPend =>
    intro m rq hrq
    by_cases hmn : m = n
    · subst hmn
      rw [hsame] at hrq
      simp [beginNode, Roll.pending] at hrq
      subst hrq
      exact ⟨(S.nd m).chg, List.mem_cons_self .., by rw [hsame]; simp [Node.chg, beginNode]⟩
    · rw [hne m hmn] at hrq
      obtain ⟨j, hj, hc⟩ := h.breqPend m rq hrq
      exact ⟨j, List.mem_cons_of_mem _ hj, by rw [eChg]; exact hc⟩
  case breqFun =>
    intro b hb b' hb' hn hsh
    try dsimp only at hb hb'
    rcases List.mem_cons.1 hb with rfl | hb <;> rcases List.mem_cons.1 hb' with rfl | hb'
    · rfl
    · exfalso
      obtain ⟨⟨k, hk1, hk2⟩, _⟩ := h.breqOK b' hb'
      simp only at hn hsh
      obtain ⟨e1, e2⟩ := pub_atom_inj (hsh.trans hk1)
      rw [← e1] at hk2
      omega
    · exfalso
      obtain ⟨⟨k, hk1, hk2⟩, _⟩ := h.breqOK b hb
      simp only at hn hsh
      obtain ⟨e1, e2⟩ := pub_atom_inj (hk1.symm.trans hsh)
      rw [e1] at hk2
      omega
    · exact h.breqFun b hb b' hb' hn hsh
  case breqF3 =>
    intro b hb hd hj
    try dsimp only at hb
    rcases List.mem_cons.1 hb with rfl | hb
    · simp only [eChg] at hj; omega
    · rw [eChg] at hj; rw [eDial] at hd
      rw [eDers]; exact h.breqF3 b hb hd hj
  case derBreq =>
    intro m q e he hs
    rw [eDers] at he
    exact List.mem_cons_of_mem _ (h.derBreq m q e he hs)
  case stlOK =>
    intro c hc
    obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := h.stlOK c hc
    refine ⟨s1, s2.mono (eCtr _), ?_, ?_, ?_, ?_, s7⟩
    · rw [eDers]; exact s3
    · rw [eCur]; exact s4
    · rw [eNpn]; exact s5
    · exact s6
  case outAns =>
    intro m a ho ha
    by_cases hmn : m = n
    · subst hmn; rw [hsame] at ho; simp [beginNode] at ho; subst ho; simp [Msg.req] at ha
    · rw [hne m hmn] at ho; exact h.outAns m a ho ha
  case ansLastStl =>
    intro m a hl
    by_cases hmn : m = n
    · subst hmn; rw [hsame] at hl; exact h.ansLastStl m a (by simpa [beginNode] using hl)
    · rw [hne m hmn] at hl; exact h.ansLastStl m a hl
  case lastAnsStl =>
    intro m sh a hl
    by_cases hmn : m = n
    · subst hmn; rw [hsame] at hl; exact h.lastAnsStl m sh a (by simpa [beginNode] using hl)
    · rw [hne m hmn] at hl; exact h.lastAnsStl m sh a hl
  case unsent =>
    intro m mm ho ha p hp heq
    by_cases hmn : m = n
    · subst hmn
      rw [hsame] at ho; simp only [beginNode, Option.some.injEq] at ho; subst ho
      obtain ⟨_, k, hk, hk2⟩ := (h.netMsg p hp _ heq).req (by simp [Msg.req])
      simp only [Msg.req] at hk
      have := pub_atom_inj hk
      obtain ⟨e1, e2⟩ := this
      subst e1
      omega
    · rw [hne m hmn] at ho; exact h.unsent m mm ho ha p hp heq
  case compOK =>
    intro c hc
    obtain ⟨⟨k, hk1, hk2⟩, hp⟩ := h.compOK c hc
    refine ⟨⟨k, hk1, Nat.lt_of_lt_of_le hk2 (eCtr _)⟩, ?_⟩
    by_cases hcn : c.n = n
    · rw [hcn] at hp hk1 hk2 ⊢
      rw [hsame]
      simp only [beginNode, Roll.pending, Option.map_some, ne_eq, Option.some.injEq]
      intro heq
      have := pub_atom_inj (hk1.symm.trans heq.symm)
      omega
    · rw [hne _ hcn]; exact hp
  case compUniq => exact h.compUniq
  case agree => exact h.agree
  case d1 =>
    intro m
    rw [eSk, eCur, eNxt]; exact h.d1 m
  case pp => rw [eDers, eDers]; exact h.pp
  case qq =>
    intro m rq hrq c hc hcn hto
    by_cases hmn : m = n
    · subst hmn
      rw [hsame] at hrq
      simp [beginNode, Roll.pending] at hrq
      subst hrq
      exfalso
      obtain ⟨_, _, _, _, _, _, p, hp, r, hr1, hr2, hr3⟩ := h.stlOK c hc
      obtain ⟨_, k, hk, hk2⟩ := (h.netMsg p hp r hr1).req hr2
      simp only [Msg.req] at hto
      rw [hr3] at hto
      have hto' := T.id.inj hto
      rw [hk] at hto'
      -- hto' : pub (atomOf p.src k) = pub (atomOf m ctr)
      have := pub_atom_inj hto'.symm
      obtain ⟨e1, e2⟩ := this
      subst e1
      omega
    · rw [hne m hmn] at hrq
      rw [eChg]; exact h.qq m rq hrq c hc hcn hto
  case nxtFloor =>
    intro m x hx
    rw [eNxt] at hx
    rw [eCur]; exact h.nxtFloor m x hx

/-! ## `SendPkt` keeps the invariant -/

theorem sendOk_spec {P : Params} {S : Sys} {n w : Bool} (h : sendOk P S n w = true) :
    (sendQ P S n w).2.npn ≤ P.maxPn ∧ (w = true → (sendQ P S n w).1.isSome = true) := by
  simp only [sendOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun hw => ?_⟩
  rcases h2 with h2 | h2
  · simp [hw] at h2
  · exact h2

theorem sendQ_node (P : Params) (S : Sys) (n w : Bool) (h : sendOk P S n w = true) :
    ∃ r l o, (o = none ∨ o = (S.nd n).out) ∧ ((sendQ P S n w).1 ≠ none → o = none) ∧ LastOK (S.nd n) l ∧
      (sendQ P S n w).2 = { S.nd n with out := o, reqAt := r, lastAns := l } := by
  cases w with
  | true =>
    obtain ⟨r, l, e, _, hl⟩ := poll_node (S.nd n) S.now P.pto
    exact ⟨r, l, none, Or.inl rfl, fun _ => rfl, hl, by simpa [sendQ] using e⟩
  | false =>
    exact ⟨(S.nd n).reqAt, (S.nd n).lastAns, (S.nd n).out, Or.inr rfl, fun hh => by simp [sendQ] at hh, Or.inl rfl,
      by simp only [sendQ, Bool.false_eq_true, ↓reduceIte]⟩

theorem sendQ_msg (P : Params) (S : Sys) (n w : Bool) (m : Msg) (hm : (sendQ P S n w).1 = some m) :
    (S.nd n).out = some m ∨ ((S.nd n).out = none ∧ (S.nd n).roll.pending = some m) := by
  cases w with
  | true => exact poll_msg _ _ _ m (by simpa [sendQ] using hm)
  | false => simp [sendQ] at hm

/-- The node after `SendPkt`. -/
def sendNode (P : Params) (S : Sys) (n w : Bool) : Node := { (sendQ P S n w).2 with npn := (sendQ P S n w).2.npn + 1 }

theorem sendUpd_eq {P : Params} {S : Sys} {n w : Bool} (h : sendOk P S n w = true) :
    ∃ r l o, (o = none ∨ o = (S.nd n).out) ∧ ((sendQ P S n w).1 ≠ none → o = none) ∧ LastOK (S.nd n) l ∧
      sendUpd P S n w =
      { (S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }) with
        net := ⟨n, (S.nd n).sph, (S.nd n).npn, (S.nd n).sk.sec, (sendQ P S n w).1⟩ :: S.net
        slog := ⟨n, (S.nd n).sk.sec, (S.nd n).sk.g, (S.nd n).npn⟩ :: S.slog } := by
  obtain ⟨r, l, o, hoo, hno, hl, hq⟩ := sendQ_node P S n w h
  refine ⟨r, l, o, hoo, hno, hl, ?_⟩
  simp only [sendUpd, sendPkt, hq]

theorem inv_send {P : Params} {S : Sys} {n w : Bool} (h : Inv P S) (hok : sendOk P S n w = true) :
    Inv P (sendUpd P S n w) := by
  obtain ⟨r, l, o, hoo, hno, hlo, he⟩ := sendUpd_eq hok
  rw [he]
  generalize hpl : (sendQ P S n w).1 = pl at *
  have hplm : ∀ m, pl = some m → (S.nd n).out = some m ∨ ((S.nd n).out = none ∧ (S.nd n).roll.pending = some m) := by
    intro m hm; rw [← hpl] at hm; exact sendQ_msg P S n w m hm
  have hnn : NodeInv P n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 } :=
    ((h.node n).setOut o r l hoo hlo).setNpn _
  have dep := (h.node n).depths
  have hsk := NodeInv.cnSk (h.node n)
  have hne : ∀ m, m ≠ n → (S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m = S.nd m :=
    fun m hm => Sys.setNode_ne S n m _ hm
  have hsame : (S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd n =
      { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 } := Sys.setNode_same _ _ _
  have fr : ∀ m, (S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m = S.nd m ∨
      (m = n ∧ (S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m =
        { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }) := by
    intro m; by_cases hm : m = n
    · subst hm; exact Or.inr ⟨rfl, hsame⟩
    · exact Or.inl (hne m hm)
  have eSk : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m).sk = (S.nd m).sk := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eCtr : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m).ctr = (S.nd m).ctr := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eCur : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m).cur = (S.nd m).cur := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eNxt : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m).nxt = (S.nd m).nxt := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eDers : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m).ders = (S.nd m).ders := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eRoll : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m).roll = (S.nd m).roll := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e]
  have eNpn : ∀ m, (S.nd m).npn ≤ ((S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m).npn := by
    intro m; rcases fr m with e | ⟨rfl, e⟩ <;> rw [e] <;> first | exact Nat.le_refl _ | exact Nat.le_succ _
  have eChg : ∀ m, ((S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m).chg = (S.nd m).chg := by
    intro m; simp [Node.chg, eDers m]
  have eOut : ∀ m, m ≠ n → ((S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd m).out = (S.nd m).out := by
    intro m hm; rw [hne m hm]
  have eOutN : ((S.setNode n { S.nd n with out := o, reqAt := r, lastAns := l, npn := (S.nd n).npn + 1 }).nd n).out = o := by
    rw [hsame]
  have hdsk : (S.nd n).sk.sec.depth = (S.nd n).sk.g := dep.1
  inv_mk
  all_goals try dsimp only
  case node =>
    intro m
    rcases fr m with e | ⟨rfl, e⟩
    · rw [e]; exact h.node m
    · rw [e]; exact hnn
  case netPh =>
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · simp only [hdsk]; exact NodeInv.phS (h.node n)
    · exact h.netPh p hp
  case netDep =>
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · simp only [hsame, hdsk]; exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
    · obtain ⟨a1, a2⟩ := h.netDep p hp
      rw [eSk]; exact ⟨a1, Nat.lt_of_lt_of_le a2 (eNpn _)⟩
  case netMsg =>
    intro p hp m hm
    rcases List.mem_cons.1 hp with rfl | hp
    · simp only at hm
      rw [eCtr]
      rcases hplm m hm with ho | ⟨_, hpd⟩
      · exact (h.node n).outMsg m ho
      · exact (h.node n).pendMsg m hpd
    · rw [eCtr]; exact h.netMsg p hp m hm
  case netSlog =>
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · simp only [hdsk]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (h.netSlog p hp)
  case netReq =>
    intro p hp m hm ha
    rcases List.mem_cons.1 hp with rfl | hp
    · simp only at hm
      have key : ∀ hpd : (S.nd n).roll.pending = some m, ∃ j, (⟨n, m.share, j⟩ : BReq) ∈ S.breq ∧
          (S.nd n).sk.g = j := by
        intro hpd
        obtain ⟨j, hj, hc⟩ := h.breqPend n m hpd
        exact ⟨j, hj, by rw [← hc]; exact ((h.node n).pending_chg hpd).1.symm⟩
      rcases hplm m hm with ho | ⟨_, hpd⟩
      · obtain ⟨j, hj, hc⟩ := key ((h.node n).outReq m ho ha)
        exact ⟨j, hj, by simp only [hdsk]; exact hc⟩
      · obtain ⟨j, hj, hc⟩ := key hpd
        exact ⟨j, hj, by simp only [hdsk]; exact hc⟩
    · obtain ⟨j, hj, hd⟩ := h.netReq p hp m hm ha
      exact ⟨j, hj, hd⟩
  case netAns =>
    intro p hp m hm ha
    rcases List.mem_cons.1 hp with rfl | hp
    · simp only at hm ⊢
      rcases hplm m hm with ho | ⟨_, hpd⟩
      · exact h.outAns n m ho ha
      · rw [(h.node n).pending_answer hpd] at ha; simp at ha
    · exact h.netAns p hp m hm ha
  case slogOK =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [hsame]; exact Nat.lt_succ_self _
      · simp only [hdsk]
      · simp only [hsame]; exact Nat.le_refl _
      · simp only
        exact ⟨_, NodeInv.kfSk (h.node n)⟩
    · obtain ⟨a1, a2, a3, a4⟩ := h.slogOK x hx
      refine ⟨Nat.lt_of_lt_of_le a1 (eNpn _), a2, ?_, a4⟩
      rw [eSk]; exact a3
  case slogOrd =>
    intro x hx y hy hn hlt
    rcases List.mem_cons.1 hx with rfl | hx <;> rcases List.mem_cons.1 hy with rfl | hy
    · omega
    · have := (h.slogOK y hy).1
      simp only at hlt hn
      subst hn
      omega
    · have := (h.slogOK x hx).2.2.1
      simp only at hn ⊢
      rw [hn] at this
      exact this
    · exact h.slogOrd x hx y hy hn hlt
  case slogUniq =>
    intro x hx y hy hn hp
    rcases List.mem_cons.1 hx with rfl | hx <;> rcases List.mem_cons.1 hy with rfl | hy
    · rfl
    · have := (h.slogOK y hy).1
      simp only at hn hp
      subst hn
      omega
    · have := (h.slogOK x hx).1
      simp only at hn hp
      subst hn
      omega
    · exact h.slogUniq x hx y hy hn hp
  case breqOK =>
    intro b hb
    obtain ⟨⟨k, k1, k2⟩, b2, b3⟩ := h.breqOK b hb
    refine ⟨⟨k, k1, by rw [eCtr]; exact k2⟩, by rw [eChg]; exact b2, ?_⟩
    rw [eChg, eRoll]; exact b3
  case breqPend =>
    intro m rq hp
    rw [eRoll] at hp
    obtain ⟨j, hj, hc⟩ := h.breqPend m rq hp
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
    obtain ⟨s1, s2, s3, s4, s5, s6, p, hp, s7⟩ := h.stlOK c hc
    refine ⟨s1, by rw [eCtr]; exact s2, by rw [eDers]; exact s3, by rw [eCur]; exact s4,
      Nat.le_trans s5 (eNpn _), ?_, p, List.mem_cons_of_mem _ hp, s7⟩
    intro x hx hxn hpos
    rcases List.mem_cons.1 hx with rfl | hx
    · simp only at hxn ⊢
      rw [← hxn] at s5
      exact s5
    · exact s6 x hx hxn hpos
  case outAns =>
    intro m a ho ha
    by_cases hmn : m = n
    · subst hmn; rw [eOutN] at ho
      rcases hoo with h0 | h0
      · rw [h0] at ho; simp at ho
      · exact h.outAns m a (by rw [← h0]; exact ho) ha
    · rw [eOut m hmn] at ho; exact h.outAns m a ho ha
  case ansLastStl =>
    intro m a hl
    by_cases hmn : m = n
    · subst hmn
      rw [hsame] at hl
      have hl' : l = some a := hl
      rcases hlo with h0 | ⟨m0, hm0, ha0, h0⟩
      · exact h.ansLastStl m a (by rw [← h0]; exact hl')
      · rw [h0] at hl'
        have : m0 = a := Option.some.inj hl'
        subst this
        exact h.outAns m m0 hm0 ha0
    · rw [hne m hmn] at hl; exact h.ansLastStl m a hl
  case lastAnsStl =>
    intro m sh a hl
    rw [eRoll] at hl
    exact h.lastAnsStl m sh a hl
  case unsent =>
    intro m mm ho ha p hp heq
    by_cases hmn : m = n
    · subst hmn; rw [eOutN] at ho
      rcases hoo with h0 | h0
      · rw [h0] at ho; simp at ho
      · have ho' : (S.nd m).out = some mm := by rw [← h0]; exact ho
        rcases List.mem_cons.1 hp with rfl | hp
        · simp only at heq
          have := hno (by rw [heq]; simp)
          rw [this] at ho; simp at ho
        · exact h.unsent m mm ho' ha p hp heq
    · rw [eOut m hmn] at ho
      rcases List.mem_cons.1 hp with rfl | hp
      · simp only at heq
        subst heq
        obtain ⟨_, k, hk, _⟩ := (h.node m).outMsg _ ho |>.req ha
        rcases hplm _ rfl with ho' | ⟨_, hpd⟩
        · have := (h.node n).outMsg _ ho'
          obtain ⟨_, k', hk', _⟩ := this.req ha
          obtain ⟨e1, _⟩ := pub_atom_inj (hk.symm.trans hk')
          exact hmn e1
        · have := (h.node n).pendMsg _ hpd
          obtain ⟨_, k', hk', _⟩ := this.req ha
          obtain ⟨e1, _⟩ := pub_atom_inj (hk.symm.trans hk')
          exact hmn e1
      · exact h.unsent m mm ho ha p hp heq
  case compOK =>
    intro c hc
    obtain ⟨⟨k, k1, k2⟩, k3⟩ := h.compOK c hc
    refine ⟨⟨k, k1, by rw [eCtr]; exact k2⟩, ?_⟩
    rw [eRoll]; exact k3
  case compUniq => exact h.compUniq
  case agree => exact h.agree
  case d1 =>
    intro m
    simp only [eSk, eCur, eNxt]; exact h.d1 m
  case pp => simp only [eDers]; exact h.pp
  case qq =>
    intro m rq hrq c hc hcn hto
    rw [eRoll] at hrq
    rw [eChg]; exact h.qq m rq hrq c hc hcn hto
  case nxtFloor =>
    intro m x hx
    rw [eNxt] at hx
    rw [eCur]; exact h.nxtFloor m x hx

end Vinc.KeyRollSys
