import Vinc.KeyRollSysNode

namespace Vinc.KeyRollSys
open Vinc.KeyRoll

/-! ## The invariant of the system

`NodeInv` for each node, the packets on the network, the logs and the cross-node facts. Everything here is proved
by induction over `Reach`; `Inv.cross` needs `bindAnswers`. -/

/-- A derivation as the other node sees it: the request and the Diffie-Hellman value. -/
def Der.core (e : Der) : T × T := (e.rid, e.dh)

/-- Two lists, one a prefix of the other. -/
def PP {α : Type} (a b : List α) : Prop := a <+: b ∨ b <+: a

theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : upd f a b a = b := by simp [upd]
theorem upd_not (f : Bool → Node) (a : Bool) (b : Node) : upd f a b (!a) = f (!a) := by
  cases a <;> simp [upd]

/-- The invariants that do not need the other node to be in step with this one. -/
structure Inv (P : Params) (S : Sys) : Prop where
  node : ∀ n, NodeInv P n (S.nd n)
  -- the network
  netPh : ∀ p ∈ S.net, p.ph = decide (p.sec.depth % 2 = 1)
  netDep : ∀ p ∈ S.net, p.sec.depth ≤ (S.nd p.src).sk.g ∧ p.pn < (S.nd p.src).npn
  netMsg : ∀ p ∈ S.net, ∀ m, p.pl = some m → MsgOK p.src (S.nd p.src).ctr m
  netSlog : ∀ p ∈ S.net, (⟨p.src, p.sec, p.sec.depth, p.pn⟩ : Seal) ∈ S.slog
  netReq : ∀ p ∈ S.net, ∀ m, p.pl = some m → m.answer = false →
    ∃ j, (⟨p.src, m.share, j⟩ : BReq) ∈ S.breq ∧ p.sec.depth = j
  netAns : ∀ p ∈ S.net, ∀ m, p.pl = some m → m.answer = true → ∃ c ∈ S.stl, c.ans = m ∧ c.n = p.src
  -- the seals
  slogOK : ∀ x ∈ S.slog, x.pn < (S.nd x.n).npn ∧ x.g = x.sec.depth ∧ x.g ≤ (S.nd x.n).sk.g ∧
    ∃ ds, x.sec = rollAll (.base (nid x.n)) ds
  slogOrd : ∀ x ∈ S.slog, ∀ y ∈ S.slog, x.n = y.n → x.pn < y.pn → x.g ≤ y.g
  slogUniq : ∀ x ∈ S.slog, ∀ y ∈ S.slog, x.n = y.n → x.pn = y.pn → x = y
  -- the begun requests
  breqOK : ∀ b ∈ S.breq, (∃ k, b.sh = .pub (atomOf b.n k) ∧ k < (S.nd b.n).ctr) ∧ b.j ≤ (S.nd b.n).chg ∧
    ((S.nd b.n).chg = b.j → (S.nd b.n).roll.pending.map Msg.share = some b.sh)
  breqPend : ∀ n m, (S.nd n).roll.pending = some m → ∃ j, (⟨n, m.share, j⟩ : BReq) ∈ S.breq ∧ (S.nd n).chg = j
  breqFun : ∀ b ∈ S.breq, ∀ b' ∈ S.breq, b.n = b'.n → b.sh = b'.sh → b = b'
  breqF3 : ∀ b ∈ S.breq, (S.nd b.n).roll.dialer = true → b.j < (S.nd b.n).chg →
    ∃ e, (S.nd b.n).ders[b.j]? = some e ∧ e.stg = false ∧ e.rid = b.sh
  derBreq : ∀ (n : Bool) (q : Nat) (e : Der), (S.nd n).ders[q]? = some e → e.stg = true → (⟨!n, e.rid, e.lvl⟩ : BReq) ∈ S.breq
  -- the stagings
  stlOK : ∀ c ∈ S.stl, c.ans.answer = true ∧ MsgOK c.n (S.nd c.n).ctr c.ans ∧
    (∃ lv, (S.nd c.n).ders[c.pos]? = some ⟨true, c.ans.to, c.ans.gdh, lv⟩) ∧ c.pos ≤ (S.nd c.n).cur.g ∧
    c.ans.spn ≤ (S.nd c.n).npn ∧
    (∀ x ∈ S.slog, x.n = c.n → c.pos < x.g → c.ans.spn ≤ x.pn) ∧
    ∃ p ∈ S.net, ∃ r, p.pl = some r ∧ r.answer = false ∧ r.share = c.ans.to
  outAns : ∀ n a, (S.nd n).out = some a → a.answer = true → ∃ c ∈ S.stl, c.ans = a ∧ c.n = n
  lastAnsStl : ∀ n sh a, (S.nd n).roll.last = some (sh, a) → ∃ c ∈ S.stl, c.ans = a ∧ c.n = n
  unsent : ∀ n m, (S.nd n).out = some m → m.answer = false → ∀ p ∈ S.net, p.pl ≠ some m
  -- the completions
  compOK : ∀ c ∈ S.comp, (∃ k, c.req = .pub (atomOf c.n k) ∧ k < (S.nd c.n).ctr) ∧ (S.nd c.n).roll.pending.map Msg.share ≠ some c.req
  compUniq : ∀ c ∈ S.comp, ∀ c' ∈ S.comp, c.req = c'.req → c = c'
  agree : ∀ c ∈ S.comp, c.dh = c.gdh
  -- the two nodes together (the cross-node facts)
  d1 : ∀ n, (S.nd (!n)).cur.g ≤ (S.nd n).sk.g ∧ (S.nd n).sk.g ≤ (S.nd (!n)).cur.g + 1 ∧
    ((S.nd n).sk.g = (S.nd (!n)).cur.g + 1 → (S.nd (!n)).nxt.isSome = true)
  pp : PP ((S.nd false).ders.map Der.core) ((S.nd true).ders.map Der.core)
  qq : ∀ n rq, (S.nd n).roll.pending = some rq → ∀ c ∈ S.stl, c.n = !n → c.ans.to = rq.share →
    c.pos = (S.nd n).chg
  nxtFloor : ∀ n x, (S.nd n).nxt = some x →
    x.floor = 0 ∨ ∃ c ∈ S.stl, c.n = !n ∧ c.pos = (S.nd n).cur.g ∧ c.ans.spn = x.floor

/-- Prove every field of `Inv` separately. -/
macro "inv_mk" : tactic => `(tactic| refine Inv.mk ?node ?netPh ?netDep ?netMsg ?netSlog ?netReq ?netAns ?slogOK ?slogOrd ?slogUniq ?breqOK ?breqPend ?breqFun ?breqF3 ?derBreq ?stlOK ?outAns ?lastAnsStl ?unsent ?compOK ?compUniq ?agree ?d1 ?pp ?qq ?nxtFloor)

theorem Inv.init (P : Params) : Inv P Sys.init := by
  inv_mk
  case node => intro n; exact NodeInv.init P n
  case d1 => intro n; simp [Sys.init, Node.init, PK.new]
  case pp => left; simp [Sys.init, Node.init]
  all_goals intros; simp_all [Sys.init, Node.init, Roll.new, Roll.pending]

@[simp] theorem Sys.setNode_same (S : Sys) (n : Bool) (s' : Node) : (S.setNode n s').nd n = s' := by
  simp [Sys.setNode, upd]
@[simp] theorem Sys.setNode_not (S : Sys) (n : Bool) (s' : Node) : (S.setNode n s').nd (!n) = S.nd (!n) := by
  cases n <;> simp [Sys.setNode, upd]
theorem Sys.setNode_ne (S : Sys) (n m : Bool) (s' : Node) (h : m ≠ n) : (S.setNode n s').nd m = S.nd m := by
  simp [Sys.setNode, upd, h]

theorem atomOf_inj {n n' : Bool} {k k' : Nat} (h : atomOf n k = atomOf n' k') : n = n' ∧ k = k' := by
  cases n <;> cases n' <;> simp [atomOf, nid] at h <;> simp [h]

theorem pub_atom_inj {n n' : Bool} {k k' : Nat} (h : T.pub (atomOf n k) = T.pub (atomOf n' k')) : n = n' ∧ k = k' :=
  atomOf_inj (T.pub.inj h)

end Vinc.KeyRollSys
