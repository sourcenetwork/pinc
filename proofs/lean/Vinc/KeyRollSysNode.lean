import Vinc.KeyRollSysInv

namespace Vinc.KeyRollSys
open Vinc.KeyRoll

/-! ## The local invariant of one node

Everything here is about one node and its own ghost list `ders`; nothing needs the other node. -/

/-- The Diffie-Hellman values derived so far. -/
def dhs (s : Node) : List T := s.ders.map Der.dh

/-- The share of an atom of node `n`. -/
def own (n : Bool) (t : T) : Prop := ∃ k, t = .pub (atomOf n k)

/-- The rid of the last derivation if it was a staging: what `Roll.last` must remember. -/
def Node.lastRid (s : Node) : Option T :=
  match s.ders.getLast? with
  | some e => if e.stg then some e.rid else none
  | none => none

/-- A message sent by node `n` that has drawn `c` atoms: shares are public values of its own atoms, an answer carries
the identifier of the request share it answers and the Diffie-Hellman value of the two atoms with it bound in. -/
structure MsgOK (n : Bool) (c : Nat) (m : Msg) : Prop where
  req : m.answer = false → m = Msg.req m.share ∧ ∃ k, m.share = .pub (atomOf n k) ∧ k < c
  ans : m.answer = true → ∃ k k', m.share = .pub (atomOf n k) ∧ k < c ∧ m.to = .id (.pub (atomOf (!n) k')) ∧
    m.gdh = .bound (.id (.pub (atomOf (!n) k'))) (Dh (atomOf n k) (atomOf (!n) k'))

theorem MsgOK.mono {n : Bool} {c c' : Nat} {m : Msg} (h : MsgOK n c m) (hc : c ≤ c') : MsgOK n c' m :=
  ⟨fun a => let ⟨x, k, y, z⟩ := h.req a; ⟨x, k, y, by omega⟩,
   fun a => let ⟨k, k', y, z, w, v⟩ := h.ans a; ⟨k, k', y, by omega, w, v⟩⟩

/-- Each staging (derivation as answerer) follows the one before it only for another request. -/
def NoDupStg (l : List Der) : Prop :=
  ∀ i e e', l[i]? = some e → l[i + 1]? = some e' → e.stg = true → e'.stg = true → e'.rid ≠ e.rid

/-- A staging happened for a request begun at the level of the staging or the level below. -/
def DerLvl (l : List Der) : Prop :=
  ∀ i e, l[i]? = some e → e.stg = true → e.lvl = i ∨ e.lvl + 1 = i

/-- A staging answers a request of the peer, a completion takes the answer to a request of this node. -/
def DerOK (n : Bool) (l : List Der) : Prop :=
  ∀ e ∈ l, (e.stg = true ∧ own (!n) e.rid) ∨ (e.stg = false ∧ own n e.rid)

structure NodeInv (P : Params) (n : Bool) (s : Node) : Prop where
  dialer : s.roll.dialer = !n
  kfSk : s.sk.sec = rollAll (.base (nid n)) ((dhs s).take s.sk.g)
  kfCur : s.cur.sec = rollAll (.base (nid (!n))) ((dhs s).take s.cur.g)
  kfStg : ∀ k, s.stg = some k → k.sec = rollAll (.base (nid n)) ((dhs s).take (s.sk.g + 1)) ∧ k.g = s.sk.g + 1
  kfNxt : ∀ x, s.nxt = some x →
    x.k.sec = rollAll (.base (nid (!n))) ((dhs s).take (s.cur.g + 1)) ∧ x.k.g = s.cur.g + 1
  kfPrev : ∀ pv, s.prev = some pv →
    pv.k.sec = rollAll (.base (nid (!n))) ((dhs s).take pv.k.g) ∧ pv.k.g + 1 = s.cur.g
  cnSk : s.chg = s.sk.g + (if s.stg.isSome then 1 else 0)
  cnCur : s.chg = s.cur.g + (if s.nxt.isSome then 1 else 0)
  cnSN : s.stg.isSome → s.nxt.isSome
  phS : s.sph = decide (s.sk.g % 2 = 1)
  phR : s.rph = decide (s.cur.g % 2 = 1)
  req : s.roll.isIdle = false → s.nxt = none ∧ s.stg = none
  hold : ∀ pv, s.prev = some pv → ∃ t, s.promAt = some t ∧ pv.dl = t + P.pto
  rolls : s.roll.rolls = min s.chg Record.u64max
  derOK : DerOK n s.ders
  lastInv : s.roll.last.map Prod.fst = s.lastRid
  stgLast : s.stg.isSome → ∃ e, s.ders.getLast? = some e ∧ e.stg = true
  noDup : NoDupStg s.ders
  derLvl : DerLvl s.ders
  outMsg : ∀ m, s.out = some m → MsgOK n s.ctr m
  pendMsg : ∀ m, s.roll.pending = some m → MsgOK n s.ctr m
  lastMsg : ∀ sh a, s.roll.last = some (sh, a) → MsgOK n s.ctr a
  lastAns : ∀ sh a, s.roll.last = some (sh, a) → a.answer = true
  outReq : ∀ m, s.out = some m → m.answer = false → s.roll.pending = some m
  pendSeed : ∀ seed rq, s.roll.st = .req seed rq → rq = Msg.req (.pub seed) ∧ ∃ k, seed = atomOf n k ∧ k < s.ctr
  ansLast : ∀ m, s.lastAns = some m → MsgOK n s.ctr m ∧ m.answer = true

/-- Prove every field of `NodeInv` separately. -/
macro "node_inv" : tactic => `(tactic| refine NodeInv.mk ?dialer ?kfSk ?kfCur ?kfStg ?kfNxt ?kfPrev ?cnSk ?cnCur ?cnSN ?phS ?phR ?req ?hold ?rolls ?derOK ?lastInv ?stgLast ?noDup ?derLvl ?outMsg ?pendMsg ?lastMsg ?lastAns ?outReq ?pendSeed ?ansLast)

/-- `node_inv` closing every field that reads only fields the update leaves alone. -/
macro "close_same " h:ident : tactic =>
  `(tactic| first | (have t := NodeInv.dialer $h; exact t) | (have t := NodeInv.kfSk $h; exact t) | (have t := NodeInv.kfCur $h; exact t) | (have t := NodeInv.kfStg $h; exact t) | (have t := NodeInv.kfNxt $h; exact t) | (have t := NodeInv.kfPrev $h; exact t) | (have t := NodeInv.cnSk $h; exact t) | (have t := NodeInv.cnCur $h; exact t) | (have t := NodeInv.cnSN $h; exact t) | (have t := NodeInv.phS $h; exact t) | (have t := NodeInv.phR $h; exact t) | (have t := NodeInv.req $h; exact t) | (have t := NodeInv.hold $h; exact t) | (have t := NodeInv.rolls $h; exact t) | (have t := NodeInv.derOK $h; exact t) | (have t := NodeInv.lastInv $h; exact t) | (have t := NodeInv.stgLast $h; exact t) | (have t := NodeInv.noDup $h; exact t) | (have t := NodeInv.derLvl $h; exact t) | (have t := NodeInv.outMsg $h; exact t) | (have t := NodeInv.pendMsg $h; exact t) | (have t := NodeInv.lastMsg $h; exact t) | (have t := NodeInv.lastAns $h; exact t) | (have t := NodeInv.outReq $h; exact t) | (have t := NodeInv.pendSeed $h; exact t) | (have t := NodeInv.ansLast $h; exact t))

macro "node_inv_same " h:ident : tactic => `(tactic| (node_inv <;> close_same $h))

theorem NodeInv.init (P : Params) (n : Bool) : NodeInv P n (Node.init n) := by
  node_inv
  all_goals simp [Node.init, Node.chg, dhs, Roll.new, Roll.isIdle, Roll.pending, DerOK, NoDupStg, DerLvl, Node.lastRid,
    PK.new, rollAll]

theorem NodeInv.begin {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (hnx : s.nxt = none)
    (hst : s.stg = none) :
    NodeInv P n { s with roll := { s.roll with st := .req (atomOf n s.ctr) (Msg.req (.pub (atomOf n s.ctr))) },
                         out := some (Msg.req (.pub (atomOf n s.ctr))), reqAt := none, ctr := s.ctr + 1 } := by
  have hm : MsgOK n (s.ctr + 1) (Msg.req (.pub (atomOf n s.ctr))) :=
    ⟨fun _ => ⟨rfl, s.ctr, rfl, by show s.ctr < s.ctr + 1; omega⟩, fun a => by simp [Msg.req] at a⟩
  have hp : ({ s.roll with st := .req (atomOf n s.ctr) (Msg.req (.pub (atomOf n s.ctr))) } : Roll).pending
      = some (Msg.req (.pub (atomOf n s.ctr))) := rfl
  node_inv
  · exact h.dialer
  · exact h.kfSk
  · exact h.kfCur
  · exact h.kfStg
  · exact h.kfNxt
  · exact h.kfPrev
  · exact h.cnSk
  · exact h.cnCur
  · exact h.cnSN
  · exact h.phS
  · exact h.phR
  · intro _; exact ⟨hnx, hst⟩
  · exact h.hold
  · exact h.rolls
  · exact h.derOK
  · exact h.lastInv
  · exact h.stgLast
  · exact h.noDup
  · exact h.derLvl
  · intro m hm'; simp only [Option.some.injEq] at hm'; subst hm'; exact hm
  · intro m hm'; rw [hp] at hm'; simp only [Option.some.injEq] at hm'; subst hm'; exact hm
  · intro sh a hl; exact (h.lastMsg sh a hl).mono (by show s.ctr ≤ s.ctr + 1; omega)
  · exact h.lastAns
  · intro m hm' _; simp only [Option.some.injEq] at hm'; subst hm'; exact hp
  · intro seed rq hs
    simp only [St.req.injEq] at hs
    obtain ⟨e1, e2⟩ := hs
    subst e1; subst e2
    exact ⟨rfl, s.ctr, rfl, by show s.ctr < s.ctr + 1; omega⟩
  · intro m hm'; have t := h.ansLast m hm'; exact ⟨t.1.mono (by show s.ctr ≤ s.ctr + 1; omega), t.2⟩

/-- What `poll` does to the last answer: nothing, or it becomes the answer that was waiting. -/
def LastOK (s : Node) (l : Option Msg) : Prop :=
  l = s.lastAns ∨ ∃ m, s.out = some m ∧ m.answer = true ∧ l = some m

theorem poll_node (s : Node) (now pto : Nat) :
    ∃ r l, (s.poll now pto).2 = { s with out := none, reqAt := r, lastAns := l } ∧
      (s.out = none ∨ ∃ m, s.out = some m) ∧ LastOK s l := by
  unfold Node.poll
  split
  · rename_i m ho
    refine ⟨_, if m.answer = true then some m else s.lastAns, rfl, Or.inr ⟨m, ho⟩, ?_⟩
    by_cases ha : m.answer = true
    · exact Or.inr ⟨m, ho, ha, by simp [ha]⟩
    · exact Or.inl (by simp [ha])
  · rename_i ho
    split
    · rename_i r hp
      by_cases hd : s.pollDue now pto = true
      · simp only [hd, ↓reduceIte]
        refine ⟨some now, s.lastAns, ?_, Or.inl ho, Or.inl rfl⟩
        cases s; simp_all
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        refine ⟨s.reqAt, s.lastAns, ?_, Or.inl ho, Or.inl rfl⟩
        cases s; simp_all
    · refine ⟨s.reqAt, s.lastAns, ?_, Or.inl ho, Or.inl rfl⟩
      cases s; simp_all

theorem poll_none_out (s : Node) (now pto : Nat) (h : (s.poll now pto).1 = none) : s.out = none := by
  unfold Node.poll at h
  split at h
  · simp at h
  · rename_i ho; exact ho

theorem poll_msg (s : Node) (now pto : Nat) (m : Msg) (h : (s.poll now pto).1 = some m) :
    s.out = some m ∨ (s.out = none ∧ s.roll.pending = some m) := by
  unfold Node.poll at h
  split at h
  · rename_i m' ho; simp only [Option.some.injEq] at h; subst h; exact Or.inl ho
  · rename_i ho
    split at h
    · rename_i r hp
      by_cases hd : s.pollDue now pto = true
      · simp only [hd, ↓reduceIte, Option.some.injEq] at h; subst h; exact Or.inr ⟨ho, hp⟩
      · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h; simp at h
    · simp at h

/-- Setting the message waiting (`out`) to nothing or leaving it, and the time of the last send, keeps the invariant. -/
theorem NodeInv.setOut {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (o : Option Msg) (r : Option Nat)
    (l : Option Msg) (ho : o = none ∨ o = s.out) (hl : LastOK s l) :
    NodeInv P n { s with out := o, reqAt := r, lastAns := l } := by
  node_inv
  · exact h.dialer
  · exact h.kfSk
  · exact h.kfCur
  · exact h.kfStg
  · exact h.kfNxt
  · exact h.kfPrev
  · exact h.cnSk
  · exact h.cnCur
  · exact h.cnSN
  · exact h.phS
  · exact h.phR
  · exact h.req
  · exact h.hold
  · exact h.rolls
  · exact h.derOK
  · exact h.lastInv
  · exact h.stgLast
  · exact h.noDup
  · exact h.derLvl
  · intro m hm; rcases ho with rfl | rfl
    · simp at hm
    · exact h.outMsg m hm
  · exact h.pendMsg
  · exact h.lastMsg
  · exact h.lastAns
  · intro m hm hq; rcases ho with rfl | rfl
    · simp at hm
    · exact h.outReq m hm hq
  · exact h.pendSeed
  · intro m hm
    rcases hl with rfl | ⟨m', hm', ha, rfl⟩
    · exact h.ansLast m hm
    · simp only [Option.some.injEq] at hm; subst hm; exact ⟨h.outMsg m' hm', ha⟩

/-- The packet number does not matter to the local invariant. -/
theorem NodeInv.setNpn {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (k : Nat) :
    NodeInv P n { s with npn := k } := by node_inv_same h

/-! ### The keys layer (`RecvKeys`) keeps the local invariant -/

theorem expire_cases (s : Node) (t : Nat) : s.expire t = s ∨ s.expire t = { s with prev := none } := by
  unfold Node.expire
  cases hp : s.prev with
  | none => exact Or.inl rfl
  | some p => by_cases h : p.dl ≤ t <;> simp [h]

theorem NodeInv.dropPrev {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) : NodeInv P n { s with prev := none } := by
  node_inv
  all_goals first
    | (intro pv hp; simp at hp; done)
    | skip
  all_goals close_same h

theorem NodeInv.expire {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (t : Nat) : NodeInv P n (s.expire t) := by
  rcases expire_cases s t with e | e <;> rw [e]
  · exact h
  · exact h.dropPrev

theorem NodeInv.first {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (f : Nat) :
    NodeInv P n { s with first := f } := by node_inv_same h

theorem NodeInv.seen {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (l : List Nat) :
    NodeInv P n { s with seen := l } := by node_inv_same h

theorem NodeInv.bump {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (sel : Sel) : NodeInv P n (s.bumpFC sel) := by
  cases sel with
  | err => exact h
  | cur => node_inv_same h
  | prev =>
    node_inv
    case kfPrev =>
      intro pv hp
      cases hq : s.prev with
      | none => simp [Node.bumpFC, hq] at hp
      | some q => simp [Node.bumpFC, hq] at hp; subst hp; exact NodeInv.kfPrev h q hq
    case hold =>
      intro pv hp
      cases hq : s.prev with
      | none => simp [Node.bumpFC, hq] at hp
      | some q => simp [Node.bumpFC, hq] at hp; subst hp; exact NodeInv.hold h q hq
    all_goals close_same h
  | next =>
    have e : (s.bumpFC .next).nxt.isSome = s.nxt.isSome := by simp [Node.bumpFC]
    have e2 : (s.bumpFC .next).nxt = none ↔ s.nxt = none := by simp [Node.bumpFC]
    node_inv
    case kfNxt =>
      intro x hx
      cases hq : s.nxt with
      | none => simp [Node.bumpFC, hq] at hx
      | some q => simp [Node.bumpFC, hq] at hx; subst hx; exact NodeInv.kfNxt h q hq
    case cnCur => have t := NodeInv.cnCur h; show s.chg = s.cur.g + _; rw [e]; exact t
    case cnSN => intro hs; rw [e]; exact NodeInv.cnSN h hs
    case req => intro hi; have t := NodeInv.req h hi; exact ⟨e2.2 t.1, t.2⟩
    all_goals close_same h

theorem parity_succ (a : Nat) (b : Bool) (h : b = decide (a % 2 = 1)) : (!b) = decide ((a + 1) % 2 = 1) := by
  subst h
  by_cases c : a % 2 = 1
  · have : ¬ (a + 1) % 2 = 1 := by omega
    simp [c, this]
  · have : (a + 1) % 2 = 1 := by omega
    simp [c, this]

/-- Promoting the staged key (and, as `Keys::update_send` does, switching the staged sending key) keeps the invariant. -/
theorem NodeInv.promoteSend {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (pn t : Nat) :
    NodeInv P n ((s.promote pn t P.pto).updateSend) := by
  cases hn : s.nxt with
  | none =>
    have : s.stg = none := by
      cases hs : s.stg with
      | none => rfl
      | some k => have := NodeInv.cnSN h (by simp [hs]); simp [hn] at this
    simp [Node.promote, Node.updateSend, hn, this]; exact h
  | some x =>
    obtain ⟨hx1, hx2⟩ := NodeInv.kfNxt h x hn
    have hc := NodeInv.cnCur h
    simp only [hn, Option.isSome_some, if_true] at hc
    have hp := parity_succ _ _ (NodeInv.phR h)
    cases hs : s.stg with
    | none =>
      simp only [Node.promote, Node.updateSend, hn, hs]
      node_inv
      case dialer => (have t := NodeInv.dialer h; exact t)
      case kfSk => (have t := NodeInv.kfSk h; exact t)
      case kfCur => show x.k.sec = rollAll _ (List.take x.k.g _); rw [hx2]; exact hx1
      case kfStg => intro k hk; simp at hk
      case kfNxt => intro y hy; simp at hy
      case kfPrev =>
        intro pv hpv
        simp only [Option.some.injEq] at hpv
        subst hpv
        exact ⟨NodeInv.kfCur h, by show s.cur.g + 1 = x.k.g; omega⟩
      case cnSk => have t := NodeInv.cnSk h; simp only [hs] at t; show s.chg = s.sk.g + 0; simpa using t
      case cnCur => show s.chg = x.k.g + 0; omega
      case cnSN => intro h; simp at h
      case phS => (have t := NodeInv.phS h; exact t)
      case phR => show (!s.rph) = decide (x.k.g % 2 = 1); rw [hx2]; exact hp
      case req => intro _; exact ⟨rfl, rfl⟩
      case hold => intro pv hpv; simp only [Option.some.injEq] at hpv; subst hpv; exact ⟨t, rfl, rfl⟩
      case rolls => (have t := NodeInv.rolls h; exact t)
      case derOK => (have t := NodeInv.derOK h; exact t)
      case lastInv => (have t := NodeInv.lastInv h; exact t)
      case stgLast => intro h; simp at h
      case noDup => (have t := NodeInv.noDup h; exact t)
      case derLvl => (have t := NodeInv.derLvl h; exact t)
      case outMsg => (have t := NodeInv.outMsg h; exact t)
      case pendMsg => (have t := NodeInv.pendMsg h; exact t)
      case lastMsg => (have t := NodeInv.lastMsg h; exact t)
      case lastAns => (have t := NodeInv.lastAns h; exact t)
      case outReq => (have t := NodeInv.outReq h; exact t)
      case pendSeed => (have t := NodeInv.pendSeed h; exact t)
      case ansLast => (have t := NodeInv.ansLast h; exact t)
    | some k =>
      obtain ⟨hk1, hk2⟩ := NodeInv.kfStg h k hs
      have hcs := NodeInv.cnSk h
      simp only [hs, Option.isSome_some, if_true] at hcs
      have hps := parity_succ _ _ (NodeInv.phS h)
      simp only [Node.promote, Node.updateSend, hn, hs]
      node_inv
      case dialer => (have t := NodeInv.dialer h; exact t)
      case kfSk => show k.sec = rollAll _ (List.take k.g _); rw [hk2]; exact hk1
      case kfCur => show x.k.sec = rollAll _ (List.take x.k.g _); rw [hx2]; exact hx1
      case kfStg => intro k hk; simp at hk
      case kfNxt => intro y hy; simp at hy
      case kfPrev =>
        intro pv hpv
        simp only [Option.some.injEq] at hpv
        subst hpv
        exact ⟨NodeInv.kfCur h, by show s.cur.g + 1 = x.k.g; omega⟩
      case cnSk => show s.chg = k.g + 0; omega
      case cnCur => show s.chg = x.k.g + 0; omega
      case cnSN => intro h; simp at h
      case phS => show (!s.sph) = decide (k.g % 2 = 1); rw [hk2]; exact hps
      case phR => show (!s.rph) = decide (x.k.g % 2 = 1); rw [hx2]; exact hp
      case req => intro _; exact ⟨rfl, rfl⟩
      case hold => intro pv hpv; simp only [Option.some.injEq] at hpv; subst hpv; exact ⟨t, rfl, rfl⟩
      case rolls => (have t := NodeInv.rolls h; exact t)
      case derOK => (have t := NodeInv.derOK h; exact t)
      case lastInv => (have t := NodeInv.lastInv h; exact t)
      case stgLast => intro h; simp at h
      case noDup => (have t := NodeInv.noDup h; exact t)
      case derLvl => (have t := NodeInv.derLvl h; exact t)
      case outMsg => (have t := NodeInv.outMsg h; exact t)
      case pendMsg => (have t := NodeInv.pendMsg h; exact t)
      case lastMsg => (have t := NodeInv.lastMsg h; exact t)
      case lastAns => (have t := NodeInv.lastAns h; exact t)
      case outReq => (have t := NodeInv.outReq h; exact t)
      case pendSeed => (have t := NodeInv.pendSeed h; exact t)
      case ansLast => (have t := NodeInv.ansLast h; exact t)

/-- What `RecvKeys` can do to the node. -/
theorem recvKeys_form (s : Node) (p : Pkt) (f : Bool) (t pto : Nat) :
    (s.recvKeys p f t pto).s = s.expire t ∨ (∃ fst, (s.recvKeys p f t pto).s = { s.expire t with first := fst }) ∨
    (∃ sel, (s.recvKeys p f t pto).s = (s.expire t).bumpFC sel) ∨
    ((s.recvKeys p f t pto).acc = true ∧ (s.recvKeys p f t pto).sel = .next ∧
      (s.recvKeys p f t pto).s = ((s.expire t).promote p.pn t pto).updateSend) := by
  unfold Node.recvKeys
  dsimp only
  generalize s.expire t = s1
  generalize (s1.select (if f = true then !p.ph else p.ph) p.pn) = sel
  generalize (!f && decide (s1.slotSec sel = some p.sec)) = ok
  cases sel <;> cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
    | (right; right; right; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial)

theorem NodeInv.recvKeys {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (p : Pkt) (f : Bool) (t : Nat) :
    NodeInv P n (s.recvKeys p f t P.pto).s := by
  have h1 := h.expire t
  rcases recvKeys_form s p f t P.pto with e | ⟨fst, e⟩ | ⟨sel, e⟩ | ⟨_, _, e⟩ <;> rw [e]
  · exact h1
  · exact h1.first fst
  · exact h1.bump sel
  · exact h1.promoteSend _ _

theorem NodeInv.afterRecv {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (p : Pkt) (f : Bool) (t : Nat) :
    NodeInv P n (s.afterRecv P p f t).1 := by
  unfold Node.afterRecv
  simp only
  split
  · exact (h.recvKeys p f t).seen _
  · exact h.recvKeys p f t

/-! ### `RekeyRx` keeps the local invariant -/

theorem NoDupStg.snoc {l : List Der} (hn : NoDupStg l) (e : Der)
    (hl : ∀ x, l.getLast? = some x → x.stg = true → e.stg = true → e.rid ≠ x.rid) : NoDupStg (l ++ [e]) := by
  intro i a b ha hb sa sb
  by_cases h1 : i + 1 < l.length
  · rw [List.getElem?_append_left (by omega)] at ha
    rw [List.getElem?_append_left h1] at hb
    exact hn i a b ha hb sa sb
  · by_cases h2 : i < l.length
    · have hi : i + 1 = l.length := by omega
      rw [List.getElem?_append_left h2] at ha
      rw [List.getElem?_append_right (by omega)] at hb
      simp [hi] at hb
      subst hb
      have hlast : l.getLast? = some a := by
        rw [List.getLast?_eq_getElem?]
        have : l.length - 1 = i := by omega
        rw [this]; exact ha
      exact hl a hlast sa sb
    · rw [List.getElem?_append_right (by omega)] at hb
      simp [List.getElem?_eq_none (show [e].length ≤ i + 1 - l.length by simp; omega)] at hb

theorem DerLvl.snoc {l : List Der} (hn : DerLvl l) (e : Der)
    (he : e.stg = true → e.lvl = l.length ∨ e.lvl + 1 = l.length) : DerLvl (l ++ [e]) := by
  intro i a ha sa
  by_cases h : i < l.length
  · rw [List.getElem?_append_left h] at ha
    exact hn i a ha sa
  · rw [List.getElem?_append_right (by omega)] at ha
    by_cases h0 : i - l.length = 0
    · simp [h0] at ha
      subst ha
      have : i = l.length := by omega
      subst this
      exact he sa
    · simp [List.getElem?_eq_none (show [e].length ≤ i - l.length by simp; omega)] at ha

theorem DerOK.snoc {n : Bool} {l : List Der} (hn : DerOK n l) (e : Der)
    (he : (e.stg = true ∧ own (!n) e.rid) ∨ (e.stg = false ∧ own n e.rid)) : DerOK n (l ++ [e]) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hn x hx
  · simp at hx; subst hx; exact he

theorem dhs_snoc (s : Node) (e : Der) : dhs { s with ders := s.ders ++ [e] } = dhs s ++ [e.dh] := by
  simp [dhs]

theorem dhs_length (s : Node) : (dhs s).length = s.chg := by simp [dhs, Node.chg]

theorem Node.lastRid_snoc (s : Node) (e : Der) :
    ({ s with ders := s.ders ++ [e] } : Node).lastRid = if e.stg then some e.rid else none := by
  simp [Node.lastRid]

theorem rolls_inc (c : Nat) : Record.inc (min c Record.u64max) = min (c + 1) Record.u64max := by
  unfold Record.inc; omega

@[simp] theorem consumed_roll (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) : (s.consumed r dh p rid).roll = r := rfl
@[simp] theorem consumed_ctr (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) : (s.consumed r dh p rid).ctr = s.ctr := rfl
@[simp] theorem consumed_sk (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) :
    (s.consumed r dh p rid).sk = PK.new (.roll s.sk.sec dh) (s.sk.g + 1) := rfl
@[simp] theorem consumed_sph (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) : (s.consumed r dh p rid).sph = !s.sph := rfl
@[simp] theorem consumed_stg (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) : (s.consumed r dh p rid).stg = s.stg := rfl
@[simp] theorem consumed_out (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) : (s.consumed r dh p rid).out = s.out := rfl
@[simp] theorem consumed_cur (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) : (s.consumed r dh p rid).cur = s.cur := rfl
@[simp] theorem consumed_rph (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) : (s.consumed r dh p rid).rph = s.rph := rfl
@[simp] theorem consumed_prev (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) : (s.consumed r dh p rid).prev = s.prev := rfl
@[simp] theorem consumed_nxt (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) :
    (s.consumed r dh p rid).nxt = some ⟨PK.new (.roll s.cur.sec dh) (s.cur.g + 1), p⟩ := rfl
@[simp] theorem consumed_npn (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) : (s.consumed r dh p rid).npn = s.npn := rfl
@[simp] theorem consumed_promAt (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) : (s.consumed r dh p rid).promAt = s.promAt := rfl
@[simp] theorem consumed_ders (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) :
    (s.consumed r dh p rid).ders = s.ders ++ [⟨false, rid, dh, 0⟩] := rfl
@[simp] theorem consumed_chg (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) : (s.consumed r dh p rid).chg = s.chg + 1 := by
  simp [Node.chg]

@[simp] theorem staged_roll (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) : (s.staged r a dh rid l).roll = r := rfl
@[simp] theorem staged_ctr (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) : (s.staged r a dh rid l).ctr = s.ctr + 1 := rfl
@[simp] theorem staged_sk (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) : (s.staged r a dh rid l).sk = s.sk := rfl
@[simp] theorem staged_sph (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) : (s.staged r a dh rid l).sph = s.sph := rfl
@[simp] theorem staged_stg (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) :
    (s.staged r a dh rid l).stg = some (PK.new (.roll s.sk.sec dh) (s.sk.g + 1)) := rfl
@[simp] theorem staged_out (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) : (s.staged r a dh rid l).out = some a := rfl
@[simp] theorem staged_cur (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) : (s.staged r a dh rid l).cur = s.cur := rfl
@[simp] theorem staged_rph (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) : (s.staged r a dh rid l).rph = s.rph := rfl
@[simp] theorem staged_prev (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) : (s.staged r a dh rid l).prev = s.prev := rfl
@[simp] theorem staged_nxt (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) :
    (s.staged r a dh rid l).nxt = some ⟨PK.new (.roll s.cur.sec dh) (s.cur.g + 1), 0⟩ := rfl
@[simp] theorem staged_npn (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) : (s.staged r a dh rid l).npn = s.npn := rfl
@[simp] theorem staged_promAt (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) : (s.staged r a dh rid l).promAt = s.promAt := rfl
@[simp] theorem staged_ders (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) :
    (s.staged r a dh rid l).ders = s.ders ++ [⟨true, rid, dh, l⟩] := rfl
@[simp] theorem staged_chg (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) : (s.staged r a dh rid l).chg = s.chg + 1 := by
  simp [Node.chg]

theorem dhs_ders_snoc (s : Node) (e : Der) : (s.ders ++ [e]).map Der.dh = dhs s ++ [e.dh] := by simp [dhs]

theorem take_len_self {α : Type} (l : List α) (g : Nat) (h : g = l.length) : l.take g = l := by
  subst h; exact List.take_length

@[simp] theorem dhs_consumed (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) :
    dhs (s.consumed r dh p rid) = dhs s ++ [dh] := by simp [dhs]
@[simp] theorem dhs_staged (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) :
    dhs (s.staged r a dh rid l) = dhs s ++ [dh] := by simp [dhs]
@[simp] theorem lastRid_consumed (s : Node) (r : Roll) (dh : T) (p : Nat) (rid : T) :
    (s.consumed r dh p rid).lastRid = none := by simp [Node.lastRid]
@[simp] theorem lastRid_staged (s : Node) (r : Roll) (a : Msg) (dh : T) (rid : T) (l : Nat) :
    (s.staged r a dh rid l).lastRid = some rid := by simp [Node.lastRid]

theorem NodeInv.consumed {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (seed : Atom) (rq : Msg) (b : Atom)
    (pspn : Nat) (hst : s.roll.st = .req seed rq) (hnoreq : ∀ m', s.out = some m' → m'.answer = true) :
    NodeInv P n (s.consumed s.roll.completed (.bound (.id rq.share) (Dh seed b)) pspn rq.share) := by
  have hr := h.req (by simp [Roll.isIdle, hst])
  have hc1 := NodeInv.cnSk h
  have hc2 := NodeInv.cnCur h
  simp only [hr.1, hr.2, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc1 hc2
  obtain ⟨hps1, k, hps2, hps3⟩ := h.pendSeed seed rq hst
  have hdl : (dhs s).length = s.chg := dhs_length s
  have e1 : (dhs s).take s.sk.g = dhs s := take_len_self _ _ (by omega)
  have e2 : (dhs s).take s.cur.g = dhs s := take_len_self _ _ (by omega)
  have hsp := parity_succ _ _ (NodeInv.phS h)
  have tk1 : List.take (s.sk.g + 1) (dhs s ++ [.bound (.id rq.share) (Dh seed b)]) = dhs s ++ [.bound (.id rq.share) (Dh seed b)] :=
    List.take_of_length_le (by simp; omega)
  have tk2 : List.take (s.cur.g + 1) (dhs s ++ [.bound (.id rq.share) (Dh seed b)]) = dhs s ++ [.bound (.id rq.share) (Dh seed b)] :=
    List.take_of_length_le (by simp; omega)
  node_inv
  case dialer => simpa [Roll.completed] using NodeInv.dialer h
  case kfSk =>
    simp only [consumed_sk, PK.new, dhs_consumed]
    rw [tk1, rollAll_snoc, ← e1, ← NodeInv.kfSk h]
  case kfCur =>
    simp only [consumed_cur, dhs_consumed]
    rw [List.take_append_of_le_length (by omega)]
    exact NodeInv.kfCur h
  case kfStg => intro k hk; simp only [consumed_stg, hr.2] at hk; simp at hk
  case kfNxt =>
    intro x hx
    simp only [consumed_nxt, Option.some.injEq] at hx
    subst hx
    refine ⟨?_, rfl⟩
    simp only [PK.new, dhs_consumed, consumed_cur]
    rw [tk2, rollAll_snoc, ← e2, ← NodeInv.kfCur h]
  case kfPrev =>
    intro pv hpv
    simp only [consumed_prev] at hpv
    obtain ⟨a1, a2⟩ := NodeInv.kfPrev h pv hpv
    simp only [dhs_consumed, consumed_cur]
    refine ⟨?_, a2⟩
    rw [List.take_append_of_le_length (by omega)]
    exact a1
  case cnSk => simp only [consumed_chg, consumed_sk, consumed_stg, hr.2, PK.new]; simp; omega
  case cnCur => simp only [consumed_chg, consumed_cur, consumed_nxt]; simp; omega
  case cnSN => intro hh; simp only [consumed_stg, hr.2] at hh; simp at hh
  case phS => simp only [consumed_sph, consumed_sk, PK.new]; exact hsp
  case phR => have t := NodeInv.phR h; exact t
  case req => intro hh; simp [Roll.completed, Roll.isIdle] at hh
  case hold => have t := NodeInv.hold h; exact t
  case rolls =>
    simp only [consumed_chg, consumed_roll, Roll.completed]
    rw [NodeInv.rolls h]; exact rolls_inc _
  case derOK => exact DerOK.snoc (NodeInv.derOK h) _ (Or.inr ⟨rfl, k, by simp [hps1, hps2, Msg.req]⟩)
  case lastInv => simp [Roll.completed]
  case stgLast => intro hh; simp only [consumed_stg, hr.2] at hh; simp at hh
  case noDup => exact NoDupStg.snoc (NodeInv.noDup h) _ (by intro x _ _ hd; simp at hd)
  case derLvl => exact DerLvl.snoc (NodeInv.derLvl h) _ (by intro hd; simp at hd)
  case outMsg => have t := NodeInv.outMsg h; exact t
  case pendMsg => intro m hm; simp [Roll.pending, Roll.completed] at hm
  case lastMsg => intro sh a hl; simp [Roll.completed] at hl
  case lastAns => intro sh a hl; simp [Roll.completed] at hl
  case outReq =>
    intro m hm hq
    have := hnoreq m hm
    rw [hq] at this; simp at this
  case pendSeed => intro sd r hs; simp [Roll.completed] at hs
  case ansLast => have t := NodeInv.ansLast h; exact t

theorem NodeInv.staged {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (m : Msg) (lvl : Nat) (b : Atom)
    {c : Nat} (hmok : MsgOK (!n) c m) (hm : m.answer = false) (hsh : m.share = .pub b)
    (hnx : s.nxt = none) (hnd : s.roll.isDup m = false) (hlvl : lvl = s.ders.length ∨ lvl + 1 = s.ders.length) :
    NodeInv P n (s.staged (s.roll.answeredWith m.share (answerTo n s.ctr s.npn m.share b))
      (answerTo n s.ctr s.npn m.share b) (.bound (.id m.share) (Dh (atomOf n s.ctr) b)) m.share lvl) := by
  have hstg : s.stg = none := by
    cases hs : s.stg with
    | none => rfl
    | some k => have := NodeInv.cnSN h (by simp [hs]); simp [hnx] at this
  have hc1 := NodeInv.cnSk h
  have hc2 := NodeInv.cnCur h
  simp only [hnx, hstg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc1 hc2
  obtain ⟨_, k', hk1, _⟩ := hmok.req hm
  have hb : b = atomOf (!n) k' := by rw [hsh] at hk1; exact T.pub.inj hk1
  have hdl : (dhs s).length = s.chg := dhs_length s
  have e1 : (dhs s).take s.sk.g = dhs s := take_len_self _ _ (by omega)
  have e2 : (dhs s).take s.cur.g = dhs s := take_len_self _ _ (by omega)
  have tk1 : List.take (s.sk.g + 1) (dhs s ++ [.bound (.id m.share) (Dh (atomOf n s.ctr) b)]) =
      dhs s ++ [.bound (.id m.share) (Dh (atomOf n s.ctr) b)] :=
    List.take_of_length_le (by simp; omega)
  have tk2 : List.take (s.cur.g + 1) (dhs s ++ [.bound (.id m.share) (Dh (atomOf n s.ctr) b)]) =
      dhs s ++ [.bound (.id m.share) (Dh (atomOf n s.ctr) b)] :=
    List.take_of_length_le (by simp; omega)
  have hansok : MsgOK n (s.ctr + 1) (answerTo n s.ctr s.npn m.share b) :=
    ⟨fun a => by simp [answerTo] at a,
     fun _ => ⟨s.ctr, k', rfl, by omega, by simp [answerTo, hk1], by simp [answerTo, hk1, hb]⟩⟩
  node_inv
  case dialer => simpa [Roll.answeredWith] using NodeInv.dialer h
  case kfSk =>
    simp only [staged_sk, dhs_staged]
    rw [List.take_append_of_le_length (by omega)]
    exact NodeInv.kfSk h
  case kfCur =>
    simp only [staged_cur, dhs_staged]
    rw [List.take_append_of_le_length (by omega)]
    exact NodeInv.kfCur h
  case kfStg =>
    intro kk hk
    simp only [staged_stg, Option.some.injEq] at hk
    subst hk
    refine ⟨?_, rfl⟩
    simp only [PK.new, dhs_staged, staged_sk]
    rw [tk1, rollAll_snoc, ← e1, ← NodeInv.kfSk h]
  case kfNxt =>
    intro x hx
    simp only [staged_nxt, Option.some.injEq] at hx
    subst hx
    refine ⟨?_, rfl⟩
    simp only [PK.new, dhs_staged, staged_cur]
    rw [tk2, rollAll_snoc, ← e2, ← NodeInv.kfCur h]
  case kfPrev =>
    intro pv hpv
    simp only [staged_prev] at hpv
    obtain ⟨a1, a2⟩ := NodeInv.kfPrev h pv hpv
    simp only [dhs_staged, staged_cur]
    refine ⟨?_, a2⟩
    rw [List.take_append_of_le_length (by omega)]
    exact a1
  case cnSk => simp only [staged_chg, staged_sk, staged_stg]; simp; omega
  case cnCur => simp only [staged_chg, staged_cur, staged_nxt]; simp; omega
  case cnSN => intro _; rfl
  case phS => have t := NodeInv.phS h; exact t
  case phR => have t := NodeInv.phR h; exact t
  case req => intro hh; simp [Roll.answeredWith, Roll.isIdle] at hh
  case hold => have t := NodeInv.hold h; exact t
  case rolls =>
    simp only [staged_chg, staged_roll, Roll.answeredWith]
    rw [NodeInv.rolls h]; exact rolls_inc _
  case derOK =>
    obtain ⟨_, k'', hk'', _⟩ := hmok.req hm
    exact DerOK.snoc (NodeInv.derOK h) _ (Or.inl ⟨rfl, k'', hk''⟩)
  case lastInv => simp [Roll.answeredWith]
  case stgLast => intro _; exact ⟨⟨true, m.share, .bound (.id m.share) (Dh (atomOf n s.ctr) b), lvl⟩, by simp, rfl⟩
  case noDup =>
    refine NoDupStg.snoc (NodeInv.noDup h) _ ?_
    intro x hx hxs hds
    have hli := NodeInv.lastInv h
    have : s.lastRid = some x.rid := by simp [Node.lastRid, hx, hxs]
    rw [this] at hli
    intro heq
    have hl : ∃ a, s.roll.last = some (m.share, a) := by
      cases hl : s.roll.last with
      | none => rw [hl] at hli; simp at hli
      | some y =>
        obtain ⟨y1, y2⟩ := y
        rw [hl] at hli
        simp at hli
        exact ⟨y2, by rw [show y1 = m.share from hli.trans heq.symm]⟩
    exact absurd ((isDup_iff _ _).2 hl) (by simp [hnd])
  case derLvl => exact DerLvl.snoc (NodeInv.derLvl h) _ (fun _ => hlvl)
  case outMsg => intro mm hmm; simp only [staged_out, Option.some.injEq] at hmm; subst hmm; exact hansok
  case pendMsg => intro mm hmm; simp [Roll.pending, Roll.answeredWith] at hmm
  case lastMsg =>
    intro sh a hl
    simp only [staged_roll, Roll.answeredWith, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨_, rfl⟩ := hl
    simpa using hansok
  case lastAns =>
    intro sh a hl
    simp only [staged_roll, Roll.answeredWith, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨_, rfl⟩ := hl
    rfl
  case outReq => intro mm hmm hq; simp only [staged_out, Option.some.injEq] at hmm; subst hmm; simp [answerTo] at hq
  case pendSeed => intro sd r hs; simp [Roll.answeredWith] at hs
  case ansLast =>
    intro mm hmm
    have t := NodeInv.ansLast h mm hmm
    exact ⟨t.1.mono (by show s.ctr ≤ s.ctr + 1; omega), t.2⟩

theorem NodeInv.dupOut {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (sh : T) (ans : Msg)
    (hl : s.roll.last = some (sh, ans)) : NodeInv P n { s with out := some ans } := by
  node_inv
  case outMsg => intro m hm; simp only [Option.some.injEq] at hm; subst hm; exact NodeInv.lastMsg h sh ans hl
  case outReq =>
    intro m hm hq; simp only [Option.some.injEq] at hm; subst hm
    rw [NodeInv.lastAns h sh ans hl] at hq; simp at hq
  all_goals close_same h

/-- `RekeyRx` keeps the local invariant, for a body from the peer (`MsgOK`) whose request level is in the window. -/
theorem NodeInv.rekeyRx {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (m : Msg) (lvl : Nat) {c : Nat}
    (hmok : MsgOK (!n) c m) (hlvl : lvl = s.ders.length ∨ lvl + 1 = s.ders.length)
    (hnoreq : m.answer = true → ∀ m', s.out = some m' → m'.answer = true) :
    NodeInv P n (rekeyRx s m n lvl).s := by
  by_cases ha : m.answer = true
  · cases hok : (s.roll.onAnswer m).2 with
    | ok c' =>
      obtain ⟨seed, rq, b, hst, _, hsh, he, _⟩ := onAnswer_ok_st s.roll m c' hok
      rw [rekeyRx_consume s m n lvl seed rq b ha hst hsh he]
      exact h.consumed seed rq b m.spn hst (hnoreq ha)
    | error e =>
      rw [rekeyRx_answer_refused s m n lvl ha (by intro c'' hc; rw [hok] at hc; cases hc)]
      exact h
  · have ha' : m.answer = false := by simpa using ha
    by_cases hg : gated s m = true
    · rw [rekeyRx_gated s m n lvl ha' hg]; exact h
    · have hg' : gated s m = false := by simpa using hg
      rcases onRequest_split s.roll m ha' with hd | ⟨hn, hb⟩ | ⟨hn, hf⟩
      · obtain ⟨ans, hl⟩ := isDup_last s.roll m hd
        rw [rekeyRx_dup s m n lvl ha' hg' ans hl]
        exact h.dupOut _ _ hl
      · rw [rekeyRx_busy s m n lvl ha' hg' hn hb]; exact h
      · obtain ⟨_, k, hk, _⟩ := hmok.req ha'
        rw [rekeyRx_stage s m n lvl (atomOf (!n) k) ha' hg' hn hf hk]
        exact h.staged m lvl (atomOf (!n) k) hmok ha' hk (gated_nodup P s m ha' hn hg') hn hlvl

theorem NodeInv.pending_req {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) {m : Msg}
    (hp : s.roll.pending = some m) : ∃ seed, m = Msg.req (.pub seed) := by
  unfold Roll.pending at hp
  cases hst : s.roll.st with
  | idle => simp [hst] at hp
  | req seed rq =>
    simp only [hst, Option.some.injEq] at hp
    subst hp
    exact ⟨seed, (h.pendSeed seed _ hst).1⟩

theorem NodeInv.pending_answer {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) {m : Msg}
    (hp : s.roll.pending = some m) : m.answer = false := by
  obtain ⟨seed, rfl⟩ := h.pending_req hp; rfl

/-- The depth of a key is its generation. -/
theorem NodeInv.depths {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) :
    s.sk.sec.depth = s.sk.g ∧ s.cur.sec.depth = s.cur.g ∧ (∀ k, s.stg = some k → k.sec.depth = k.g) ∧
    (∀ x, s.nxt = some x → x.k.sec.depth = x.k.g) ∧ (∀ pv, s.prev = some pv → pv.k.sec.depth = pv.k.g) := by
  have hdl : (dhs s).length = s.chg := dhs_length s
  have h1 := NodeInv.cnSk h
  have h2 := NodeInv.cnCur h
  have hl : ∀ g, g ≤ s.chg → ((dhs s).take g).length = g := fun g hg => by simp [hdl]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [NodeInv.kfSk h, depth_rollAll, hl _ (by split at h1 <;> omega)]
  · rw [NodeInv.kfCur h, depth_rollAll, hl _ (by split at h2 <;> omega)]
  · intro k hk
    obtain ⟨a1, a2⟩ := NodeInv.kfStg h k hk
    rw [a1, depth_rollAll, a2, hl _ (by simp only [hk, Option.isSome_some, ↓reduceIte] at h1; omega)]
  · intro x hx
    obtain ⟨a1, a2⟩ := NodeInv.kfNxt h x hx
    rw [a1, depth_rollAll, a2, hl _ (by simp only [hx, Option.isSome_some, ↓reduceIte] at h2; omega)]
  · intro pv hpv
    obtain ⟨a1, a2⟩ := NodeInv.kfPrev h pv hpv
    rw [a1, depth_rollAll, hl _ (by split at h2 <;> omega)]

theorem NodeInv.pending_chg {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) {m : Msg}
    (hp : s.roll.pending = some m) : s.chg = s.sk.g ∧ s.chg = s.cur.g := by
  have hi : s.roll.isIdle = false := by
    unfold Roll.pending at hp
    cases hst : s.roll.st with
    | idle => simp [hst] at hp
    | req sd rq => simp [Roll.isIdle, hst]
  have hr := h.req hi
  have c1 := NodeInv.cnSk h
  have c2 := NodeInv.cnCur h
  simp only [hr.1, hr.2, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at c1 c2
  exact ⟨c1, c2⟩

/-- The counts in a form `omega` takes. -/
theorem NodeInv.cn {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) :
    (s.stg.isSome = true → s.chg = s.sk.g + 1) ∧ (s.stg.isSome = false → s.chg = s.sk.g) ∧
    (s.nxt.isSome = true → s.chg = s.cur.g + 1) ∧ (s.nxt.isSome = false → s.chg = s.cur.g) ∧
    (s.stg.isSome = true → s.nxt.isSome = true) := by
  have c1 := NodeInv.cnSk h
  have c2 := NodeInv.cnCur h
  have c3 := NodeInv.cnSN h
  refine ⟨fun a => ?_, fun a => ?_, fun a => ?_, fun a => ?_, c3⟩
  · rw [a] at c1; simpa using c1
  · rw [a] at c1; simpa using c1
  · rw [a] at c2; simpa using c2
  · rw [a] at c2; simpa using c2

theorem Option.isSome_false_iff_none {α : Type} (o : Option α) : o.isSome = false ↔ o = none := by
  cases o <;> simp

end Vinc.KeyRollSys
