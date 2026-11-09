import Vinc.KeyRollSysThm

/-!
# Action properties of the key roll system

The properties of one step: what a delivered packet is accepted under, what a forged phase bit costs, how the
generations move, and what a duplicate request or a collision does.
-/

namespace Vinc.KeyRollSys
open Vinc.KeyRoll

theorem expire_first (s : Node) (t : Nat) : (s.expire t).first = s.first := by rcases expire_cases s t with e | e <;> rw [e]
theorem expire_rph (s : Node) (t : Nat) : (s.expire t).rph = s.rph := by rcases expire_cases s t with e | e <;> rw [e]

theorem expire_prev (s : Node) (t : Nat) :
    (s.expire t).prev = (match s.prev with | some pv => if pv.dl ≤ t then none else some pv | none => none) := by
  cases hp : s.prev with
  | none => simp [Node.expire, hp]
  | some pv => by_cases h : pv.dl ≤ t <;> simp [Node.expire, hp, h]

/-- A packet is accepted exactly when its secret is the one of the slot it selects. -/
theorem recvKeys_acc_eq (s : Node) (p : Pkt) (t pto : Nat) :
    (s.recvKeys p false t pto).acc =
      decide ((s.expire t).slotSec ((s.expire t).select p.ph p.pn) = some p.sec) := by
  unfold Node.recvKeys
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
  generalize s.expire t = s1
  cases hsel : s1.select p.ph p.pn <;> simp only [Node.slotSec]
  · by_cases hok : (decide (s1.cur.sec = p.sec)) = true <;> simp_all
  · by_cases hx : (∃ a, s1.nxt = some a ∧ a.k.sec = p.sec) <;> simp [hx]
  · by_cases hx : (∃ a, s1.prev = some a ∧ a.k.sec = p.sec) <;> simp [hx]
  · simp

/-- The receiver holds the key the packet was sealed under: the current one, the previous one within its hold and
below the first number of the phase, or the staged next one at or above its floor (`Holds`). -/
def Node.holds (s : Node) (p : Pkt) (t : Nat) : Prop :=
  p.sec = s.cur.sec ∨
  (∃ pv, s.prev = some pv ∧ t < pv.dl ∧ p.pn < s.first ∧ p.sec = pv.k.sec ∧
      ¬ ∃ x, s.nxt = some x ∧ x.floor ≤ p.pn) ∨
  (∃ x, s.nxt = some x ∧ x.floor ≤ p.pn ∧ p.sec = x.k.sec)

theorem par_ne (a : Nat) : decide ((a + 1) % 2 = 1) ≠ decide (a % 2 = 1) := by
  by_cases h : a % 2 = 1
  · have : ¬ (a + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (a + 1) % 2 = 1 := by omega
    simp [h, this]

/-- A packet is accepted iff the receiver holds the key it was sealed under (`AcceptIff`). -/
theorem acceptIff {P : Params} {S : Sys} (hr : Reach P S) {n : Bool} {p : Pkt}
    (hp : p ∈ S.net) :
    ((S.nd n).recvKeys p false S.now P.pto).acc = true ↔ (S.nd n).holds p S.now := by
  have I := hr.inv
  have hph := I.netPh p hp
  have hn := I.node n
  have hdep := hn.depths
  rw [recvKeys_acc_eq, decide_eq_true_eq]
  generalize hs : S.nd n = s at hn hdep ⊢
  generalize S.now = t
  have hrph := hn.phR
  simp only [Node.select, expire_rph, expire_nxt, expire_first, expire_prev, expire_cur]
  have hpd : ∀ pv, s.prev = some pv → p.sec = pv.k.sec → p.ph = decide ((s.cur.g - 1) % 2 = 1) := by
    intro pv hpv he
    have := (hn.kfPrev pv hpv).2
    rw [hph, he, hdep.2.2.2.2 pv hpv]
    congr 2; omega
  have hxd : ∀ x, s.nxt = some x → p.sec = x.k.sec → p.ph = decide ((s.cur.g + 1) % 2 = 1) := by
    intro x hx he
    rw [hph, he, hdep.2.2.2.1 x hx, (hn.kfNxt x hx).2]
  have hcd : p.sec = s.cur.sec → p.ph = s.rph := by
    intro he; rw [hph, he, hdep.2.1, hrph]
  by_cases hpar : p.ph = s.rph
  · simp only [hpar, beq_self_eq_true, ↓reduceIte, Node.slotSec, Option.some.injEq, expire_cur]
    constructor
    · intro h; exact Or.inl h.symm
    · rintro (h | ⟨pv, hpv, _, _, he, _⟩ | ⟨x, hx, _, he⟩)
      · exact h.symm
      · exfalso
        have h1 := (hrph.symm.trans hpar.symm).trans (hpd pv hpv he)
        have hcg := (hn.kfPrev pv hpv).2
        have key := par_ne (s.cur.g - 1)
        rw [Nat.sub_add_cancel (by omega)] at key
        exact key h1
      · exfalso
        have h1 := (hrph.symm.trans hpar.symm).trans (hxd x hx he)
        exact par_ne _ h1.symm
  · have hbeq : (p.ph == s.rph) = false := by simpa using hpar
    have hnc : ¬ (p.sec = s.cur.sec) := fun he => hpar (hcd he)
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    cases hnx : s.nxt with
    | none =>
      cases hpv : s.prev with
      | none => simp [Node.slotSec, Node.holds, hnx, hpv, hnc]
      | some pv =>
        by_cases h1 : t < pv.dl <;> by_cases h2 : p.pn < s.first
        · have h1n : ¬ pv.dl ≤ t := Nat.not_le.2 h1
          simp [Node.slotSec, Node.holds, hnx, hpv, hnc, h1, h1n, h2, expire_prev, expire_nxt, eq_comm]
        all_goals
          first
          | (have h1n : pv.dl ≤ t := Nat.not_lt.1 h1
             simp [Node.slotSec, Node.holds, hnx, hpv, hnc, h1, h1n, h2, expire_prev, expire_nxt])
          | (have h1n : ¬ pv.dl ≤ t := Nat.not_le.2 h1
             simp [Node.slotSec, Node.holds, hnx, hpv, hnc, h1, h1n, h2, expire_prev, expire_nxt])
    | some x =>
      by_cases hf : x.floor ≤ p.pn
      · cases hpv : s.prev with
        | none => simp [Node.slotSec, Node.holds, hnx, hpv, hnc, hf, expire_prev, expire_nxt, eq_comm]
        | some pv =>
          by_cases h1 : t < pv.dl
          · have h1n : ¬ pv.dl ≤ t := Nat.not_le.2 h1
            simp [Node.slotSec, Node.holds, hnx, hpv, hnc, hf, h1, h1n, expire_prev, expire_nxt, eq_comm]
          · have h1n : pv.dl ≤ t := Nat.not_lt.1 h1
            simp [Node.slotSec, Node.holds, hnx, hpv, hnc, hf, h1, h1n, expire_prev, expire_nxt, eq_comm]
      · cases hpv : s.prev with
        | none => simp [Node.slotSec, Node.holds, hnx, hpv, hnc, hf, expire_prev, expire_nxt]
        | some pv =>
          by_cases h1 : t < pv.dl <;> by_cases h2 : p.pn < s.first
          · have h1n : ¬ pv.dl ≤ t := Nat.not_le.2 h1
            simp [Node.slotSec, Node.holds, hnx, hpv, hnc, hf, h1, h1n, h2, expire_prev, expire_nxt, eq_comm]
          all_goals
            first
            | (have h1n : pv.dl ≤ t := Nat.not_lt.1 h1
               simp [Node.slotSec, Node.holds, hnx, hpv, hnc, hf, h1, h1n, h2, expire_prev, expire_nxt])
            | (have h1n : ¬ pv.dl ≤ t := Nat.not_le.2 h1
               simp [Node.slotSec, Node.holds, hnx, hpv, hnc, hf, h1, h1n, h2, expire_prev, expire_nxt])

/-- A packet is never accepted under a key of another secret: the secret of an accepted packet is one the receiver
holds, the previous one only before its deadline (`NeverOtherKey`). -/
theorem neverOtherKey (s : Node) (p : Pkt) (f : Bool) (t pto : Nat) (hacc : (s.recvKeys p f t pto).acc = true) :
    p.sec = s.cur.sec ∨ (∃ pv, s.prev = some pv ∧ t < pv.dl ∧ p.sec = pv.k.sec) ∨
      (∃ x, s.nxt = some x ∧ p.sec = x.k.sec) := by
  obtain ⟨_, hc⟩ := recvKeys_acc_cases s p f t pto hacc
  rcases hc with ⟨hcs, _⟩ | ⟨pv, hpv, hps, _⟩ | ⟨x, hx, hxs, _⟩
  · left; rw [expire_cur] at hcs; exact hcs.symm
  · right; left
    rw [expire_prev] at hpv
    cases hp0 : s.prev with
    | none => rw [hp0] at hpv; simp at hpv
    | some q =>
      rw [hp0] at hpv
      by_cases h : q.dl ≤ t
      · simp [h] at hpv
      · simp [h] at hpv
        subst hpv
        exact ⟨q, rfl, Nat.not_le.1 h, hps.symm⟩
  · right; right; rw [expire_nxt] at hx; exact ⟨x, hx, hxs.symm⟩

theorem select_prev_isSome (s : Node) (ph : Bool) (pn : Nat) (h : s.select ph pn = .prev) : s.prev.isSome = true := by
  unfold Node.select at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp_all
        · simp at h
    · split at h
      · simp_all
      · simp at h

theorem select_next_isSome (s : Node) (ph : Bool) (pn : Nat) (h : s.select ph pn = .next) : s.nxt.isSome = true := by
  unfold Node.select at h
  split at h
  · simp at h
  · split at h
    · simp_all
    · split at h <;> simp at h

theorem recvKeys_sel (s : Node) (p : Pkt) (f : Bool) (t pto : Nat) :
    (s.recvKeys p f t pto).sel = (s.expire t).select (if f then !p.ph else p.ph) p.pn := by
  unfold Node.recvKeys
  dsimp only
  generalize s.expire t = s1
  generalize s1.select (if f = true then !p.ph else p.ph) p.pn = sel
  cases sel <;> simp <;> split <;> rfl

/-- The previous key is accepted before its deadline and refused from it on (`OldKeyOnePTO`). -/
theorem oldKeyOnePTO (s : Node) (p : Pkt) (f : Bool) (t pto : Nat) (hsel : (s.recvKeys p f t pto).sel = .prev) :
    ∃ pv, s.prev = some pv ∧ t < pv.dl := by
  rw [recvKeys_sel] at hsel
  have := select_prev_isSome _ _ _ hsel
  rw [expire_prev] at this
  cases hp0 : s.prev with
  | none => rw [hp0] at this; simp at this
  | some q =>
    rw [hp0] at this
    by_cases h : q.dl ≤ t
    · simp [h] at this
    · exact ⟨q, rfl, Nat.not_le.1 h⟩

/-- A key with its failed-open counter cleared. -/
def PK.zero (k : PK) : PK := { k with fc := 0 }

/-- The node with every failed-open counter cleared (`Strip`). -/
def Node.strip (s : Node) : Node :=
  { s with cur := s.cur.zero, sk := s.sk.zero, stg := s.stg.map PK.zero,
           prev := s.prev.map fun x => { x with k := x.k.zero },
           nxt := s.nxt.map fun x => { x with k := x.k.zero } }

/-- The failed opens counted against the keys that open packets (`FCs`). -/
def Node.fcs (s : Node) : Nat :=
  s.cur.fc + s.sk.fc + (s.prev.map fun x => x.k.fc).getD 0 + (s.nxt.map fun x => x.k.fc).getD 0

/-- The counter of the slot a packet is tried with. -/
def Node.slotFc (s : Node) : Sel → Nat
  | .cur => s.cur.fc
  | .next => (s.nxt.map fun x => x.k.fc).getD 0
  | .prev => (s.prev.map fun x => x.k.fc).getD 0
  | .err => 0

/-- A forged phase bit is never accepted, costs at most one failed open (exactly one while the counter of the key
is below its saturation), and changes nothing else (`ForgedCostsOneOpen`, the keys layer part). -/
theorem forgedCostsOneOpen (s : Node) (p : Pkt) (t pto : Nat) :
    (s.recvKeys p true t pto).acc = false ∧
    (s.recvKeys p true t pto).s.strip = (s.expire t).strip ∧
    (s.recvKeys p true t pto).s.seen = (s.expire t).seen ∧
    ((s.recvKeys p true t pto).sel = .err → (s.recvKeys p true t pto).s.fcs = (s.expire t).fcs) ∧
    ((s.recvKeys p true t pto).sel ≠ .err →
      (s.recvKeys p true t pto).s.fcs + (s.expire t).slotFc (s.recvKeys p true t pto).sel =
        (s.expire t).fcs + Record.inc ((s.expire t).slotFc (s.recvKeys p true t pto).sel)) := by
  unfold Node.recvKeys
  dsimp only
  generalize s.expire t = s1
  generalize hsel : s1.select (if true = true then !p.ph else p.ph) p.pn = sel
  have hn := select_next_isSome s1 (if true = true then !p.ph else p.ph) p.pn
  have hpv := select_prev_isSome s1 (if true = true then !p.ph else p.ph) p.pn
  rw [hsel] at hn hpv
  cases sel <;> simp [Node.bumpFC, Node.strip, Node.fcs, Node.slotFc, PK.zero]
  · omega
  · have := hn rfl
    cases hx : s1.nxt <;> simp [hx] at this ⊢ <;> omega
  · have := hpv rfl
    cases hx : s1.prev <;> simp [hx] at this ⊢ <;> omega

/-- What `Deliver` does with the body of the packet. -/
def rkOf (r : Node × Bool) (sel : Sel) (p : Pkt) (n : Bool) : Rk :=
  match p.pl with
  | some m => if r.2 && acts m sel then rekeyRx r.1 m n p.sec.depth else ⟨r.1, none, none⟩
  | none => ⟨r.1, none, none⟩

theorem deliverUpd_nd (P : Params) (S : Sys) (n : Bool) (p : Pkt) (f : Bool) :
    (deliverUpd P S n p f).nd n = (rkOf ((S.nd n).afterRecv P p f S.now) ((S.nd n).rxSel P p f S.now) p n).s ∧
    (deliverUpd P S n p f).nd (!n) = S.nd (!n) ∧ (deliverUpd P S n p f).net = S.net ∧
    (deliverUpd P S n p f).slog = S.slog ∧ (deliverUpd P S n p f).breq = S.breq := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · unfold deliverUpd rkOf; dsimp only; exact Sys.setNode_same _ _ _
  · unfold deliverUpd; dsimp only; exact Sys.setNode_not _ _ _

/-- A forged phase bit changes the receiving node as the keys layer says and nothing else
(`ForgedCostsOneOpen`, the system part). -/
theorem forged_deliver (P : Params) (S : Sys) (n : Bool) (p : Pkt) :
    (deliverUpd P S n p true).nd n = ((S.nd n).recvKeys p true S.now P.pto).s ∧
    (deliverUpd P S n p true).nd (!n) = S.nd (!n) ∧ (deliverUpd P S n p true).net = S.net ∧
    (deliverUpd P S n p true).comp = S.comp ∧ (deliverUpd P S n p true).stl = S.stl := by
  have hacc := (forgedCostsOneOpen (S.nd n) p S.now P.pto).1
  have hr : (S.nd n).afterRecv P p true S.now = (((S.nd n).recvKeys p true S.now P.pto).s, false) := by
    unfold Node.afterRecv; dsimp only; rw [hacc]; simp
  obtain ⟨a, b, c, _, _⟩ := deliverUpd_nd P S n p true
  refine ⟨?_, b, c, ?_, ?_⟩
  · rw [a, hr]; unfold rkOf; cases p.pl <;> rfl
  · unfold deliverUpd; dsimp only; rw [hr]; cases p.pl <;> simp [addOpt]
  · unfold deliverUpd; dsimp only; rw [hr]; cases p.pl <;> simp [addOpt]

/-- What the body of a packet can do to the keys and the staged next key of the node: it never moves the current
key, it moves the sending key by one only when it takes the answer to a request that is out, and it sets the staged
next key only when none was staged. -/
theorem rekeyRx_keys {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (m : Msg) (me : Bool) (lvl : Nat) :
    (rekeyRx s m me lvl).s.cur = s.cur ∧
    ((rekeyRx s m me lvl).s.sk = s.sk ∨ ((rekeyRx s m me lvl).s.sk.g = s.sk.g + 1 ∧ s.roll.isIdle = false)) ∧
    ((rekeyRx s m me lvl).s.nxt = s.nxt ∨ s.nxt = none) ∧
    ((rekeyRx s m me lvl).s.sk.sec = s.sk.sec ∨ s.roll.isIdle = false) ∧
    ((rekeyRx s m me lvl).s.ders = s.ders ∨ s.roll.isIdle = false ∨ s.nxt = none) := by
  unfold rekeyRx
  by_cases ha : m.answer = true
  · simp only [ha, ↓reduceIte]
    cases hoa : s.roll.onAnswer m
    rename_i r res
    cases res with
    | error e => cases s.roll.pending <;> simp
    | ok c =>
      obtain ⟨dh, pspn⟩ := c
      have hok : (s.roll.onAnswer m).2 = .ok (dh, pspn) := by rw [hoa]
      obtain ⟨seed, rq, b, hst, _⟩ := onAnswer_ok_st s.roll m _ hok
      have hid : s.roll.isIdle = false := by simp [Roll.isIdle, hst]
      have hp : s.roll.pending = some rq := by simp [Roll.pending, hst]
      simp only [hp]
      have hnx := (h.req hid).1
      simp [Node.consumed, PK.new, hid, hnx]
  · have ha' : m.answer = false := by simpa using ha
    simp only [ha, Bool.false_eq_true, ↓reduceIte]
    by_cases hg : gated s m = true
    · simp [hg]
    · have hg' : gated s m = false := by simpa using hg
      simp only [hg, Bool.false_eq_true, ↓reduceIte]
      cases hor : s.roll.onRequest m s.npn (some (atomOf me s.ctr))
      rename_i r res
      cases res with
      | error e => simp
      | ok c =>
        obtain ⟨ans, odh⟩ := c
        cases odh with
        | none => simp
        | some dh =>
          have hn : s.nxt = none := by
            by_cases hd : s.roll.isDup m = true
            · exfalso
              -- a duplicate gives no Diffie-Hellman value
              obtain ⟨a, hl⟩ := isDup_last s.roll m hd
              rw [onRequest_dup s.roll m s.npn _ m.share a hl rfl ha'] at hor
              simp at hor
            · exact gated_nodup P s m ha' (by simpa using hd) hg'
          simp [Node.staged, hn]

/-- The sending and receiving generations of a node only move forward, by one, in one delivery. -/
theorem deliver_gen {P : Params} {n : Bool} {s0 : Node} (h : NodeInv P n s0) (p : Pkt) (f : Bool) (now : Nat) :
    ((rkOf (s0.afterRecv P p f now) (s0.rxSel P p f now) p n).s.sk.g = s0.sk.g ∨
        (rkOf (s0.afterRecv P p f now) (s0.rxSel P p f now) p n).s.sk.g = s0.sk.g + 1) ∧
      ((rkOf (s0.afterRecv P p f now) (s0.rxSel P p f now) p n).s.cur.g = s0.cur.g ∨
        (rkOf (s0.afterRecv P p f now) (s0.rxSel P p f now) p n).s.cur.g = s0.cur.g + 1) := by
  have h1 := h.afterRecv (f := f) (t := now) p
  have rf := afterRecv_facts h p f now
  have hs1 : ((s0.afterRecv P p f now).1.sk.g = s0.sk.g ∨ (s0.afterRecv P p f now).1.sk.g = s0.sk.g + 1) ∧
      ((s0.afterRecv P p f now).1.cur.g = s0.cur.g ∨ (s0.afterRecv P p f now).1.cur.g = s0.cur.g + 1) ∧
      ((s0.afterRecv P p f now).1.sk.g = s0.sk.g + 1 → s0.stg.isSome = true) := by
    rcases rf.keys with k | ⟨k, _⟩
    · have k1 := k.1
      exact ⟨Or.inl k.1, Or.inl k.2.1, fun hh => by omega⟩
    · refine ⟨?_, Or.inr k.2.1, ?_⟩
      · by_cases hst : s0.stg.isSome = true
        · exact Or.inr (k.2.2.2.2.1 hst)
        · exact Or.inl (k.2.2.2.2.2 (by simpa using hst))
      · intro hh
        by_cases hst : s0.stg.isSome = true
        · exact hst
        · have k6 := k.2.2.2.2.2 (by simpa using hst); omega
  obtain ⟨a1, a2, a3⟩ := hs1
  unfold rkOf
  generalize (s0.afterRecv P p f now) = r at *
  obtain ⟨s1, pr⟩ := r
  simp only at *
  cases hpl : p.pl with
  | none => simp only; exact ⟨a1, a2⟩
  | some m =>
    by_cases hp : (pr && acts m (s0.rxSel P p f now)) = true
    · simp only [hp, if_true]
      obtain ⟨c1, c2, c3, c4, c5⟩ := rekeyRx_keys h1 m n p.sec.depth
      refine ⟨?_, by rw [c1]; exact a2⟩
      rcases c2 with c2 | ⟨c2, c2'⟩
      · rw [c2]; exact a1
      · right
        rw [c2]
        have hid : s0.roll.isIdle = false := by rw [← rf.roll]; exact c2'
        have hnst : s0.stg = none := (h.req hid).2
        have : s1.sk.g = s0.sk.g := by
          rcases a1 with e | e
          · exact e
          · have := a3 e; rw [hnst] at this; simp at this
        omega
    · simp only [hp]; simp; exact ⟨a1, a2⟩

/-- The sending generation and the receiving generation only move forward, by one (`GenMonotone`). -/
theorem genMonotone {P : Params} {S S' : Sys} (hr : Reach P S) (hs : Step P S S') (n : Bool) :
    ((S'.nd n).sk.g = (S.nd n).sk.g ∨ (S'.nd n).sk.g = (S.nd n).sk.g + 1) ∧
    ((S'.nd n).cur.g = (S.nd n).cur.g ∨ (S'.nd n).cur.g = (S.nd n).cur.g + 1) := by
  have I := hr.inv
  cases hs with
  | begin d hok =>
    rw [beginUpd_eq hok]
    dsimp only
    rcases Sys.setNode_cases S d n (beginNode (S.nd d) d) with e | ⟨rfl, e⟩
    · rw [e]; exact ⟨Or.inl rfl, Or.inl rfl⟩
    · rw [e]; exact ⟨Or.inl rfl, Or.inl rfl⟩
  | send d w hok =>
    obtain ⟨r, l, o, _, _, hlo, he⟩ := sendUpd_eq hok
    rw [he]
    dsimp only
    rcases Sys.setNode_cases S d n { S.nd d with out := o, reqAt := r, lastAns := l, npn := (S.nd d).npn + 1 } with e | ⟨rfl, e⟩
    · rw [e]; exact ⟨Or.inl rfl, Or.inl rfl⟩
    · rw [e]; exact ⟨Or.inl rfl, Or.inl rfl⟩
  | deliver d p f hok =>
    obtain ⟨a, b, _⟩ := deliverUpd_nd P S d p f
    by_cases hn : n = d
    · subst hn
      rw [a]
      exact deliver_gen (I.node n) p f S.now
    · have : n = !d := by cases n <;> cases d <;> simp_all
      rw [this, b]
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  | tick => exact ⟨Or.inl rfl, Or.inl rfl⟩
  | requeue d _ =>
    unfold requeueUpd
    rcases Sys.setNode_cases S d n { S.nd d with out := (S.nd d).lastAns } with e | ⟨rfl, e⟩ <;>
      rw [e] <;> exact ⟨Or.inl rfl, Or.inl rfl⟩
  | reqLost d _ =>
    unfold reqLostUpd
    rcases Sys.setNode_cases S d n { S.nd d with reqAt := none } with e | ⟨rfl, e⟩ <;>
      rw [e] <;> exact ⟨Or.inl rfl, Or.inl rfl⟩

/-- Unless the packet promotes the staged next key, the keys layer leaves the generations and the floor alone. -/
theorem recvKeys_neutral (s : Node) (p : Pkt) (f : Bool) (t pto : Nat)
    (hnp : ¬ ((s.recvKeys p f t pto).acc = true ∧ (s.recvKeys p f t pto).sel = .next)) :
    s.KeyNeutral (s.recvKeys p f t pto).s := by
  have base : s.KeyNeutral (s.expire t) := by
    refine ⟨by rw [expire_sk], by rw [expire_cur], by rw [expire_nxt], by rw [expire_stg], ?_⟩
    intro x' hx'; rw [expire_nxt] at hx'; exact ⟨x', hx', rfl⟩
  rcases recvKeys_form s p f t pto with e | ⟨fst, e⟩ | ⟨sel, e⟩ | ⟨ha, hs, _⟩
  · rw [e]; exact base
  · rw [e]
    obtain ⟨a, b, c, d, g⟩ := base
    exact ⟨a, b, c, d, g⟩
  · rw [e]
    obtain ⟨a, b, c, d, g⟩ := base
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · cases sel <;> simp [Node.bumpFC, a]
    · cases sel <;> simp [Node.bumpFC, b]
    · cases sel <;> simp [Node.bumpFC, c]
    · cases sel <;> simp [Node.bumpFC, d]
    · intro x' hx'
      cases sel <;> simp only [Node.bumpFC] at hx'
      all_goals first
        | exact g x' hx'
        | (cases hn : (s.expire t).nxt with
           | none => rw [hn] at hx'; simp at hx'
           | some y => rw [hn] at hx'; simp at hx'; exact ⟨y, by rw [expire_nxt] at hn; exact hn, by rw [← hx']⟩)
  · exact absurd ⟨ha, hs⟩ hnp

theorem afterRecv_neutral {P : Params} (s : Node) (p : Pkt) (f : Bool) (t : Nat)
    (hnp : ¬ ((s.recvKeys p f t P.pto).acc = true ∧ (s.recvKeys p f t P.pto).sel = .next)) :
    s.KeyNeutral (s.afterRecv P p f t).1 := by
  have h := recvKeys_neutral s p f t P.pto hnp
  unfold Node.afterRecv
  dsimp only
  split
  · exact h
  · exact h

/-- The floor of a staged next key does not change while it is staged, unless the packet promotes it
(`FloorsRespected`, delivery). -/
theorem floorsRespected_deliver {P : Params} {S : Sys} (hr : Reach P S) {n : Bool}
    {p : Pkt} {f : Bool}
    (hnp : ¬ (((S.nd n).recvKeys p f S.now P.pto).acc = true ∧ ((S.nd n).recvKeys p f S.now P.pto).sel = .next))
    {x x' : Nxt} (hx : (S.nd n).nxt = some x) (hx' : ((deliverUpd P S n p f).nd n).nxt = some x') :
    x'.floor = x.floor := by
  have I := hr.inv
  have kn := afterRecv_neutral (P := P) (S.nd n) p f S.now hnp
  have h1 := (I.node n).afterRecv p f S.now
  rw [(deliverUpd_nd P S n p f).1] at hx'
  have key : ∀ y, ((S.nd n).afterRecv P p f S.now).1.nxt = some y → y.floor = x.floor := by
    intro y hy
    obtain ⟨z, hz, hfl⟩ := kn.2.2.2.2 y hy
    rw [hx] at hz
    cases hz
    exact hfl
  unfold rkOf at hx'
  generalize (S.nd n).afterRecv P p f S.now = r at *
  obtain ⟨s1, pr⟩ := r
  simp only at *
  cases hpl : p.pl with
  | none => simp only [hpl] at hx'; exact key x' hx'
  | some m =>
    by_cases hp : (pr && acts m ((S.nd n).rxSel P p f S.now)) = true
    · simp only [hpl, hp, if_true] at hx'
      obtain ⟨_, _, c3, _⟩ := rekeyRx_keys h1 m n p.sec.depth
      rcases c3 with c3 | c3
      · exact key x' (by rw [← c3]; exact hx')
      · exfalso
        have := kn.2.2.1
        rw [c3, hx] at this
        simp at this
    · simp only [hpl, hp] at hx'; simp at hx'; exact key x' hx'

/-- The floor of a staged next key does not change while it is staged, in any step, unless the step is the delivery
of a packet that promotes it (`FloorsRespected`). -/
theorem floorsRespected {P : Params} {S S' : Sys} (hr : Reach P S) (hs : Step P S S')
    (n : Bool) {x x' : Nxt} (hx : (S.nd n).nxt = some x) (hx' : (S'.nd n).nxt = some x')
    (hnp : ∀ p f, S' = deliverUpd P S n p f →
      ¬ (((S.nd n).recvKeys p f S.now P.pto).acc = true ∧ ((S.nd n).recvKeys p f S.now P.pto).sel = .next)) :
    x'.floor = x.floor := by
  cases hs with
  | begin d hok =>
    rw [beginUpd_eq hok] at hx'
    dsimp only at hx'
    rcases Sys.setNode_cases S d n (beginNode (S.nd d) d) with e | ⟨rfl, e⟩
    · rw [e] at hx'; rw [hx] at hx'; cases hx'; rfl
    · rw [e] at hx'; simp only [beginNode] at hx'; rw [hx] at hx'; cases hx'; rfl
  | send d w hok =>
    obtain ⟨r, l, o, _, _, hlo, he⟩ := sendUpd_eq hok
    rw [he] at hx'
    dsimp only at hx'
    rcases Sys.setNode_cases S d n { S.nd d with out := o, reqAt := r, lastAns := l, npn := (S.nd d).npn + 1 } with e | ⟨rfl, e⟩
    · rw [e] at hx'; rw [hx] at hx'; cases hx'; rfl
    · rw [e] at hx'; simp only at hx'; rw [hx] at hx'; cases hx'; rfl
  | deliver d p f hok =>
    by_cases hn : n = d
    · subst hn
      exact floorsRespected_deliver hr (hnp p f rfl) hx hx'
    · have : n = !d := by cases n <;> cases d <;> simp_all
      rw [this, (deliverUpd_nd P S d p f).2.1] at hx'
      rw [this] at hx
      rw [hx] at hx'; cases hx'; rfl
  | tick => have : (tickUpd S).nd n = S.nd n := rfl
            rw [this, hx] at hx'; cases hx'; rfl
  | requeue d _ =>
    unfold requeueUpd at hx'
    rcases Sys.setNode_cases S d n { S.nd d with out := (S.nd d).lastAns } with e | ⟨rfl, e⟩
    · rw [e] at hx'; rw [hx] at hx'; cases hx'; rfl
    · rw [e] at hx'; simp only at hx'; rw [hx] at hx'; cases hx'; rfl
  | reqLost d _ =>
    unfold reqLostUpd at hx'
    rcases Sys.setNode_cases S d n { S.nd d with reqAt := none } with e | ⟨rfl, e⟩
    · rw [e] at hx'; rw [hx] at hx'; cases hx'; rfl
    · rw [e] at hx'; simp only at hx'; rw [hx] at hx'; cases hx'; rfl

/-- A duplicate request is answered with the same answer and creates no key (`DupRequestAnswered`), also while the
next key is staged; the old code, which refused it there, is shown by `KeyRollSysCex.lean`. A request that arrived
under the previous key (`sel = prev`) is a late copy of a settled roll and is ignored instead. -/
theorem dupRequestAnswered {P : Params} {S : Sys}
    (hr : Reach P S) {n : Bool} {p : Pkt} {f : Bool} {m : Msg}
    (hproc : ((S.nd n).afterRecv P p f S.now).2 = true) (hpl : p.pl = some m) (hm : m.answer = false)
    (hsel : (S.nd n).rxSel P p f S.now ≠ .prev) (hd : (S.nd n).roll.isDup m = true) :
    ∃ ans, (S.nd n).roll.last = some (m.share, ans) ∧
      ((deliverUpd P S n p f).nd n).out = some ans ∧ ((deliverUpd P S n p f).nd n).chg = (S.nd n).chg := by
  have I := hr.inv
  have rf := afterRecv_facts (I.node n) p f S.now
  obtain ⟨ans, hl⟩ := isDup_last _ _ hd
  have hl1 : ((S.nd n).afterRecv P p f S.now).1.roll.last = some (m.share, ans) := by rw [rf.roll]; exact hl
  have hd1' : ((S.nd n).afterRecv P p f S.now).1.roll.isDup m = true := by rw [rf.roll]; exact hd
  have hg : gated ((S.nd n).afterRecv P p f S.now).1 m = false := by
    simp [gated, isDupMsg, hm, hd1']
  have hact : acts m ((S.nd n).rxSel P p f S.now) = true := by simp [acts, hm, hsel]
  refine ⟨ans, hl, ?_⟩
  rw [(deliverUpd_nd P S n p f).1]
  unfold rkOf
  generalize (S.nd n).afterRecv P p f S.now = r at *
  obtain ⟨s1, pr⟩ := r
  simp only at *
  simp only [hpl, hproc, hact, Bool.and_self, ite_true]
  rw [rekeyRx_dup s1 m n _ hm hg ans hl1]
  exact ⟨rfl, by simp [Node.chg, rf.ders]⟩

/-- The dialer wins a collision: while its own request is out, the dialing side ignores the other side's request
and keeps its state; the accepting side drops its own request and answers (`DialerWins`). -/
theorem dialerWins {P : Params} {S : Sys} (hr : Reach P S) {n : Bool} {p : Pkt}
    {f : Bool} (hok : deliverOk P S n p f = true) {m : Msg}
    (hproc : ((S.nd n).afterRecv P p f S.now).2 = true) (hpl : p.pl = some m) (hm : m.answer = false)
    (hsel : (S.nd n).rxSel P p f S.now ≠ .prev)
    (hnd : (S.nd n).roll.isDup m = false) (hreq : (S.nd n).roll.isIdle = false) (hnx : (S.nd n).nxt = none) :
    ((S.nd n).roll.dialer = true →
      ((deliverUpd P S n p f).nd n).roll = (S.nd n).roll ∧ ((deliverUpd P S n p f).nd n).stg = none) ∧
    ((S.nd n).roll.dialer = false →
      ((deliverUpd P S n p f).nd n).roll.st = .idle ∧ ((deliverUpd P S n p f).nd n).out ≠ none) := by
  have I := hr.inv
  obtain ⟨hp, hsrc⟩ := deliverOk_spec hok
  have rf := afterRecv_facts (I.node n) p f S.now
  have hstg0 : (S.nd n).stg = none := ((I.node n).req hreq).2
  have hk : ((S.nd n).afterRecv P p f S.now).1.nxt = none ∧ ((S.nd n).afterRecv P p f S.now).1.stg = none := by
    rcases rf.keys with k | ⟨k, _⟩
    · have a := k.2.2.1
      have b := k.2.2.2.1
      rw [hnx] at a
      rw [hstg0] at b
      exact ⟨by cases h : ((S.nd n).afterRecv P p f S.now).1.nxt <;> simp_all,
             by cases h : ((S.nd n).afterRecv P p f S.now).1.stg <;> simp_all⟩
    · have := k.1; rw [hnx] at this; simp at this
  have hg : gated ((S.nd n).afterRecv P p f S.now).1 m = false := by simp [gated, hk.1]
  have hnd1 : ((S.nd n).afterRecv P p f S.now).1.roll.isDup m = false := by rw [rf.roll]; exact hnd
  have hmok := (I.netMsg p hp m hpl)
  rw [hsrc] at hmok
  obtain ⟨_, kk, hkk, _⟩ := hmok.req hm
  have hd1 := (deliverUpd_nd P S n p f).1
  have hact : acts m ((S.nd n).rxSel P p f S.now) = true := by simp [acts, hm, hsel]
  unfold rkOf at hd1
  generalize (S.nd n).afterRecv P p f S.now = r at *
  obtain ⟨s1, pr⟩ := r
  simp only at *
  simp only [hpl, hproc, hact, Bool.and_self, if_true] at hd1
  constructor
  · intro hdl
    have hc : (!s1.roll.isIdle && s1.roll.dialer) = true := by rw [rf.roll]; simp [hreq, hdl]
    rw [hd1, rekeyRx_busy s1 m n _ hm hg hnd1 hc]
    exact ⟨rf.roll, hk.2⟩
  · intro hdl
    have hc : (!s1.roll.isIdle && s1.roll.dialer) = false := by rw [rf.roll]; simp [hdl]
    rw [hd1, rekeyRx_stage s1 m n _ (atomOf (!n) kk) hm hg hnd1 hc hkk]
    simp [Node.staged, Roll.answeredWith]

/-- An answer while no request is out changes no key (a packet that promotes the staged key still does)
(`StaleAnswerNoKey`). -/
theorem staleAnswerNoKey {P : Params} {S : Sys} (hr : Reach P S) {n : Bool} {p : Pkt}
    {f : Bool} {m : Msg}
    (hnp : ¬ (((S.nd n).recvKeys p f S.now P.pto).acc = true ∧ ((S.nd n).recvKeys p f S.now P.pto).sel = .next))
    (hpl : p.pl = some m) (hm : m.answer = true) (hidle : (S.nd n).roll.isIdle = true) :
    ((deliverUpd P S n p f).nd n).sk.g = (S.nd n).sk.g ∧ ((deliverUpd P S n p f).nd n).chg = (S.nd n).chg := by
  have I := hr.inv
  have rf := afterRecv_facts (I.node n) p f S.now
  have kn := afterRecv_neutral (P := P) (S.nd n) p f S.now hnp
  have hd1 := (deliverUpd_nd P S n p f).1
  have hact : acts m ((S.nd n).rxSel P p f S.now) = true := by simp [acts, hm]
  unfold rkOf at hd1
  generalize (S.nd n).afterRecv P p f S.now = r at *
  obtain ⟨s1, pr⟩ := r
  simp only at *
  have hstale : ∀ c, (s1.roll.onAnswer m).2 ≠ .ok c := by
    intro c hc
    obtain ⟨seed, rq, b, hst, _⟩ := onAnswer_ok_st s1.roll m c hc
    have := (isIdle_st s1.roll).1 (by rw [rf.roll]; exact hidle)
    rw [this] at hst; cases hst
  by_cases hp : pr = true
  · simp only [hpl, hp, hact, Bool.and_self, if_true] at hd1
    rw [hd1, rekeyRx_answer_refused s1 m n _ hm hstale]
    exact ⟨kn.1, by simp [Node.chg, rf.ders]⟩
  · simp only [hpl, hp] at hd1
    simp at hd1
    rw [hd1]
    exact ⟨kn.1, by simp [Node.chg, rf.ders]⟩

/-- A seal never repeats a (secret, packet number) pair and a node's numbers increase (`FreshSeal`). -/
theorem freshSeal {P : Params} {S : Sys} (hr : Reach P S) (n : Bool) :
    ∀ x ∈ S.slog, ¬ (x.sec = (S.nd n).sk.sec ∧ x.pn = (S.nd n).npn) ∧ (x.n = n → x.pn < (S.nd n).npn) := by
  have I := hr.inv
  intro x hx
  obtain ⟨a1, a2, a3, ds, hds⟩ := I.slogOK x hx
  have hxn : x.n = n → x.pn < (S.nd n).npn := fun e => by rw [← e]; exact a1
  refine ⟨?_, hxn⟩
  rintro ⟨e1, e2⟩
  have := (rollAll_base_inj _ _ _ _ (hds.symm.trans (e1.trans (NodeInv.kfSk (I.node n))))).1
  have hn : x.n = n := by cases hx' : x.n <;> cases n <;> simp_all [nid]
  have := hxn hn
  omega

end Vinc.KeyRollSys
