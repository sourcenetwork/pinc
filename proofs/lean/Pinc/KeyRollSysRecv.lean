import Pinc.KeyRollSysNode

namespace Pinc.KeyRollSys
open Pinc.KeyRoll

/-! ## What the keys layer does to the node, as the cross-node invariants need it -/

/-- What `RecvKeys` does when the packet opens, case by case (`s1` is the node after `expire`). -/
theorem recvKeys_acc_cases (s : Node) (p : Pkt) (f : Bool) (t pto : Nat)
    (hacc : (s.recvKeys p f t pto).acc = true) :
    f = false ∧
    (((s.expire t).cur.sec = p.sec ∧ ∃ fst, (s.recvKeys p f t pto).s = { s.expire t with first := fst }) ∨
     (∃ pv, (s.expire t).prev = some pv ∧ pv.k.sec = p.sec ∧ (s.recvKeys p f t pto).s = s.expire t) ∨
     (∃ x, (s.expire t).nxt = some x ∧ x.k.sec = p.sec ∧
        (s.recvKeys p f t pto).s = ((s.expire t).promote p.pn t pto).updateSend)) := by
  unfold Node.recvKeys at hacc ⊢
  dsimp only at hacc ⊢
  generalize s.expire t = s1 at hacc ⊢
  generalize hsel : s1.select (if f = true then !p.ph else p.ph) p.pn = sel at hacc ⊢
  generalize hok : (!f && decide (s1.slotSec sel = some p.sec)) = ok at hacc ⊢
  have hnf : ok = true → f = false ∧ s1.slotSec sel = some p.sec := by
    intro h; rw [← hok] at h; simp at h; exact h
  cases sel <;> cases ok <;> simp only [Bool.false_eq_true, ↓reduceIte] at hacc ⊢
  · -- cur, ok
    obtain ⟨hf, hs⟩ := hnf rfl
    refine ⟨hf, Or.inl ⟨?_, _, rfl⟩⟩
    simpa [Node.slotSec] using hs
  · -- next, ok
    obtain ⟨hf, hs⟩ := hnf rfl
    refine ⟨hf, Or.inr (Or.inr ?_)⟩
    cases hn : s1.nxt with
    | none => simp [Node.slotSec, hn] at hs
    | some x => simp [Node.slotSec, hn] at hs; exact ⟨x, rfl, hs, trivial⟩
  · -- prev, ok
    obtain ⟨hf, hs⟩ := hnf rfl
    refine ⟨hf, Or.inr (Or.inl ?_)⟩
    cases hn : s1.prev with
    | none => simp [Node.slotSec, hn] at hs
    | some x => simp [Node.slotSec, hn] at hs; exact ⟨x, rfl, hs, trivial⟩

theorem expire_roll (s : Node) (t : Nat) : (s.expire t).roll = s.roll := by rcases expire_cases s t with e | e <;> rw [e]
theorem expire_ctr (s : Node) (t : Nat) : (s.expire t).ctr = s.ctr := by rcases expire_cases s t with e | e <;> rw [e]
theorem expire_ders (s : Node) (t : Nat) : (s.expire t).ders = s.ders := by rcases expire_cases s t with e | e <;> rw [e]
theorem expire_out (s : Node) (t : Nat) : (s.expire t).out = s.out := by rcases expire_cases s t with e | e <;> rw [e]
theorem expire_npn (s : Node) (t : Nat) : (s.expire t).npn = s.npn := by rcases expire_cases s t with e | e <;> rw [e]
theorem expire_sk (s : Node) (t : Nat) : (s.expire t).sk = s.sk := by rcases expire_cases s t with e | e <;> rw [e]
theorem expire_cur (s : Node) (t : Nat) : (s.expire t).cur = s.cur := by rcases expire_cases s t with e | e <;> rw [e]
theorem expire_nxt (s : Node) (t : Nat) : (s.expire t).nxt = s.nxt := by rcases expire_cases s t with e | e <;> rw [e]
theorem expire_stg (s : Node) (t : Nat) : (s.expire t).stg = s.stg := by rcases expire_cases s t with e | e <;> rw [e]

/-- The sending and receiving generations and the staged next key, before and after the keys layer, when it does not
promote. -/
def Node.KeyNeutral (s0 s1 : Node) : Prop :=
  s1.sk.g = s0.sk.g ∧ s1.cur.g = s0.cur.g ∧ s1.nxt.isSome = s0.nxt.isSome ∧ s1.stg.isSome = s0.stg.isSome ∧
    (∀ x', s1.nxt = some x' → ∃ x, s0.nxt = some x ∧ x'.floor = x.floor)

/-- ... and when it promotes the staged next key. -/
def Node.KeyPromoted (s0 s1 : Node) : Prop :=
  s0.nxt.isSome = true ∧ s1.cur.g = s0.cur.g + 1 ∧ s1.nxt = none ∧ s1.stg = none ∧
    (s0.stg.isSome = true → s1.sk.g = s0.sk.g + 1) ∧ (s0.stg = none → s1.sk.g = s0.sk.g)

structure RecvFacts (s0 s1 : Node) (p : Pkt) : Prop where
  roll : s1.roll = s0.roll
  ctr : s1.ctr = s0.ctr
  ders : s1.ders = s0.ders
  out : s1.out = s0.out
  npn : s1.npn = s0.npn
  keys : s0.KeyNeutral s1 ∨ (s0.KeyPromoted s1 ∧ p.sec.depth = s0.cur.g + 1)

/-- Promotion with the switch of the staged sending key: what it does to the fields that matter. -/
theorem promoteSend_spec {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (x : Nxt) (hn : s.nxt = some x)
    (pn t : Nat) :
    let s1 := (s.promote pn t P.pto).updateSend
    s1.roll = s.roll ∧ s1.ctr = s.ctr ∧ s1.ders = s.ders ∧ s1.out = s.out ∧ s1.npn = s.npn ∧
    s.KeyPromoted s1 := by
  intro s1
  obtain ⟨hx1, hx2⟩ := NodeInv.kfNxt h x hn
  cases hs : s.stg with
  | none =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [s1, Node.promote, Node.updateSend, hn, hs, Node.KeyPromoted, hx2]
  | some k =>
    obtain ⟨hk1, hk2⟩ := NodeInv.kfStg h k hs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [s1, Node.promote, Node.updateSend, hn, hs, Node.KeyPromoted, hx2, hk2]

theorem recvKeys_facts {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (p : Pkt) (f : Bool) (t : Nat) :
    RecvFacts s (s.recvKeys p f t P.pto).s p := by
  have hneut : ∀ s1 : Node, s1.roll = s.roll → s1.ctr = s.ctr → s1.ders = s.ders → s1.out = s.out → s1.npn = s.npn →
      s.KeyNeutral s1 → RecvFacts s s1 p := fun s1 a b c d e g => ⟨a, b, c, d, e, Or.inl g⟩
  have hexp : RecvFacts s (s.expire t) p := by
    refine hneut _ (expire_roll _ _) (expire_ctr _ _) (expire_ders _ _) (expire_out _ _) (expire_npn _ _) ?_
    refine ⟨by rw [expire_sk], by rw [expire_cur], by rw [expire_nxt], by rw [expire_stg], ?_⟩
    intro x' hx'; rw [expire_nxt] at hx'; exact ⟨x', hx', rfl⟩
  by_cases hacc : (s.recvKeys p f t P.pto).acc = true
  · obtain ⟨_, hc⟩ := recvKeys_acc_cases s p f t P.pto hacc
    rcases hc with ⟨hcs, fst, he⟩ | ⟨pv, hpv, hps, he⟩ | ⟨x, hx, hxs, he⟩
    · rw [he]
      refine hneut _ ?_ ?_ ?_ ?_ ?_ ?_
      · exact expire_roll _ _
      · exact expire_ctr _ _
      · exact expire_ders _ _
      · exact expire_out _ _
      · exact expire_npn _ _
      · refine ⟨by simp [expire_sk], by simp [expire_cur], by simp [expire_nxt], by simp [expire_stg], ?_⟩
        intro x' hx'; simp only [expire_nxt] at hx'; exact ⟨x', hx', rfl⟩
    · rw [he]; exact hexp
    · rw [he]
      have hx0 : s.nxt = some x := by rw [← expire_nxt s t]; exact hx
      obtain ⟨r1, r2, r3, r4, r5, r6⟩ := promoteSend_spec (h.expire t) x hx p.pn t
      have hxg := (NodeInv.kfNxt h x hx0).2
      have hdx' : x.k.sec.depth = x.k.g := (h.depths).2.2.2.1 x hx0
      have r6' : s.KeyPromoted ((s.expire t).promote p.pn t P.pto).updateSend := by
        simpa [Node.KeyPromoted, expire_cur, expire_nxt, expire_sk, expire_stg] using r6
      refine ⟨by rw [r1, expire_roll], by rw [r2, expire_ctr], by rw [r3, expire_ders], by rw [r4, expire_out],
        by rw [r5, expire_npn], Or.inr ⟨r6', ?_⟩⟩
      rw [← hxs, hdx', hxg]
  · -- the packet did not open: the keys layer only counts the failure
    have hf := recvKeys_form s p f t P.pto
    rcases hf with e | ⟨fst, e⟩ | ⟨sel, e⟩ | ⟨ha, _⟩
    · rw [e]; exact hexp
    · rw [e]
      refine hneut _ (expire_roll _ _) (expire_ctr _ _) (expire_ders _ _) (expire_out _ _) (expire_npn _ _) ?_
      refine ⟨by simp [expire_sk], by simp [expire_cur], by simp [expire_nxt], by simp [expire_stg], ?_⟩
      intro x' hx'; simp only [expire_nxt] at hx'; exact ⟨x', hx', rfl⟩
    · rw [e]
      have hb := (h.expire t)
      refine hneut _ ?_ ?_ ?_ ?_ ?_ ?_
      · cases sel <;> simp [Node.bumpFC, expire_roll]
      · cases sel <;> simp [Node.bumpFC, expire_ctr]
      · cases sel <;> simp [Node.bumpFC, expire_ders]
      · cases sel <;> simp [Node.bumpFC, expire_out]
      · cases sel <;> simp [Node.bumpFC, expire_npn]
      · cases sel with
        | err => exact ⟨by simp [Node.bumpFC, expire_sk], by simp [Node.bumpFC, expire_cur], by simp [Node.bumpFC, expire_nxt],
            by simp [Node.bumpFC, expire_stg], fun x' hx' => ⟨x', by simpa [Node.bumpFC, expire_nxt] using hx', rfl⟩⟩
        | cur => exact ⟨by simp [Node.bumpFC, expire_sk], by simp [Node.bumpFC, expire_cur], by simp [Node.bumpFC, expire_nxt],
            by simp [Node.bumpFC, expire_stg], fun x' hx' => ⟨x', by simpa [Node.bumpFC, expire_nxt] using hx', rfl⟩⟩
        | prev => exact ⟨by simp [Node.bumpFC, expire_sk], by simp [Node.bumpFC, expire_cur], by simp [Node.bumpFC, expire_nxt],
            by simp [Node.bumpFC, expire_stg], fun x' hx' => ⟨x', by simpa [Node.bumpFC, expire_nxt] using hx', rfl⟩⟩
        | next =>
          refine ⟨by simp [Node.bumpFC, expire_sk], by simp [Node.bumpFC, expire_cur], by simp [Node.bumpFC, expire_nxt],
            by simp [Node.bumpFC, expire_stg], ?_⟩
          intro x' hx'
          simp only [Node.bumpFC, expire_nxt] at hx'
          cases hn : s.nxt with
          | none => simp [hn] at hx'
          | some y =>
            simp [hn] at hx'
            exact ⟨y, rfl, by rw [← hx']⟩
    · exact absurd ha hacc

/-- A packet that opens was sealed under the current key, the previous one or the staged next one, which the
node holds afterwards as the current key or the one below it. -/
theorem recvKeys_depth {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (p : Pkt) (f : Bool) (t : Nat)
    (hacc : (s.recvKeys p f t P.pto).acc = true) :
    p.sec.depth = (s.recvKeys p f t P.pto).s.cur.g ∨ p.sec.depth + 1 = (s.recvKeys p f t P.pto).s.cur.g := by
  obtain ⟨_, hc⟩ := recvKeys_acc_cases s p f t P.pto hacc
  have he := h.expire t
  have hdep := he.depths
  rcases hc with ⟨hcs, fst, e⟩ | ⟨pv, hpv, hps, e⟩ | ⟨x, hx, hxs, e⟩
  · rw [e]; left
    rw [← hcs]; exact hdep.2.1
  · rw [e]; right
    obtain ⟨_, a2⟩ := NodeInv.kfPrev he pv hpv
    rw [← hps, hdep.2.2.2.2 pv hpv]; exact a2
  · rw [e]; left
    have hx0 : s.nxt = some x := by rw [← expire_nxt s t]; exact hx
    obtain ⟨_, _, _, _, _, r6⟩ := promoteSend_spec he x hx p.pn t
    rw [← hxs, hdep.2.2.2.1 x hx, (NodeInv.kfNxt he x hx).2, r6.2.1]

theorem RecvFacts.seen {s0 s1 : Node} {p : Pkt} (h : RecvFacts s0 s1 p) (l : List Nat) :
    RecvFacts s0 { s1 with seen := l } p := by
  refine ⟨h.roll, h.ctr, h.ders, h.out, h.npn, ?_⟩
  rcases h.keys with k | ⟨k, d⟩
  · exact Or.inl k
  · exact Or.inr ⟨k, d⟩

theorem afterRecv_facts {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (p : Pkt) (f : Bool) (t : Nat) :
    RecvFacts s (s.afterRecv P p f t).1 p := by
  unfold Node.afterRecv
  dsimp only
  split
  · exact (recvKeys_facts h p f t).seen _
  · exact recvKeys_facts h p f t

theorem afterRecv_depth {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) (p : Pkt) (f : Bool) (t : Nat)
    (hp : (s.afterRecv P p f t).2 = true) :
    p.sec.depth = (s.afterRecv P p f t).1.cur.g ∨ p.sec.depth + 1 = (s.afterRecv P p f t).1.cur.g := by
  unfold Node.afterRecv at hp ⊢
  dsimp only at hp ⊢
  have hp' : (s.recvKeys p f t P.pto).acc = true ∧ (decide ¬p.pn ∈ s.seen) = true := by
    simpa [Bool.and_eq_true] using hp
  have hacc := hp'.1
  rw [if_pos (by simpa [Bool.and_eq_true] using hp')]
  exact recvKeys_depth h p f t hacc

/-- Receiving a packet never touches the last answer polled. -/
theorem afterRecv_lastAns (P : Params) (s : Node) (p : Pkt) (f : Bool) (t : Nat) :
    (s.afterRecv P p f t).1.lastAns = s.lastAns := by
  have he : (s.expire t).lastAns = s.lastAns := by
    unfold Node.expire; split <;> (try split) <;> rfl
  have hb : ∀ (x : Node) (sel : Sel), (x.bumpFC sel).lastAns = x.lastAns := by
    intro x sel; cases sel <;> rfl
  have hp : ∀ (x : Node) (a b c : Nat), ((x.promote a b c).updateSend).lastAns = x.lastAns := by
    intro x a b c; unfold Node.promote Node.updateSend; split <;> (try split) <;> rfl
  unfold Node.afterRecv Node.recvKeys
  dsimp only
  repeat' split
  all_goals simp_all [he, hb, hp]

end Pinc.KeyRollSys
