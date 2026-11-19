import Pinc.DtnScenarioChainLib

/-!
# Custody handoff chains

`Cust s n` says node `n`'s ledger keeps a custody item of the bundle. `Ended s` says the bundle is finished: it was
delivered to the destination, some node was told of the delivery by an ack (`fin`), or it expired.

**`custody_chain`** (for the ranked policy, custody offered only to a higher node id): in every reachable system, as long
as the bundle is not `Ended`, every node that ever accepted custody (the origin included) is itself in custody or
has a node of at least its id in custody. So custody of an unfinished bundle is never absent from the system; in
particular some node keeps it. The proof is the invariant `ChInv`:

* a relief at node `p` needs an ack from the node `c` custody was offered to, so `p < c` (`rank`);
* every ack in the network was made by a node that accepted custody, or by the destination after the delivery
  (`ackd`);
* the acknowledging node `c` accepted custody, so by the invariant a node `n >= c > p` is in custody, and `n` is not
  `p` and is not touched by the ack;
* a custody item leaves a ledger only by delivery, release, relief or expiry (`custody_stays`), and each of the first
  two and the last ends the bundle.

Without the ranking the proof does not go through: before an ack carried an offer id, a stale ack of a first handover
and the ack of a handover back relieved both nodes of a cycle. That run now keeps custody at node 1
(`DtnScenarioCycle.cycle_keeps_custody`, and `DtnScenario_cycle.cfg` in TLA+).
-/

namespace Pinc.DtnScenario

def Cust (s : Sys) (n : Nat) : Prop :=
  ∃ e ∈ (s.nodes n).L.entries, e.key = DtnStore.bkey bid ∧ e.cls = .custody

def Ended (s : Sys) : Prop := s.delivered = true ∨ s.fin = true ∨ s.cfg.exp ≤ s.t

theorem exec_mono (s : Sys) (ev : Ev) :
    (s.delivered = true → (exec s ev).delivered = true) ∧ (s.fin = true → (exec s ev).fin = true) ∧
      s.t ≤ (exec s ev).t := by
  cases ev <;> (simp only [exec, exec0, Sys.set]; repeat' split) <;> simp_all

theorem ended_mono {s : Sys} (h : Ended s) (ev : Ev) : Ended (exec s ev) := by
  obtain ⟨h1, h2, h3⟩ := exec_mono s ev
  have hc : (exec s ev).cfg = s.cfg := exec_cfg s ev
  rcases h with h | h | h
  · exact Or.inl (h1 h)
  · exact Or.inr (Or.inl (h2 h))
  · exact Or.inr (Or.inr (by rw [hc]; omega))

/-- The shapes of the `DtnStore` events the glue applies to node `m`. -/
theorem ledgerEv_forms (s : Sys) (ev : Ev) (m : Nat) (le : DtnStore.Ev) (h : ledgerEv s ev m = some le) :
    (le = .bexpire (s.t + 1) ∧ ev = .tick) ∨ (∃ p, le = .offer bid p ∧ ev = .poll m ∧ offerable s.cfg m p = true) ∨
      (le = .delivered bid ∧ ev = .poll m) ∨ (∃ f, le = .accept bid 1 s.cfg.exp f s.t) ∨ (∃ c o, le = .ack bid c o true) ∨
      (∃ k, le = .hostAdmit ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t) := by
  cases ev with
  | tick => simp only [ledgerEv] at h; cases h; exact Or.inl ⟨rfl, rfl⟩
  | poll n =>
    simp only [ledgerEv] at h
    by_cases hmn : m = n
    · subst hmn
      simp only [if_true] at h
      cases hp : DtnForward.poll (s.nodes m).f with
      | mk f' a =>
        rw [hp] at h
        cases a with
        | none => simp at h
        | send p b c r =>
          simp only at h
          split at h
          · rename_i hc
            cases h
            right; left
            refine ⟨p, rfl, rfl, ?_⟩
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            exact hc.2
          · simp at h
        | release b => cases h; right; right; left; exact ⟨rfl, rfl⟩
    · simp [hmn] at h
  | bun mm =>
    cases mm with
    | bun a b c d e f =>
      simp only [ledgerEv] at h
      split at h
      · cases h; right; right; right; left; exact ⟨_, rfl⟩
      · simp at h
    | ack a b c d => simp [ledgerEv] at h
  | ack mm =>
    cases mm with
    | ack a c p o =>
      simp only [ledgerEv] at h
      split at h
      · cases h; right; right; right; right; left; exact ⟨_, _, rfl⟩
      · simp at h
    | bun a b c d e f => simp [ledgerEv] at h
  | press n k' =>
    simp only [ledgerEv] at h
    split at h
    · cases h; right; right; right; right; right; exact ⟨_, rfl⟩
    · simp at h
  | contact a b up => simp [ledgerEv] at h
  | lose mm => simp [ledgerEv] at h
  | bad => simp [ledgerEv] at h

theorem exec_acc (s : Sys) (ev : Ev) (hE : En s ev) :
    (exec s ev).acc = s.acc ∨ ∃ r ∈ s.cfg.ids, (exec s ev).acc = r :: s.acc := by
  cases ev with
  | bun mm =>
    cases mm with
    | ack a b c d => exact hE.2.elim
    | bun a b r d e off =>
      by_cases hd : r = s.cfg.dest
      · left; simp [exec, exec0, hd]
      · simp only [exec, exec0, hd, ite_false]
        split
        · left; rfl
        · right; exact ⟨r, hE.2, rfl⟩
  | _ => left; (simp only [exec, exec0, Sys.set]; repeat' split) <;> rfl

theorem exec_msgs (s : Sys) (ev : Ev) (hE : En s ev) : ∀ m' ∈ (exec s ev).msgs,
    m' ∈ s.msgs ∨ (∃ a b c d e f, m' = Msg.bun a b c d e f) ∨
      (∃ id c p o, m' = Msg.ack id c p o ∧ (c ∈ (exec s ev).acc ∨ (exec s ev).delivered = true)) := by
  intro m' hm'
  cases ev with
  | bun mm =>
    cases mm with
    | ack a b c d => exact hE.2.elim
    | bun a b r d e off =>
      by_cases hd : r = s.cfg.dest
      · simp only [exec, exec0, hd, ite_true, List.mem_cons] at hm'
        rcases hm' with rfl | h
        · right; right; exact ⟨_, _, _, _, rfl, Or.inr (by simp [exec, exec0, hd])⟩
        · left; exact List.mem_of_mem_erase h
      · simp only [exec, exec0, hd, ite_false] at hm'
        split at hm'
        · left; exact List.mem_of_mem_erase hm'
        · simp only [List.mem_cons] at hm'
          rcases hm' with rfl | h
          · right; right; exact ⟨_, _, _, _, rfl, Or.inl (by simp [exec, exec0, hd]; split <;> simp_all)⟩
          · left; exact List.mem_of_mem_erase h
  | poll n =>
    simp only [exec, exec0] at hm'
    split at hm'
    · left; exact hm'
    · simp only [List.mem_cons] at hm'
      rcases hm' with rfl | h
      · right; left; exact ⟨_, _, _, _, _, _, rfl⟩
      · left; exact h
    · left; exact hm'
  | ack mm =>
    cases mm with
    | bun a b c d e f => exact hE.2.elim
    | ack a c p o =>
      simp only [exec, exec0] at hm'
      left; exact List.mem_of_mem_erase hm'
  | lose mm =>
    simp only [exec, exec0] at hm'
    left; exact List.mem_of_mem_erase hm'
  | contact a b up => left; simpa [exec, exec0, Sys.set] using hm'
  | tick => left; simpa [exec, exec0] using hm'
  | press n k =>
    left
    simp only [exec, exec0] at hm'
    split at hm'
    · exact hm'
    · exact hm'
  | bad => left; simpa [exec, exec0] using hm'

/-- The invariant of the chain theorem. -/
structure ChInv (s : Sys) : Prop where
  rank : s.cfg.ranked = true → ∀ n ∈ s.cfg.ids, ∀ r ∈ DtnStore.recs (s.nodes n).B, ∀ q, r.offered = some q → n < q
  le : ∀ n ∈ s.cfg.ids, ∀ e ∈ (s.nodes n).L.entries, e.key = DtnStore.bkey bid → e.expires = s.cfg.exp
  ackd : ∀ id c p o, Msg.ack id c p o ∈ s.msgs → c ∈ s.acc ∨ s.delivered = true
  flag : s.anyFlag = true → s.fin = true
  alive : s.cfg.ranked = true → ¬ Ended s → ∀ x ∈ s.acc, ∃ n ∈ s.cfg.ids, x ≤ n ∧ Cust s n

theorem exec_flag (s : Sys) (ev : Ev) : (exec s ev).anyFlag = true → (exec s ev).fin = true := by
  intro h
  show ((exec0 s ev).fin || (exec0 s ev).anyFlag) = true
  have : (exec0 s ev).anyFlag = true := h
  simp [this]

/-- A release is of a delivered or an expired bundle: the bundle is finished. -/
theorem release_ended {s : Sys} (hI : SysInv s) (hC : ChInv s) (n : Nat) (hn : n ∈ s.cfg.ids) (b : Nat)
    (hr : (DtnForward.poll (s.nodes n).f).2 = .release b) : Ended s := by
  have hx := hI.fwd n hn
  obtain ⟨i, b0, -, hb0, -, hcase⟩ := DtnForward.poll_release_only_done (s.nodes n).f (DtnForward.poll (s.nodes n).f).1 b
    (by rw [← hr])
  rcases hcase with hd | hex
  · right; left
    apply hC.flag
    unfold Sys.anyFlag
    simp only [List.any_eq_true]
    refine ⟨n, hn, some b0, ?_, by simp [hd]⟩
    unfold DtnForward.slot at hb0
    have : (s.nodes n).f.bs[i]? = some (some b0) := by
      cases h : (s.nodes n).f.bs[i]? with
      | none => simp [h] at hb0
      | some o => simp [h] at hb0; rw [hb0]
    exact List.mem_of_getElem? this
  · right; right
    have h1 := (hx.bok i b0 hb0).2.1
    have h2 := hx.now
    omega

theorem cust_keep {s : Sys} (hR : Reach s) (hI : SysInv s) (hC : ChInv s) (ev : Ev)
    (hend : ¬ Ended (exec s ev)) (n : Nat) (hn : n ∈ s.cfg.ids) (hcu : Cust s n)
    (hna : ¬ ∃ a c o, ev = .ack (.ack a c n o)) : Cust (exec s ev) n := by
  obtain ⟨e, he, hk, hc⟩ := hcu
  have hexp := hC.le n hn e he hk
  have hcfg := exec_cfg s ev
  obtain ⟨-, -, hmono⟩ := exec_mono s ev
  have hlt : (exec s ev).t < s.cfg.exp := by
    have h3 : ¬ (exec s ev).cfg.exp ≤ (exec s ev).t := fun h => hend (Or.inr (Or.inr h))
    rw [hcfg] at h3; omega
  have hrel : ¬ (ev = .poll n ∧ ∃ b, (DtnForward.poll (s.nodes n).f).2 = .release b) := by
    rintro ⟨rfl, b, hb⟩
    exact hend (ended_mono (release_ended hI hC n hn b hb) _)
  have hlive : ∀ le t, ledgerEv s ev n = some le → le.now = some t → DtnStore.expiredAt t e = false := by
    intro le t hle hnow
    rcases ledgerEv_forms s ev n le hle with ⟨rfl, rfl⟩ | ⟨p, rfl, -⟩ | ⟨rfl, -⟩ | ⟨f, rfl⟩ | ⟨c, o, rfl⟩ | ⟨k, rfl⟩
    · simp only [DtnStore.Ev.now, Option.some.injEq] at hnow
      subst hnow
      have : (exec s .tick).t = s.t + 1 := by simp [exec, exec0]
      simp only [DtnStore.expiredAt, decide_eq_false_iff_not]
      omega
    · simp [DtnStore.Ev.now] at hnow
    · simp [DtnStore.Ev.now] at hnow
    · simp only [DtnStore.Ev.now, Option.some.injEq] at hnow
      subst hnow
      simp only [DtnStore.expiredAt, decide_eq_false_iff_not]
      omega
    · simp [DtnStore.Ev.now] at hnow
    · simp only [DtnStore.Ev.now, Option.some.injEq] at hnow
      subst hnow
      simp only [DtnStore.expiredAt, decide_eq_false_iff_not]
      omega
  have hmem := custody_stays hR ev n hn e he hc hlive (fun h => h.elim hrel hna)
  exact ⟨e, hmem, hk, hc⟩

theorem rank_exec {s : Sys} (hR : Reach s) (hC : ChInv s) (ev : Ev) :
    (exec s ev).cfg.ranked = true → ∀ m ∈ (exec s ev).cfg.ids, ∀ r ∈ DtnStore.recs ((exec s ev).nodes m).B,
      ∀ q, r.offered = some q → m < q := by
  intro hrk m hm r hr q hq
  rw [exec_cfg] at hrk hm
  obtain ⟨hB, -, -⟩ := exec_BL s ev m hm
  rw [hB] at hr
  have hold := hC.rank hrk m hm
  have hnd := node_inv hR m hm
  unfold ledgerAfter at hr
  cases hle : ledgerEv s ev m with
  | none => simp only [hle] at hr; exact hold r hr q hq
  | some le =>
    simp only [hle] at hr
    rcases ledgerEv_forms s ev m le hle with ⟨rfl, -⟩ | ⟨p, rfl, hev, hoff⟩ | ⟨rfl, -⟩ | ⟨f, rfl⟩ | ⟨c, o, rfl⟩ | ⟨k, rfl⟩
    · exact hold r (DtnStore.bexpire_recs_sub _ _ _ r hr) q hq
    · rcases DtnStore.offer_recs _ _ _ _ r hr with h | ⟨-, ho⟩
      · exact hold r h q hq
      · rw [ho] at hq
        cases hq
        simp only [offerable, hrk, if_true, decide_eq_true_eq] at hoff
        exact hoff
    · exact hold r (DtnStore.delivered_recs_sub _ _ _ r hr) q hq
    · rcases DtnStore.accept_recs_sub _ _ _ _ _ _ _ r hr with h | h
      · exact hold r h q hq
      · rw [h] at hq; cases hq
    · exact hold r ((DtnStore.onAck_records (L := (s.nodes m).L) hnd.nodup bid c o true).1 r hr) q hq
    · exact hold r hr q hq

theorem le_exec {s : Sys} (hR : Reach s) (hC : ChInv s) (ev : Ev) :
    ∀ m ∈ (exec s ev).cfg.ids, ∀ e ∈ ((exec s ev).nodes m).L.entries, e.key = DtnStore.bkey bid →
      e.expires = (exec s ev).cfg.exp := by
  intro m hm e he hk
  rw [exec_cfg] at hm ⊢
  obtain ⟨-, hL, -⟩ := exec_BL s ev m hm
  rw [hL] at he
  have hold := hC.le m hm
  have hnd := node_inv hR m hm
  unfold ledgerAfter at he
  cases hle : ledgerEv s ev m with
  | none => simp only [hle] at he; exact hold e he hk
  | some le =>
    simp only [hle] at he
    rcases ledgerEv_forms s ev m le hle with ⟨rfl, -⟩ | ⟨p, rfl, hev, hoff⟩ | ⟨rfl, -⟩ | ⟨f, rfl⟩ | ⟨c, o, rfl⟩ | ⟨k, rfl⟩
    · exact hold e (DtnStore.expire_sub _ _ e he) hk
    · exact hold e he hk
    · exact hold e (DtnStore.delivered_entries_sub _ _ _ e he) hk
    · rcases DtnStore.accept_entries_exp hnd.inv (s.nodes m).B bid 1 s.cfg.exp f s.t e he with h | ⟨y, hy, rfl⟩ | ⟨-, h⟩
      · exact hold e h hk
      · exact hold y hy hk
      · exact h
    · rcases DtnStore.onAck_entries_shape (L := (s.nodes m).L) hnd.nodup bid c o true e he with h | ⟨x, hx, hxk, rfl⟩
      · exact hold e h hk
      · exact hold x hx hxk
    · rcases DtnStore.admit_entries_sub hnd.inv ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t e he with h | rfl
      · exact hold e h hk
      · simp [DtnStore.bkey] at hk

theorem ackd_exec {s : Sys} (hC : ChInv s) (ev : Ev) (hE : En s ev) :
    ∀ id c p o, Msg.ack id c p o ∈ (exec s ev).msgs → c ∈ (exec s ev).acc ∨ (exec s ev).delivered = true := by
  intro id c p o hm
  obtain ⟨hd, -, -⟩ := exec_mono s ev
  rcases exec_msgs s ev hE _ hm with h | ⟨a, b, c', d, e, f, h⟩ | ⟨id', c', p', o', h, hc⟩
  · rcases hC.ackd id c p o h with h1 | h1
    · left
      rcases exec_acc s ev hE with ha | ⟨r, -, ha⟩
      · rw [ha]; exact h1
      · rw [ha]; exact List.mem_cons_of_mem _ h1
    · exact Or.inr (hd h1)
  · cases h
  · simp only [Msg.ack.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact hc

theorem alive_old {s : Sys} (hR : Reach s) (hI : SysInv s) (hC : ChInv s) (ev : Ev)
    (hrk : s.cfg.ranked = true) (hend : ¬ Ended (exec s ev)) (hna : ∀ n, ¬ ∃ a c o, ev = .ack (.ack a c n o)) :
    ∀ x ∈ s.acc, ∃ n ∈ s.cfg.ids, x ≤ n ∧ Cust (exec s ev) n := by
  intro x hx
  have hend0 : ¬ Ended s := fun h => hend (ended_mono h ev)
  obtain ⟨n, hn, hxn, hcu⟩ := hC.alive hrk hend0 x hx
  exact ⟨n, hn, hxn, cust_keep hR hI hC ev hend n hn hcu (hna n)⟩

theorem alive_ack {s : Sys} (hR : Reach s) (hI : SysInv s) (hC : ChInv s) (id c p o : Nat)
    (hm : Msg.ack id c p o ∈ s.msgs) (hp : p ∈ s.cfg.ids) (hrk : s.cfg.ranked = true)
    (hend : ¬ Ended (exec s (.ack (.ack id c p o)))) :
    ∀ x ∈ s.acc, ∃ n ∈ s.cfg.ids, x ≤ n ∧ Cust (exec s (.ack (.ack id c p o))) n := by
  intro x hx
  have hend0 : ¬ Ended s := fun h => hend (ended_mono h _)
  have hnd := node_inv hR p hp
  obtain ⟨n, hn, hxn, hcu⟩ := hC.alive hrk hend0 x hx
  by_cases hrel : (DtnStore.onAck (s.nodes p).B (s.nodes p).L bid c o true).err = none
  · -- a relief at p: the acknowledging node c accepted custody and some node of at least its id keeps it
    obtain ⟨-, hr, -⟩ := (DtnStore.onAck_ok_iff hnd.nodup bid c o true).1 hrel
    obtain ⟨r, hrm, -, hro⟩ := hr
    have hpc : p < c := hC.rank hrk p hp r hrm c hro.1
    have hdel : s.delivered = false := by
      cases h : s.delivered
      · rfl
      · exact absurd (Or.inl h) hend0
    have hcacc : c ∈ s.acc := by
      rcases hC.ackd id c p o hm with h | h
      · exact h
      · rw [hdel] at h; cases h
    obtain ⟨nc, hnc, hcnc, hcuc⟩ := hC.alive hrk hend0 c hcacc
    have hncp : nc ≠ p := by omega
    have kc : Cust (exec s (.ack (.ack id c p o))) nc :=
      cust_keep hR hI hC _ hend nc hnc hcuc (by
        rintro ⟨a, c', o', h⟩
        simp only [Ev.ack.injEq, Msg.ack.injEq] at h
        exact hncp h.2.2.1.symm)
    by_cases hnp : n = p
    · exact ⟨nc, hnc, by omega, kc⟩
    · exact ⟨n, hn, hxn, cust_keep hR hI hC _ hend n hn hcu (by
        rintro ⟨a, c', o', h⟩
        simp only [Ev.ack.injEq, Msg.ack.injEq] at h
        exact hnp h.2.2.1.symm)⟩
  · -- no relief: the ledger of p is untouched
    refine ⟨n, hn, hxn, ?_⟩
    by_cases hnp : n = p
    · subst hnp
      obtain ⟨e, he, hk, hc⟩ := hcu
      obtain ⟨-, hL, -⟩ := exec_BL s (.ack (.ack id c n o)) n hn
      have hLs : ((exec s (.ack (.ack id c n o))).nodes n).L = (s.nodes n).L := by
        rw [hL]
        have hledg : ledgerEv s (.ack (.ack id c n o)) n = some (.ack bid c o true) := by simp [ledgerEv]
        simp only [ledgerAfter, hledg, DtnStore.step]
        rcases DtnStore.onAck_L_cases (L := (s.nodes n).L) (B := (s.nodes n).B) hnd.nodup bid c o true with h | ⟨h, -⟩
        · exact h
        · exact absurd h hrel
      exact ⟨e, by rw [hLs]; exact he, hk, hc⟩
    · exact cust_keep hR hI hC _ hend n hn hcu (by
        rintro ⟨a, c', o', h⟩
        simp only [Ev.ack.injEq, Msg.ack.injEq] at h
        exact hnp h.2.2.1.symm)

theorem alive_exec {s : Sys} (hR : Reach s) (hI : SysInv s) (hC : ChInv s) (ev : Ev) (hE : En s ev) :
    (exec s ev).cfg.ranked = true → ¬ Ended (exec s ev) →
      ∀ x ∈ (exec s ev).acc, ∃ n ∈ (exec s ev).cfg.ids, x ≤ n ∧ Cust (exec s ev) n := by
  intro hrk hend x hx
  rw [exec_cfg] at hrk ⊢
  have noack : ∀ (e : Ev), (∀ a b c d, e ≠ .ack (.ack a b c d)) → ∀ n, ¬ ∃ a c o, e = .ack (.ack a c n o) :=
    fun e h n ⟨a, c, o, hh⟩ => h a c n o hh
  have old := fun (h : ∀ n, ¬ ∃ a c o, ev = .ack (.ack a c n o)) => alive_old hR hI hC ev hrk hend h
  cases ev with
  | ack mm =>
    cases mm with
    | bun a b c d e f => exact hE.2.elim
    | ack id c p o =>
      have hacc : (exec s (.ack (.ack id c p o))).acc = s.acc := by simp [exec, exec0, Sys.set]
      rw [hacc] at hx
      exact alive_ack hR hI hC id c p o hE.1 hE.2 hrk hend x hx
  | bun mm =>
    cases mm with
    | ack a b c d => exact hE.2.elim
    | bun id from_ r c fresh off =>
      have hna : ∀ n, ¬ ∃ a c' o', Ev.bun (Msg.bun id from_ r c fresh off) = .ack (.ack a c' n o') := by
        rintro n ⟨a, c', o', h⟩; cases h
      by_cases hd : r = s.cfg.dest
      · have hacc : (exec s (.bun (.bun id from_ r c fresh off))).acc = s.acc := by simp [exec, exec0, hd]
        rw [hacc] at hx
        exact old hna x hx
      · cases hacc : (DtnStore.accept (s.nodes r).B (s.nodes r).L bid 1 s.cfg.exp from_ s.t).err with
        | some e =>
          have hacc2 : (exec s (.bun (.bun id from_ r c fresh off))).acc = s.acc := by simp [exec, exec0, hd, hacc, Sys.set]
          rw [hacc2] at hx
          exact old hna x hx
        | none =>
          have hacc2 : (exec s (.bun (.bun id from_ r c fresh off))).acc = r :: s.acc := by simp [exec, exec0, hd, hacc]
          rw [hacc2] at hx
          rcases List.mem_cons.1 hx with rfl | hx'
          · refine ⟨x, hE.2, Nat.le_refl _, ?_⟩
            have hnd := node_inv hR x hE.2
            obtain ⟨-, e, he, hk, hc⟩ := DtnStore.accept_ok hnd.inv hnd.nodup hnd.linked bid 1 s.cfg.exp from_ s.t hacc
            obtain ⟨-, hL, -⟩ := exec_BL s (.bun (.bun id from_ x c fresh off)) x hE.2
            refine ⟨e, ?_, hk, hc⟩
            rw [hL]
            have hledg : ledgerEv s (.bun (.bun id from_ x c fresh off)) x = some (.accept bid 1 s.cfg.exp from_ s.t) := by
              simp [ledgerEv, hd]
            simp only [ledgerAfter, hledg, DtnStore.step]
            exact he
          · exact old hna x hx'
  | contact a b up => exact old (by rintro n ⟨a', c', o', h⟩; cases h) x (by simpa [exec, exec0, Sys.set] using hx)
  | tick => exact old (by rintro n ⟨a', c', o', h⟩; cases h) x (by simpa [exec, exec0] using hx)
  | poll n => exact old (by rintro n' ⟨a', c', o', h⟩; cases h) x (by
      simp only [exec, exec0] at hx; split at hx <;> exact hx)
  | lose m => exact old (by rintro n ⟨a', c', o', h⟩; cases h) x (by simpa [exec, exec0] using hx)
  | press n k => exact old (by rintro n' ⟨a', c', o', h⟩; cases h) x (by
      simp only [exec, exec0] at hx; split at hx <;> exact hx)
  | bad => exact old (by rintro n ⟨a', c', o', h⟩; cases h) x (by simpa [exec, exec0] using hx)

theorem chinv_exec {s : Sys} (hR : Reach s) (hI : SysInv s) (hC : ChInv s) (ev : Ev) (hE : En s ev) :
    ChInv (exec s ev) :=
  ⟨rank_exec hR hC ev, le_exec hR hC ev, ackd_exec hC ev hE, exec_flag s ev, alive_exec hR hI hC ev hE⟩

theorem init_src (c : Cfg) : (Sys.init c).nodes c.src = ⟨(originHold c).1, (originAcc c).B, (originAcc c).L, 0⟩ := by
  simp [Sys.init]

theorem init_other (c : Cfg) (n : Nat) (hn : n ≠ c.src) : (Sys.init c).nodes n = Node.empty c n := by
  simp [Sys.init, hn]

theorem origin_bs_no_flag (c : Cfg) (hhold : (originHold c).2 = .ok) :
    DtnForward.anyS (fun x : DtnForward.Bundle => x.delivered) (originHold c).1.bs = false := by
  have hs := origin_step c hhold
  rcases DtnForward.hold_total _ _ bid c.dest c.exp c.copies _ _ hs bid with ⟨he, _⟩ | ⟨_, _, _, _, i, _, k, _, hf⟩
  · exact absurd rfl he
  · rw [hf]
    cases h : DtnForward.anyS (fun x : DtnForward.Bundle => x.delivered)
        (DtnForward.upd (DtnForward.advance (Node.empty c c.src).f 0).bs i
          fun _ => some ⟨bid, c.dest, c.exp, c.copies, false⟩) with
    | false => rfl
    | true =>
      rcases DtnForward.anyS_upd_fill _ _ _ _ h with h3 | h3
      · simp [DtnForward.anyS, Node.empty, DtnForward.F.new, DtnForward.advance] at h3
      · simp at h3

theorem chinv_init (c : Cfg) (hn : c.ids.Nodup) (hsrc : c.src ∈ c.ids) (hmax : c.lbud ≤ DtnStore.MAX)
    (hacc : (originAcc c).err = none) (hhold : (originHold c).2 = .ok) : ChInv (Sys.init c) := by
  have hB0 : DtnStore.SInv ⟨List.replicate c.bslots none, DtnStore.Ledger.empty (if c.src = c.tight then 0 else c.lbud) c.lslots, 0⟩ :=
    DtnStore.SInv.init _ _ _ (by split <;> omega)
  have hrec0 : ∀ k, DtnStore.recs (List.replicate k (none : Option DtnStore.Record)) = [] := by
    intro k; simp [DtnStore.recs]
  have hent0 : ∀ b k, (DtnStore.Ledger.empty b k).entries = [] := by
    intro b k; simp [DtnStore.Ledger.entries, DtnStore.Ledger.empty]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ m hm r hr q hq
    by_cases hms : m = c.src
    · subst hms
      rw [init_src] at hr
      have hsub := DtnStore.accept_recs_sub (Node.empty c c.src).B (Node.empty c c.src).L bid 1 c.exp 0 0 r hr
      rcases hsub with h | h
      · have : (Node.empty c c.src).B = List.replicate c.bslots none := rfl
        rw [this, hrec0] at h; simp at h
      · rw [h] at hq; cases hq
    · rw [init_other c m hms] at hr
      have : (Node.empty c m).B = List.replicate c.bslots none := rfl
      rw [this, hrec0] at hr; simp at hr
  · intro m hm e he hk
    by_cases hms : m = c.src
    · subst hms
      rw [init_src] at he
      have := DtnStore.accept_entries_exp (B := (Node.empty c c.src).B) hB0.inv bid 1 c.exp 0 0 e he
      rcases this with h | ⟨y, hy, _⟩ | ⟨-, h⟩
      · have h' : e ∈ (DtnStore.Ledger.empty (if c.src = c.tight then 0 else c.lbud) c.lslots).entries := h
        rw [hent0] at h'; simp at h'
      · have h' : y ∈ (DtnStore.Ledger.empty (if c.src = c.tight then 0 else c.lbud) c.lslots).entries := hy
        rw [hent0] at h'; simp at h'
      · exact h
    · rw [init_other c m hms] at he
      have : (Node.empty c m).L = DtnStore.Ledger.empty (if m = c.tight then 0 else c.lbud) c.lslots := rfl
      rw [this, hent0] at he; simp at he
  · intro id c' p o h; simp [Sys.init] at h
  · intro h
    exfalso
    have hf : (Sys.init c).anyFlag = false := by
      unfold Sys.anyFlag
      cases hh : (Sys.init c).cfg.ids.any (fun n => ((Sys.init c).nodes n).f.bs.any fun o => o.any (·.delivered)) with
      | false => rfl
      | true =>
        exfalso
        rw [List.any_eq_true] at hh
        obtain ⟨n, -, hn2⟩ := hh
        by_cases hms : n = c.src
        · subst hms
          rw [init_src] at hn2
          have := origin_bs_no_flag c hhold
          unfold DtnForward.anyS at this
          simp only at hn2
          rw [this] at hn2; cases hn2
        · rw [init_other c n hms] at hn2
          have : (Node.empty c n).f.bs = List.replicate c.fb none := rfl
          rw [this] at hn2
          simp at hn2
    rw [hf] at h; cases h
  · intro _ _ x hx
    have hx' : x ∈ [c.src] := hx
    have hx2 := List.mem_singleton.1 hx'
    subst hx2
    refine ⟨c.src, hsrc, Nat.le_refl _, ?_⟩
    obtain ⟨-, e, he, hk, hc⟩ := DtnStore.accept_ok hB0.inv hB0.nodup hB0.linked bid 1 c.exp 0 0 hacc
    refine ⟨e, ?_, hk, hc⟩
    rw [init_src]
    exact he

theorem reach_chinv {s : Sys} (h : Reach s) : ChInv s := by
  induction h with
  | init c hn hsrc hmax hacc hhold => exact chinv_init c hn hsrc hmax hacc hhold
  | @step s0 ev hR hE ih => exact chinv_exec hR (reach_inv hR) ih ev hE

theorem reach_src_acc {s : Sys} (h : Reach s) : s.cfg.src ∈ s.acc := by
  induction h with
  | init c hn hsrc hmax hacc hhold => exact List.mem_singleton.2 rfl
  | @step s0 ev hR hE ih =>
    rw [exec_cfg]
    rcases exec_acc s0 ev hE with ha | ⟨r, -, ha⟩
    · rw [ha]; exact ih
    · rw [ha]; exact List.mem_cons_of_mem _ ih

/-- **Custody handoff chains.** With custody offered only to a higher node id, in every reachable system and for
every number of nodes, as long as the bundle is not finished (not delivered, no node told of a delivery, not expired)
some node keeps it in custody: the origin keeps it until some node of a higher id has it, and so on up the chain. -/
theorem custody_chain {s : Sys} (h : Reach s) (hrk : s.cfg.ranked = true) (hend : ¬ Ended s) :
    ∃ n ∈ s.cfg.ids, Cust s n := by
  obtain ⟨n, hn, -, hc⟩ := (reach_chinv h).alive hrk hend s.cfg.src (reach_src_acc h)
  exact ⟨n, hn, hc⟩

/-- Every node that accepted custody is itself in custody, or a node of at least its id is. -/
theorem custody_chain_acc {s : Sys} (h : Reach s) (hrk : s.cfg.ranked = true) (hend : ¬ Ended s) :
    ∀ x ∈ s.acc, ∃ n ∈ s.cfg.ids, x ≤ n ∧ Cust s n :=
  (reach_chinv h).alive hrk hend

/-- The delivery flag that ends a bundle for the chain is a node learning, by an ack, of the delivery. -/
theorem flag_means_fin {s : Sys} (h : Reach s) : s.anyFlag = true → s.fin = true := (reach_chinv h).flag

#audit_axioms Pinc.DtnScenario.custody_chain
#audit_axioms Pinc.DtnScenario.custody_chain_acc

end Pinc.DtnScenario
