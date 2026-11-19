import Pinc.DtnScenarioChain

/-!
# Time in a scenario: expiry during an outage, frozen timers

* `tick_expires`: when a tick reaches the expiry of the bundle, every node's ledger drops it and every book drops its
  record, whatever the links did and whether or not any contact happened since the bundle was created.
* `expiry_release`: after such a tick every forwarder that holds the bundle releases it at its next poll (the clock
  alone decides, the links and the timers do not enter).
* `tick_frozen`: a tick never runs a retransmission timer whose link is down; the timer keeps its remaining time
  exactly.
-/

namespace Pinc.DtnScenario

theorem tick_expires {s : Sys} (h : Reach s) (hexp : s.cfg.exp ≤ s.t + 1) :
    ∀ n ∈ s.cfg.ids, DtnStore.holds ((exec s .tick).nodes n).B bid = false ∧
      ((exec s .tick).nodes n).L.contains (DtnStore.bkey bid) = false := by
  intro n hn
  have hC := reach_chinv h
  obtain ⟨hB, hL, -⟩ := exec_BL s .tick n hn
  have hledg : ledgerEv s .tick n = some (.bexpire (s.t + 1)) := by simp [ledgerEv]
  have hfun : ledgerAfter s .tick n = DtnStore.step ⟨(s.nodes n).B, (s.nodes n).L, (s.nodes n).nx⟩ (.bexpire (s.t + 1)) := by
    simp [ledgerAfter, hledg]
  have hnone : ((exec s .tick).nodes n).L.contains (DtnStore.bkey bid) = false := by
    rw [hL, hfun]
    obtain ⟨-, -, hent⟩ := DtnStore.bexpire_exits (s.nodes n).B (s.nodes n).L (s.t + 1)
    cases hc : (DtnStore.step ⟨(s.nodes n).B, (s.nodes n).L, (s.nodes n).nx⟩ (.bexpire (s.t + 1))).L.contains (DtnStore.bkey bid) with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨e, he, hk⟩ := DtnStore.contains_iff.1 hc
      have he' : e ∈ (DtnStore.bexpire (s.nodes n).B (s.nodes n).L (s.t + 1)).L.entries := he
      rw [hent] at he'
      obtain ⟨he1, he2⟩ := List.mem_filter.1 he'
      have := hC.le n hn e he1 hk
      simp only [DtnStore.expiredAt, Bool.not_eq_true', decide_eq_false_iff_not] at he2
      omega
  refine ⟨?_, hnone⟩
  cases hh : DtnStore.holds ((exec s .tick).nodes n).B bid with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨r, hr, hrb⟩ := DtnStore.holds_iff.1 hh
    rw [hB, hfun] at hr
    have := (DtnStore.bexpire_exits (s.nodes n).B (s.nodes n).L (s.t + 1)).1 r hr
    rw [hrb] at this
    rw [hL, hfun] at hnone
    have hn2 : (DtnStore.bexpire (s.nodes n).B (s.nodes n).L (s.t + 1)).L.contains (DtnStore.bkey bid) = false := hnone
    rw [hn2] at this
    cases this

theorem tick_forwarder (s : Sys) (n : Nat) (hn : n ∈ s.cfg.ids) :
    ((exec s .tick).nodes n).f = DtnForward.advance (s.nodes n).f (s.t + 1) := by
  simp [exec, exec0, hn, DtnForward.step]

/-- **Expiry is wall-clock.** After a tick that reaches the expiry, a forwarder that holds the bundle releases it at
its next poll, whatever its links and timers say. -/
theorem expiry_release {s : Sys} (h : Reach s) (hexp : s.cfg.exp ≤ s.t + 1) (n : Nat) (hn : n ∈ s.cfg.ids)
    (i : Nat) (b : DtnForward.Bundle) (hb : DtnForward.slot ((exec s .tick).nodes n).f.bs i = some b) :
    ∃ id, (DtnForward.poll ((exec s .tick).nodes n).f).2 = .release id := by
  have hI := reach_inv h
  rw [tick_forwarder s n hn] at hb ⊢
  have hx := hI.fwd n hn
  have hbok := (hx.bok i b hb).2.1
  have hnow : (DtnForward.advance (s.nodes n).f (s.t + 1)).now = max (s.nodes n).f.now (s.t + 1) := rfl
  have hle : (s.nodes n).f.now ≤ s.t := hx.now
  cases hd : DtnForward.doneIdx (DtnForward.advance (s.nodes n).f (s.t + 1)) with
  | none =>
    exfalso
    have := DtnForward.firstIdx_none hd i
    unfold DtnForward.doneIdx at hd
    have hb' : DtnForward.slot (DtnForward.advance (s.nodes n).f (s.t + 1)).bs i = some b := hb
    simp only [hb', Option.any_some, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
    rw [hnow] at this
    omega
  | some j =>
    obtain ⟨b', -, -, hp⟩ := DtnForward.poll_release_done _ j hd
    exact ⟨b'.id, by rw [hp]⟩

/-- **Timers are frozen while a link is down.** A tick leaves a running retransmission timer on a link that is down
exactly as it was. -/
theorem tick_frozen (s : Sys) (n : Nat) (hn : n ∈ s.cfg.ids) (i : Nat) (t : DtnForward.Transfer)
    (h : DtnForward.slot (s.nodes n).f.ts i = some t) (hd : DtnForward.upLink (s.nodes n).f.ls t.peer = false) :
    DtnForward.slot ((exec s .tick).nodes n).f.ts i = some t := by
  rw [tick_forwarder s n hn]
  exact DtnForward.advance_timer_down _ _ i t h hd

/-- And on a link that is up it is charged exactly the time that passed (down to 0). -/
theorem tick_charged (s : Sys) (n : Nat) (hn : n ∈ s.cfg.ids) (i r k : Nat) (t : DtnForward.Transfer)
    (h : DtnForward.slot (s.nodes n).f.ts i = some t) (hp : t.phase = .sent r k)
    (hu : DtnForward.upLink (s.nodes n).f.ls t.peer = true) :
    DtnForward.slot ((exec s .tick).nodes n).f.ts i =
      some { t with phase := .sent (r - (s.t + 1 - (s.nodes n).f.now)) k } := by
  rw [tick_forwarder s n hn]
  exact DtnForward.advance_timer_up _ _ i r k t h hp hu

/-! ### Liveness: a contact with the destination delivers the bundle -/

theorem exec_bun_dest (s : Sys) (id f r c : Nat) (fr : Bool) (off : Nat) (hr : r = s.cfg.dest) :
    (exec s (.bun (.bun id f r c fr off))).delivered = true := by
  subst hr
  simp [exec, exec0]

/-- A contact to `peer` brings the link up on the side that learns of it, if the link table has a slot for it. -/
theorem contact_brings_link_up (f : DtnForward.F) (n peer : Nat)
    (hroom : (∃ i l, DtnForward.slot (DtnForward.advance f n).ls i = some l ∧ l.peer = peer) ∨
      (DtnForward.freeIdx (DtnForward.advance f n).ls).isSome = true) :
    DtnForward.upLink (DtnForward.step f n (.linkUp peer)).1.ls peer = true := by
  unfold DtnForward.step
  simp only
  cases hf : DtnForward.firstIdx (·.peer == peer) (DtnForward.advance f n).ls with
  | some i =>
    obtain ⟨l, hl, hp, -⟩ := DtnForward.firstIdx_some hf
    have hlen : i < (DtnForward.advance f n).ls.length := by
      refine Classical.byContradiction fun hlt => ?_
      have : DtnForward.slot (DtnForward.advance f n).ls i = none := by
        unfold DtnForward.slot
        rw [List.getElem?_eq_none (by omega)]; rfl
      rw [this] at hl; cases hl
    unfold DtnForward.upLink
    rw [DtnForward.anyS_iff]
    refine ⟨i, { l with up := true }, ?_, by simpa using hp⟩
    have := DtnForward.slot_upd_same (DtnForward.advance f n).ls i (Option.map fun l => { l with up := true }) hlen
    simpa [hl] using this
  | none =>
    cases hfr : DtnForward.freeIdx (DtnForward.advance f n).ls with
    | none =>
      exfalso
      rcases hroom with ⟨i, l, hl, hp⟩ | h
      · have := DtnForward.firstIdx_of_slot (p := (·.peer == peer)) hl (by simpa using hp)
        rw [hf] at this; cases this
      · rw [hfr] at h; cases h
    | some i =>
      obtain ⟨hsn, hsl⟩ := DtnForward.freeIdx_some hfr
      unfold DtnForward.upLink
      rw [DtnForward.anyS_iff]
      refine ⟨i, ⟨peer, true⟩, ?_, by simp⟩
      exact DtnForward.slot_upd_same _ _ _ hsl

/-- **A holder whose link to the destination is up delivers.** In a reachable system, if a node that is not the
destination holds the bundle undelivered before its expiry, the link to the destination is up and no other link is,
no transfer to the destination exists and the transfer table has a free slot, then its next poll hands the bundle to
the destination (a delivery send with no copies), and delivering that message makes the destination receive it.
These are the side conditions of the liveness: a contact, room in the transfer table, the expiry not reached. -/
theorem delivery_schedule {s : Sys} (h : Reach s) (n : Nat) (hn : n ∈ s.cfg.ids) (hd : s.cfg.dest ∈ s.cfg.ids)
    (hexp : s.t < s.cfg.exp)
    (hundel : ∀ i b, DtnForward.slot (s.nodes n).f.bs i = some b → b.delivered = false)
    (hheld : ∃ bi b, DtnForward.slot (s.nodes n).f.bs bi = some b)
    (hlink : ∃ li l, DtnForward.slot (s.nodes n).f.ls li = some l ∧ l.peer = s.cfg.dest ∧ l.up = true)
    (hothers : ∀ i l, DtnForward.slot (s.nodes n).f.ls i = some l → l.peer ≠ s.cfg.dest → l.up = false)
    (hnot : DtnForward.anyS (fun t => t.bundle == bid && t.peer == s.cfg.dest) (s.nodes n).f.ts = false)
    (hroom : ∃ s0, DtnForward.slot (s.nodes n).f.ts s0 = none ∧ s0 < (s.nodes n).f.ts.length) :
    En s (.poll n) ∧ ∃ m, m ∈ (exec s (.poll n)).msgs ∧ En (exec s (.poll n)) (.bun m) ∧
      (exec (exec s (.poll n)) (.bun m)).delivered = true := by
  have hI := reach_inv h
  have hx := hI.fwd n hn
  obtain ⟨bi, b, hb⟩ := hheld
  obtain ⟨li, l, hl, hlp, hlu⟩ := hlink
  obtain ⟨s0, hs0, hs0l⟩ := hroom
  have hbid := (hx.bok bi b hb)
  have hbdest : b.dest = s.cfg.dest := hbid.2.2
  have hno : DtnForward.anyS (fun t => t.bundle == b.id && t.peer == l.peer) (s.nodes n).f.ts = false := by
    rw [hbid.1, hlp]; exact hnot
  have hok : (l.peer == b.dest || b.copies / 2 != 0) = true := by simp [hlp, hbdest]
  have hne := DtnForward.poll_serves_ready (s.nodes n).f hl hlu hb hno hok hs0 hs0l
  have hdone : DtnForward.doneIdx (s.nodes n).f = none := by
    cases hdi : DtnForward.doneIdx (s.nodes n).f with
    | none => rfl
    | some i =>
      exfalso
      obtain ⟨b', hb', hcase, -⟩ := DtnForward.poll_release_done _ i hdi
      rcases hcase with hdl | hex
      · rw [hundel i b' hb'] at hdl; cases hdl
      · have := (hx.bok i b' hb').2.1
        have := hx.now
        omega
  cases hp : DtnForward.poll (s.nodes n).f with
  | mk f' a =>
    rw [hp] at hne
    simp only at hne
    cases a with
    | none => exact absurd rfl hne
    | release id =>
      exfalso
      obtain ⟨i, b', hdi, -⟩ := DtnForward.poll_release_only_done _ _ id hp
      rw [hdone] at hdi; cases hdi
    | send p id c r =>
      obtain ⟨-, hret, hfresh⟩ := DtnForward.poll_send_spec hp
      have hup : DtnForward.upLink (s.nodes n).f.ls p = true := by
        cases r
        · exact (hfresh rfl).1
        · obtain ⟨i, t, s1, -, -, hu, -⟩ := hret rfl
          exact hu
      have hpd : p = s.cfg.dest := by
        unfold DtnForward.upLink at hup
        obtain ⟨j, l', hj, hu'⟩ := (DtnForward.anyS_iff _ _).1 hup
        simp only [Bool.and_eq_true, beq_iff_eq] at hu'
        refine Classical.byContradiction fun hpn => ?_
        have := hothers j l' hj (by rw [hu'.2]; exact hpn)
        rw [hu'.1] at this; cases this
      have hr : r = false := by
        cases r
        · rfl
        · exfalso
          obtain ⟨i, t, s1, hts, -, -, -, hpe, hbu, -⟩ := hret rfl
          have hlive := hx.live i t hts
          obtain ⟨j, b', hj, hb'⟩ := (DtnForward.anyS_iff _ _).1 hlive
          have hb1 := (hx.bok j b' hj).1
          simp only [beq_iff_eq] at hb'
          have ht : t.bundle = bid := by rw [← hb', hb1]
          have := DtnForward.anyS_iff (fun t : DtnForward.Transfer => t.bundle == bid && t.peer == s.cfg.dest) (s.nodes n).f.ts
          rw [hnot] at this
          have h2 : false = true := this.2 ⟨i, t, hts, by simp [ht, hpe, hpd]⟩
          cases h2
      subst hr
      obtain ⟨-, -, bi2, b2, hb2, hid2, -, hcase⟩ := hfresh rfl
      have hb2dest := (hx.bok bi2 b2 hb2).2.2
      have hc0 : c = 0 := by
        rcases hcase with ⟨-, h0⟩ | ⟨hne2, -⟩
        · exact h0
        · exact absurd (hpd.trans hb2dest.symm) hne2
      subst hc0
      subst hpd
      have hE : En s (.poll n) := hn
      have hexec : (exec s (.poll n)).msgs = Msg.bun s.seq n s.cfg.dest 0 true 0 :: s.msgs := by
        simp [exec, exec0, hp]
      refine ⟨hE, Msg.bun s.seq n s.cfg.dest 0 true 0, by rw [hexec]; exact List.mem_cons_self, ?_, ?_⟩
      · refine ⟨by rw [hexec]; exact List.mem_cons_self, ?_⟩
        show s.cfg.dest ∈ (exec s (.poll n)).cfg.ids
        rw [exec_cfg]; exact hd
      · exact exec_bun_dest _ _ _ _ _ _ _ (by rw [exec_cfg])

#audit_axioms Pinc.DtnScenario.delivery_schedule
#audit_axioms Pinc.DtnScenario.contact_brings_link_up
#audit_axioms Pinc.DtnScenario.tick_expires
#audit_axioms Pinc.DtnScenario.expiry_release
#audit_axioms Pinc.DtnScenario.tick_frozen

end Pinc.DtnScenario
