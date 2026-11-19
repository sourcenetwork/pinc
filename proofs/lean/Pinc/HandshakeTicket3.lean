import Pinc.HandshakeTicket2

/-!
# Resumption: the client stores, and `Inv4` holds in every reachable state

The step proofs of the client-store clauses of `Inv4`: a ticket enters a client store only when a finished session
hands over the tickets of the responder session it finished with (`accept_batch`), and every ticket in a store or
a snapshot is a ticket of the ledger of an honest peer whose pre-shared key the attacker does not know. Then the
assembly of all clauses: `Inv4` holds in every reachable state, for any number of nodes, sessions and tickets and
any store capacities.
-/

namespace Pinc.Hs
open Term

theorem CliTk_mono {g g' : G} (hs : Step g g') {n : Nat} {tk : Tk} (h : CliTk g n tk) : CliTk g' n tk := by
  obtain ⟨a, b, c, t, ht, e⟩ := h
  exact ⟨a, b, c, t, issued_mono hs t ht, e⟩

/-- The tickets a finished session hands to its node's store are tickets of the ledger of its peer. -/
theorem accept_cli {K C : Nat} {g : G} (hr : Reach K C g) (h4 : Inv4 g) (s0 : Nat × Nat) (tids : List Term)
    (hn : s0.1 ≠ att) (hph : (g.ist s0).ph = .done) (hpe : (g.ist s0).peer ≠ att) (hat : AcceptTids g s0 tids) :
    ∀ tk ∈ acceptTks (g.ist s0) tids, CliTk g s0.1 tk := by
  have hdata : ∃ r, Est (g.rst r).ph ∧ r.1 = (g.ist s0).peer ∧ (g.ist s0).res = (g.rst r).res ∧
      (g.ist s0).pcr = RCr r.1 ∧ (g.rst r).peer = s0.1 ∧ tids = (g.rst r).mytids := by
    by_cases hres : (g.ist s0).resumed = true
    · simp only [AcceptTids, hres, if_true] at hat
      obtain ⟨r, hE, -, -, htids, hres2, hpcr, hr1, hpeer⟩ := h4.ires2 s0 hph hres
      exact ⟨r, hE, hr1, hres2, hpcr, hpeer, hat.trans htids⟩
    · have hres' : (g.ist s0).resumed = false := by simpa using hres
      simp only [AcceptTids, hres', Bool.false_eq_true, if_false] at hat
      obtain ⟨r, hr1, hrd, hth, hmy⟩ := hat
      have hflag := agreement_resumed_flag hr s0 r hph hrd hth.symm
      obtain ⟨-, -, hres3, -, hpeer, hrp, -, -, hpcr, -, -⟩ :=
        agreement_full hr s0 r hph hrd hres' (by rw [← hflag]; exact hres') hth.symm
      exact ⟨r, Or.inl hrd, hr1.symm ▸ hpeer.symm ▸ rfl, hres3, hpcr, hrp, hmy⟩
  obtain ⟨r, hE, hr1, hres, hpcr, hrp, hmy⟩ := hdata
  intro tk htk
  simp only [acceptTks, List.mem_map] at htk
  obtain ⟨t, ht, rfl⟩ := htk
  obtain ⟨e, he, e1, e2, e3, e4, e5⟩ := h4.myt r hE t (by rw [← hmy]; exact ht)
  have hpsk : psk (g.ist s0).res t (g.ist s0).pcr = e.psk := by rw [e2, hres, hpcr]
  refine ⟨hpe, ⟨r.2, ?_⟩, ?_, e, he, e1, hpsk.symm, by rw [e3, hrp], by rw [e5, hpcr]⟩
  · show pskSess (psk (g.ist s0).res t (g.ist s0).pcr) = some ((g.ist s0).peer, r.2)
    rw [hpsk, e4, ← hr1]
  · show ¬ Known (psk (g.ist s0).res t (g.ist s0).pcr)
    rw [hpsk]
    exact h4.lsec e he (by rw [e3, hrp]; exact hn)

theorem cli_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ n x, x ∈ g'.cli n → x.occ = true → CliTk g' n (TicketOf x) := by
  have hs0 := hs
  cases hs with
  | iStart s0 peer al short take hn hph hpe =>
    intro n x hx ho
    by_cases e : n = s0.1
    · subst e
      have hx' : x ∈ (if take = true then CTake (g.cli s0.1) peer al else (⟨g.cli s0.1, none⟩ : CTakeRes)).sl := by
        have : (stepIStart g s0 peer al short take).cli s0.1 = (if take = true then CTake (g.cli s0.1) peer al
            else (⟨g.cli s0.1, none⟩ : CTakeRes)).sl := by
          show upd g.cli s0.1 _ s0.1 = _; rw [upd_same]
        rw [this] at hx; exact hx
      have : x ∈ g.cli s0.1 := by
        by_cases ht : take = true
        · simp only [ht, if_true] at hx'; exact CTake_mem hx' ho
        · simp only [ht, if_false] at hx'; exact hx'
      exact CliTk_mono hs0 (h4.cli s0.1 x this ho)
    · have : (stepIStart g s0 peer al short take).cli n = g.cli n := upd_ne _ _ _ _ e
      rw [this] at hx
      exact CliTk_mono hs0 (h4.cli n x hx ho)
  | iAccept s0 tids hn hph hacc hpe hat =>
    intro n x hx ho
    by_cases e : n = s0.1
    · subst e
      have : (stepIAccept g s0 tids).cli s0.1 = CInsertAll (g.cli s0.1) (acceptTks (g.ist s0) tids) := by
        show upd g.cli s0.1 _ s0.1 = _; rw [upd_same]
      rw [this] at hx
      rcases CInsertAll_mem _ hx with hx | ⟨tk, htk, e'⟩
      · exact CliTk_mono hs0 (h4.cli s0.1 x hx ho)
      · rw [e']; exact CliTk_mono hs0 (accept_cli hr h4 s0 tids hn hph hpe hat tk htk)
    · have : (stepIAccept g s0 tids).cli n = g.cli n := upd_ne _ _ _ _ e
      rw [this] at hx
      exact CliTk_mono hs0 (h4.cli n x hx ho)
  | expireC n0 i sl hn hsl hocc hexp =>
    intro n x hx ho
    by_cases e : n = n0
    · subst e
      have : (stepExpireC g n i).cli n = (g.cli n).modify i (fun sl => { sl with exp := true }) := by
        show upd g.cli n _ n = _; rw [upd_same]
      rw [this] at hx
      rcases mem_modify hx with hx | ⟨y, hy, rfl⟩
      · exact CliTk_mono hs0 (h4.cli n x hx ho)
      · exact CliTk_mono hs0 (h4.cli n y hy ho)
    · have : (stepExpireC g n0 i).cli n = g.cli n := upd_ne _ _ _ _ e
      rw [this] at hx
      exact CliTk_mono hs0 (h4.cli n x hx ho)
  | restore n0 drop hn =>
    intro n x hx ho
    by_cases e : n = n0
    · subst e
      have : (stepRestore g n drop).cli n = CInsertAll (g.cli n) (KeepSeq (g.snap n) drop 0) := by
        show upd g.cli n _ n = _; rw [upd_same]
      rw [this] at hx
      rcases CInsertAll_mem _ hx with hx | ⟨tk, htk, e'⟩
      · exact CliTk_mono hs0 (h4.cli n x hx ho)
      · rw [e']; exact CliTk_mono hs0 (h4.snap n tk (KeepSeq_mem _ _ _ htk))
    · have : (stepRestore g n0 drop).cli n = g.cli n := upd_ne _ _ _ _ e
      rw [this] at hx
      exact CliTk_mono hs0 (h4.cli n x hx ho)
  | restart n0 hn =>
    intro n x hx ho
    by_cases e : n = n0
    · subst e
      have : (stepRestart g n).cli n = (g.cli n).map (fun _ => NoSlot) := by
        show upd g.cli n _ n = _; rw [upd_same]
      rw [this] at hx
      simp only [List.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      simp [NoSlot] at ho
    · have : (stepRestart g n0).cli n = g.cli n := upd_ne _ _ _ _ e
      rw [this] at hx
      exact CliTk_mono hs0 (h4.cli n x hx ho)
  | _ => intro n x hx ho; exact CliTk_mono hs0 (h4.cli n x hx ho)

theorem snap_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ n tk, tk ∈ g'.snap n → CliTk g' n tk := by
  have hs0 := hs
  cases hs with
  | «export» n0 mx hn =>
    intro n tk htk
    by_cases e : n = n0
    · subst e
      have : (stepExport g n mx).snap n = CExport (g.cli n) mx := by
        show upd g.snap n _ n = _; rw [upd_same]
      rw [this] at htk
      obtain ⟨y, hy, ho, rfl⟩ := CExport_mem htk
      exact CliTk_mono hs0 (h4.cli n y hy ho)
    · have : (stepExport g n0 mx).snap n = g.snap n := upd_ne _ _ _ _ e
      rw [this] at htk
      exact CliTk_mono hs0 (h4.snap n tk htk)
  | _ => intro n tk htk; exact CliTk_mono hs0 (h4.snap n tk htk)

theorem Inv4_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') : Inv4 g' :=
  ⟨(led_step hr h4 hs).1, (led_step hr h4 hs).2, myt_step hr h4 hs, rok_step hr h4 hs, hauth_step hr h4 hs,
    iloc_step hr h4 hs, ick_step hr h4 hs, ires2_step hr h4 hs, cli_step hr h4 hs, snap_step hr h4 hs,
    netConf_step hr h4 hs, netHello_step hr h4 hs⟩

/-- Every reachable state satisfies the invariant. -/
theorem Inv4_reach {K C : Nat} {g : G} (h : Reach K C g) : Inv4 g := by
  induction h with
  | init => exact Inv4_init K C
  | step hr hs ih => exact Inv4_step hr ih hs

#audit_axioms Pinc.Hs.Inv4_reach

end Pinc.Hs
