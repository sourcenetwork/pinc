import Vinc.BroadcastNodeLemmas5

/-!
# Broadcast node: the access answer, the sweep and the timer

`Post p N now r` for `AcpAnswer` and `OnTimer` (the sweep, and the end of the floor wait, which settles the floors
with nothing learned from the hubs).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Vinc.BroadcastNode

/-! ## `acp_answer` -/

theorem acp1_len {p : Params} {N : Node} (hI : NodeInv p N) (origin : Nat) (allow : Bool) (now : Nat)
    (acp1 : List (Nat × AcpE))
    (h : acp1 = if (N.acp.lookup origin).isSome || decide (N.acp.length < p.acpMax) then
        (if (N.acp.lookup origin).isSome then
          N.acp.map (fun e => if e.1 == origin then (origin, ⟨allow, now + p.acpCap⟩) else e)
         else N.acp ++ [(origin, ⟨allow, now + p.acpCap⟩)])
      else N.acp) : acp1.length ≤ p.acpMax := by
  subst h
  have := hI.acpLen
  by_cases h1 : (N.acp.lookup origin).isSome = true
  · simp [h1, this]
  · by_cases h2 : N.acp.length < p.acpMax
    · simp [h1, h2]; omega
    · simp [h1, h2, this]

theorem acp_delta (held : List Ent) (o : Nat) (allow : Bool) (x : Nat) :
    ((if allow = true then held.filter (fun e => e.origin == o) else []).map (·.mid)).count x
      + ((held.filter (fun e => e.origin != o)).map (·.mid)).count x ≤ (held.map (·.mid)).count x := by
  have cs := count_filter_split (fun e => e.origin == o) x held
  have e : held.filter (fun e => e.origin != o) = held.filter (fun e => !(e.origin == o)) := rfl
  rw [e]
  by_cases hal : allow = true
  · simp only [hal, if_true]; omega
  · have hal' : allow = false := by simpa using hal
    subst hal'
    simp only [Bool.false_eq_true, if_false, List.map_nil, List.count_nil]; omega

theorem AcpAnswer_post {p : Params} {N : Node} {now id : Nat} {allow : Bool} (hI : NodeInv p N) :
    Post p N now (AcpAnswer p N now id allow) := by
  unfold AcpAnswer
  rcases hf : N.checks.find? (fun c => c.id == id) with _ | c
  · simp only [hf]
    exact Post_req hI N.req [] 0 (by simp)
  · simp only [hf]
    generalize hacc1 : (if (N.acp.lookup c.origin).isSome || decide (N.acp.length < p.acpMax) then
        (if (N.acp.lookup c.origin).isSome then
          N.acp.map (fun e => if e.1 == c.origin then (c.origin, ⟨allow, now + p.acpCap⟩) else e)
         else N.acp ++ [(c.origin, ⟨allow, now + p.acpCap⟩)])
      else N.acp) = acp1
    have hl1 := acp1_len hI c.origin allow now acp1 hacc1.symm
    have hmine : ∀ e ∈ (N.held.filter (fun e => e.origin == c.origin)), e ∈ N.held ∧ e.origin = c.origin := by
      intro e he; simp only [List.mem_filter, beq_iff_eq] at he; exact he
    have hI1 : NodeInv p {N with checks := N.checks.eraseP (fun c => c.id == id), acp := acp1, held := N.held.filter (fun e => e.origin != c.origin)} := by
      refine ⟨hI.seen, ?_, hI.fholdLen, ?_, hI.lgLen, hl1, ?_, hI.fholdNodup, ?_, hI.hubPhase, hI.memberLg, ?_, ?_⟩
      · exact Nat.le_trans (List.length_filter_le _ _) hI.heldLen
      · exact Nat.le_trans List.eraseP_sublist.length_le hI.checksLen
      · intro hd; exact (hI.heldNodup hd).sublist ((List.filter_sublist.map _))
      · exact hI.checksNodup.sublist (List.eraseP_sublist.map _)
      · intro h1 h2; simp [hI.gatherHeld h1 h2]
      · intro e he
        exact hI.heldNotOld e (List.mem_filter.1 he).1
    refine ⟨hI1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro mid org ts via h
      simp only [List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨e, he, h⟩
      · cases h
      · simp only [TraceRec.delivered.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        refine ⟨fun h => (by cases h), fun _ => ⟨id, ?_⟩⟩
        have hal : allow = true := by
          refine Classical.byContradiction fun hn => ?_
          simp [hn] at he
        subst hal
        simp
    · intro id' org h
      simp only [List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨e, he, h⟩
      · simp only [TraceRec.acpAnswered.injEq] at h
        obtain ⟨_, hal, rfl⟩ := h
        subst hal
        refine ⟨fun e he => ?_, fun mid ts via hv => ?_⟩
        · exact fun hh => by simpa [hh] using (List.mem_filter.1 he).2
        · simp only [List.mem_cons, List.mem_map] at hv
          rcases hv with hv | ⟨e, he, hv⟩
          · cases hv
          · simp at he
      · cases h
    · intro mid org ts via h
      simp only [List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨e, he, h⟩
      · cases h
      · simp only [TraceRec.delivered.injEq] at h
        obtain ⟨rfl, rfl, rfl, _⟩ := h
        have hm : e ∈ N.held ∧ e.origin = c.origin := by
          by_cases hal : allow = true
          · simp only [hal, if_true] at he; exact hmine e he
          · simp [hal] at he
        have := hI.heldNotOld e hm.1
        rw [hm.2] at this
        exact this
    · intro x
      have key := acp_delta N.held c.origin allow x
      have hNe : NewRec p now N {N with checks := N.checks.eraseP (fun c => c.id == id), acp := acp1, held := N.held.filter (fun e => e.origin != c.origin)} x = false := by simp [NewRec]
      simp only [hNe, Bool.false_eq_true, if_false, Nat.add_zero]
      exact key
    · intro hd
      show (List.map _ (if allow = true then _ else _)).Nodup
      by_cases hal : allow = true
      · simp only [hal, if_true]
        exact (hI.heldNodup hd).sublist ((List.filter_sublist.map _))
      · simp [hal]
    · intro _ A hJ
      exact ⟨fun x hx => by simpa using hJ.1 x hx, fun x hx => by simpa using hJ.2 x hx⟩
    · intro hh hg o ho
      have hn := hI.gatherHeld hh hg
      simp only [List.mem_cons, List.mem_map] at ho
      rcases ho with rfl | ⟨e, he, rfl⟩
      · simp [NoDel]
      · exfalso
        by_cases hal : allow = true
        · simp [hal, hn] at he
        · simp [hal] at he
    · intro h; exact ⟨h, rfl⟩

/-! ## The sweep and the timer -/

theorem Sweep_inv {p : Params} {N : Node} {now : Nat} (hcap : 0 < p.seenCap) (hI : NodeInv p N) :
    NodeInv p (Sweep p N now) := by
  unfold Sweep
  dsimp only
  have EL := LExpire_spec p N.lg now
  generalize LExpire p N.lg now = e at EL ⊢
  refine hI.withSeenLg (SweepIds_inv hcap _ (SExpire_inv hI.seen)) (Nat.le_trans EL.len hI.lgLen) (fun h => ?_)
  rcases hh : e.log.entries with _ | ⟨x, xs⟩
  · rfl
  · exfalso
    have := EL.new x.mid (by simp [LIds, hh])
    simp [LIds, hI.memberLg h] at this

theorem Sweep_J {p : Params} {N : Node} {now : Nat} (A : List Nat) (hJ : JInv A N) : JInv A (Sweep p N now) := by
  unfold Sweep
  dsimp only
  have EL := LExpire_spec p N.lg now
  generalize LExpire p N.lg now = e at EL ⊢
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases SweepIds_map_sub p now e.ev _ x hx with h | h
    · rcases EL.evSub x h with h | h
      · exact absurd h (by simp)
      · exact hJ.2 x h
    · apply hJ.1 x
      intro hn
      apply h
      cases hs : (SExpire p N.seen now).map x with
      | none => rfl
      | some t =>
        have := SExpireAux_map_sub p now x _ N.seen t hs
        rw [hn] at this; cases this
  · exact hJ.2 x (EL.new x hx)

theorem Sweep_member {p : Params} {N : Node} {now : Nat} (hm : p.isHub = false) (hI : NodeInv p N) :
    (Sweep p N now).seen = SExpire p N.seen now := by
  unfold Sweep
  dsimp only
  have EL := LExpire_spec p N.lg now
  generalize LExpire p N.lg now = e at EL ⊢
  have : e.ev = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro x hx
    rcases EL.evSub x hx with h | h
    · simp at h
    · simp [LIds, hI.memberLg hm] at h
  rw [this]
  rfl

theorem FloorsSettled_post2 {p : Params} {N X : Node} {now : Nat} (hcap : 0 < p.seenCap) (hI : NodeInv p X)
    (hg : X.phase = .gathering) (used : Bool) (rf : Option Nat) (of_ : Option (Nat → Option Nat)) (nh : Bool)
    (hheldX : X.held = N.held)
    (hms : ∀ x, SContains p X.seen x now = false → SContains p N.seen x now = false)
    (hS : p.heldFullKeepsUnseen = true → ∀ A, JInv A N → ∀ x, X.seen.map x ≠ none → x ∈ A)
    (hL : p.heldFullKeepsUnseen = true → ∀ A, JInv A N → ∀ x ∈ LIds X.lg, x ∈ A) :
    Post p N now (FloorsSettled p X now used rf of_ nh) := by
  have hhub : p.isHub = false := by
    cases h : p.isHub
    · rfl
    · have := hI.hubPhase h; rw [hg] at this; cases this
  have hheld : X.held = [] := hI.gatherHeld hhub hg
  have hI1 : NodeInv p {X with phase := .done, rfloor := rf, ofloor := of_, nohist := nh, fhold := []} :=
    ⟨hI.seen, hI.heldLen, (by simp), hI.checksLen, hI.lgLen, hI.acpLen, hI.heldNodup, (by simp), hI.checksNodup,
     (fun h => absurd h (by simp [hhub])), hI.memberLg, (fun _ h => by cases h),
     (fun e he => by simp [hheld] at he)⟩
  unfold FloorsSettled
  have T := offerAllTrans p now X.fhold (Plain {X with phase := .done, rfloor := rf, ofloor := of_, nohist := nh, fhold := []} [.floorDone used])
  generalize OfferAll p now (Plain {X with phase := .done, rfloor := rf, ofloor := of_, nohist := nh, fhold := []} [.floorDone used]) X.fhold = r at T ⊢
  have hph : r.n.phase = .done := T.core.phase
  refine Post_of_chain hcap hI1 T rfl (by simp [Plain, NoDA]) hheldX (fun h => by rw [hph] at h; cases h)
    (fun x _ h => hms x h) (fun _ => hI.fholdNodup) ?_ ?_ (fun _ h => by rw [hph] at h; cases h)
  · intro hk A hJ x hx; exact List.mem_append_left _ (hS hk A hJ x hx)
  · intro hk A hJ x hx; exact Or.inl (List.mem_append_left _ (hL hk A hJ x hx))

theorem OnTimer_post {p : Params} {N : Node} {now : Nat} (hcap : 0 < p.seenCap) (hI : NodeInv p N) :
    Post p N now (OnTimer p N now) := by
  unfold OnTimer
  dsimp only
  have hSw := Sweep_inv (now := now) hcap hI
  by_cases hs : (Sweep p N now).phase = .gathering ∧ p.floorWait < now - (Sweep p N now).born
  · rw [if_pos hs]
    have hg : N.phase = .gathering := hs.1
    have hhub : p.isHub = false := by
      cases h : p.isHub
      · rfl
      · have := hI.hubPhase h; rw [hg] at this; cases this
    refine FloorsSettled_post2 hcap hSw hs.1 false none none false rfl ?_ ?_ ?_
    · intro x hx
      refine Classical.byContradiction fun hc => ?_
      have hc' : SContains p N.seen x now = true := by simpa using hc
      have h2 := SExpire_keep p N.seen x now hc'
      rw [← Sweep_member hhub hI] at h2
      rw [hx] at h2; cases h2
    · intro _ A hJ; exact (Sweep_J (p := p) (now := now) A hJ).1
    · intro _ A hJ x hx; exact (Sweep_J (p := p) (now := now) A hJ).2 x hx
  · rw [if_neg hs]
    refine Post_quiet hSw rfl rfl rfl rfl (by simp [Plain]) ?_
    intro _ A hJ
    have := Sweep_J (p := p) (now := now) A hJ
    exact ⟨fun x hx => List.mem_append_left _ (this.1 x hx), fun x hx => List.mem_append_left _ (this.2 x hx)⟩

end Vinc.BroadcastNode
