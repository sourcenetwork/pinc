import Pinc.BroadcastNodeLemmas3

/-!
# Broadcast node: what one operator guarantees

`Post p N now r` collects what the system invariants need of the result `r` of an operator run on `N` at `now`:
the node invariant, the allowed-delivery and deny facts of the records, the floors, the epoch count, the distinct
deliveries, the accounting of the ids the set holds and the gathering phase. This file proves it for
`FloorsSettled` and `AcpAnswer`; `BroadcastNodeLemmas5` for `OnMsg` and `OnTimer`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Pinc.BroadcastNode

/-- A record that is neither a delivery nor an answer. -/
def NoDA : TraceRec → Prop
  | .delivered .. => False
  | .acpAnswered .. => False
  | _ => True

/-- A record that is not a delivery. -/
def NoDel : TraceRec → Prop
  | .delivered .. => False
  | _ => True

/-- Every delivery is allowed: a cache delivery by an unexpired allow entry, an answer delivery by an allow answer
for the origin in the same records. -/
def DelOK (acp : List (Nat × AcpE)) (now : Nat) (outs : List TraceRec) : Prop :=
  ∀ mid org ts via, TraceRec.delivered mid org ts via ∈ outs →
    (via = .cache → ∃ e, acp.lookup org = some e ∧ e.allow = true ∧ now ≤ e.exp) ∧
    (via = .answer → ∃ id, TraceRec.acpAnswered id true org ∈ outs)

/-- After a deny nothing is held for the origin and nothing is delivered for it. -/
def DenyOK (held : List Ent) (outs : List TraceRec) : Prop :=
  ∀ id org, TraceRec.acpAnswered id false org ∈ outs →
    (∀ e ∈ held, e.origin ≠ org) ∧ (∀ mid ts via, TraceRec.delivered mid org ts via ∉ outs)

/-- Every id the dedupe set holds, and every logged id, is among the accounted ids `A`. -/
def JInv (A : List Nat) (N : Node) : Prop :=
  (∀ x, N.seen.map x ≠ none → x ∈ A) ∧ (∀ x ∈ LIds N.lg, x ∈ A)

/-- What the system invariants need of one operator result. -/
structure Post (p : Params) (N : Node) (now : Nat) (r : Res) : Prop where
  inv : NodeInv p r.n
  del : DelOK r.n.acp now r.outs
  deny : DenyOK r.n.held r.outs
  resp : FreshDel p r.n r.outs
  delta : ∀ x, r.dl.count x + hc r.n x ≤ hc N x + (if NewRec p now N r.n x then 1 else 0)
  nodup : p.heldDedup = true → r.dl.Nodup
  acc : p.heldFullKeepsUnseen = true → ∀ A, JInv A N → JInv (A ++ r.acc) r.n
  floor : p.isHub = false → r.n.phase = .gathering → ∀ o ∈ r.outs, NoDel o
  phase : r.n.phase = .gathering → N.phase = .gathering ∧ r.n.born = N.born

theorem NewRec_of (p : Params) (now : Nat) (N N' : Node) (x : Nat) (h0 : SContains p N.seen x now = false)
    (h1 : SContains p N'.seen x now = true) : NewRec p now N N' x = true := by
  rw [SContains_iff] at h1
  obtain ⟨t, ht, hle⟩ := h1
  have h0' : ¬ ∃ t0, N.seen.map x = some t0 ∧ now - t0 ≤ p.ttl := by
    rw [← SContains_iff]; simpa using h0
  unfold NewRec; rw [ht]
  cases ho : N.seen.map x with
  | none => simp
  | some t0 =>
    have h2 : ¬ now - t0 ≤ p.ttl := fun h => h0' ⟨t0, ho, h⟩
    have h3 : t ≠ t0 := fun e => h2 (e ▸ hle)
    simp [h3]; omega

theorem delta_conv {p : Params} {now : Nat} {N N0 N' : Node} {x : Nat} {ms : List Nat}
    (hs : ∀ x ∈ ms, SContains p N0.seen x now = false → SContains p N.seen x now = false) :
    (if x ∈ ms ∧ SContains p N0.seen x now = false ∧ SContains p N'.seen x now = true then 1 else 0) ≤
      (if NewRec p now N N' x then 1 else 0) := by
  by_cases c : x ∈ ms ∧ SContains p N0.seen x now = false ∧ SContains p N'.seen x now = true
  · simp only [c, and_self, ite_true, NewRec_of p now N N' x (hs x c.1 c.2.1) c.2.2]; exact Nat.le_refl _
  · simp only [c, ite_false]; exact Nat.zero_le _

theorem chain_outs {p : Params} {now : Nat} {ms : List Nat} {r0 r : Res} (T : TransSpec p now ms r0 r)
    (hq : ∀ o ∈ r0.outs, NoDA o) :
    DelOK r.n.acp now r.outs ∧ (∀ id a org, TraceRec.acpAnswered id a org ∉ r.outs) ∧ FreshDel p r.n r.outs := by
  obtain ⟨ex, hout, oR, cG, fD⟩ := T.outs
  have hac := T.core.acp
  rw [hout]
  refine ⟨?_, ?_, ?_⟩
  · intro mid org ts via h
    rcases List.mem_append.1 h with h | h
    · exact absurd (hq _ h) (by simp [NoDA])
    · have := oR _ h
      simp only [OfferRec] at this
      subst this
      refine ⟨fun _ => ?_, fun e => by cases e⟩
      rw [hac]; exact cG mid org ts h
  · intro id a org h
    rcases List.mem_append.1 h with h | h
    · exact (hq _ h)
    · exact oR _ h
  · intro mid org ts via h
    rcases List.mem_append.1 h with h | h
    · exact absurd (hq _ h) (by simp [NoDA])
    · rw [T.core.isOld]; exact fD mid org ts via h

theorem count_filter_split (f : Ent → Bool) (x : Nat) (l : List Ent) :
    ((l.filter f).map (·.mid)).count x + ((l.filter (fun e => !f e)).map (·.mid)).count x = (l.map (·.mid)).count x := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : f a <;> simp [h, List.count_cons] <;> omega

/-- The floors are settled (or the wait ran out) on a gathering node: what is offered afterwards. -/
theorem FloorsSettled_post {p : Params} {N : Node} {now : Nat} (hcap : 0 < p.seenCap) (hI : NodeInv p N)
    (hg : N.phase = .gathering) (used : Bool) (rf : Option Nat) (of_ : Option (Nat → Option Nat)) (nh : Bool) :
    Post p N now (FloorsSettled p N now used rf of_ nh) := by
  have hhub : p.isHub = false := by
    cases h : p.isHub
    · rfl
    · have := hI.hubPhase h; rw [hg] at this; cases this
  have hheld : N.held = [] := hI.gatherHeld hhub hg
  have hI1 : NodeInv p {N with phase := .done, rfloor := rf, ofloor := of_, nohist := nh, fhold := []} :=
    ⟨hI.seen, hI.heldLen, (by simp), hI.checksLen, hI.lgLen, hI.acpLen, hI.heldNodup, (by simp), hI.checksNodup,
     (fun h => absurd h (by simp [hhub])), hI.memberLg, (fun _ h => by cases h),
     (fun e he => by simp [hheld] at he)⟩
  unfold FloorsSettled
  have T := offerAllTrans p now N.fhold (Plain {N with phase := .done, rfloor := rf, ofloor := of_, nohist := nh, fhold := []} [.floorDone used])
  generalize OfferAll p now (Plain {N with phase := .done, rfloor := rf, ofloor := of_, nohist := nh, fhold := []} [.floorDone used]) N.fhold = r at T ⊢
  have co := chain_outs T (by simp [Plain, NoDA])
  have hph : r.n.phase = .done := T.core.phase
  obtain ⟨dx, hdl, hsub⟩ := T.dl
  refine ⟨T.inv hcap hI1, co.1, ?_, co.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro id org h; exact absurd h (co.2.1 id false org)
  · intro x
    have d := T.delta x
    have cv := delta_conv (p := p) (now := now) (N := N) (N0 := (Plain {N with phase := .done, rfloor := rf, ofloor := of_, nohist := nh, fhold := []} [.floorDone used]).n) (N' := r.n) (x := x) (ms := N.fhold.map (·.mid)) (fun _ _ h => h)
    have hh : hc {N with phase := .done, rfloor := rf, ofloor := of_, nohist := nh, fhold := []} x = hc N x := rfl
    simp only [Plain, List.count_nil] at d
    simp only [Plain] at cv
    omega
  · intro _; rw [hdl]; simp only [Plain, List.nil_append]; exact (hI.fholdNodup).sublist hsub
  · intro hk A hJ
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rcases T.accN hk x hx with h | h
      · exact List.mem_append_left _ (hJ.1 x h)
      · exact List.mem_append_right _ h
    · rw [T.lg] at hx; exact List.mem_append_left _ (hJ.2 x hx)
  · intro _ h; rw [hph] at h; cases h
  · intro h; rw [hph] at h; cases h

end Pinc.BroadcastNode
