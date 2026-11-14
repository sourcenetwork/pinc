import Vinc.Axioms
import Vinc.TransportStreamsGrant

/-!
# Opening a local stream is charged to the credit ledger (POOL_GRANT, local streams)

Unbounded theorems about `Vinc.TransportStreams.openLocal`, which is `Streams::open_stream` for a bidirectional
stream. Its receive window is the one the connection advertised, so it cannot be made smaller: the stream opens only
when `windowsFit` says its first charge fits beside the credit already granted, the same test a peer stream beyond
the credit meets in `admits`; the whole window is counted from the stream's first byte.

* `poolDemand_fresh`, `fresh_unreceived_le`: a fresh receive half (read position 0, nothing held, no final size)
  with credit up to `l` claims at most `l` rounded up to whole chunks; having carried no data, it counts at most its
  first charge, which is what `windowsFit` counts for it.
* `openLocal_ledger`: if the credit granted, with the windows kept for the credit given to the peer, fits in the pool
  before, it fits after a local stream opens (or is refused). Together with `grantOne_ledger` and the peer admission,
  no way of granting credit, local streams included, takes the credit beyond the pool bytes left. A free slot is a
  new slot (`FreeIsNew`, checked by TLC). Early opens change nothing here: the pool test is the same.
* Early opens (an optimistic dial, `Streams::set_early`): an open passes the limit on what we may open only while
  opens are early (`openLocal_past_early`); a stream frame leaves only for a stream whose ordinal the limit covers,
  any other `sendOut` changes nothing (`sendOut_gated`); and a raise of the limit never takes that back
  (`canSend_raise`), so the streams let go are the first ones opened, in order, and stay let go.
-/

namespace Vinc.TransportStreams

theorem poolDemand_fresh (p : P) (r : Slot) (l : Nat) (hch : 0 < p.ch) (hopen : r.open_ = true)
    (hread : r.read = 0) (hheld : r.held = []) (hfin : r.fin = none) :
    poolDemand p r l ≤ (l + p.ch - 1) / p.ch * p.ch := by
  by_cases hl : l = 0
  · subst hl
    simp [poolDemand, Slot.reach, hfin, hread]
  · have hdiv : (l + p.ch - 1) / p.ch = (l - 1) / p.ch + 1 := by
      have : l + p.ch - 1 = (l - 1) + p.ch := by omega
      rw [this, Nat.add_div_right _ hch]
    have hr : r.reach l = l := by simp [Slot.reach, hfin]
    rw [hdiv]
    simp [poolDemand, hr, hread, hheld, hopen, hl]

/-- The slot `allocSlot` writes into the first free one: what it holds, and that nothing else of the table changes
that the ledger sees. -/
theorem allocSlot_tab (p : P) (T : Tab) (id i : Nat) (hf : firstFree T = some i) :
    ∃ r : Slot, (allocSlot p T id).slots = T.slots.set i r ∧ (allocSlot p T id).ext = T.ext ∧
      (allocSlot p T id).rn = T.rn ∧ (allocSlot p T id).adv = T.adv ∧
      r.open_ = (!isUni id || !isLocal id) ∧ r.limit = (if (!isUni id || !isLocal id) = true then p.sw else 0) ∧
      r.read = 0 ∧ r.held = [] ∧ r.fin = none ∧ r.hi = 0 ∧ r.id = some id := by
  refine ⟨{ Slot.new with id := some id, open_ := !isUni id || !isLocal id,
                          limit := if (!isUni id || !isLocal id) = true then p.sw else 0,
                          size := if (!isUni id || !isLocal id) = true then p.sw else 0,
                          sdone := !(!isUni id || isLocal id), cnt := true,
                          ord := if isLocal id then T.lo.1 + T.lo.2 + 1 else 0 },
    ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · simp only [allocSlot, hf, setSlot]
    split <;> rfl

/-- A receiving slot `allocSlot` opens counts at most its first charge in the ledger: it has carried no data, so the
ledger counts the first `firstk` chunks of its window, or the window if smaller. -/
theorem fresh_unreceived_le (p : P) (r : Slot) (hch : 0 < p.ch) (ho : r.open_ = true) (hlim : r.limit = p.sw)
    (hread : r.read = 0) (hheld : r.held = []) (hfin : r.fin = none) (hhi : r.hi = 0) :
    r.unreceived p ≤ p.firstW := by
  have hd := poolDemand_fresh p r (min p.sw (p.firstk * p.ch)) hch ho hread hheld hfin
  have hm : r.chargeTo p r.limit = min p.sw (p.firstk * p.ch) := by
    simp [Slot.chargeTo, hhi, hlim]
  have hu : r.unreceived p = poolDemand p r (min p.sw (p.firstk * p.ch)) := by
    unfold Slot.unreceived Slot.demandTo
    rw [hm]
  rw [hu]
  refine Nat.le_trans hd ?_
  unfold P.firstW P.winC
  refine Nat.le_min.mpr ⟨?_, ?_⟩
  · exact Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))
  · have h1 : (min p.sw (p.firstk * p.ch) + p.ch - 1) / p.ch < p.firstk + 1 := by
      apply (Nat.div_lt_iff_lt_mul hch).2
      rw [Nat.add_mul, Nat.one_mul]
      have := Nat.min_le_right p.sw (p.firstk * p.ch)
      omega
    exact Nat.mul_le_mul_right _ (by omega)

/-- Opening a local stream keeps the credit granted within the pool bytes left. -/
theorem openLocal_ledger (p : P) (T : Tab) (hch : 0 < p.ch)
    (hfree : ∀ i, firstFree T = some i → T.slots.getD i Slot.new = Slot.new)
    (h : gu p T + resv p T ≤ avail p T) :
    gu p (openLocal p T) + resv p (openLocal p T) ≤ avail p (openLocal p T) := by
  unfold openLocal
  by_cases hg : ((!T.early && decide (T.lo.1 + T.lo.2 ≥ T.adlim)) || (firstFree T).isNone
      || decide (freeSlots T ≤ creditLeft T) || !windowsFit p T (creditLeft T + 1)) = true
  · rw [if_pos hg]; exact h
  · rw [if_neg hg]
    cases hf : firstFree T with
    | none => simp [hf] at hg
    | some i =>
      have hw : windowsFit p T (creditLeft T + 1) = true := by
        by_cases hw : windowsFit p T (creditLeft T + 1) = true
        · exact hw
        · exfalso
          apply hg
          have hw' : windowsFit p T (creditLeft T + 1) = false := by simpa using hw
          simp [hw']
      have hfit := hw
      unfold windowsFit at hfit
      simp only [decide_eq_true_eq] at hfit
      rw [Nat.add_mul, Nat.one_mul] at hfit
      have hfi := hfree i hf
      obtain ⟨hlt, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      have hid1 : isUni (T.lo.1 * 4 + 1) = false := by
        have : (T.lo.1 * 4 + 1) / 2 % 2 = 0 := by omega
        simp [isUni, this]
      have hid2 : isLocal (T.lo.1 * 4 + 1) = true := by
        have : (T.lo.1 * 4 + 1) % 2 = 1 := by omega
        simp [isLocal, this]
      obtain ⟨r, hsl, hext, hrn, hadv, ho, hlim, hread, hheld, hfin, hhi, -⟩ := allocSlot_tab p T (T.lo.1 * 4 + 1) i hf
      simp [hid1, hid2] at ho hlim
      have hsu := sum_map_set (fun s => s.unreceived p) T.slots i r hlt
      have hsh := sum_map_set (fun s => s.held.length) T.slots i r hlt
      rw [hfi] at hsu hsh
      have hu0 : Slot.unreceived p Slot.new = 0 := by simp [Slot.unreceived, Slot.demandTo, poolDemand, Slot.new]
      have hur := fresh_unreceived_le p r hch ho hlim hread hheld hfin hhi
      simp only [hu0, hheld, List.length_nil] at hsu hsh
      have hh0 : (Slot.new).held.length = 0 := rfl
      simp only [hh0] at hsh
      simp only [gu, avail, availC, used, heldTotal, resv, creditLeft, admitted] at hfit h ⊢
      simp only [hsl, hext, hrn, hadv]
      have hSH : (List.map (fun s => s.held.length) (T.slots.set i r)).sum
          = (List.map (fun s => s.held.length) T.slots).sum := by omega
      rw [hSH]
      omega

/-- An open passes the limit on what we may open only while opens are early: a stream opened when early opens are
off finds the limit above the streams opened before it. -/
theorem openLocal_past_early (p : P) (T : Tab)
    (hopen : T.lo.1 + T.lo.2 < (openLocal p T).lo.1 + (openLocal p T).lo.2)
    (hpast : T.adlim < (openLocal p T).lo.1 + (openLocal p T).lo.2) : T.early = true := by
  unfold openLocal at hopen hpast
  by_cases hg : ((!T.early && decide (T.lo.1 + T.lo.2 ≥ T.adlim)) || (firstFree T).isNone
      || decide (freeSlots T ≤ creditLeft T) || !windowsFit p T (creditLeft T + 1)) = true
  · rw [if_pos hg] at hopen
    exact absurd hopen (Nat.lt_irrefl _)
  · rw [if_neg hg] at hpast
    simp only at hpast
    cases he : T.early with
    | true => rfl
    | false =>
      exfalso; apply hg
      have : T.adlim ≤ T.lo.1 + T.lo.2 := by omega
      simp [he, this]

/-- A stream whose ordinal the limit does not cover sends nothing: `sendOut` leaves the table as it was. -/
theorem sendOut_gated (T : Tab) (i : Nat) (f : Bool) (h : canSend T i = false) : sendOut T i f = T := by
  unfold sendOut
  simp [h]

/-- A raise of the limit never takes back a stream's leave to send. -/
theorem canSend_raise (T : Tab) (i l : Nat) (h : canSend T i = true) : canSend (recvMaxStreams T l) i = true := by
  unfold canSend at h ⊢
  unfold recvMaxStreams
  exact decide_eq_true (Nat.le_trans (of_decide_eq_true h) (Nat.le_max_left _ _))

#audit_axioms Vinc.TransportStreams.openLocal_past_early
#audit_axioms Vinc.TransportStreams.sendOut_gated
#audit_axioms Vinc.TransportStreams.canSend_raise

end Vinc.TransportStreams
