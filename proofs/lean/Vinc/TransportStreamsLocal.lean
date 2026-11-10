import Vinc.TransportStreamsGrant

/-!
# Opening a local stream is charged to the credit ledger (POOL_GRANT, local streams)

Unbounded theorems about `Vinc.TransportStreams.openLocal`, which is `Streams::open_stream` for a bidirectional
stream. Its receive window is the one the connection advertised, so it cannot be made smaller: the stream opens only
when `windowsFit` says the window, in whole chunks, fits beside the credit already granted, the same test a peer
stream meets in `admits`.

* `poolDemand_fresh`: a fresh receive half (read position 0, nothing held, no final size) with credit up to `l`
  claims at most `l` rounded up to whole chunks, which is what `windowsFit` counts for it.
* `openLocal_ledger`: if the credit granted, with the windows kept for the credit given to the peer, fits in the pool
  before, it fits after a local stream opens (or is refused). Together with `grantOne_ledger` and the peer admission,
  no way of granting credit, local streams included, takes the credit beyond the pool bytes left. A free slot is a
  new slot (`FreeIsNew`, checked by TLC).
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
      r.read = 0 ∧ r.held = [] ∧ r.fin = none := by
  refine ⟨{ Slot.new with id := some id, open_ := !isUni id || !isLocal id,
                          limit := if (!isUni id || !isLocal id) = true then p.sw else 0,
                          size := if (!isUni id || !isLocal id) = true then p.sw else 0,
                          sdone := !(!isUni id || isLocal id) }, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · simp only [allocSlot, hf, setSlot]
    split <;> rfl

/-- Opening a local stream keeps the credit granted within the pool bytes left. -/
theorem openLocal_ledger (p : P) (T : Tab) (hch : 0 < p.ch)
    (hfree : ∀ i, firstFree T = some i → T.slots.getD i Slot.new = Slot.new)
    (h : gu p T + resv p T ≤ avail p T) :
    gu p (openLocal p T) + resv p (openLocal p T) ≤ avail p (openLocal p T) := by
  unfold openLocal
  by_cases hg : (decide (T.lo.1 + T.lo.2 ≥ T.adlim) || (firstFree T).isNone || decide (freeSlots T ≤ creditLeft T)
      || !windowsFit p T (creditLeft T + 1)) = true
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
      obtain ⟨r, hsl, hext, hrn, hadv, ho, hlim, hread, hheld, hfin⟩ := allocSlot_tab p T (T.lo.1 * 4 + 1) i hf
      simp [hid1, hid2] at ho hlim
      have hsu := sum_map_set (fun s => s.unreceived p) T.slots i r hlt
      have hsh := sum_map_set (fun s => s.held.length) T.slots i r hlt
      rw [hfi] at hsu hsh
      have hu0 : Slot.unreceived p Slot.new = 0 := by simp [Slot.unreceived, poolDemand, Slot.new]
      have hur : r.unreceived p ≤ p.winC := by
        have := poolDemand_fresh p r p.sw hch ho hread hheld hfin
        unfold Slot.unreceived P.winC
        rw [hlim]
        exact this
      simp only [hu0, hheld, List.length_nil] at hsu hsh
      have hh0 : (Slot.new).held.length = 0 := rfl
      simp only [hh0] at hsh
      simp only [gu, avail, availC, used, heldTotal, resv, creditLeft, admitted] at hfit h ⊢
      simp only [hsl, hext, hrn, hadv]
      have hSH : (List.map (fun s => s.held.length) (T.slots.set i r)).sum
          = (List.map (fun s => s.held.length) T.slots).sum := by omega
      rw [hSH]
      omega

end Vinc.TransportStreams
