import Pinc.TransportStreamsLocal

/-!
# Admission inside the stream credit: the index jump (STREAM_CAP, POOL_GRANT)

Unbounded theorems about `Pinc.TransportStreams.locate` for a peer stream inside the credit the table advertised,
which is `Streams::locate` with `Streams::admits`. A frame for a stream index above the next expected one opens every
skipped lower index at once; a stream's window is charged to the ledger from its first byte, so the skipped streams,
which have carried nothing, cost only the first charges the credit already kept for them.

* `admits_inside_credit`: inside the credit an admission needs only the live-stream cap and free slots, never pool
  room: however full the ledger or the pool, it is not refused for them.
* `allocSlot_peer`, `foldl_alloc_peer`: opening any run of peer streams adds at most one first charge per stream to
  the ledger, takes no pool chunk, and leaves every free slot new.
* `locate_inside_credit`: the jump inside the credit is admitted and adds nothing to the ledger. With
  `grantOne_ledger` and `openLocal_ledger`, the stream limit the receiver advertised is admitted at no cost, whatever
  lower indices a frame skips.

A free slot is a new slot (`FreeIsNew`, checked by TLC), here the hypothesis `FreeNew`.
-/

namespace Pinc.TransportStreams

/-- Every free slot is a new one. -/
def FreeNew (T : Tab) : Prop := ∀ j, (T.slots.getD j Slot.new).id = none → T.slots.getD j Slot.new = Slot.new

/-- Inside the credit, an admission is refused only for the cap or the slots, never for the pool. -/
theorem admits_inside_credit (p : P) (T : Tab) (c next count : Nat) (hcap : T.rl + count ≤ p.maxrem)
    (hfree : count ≤ freeSlots T) (hin : admitted T + count ≤ T.adv) : admits p T c next count = true := by
  unfold freeSlots at hfree
  simpa [admits, hcap, hin] using hfree

/-- A raise of the stream credit keeps to the configured limit: the streams the peer may still open plus those live
stay at most `maxrem` (`CreditInLimit` in `Streams.tla`). -/
theorem refreshAdmit_within_limit (p : P) (T : Tab) (h : T.adv ≤ admitted T + (p.maxrem - T.rl)) :
    (refreshAdmit p T).adv ≤ admitted T + (p.maxrem - T.rl) := by
  have h1 : admitRoom p T ≤ p.capLive - T.rl := Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_left _ _)
  have h2 : p.capLive ≤ p.maxrem := Nat.min_le_left _ _
  unfold refreshAdmit
  dsimp only
  split
  · dsimp only
    omega
  · exact h

/-- Opening one peer stream: the ledger grows by at most one first charge, no chunk is taken, the counters the ledger
reads stay, and every free slot stays new. -/
theorem allocSlot_peer (p : P) (T : Tab) (id : Nat) (hch : 0 < p.ch) (hpeer : isLocal id = false)
    (hnew : FreeNew T) :
    gu p (allocSlot p T id) ≤ gu p T + p.firstW ∧ heldTotal (allocSlot p T id) = heldTotal T ∧
      (allocSlot p T id).ext = T.ext ∧ (allocSlot p T id).rn = T.rn ∧ (allocSlot p T id).adv = T.adv ∧
      FreeNew (allocSlot p T id) := by
  cases hf : firstFree T with
  | none =>
    have he : allocSlot p T id = T := by simp [allocSlot, hf]
    rw [he]
    exact ⟨Nat.le_add_right _ _, rfl, rfl, rfl, rfl, hnew⟩
  | some i =>
    obtain ⟨hlt, hpi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    have hgi : T.slots.getD i Slot.new = T.slots[i] := by
      simp [List.getD_eq_getElem?_getD, hlt]
    have hidn : (T.slots.getD i Slot.new).id = none := by
      rw [hgi]
      simpa using hpi
    have hfi := hnew i hidn
    obtain ⟨r, hsl, hext, hrn, hadv, ho, hlim, hread, hheld, hfin, hhi, hrid, hch0⟩ := allocSlot_tab p T id i hf
    simp [hpeer] at ho hlim
    have hur := fresh_unreceived_le p r hch ho hlim hread hheld hfin hhi
    have hsu := sum_map_set (fun s => s.unreceived p) T.slots i r hlt
    have hsh := sum_map_set (fun s => s.chunks) T.slots i r hlt
    rw [hfi] at hsu hsh
    have hu0 : Slot.unreceived p Slot.new = 0 := by simp [Slot.unreceived, Slot.demandTo, poolDemand, Slot.new]
    have hh0 : (Slot.new).chunks = 0 := rfl
    simp only [hu0, hh0, hheld, hch0, List.length_nil] at hsu hsh
    refine ⟨?_, ?_, hext, hrn, hadv, ?_⟩
    · simp only [gu, hsl]
      omega
    · simp only [heldTotal, hsl]
      omega
    · intro j hj
      rw [hsl] at hj ⊢
      by_cases hji : j = i
      · subst hji
        rw [getD_set_self _ _ _ _ hlt] at hj
        rw [hrid] at hj
        exact absurd hj (by simp)
      · rw [getD_set_ne _ _ _ _ _ hji] at hj ⊢
        exact hnew j hj

/-- Opening a run of peer streams, as `locate` does for a frame that skips lower indices: the ledger grows by at most
one first charge per stream, and nothing else it reads changes. -/
theorem foldl_alloc_peer (p : P) (hch : 0 < p.ch) (f : Nat → Nat) (hpeer : ∀ k, isLocal (f k) = false)
    (ks : List Nat) : ∀ T : Tab, FreeNew T →
      gu p (ks.foldl (fun T k => allocSlot p T (f k)) T) ≤ gu p T + ks.length * p.firstW ∧
      heldTotal (ks.foldl (fun T k => allocSlot p T (f k)) T) = heldTotal T ∧
      (ks.foldl (fun T k => allocSlot p T (f k)) T).ext = T.ext ∧
      (ks.foldl (fun T k => allocSlot p T (f k)) T).rn = T.rn ∧
      (ks.foldl (fun T k => allocSlot p T (f k)) T).adv = T.adv ∧
      FreeNew (ks.foldl (fun T k => allocSlot p T (f k)) T) := by
  induction ks with
  | nil =>
    intro T hn
    exact ⟨by simp, rfl, rfl, rfl, rfl, hn⟩
  | cons k ks ih =>
    intro T hn
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := allocSlot_peer p T (f k) hch (hpeer k) hn
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := ih (allocSlot p T (f k)) h6
    simp only [List.foldl_cons, List.length_cons]
    refine ⟨?_, g2.trans h2, g3.trans h3, g4.trans h4, g5.trans h5, g6⟩
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- The index jump inside the credit: a frame for a peer stream index at or above the next expected one, inside the
credit the table advertised and under its cap, is admitted with every skipped lower index, adds nothing to the
ledger (the first charges of the streams it opens were kept for the credit) and takes no pool chunk. -/
theorem locate_inside_credit (p : P) (T : Tab) (id : Nat) (hch : 0 < p.ch) (hn : FreeNew T)
    (hl : isLocal id = false) (h2 : ¬ idx id < cget T.rn (cls id))
    (h4 : ¬ idx id ≥ cget T.rn (cls id) + p.maxrem)
    (hcap : T.rl + (idx id - cget T.rn (cls id) + 1) ≤ p.maxrem)
    (hfree : idx id - cget T.rn (cls id) + 1 ≤ freeSlots T)
    (hin : admitted T + (idx id - cget T.rn (cls id) + 1) ≤ T.adv) :
    (locate p T id).2.2 = "ok" ∧
      gu p (locate p T id).1 + resv p (locate p T id).1 ≤ gu p T + resv p T ∧
      avail p (locate p T id).1 = avail p T := by
  have h5 := admits_inside_credit p T (cls id) (cget T.rn (cls id)) _ hcap hfree hin
  have hl' : ¬ isLocal id = true := by simp [hl]
  have hn5 : ¬ (!admits p T (cls id) (cget T.rn (cls id)) (idx id - cget T.rn (cls id) + 1)) = true := by
    simp [h5]
  have hpeer : ∀ k, isLocal ((cget T.rn (cls id) + k) * 4 + id % 4) = false := by
    intro k
    simp only [isLocal, beq_eq_false_iff_ne, ne_eq] at hl ⊢
    omega
  obtain ⟨g1, g2, g3, g4, g5, -⟩ := foldl_alloc_peer p hch (fun k => (cget T.rn (cls id) + k) * 4 + id % 4) hpeer
    (List.range (idx id - cget T.rn (cls id) + 1)) T hn
  simp only [List.length_range] at g1
  have hloc : locate p T id =
      ({ (List.range (idx id - cget T.rn (cls id) + 1)).foldl
            (fun S k => allocSlot p S ((cget T.rn (cls id) + k) * 4 + id % 4)) T with
          rn := cset ((List.range (idx id - cget T.rn (cls id) + 1)).foldl
            (fun S k => allocSlot p S ((cget T.rn (cls id) + k) * 4 + id % 4)) T).rn (cls id) (idx id + 1) },
        findSlot { (List.range (idx id - cget T.rn (cls id) + 1)).foldl
            (fun S k => allocSlot p S ((cget T.rn (cls id) + k) * 4 + id % 4)) T with
          rn := cset ((List.range (idx id - cget T.rn (cls id) + 1)).foldl
            (fun S k => allocSlot p S ((cget T.rn (cls id) + k) * 4 + id % 4)) T).rn (cls id) (idx id + 1) } id,
        "ok") := by
    simp only [locate, hl', h2, h4, hn5, Bool.false_eq_true, ↓reduceIte]
  rw [hloc]
  generalize (List.range (idx id - cget T.rn (cls id) + 1)).foldl
      (fun S k => allocSlot p S ((cget T.rn (cls id) + k) * 4 + id % 4)) T = T2 at g1 g2 g3 g4 g5 ⊢
  refine ⟨rfl, ?_, ?_⟩
  · show gu p { T2 with rn := cset T2.rn (cls id) (idx id + 1) }
        + resv p { T2 with rn := cset T2.rn (cls id) (idx id + 1) } ≤ gu p T + resv p T
    -- the new streams' first charges come out of the credit kept for them
    have hadm : admitted { T2 with rn := cset T2.rn (cls id) (idx id + 1) }
        = admitted T + (idx id - cget T.rn (cls id) + 1) := by
      simp only [admitted, g4]
      unfold cget cset at *
      by_cases hk : cls id = 0 <;> simp [hk] at h2 ⊢ <;> omega
    have hres : resv p { T2 with rn := cset T2.rn (cls id) (idx id + 1) }
        = (T.adv - (admitted T + (idx id - cget T.rn (cls id) + 1))) * p.firstW := by
      simp only [resv, creditLeft]
      rw [hadm]
      simp only [g5]
    have hgu : gu p { T2 with rn := cset T2.rn (cls id) (idx id + 1) } = gu p T2 := rfl
    have hsplit : resv p T = (T.adv - (admitted T + (idx id - cget T.rn (cls id) + 1))) * p.firstW
        + (idx id - cget T.rn (cls id) + 1) * p.firstW := by
      simp only [resv, creditLeft]
      rw [← Nat.add_mul]
      congr 1
      omega
    rw [hres, hgu, hsplit]
    omega
  · show (p.b - (heldTotal T2 + T2.ext)) * p.ch = (p.b - (heldTotal T + T.ext)) * p.ch
    rw [g2, g3]
