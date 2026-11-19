import Pinc.ReconcileRefEv

/-!
# Reconcile refinement, part 2j: the handlers of the merge

The responder's handler of a FULL part (bitmap of the initiator's items we hold, our extra items staged) and the
initiator's (our report arenas grow by the peer's and our own differing items), folded over the events of the merge.
-/

namespace Pinc.Reconcile

/-- The responder's handler of a FULL part. -/
def respFullF (m : Cmp) (st : List Nat × Out × Nat) : Except Err (List Nat × Out × Nat) :=
  match m with
  | .both k => .ok (setBit st.1 k, st.2.1, st.2.2)
  | .theirs _ => .ok st
  | .mine x => .ok (st.1, st.2.1.stageItem x, st.2.2 + 1)

theorem respFull_fold : ∀ (evs : List Cmp) (st : List Nat × Out × Nat),
    evFold respFullF st evs = .ok (((evs.filterMap Cmp.bothIdx).foldl setBit st.1),
      { st.2.1 with stage := st.2.1.stage ++ stageBytes (evs.filterMap Cmp.mineItem) },
      st.2.2 + (evs.filterMap Cmp.mineItem).length)
  | [], st => by simp [evFold_nil, stageBytes]
  | e :: evs, st => by
    cases e with
    | both k =>
      simp only [evFold_cons, respFullF, bind, Except.bind]
      rw [respFull_fold evs]; simp [Cmp.bothIdx, Cmp.mineItem, List.filterMap_cons]
    | theirs x =>
      simp only [evFold_cons, respFullF, bind, Except.bind]
      rw [respFull_fold evs]; simp [Cmp.theirsItem, Cmp.mineItem, Cmp.bothIdx, List.filterMap_cons]
    | mine x =>
      simp only [evFold_cons, respFullF, bind, Except.bind]
      rw [respFull_fold evs]
      simp [Cmp.mineItem, Cmp.bothIdx, List.filterMap_cons, Out.stageItem, stageBytes_cons, List.append_assoc]
      omega

/-- The initiator's handler of a FULL or COLD part: the peer's items to `here`, ours to `there`. -/
def initFullF (cap : Nat) (m : Cmp) (st : List Item × List Item) : Except Err (List Item × List Item) :=
  match m with
  | .both _ => .ok st
  | .theirs x => do pure (← pushItem st.1 (dataLen st.2) cap x, st.2)
  | .mine x => do pure (st.1, ← pushItem st.2 (dataLen st.1) cap x)

theorem dataLen_nil : dataLen [] = 0 := by simp [dataLen]

theorem dataLen_cons (x : Item) (l : List Item) : dataLen (x :: l) = (venc x.length).length + x.length + dataLen l := by
  simp [dataLen]

theorem dataLen_append (a b : List Item) : dataLen (a ++ b) = dataLen a + dataLen b := by
  simp [dataLen, List.map_append, List.sum_append]

theorem venc_len_pos (n : Nat) : 1 ≤ (venc n).length := by rw [venc_length]; exact Varint.encodedLen_pos _

theorem initFull_fold (cap : Nat) : ∀ (evs : List Cmp) (st : List Item × List Item),
    dataLen st.1 + dataLen st.2 + dataLen (evs.filterMap Cmp.theirsItem) + dataLen (evs.filterMap Cmp.mineItem)
      + varMax ≤ cap →
    evFold (initFullF cap) st evs =
      .ok (st.1 ++ evs.filterMap Cmp.theirsItem, st.2 ++ evs.filterMap Cmp.mineItem)
  | [], st, _ => by simp [evFold_nil]
  | e :: evs, st, h => by
    cases e with
    | both k =>
      simp only [evFold_cons, initFullF, bind, Except.bind]
      rw [initFull_fold cap evs st (by simpa [Cmp.theirsItem, Cmp.mineItem, List.filterMap_cons] using h)]
      simp [Cmp.theirsItem, Cmp.mineItem, List.filterMap_cons]
    | theirs x =>
      simp only [Cmp.theirsItem, Cmp.mineItem, List.filterMap_cons, dataLen_cons] at h
      have hp := venc_len_pos x.length
      have hok : ¬ (dataLen st.1 + dataLen st.2 + x.length + varMax > cap) := by omega
      simp only [evFold_cons, initFullF, bind, Except.bind, pushItem, hok, ite_false, pure, Except.pure]
      have h' : dataLen (st.1 ++ [x]) + dataLen st.2 + dataLen (evs.filterMap Cmp.theirsItem)
          + dataLen (evs.filterMap Cmp.mineItem) + varMax ≤ cap := by
        simp only [dataLen_append, dataLen_cons, dataLen_nil]; omega
      rw [initFull_fold cap evs (st.1 ++ [x], st.2) h']
      simp [Cmp.theirsItem, Cmp.mineItem, List.filterMap_cons, List.append_assoc]
    | mine x =>
      simp only [Cmp.theirsItem, Cmp.mineItem, List.filterMap_cons, dataLen_cons] at h
      have hp := venc_len_pos x.length
      have hok : ¬ (dataLen st.2 + dataLen st.1 + x.length + varMax > cap) := by omega
      simp only [evFold_cons, initFullF, bind, Except.bind, pushItem, hok, ite_false, pure, Except.pure]
      have h' : dataLen st.1 + dataLen (st.2 ++ [x]) + dataLen (evs.filterMap Cmp.theirsItem)
          + dataLen (evs.filterMap Cmp.mineItem) + varMax ≤ cap := by
        simp only [dataLen_append, dataLen_cons, dataLen_nil]; omega
      rw [initFull_fold cap evs (st.1, st.2 ++ [x]) h']
      simp [Cmp.theirsItem, Cmp.mineItem, List.filterMap_cons, List.append_assoc]

end Pinc.Reconcile
