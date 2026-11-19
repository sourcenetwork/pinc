import Pinc.HandshakeCases

/-!
# The ticket stores and the prekey cache, for unboundedly many sessions

Inductive invariants of the stores of the system of `HandshakeSys`, proved over every reachable state for any number
of nodes, sessions and tickets and any store capacities:

* the stored ids of every server store are pairwise distinct whatever the generator returns (`uniqueIds`): the
  fresh-id check of `issue_batch` discharges the assumption a generator would otherwise need;
* every occupied slot of a server store is a ticket that was issued (`ticketsIssued`);
* a prekey hash enters a cache only together with a finished responder session that used that prekey
  (`cacheAuthenticated`);
* a client store holds at most one ticket per peer (`clientOnePerPeer`), and only tickets some responder issued
  (`clientTicketsIssued`).
-/

namespace Pinc.Hs
open Term

/-- The occupied slots of a store have pairwise distinct ticket ids. -/
def UniqTids (sl : List Slot) : Prop :=
  ∀ (i j : Nat) (a b : Slot), sl[i]? = some a → sl[j]? = some b → a.occ = true → b.occ = true → a.tid = b.tid → i = j

theorem StoredIn_false {sl : List Slot} {t : Term} (h : StoredIn sl t = false) :
    ∀ s ∈ sl, s.occ = true → s.tid ≠ t := by
  intro s hs ho e
  simp only [StoredIn, List.any_eq_false] at h
  have := h s hs
  simp [ho, e] at this

theorem FreshFrom_some {sl : List Slot} {c : List Nat} {t : Term} (h : FreshFrom sl c = some t) :
    StoredIn sl t = false := by
  induction c with
  | nil => simp [FreshFrom] at h
  | cons x r ih =>
    simp only [FreshFrom] at h
    split at h
    · exact ih h
    · rename_i hn; simp at h; subst h; simpa using hn

theorem Put_get {sl : List Slot} {v : Option Nat} {x a : Slot} {j : Nat} (h : (Put sl v x)[j]? = some a) :
    (v = some j ∧ a = x) ∨ sl[j]? = some a := by
  cases v with
  | none => right; simpa [Put] using h
  | some i =>
    simp only [Put] at h
    rw [List.getElem?_set] at h
    split at h
    · rename_i hh; split at h
      · simp at h; left; exact ⟨by rw [hh], h.symm⟩
      · simp at h
    · right; exact h

theorem Put_mem {sl : List Slot} {v : Option Nat} {x a : Slot} (h : a ∈ Put sl v x) : a ∈ sl ∨ a = x := by
  cases v with
  | none => left; simpa [Put] using h
  | some i =>
    simp only [Put] at h
    rcases List.mem_or_eq_of_mem_set h with h | h
    · left; exact h
    · right; exact h

theorem Uniq_put {sl : List Slot} (hu : UniqTids sl) (v : Option Nat) (x : Slot) (hx : x.occ = true)
    (hf : StoredIn sl x.tid = false) : UniqTids (Put sl v x) := by
  intro i j a b ha hb hao hbo hab
  rcases Put_get ha with ⟨hi, rfl⟩ | ha'
  · rcases Put_get hb with ⟨hj, rfl⟩ | hb'
    · exact Option.some.inj (hi.symm.trans hj)
    · exact absurd hab.symm (StoredIn_false hf b (List.mem_of_getElem? hb') hbo)
  · rcases Put_get hb with ⟨hj, rfl⟩ | hb'
    · exact absurd hab (StoredIn_false hf a (List.mem_of_getElem? ha') hao)
    · exact hu i j a b ha' hb' hao hbo hab

theorem Uniq_remove {sl : List Slot} (hu : UniqTids sl) (v : Option Nat) : UniqTids (Put sl v NoSlot) := by
  intro i j a b ha hb hao hbo hab
  rcases Put_get ha with ⟨-, rfl⟩ | ha'
  · simp [NoSlot] at hao
  · rcases Put_get hb with ⟨-, rfl⟩ | hb'
    · simp [NoSlot] at hbo
    · exact hu i j a b ha' hb' hao hbo hab


/-! ## issue_batch -/

/-- The slot `IssueOne` stores for the id `t`. -/
def newSlot (sl : List Slot) (t rs cr : Term) (peer : Nat) (al ad : Term) : Slot :=
  { occ := true, tid := t, psk := psk rs t cr, peer := peer, al := al, ad := ad, cr := cr, exp := false,
    stamp := Stamp sl }

theorem IssueOne_cases (sl : List Slot) (c : List Nat) (rs cr : Term) (peer : Nat) (al ad : Term) :
    (FreshFrom sl c = none ∧ (IssueOne sl c rs cr peer al ad).ok = false ∧ (IssueOne sl c rs cr peer al ad).sl = sl
      ∧ (IssueOne sl c rs cr peer al ad).tid = none)
    ∨ ∃ t, FreshFrom sl c = some t ∧ (IssueOne sl c rs cr peer al ad).ok = true ∧
      (IssueOne sl c rs cr peer al ad).sl = Put sl (Victim sl) (newSlot sl t rs cr peer al ad) ∧
      (IssueOne sl c rs cr peer al ad).tid = (if Victim sl = none then none else some t) := by
  unfold IssueOne
  cases h : FreshFrom sl c with
  | none => left; simp
  | some t => right; exact ⟨t, rfl, rfl, rfl, rfl⟩

theorem IssueOne_uniq {sl : List Slot} (hu : UniqTids sl) (c : List Nat) (rs cr : Term) (peer : Nat) (al ad : Term) :
    UniqTids (IssueOne sl c rs cr peer al ad).sl := by
  rcases IssueOne_cases sl c rs cr peer al ad with ⟨-, -, h, -⟩ | ⟨t, hf, -, h, -⟩
  · rw [h]; exact hu
  · rw [h]; exact Uniq_put hu _ _ rfl (FreshFrom_some hf)

theorem IssueOne_prov {sl : List Slot} (c : List Nat) (rs cr : Term) (peer : Nat) (al ad : Term) :
    ∀ x ∈ (IssueOne sl c rs cr peer al ad).sl, x.occ = true →
      x ∈ sl ∨ ∃ t, x = newSlot sl t rs cr peer al ad := by
  intro x hx ho
  rcases IssueOne_cases sl c rs cr peer al ad with ⟨-, -, h, -⟩ | ⟨t, hf, -, h, -⟩
  · rw [h] at hx; exact Or.inl hx
  · rw [h] at hx
    rcases Put_mem hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr ⟨t, hx⟩

theorem IssueAll_uniq (rs cr : Term) (peer : Nat) (al ad : Term) (cs : List (List Nat)) :
    ∀ (sl : List Slot) (tids : List Term), UniqTids sl → UniqTids (IssueAll sl rs cr peer al ad tids cs).sl := by
  induction cs with
  | nil => intro sl tids hu; simpa [IssueAll] using hu
  | cons c r ih =>
    intro sl tids hu
    simp only [IssueAll]
    split
    · exact IssueOne_uniq hu c rs cr peer al ad
    · exact ih _ _ (IssueOne_uniq hu c rs cr peer al ad)

theorem IssueAll_tids_sub (rs cr : Term) (peer : Nat) (al ad : Term) (cs : List (List Nat)) :
    ∀ (sl : List Slot) (tids : List Term), ∀ t ∈ tids, t ∈ (IssueAll sl rs cr peer al ad tids cs).tids := by
  induction cs with
  | nil => intro sl tids t ht; simpa [IssueAll] using ht
  | cons c r ih =>
    intro sl tids t ht
    simp only [IssueAll]
    split
    · exact ht
    · apply ih
      split
      · exact ht
      · exact List.mem_append_left _ ht

/-- Every occupied slot after `issue_batch` is an old slot or a ticket the batch issued. -/
theorem IssueAll_prov (rs cr : Term) (peer : Nat) (al ad : Term) (cs : List (List Nat)) :
    ∀ (sl : List Slot) (tids : List Term), ∀ x ∈ (IssueAll sl rs cr peer al ad tids cs).sl, x.occ = true →
      x ∈ sl ∨ TicketOf x ∈ IssuedOf (IssueAll sl rs cr peer al ad tids cs).tids rs cr peer al ad := by
  induction cs with
  | nil => intro sl tids x hx ho; exact Or.inl (by simpa [IssueAll] using hx)
  | cons c r ih =>
    intro sl tids x hx ho
    rcases IssueOne_cases sl c rs cr peer al ad with ⟨-, hok, hsl, -⟩ | ⟨t, hf, hok, hsl, htid⟩
    · simp only [IssueAll, hok] at hx ⊢
      simp at hx ⊢
      rw [hsl] at hx
      exact Or.inl hx
    · have e : IssueAll sl rs cr peer al ad tids (c :: r) =
          IssueAll (IssueOne sl c rs cr peer al ad).sl rs cr peer al ad
            (match (IssueOne sl c rs cr peer al ad).tid with | none => tids | some t => tids ++ [t]) r := by
        simp only [IssueAll, hok, Bool.not_true, Bool.false_eq_true, ite_false]
        rfl
      rw [e] at hx ⊢
      rcases ih _ _ x hx ho with h | h
      · rw [hsl] at h
        cases hv : Victim sl with
        | none => rw [hv] at h; exact Or.inl (by simpa [Put] using h)
        | some v =>
          rw [hv] at h
          rcases Put_mem h with h | h
          · exact Or.inl h
          · right
            have hm := IssueAll_tids_sub rs cr peer al ad r (IssueOne sl c rs cr peer al ad).sl
              (match (IssueOne sl c rs cr peer al ad).tid with | none => tids | some t => tids ++ [t])
            have ht : t ∈ (match (IssueOne sl c rs cr peer al ad).tid with | none => tids | some t => tids ++ [t]) := by
              rw [htid, hv]; simp
            have := hm t ht
            subst h
            simp only [IssuedOf, List.mem_map]
            exact ⟨t, this, rfl⟩
      · exact Or.inr h

/-! ## What a responder step does to its store -/

theorem Issue_uniq {sl : List Slot} (hu : UniqTids sl) (cs : List (List Nat)) (rs cr : Term) (peer : Nat) (al ad : Term) :
    UniqTids (Issue sl cs rs cr peer al ad).sl := IssueAll_uniq rs cr peer al ad cs sl [] hu

theorem Issue_prov (sl : List Slot) (cs : List (List Nat)) (rs cr : Term) (peer : Nat) (al ad : Term) :
    ∀ x ∈ (Issue sl cs rs cr peer al ad).sl, x.occ = true →
      x ∈ sl ∨ TicketOf x ∈ IssuedOf (Issue sl cs rs cr peer al ad).tids rs cr peer al ad :=
  IssueAll_prov rs cr peer al ad cs sl []

/-- The store a step leaves: still pairwise distinct ids, every new slot an issued ticket, and a prekey hash only
added by a Finish that completes. -/
def StoOK (st : RState) (sto : Store) (r : RRes) : Prop :=
  (UniqTids sto.tks → UniqTids r.sto.tks) ∧
  (∀ x ∈ r.sto.tks, x.occ = true → x ∈ sto.tks ∨ TicketOf x ∈ r.iss) ∧
  (∀ h ∈ r.sto.pkc, h ∈ sto.pkc ∨ (st.ph = .finish ∧ r.st.ph = .done ∧ r.st.hpk = st.hpk ∧ h = st.hpk))

theorem StoOK_same (st : RState) (sto : Store) (r : RRes) (h : r.sto = sto) : StoOK st sto r := by
  refine ⟨fun hu => h ▸ hu, fun x hx _ => Or.inl (h ▸ hx), fun x hx => Or.inl (h ▸ hx)⟩

theorem RemoveSlot_tks (sto : Store) (i : Option Nat) : (RemoveSlot sto i).tks = Put sto.tks i NoSlot := rfl

theorem rhStoR_prov (sto : Store) (m : Msg) : ∀ x ∈ (rhStoR sto m).tks, x.occ = true → x ∈ sto.tks := by
  intro x hx ho
  rcases Put_mem hx with h | h
  · exact h
  · subst h; simp [NoSlot] at ho

theorem rfSto2_tks (st : RState) (n : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) :
    (rfSto2 st n sto m cs).tks = (rfIs st n sto m cs).sl := by
  unfold rfSto2; split <;> rfl

theorem rfSto2_pkc (st : RState) (n : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) :
    ∀ h ∈ (rfSto2 st n sto m cs).pkc, h ∈ sto.pkc ∨ h = st.hpk := by
  intro h hh
  unfold rfSto2 at hh; split at hh
  · simp [rfSto1] at hh; rcases hh with hh | hh
    · exact Or.inr hh
    · exact Or.inl hh
  · exact Or.inl (by simpa [rfSto1] using hh)

theorem RHandle_sto (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) :
    StoOK st sto (RHandle st n k sto m cs) := by
  rcases RHandle_cases st n k sto m cs with
    ⟨-, -, c, -⟩ | ⟨-, -, -, c, -⟩ | ⟨-, -, -, c, -⟩ | ⟨-, -, -, -, c, -⟩ | ⟨-, -, -, -, c, -⟩ |
    ⟨-, -, -, -, -, -, -, c, -⟩ | ⟨hph, -, -, -, -, -, hst, -, hsto, hiss, -⟩ |
    ⟨hph, -, -, -, -, -, hst, -, hsto, hiss, -⟩ | ⟨-, -, -, -, -, hst, -, hsto, hiss, -⟩ |
    ⟨-, -, -, -, -, -, hst, -, hsto, hiss, -⟩ | ⟨-, -, -, -, -, -, hst, -, hsto, hiss, -⟩
  · exact StoOK_same _ _ _ c
  · exact StoOK_same _ _ _ c
  · exact StoOK_same _ _ _ c
  · exact StoOK_same _ _ _ c
  · exact StoOK_same _ _ _ c
  · exact StoOK_same _ _ _ c
  · refine ⟨fun hu => ?_, fun x hx ho => ?_, fun h hh => ?_⟩
    · rw [hsto, rfSto2_tks]; exact Issue_uniq hu _ _ _ _ _ _
    · rw [hsto, rfSto2_tks] at hx; rw [hiss]; exact Issue_prov _ _ _ _ _ _ _ x hx ho
    · rw [hsto] at hh
      rcases rfSto2_pkc st n sto m cs h hh with h' | h'
      · exact Or.inl h'
      · right; refine ⟨hph, ?_, ?_, h'⟩ <;> rw [hst] <;> rfl
  · refine ⟨fun hu => ?_, fun x hx ho => ?_, fun h hh => Or.inl ?_⟩
    · rw [hsto]; exact Issue_uniq hu _ _ _ _ _ _
    · rw [hsto] at hx; rw [hiss]; exact Issue_prov _ _ _ _ _ _ _ x hx ho
    · rw [hsto] at hh; exact hh
  · refine ⟨fun hu => ?_, fun x hx ho => Or.inl ?_, fun h hh => Or.inl ?_⟩
    · rw [hsto]; unfold rhStoRej; split
      · exact Uniq_remove hu _
      · exact hu
    · rw [hsto] at hx; unfold rhStoRej at hx; split at hx
      · exact rhStoR_prov sto m x hx ho
      · exact hx
    · rw [hsto] at hh; unfold rhStoRej at hh; split at hh <;> exact hh
  all_goals
    refine ⟨fun hu => ?_, fun x hx ho => ?_, fun h hh => Or.inl ?_⟩
    · rw [hsto]; exact Issue_uniq (Uniq_remove hu _) _ _ _ _ _ _
    · rw [hsto] at hx
      rw [hiss]
      rcases Issue_prov _ _ _ _ _ _ _ x hx ho with h | h
      · exact Or.inl (rhStoR_prov sto m x h ho)
      · exact Or.inr h
    · rw [hsto] at hh; exact hh

/-! ## The client store -/

/-- The occupied slots of a client store name pairwise distinct peers. -/
def UniqPeer (sl : List Slot) : Prop :=
  ∀ (i j : Nat) (a b : Slot), sl[i]? = some a → sl[j]? = some b → a.occ = true → b.occ = true → a.peer = b.peer → i = j

theorem CFindPeer_some {sl : List Slot} {p i : Nat} (h : CFindPeer sl p = some i) :
    ∃ a, sl[i]? = some a ∧ a.occ = true ∧ a.peer = p := by
  unfold CFindPeer at h
  rw [List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hl, hp, -⟩ := h
  refine ⟨sl[i], List.getElem?_eq_getElem hl, ?_⟩
  simpa using hp

theorem Uniq_put_peer {sl : List Slot} (hu : UniqPeer sl) (v : Option Nat) (x : Slot)
    (hv : ∀ (j : Nat) (b : Slot), sl[j]? = some b → b.occ = true → b.peer = x.peer → v = some j)
    (hx : x.occ = true) : UniqPeer (Put sl v x) := by
  intro i j a b ha hb hao hbo hab
  rcases Put_get ha with ⟨hi, rfl⟩ | ha'
  · rcases Put_get hb with ⟨hj, rfl⟩ | hb'
    · exact Option.some.inj (hi.symm.trans hj)
    · exact Option.some.inj (hi.symm.trans (hv j b hb' hbo hab.symm))
  · rcases Put_get hb with ⟨hj, rfl⟩ | hb'
    · exact (Option.some.inj (hj.symm.trans (hv i a ha' hao hab))).symm
    · exact hu i j a b ha' hb' hao hbo hab

theorem Uniq_remove_peer {sl : List Slot} (hu : UniqPeer sl) (v : Option Nat) : UniqPeer (Put sl v NoSlot) := by
  intro i j a b ha hb hao hbo hab
  rcases Put_get ha with ⟨-, rfl⟩ | ha'
  · simp [NoSlot] at hao
  · rcases Put_get hb with ⟨-, rfl⟩ | hb'
    · simp [NoSlot] at hbo
    · exact hu i j a b ha' hb' hao hbo hab

theorem CInsert_uniq {sl : List Slot} (hu : UniqPeer sl) (tk : Tk) : UniqPeer (CInsert sl tk) := by
  unfold CInsert
  apply Uniq_put_peer hu _ _ _ rfl
  intro j b hb hbo hbp
  cases hf : CFindPeer sl tk.peer with
  | none =>
    exfalso
    unfold CFindPeer at hf
    rw [List.findIdx?_eq_none_iff] at hf
    have := hf b (List.mem_of_getElem? hb)
    simp [hbo, hbp] at this
  | some i =>
    obtain ⟨a, ha, hao, hap⟩ := CFindPeer_some hf
    have : i = j := hu i j a b ha hb hao hbo (hap.trans hbp.symm)
    simp [this]

theorem CInsertAll_uniq (tks : List Tk) : ∀ {sl : List Slot}, UniqPeer sl → UniqPeer (CInsertAll sl tks) := by
  induction tks with
  | nil => intro sl h; exact h
  | cons t r ih => intro sl h; exact ih (CInsert_uniq h t)

theorem dropExp_occ {x a : Slot} (h : (if (x.occ && x.exp) = true then NoSlot else x) = a) (ho : a.occ = true) :
    a = x := by
  split at h
  · subst h; simp [NoSlot] at ho
  · exact h.symm

theorem CTake_uniq {sl : List Slot} (hu : UniqPeer sl) (peer : Nat) (al : Term) : UniqPeer (CTake sl peer al).sl := by
  have hd : UniqPeer (CDropExpired sl) := by
    intro i j a b ha hb hao hbo hab
    simp only [CDropExpired, List.getElem?_map] at ha hb
    cases hi : sl[i]? with
    | none => rw [hi] at ha; simp at ha
    | some x =>
      cases hj : sl[j]? with
      | none => rw [hj] at hb; simp at hb
      | some y =>
        rw [hi] at ha; rw [hj] at hb
        simp only [Option.map_some, Option.some.injEq] at ha hb
        have ex := dropExp_occ ha hao
        have ey := dropExp_occ hb hbo
        subst ex; subst ey
        exact hu i j _ _ hi hj hao hbo hab
  unfold CTake
  cases hc : CFind (CDropExpired sl) peer al with
  | none => simpa [hc] using hd
  | some i => simpa [hc] using Uniq_remove_peer hd (some i)

theorem UniqPeer_modify {sl : List Slot} (hu : UniqPeer sl) (i : Nat) (f : Slot → Slot)
    (hf : ∀ s, (f s).occ = s.occ ∧ (f s).peer = s.peer) : UniqPeer (sl.modify i f) := by
  intro j k a b ha hb hao hbo hab
  rw [List.getElem?_modify] at ha hb
  cases hj : sl[j]? with
  | none => rw [hj] at ha; simp at ha
  | some x =>
    cases hk : sl[k]? with
    | none => rw [hk] at hb; simp at hb
    | some y =>
      rw [hj] at ha; rw [hk] at hb
      have ha : (if i = j then f x else x) = a := Option.some.inj ha
      have hb : (if i = k then f y else y) = b := Option.some.inj hb
      have hx : ∀ z : Slot, (if i = j then f z else z).occ = z.occ ∧ (if i = j then f z else z).peer = z.peer := by
        intro z; split
        · exact hf z
        · exact ⟨rfl, rfl⟩
      have hy : ∀ z : Slot, (if i = k then f z else z).occ = z.occ ∧ (if i = k then f z else z).peer = z.peer := by
        intro z; split
        · exact hf z
        · exact ⟨rfl, rfl⟩
      rw [← ha] at hao hab; rw [← hb] at hbo hab
      rw [(hx x).1] at hao; rw [(hy y).1] at hbo
      rw [(hx x).2, (hy y).2] at hab
      exact hu j k x y hj hk hao hbo hab

theorem UniqPeer_empty (sl : List Slot) (h : ∀ s ∈ sl, s.occ = false) : UniqPeer sl := by
  intro i j a b ha _ hao
  rw [h a (List.mem_of_getElem? ha)] at hao; cases hao

theorem UniqTids_modify {sl : List Slot} (hu : UniqTids sl) (i : Nat) (f : Slot → Slot)
    (hf : ∀ s, (f s).occ = s.occ ∧ (f s).tid = s.tid) : UniqTids (sl.modify i f) := by
  intro j k a b ha hb hao hbo hab
  rw [List.getElem?_modify] at ha hb
  cases hj : sl[j]? with
  | none => rw [hj] at ha; simp at ha
  | some x =>
    cases hk : sl[k]? with
    | none => rw [hk] at hb; simp at hb
    | some y =>
      rw [hj] at ha; rw [hk] at hb
      have ha : (if i = j then f x else x) = a := Option.some.inj ha
      have hb : (if i = k then f y else y) = b := Option.some.inj hb
      have hx : ∀ z : Slot, (if i = j then f z else z).occ = z.occ ∧ (if i = j then f z else z).tid = z.tid := by
        intro z; split
        · exact hf z
        · exact ⟨rfl, rfl⟩
      have hy : ∀ z : Slot, (if i = k then f z else z).occ = z.occ ∧ (if i = k then f z else z).tid = z.tid := by
        intro z; split
        · exact hf z
        · exact ⟨rfl, rfl⟩
      rw [← ha] at hao hab; rw [← hb] at hbo hab
      rw [(hx x).1] at hao; rw [(hy y).1] at hbo
      rw [(hx x).2, (hy y).2] at hab
      exact hu j k x y hj hk hao hbo hab

theorem mem_modify {sl : List Slot} {i : Nat} {f : Slot → Slot} {x : Slot} (h : x ∈ sl.modify i f) :
    x ∈ sl ∨ ∃ y ∈ sl, x = f y := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
  rw [List.getElem?_modify] at hj
  cases hs : sl[j]? with
  | none => rw [hs] at hj; simp at hj
  | some y =>
    rw [hs] at hj
    have hj : (if i = j then f y else y) = x := Option.some.inj hj
    split at hj
    · exact Or.inr ⟨y, List.mem_of_getElem? hs, hj.symm⟩
    · exact Or.inl (hj ▸ List.mem_of_getElem? hs)

/-- The store invariants, on the components of the global state they concern. -/
structure StoreInv (rst : Nat × Nat → RState) (sto : Nat → Store) (cli : Nat → List Slot) (issued : Tk → Prop) :
    Prop where
  sU : ∀ n, UniqTids (sto n).tks
  sI : ∀ n x, x ∈ (sto n).tks → x.occ = true → issued (TicketOf x)
  ch : ∀ n h, h ∈ (sto n).pkc → ∃ k, (rst (n, k)).ph = .done ∧ (rst (n, k)).hpk = h
  cU : ∀ n, UniqPeer (cli n)

theorem StoreInv_init (K C : Nat) : StoreInv (G0 K C).rst (G0 K C).sto (G0 K C).cli (G0 K C).issued := by
  have h1 : ∀ s ∈ List.replicate K NoSlot, s.occ = false := by
    intro s hs; rw [(List.mem_replicate.mp hs).2]; rfl
  have h2 : ∀ s ∈ List.replicate C NoSlot, s.occ = false := by
    intro s hs; rw [(List.mem_replicate.mp hs).2]; rfl
  refine ⟨fun n => ?_, fun n x hx ho => ?_, fun n h hh => ?_, fun n => ?_⟩
  · intro i j a b ha _ hao; rw [h1 a (List.mem_of_getElem? ha)] at hao; cases hao
  · rw [h1 x hx] at ho; cases ho
  · simp [G0] at hh
  · exact UniqPeer_empty _ h2

theorem RHandle_done (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) (hd : st.ph = .done) :
    (RHandle st n k sto m cs).st = st := by
  rcases RHandle_cases st n k sto m cs with ⟨c, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
    ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact c
  all_goals (rw [hd] at h; simp at h)

theorem RKey_done (st : RState) (n k : Nat) (sto : Store) (kind : KRes) (hd : st.ph = .done) :
    (RKey st n k sto kind).st = st := by
  rcases RKey_cases st n k sto kind with ⟨c, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact c
  all_goals (rw [hd] at h; simp at h)

theorem keep_upd (rst : Nat × Nat → RState) (s : Nat × Nat) (st' : RState) (h : (rst s).ph = .done → st' = rst s) :
    ∀ r, (rst r).ph = .done → (upd rst s st' r).ph = .done ∧ (upd rst s st' r).hpk = (rst r).hpk := by
  intro r hr
  by_cases e : r = s
  · subst e; rw [upd_same, h hr]; exact ⟨hr, rfl⟩
  · rw [upd_ne _ _ _ _ e]; exact ⟨hr, rfl⟩

theorem StoreInv_ch_keep {rst rst' : Nat × Nat → RState} {sto : Nat → Store}
    (hk : ∀ r, (rst r).ph = .done → (rst' r).ph = .done ∧ (rst' r).hpk = (rst r).hpk)
    (h : ∀ n h, h ∈ (sto n).pkc → ∃ k, (rst (n, k)).ph = .done ∧ (rst (n, k)).hpk = h) :
    ∀ n h, h ∈ (sto n).pkc → ∃ k, (rst' (n, k)).ph = .done ∧ (rst' (n, k)).hpk = h := by
  intro n hh hm
  obtain ⟨k, h1, h2⟩ := h n hh hm
  obtain ⟨a, b⟩ := hk _ h1
  exact ⟨k, a, b.trans h2⟩

theorem StoreInv_step {g g' : G} (h : StoreInv g.rst g.sto g.cli g.issued) (hs : Step g g') :
    StoreInv g'.rst g'.sto g'.cli g'.issued := by
  cases hs with
  | iStart s peer al short take _ _ _ =>
    refine ⟨h.sU, h.sI, h.ch, fun n => ?_⟩
    show UniqPeer (upd g.cli s.1 _ n)
    by_cases e : n = s.1
    · subst e; rw [upd_same]
      by_cases ht : take = true
      · simp only [ht, ite_true]; exact CTake_uniq (h.cU _) _ _
      · simp only [ht, ite_false]; exact h.cU _
    · rw [upd_ne _ _ _ _ e]; exact h.cU n
  | iRecv s m _ _ => exact h
  | iAnswer s kind _ _ => exact h
  | iRetrans s _ _ => exact h
  | iShed s _ _ => exact h
  | iAccept s tids _ _ _ _ _ =>
    refine ⟨h.sU, h.sI, h.ch, fun n => ?_⟩
    show UniqPeer (upd g.cli s.1 _ n)
    by_cases e : n = s.1
    · subst e; rw [upd_same]; exact CInsertAll_uniq _ (h.cU _)
    · rw [upd_ne _ _ _ _ e]; exact h.cU n
  | rRecv s m cs _ _ =>
    obtain ⟨hu, hsI, hch⟩ := RHandle_sto (g.rst s) s.1 s.2 (g.sto s.1) m cs
    refine ⟨fun n => ?_, fun n x hx ho => ?_, fun n hh hm => ?_, h.cU⟩
    · show UniqTids (upd g.sto s.1 _ n).tks
      by_cases e : n = s.1
      · subst e; rw [upd_same]; exact hu (h.sU _)
      · rw [upd_ne _ _ _ _ e]; exact h.sU n
    · show g.issued (TicketOf x) ∨ _
      by_cases e : n = s.1
      · subst e
        have hx' : x ∈ (upd g.sto s.1 (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).sto s.1).tks := hx
        rw [upd_same] at hx'
        rcases hsI x hx' ho with h1 | h1
        · exact Or.inl (h.sI _ x h1 ho)
        · exact Or.inr h1
      · have hx' : x ∈ (upd g.sto s.1 (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).sto n).tks := hx
        rw [upd_ne _ _ _ _ e] at hx'
        exact Or.inl (h.sI n x hx' ho)
    · have hm' : hh ∈ (upd g.sto s.1 (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).sto n).pkc := hm
      by_cases e : n = s.1
      · subst e
        rw [upd_same] at hm'
        rcases hch hh hm' with h1 | ⟨hf, hd, hp, rfl⟩
        · obtain ⟨k, a, b⟩ := h.ch _ hh h1
          obtain ⟨a', b'⟩ := keep_upd g.rst s (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).st
            (fun hd => RHandle_done _ _ _ _ _ _ hd) (s.1, k) a
          exact ⟨k, a', b'.trans b⟩
        · refine ⟨s.2, ?_, ?_⟩
          · show (upd g.rst s _ (s.1, s.2)).ph = .done
            rw [upd_same]; exact hd
          · show (upd g.rst s _ (s.1, s.2)).hpk = _
            rw [upd_same]; exact hp
      · rw [upd_ne _ _ _ _ e] at hm'
        obtain ⟨k, a, b⟩ := h.ch n hh hm'
        have hne : (n, k) ≠ s := fun e' => e (by rw [← e'])
        exact ⟨k, by show (upd g.rst s _ (n, k)).ph = .done; rw [upd_ne _ _ _ _ hne]; exact a,
               by show (upd g.rst s _ (n, k)).hpk = _; rw [upd_ne _ _ _ _ hne]; exact b⟩
  | rAnswer s kind _ _ =>
    exact ⟨h.sU, h.sI, StoreInv_ch_keep (keep_upd g.rst s _ (fun hd => RKey_done _ _ _ _ _ hd)) h.ch, h.cU⟩
  | rRetrans s _ _ => exact h
  | rShed s _ =>
    refine ⟨h.sU, h.sI, StoreInv_ch_keep (keep_upd g.rst s _ ?_) h.ch, h.cU⟩
    intro hd; simp [RShed, hd]
  | expire n i sl _ _ _ _ =>
    refine ⟨fun m => ?_, fun m x hx ho => ?_, fun m hh hm => h.ch m hh ?_, h.cU⟩
    · show UniqTids (upd g.sto n _ m).tks
      by_cases e : m = n
      · subst e; rw [upd_same]; exact UniqTids_modify (h.sU _) _ _ (fun _ => ⟨rfl, rfl⟩)
      · rw [upd_ne _ _ _ _ e]; exact h.sU m
    · have hx' : x ∈ (upd g.sto n { g.sto n with tks := (g.sto n).tks.modify i (fun sl => { sl with exp := true }) } m).tks := hx
      by_cases e : m = n
      · subst e
        rw [upd_same] at hx'
        rcases mem_modify hx' with h1 | ⟨y, hy, rfl⟩
        · exact h.sI _ x h1 ho
        · exact h.sI _ y hy ho
      · rw [upd_ne _ _ _ _ e] at hx'; exact h.sI m x hx' ho
    · by_cases e : m = n
      · subst e; simpa [stepExpire, upd_same] using hm
      · simpa [stepExpire, upd_ne _ _ _ _ e] using hm
  | expireC n i sl _ _ _ _ =>
    refine ⟨h.sU, h.sI, h.ch, fun m => ?_⟩
    show UniqPeer (upd g.cli n _ m)
    by_cases e : m = n
    · subst e; rw [upd_same]; exact UniqPeer_modify (h.cU _) _ _ (fun _ => ⟨rfl, rfl⟩)
    · rw [upd_ne _ _ _ _ e]; exact h.cU m
  | «export» n mx _ => exact h
  | restore n drop _ =>
    refine ⟨h.sU, h.sI, h.ch, fun m => ?_⟩
    show UniqPeer (upd g.cli n _ m)
    by_cases e : m = n
    · subst e; rw [upd_same]; exact CInsertAll_uniq _ (h.cU _)
    · rw [upd_ne _ _ _ _ e]; exact h.cU m
  | restart n _ =>
    refine ⟨h.sU, h.sI, h.ch, fun m => ?_⟩
    show UniqPeer (upd g.cli n _ m)
    by_cases e : m = n
    · subst e; rw [upd_same]
      apply UniqPeer_empty; intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; rfl
    · rw [upd_ne _ _ _ _ e]; exact h.cU m

theorem StoreInv_reach {K C : Nat} {g : G} (hr : Reach K C g) : StoreInv g.rst g.sto g.cli g.issued := by
  induction hr with
  | init => exact StoreInv_init K C
  | step _ hs ih => exact StoreInv_step ih hs

/-- Stored ticket ids of every server store are pairwise distinct, whatever the generator returns. -/
theorem uniqueIds {K C : Nat} {g : G} (h : Reach K C g) (n i j : Nat) (a b : Slot) (ha : (g.sto n).tks[i]? = some a)
    (hb : (g.sto n).tks[j]? = some b) (hao : a.occ = true) (hbo : b.occ = true) (hab : a.tid = b.tid) : i = j :=
  (StoreInv_reach h).sU n i j a b ha hb hao hbo hab

/-- Every occupied slot of a server store is a ticket a responder issued. -/
theorem ticketsIssued {K C : Nat} {g : G} (h : Reach K C g) (n i : Nat) (sl : Slot) (hs : (g.sto n).tks[i]? = some sl)
    (ho : sl.occ = true) : g.issued ⟨sl.tid, sl.psk, sl.peer, sl.al, sl.ad, sl.cr⟩ :=
  (StoreInv_reach h).sI n sl (List.mem_of_getElem? hs) ho

/-- A prekey hash is in a cache only if a finished responder session of that node used that prekey. -/
theorem cacheAuthenticated {K C : Nat} {g : G} (h : Reach K C g) (n : Nat) (hp : Term) (hm : hp ∈ (g.sto n).pkc) :
    ∃ k, (g.rst (n, k)).ph = .done ∧ (g.rst (n, k)).hpk = hp :=
  (StoreInv_reach h).ch n hp hm

/-- A client store holds at most one ticket per peer. -/
theorem clientOnePerPeer {K C : Nat} {g : G} (h : Reach K C g) (n i j : Nat) (a b : Slot)
    (ha : (g.cli n)[i]? = some a) (hb : (g.cli n)[j]? = some b) (hao : a.occ = true) (hbo : b.occ = true)
    (hab : a.peer = b.peer) : i = j :=
  (StoreInv_reach h).cU n i j a b ha hb hao hbo hab

#audit_axioms Pinc.Hs.uniqueIds
#audit_axioms Pinc.Hs.ticketsIssued
#audit_axioms Pinc.Hs.cacheAuthenticated
#audit_axioms Pinc.Hs.clientOnePerPeer

end Pinc.Hs
