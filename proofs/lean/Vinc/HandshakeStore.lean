import Vinc.HandshakeInv2

/-!
# The ticket store, the prekey cache and 0-RTT, for unboundedly many sessions

Inductive invariants of the responder side of the system of `HandshakeSys`, proved over every reachable state for
any number of nodes, sessions and tickets and any store capacity `K`:

* every occupied slot of a ticket store is a ticket that was issued (`TicketsIssued`), is owned by a finished
  session of the same node (its id is `tid n k`) and its ticket id is unique in the store;
* a responder that raised the early keys holds them from an issued ticket and authenticated (`NoEarly`);
* no two responder sessions accepted a Hello with the same ticket id (`ZeroRttOnce`): the accepted slot is removed,
  and nothing puts a ticket with that id back, because only a session that is not finished issues, under its own id;
* a prekey hash enters a cache only together with a finished responder session that used that prekey
  (`CacheAuthenticated`).

A rejected Hello leaves the responder and its store as they were, except that an expired slot is removed.
-/

namespace Vinc.Hs
open Term

/-- The invariant, on the three components of the global state it concerns. -/
structure InvRT (rst : Nat × Nat → RState) (sto : Nat → Store) (issued : Tk → Prop) : Prop where
  sI : ∀ (n i : Nat) (sl : Slot), (sto n).tks[i]? = some sl → sl.occ = true → issued ⟨sl.tid, sl.psk, sl.peer⟩
  sO : ∀ (n i : Nat) (sl : Slot), (sto n).tks[i]? = some sl → sl.occ = true → ∃ k, sl.tid = Term.tid n k ∧ (rst (n, k)).ph = .done
  sU : ∀ (n i j : Nat) (a b : Slot), (sto n).tks[i]? = some a → (sto n).tks[j]? = some b → a.occ = true → b.occ = true →
    a.tid = b.tid → i = j
  eI : ∀ r, (rst r).early ≠ nil → (rst r).auth = true ∧
    ∃ t, issued t ∧ t.tid = (rst r).tid ∧ (rst r).early = early (ckpsk t.psk) (rst r).thh
  eT : ∀ r, (rst r).early ≠ nil → ∃ k0, (rst r).tid = Term.tid r.1 k0 ∧ (rst (r.1, k0)).ph = .done
  eN : ∀ r, (rst r).early ≠ nil → ∀ (i : Nat) (sl : Slot), (sto r.1).tks[i]? = some sl → sl.occ = true → sl.tid ≠ (rst r).tid
  ch : ∀ n h, h ∈ (sto n).pkc → ∃ k, (rst (n, k)).ph = .done ∧ (rst (n, k)).hpk = h
  fR : ∀ s, (rst s).ph = .finish → (rst s).reply.ty = .reply
  zr : ∀ r1 r2, r1 ≠ r2 → (rst r1).early ≠ nil → (rst r2).early ≠ nil → (rst r1).tid ≠ (rst r2).tid

theorem InvRT_init (K : Nat) : InvRT (G0 K).rst (G0 K).sto (G0 K).issued := by
  have hg : ∀ (n i : Nat) (sl : Slot), ((G0 K).sto n).tks[i]? = some sl → sl.occ = false := by
    intro n i sl h
    simp only [G0, List.getElem?_replicate] at h
    split at h
    · simp at h; subst h; rfl
    · simp at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i sl h ho; rw [hg n i sl h] at ho; cases ho
  · intro n i sl h ho; rw [hg n i sl h] at ho; cases ho
  · intro n i j a b ha hb hao; rw [hg n i a ha] at hao; cases hao
  · intro r h; simp [G0] at h
  · intro r h; simp [G0] at h
  · intro r h; simp [G0] at h
  · intro n h hm; simp [G0] at hm
  · intro s h; simp [G0] at h
  · intro r1 r2 _ h; simp [G0] at h

/-- The responder session `s` does not move to `done`, keeps what the early-key and finish clauses read, and its
store and ledger do not change. -/
def Frame (st st' : RState) : Prop :=
  st.ph ≠ .done ∧ st'.ph ≠ .done ∧ st'.early = st.early ∧ st'.tid = st.tid ∧ st'.thh = st.thh ∧
    (st.auth = true → st'.auth = true) ∧ (st'.ph = .finish → st'.reply.ty = .reply)

theorem upd_comm_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) (h : f a = b) : upd f a b = f := by
  subst h; exact upd_self f a

theorem upd_self' {α β : Type} [DecidableEq α] (f : α → β) (a : α) : upd f a (f a) = f := by
  funext x; by_cases h : x = a
  · subst h; simp [upd]
  · simp [upd, h]

/-- A step that changes one responder session but not its store, and issues nothing. -/
theorem InvRT_frame {rst sto issued} (h : InvRT rst sto issued) (s : Nat × Nat) (st' : RState)
    (hf : Frame (rst s) st') :
    InvRT (upd rst s st') sto (fun t => issued t ∨ t ∈ ([] : List Tk)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
  have hdone : ∀ w, (rst w).ph = .done → w ≠ s := fun w hw e => f1 (e ▸ hw)
  have hu : ∀ w, w ≠ s → upd rst s st' w = rst w := fun w hw => upd_ne _ _ _ _ hw
  have mono : ∀ t, issued t → (issued t ∨ t ∈ ([] : List Tk)) := fun t ht => Or.inl ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i sl hs ho; exact mono _ (h.sI n i sl hs ho)
  · intro n i sl hs ho
    obtain ⟨k, hk1, hk2⟩ := h.sO n i sl hs ho
    exact ⟨k, hk1, by rw [hu _ (hdone _ hk2)]; exact hk2⟩
  · exact h.sU
  · intro r hr
    by_cases hrs : r = s
    · subst hrs
      simp only [upd_same] at hr ⊢
      rw [f3] at hr ⊢
      obtain ⟨a, t, ht1, ht2, ht3⟩ := h.eI r hr
      exact ⟨f6 a, t, mono _ ht1, by rw [f4]; exact ht2, by rw [f5]; exact ht3⟩
    · rw [hu r hrs] at hr ⊢
      obtain ⟨a, t, ht1, ht2, ht3⟩ := h.eI r hr
      exact ⟨a, t, mono _ ht1, ht2, ht3⟩
  · intro r hr
    by_cases hrs : r = s
    · subst hrs
      simp only [upd_same] at hr ⊢
      rw [f3] at hr
      obtain ⟨k0, hk0, hk1⟩ := h.eT r hr
      exact ⟨k0, by rw [f4]; exact hk0, by rw [hu _ (hdone _ hk1)]; exact hk1⟩
    · rw [hu r hrs] at hr ⊢
      obtain ⟨k0, hk0, hk1⟩ := h.eT r hr
      exact ⟨k0, hk0, by rw [hu _ (hdone _ hk1)]; exact hk1⟩
  · intro r hr i sl hs ho
    by_cases hrs : r = s
    · subst hrs
      simp only [upd_same] at hr ⊢
      rw [f3] at hr; rw [f4]; exact h.eN r hr i sl hs ho
    · rw [hu r hrs] at hr ⊢; exact h.eN r hr i sl hs ho
  · intro n hh hm
    obtain ⟨k, hk1, hk2⟩ := h.ch n hh hm
    exact ⟨k, by rw [hu _ (hdone _ hk1)]; exact hk1, by rw [hu _ (hdone _ hk1)]; exact hk2⟩
  · intro r hr
    by_cases hrs : r = s
    · subst hrs; simp only [upd_same] at hr ⊢; exact f7 hr
    · rw [hu r hrs] at hr ⊢; exact h.fR r hr
  · intro r1 r2 hne h1 h2
    by_cases a : r1 = s <;> by_cases b : r2 = s
    · exact absurd (a.trans b.symm) hne
    · subst a; simp only [upd_same, hu _ b] at h1 h2 ⊢; rw [f3] at h1; rw [f4]; exact h.zr r1 r2 hne h1 h2
    · subst b; simp only [upd_same, hu _ a] at h1 h2 ⊢; rw [f3] at h2; rw [f4]; exact h.zr r1 r2 hne h1 h2
    · simp only [hu _ a, hu _ b] at h1 h2 ⊢; exact h.zr r1 r2 hne h1 h2


/-! ## The store operations -/

theorem IssueTicket_get (sto : Store) (t p : Term) (peer j : Nat) (sl : Slot)
    (h : (IssueTicket sto t p peer).tks[j]? = some sl) :
    (j = Victim sto.tks ∧ sl = { occ := true, tid := t, psk := p, peer := peer, exp := false, stamp := sto.clk + 1 })
    ∨ (j ≠ Victim sto.tks ∧ sto.tks[j]? = some sl) := by
  simp only [IssueTicket, List.getElem?_set] at h
  by_cases hv : Victim sto.tks = j
  · simp only [hv, ite_true] at h
    split at h
    · simp at h; left; exact ⟨hv.symm, h.symm⟩
    · simp at h
  · simp only [hv, ite_false] at h
    right; exact ⟨fun e => hv e.symm, h⟩

theorem RemoveSlot_get (sto : Store) (i j : Nat) (sl : Slot) (h : (RemoveSlot sto i).tks[j]? = some sl)
    (ho : sl.occ = true) : sto.tks[j]? = some sl ∧ j ≠ i := by
  simp only [RemoveSlot, List.getElem?_set] at h
  by_cases hv : i = j
  · simp only [hv, ite_true] at h
    split at h
    · simp at h; subst h; simp [NoSlot] at ho
    · simp at h
  · simp only [hv, ite_false] at h
    exact ⟨h, fun e => hv e.symm⟩

theorem IssueTicket_sU (sto : Store) (t p : Term) (peer : Nat)
    (hU : ∀ (i j : Nat) (a b : Slot), sto.tks[i]? = some a → sto.tks[j]? = some b → a.occ = true → b.occ = true →
      a.tid = b.tid → i = j)
    (hfresh : ∀ (j : Nat) (sl : Slot), sto.tks[j]? = some sl → sl.occ = true → sl.tid ≠ t) :
    ∀ (i j : Nat) (a b : Slot), (IssueTicket sto t p peer).tks[i]? = some a → (IssueTicket sto t p peer).tks[j]? = some b →
      a.occ = true → b.occ = true → a.tid = b.tid → i = j := by
  intro i j a b ha hb hao hbo hab
  rcases IssueTicket_get _ _ _ _ _ _ ha with ⟨hi, rfl⟩ | ⟨hi, ha'⟩
  · rcases IssueTicket_get _ _ _ _ _ _ hb with ⟨hj, rfl⟩ | ⟨hj, hb'⟩
    · rw [hi, hj]
    · exact absurd hab.symm (hfresh j b hb' hbo)
  · rcases IssueTicket_get _ _ _ _ _ _ hb with ⟨hj, rfl⟩ | ⟨hj, hb'⟩
    · exact absurd hab (hfresh i a ha' hao)
    · exact hU i j a b ha' hb' hao hbo hab

/-- The generic step in which one responder session finishes (becomes `done`) and writes its node's store. -/
theorem InvRT_done {rst sto issued} (h : InvRT rst sto issued) (n k : Nat) (st' : RState) (stn : Store) (iss : Tk)
    (hst : (rst (n, k)).ph ≠ .done) (hst' : st'.ph = .done)
    (hget : ∀ (j : Nat) (sl : Slot), stn.tks[j]? = some sl → sl.occ = true →
      (sl.tid = Term.tid n k ∧ (⟨sl.tid, sl.psk, sl.peer⟩ : Tk) = iss) ∨ (sto n).tks[j]? = some sl)
    (hsU : ∀ (i j : Nat) (a b : Slot), stn.tks[i]? = some a → stn.tks[j]? = some b → a.occ = true → b.occ = true →
      a.tid = b.tid → i = j)
    (hpk : ∀ x, x ∈ stn.pkc → x ∈ (sto n).pkc ∨ x = st'.hpk)
    (hE : st'.early ≠ nil → st'.auth = true ∧ (∃ t, (issued t ∨ t = iss) ∧ t.tid = st'.tid ∧
        st'.early = early (ckpsk t.psk) st'.thh) ∧ (∃ k0, st'.tid = Term.tid n k0 ∧ (rst (n, k0)).ph = .done) ∧
      (∀ (j : Nat) (sl : Slot), stn.tks[j]? = some sl → sl.occ = true → sl.tid ≠ st'.tid) ∧
      ∀ r2, r2 ≠ (n, k) → (rst r2).early ≠ nil → (rst r2).tid ≠ st'.tid) :
    InvRT (upd rst (n, k) st') (upd sto n stn) (fun t => issued t ∨ t ∈ [iss]) := by
  have hu : ∀ w, w ≠ (n, k) → upd rst (n, k) st' w = rst w := fun w hw => upd_ne _ _ _ _ hw
  have hdn : ∀ w, (rst w).ph = .done → w ≠ (n, k) := fun w hw e => hst (e ▸ hw)
  have hdp : ∀ w, (rst w).ph = .done → (upd rst (n, k) st' w).ph = .done := fun w hw => by
    rw [hu w (hdn w hw)]; exact hw
  have mono : ∀ t, issued t → (issued t ∨ t ∈ [iss]) := fun t ht => Or.inl ht
  have hsn : ∀ m, m ≠ n → upd sto n stn m = sto m := fun m hm => upd_ne _ _ _ _ hm
  have hnn : upd sto n stn n = stn := upd_same _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m i sl hs ho
    by_cases hm : m = n
    · subst hm; rw [hnn] at hs
      rcases hget i sl hs ho with ⟨-, he⟩ | hs'
      · right; simp [← he]
      · exact mono _ (h.sI m i sl hs' ho)
    · rw [hsn m hm] at hs; exact mono _ (h.sI m i sl hs ho)
  · intro m i sl hs ho
    by_cases hm : m = n
    · subst hm; rw [hnn] at hs
      rcases hget i sl hs ho with ⟨he, -⟩ | hs'
      · exact ⟨k, he, by simp [upd_same, hst']⟩
      · obtain ⟨k1, hk1, hk2⟩ := h.sO m i sl hs' ho
        exact ⟨k1, hk1, hdp _ hk2⟩
    · rw [hsn m hm] at hs
      obtain ⟨k1, hk1, hk2⟩ := h.sO m i sl hs ho
      exact ⟨k1, hk1, hdp _ hk2⟩
  · intro m i j a b ha hb hao hbo hab
    by_cases hm : m = n
    · subst hm; rw [hnn] at ha hb; exact hsU i j a b ha hb hao hbo hab
    · rw [hsn m hm] at ha hb; exact h.sU m i j a b ha hb hao hbo hab
  · intro r hr
    by_cases hrs : r = (n, k)
    · subst hrs; simp only [upd_same] at hr ⊢
      obtain ⟨a, ⟨t, ht1, ht2, ht3⟩, -, -, -⟩ := hE hr
      refine ⟨a, t, ?_, ht2, ht3⟩
      rcases ht1 with ht1 | ht1
      · exact Or.inl ht1
      · right; simp [ht1]
    · rw [hu r hrs] at hr ⊢
      obtain ⟨a, t, ht1, ht2, ht3⟩ := h.eI r hr
      exact ⟨a, t, mono _ ht1, ht2, ht3⟩
  · intro r hr
    by_cases hrs : r = (n, k)
    · subst hrs; simp only [upd_same] at hr ⊢
      obtain ⟨-, -, ⟨k0, hk0, hk1⟩, -, -⟩ := hE hr
      exact ⟨k0, hk0, hdp _ hk1⟩
    · rw [hu r hrs] at hr ⊢
      obtain ⟨k0, hk0, hk1⟩ := h.eT r hr
      exact ⟨k0, hk0, hdp _ hk1⟩
  · intro r hr i sl hs ho
    by_cases hrs : r = (n, k)
    · subst hrs; simp only [upd_same] at hr hs ⊢
      try rw [hnn] at hs
      obtain ⟨-, -, -, hn, -⟩ := hE hr
      exact hn i sl hs ho
    · rw [hu r hrs] at hr ⊢
      by_cases hm : r.1 = n
      · rw [hm, hnn] at hs
        rcases hget i sl hs ho with ⟨he, -⟩ | hs'
        · obtain ⟨k0, hk0, hk1⟩ := h.eT r hr
          intro e
          rw [he, hk0, hm] at e
          injection e with e1 e2
          subst e2
          rw [hm] at hk1
          exact hst hk1
        · exact h.eN r hr i sl (by rw [hm]; exact hs') ho
      · rw [hsn _ hm] at hs; exact h.eN r hr i sl hs ho
  · intro m hh hm
    by_cases hmn : m = n
    · subst hmn; rw [hnn] at hm
      rcases hpk hh hm with hm' | he
      · obtain ⟨k1, hk1, hk2⟩ := h.ch m hh hm'
        exact ⟨k1, hdp _ hk1, by rw [hu _ (hdn _ hk1)]; exact hk2⟩
      · exact ⟨k, by simp [upd_same, hst'], by simp [upd_same, he]⟩
    · rw [hsn m hmn] at hm
      obtain ⟨k1, hk1, hk2⟩ := h.ch m hh hm
      exact ⟨k1, hdp _ hk1, by rw [hu _ (hdn _ hk1)]; exact hk2⟩
  · intro r hr
    by_cases hrs : r = (n, k)
    · subst hrs; simp only [upd_same] at hr; rw [hst'] at hr; cases hr
    · rw [hu r hrs] at hr ⊢; exact h.fR r hr
  · intro r1 r2 hne h1 h2
    by_cases a : r1 = (n, k) <;> by_cases b : r2 = (n, k)
    · exact absurd (a.trans b.symm) hne
    · subst a; simp only [upd_same, hu _ b] at h1 h2 ⊢
      obtain ⟨-, -, -, -, hz⟩ := hE h1
      exact fun e => hz r2 b h2 e.symm
    · subst b; simp only [upd_same, hu _ a] at h1 h2 ⊢
      obtain ⟨-, -, -, -, hz⟩ := hE h2
      exact hz r1 a h1
    · simp only [hu _ a, hu _ b] at h1 h2 ⊢; exact h.zr r1 r2 hne h1 h2

/-- A step that leaves every responder session as it was and replaces a node's store by one whose occupied slots
are slots of the old one (nothing is added, a slot may be removed). -/
theorem InvRT_shrink {rst sto issued} (h : InvRT rst sto issued) (n : Nat) (stn : Store)
    (hget : ∀ (j : Nat) (sl : Slot), stn.tks[j]? = some sl → sl.occ = true → (sto n).tks[j]? = some sl)
    (hpk : stn.pkc = (sto n).pkc) :
    InvRT rst (upd sto n stn) (fun t => issued t ∨ t ∈ ([] : List Tk)) := by
  have hg : ∀ m (j : Nat) (sl : Slot), (upd sto n stn m).tks[j]? = some sl → sl.occ = true →
      (sto m).tks[j]? = some sl := by
    intro m j sl hs ho
    by_cases hm : m = n
    · subst hm; rw [upd_same] at hs; exact hget j sl hs ho
    · rw [upd_ne _ _ _ _ hm] at hs; exact hs
  have hp : ∀ m, (upd sto n stn m).pkc = (sto m).pkc := by
    intro m
    by_cases hm : m = n
    · subst hm; rw [upd_same]; exact hpk
    · rw [upd_ne _ _ _ _ hm]
  have mono : ∀ t, issued t → (issued t ∨ t ∈ ([] : List Tk)) := fun t ht => Or.inl ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m i sl hs ho; exact mono _ (h.sI m i sl (hg m i sl hs ho) ho)
  · intro m i sl hs ho; exact h.sO m i sl (hg m i sl hs ho) ho
  · intro m i j a b ha hb hao hbo hab; exact h.sU m i j a b (hg m i a ha hao) (hg m j b hb hbo) hao hbo hab
  · intro r hr
    obtain ⟨a, t, ht1, ht2, ht3⟩ := h.eI r hr
    exact ⟨a, t, mono _ ht1, ht2, ht3⟩
  · exact h.eT
  · intro r hr i sl hs ho; exact h.eN r hr i sl (hg r.1 i sl hs ho) ho
  · intro m hh hm; rw [hp] at hm; exact h.ch m hh hm
  · exact h.fR
  · exact h.zr

/-! ## The responder steps -/

theorem find_facts (tks : List Slot) (t : Term) (i0 : Nat)
    (h : tks.findIdx? (fun s => s.occ && s.tid == t) = some i0) :
    ∃ sl0, tks[i0]? = some sl0 ∧ sl0.occ = true ∧ sl0.tid = t := by
  rw [List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hl, hp, -⟩ := h
  refine ⟨tks[i0], List.getElem?_eq_getElem hl, ?_⟩
  simpa [Bool.and_eq_true, beq_iff_eq] using hp

theorem issued_nil {i : Tk → Prop} : (fun t => i t ∨ t ∈ ([] : List Tk)) = i := by
  funext t; apply propext; simp

theorem RHello_rej (st : RState) (n k : Nat) (sto : Store) (m : Msg) (hi : st.ph = .idle) (hp : m.prm = ok)
    (ho : (RHello st n k sto m).out = [{ ty := .rrej, echo := rhThh m }]) :
    (RHello st n k sto m).st = st ∧ ((RHello st n k sto m).sto = sto ∨ ∃ i, (RHello st n k sto m).sto = RemoveSlot sto i) := by
  unfold RHello at ho ⊢
  dsimp only at ho ⊢
  rw [if_neg (by rw [hi]; simp), if_neg (by simp [hi]), if_neg (by simp [hp])] at ho ⊢
  by_cases hu : (sto.tks.findIdx? (fun s => s.occ && s.tid == m.tid)).isSome = true ∧
      (rhSlot sto ((sto.tks.findIdx? (fun s => s.occ && s.tid == m.tid)).getD 0)).exp = false ∧
      binder (rhSlot sto ((sto.tks.findIdx? (fun s => s.occ && s.tid == m.tid)).getD 0)).psk (rhThh m) = m.binder
  · simp only [hu, not_true_eq_false, ite_false] at ho
    simp [rhMsg] at ho
  · simp only [hu, not_false_eq_true, ite_true, ROk]
    refine ⟨trivial, ?_⟩
    split
    · right; exact ⟨_, rfl⟩
    · left; rfl

theorem rfSto_tks (st : RState) (n k : Nat) (sto : Store) (m : Msg) :
    (rfSto st n k sto m).tks = (IssueTicket sto (Term.tid n k) (psk (rfRes st m) (Term.tid n k)) m.sealed.id).tks := by
  unfold rfSto; split <;> rfl

theorem rfSto_pkc (st : RState) (n k : Nat) (sto : Store) (m : Msg) :
    ∀ x, x ∈ (rfSto st n k sto m).pkc → x ∈ sto.pkc ∨ x = st.hpk := by
  intro x hx
  unfold rfSto at hx
  split at hx
  · simp [IssueTicket] at hx; rcases hx with hx | hx
    · right; exact hx
    · left; exact hx
  · left; simpa [IssueTicket] using hx

theorem RHandle_hello (st : RState) (n k : Nat) (sto : Store) (m : Msg) (hf : st.ph ≠ .failed) (hty : m.ty = .hello) :
    RHandle st n k sto m = RHello st n k sto m := by
  simp [RHandle, hf, hty]

/-- The invariant is kept by a responder receiving any message. -/
theorem InvRT_rRecv {rst sto issued} (h : InvRT rst sto issued) (n k : Nat) (m : Msg) :
    InvRT (upd rst (n, k) (RHandle (rst (n, k)) n k (sto n) m).st)
      (upd sto n (RHandle (rst (n, k)) n k (sto n) m).sto)
      (fun t => issued t ∨ t ∈ (RHandle (rst (n, k)) n k (sto n) m).iss) := by
  rcases RHandle_cases (rst (n, k)) n k (sto n) m with ⟨c1, c2, c3, c4, c5⟩
    | ⟨hp, c1, c2, c3, c4, c5⟩ | ⟨hp, hty, c1, c2, c3, c4, c5⟩ | ⟨hp, hty, c1, c2, c3, c4, c5⟩
    | ⟨hp, hty, hpr, c1, c2, c3, c4, c5⟩ | ⟨hp, hty, hk, had, hsig, c1, c2, c3, c4, c5⟩
    | ⟨hp, hty, hpr, c1, c2, c4, c5⟩ | ⟨hp, hty, hpr, i0, hfi, hexp, hbind, c1, c2, c3, c4, c5⟩
  · rw [c1, c3, c4, upd_self', upd_self', issued_nil]; exact h
  · have hnd : (rst (n, k)).ph ≠ .done := by rcases hp with hp | hp <;> simp [hp]
    have hF : Frame (rst (n, k)) (RHandle (rst (n, k)) n k (sto n) m).st := by
      rw [c1]; exact ⟨hnd, by simp, rfl, rfl, rfl, fun a => a, by intro e; simp at e⟩
    rw [c3, c4, upd_self']
    exact InvRT_frame h (n, k) _ hF
  · rw [c1, c3, c4, upd_self', upd_self', issued_nil]; exact h
  · rw [c1, c3, c4, upd_self', upd_self', issued_nil]; exact h
  · have hF : Frame (rst (n, k)) (RHandle (rst (n, k)) n k (sto n) m).st := by
      rw [c1]; exact ⟨by simp [hp], by simp [rInitSt], rfl, rfl, rfl, fun a => a, by intro e; simp [rInitSt] at e⟩
    rw [c3, c4, upd_self']
    exact InvRT_frame h (n, k) _ hF
  · -- the Finish authenticates: the session finishes and issues its ticket
    rw [c1, c3, c4]
    have hfresh : ∀ (j : Nat) (sl : Slot), (sto n).tks[j]? = some sl → sl.occ = true → sl.tid ≠ Term.tid n k := by
      intro j sl hs ho e
      obtain ⟨k1, hk1, hk2⟩ := h.sO n j sl hs ho
      have := Term.tid.inj (e.symm.trans hk1)
      obtain ⟨-, rfl⟩ := this
      rw [hp] at hk2; cases hk2
    refine InvRT_done h n k _ _ _ (by simp [hp]) (by simp [rfSt]) ?_ ?_ (fun x hx => rfSto_pkc _ n k _ m x hx) ?_
    · intro j sl hs ho
      rw [rfSto_tks] at hs
      rcases IssueTicket_get _ _ _ _ _ _ hs with ⟨-, rfl⟩ | ⟨-, hs'⟩
      · left; exact ⟨rfl, rfl⟩
      · right; exact hs'
    · intro i j a b ha hb hao hbo hab
      rw [rfSto_tks] at ha hb
      exact IssueTicket_sU _ _ _ _ (h.sU n) hfresh i j a b ha hb hao hbo hab
    · intro he
      obtain ⟨ha, t, ht1, ht2, ht3⟩ := h.eI (n, k) he
      obtain ⟨k0, hk0, hk1⟩ := h.eT (n, k) he
      refine ⟨by simp [rfSt], ⟨t, Or.inl ht1, ht2, ht3⟩, ⟨k0, hk0, hk1⟩, ?_,
        fun r2 hr2 he2 e => h.zr (n, k) r2 (Ne.symm hr2) he he2 e.symm⟩
      intro j sl hs ho
      rw [rfSto_tks] at hs
      rcases IssueTicket_get _ _ _ _ _ _ hs with ⟨-, rfl⟩ | ⟨-, hs'⟩
      · intro e
        have e2 : Term.tid n k = Term.tid n k0 := e.trans hk0
        obtain ⟨-, rfl⟩ := Term.tid.inj e2
        rw [hp] at hk1; cases hk1
      · exact h.eN (n, k) he j sl hs' ho
  · have hf : (rst (n, k)).ph ≠ .failed := by rw [hp]; simp
    have hr := RHello_rej _ n k (sto n) m hp hpr (by rw [← RHandle_hello _ n k _ m hf hty]; exact c2)
    rw [RHandle_hello _ n k _ m hf hty] at c1 c4 ⊢
    rw [hr.1, c4, upd_self']
    refine InvRT_shrink h n _ ?_ ?_
    · rcases hr.2 with e | ⟨i, e⟩
      · rw [e]; exact fun j sl hs _ => hs
      · rw [e]; intro j sl hs ho; exact (RemoveSlot_get _ _ _ _ hs ho).1
    · rcases hr.2 with e | ⟨i, e⟩ <;> rw [e] <;> rfl
  · obtain ⟨sl0, hsl0, hocc0, htid0⟩ := find_facts _ _ _ hfi
    have hslot : rhSlot (sto n) i0 = sl0 := by simp [rhSlot, List.getD_eq_getElem?_getD, hsl0]
    rw [c1, c3, c4]
    have hfresh : ∀ (j : Nat) (sl : Slot), (RemoveSlot (sto n) i0).tks[j]? = some sl → sl.occ = true →
        sl.tid ≠ Term.tid n k := by
      intro j sl hs ho e
      obtain ⟨hs', -⟩ := RemoveSlot_get _ _ _ _ hs ho
      obtain ⟨k1, hk1, hk2⟩ := h.sO n j sl hs' ho
      obtain ⟨-, rfl⟩ := Term.tid.inj (e.symm.trans hk1)
      rw [hp] at hk2; cases hk2
    refine InvRT_done h n k _ _ _ (by simp [hp]) (by simp [rhSt]) ?_ ?_ ?_ ?_
    · intro j sl hs ho
      simp only [rhSto] at hs
      rcases IssueTicket_get _ _ _ _ _ _ hs with ⟨-, rfl⟩ | ⟨-, hs'⟩
      · left; exact ⟨rfl, rfl⟩
      · right; exact (RemoveSlot_get _ _ _ _ hs' ho).1
    · intro i j a b ha hb hao hbo hab
      simp only [rhSto] at ha hb
      refine IssueTicket_sU _ _ _ _ ?_ hfresh i j a b ha hb hao hbo hab
      intro i' j' a' b' ha' hb' hao' hbo' hab'
      exact h.sU n i' j' a' b' (RemoveSlot_get _ _ _ _ ha' hao').1 (RemoveSlot_get _ _ _ _ hb' hbo').1 hao' hbo' hab'
    · intro x hx; left; simpa [rhSto, IssueTicket, RemoveSlot] using hx
    · intro _
      obtain ⟨k0, hk0, hk1⟩ := h.sO n i0 sl0 hsl0 hocc0
      have htid' : (rhSt (rst (n, k)) n k (sto n) i0 m).tid = sl0.tid := by simp [rhSt, htid0]
      refine ⟨by simp [rhSt], ⟨⟨sl0.tid, sl0.psk, sl0.peer⟩, Or.inl (h.sI n i0 sl0 hsl0 hocc0), htid'.symm, ?_⟩,
        ⟨k0, by rw [htid']; exact hk0, hk1⟩, ?_, ?_⟩
      · simp [rhSt, hslot]
      · intro j sl hs ho
        simp only [rhSto] at hs
        rcases IssueTicket_get _ _ _ _ _ _ hs with ⟨-, rfl⟩ | ⟨-, hs'⟩
        · intro e
          rw [htid'] at e
          have e' : Term.tid n k = sl0.tid := e
          obtain ⟨-, rfl⟩ := Term.tid.inj (e'.trans hk0)
          rw [hp] at hk1; cases hk1
        · obtain ⟨hs'', hne⟩ := RemoveSlot_get _ _ _ _ hs' ho
          intro e
          rw [htid'] at e
          exact hne (h.sU n j i0 sl sl0 hs'' hsl0 ho hocc0 e)
      · intro r2 hr2 he2 e
        have e1 : (rst r2).tid = sl0.tid := e.trans htid'
        obtain ⟨k2, hk2, -⟩ := h.eT r2 he2
        obtain ⟨hn2, -⟩ := Term.tid.inj ((hk2.symm.trans e1).trans hk0)
        exact h.eN r2 he2 i0 sl0 (by rw [hn2]; exact hsl0) hocc0 e1.symm

/-- As `InvRT_shrink`, for a store whose occupied slots equal old ones in everything the invariant reads (the
expiry flag may differ). -/
theorem InvRT_shrink2 {rst sto issued} (h : InvRT rst sto issued) (n : Nat) (stn : Store)
    (hget : ∀ (j : Nat) (sl : Slot), stn.tks[j]? = some sl → sl.occ = true →
      ∃ sl' : Slot, (sto n).tks[j]? = some sl' ∧ sl'.occ = true ∧ sl'.tid = sl.tid ∧ sl'.psk = sl.psk ∧ sl'.peer = sl.peer)
    (hpk : stn.pkc = (sto n).pkc) :
    InvRT rst (upd sto n stn) (fun t => issued t ∨ t ∈ ([] : List Tk)) := by
  have hg : ∀ m (j : Nat) (sl : Slot), (upd sto n stn m).tks[j]? = some sl → sl.occ = true →
      ∃ sl' : Slot, (sto m).tks[j]? = some sl' ∧ sl'.occ = true ∧ sl'.tid = sl.tid ∧ sl'.psk = sl.psk ∧
        sl'.peer = sl.peer := by
    intro m j sl hs ho
    by_cases hm : m = n
    · subst hm; rw [upd_same] at hs; exact hget j sl hs ho
    · rw [upd_ne _ _ _ _ hm] at hs; exact ⟨sl, hs, ho, rfl, rfl, rfl⟩
  have hp : ∀ m, (upd sto n stn m).pkc = (sto m).pkc := by
    intro m
    by_cases hm : m = n
    · subst hm; rw [upd_same]; exact hpk
    · rw [upd_ne _ _ _ _ hm]
  have mono : ∀ t, issued t → (issued t ∨ t ∈ ([] : List Tk)) := fun t ht => Or.inl ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m i sl hs ho
    obtain ⟨sl', h1, h2, h3, h4, h5⟩ := hg m i sl hs ho
    have := h.sI m i sl' h1 h2
    rw [h3, h4, h5] at this
    exact mono _ this
  · intro m i sl hs ho
    obtain ⟨sl', h1, h2, h3, -, -⟩ := hg m i sl hs ho
    obtain ⟨k, hk1, hk2⟩ := h.sO m i sl' h1 h2
    exact ⟨k, h3 ▸ hk1, hk2⟩
  · intro m i j a b ha hb hao hbo hab
    obtain ⟨a', h1, h2, h3, -, -⟩ := hg m i a ha hao
    obtain ⟨b', h1', h2', h3', -, -⟩ := hg m j b hb hbo
    exact h.sU m i j a' b' h1 h1' h2 h2' (by rw [h3, h3']; exact hab)
  · intro r hr
    obtain ⟨a, t, ht1, ht2, ht3⟩ := h.eI r hr
    exact ⟨a, t, mono _ ht1, ht2, ht3⟩
  · exact h.eT
  · intro r hr i sl hs ho
    obtain ⟨sl', h1, h2, h3, -, -⟩ := hg r.1 i sl hs ho
    rw [← h3]; exact h.eN r hr i sl' h1 h2
  · intro m hh hm; rw [hp] at hm; exact h.ch m hh hm
  · exact h.fR
  · exact h.zr

theorem InvRT_rAnswer {rst sto issued} (h : InvRT rst sto issued) (n k : Nat) (kind : KRes) :
    InvRT (upd rst (n, k) (RKey (rst (n, k)) n k (sto n) kind).st) sto issued := by
  rcases RKey_cases (rst (n, k)) n k (sto n) kind with ⟨c1, -, -, -, -⟩ | ⟨hp, c1, -, -, -, -⟩
    | ⟨hp, hk, c1, -, -, -, -⟩
  · rw [c1, upd_self']; exact h
  · have hF : Frame (rst (n, k)) (RKey (rst (n, k)) n k (sto n) kind).st := by
      rw [c1]; exact ⟨by simp [hp], by simp, rfl, rfl, rfl, fun a => a, by intro e; simp at e⟩
    have := InvRT_frame h (n, k) _ hF
    rwa [issued_nil] at this
  · have hF : Frame (rst (n, k)) (RKey (rst (n, k)) n k (sto n) kind).st := by
      rw [c1]; exact ⟨by simp [hp], by simp [rkSt], rfl, rfl, rfl, fun a => a, by intro _; simp [rkSt, rkReply]⟩
    have := InvRT_frame h (n, k) _ hF
    rwa [issued_nil] at this

theorem InvRT_expire {rst sto issued} (h : InvRT rst sto issued) (n i : Nat) :
    InvRT rst (upd sto n { sto n with tks := (sto n).tks.modify i (fun sl => { sl with exp := true }) })
      (fun t => issued t ∨ t ∈ ([] : List Tk)) := by
  refine InvRT_shrink2 h n _ ?_ rfl
  intro j sl hs ho
  simp only [List.getElem?_modify] at hs
  cases hj : (sto n).tks[j]? with
  | none => simp [hj] at hs
  | some a =>
    simp only [hj, Option.map_some] at hs
    refine ⟨a, rfl, ?_⟩
    have hsl : sl = if i = j then { a with exp := true } else a := by
      simp at hs; exact hs.symm
    split at hsl <;> (subst hsl; simp_all)

/-- The invariant holds in every reachable state. -/
theorem InvRT_reach {K : Nat} {g : G} (hr : Reach K g) : InvRT g.rst g.sto g.issued := by
  induction hr with
  | init => exact InvRT_init K
  | step _ hs ih =>
    cases hs with
    | startFull => exact ih
    | startResume => exact ih
    | iRecv => exact ih
    | iAnswer => exact ih
    | iRetransmit => exact ih
    | iAcceptFull => exact ih
    | iAcceptResumed => exact ih
    | rRecv s m _ _ =>
      obtain ⟨n, k⟩ := s
      exact InvRT_rRecv ih n k m
    | rAnswer s kind _ =>
      obtain ⟨n, k⟩ := s
      exact InvRT_rAnswer ih n k kind
    | expire n i =>
      have := InvRT_expire ih n i
      rwa [issued_nil] at this

/-! ## The properties of `Handshake.tla` -/

/-- TicketsIssued: every occupied slot of every ticket store is a ticket that was issued. -/
theorem ticketsIssued {K : Nat} {g : G} (h : Reach K g) (n i : Nat) (sl : Slot)
    (hs : (g.sto n).tks[i]? = some sl) (ho : sl.occ = true) : g.issued ⟨sl.tid, sl.psk, sl.peer⟩ :=
  (InvRT_reach h).sI n i sl hs ho

/-- ZeroRttOnce: no two responder sessions accepted a Hello with the same ticket id. -/
theorem zeroRttOnce {K : Nat} {g : G} (h : Reach K g) (r1 r2 : Nat × Nat) (hne : r1 ≠ r2)
    (h1 : (g.rst r1).early ≠ nil) (h2 : (g.rst r2).early ≠ nil) : (g.rst r1).tid ≠ (g.rst r2).tid :=
  (InvRT_reach h).zr r1 r2 hne h1 h2

/-- NoEarly, second half: a responder holding early keys authenticated, and the keys come from a ticket in the
issued ledger with the ticket id of its Hello. -/
theorem earlyTied {K : Nat} {g : G} (h : Reach K g) (r : Nat × Nat) (he : (g.rst r).early ≠ nil) :
    (g.rst r).auth = true ∧ ∃ t, g.issued t ∧ t.tid = (g.rst r).tid ∧
      (g.rst r).early = early (ckpsk t.psk) (g.rst r).thh :=
  (InvRT_reach h).eI r he

/-- CacheAuthenticated: a prekey hash in a node's cache belongs to a finished responder session of that node. -/
theorem cacheAuthenticated {K : Nat} {g : G} (h : Reach K g) (n : Nat) (hp : Term) (hm : hp ∈ (g.sto n).pkc) :
    ∃ k, (g.rst (n, k)).ph = .done ∧ (g.rst (n, k)).hpk = hp :=
  (InvRT_reach h).ch n hp hm

/-- The ticket id of an accepted Hello is not in its node's store: the slot was removed and nothing re-adds it. -/
theorem acceptedGone {K : Nat} {g : G} (h : Reach K g) (r : Nat × Nat) (he : (g.rst r).early ≠ nil) (i : Nat)
    (sl : Slot) (hs : (g.sto r.1).tks[i]? = some sl) (ho : sl.occ = true) : sl.tid ≠ (g.rst r).tid :=
  (InvRT_reach h).eN r he i sl hs ho

#audit_axioms Vinc.Hs.ticketsIssued
#audit_axioms Vinc.Hs.zeroRttOnce
#audit_axioms Vinc.Hs.earlyTied
#audit_axioms Vinc.Hs.cacheAuthenticated
#audit_axioms Vinc.Hs.acceptedGone

end Vinc.Hs
