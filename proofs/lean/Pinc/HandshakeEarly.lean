import Pinc.HandshakeStore

/-!
# 0-RTT at most once, and the early keys, for unboundedly many sessions

Inductive invariants of the responder side of the system of `HandshakeSys`, proved over every reachable state for any
number of nodes, sessions and tickets and any store capacities:

* a responder that raised the early keys authenticated, and holds them from a ticket that was issued (`earlyTied`);
* no two responder sessions accepted a Hello with the same pre-shared key (`zeroRttOnce`), and the accepted ticket is
  gone from the store (`acceptedGone`). The generator may repeat a ticket id once the ticket left the store, so the
  statement is about the pre-shared key, which names the session that issued it.
-/

namespace Pinc.Hs
open Term

/-! ## Which session a pre-shared key belongs to

The transcript hash of a session ends in the responder's own connection id (`RCid`), so the resumption secret and
the pre-shared key of the tickets a session issues name that session: two sessions never issue the same pre-shared
key. This is what makes 0-RTT at most once although the generator may repeat a ticket id once the ticket left the
store. -/

/-- The responder session a transcript hash belongs to (the connection id in its first hash). -/
def tsess : Term → Option (Nat × Nat)
  | th5 t _ => tsess t
  | th4 t _ => tsess t
  | th3 t _ => tsess t
  | th2 t _ _ => tsess t
  | th1 _ (cid 2 n k) _ _ _ => some (n, k)
  | thR _ _ (cid 2 n k) _ _ => some (n, k)
  | _ => none

/-- The session a resumption secret belongs to. -/
def resSess : Term → Option (Nat × Nat)
  | res _ th => tsess th
  | _ => none

/-- The session a pre-shared key belongs to. -/
def pskSess : Term → Option (Nat × Nat)
  | psk r _ _ => resSess r
  | _ => none

/-- The phases of a responder session that has issued its tickets (or tried and failed). -/
def PhI (p : RPh) : Prop := p = .resumed ∨ p = .done ∨ p = .failed

theorem psk_inj {a b c d e f : Term} (h : psk a b c = psk d e f) : a = d ∧ b = e ∧ c = f := by
  simp only [psk.injEq] at h; exact h

theorem pskSess_psk (r t c : Term) : pskSess (psk r t c) = resSess r := rfl

theorem tsess_rfT5 (st : RState) (m : Msg) : tsess (rfT5 st m) = tsess st.th3 := by simp [rfT5, rfT4, tsess]

theorem resSess_rfRes (st : RState) (m : Msg) : resSess (rfRes st m) = tsess st.th3 := by
  simp [rfRes, resSess, tsess_rfT5]

theorem resSess_rhRes (n k : Nat) (sto : Store) (m : Msg) :
    resSess (res (rhCk2 n k sto m) (rhThr n k m)) = some (n, k) := by
  simp [resSess, rhThr, tsess, RCid]

theorem tsess_rT2 (n k : Nat) (m : Msg) : tsess (rT2 n k m) = some (n, k) := by
  simp [rT2, rT1, tsess, RCid]

theorem IssuedOf_psk {tids : List Term} {rs cr : Term} {peer : Nat} {al ad : Term} {x : Tk}
    (h : x ∈ IssuedOf tids rs cr peer al ad) : ∃ t, x.psk = psk rs t cr ∧ x.tid = t := by
  simp only [IssuedOf, List.mem_map] at h
  obtain ⟨t, -, rfl⟩ := h
  exact ⟨t, rfl, rfl⟩


theorem PhI_handle (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) (h : PhI st.ph) :
    PhI (RHandle st n k sto m cs).st.ph := by
  rcases RHandle_cases st n k sto m cs with ⟨c, -⟩ | ⟨-, c, -⟩ | ⟨-, ⟨sp, nr, c⟩, -⟩ | ⟨-, -, c, -⟩ | ⟨-, -, c, -⟩ |
    ⟨hp, -, -, -, -, c, -⟩ | ⟨hp, -, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, c, -⟩ |
    ⟨hp, -, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, -, c, -⟩
  · rw [c]; exact h
  · rw [c]; right; right; rfl
  · rw [c]; exact h
  · rw [c]; exact h
  · rw [c]; exact h
  · rw [hp] at h; simp [PhI] at h
  · rw [hp] at h; simp [PhI] at h
  · rw [c]; right; right; rfl
  · rw [c]; exact h
  · rw [hp] at h; simp [PhI] at h
  · rw [c]; right; right; rfl

theorem PhI_key (st : RState) (n k : Nat) (sto : Store) (kind : KRes) (h : PhI st.ph) :
    PhI (RKey st n k sto kind).st.ph := by
  rcases RKey_cases st n k sto kind with ⟨c, -⟩ | ⟨hp, c, -⟩ | ⟨hp, -, c, -⟩
  · rw [c]; exact h
  · rw [hp] at h; simp [PhI] at h
  · rw [hp] at h; simp [PhI] at h

/-- Tickets a responder step issues belong to the session that made them, which has now issued; and only a session
that had not issued yet issues. -/
theorem RHandle_iss (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat))
    (hl : st.ph = .finish → tsess st.th3 = some (n, k)) :
    ∀ t ∈ (RHandle st n k sto m cs).iss, pskSess t.psk = some (n, k) ∧ PhI (RHandle st n k sto m cs).st.ph ∧
      ¬ PhI st.ph ∧ ∃ x, t.psk = psk x t.tid (RCr n) := by
  intro t ht
  rcases RHandle_cases st n k sto m cs with ⟨-, -, -, c, -⟩ | ⟨-, -, -, -, c, -⟩ | ⟨-, -, -, -, c, -⟩ |
    ⟨-, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, -, -, -, c, -⟩ |
    ⟨hp, -, -, -, -, -, hs, -, -, hi, -⟩ | ⟨hp, -, -, -, -, -, hs, -, -, hi, -⟩ | ⟨-, -, -, -, -, -, -, -, c, -⟩ |
    ⟨hp, -, -, -, -, -, hs, -, -, hi, -⟩ | ⟨hp, -, -, -, -, -, hs, -, -, hi, -⟩
  all_goals first | (rw [c] at ht; cases ht; done) | skip
  · rw [hi] at ht
    obtain ⟨x, hx1, hx2⟩ := IssuedOf_psk ht
    refine ⟨?_, ?_, ?_, _, by rw [hx1, hx2]⟩
    · rw [hx1, pskSess_psk]; rw [resSess_rfRes, hl hp]
    · rw [hs]; right; left; rfl
    · rw [hp]; simp [PhI]
  · rw [hi] at ht
    obtain ⟨x, hx1, hx2⟩ := IssuedOf_psk ht
    refine ⟨?_, ?_, ?_, _, by rw [hx1, hx2]⟩
    · rw [hx1, pskSess_psk]; rw [resSess_rfRes, hl hp]
    · rw [hs]; right; right; rfl
    · rw [hp]; simp [PhI]
  · rw [hi] at ht
    obtain ⟨x, hx1, hx2⟩ := IssuedOf_psk ht
    refine ⟨?_, ?_, ?_, _, by rw [hx1, hx2]⟩
    · rw [hx1, pskSess_psk]; exact resSess_rhRes _ _ _ _
    · rw [hs]; left; rfl
    · rw [hp]; simp [PhI]
  · rw [hi] at ht
    obtain ⟨x, hx1, hx2⟩ := IssuedOf_psk ht
    refine ⟨?_, ?_, ?_, _, by rw [hx1, hx2]⟩
    · rw [hx1, pskSess_psk]; exact resSess_rhRes _ _ _ _
    · rw [hs]; right; right; rfl
    · rw [hp]; simp [PhI]


theorem rhI0_spec {sto : Store} {m : Msg} (h : (rhI0 sto m).isSome = true) :
    ∃ i0 x, rhI0 sto m = some i0 ∧ sto.tks[i0]? = some x ∧ x.occ = true ∧ x.tid = m.tid ∧ rhSlot sto m = x := by
  cases hf : rhI0 sto m with
  | none => rw [hf] at h; simp at h
  | some i0 =>
    have hf' := hf
    unfold rhI0 at hf'
    rw [List.findIdx?_eq_some_iff_getElem] at hf'
    obtain ⟨hl, hp, -⟩ := hf'
    refine ⟨i0, sto.tks[i0], rfl, List.getElem?_eq_getElem hl, ?_, ?_, ?_⟩
    · simpa using (by simpa using hp : sto.tks[i0].occ = true ∧ _).1
    · simpa using (by simpa using hp : _ ∧ sto.tks[i0].tid = m.tid).2
    · simp [rhSlot, hf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]

/-- What a step does to the early-key fields of the session: nothing, or the Hello is accepted. -/
theorem RHandle_early (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) :
    ((RHandle st n k sto m cs).st.early = st.early ∧ (RHandle st n k sto m cs).st.tpsk = st.tpsk ∧
      (RHandle st n k sto m cs).st.tid = st.tid ∧ (RHandle st n k sto m cs).st.thh = st.thh ∧
      (st.auth = true → (RHandle st n k sto m cs).st.auth = true))
    ∨ (st.ph = .idle ∧ ∃ i0 x, rhI0 sto m = some i0 ∧ sto.tks[i0]? = some x ∧ x.occ = true ∧ x.tid = m.tid ∧
        rhSlot sto m = x ∧ (RHandle st n k sto m cs).st = rhSt st n k sto m cs ∧ (rhIs n k sto m cs).ok = true ∧
        (RHandle st n k sto m cs).sto = rhSto1 n k sto m cs ∧ (RHandle st n k sto m cs).iss = rhIss n k sto m cs) := by
  rcases RHandle_cases st n k sto m cs with ⟨c, -⟩ | ⟨-, c, -⟩ | ⟨-, ⟨sp, nr, c⟩, -⟩ | ⟨-, -, c, -⟩ | ⟨-, -, c, -⟩ |
    ⟨-, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, c, -⟩ |
    ⟨hp, -, -, -, hu, hok, c, -, c3, c4, -⟩ | ⟨-, -, -, -, -, -, c, -⟩
  · left; rw [c]; exact ⟨rfl, rfl, rfl, rfl, id⟩
  · left; rw [c]; exact ⟨rfl, rfl, rfl, rfl, id⟩
  · left; rw [c]; exact ⟨rfl, rfl, rfl, rfl, id⟩
  · left; rw [c]; exact ⟨rfl, rfl, rfl, rfl, id⟩
  · left; rw [c]; exact ⟨rfl, rfl, rfl, rfl, id⟩
  · left; rw [c]; exact ⟨rfl, rfl, rfl, rfl, id⟩
  · left; rw [c]; exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · left; rw [c]; exact ⟨rfl, rfl, rfl, rfl, id⟩
  · left; rw [c]; exact ⟨rfl, rfl, rfl, rfl, id⟩
  · right
    obtain ⟨i0, x, h1, h2, h3, h4, h5⟩ := rhI0_spec hu.1
    exact ⟨hp, i0, x, h1, h2, h3, h4, h5, c, hok, c3, c4⟩
  · left; rw [c]; exact ⟨rfl, rfl, rfl, rfl, id⟩


/-- The five shapes of the state a responder step leaves. -/
theorem RHandle_forms (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) :
    (∃ sp nr, (RHandle st n k sto m cs).st = { st with spent := sp, nre := nr })
    ∨ (RHandle st n k sto m cs).st = { st with ph := .failed }
    ∨ (st.ph = .idle ∧ (RHandle st n k sto m cs).st = rInitSt st n k m)
    ∨ (st.ph = .finish ∧ (RHandle st n k sto m cs).st = rfSt st n sto m cs)
    ∨ (st.ph = .idle ∧ (RHandle st n k sto m cs).st = rhSt st n k sto m cs) := by
  rcases RHandle_cases st n k sto m cs with ⟨c, -⟩ | ⟨-, c, -⟩ | ⟨-, ⟨sp, nr, c⟩, -⟩ | ⟨-, -, c, -⟩ | ⟨-, -, c, -⟩ |
    ⟨hp, -, -, -, -, c, -⟩ | ⟨hp, -, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, c, -⟩ |
    ⟨hp, -, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, -, c, -⟩
  · left; exact ⟨st.spent, st.nre, c⟩
  · right; left; exact c
  · left; exact ⟨sp, nr, c⟩
  · left; exact ⟨st.spent, st.nre, c⟩
  · left; exact ⟨st.spent, st.nre, c⟩
  · right; right; left; exact ⟨hp, c⟩
  · right; right; right; left; exact ⟨hp, c⟩
  · right; left; exact c
  · left; exact ⟨st.spent, st.nre, c⟩
  · right; right; right; right; exact ⟨hp, c⟩
  · right; left; exact c


theorem Put_remove_get {sl : List Slot} {i j : Nat} {a : Slot} (hi : i < sl.length)
    (h : (Put sl (some i) NoSlot)[j]? = some a) (ho : a.occ = true) : j ≠ i ∧ sl[j]? = some a := by
  simp only [Put] at h
  rw [List.getElem?_set] at h
  split at h
  · rename_i hh
    have h' : NoSlot = a := Option.some.inj h
    subst h'; simp [NoSlot] at ho
  · rename_i hh; exact ⟨fun e => hh e.symm, h⟩

theorem tpsk_ne_of_sess {a b : Term} {s t : Nat × Nat} (h1 : pskSess a = some s) (h2 : pskSess b = some t) (hne : s ≠ t) :
    a ≠ b := by
  intro e; subst e; rw [h1] at h2; exact hne (Option.some.inj h2)

/-- The invariants of the early keys, the tickets and the ledger, on the components they concern. -/
structure EInv (rst : Nat × Nat → RState) (sto : Nat → Store) (issued : Tk → Prop) : Prop where
  li : ∀ s, ((rst s).ph = .sign ∨ (rst s).ph = .finish) → tsess (rst s).th2 = some s
  li3 : ∀ s, (rst s).ph = .finish → tsess (rst s).th3 = some s
  led : ∀ t, issued t → ∃ s, pskSess t.psk = some s ∧ PhI (rst s).ph
  sn : ∀ n x, x ∈ (sto n).tks → x.occ = true → ∃ k, pskSess x.psk = some (n, k)
  pf : ∀ n x, x ∈ (sto n).tks → x.occ = true → ∃ r c, x.psk = psk r x.tid c
  ep : ∀ r, (rst r).early ≠ nil → PhI (rst r).ph ∧ (rst r).auth = true ∧
    (∃ t, issued t ∧ t.tid = (rst r).tid ∧ t.psk = (rst r).tpsk ∧ early (ckpsk t.psk) (rst r).thh = (rst r).early) ∧
    ∃ k, pskSess (rst r).tpsk = some (r.1, k)
  ag : ∀ r, (rst r).early ≠ nil → ∀ x ∈ (sto r.1).tks, x.occ = true → x.psk ≠ (rst r).tpsk
  zr : ∀ r1 r2, r1 ≠ r2 → (rst r1).early ≠ nil → (rst r2).early ≠ nil → (rst r1).tpsk ≠ (rst r2).tpsk

theorem EInv_init (K C : Nat) : EInv (G0 K C).rst (G0 K C).sto (G0 K C).issued := by
  have h1 : ∀ s ∈ List.replicate K NoSlot, s.occ = false := by
    intro s hs; rw [(List.mem_replicate.mp hs).2]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s h; simp [G0] at h
  · intro s h; simp [G0] at h
  · intro t h; simp [G0] at h
  · intro n x hx ho; simp only [G0] at hx; rw [h1 x hx] at ho; cases ho
  · intro n x hx ho; simp only [G0] at hx; rw [h1 x hx] at ho; cases ho
  · intro r h; simp [G0] at h
  · intro r h; simp [G0] at h
  · intro r1 r2 _ h; simp [G0] at h


theorem EInv_rRecv {rst : Nat × Nat → RState} {sto : Nat → Store} {cli : Nat → List Slot} {issued : Tk → Prop}
    (h : EInv rst sto issued) (hs : StoreInv rst sto cli issued) (s : Nat × Nat) (m : Msg) (cs : List (List Nat)) :
    EInv (upd rst s (RHandle (rst s) s.1 s.2 (sto s.1) m cs).st) (upd sto s.1 (RHandle (rst s) s.1 s.2 (sto s.1) m cs).sto)
      (fun t => issued t ∨ t ∈ (RHandle (rst s) s.1 s.2 (sto s.1) m cs).iss) := by
  have fO := RHandle_forms (rst s) s.1 s.2 (sto s.1) m cs
  have fE := RHandle_early (rst s) s.1 s.2 (sto s.1) m cs
  have fS := RHandle_sto (rst s) s.1 s.2 (sto s.1) m cs
  have fI := RHandle_iss (rst s) s.1 s.2 (sto s.1) m cs (h.li3 s)
  have fP := PhI_handle (rst s) s.1 s.2 (sto s.1) m cs
  generalize RHandle (rst s) s.1 s.2 (sto s.1) m cs = R at *
  have mono : ∀ t, issued t → (issued t ∨ t ∈ R.iss) := fun t ht => Or.inl ht
  have ups : ∀ r, r ≠ s → upd rst s R.st r = rst r := fun r hr => upd_ne _ _ _ _ hr
  have upn : ∀ n, n ≠ s.1 → upd sto s.1 R.sto n = sto n := fun n hn => upd_ne _ _ _ _ hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- li
    intro r hr
    by_cases e : r = s
    · subst e
      rw [upd_same] at hr ⊢
      rcases fO with ⟨sp, nr, c⟩ | c | ⟨hp, c⟩ | ⟨hp, c⟩ | ⟨hp, c⟩
      · rw [c] at hr ⊢; exact h.li r hr
      · rw [c] at hr; simp at hr
      · rw [c]; simp [rInitSt, tsess_rT2]
      · rw [c] at hr; simp [rfSt] at hr
      · rw [c] at hr; simp [rhSt] at hr
    · rw [ups r e] at hr ⊢; exact h.li r hr
  · -- li3
    intro r hr
    by_cases e : r = s
    · subst e
      rw [upd_same] at hr ⊢
      rcases fO with ⟨sp, nr, c⟩ | c | ⟨hp, c⟩ | ⟨hp, c⟩ | ⟨hp, c⟩
      · rw [c] at hr ⊢; exact h.li3 r hr
      · rw [c] at hr; simp at hr
      · rw [c] at hr; simp [rInitSt] at hr
      · rw [c] at hr; simp [rfSt] at hr
      · rw [c] at hr; simp [rhSt] at hr
    · rw [ups r e] at hr ⊢; exact h.li3 r hr
  · -- led
    intro t ht
    rcases ht with ht | ht
    · obtain ⟨s', h1, h2⟩ := h.led t ht
      refine ⟨s', h1, ?_⟩
      by_cases e : s' = s
      · subst e; rw [upd_same]; exact fP h2
      · rw [ups s' e]; exact h2
    · obtain ⟨h1, h2, -, -⟩ := fI t ht
      exact ⟨s, h1, by rw [upd_same]; exact h2⟩
  · -- sn
    intro n x hx ho
    by_cases e : n = s.1
    · subst e
      rw [upd_same] at hx
      rcases fS.2.1 x hx ho with h1 | h1
      · exact h.sn _ x h1 ho
      · obtain ⟨h2, -⟩ := fI _ h1
        exact ⟨s.2, h2⟩
    · rw [upn n e] at hx; exact h.sn n x hx ho
  · -- pf
    intro n x hx ho
    by_cases e : n = s.1
    · subst e
      rw [upd_same] at hx
      rcases fS.2.1 x hx ho with h1 | h1
      · exact h.pf _ x h1 ho
      · obtain ⟨-, -, -, x0, h2⟩ := fI _ h1
        exact ⟨x0, _, h2⟩
    · rw [upn n e] at hx; exact h.pf n x hx ho
  · -- ep
    intro r hr
    by_cases e : r = s
    · subst e
      rw [upd_same] at hr ⊢
      rcases fE with ⟨e1, e2, e3, e4, e5⟩ | ⟨hp, i0, x, h1, h2, h3, h4, h5, hst, hok, hsto, hiss⟩
      · rw [e1] at hr
        obtain ⟨p1, p2, ⟨t, t1, t2, t3, t4⟩, p4⟩ := h.ep r hr
        refine ⟨fP p1, e5 p2, ⟨t, mono t t1, ?_, ?_, ?_⟩, ?_⟩
        · rw [e3]; exact t2
        · rw [e2]; exact t3
        · rw [e4, e1]; exact t4
        · rw [e2]; exact p4
      · rw [hst]
        obtain ⟨k, hk⟩ := h.sn r.1 x (List.mem_of_getElem? h2) h3
        refine ⟨Or.inl rfl, rfl, ⟨TicketOf x, mono _ (hs.sI r.1 x (List.mem_of_getElem? h2) h3), ?_, ?_, ?_⟩, ?_⟩
        · simp [TicketOf, rhSt, h4]
        · simp [TicketOf, rhSt, h5]
        · simp [TicketOf, rhSt, h5]
        · simp [rhSt, h5]; exact ⟨k, hk⟩
    · rw [ups r e] at hr ⊢
      obtain ⟨p1, p2, ⟨t, t1, t2, t3, t4⟩, p4⟩ := h.ep r hr
      exact ⟨p1, p2, ⟨t, mono t t1, t2, t3, t4⟩, p4⟩
  · -- ag
    intro r hr x hx ho
    by_cases e : r = s
    · subst e
      rw [upd_same] at hr ⊢
      rw [upd_same] at hx
      rcases fE with ⟨e1, e2, e3, e4, e5⟩ | ⟨hp, i0, x0, h1, h2, h3, h4, h5, hst, hok, hsto, hiss⟩
      · rw [e2]
        rw [e1] at hr
        rcases fS.2.1 x hx ho with h1 | h1
        · exact h.ag r hr x h1 ho
        · exact absurd (h.ep r hr).1 (fI _ h1).2.2.1
      · have hp' := hp
        rw [hst]
        have hx' : x ∈ (rhIs r.1 r.2 (sto r.1) m cs).sl := by rw [hsto] at hx; exact hx
        have hx0 : x0 ∈ (sto r.1).tks := List.mem_of_getElem? h2
        simp only [rhSt]
        rw [h5]
        rcases Issue_prov _ _ _ _ _ _ _ x hx' ho with h6 | h6
        · rw [rhStoR, RemoveSlot_tks, h1] at h6
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h6
          obtain ⟨hj1, hj2⟩ := Put_remove_get (List.getElem?_eq_some_iff.mp h2).1 hj ho
          intro hp
          obtain ⟨r1, c1, hc1⟩ := h.pf r.1 x (List.mem_of_getElem? hj2) ho
          obtain ⟨r2, c2, hc2⟩ := h.pf r.1 x0 hx0 h3
          rw [hc1, hc2] at hp
          have := (psk_inj hp).2.1
          exact hj1 (hs.sU r.1 j i0 x x0 hj2 h2 ho h3 this)
        · have h6' : TicketOf x ∈ R.iss := by rw [hiss]; exact h6
          obtain ⟨hk1, -, -, -⟩ := fI _ h6'
          obtain ⟨s0, hs0, hph0⟩ := h.led (TicketOf x0) (hs.sI r.1 x0 hx0 h3)
          intro hp
          have : pskSess x.psk = some s0 := by rw [hp]; exact hs0
          have hk1' : pskSess x.psk = _ := hk1
          rw [hk1'] at this
          have e0 : r = s0 := Option.some.inj this
          rw [← e0, hp'] at hph0
          simp [PhI] at hph0
    · by_cases e1 : r.1 = s.1
      · have hx2 : x ∈ (R.sto).tks := by rw [e1, upd_same] at hx; exact hx
        rw [ups r e] at hr ⊢
        rcases fS.2.1 x hx2 ho with h1 | h1
        · exact h.ag r hr x (by rw [e1]; exact h1) ho
        · obtain ⟨hk1, -, hk3, -⟩ := fI _ h1
          obtain ⟨p1, p2, ⟨t, t1, t2, t3, t4⟩, p4⟩ := h.ep r hr
          obtain ⟨s0, hs0, hph0⟩ := h.led t t1
          intro hp
          have : pskSess x.psk = some s0 := by rw [hp, ← t3]; exact hs0
          have hk1' : pskSess x.psk = _ := hk1
          rw [hk1'] at this
          have e0 : s = s0 := Option.some.inj this
          rw [← e0] at hph0
          exact hk3 hph0
      · rw [upn r.1 e1] at hx; rw [ups r e]; rw [ups r e] at hr; exact h.ag r hr x hx ho
  · -- zr
    intro r1 r2 hne h1 h2
    have key : ∀ r, r ≠ s → (rst r).early ≠ nil → R.st.early ≠ nil → R.st.tpsk ≠ (rst r).tpsk := by
      intro r hr hre hse
      rcases fE with ⟨e1, e2, e3, e4, e5⟩ | ⟨hp, i0, x0, h1, h2, h3, h4, h5, hst, hok, hsto, hiss⟩
      · rw [e2]; rw [e1] at hse; exact h.zr s r (Ne.symm hr) hse hre
      · have hx0 : x0 ∈ (sto s.1).tks := List.mem_of_getElem? h2
        rw [hst]; simp only [rhSt]; rw [h5]
        by_cases e : r.1 = s.1
        · exact h.ag r hre x0 (by rw [e]; exact hx0) h3
        · obtain ⟨k, hk⟩ := h.sn s.1 x0 hx0 h3
          obtain ⟨-, -, -, k', hk'⟩ := h.ep r hre
          exact tpsk_ne_of_sess hk hk' (fun e' => e (by rw [← (Prod.mk.inj e').1]))
    by_cases e1 : r1 = s <;> by_cases e2 : r2 = s
    · exact absurd (e1.trans e2.symm) hne
    · subst e1
      rw [upd_same] at h1 ⊢; rw [ups r2 e2] at h2 ⊢
      exact key r2 e2 h2 h1
    · subst e2
      rw [upd_same] at h2 ⊢; rw [ups r1 e1] at h1 ⊢
      exact (key r1 e1 h1 h2).symm
    · rw [ups r1 e1] at h1 ⊢; rw [ups r2 e2] at h2 ⊢
      exact h.zr r1 r2 hne h1 h2


/-- A step that changes one responder session without touching the stores or the ledger, keeping the early-key
fields, never leaving the issued phases, and keeping the transcript clauses. -/
theorem EInv_frame {rst : Nat × Nat → RState} {sto : Nat → Store} {issued : Tk → Prop} (h : EInv rst sto issued)
    (s : Nat × Nat) (st' : RState)
    (f1 : st'.early = (rst s).early ∧ st'.tpsk = (rst s).tpsk ∧ st'.tid = (rst s).tid ∧ st'.thh = (rst s).thh ∧
      ((rst s).auth = true → st'.auth = true))
    (f2 : PhI (rst s).ph → PhI st'.ph)
    (f3 : (st'.ph = .sign ∨ st'.ph = .finish) → tsess st'.th2 = some s)
    (f4 : st'.ph = .finish → tsess st'.th3 = some s) :
    EInv (upd rst s st') sto issued := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := f1
  have ups : ∀ r, r ≠ s → upd rst s st' r = rst r := fun r hr => upd_ne _ _ _ _ hr
  refine ⟨?_, ?_, ?_, h.sn, h.pf, ?_, ?_, ?_⟩
  · intro r hr
    by_cases e : r = s
    · subst e; rw [upd_same] at hr ⊢; exact f3 hr
    · rw [ups r e] at hr ⊢; exact h.li r hr
  · intro r hr
    by_cases e : r = s
    · subst e; rw [upd_same] at hr ⊢; exact f4 hr
    · rw [ups r e] at hr ⊢; exact h.li3 r hr
  · intro t ht
    obtain ⟨s', h1, h2⟩ := h.led t ht
    refine ⟨s', h1, ?_⟩
    by_cases e : s' = s
    · subst e; rw [upd_same]; exact f2 h2
    · rw [ups s' e]; exact h2
  · intro r hr
    by_cases e : r = s
    · subst e
      rw [upd_same] at hr ⊢
      rw [g1] at hr
      obtain ⟨p1, p2, ⟨t, t1, t2, t3, t4⟩, p4⟩ := h.ep r hr
      refine ⟨f2 p1, g5 p2, ⟨t, t1, ?_, ?_, ?_⟩, ?_⟩
      · rw [g3]; exact t2
      · rw [g2]; exact t3
      · rw [g4, g1]; exact t4
      · rw [g2]; exact p4
    · rw [ups r e] at hr ⊢; exact h.ep r hr
  · intro r hr x hx ho
    by_cases e : r = s
    · subst e
      rw [upd_same] at hr ⊢
      rw [g1] at hr; rw [g2]; exact h.ag r hr x hx ho
    · rw [ups r e] at hr ⊢; exact h.ag r hr x hx ho
  · intro r1 r2 hne h1 h2
    by_cases e1 : r1 = s <;> by_cases e2 : r2 = s
    · exact absurd (e1.trans e2.symm) hne
    · subst e1
      rw [upd_same] at h1 ⊢; rw [ups r2 e2] at h2 ⊢
      rw [g2]; rw [g1] at h1; exact h.zr r1 r2 hne h1 h2
    · subst e2
      rw [upd_same] at h2 ⊢; rw [ups r1 e1] at h1 ⊢
      rw [g2]; rw [g1] at h2; exact h.zr r1 r2 hne h1 h2
    · rw [ups r1 e1] at h1 ⊢; rw [ups r2 e2] at h2 ⊢
      exact h.zr r1 r2 hne h1 h2


theorem EInv_rKey {rst : Nat × Nat → RState} {sto : Nat → Store} {issued : Tk → Prop} (h : EInv rst sto issued)
    (s : Nat × Nat) (kind : KRes) :
    EInv (upd rst s (RKey (rst s) s.1 s.2 (sto s.1) kind).st) sto issued := by
  apply EInv_frame h
  · rcases RKey_cases (rst s) s.1 s.2 (sto s.1) kind with ⟨c, -⟩ | ⟨-, c, -⟩ | ⟨-, -, c, -⟩ <;> rw [c] <;>
      exact ⟨rfl, rfl, rfl, rfl, id⟩
  · exact PhI_key _ _ _ _ _
  · rcases RKey_cases (rst s) s.1 s.2 (sto s.1) kind with ⟨c, -⟩ | ⟨-, c, -⟩ | ⟨hp, -, c, -⟩
    · rw [c]; exact h.li s
    · rw [c]; intro e; simp at e
    · rw [c]; intro _; exact h.li s (Or.inl hp)
  · rcases RKey_cases (rst s) s.1 s.2 (sto s.1) kind with ⟨c, -⟩ | ⟨-, c, -⟩ | ⟨hp, -, c, -⟩
    · rw [c]; exact h.li3 s
    · rw [c]; intro e; simp at e
    · rw [c]; intro _; simp [rkSt]; exact h.li s (Or.inl hp)

theorem EInv_rShed {rst : Nat × Nat → RState} {sto : Nat → Store} {issued : Tk → Prop} (h : EInv rst sto issued)
    (s : Nat × Nat) : EInv (upd rst s (RShed (rst s))) sto issued := by
  apply EInv_frame h
  · unfold RShed; split <;> exact ⟨rfl, rfl, rfl, rfl, id⟩
  · unfold RShed; split
    · intro _; right; left; rfl
    · exact id
  · unfold RShed; split
    · intro e; simp at e
    · exact h.li s
  · unfold RShed; split
    · intro e; simp at e
    · exact h.li3 s

theorem EInv_expire {rst : Nat × Nat → RState} {sto : Nat → Store} {issued : Tk → Prop} (h : EInv rst sto issued)
    (n i : Nat) :
    EInv rst (upd sto n { sto n with tks := (sto n).tks.modify i (fun sl => { sl with exp := true }) }) issued := by
  have mem : ∀ m x, x ∈ (upd sto n { sto n with tks := (sto n).tks.modify i (fun sl => { sl with exp := true }) } m).tks →
      x.occ = true → ∃ y, y ∈ (sto m).tks ∧ y.occ = true ∧ y.psk = x.psk ∧ y.tid = x.tid := by
    intro m x hx ho
    by_cases e : m = n
    · subst e
      rw [upd_same] at hx
      rcases mem_modify hx with h1 | ⟨y, hy, rfl⟩
      · exact ⟨x, h1, ho, rfl, rfl⟩
      · exact ⟨y, hy, ho, rfl, rfl⟩
    · rw [upd_ne _ _ _ _ e] at hx; exact ⟨x, hx, ho, rfl, rfl⟩
  refine ⟨h.li, h.li3, h.led, ?_, ?_, h.ep, ?_, h.zr⟩
  · intro m x hx ho
    obtain ⟨y, hy, hyo, hp, -⟩ := mem m x hx ho
    rw [← hp]; exact h.sn m y hy hyo
  · intro m x hx ho
    obtain ⟨y, hy, hyo, hp, ht⟩ := mem m x hx ho
    rw [← hp, ← ht]; exact h.pf m y hy hyo
  · intro r hr x hx ho
    obtain ⟨y, hy, hyo, hp, -⟩ := mem r.1 x hx ho
    rw [← hp]; exact h.ag r hr y hy hyo

theorem EInv_step {g g' : G} (h : EInv g.rst g.sto g.issued) (hs : StoreInv g.rst g.sto g.cli g.issued)
    (hst : Step g g') : EInv g'.rst g'.sto g'.issued := by
  cases hst with
  | iStart => exact h
  | iRecv => exact h
  | iAnswer => exact h
  | iRetrans => exact h
  | iShed => exact h
  | iAccept => exact h
  | rRecv s m cs _ _ => exact EInv_rRecv h hs s m cs
  | rAnswer s kind _ _ => exact EInv_rKey h s kind
  | rRetrans => exact h
  | rShed s _ => exact EInv_rShed h s
  | expire n i sl _ _ _ _ => exact EInv_expire h n i
  | expireC => exact h
  | «export» => exact h
  | restore => exact h
  | restart => exact h

theorem EInv_reach {K C : Nat} {g : G} (hr : Reach K C g) : EInv g.rst g.sto g.issued := by
  induction hr with
  | init => exact EInv_init K C
  | step hr' hs ih => exact EInv_step ih (StoreInv_reach hr') hs

/-- A responder that raised the early keys authenticated, and holds them from a ticket that was issued
(`NoEarly` of `Handshake.tla`). -/
theorem earlyTied {K C : Nat} {g : G} (h : Reach K C g) (r : Nat × Nat) (he : (g.rst r).early ≠ nil) :
    (g.rst r).auth = true ∧ ∃ t, g.issued t ∧ t.tid = (g.rst r).tid ∧ t.psk = (g.rst r).tpsk ∧
      early (ckpsk t.psk) (g.rst r).thh = (g.rst r).early := by
  obtain ⟨-, a, b, -⟩ := (EInv_reach h).ep r he
  exact ⟨a, b⟩

/-- 0-RTT at most once per pre-shared key: no two responder sessions accepted a Hello with the same pre-shared key,
whatever ticket ids the generator returns. -/
theorem zeroRttOnce {K C : Nat} {g : G} (h : Reach K C g) (r1 r2 : Nat × Nat) (hne : r1 ≠ r2)
    (h1 : (g.rst r1).early ≠ nil) (h2 : (g.rst r2).early ≠ nil) : (g.rst r1).tpsk ≠ (g.rst r2).tpsk :=
  (EInv_reach h).zr r1 r2 hne h1 h2

/-- A ticket that was accepted is gone: no slot of the store of the accepting node holds its pre-shared key. -/
theorem acceptedGone {K C : Nat} {g : G} (h : Reach K C g) (r : Nat × Nat) (he : (g.rst r).early ≠ nil) (i : Nat)
    (sl : Slot) (hs : (g.sto r.1).tks[i]? = some sl) (ho : sl.occ = true) : sl.psk ≠ (g.rst r).tpsk :=
  (EInv_reach h).ag r he sl (List.mem_of_getElem? hs) ho

#audit_axioms Pinc.Hs.earlyTied
#audit_axioms Pinc.Hs.zeroRttOnce
#audit_axioms Pinc.Hs.acceptedGone

end Pinc.Hs
