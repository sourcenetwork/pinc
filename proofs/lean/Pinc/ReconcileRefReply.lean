import Pinc.ReconcileRefFull

/-!
# Reconcile refinement, part 2l: the REPLY arm of the initiator

The reply to an ids or items part is a bitmap of the initiator's items the responder holds and the responder's extra items.
The initiator puts its items with a clear bit into `there` and the extras into `here`.
-/

namespace Pinc.Reconcile

/-- The initiator's items (from position `j`) whose bit in the bitmap is clear. -/
def unseenList (seen : List Nat) : List Item → Nat → List Item
  | [], _ => []
  | x :: xs, j => if bitAt seen j then unseenList seen xs (j + 1) else x :: unseenList seen xs (j + 1)

theorem unseen_set (lim : Limits) (S : List Item) (a : Nat) (seen : List Nat) (cc : Nat) (here : List Item) (f : Nat)
    (there : List Item) (hb : bitAt seen (cc - (f + 1)) = true) :
    unseen lim S a seen cc here (f + 1) there = unseen lim S a seen cc here f there := by
  rw [unseen]
  exact if_pos hb

theorem unseen_clear (lim : Limits) (S : List Item) (a : Nat) (seen : List Nat) (cc : Nat) (here : List Item) (f : Nat)
    (there : List Item) (hb : bitAt seen (cc - (f + 1)) = false) :
    unseen lim S a seen cc here (f + 1) there =
      (do let x ← readItem lim S (a + (cc - (f + 1)))
          unseen lim S a seen cc here f (← pushItem there (dataLen here) lim.maxReport x)) := by
  rw [unseen]
  exact if_neg (fun h => by have h' : bitAt seen (cc - (f + 1)) = true := h; rw [hb] at h'; exact absurd h' (by decide))

theorem unseen_spec (lim : Limits) (S : List Item) (hlen : ∀ x ∈ S, x.length ≤ lim.maxItem) (a : Nat)
    (seen : List Nat) (cc : Nat) (here : List Item) (hc : a + cc ≤ S.length) :
    ∀ (f : Nat) (there : List Item), f ≤ cc →
      dataLen here + dataLen there + dataLen (unseenList seen ((S.drop (a + (cc - f))).take f) (cc - f)) + varMax
        ≤ lim.maxReport →
      unseen lim S a seen cc here f there =
        .ok (there ++ unseenList seen ((S.drop (a + (cc - f))).take f) (cc - f))
  | 0, there, _, _ => by simp [unseen, unseenList]
  | f + 1, there, hf, hroom => by
    have hjs : a + (cc - (f + 1)) < S.length := by omega
    have hsl : (S.drop (a + (cc - (f + 1)))).take (f + 1) =
        S[a + (cc - (f + 1))] :: (S.drop (a + (cc - f))).take f := by
      rw [List.drop_eq_getElem_cons hjs, List.take_succ_cons, show a + (cc - (f + 1)) + 1 = a + (cc - f) by omega]
    have hj1 : cc - (f + 1) + 1 = cc - f := by omega
    rw [hsl] at hroom ⊢
    by_cases hb : bitAt seen (cc - (f + 1)) = true
    · rw [unseen_set lim S a seen cc here f there hb]
      simp only [unseenList, hb, ite_true] at hroom ⊢
      rw [hj1]; rw [hj1] at hroom
      exact unseen_spec lim S hlen a seen cc here hc f there (by omega) hroom
    · have hb' : bitAt seen (cc - (f + 1)) = false := by simpa using hb
      rw [unseen_clear lim S a seen cc here f there hb']
      simp only [unseenList, hb', Bool.false_eq_true, ite_false, dataLen_cons] at hroom ⊢
      have hp := venc_len_pos (S[a + (cc - (f + 1))]).length
      have hx := hlen _ (List.getElem_mem (h := hjs))
      have hok : ¬ (dataLen there + dataLen here + (S[a + (cc - (f + 1))]).length + varMax > lim.maxReport) := by omega
      simp only [readItem_ok lim S hlen _ hjs, bind, Except.bind, pushItem, hok, ite_false, pure, Except.pure]
      rw [hj1]
      rw [hj1] at hroom
      have := unseen_spec lim S hlen a seen cc here hc f (there ++ [S[a + (cc - (f + 1))]]) (by omega)
        (by simp only [dataLen_append, dataLen_cons, dataLen_nil]; omega)
      rw [this]
      simp [List.append_assoc]

/-- Every extra passes its check (`extraOk`) after the one before it. -/
def extrasOk (lim : Limits) (S : List Item) (lo : Item) (hi : Option Item) (b : Nat) : Option Item → List Item → Prop
  | _, [] => True
  | p, x :: E => extraOk lim S lo hi b p x = .ok () ∧ extrasOk lim S lo hi b (some x) E

theorem pushExtras_spec (lim : Limits) (S : List Item) (lo : Item) (hi : Option Item) (b : Nat) (there : List Item) :
    ∀ (E : List Item) (fuel : Nat) (prev : Option Item) (here : List Item) (rest : List Nat),
      (∀ t ∈ E, t.length ≤ lim.maxItem ∧ t.length < 2 ^ 63) → E.length < fuel → extrasOk lim S lo hi b prev E →
      dataLen here + dataLen there + dataLen E + varMax ≤ lim.maxReport →
      pushExtras lim S lo hi b there fuel ⟨E.length, stageBytes E ++ rest⟩ prev here = .ok (here ++ E, rest)
  | [], fuel, _, here, rest, _, hf, _, _ => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp [pushExtras, lr, Except.mapError, bind, Except.bind, pure, Except.pure, stageBytes]
    rfl
  | x :: E, fuel, prev, here, rest, hE, hf, hok', hroom => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hn := next_cons' lim.maxItem x E rest hE
    have hp := venc_len_pos x.length
    simp only [dataLen_cons] at hroom
    have hok : ¬ (dataLen here + dataLen there + x.length + varMax > lim.maxReport) := by omega
    simp only [pushExtras, hn, lr, Except.mapError, bind, Except.bind, pure, Except.pure, pushItem, hok, ite_false,
      hok'.1]
    have := pushExtras_spec lim S lo hi b there E f (some x) (here ++ [x]) rest
      (fun y hy => hE y (List.mem_cons_of_mem _ hy)) (by simp at hf; omega) hok'.2
      (by simp only [dataLen_append, dataLen_cons, dataLen_nil]; omega)
    rw [this]; simp [List.append_assoc]

theorem isread_putItems (xs : List Item) (rest : List Nat) (hl : xs.length < 2 ^ 63) :
    IS.read (putItems xs ++ rest) = .ok ⟨xs.length, stageBytes xs ++ rest⟩ := by
  unfold putItems IS.read stageBytes
  simp only [List.append_assoc, count_venc _ _ hl]

/-- The REPLY arm of the initiator for the part `lo..hi` of the ranks `a..b`. -/
def replyArm (S : List Item) (c : Core) (lo : Item) (hi : Option Item) (a b : Nat) (r : List Nat) :
    Except Err (Core × List Nat) := do
  let lim := c.lim
  let (cc, r) ← lr (count r)
  if cc != b - a ∨ cc > aleaf then throw (.malformed .count)
  let mf ← c.msgFloor.disjoint lo hi
  let (seen, r) ← lr (readBytes ((cc + 7) / 8) r)
  if (cc % 8 != 0) && (match seen.getLast? with | some byte => byte >>> (cc % 8) != 0 | none => false) then
    throw (.malformed .count)
  let there ← unseen lim S a seen cc c.here cc c.there
  let is ← lr (IS.read r)
  let (here, r) ← pushExtras lim S lo hi b there (is.left + 1) is none c.here
  pure ({ c with here := here, there := there, msgFloor := mf }, r)

theorem tailPart_reply (o : Oracle) (S : List Item) (c : Core) (lo : Item) (hi : Option Item) (hinit : c.init = true)
    (hab : ¬ bOf c.n S hi < rankOf S lo) (r : List Nat) (mark : Nat) :
    tailPart o S c tREPLY lo hi r mark = replyArm S c lo hi (rankOf S lo) (bOf c.n S hi) r := by
  cases hi <;> simp only [bOf] at hab ⊢ <;>
  (unfold tailPart replyArm
   simp (config := {decide := true}) only [hab, hinit, tFP, tIDS, tFULL, tCOLD, tREPLY, bOf, ite_true, ite_false,
     Bool.not_true, and_true, Bool.false_eq_true, Nat.reduceEqDiff, and_false, bind, Except.bind, pure, Except.pure]
   rfl)

/-- The REPLY arm on an honest reply whose range the floor takes and whose extras pass their checks: our items with a
clear bit go to `there`, the extras to `here`. -/
theorem replyArm_spec {lim S c} (I : Iv) (h : HCtx lim S c I) (cc : Nat) (hcc : cc = cnt S I) (hle : cc ≤ aleaf)
    (seen : List Nat) (hseen : seen.length = (cc + 7) / 8)
    (hpad : ((cc % 8 != 0) && (match seen.getLast? with | some byte => byte >>> (cc % 8) != 0 | none => false)) = false)
    (extras : List Item) (hxl : extras.length < 2 ^ 63)
    (hx : ∀ t ∈ extras, t.length ≤ lim.maxItem ∧ t.length < 2 ^ 63)
    (hex : extrasOk lim S I.lo I.hi (rankHi S I.hi) none extras) (mf : Floor) (hmf : c.msgFloor.disjoint I.lo I.hi = .ok mf)
    (rest : List Nat)
    (hroom : dataLen c.here + dataLen c.there + dataLen (unseenList seen (I.items S) 0) + dataLen extras + varMax
      ≤ lim.maxReport) :
    replyArm S c I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) (venc cc ++ (seen ++ (putItems extras ++ rest))) =
      .ok ({ c with here := c.here ++ extras, there := c.there ++ unseenList seen (I.items S) 0, msgFloor := mf },
        rest) := by
  have hr := h.ranks
  have hc := h.cnt_eq
  have hlim := h.hlim
  subst hlim
  have haleaf : aleaf = 32 := rfl
  have hcn : count (venc cc ++ (seen ++ (putItems extras ++ rest))) = .ok (cc, seen ++ (putItems extras ++ rest)) :=
    count_venc _ _ (by rw [haleaf] at hle; omega)
  have hcb : cc = rankHi S I.hi - rankOf S I.lo := by rw [hcc]; exact hc
  have hrb : readBytes ((cc + 7) / 8) (seen ++ (putItems extras ++ rest)) = .ok (seen, putItems extras ++ rest) := by
    rw [readBytes_ok _ _ (by simp [hseen]), ← hseen]; simp
  have e : (S.drop (rankOf S I.lo + (cc - cc))).take cc = I.items S := by
    rw [Nat.sub_self, Nat.add_zero, ← hr.2.2, ← hcb]
  have hroom1 : dataLen c.here + dataLen c.there +
      dataLen (unseenList seen ((S.drop (rankOf S I.lo + (cc - cc))).take cc) (cc - cc)) + varMax ≤ c.lim.maxReport := by
    rw [e, Nat.sub_self]; omega
  have hun := unseen_spec c.lim S h.hlen (rankOf S I.lo) seen cc c.here (by omega) cc c.there (Nat.le_refl _) hroom1
  rw [e, Nat.sub_self] at hun
  have hrd := isread_putItems extras rest hxl
  have hpe := pushExtras_spec c.lim S I.lo I.hi (rankHi S I.hi) (c.there ++ unseenList seen (I.items S) 0) extras
    (extras.length + 1) none c.here rest hx (by omega) hex (by simp only [dataLen_append]; omega)
  unfold replyArm
  simp only [lr, hcn, Except.mapError, bind, Except.bind, pure, Except.pure, show ¬ (cc != rankHi S I.hi - rankOf S I.lo ∨ cc > aleaf) from by
      simp [hcb] at *; omega, ite_false, hmf, hrb, hpad, Bool.false_eq_true, hun, hrd, hpe]

end Pinc.Reconcile