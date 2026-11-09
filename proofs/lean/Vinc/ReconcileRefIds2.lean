import Vinc.ReconcileRefBits

/-!
# Reconcile refinement, part 2g: the IDS arm of the responder on an honest ids list

The IDS arm on an honest ids list: `idsArm_leaf` (the reply part with the rposition bitmap and the extra items) and
`idsArm_split` (narrowing: the range is split instead).
-/

namespace Vinc.Reconcile

/-- The fingerprints and ids are the 128-bit and 64-bit values the wire carries. -/
def HBound (o : Oracle) : Prop := (∀ x, o.H x < 2 ^ 128) ∧ (∀ x, o.idf x < 2 ^ 64)

/-- The bitmap after matching each of our items to its position among the initiator's ids. -/
def bmFold (o : Oracle) (is : List Nat) (xs : List Item) (seen : List Nat) : List Nat :=
  xs.foldl (fun seen x => match rposN is (o.idf x) with | some k => setBit seen k | none => seen) seen

/-- Our items whose id is not among the initiator's. -/
def extrasOf (o : Oracle) (is : List Nat) (xs : List Item) : List Item := xs.filter fun x => (rposN is (o.idf x)).isNone

def stageBytes (xs : List Item) : List Nat := (xs.map fun x => venc x.length ++ x).flatten

theorem foldl_congr {α β : Type} (f g : β → α → β) (h : ∀ st x, f st x = g st x) (init : β) (xs : List α) :
    xs.foldl f init = xs.foldl g init := by
  have : f = g := funext fun st => funext fun x => h st x
  rw [this]

theorem idsFold_spec (o : Oracle) (is : List Nat) (hids : ∀ x ∈ is, x < 2 ^ 64) (hid : ∀ x, o.idf x < 2 ^ 64) :
    ∀ (xs : List Item) (seen : List Nat) (out : Out) (e : Nat),
      xs.foldl (idStep o (is.map (beBytes idLen))) (seen, out, e)
      = (bmFold o is xs seen, { out with stage := out.stage ++ stageBytes (extrasOf o is xs) },
         e + (extrasOf o is xs).length)
  | [], seen, out, e => by simp [bmFold, extrasOf, stageBytes]
  | x :: xs, seen, out, e => by
    have hx : rpos (is.map (beBytes idLen)) (idBytes o x) = rposN is (o.idf x) :=
      rpos_map_beBytes is (o.idf x) hids (hid x)
    cases hr : rposN is (o.idf x) with
    | some k =>
      simp only [List.foldl_cons, idStep, hx, hr]
      rw [idsFold_spec o is hids hid xs]
      simp [bmFold, extrasOf, hr]
    | none =>
      simp only [List.foldl_cons, idStep, hx, hr]
      rw [idsFold_spec o is hids hid xs]
      simp [bmFold, extrasOf, hr, stageBytes, Out.stageItem, List.append_assoc]
      omega

theorem chunks_flatten : ∀ (is : List Nat),
    chunks idLen is.length ((is.map (beBytes idLen)).flatten) = is.map (beBytes idLen)
  | [] => by simp [chunks]
  | v :: is => by
    have hl := length_beBytes idLen v
    have ih := chunks_flatten is
    have e : ((v :: is).map (beBytes idLen)).flatten = beBytes idLen v ++ (is.map (beBytes idLen)).flatten := by simp
    simp only [List.length_cons, e, chunks]
    have hne : (beBytes idLen v ++ (is.map (beBytes idLen)).flatten) ≠ [] := by
      intro h; have h2 := congrArg List.length h
      simp only [List.length_append, List.length_nil, hl] at h2; simp [idLen] at h2
    rw [if_neg hne, List.take_left' hl, List.drop_left' hl, ih]
    simp

theorem readBytes_flat (is : List Nat) (rest : List Nat) :
    readBytes (is.length * idLen) ((is.map (beBytes idLen)).flatten ++ rest) = .ok ((is.map (beBytes idLen)).flatten, rest) := by
  have hl : ((is.map (beBytes idLen)).flatten).length = is.length * idLen := by
    induction is with
    | nil => simp
    | cons v is ih => simp [length_beBytes, ih, Nat.add_mul, Nat.add_comm]
  rw [readBytes_ok _ _ (by simp [hl]), ← hl]
  simp

/-- The ids leaf of the responder on an honest ids list: the reply part, with the bitmap and the extras. -/
theorem idsArm_leaf (o : Oracle) (hb : HBound o) {lim S c} (I : Iv) (h : HCtx lim S c I) (hinit : c.init = false)
    (is : List Nat) (hlen : is.length ≤ aleaf) (hids : ∀ x ∈ is, x < 2 ^ 64) (rest : List Nat) (mark : Nat)
    (hout : c.out.stage = []) (hcnt : cnt S I ≤ aleaf) (hfit : fitsM lim S true I) :
    idsArm o S c I.lo I.hi (rankOf S I.lo) (rankHi S I.hi)
        (venc is.length ++ ((is.map (beBytes idLen)).flatten ++ rest)) mark =
      .ok ((({ c with out := c.out.addW (.reply I is.length ((bmFold o is (I.items S) [0, 0, 0, 0]).take ((is.length + 7) / 8))
        (extrasOf o is (I.items S))) }).bump 1), rest) := by
  have hr := h.ranks
  have hc := h.cnt_eq
  have hlim := h.hlim
  subst hlim
  have hf : leafOk c.lim S I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) true = .ok true := hfit
  have haleaf : aleaf = 32 := rfl
  have hcn : count (venc is.length ++ ((is.map (beBytes idLen)).flatten ++ rest)) = .ok (is.length, (is.map (beBytes idLen)).flatten ++ rest) :=
    count_venc _ _ (by rw [haleaf] at hlen; omega)
  have hnl : ¬ (rankHi S I.hi - rankOf S I.lo > aleaf) := by omega
  unfold idsArm
  simp only [lr, hcn, Except.mapError, bind, Except.bind, pure, Except.pure, show ¬ (is.length > aleaf) from by omega,
    ite_false, readBytes_flat, hnl, hf, Bool.not_true, Bool.false_eq_true,
    readRange_spec c.lim S h.hlen (rankHi S I.hi - rankOf S I.lo) (rankOf S I.lo) (by omega), hr.2.2, chunks_flatten,
    ]
  rw [idsFold_spec o is hids hb.2 (I.items S) [0, 0, 0, 0] c.out 0]
  simp only [replyPart, Out.head, Out.addW, WP.enc, putItems, stageBytes, hout, List.append_nil, Nat.zero_add,
    List.append_assoc, List.nil_append]

/-- A narrowed ids part: the responder splits its range instead of replying. -/
theorem idsArm_split (o : Oracle) {lim S c} (I : Iv) (h : HCtx lim S c I)
    (is : List Nat) (hlen : is.length ≤ aleaf) (rest : List Nat) (mark : Nat)
    (hout : c.out.snap = c.out.last ∧ c.out.stage = [] ∧ c.out.body.length = mark)
    (hno : ¬ (cnt S I ≤ aleaf ∧ fitsM lim S true I)) :
    ∃ fan, 2 ≤ fan ∧ fan ≤ 16 ∧
      idsArm o S c I.lo I.hi (rankOf S I.lo) (rankHi S I.hi)
          (venc is.length ++ ((is.map (beBytes idLen)).flatten ++ rest)) mark =
        .ok ((({ c with out :=
            { c.out with
              body := c.out.body ++ (encFps c.out.last ((splitIvs S I fan).zip
                ((blocksOf S I fan).map fun B => fpBytes (xorH o B)))).1,
              last := (encFps c.out.last ((splitIvs S I fan).zip
                ((blocksOf S I fan).map fun B => fpBytes (xorH o B)))).2 } }).bump (blocksOf S I fan).length),
          rest) := by
  have hr := h.ranks
  have hc := h.cnt_eq
  have hlim := h.hlim
  subst hlim
  have haleaf : aleaf = 32 := rfl
  obtain ⟨fan, o2, ho, h1, h2, he⟩ := splitFit_spec o c.lim S I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) mark 3 c.out
  have hrb : c.out.rollback mark = c.out := by
    obtain ⟨hs, hst, hl⟩ := hout
    rcases hco : c.out with ⟨b, st, l, sn⟩
    rw [hco] at hs hst hl
    simp only at hs hst hl
    subst hs hst
    simp [Out.rollback, ← hl]
  have ho2 : o2 = c.out := by
    rcases ho with rfl | rfl
    · rfl
    · exact hrb
  subst ho2
  refine ⟨fan, h1, h2, ?_⟩
  obtain ⟨v, hv⟩ := leafOk_total c.lim S h.hlen I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) true hr.2.1
  have hsp := splitParts_spec o c.lim S h.hS h.hlen I c.out fan (by omega) hr.1 hr.2.1
  have hcn : count (venc is.length ++ ((is.map (beBytes idLen)).flatten ++ rest)) = .ok (is.length, (is.map (beBytes idLen)).flatten ++ rest) :=
    count_venc _ _ (by rw [haleaf] at hlen; omega)
  unfold idsArm
  simp only [lr, hcn, Except.mapError, bind, Except.bind, pure, Except.pure, show ¬ (is.length > aleaf) from by omega,
    ite_false, readBytes_flat]
  by_cases hbig : rankHi S I.hi - rankOf S I.lo > aleaf
  · simp only [hbig, ite_true, he, hrb, hsp]
  · have hvf : v = false := by
      cases v
      · rfl
      · exact absurd ⟨by omega, hv⟩ hno
    subst hvf
    simp only [hbig, ite_false, hv, Bool.not_false, ite_true, bind, Except.bind, pure, Except.pure, he, hrb, hsp]

end Vinc.Reconcile