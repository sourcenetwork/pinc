import Pinc.ReconcileRefFold

/-!
# Reconcile refinement, part 2k: the FULL arms

The responder's FULL arm (merge the initiator's items with ours, reply with the bitmap and our extras, or narrow) and the
initiator's FULL/COLD arm (merge, grow the report arenas).
-/

namespace Pinc.Reconcile

/-- The FULL arm of the responder for the ranks `a..b`. -/
def fullArm (o : Oracle) (S : List Item) (c : Core) (lo : Item) (hi : Option Item) (a b : Nat) (r : List Nat)
    (mark : Nat) : Except Err (Core × List Nat) := do
  let lim := c.lim
  let is ← lr (IS.read r)
  let cc := is.left
  if cc > aleaf then throw (.malformed .count)
  let narrow ← if b - a > aleaf then pure true else do pure !(← leafOk lim S lo hi a b true)
  if narrow then
    let r ← lr (drain lim.maxItem (is.left + 1) is)
    let (out, cnt) ← splitFit o lim S c.out lo hi a b mark 3
    pure (({ c with out := out }).bump cnt, r)
  else
    let ((seen, out, extra), r) ← merge lim S a b is respFullF ([0, 0, 0, 0], c.out, 0)
    pure (({ c with out := replyPart out lo hi cc seen extra }).bump 1, r)

/-- The FULL and COLD arm of the initiator for the ranks `a..b`. -/
def initFullArm (kind : Nat) (S : List Item) (c : Core) (lo : Item) (hi : Option Item) (a b : Nat) (r : List Nat) :
    Except Err (Core × List Nat) := do
  let lim := c.lim
  let is ← lr (IS.read r)
  let cap := lim.maxReport
  let mf ← c.msgFloor.disjoint lo hi
  let cf ← if kind = tCOLD then c.coldFloor.ascending lo hi else .ok c.coldFloor
  let ((here, there), r) ← merge lim S a b is (initFullF cap lo hi) (c.here, c.there)
  let c := { c with here := here, there := there, msgFloor := mf, coldFloor := cf }
  let c := if kind = tCOLD then { c with ans := { c.ans with cold := true, coldEnd := !hi.isSome } } else c
  pure (c, r)

theorem tailPart_full (o : Oracle) (S : List Item) (c : Core) (lo : Item) (hi : Option Item) (hinit : c.init = false)
    (hab : ¬ bOf c.n S hi < rankOf S lo) (r : List Nat) (mark : Nat) :
    tailPart o S c tFULL lo hi r mark = fullArm o S c lo hi (rankOf S lo) (bOf c.n S hi) r mark := by
  cases hi <;> simp only [bOf] at hab ⊢ <;>
  (unfold tailPart fullArm
   simp (config := {decide := true}) only [hab, hinit, tFP, tIDS, tFULL, bOf, ite_true, ite_false, Bool.not_false,
     and_true, Bool.false_eq_true, Nat.reduceEqDiff, and_false, bind, Except.bind, pure, Except.pure]
   rfl)

theorem tailPart_initFull (o : Oracle) (S : List Item) (c : Core) (kind : Nat) (lo : Item) (hi : Option Item)
    (hk : kind = tFULL ∨ kind = tCOLD) (hinit : c.init = true)
    (hab : ¬ bOf c.n S hi < rankOf S lo) (r : List Nat) (mark : Nat) :
    tailPart o S c kind lo hi r mark = initFullArm kind S c lo hi (rankOf S lo) (bOf c.n S hi) r := by
  rcases hk with rfl | rfl <;> cases hi <;> simp only [bOf] at hab ⊢ <;>
  (unfold tailPart initFullArm
   simp (config := {decide := true}) only [hab, hinit, tFP, tIDS, tFULL, tCOLD, bOf, ite_true, ite_false,
     Bool.not_true, and_true, Bool.false_eq_true, Nat.reduceEqDiff, and_false, bind, Except.bind, pure, Except.pure]
   rfl)

/-- The bitmap of the positions of `xs` that `ms` holds. -/
def bitsFull (ms xs : List Item) : List Nat := (idxOf ms xs 0).foldl setBit [0, 0, 0, 0]

theorem items_asc {lim S c} (I : Iv) (h : HCtx lim S c I) : Asc (I.items S) := by
  have := h.hS.filter' I.has
  exact this

theorem stream_of (xs : List Item) (rest : List Nat) : IS.read (putItems xs ++ rest) =
    .ok ⟨xs.length, stageBytes xs ++ rest⟩ ∨ True := Or.inr trivial

theorem read_putItems (xs : List Item) (rest : List Nat) (hl : xs.length < 2 ^ 63) :
    lr (IS.read (putItems xs ++ rest)) = .ok ⟨xs.length, stageBytes xs ++ rest⟩ := by
  unfold putItems IS.read stageBytes
  simp only [List.append_assoc, count_venc _ _ hl, lr, Except.mapError]

/-- The responder's FULL arm on an honest list that fits: the reply with the bitmap and our extra items. -/
theorem fullArm_leaf (o : Oracle) {lim S c} (I : Iv) (h : HCtx lim S c I) (hinit : c.init = false)
    (xs : List Item) (hlen : xs.length ≤ aleaf) (hx : ∀ t ∈ xs, t.length ≤ lim.maxItem ∧ t.length < 2 ^ 63)
    (hasc : Asc xs) (rest : List Nat) (mark : Nat) (hout : c.out.stage = [])
    (hcnt : cnt S I ≤ aleaf) (hfit : fitsM lim S true I) :
    fullArm o S c I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) (putItems xs ++ rest) mark =
      .ok ((({ c with out := c.out.addW (.reply I xs.length ((bitsFull (I.items S) xs).take ((xs.length + 7) / 8))
        ((I.items S).filter (fun x => !xs.contains x))) }).bump 1), rest) := by
  have hr := h.ranks
  have hc := h.cnt_eq
  have hlim := h.hlim
  subst hlim
  have haleaf : aleaf = 32 := rfl
  have hf : leafOk c.lim S I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) true = .ok true := hfit
  have hnl : ¬ (rankHi S I.hi - rankOf S I.lo > aleaf) := by omega
  have hrd := read_putItems xs rest (by rw [haleaf] at hlen; have := h.hmx; omega)
  have hm := merge_spec c.lim S h.hlen (rankOf S I.lo) (rankHi S I.hi) hr.1 hr.2.1 respFullF rest
    ([0, 0, 0, 0], c.out, 0) xs hx hasc
  rw [hr.2.2] at hm
  have hme := mergeEv_spec _ (I.items S) xs 0 (Nat.le_refl _) (items_asc I h) hasc
  unfold fullArm
  simp only [hrd, bind, Except.bind, pure, Except.pure, show ¬ (xs.length > aleaf) from by omega, ite_false, hnl, hf,
    Bool.not_true, Bool.false_eq_true, hm, respFull_fold, hme.1, hme.2.1]
  simp only [replyPart, Out.head, Out.addW, WP.enc, putItems, stageBytes, hout, List.append_nil, Nat.zero_add,
    List.append_assoc, List.nil_append, bitsFull]
  rfl

/-- A narrowed FULL part: the responder drains the list and splits its range instead of replying. -/
theorem fullArm_split (o : Oracle) {lim S c} (I : Iv) (h : HCtx lim S c I)
    (xs : List Item) (hlen : xs.length ≤ aleaf) (hx : ∀ t ∈ xs, t.length ≤ lim.maxItem ∧ t.length < 2 ^ 63)
    (rest : List Nat) (mark : Nat)
    (hout : c.out.snap = c.out.last ∧ c.out.stage = [] ∧ c.out.body.length = mark)
    (hno : ¬ (cnt S I ≤ aleaf ∧ fitsM lim S true I)) :
    ∃ fan, 2 ≤ fan ∧ fan ≤ 16 ∧
      fullArm o S c I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) (putItems xs ++ rest) mark =
        .ok ((({ c with out :=
            { c.out with
              body := c.out.body ++ (encFps c.out.last ((splitIvs S I fan).zip
                ((blocksOf S I fan).map fun B => fpBytes (o.enc (sumH B) B.length)))).1,
              last := (encFps c.out.last ((splitIvs S I fan).zip
                ((blocksOf S I fan).map fun B => fpBytes (o.enc (sumH B) B.length)))).2 } }).bump (blocksOf S I fan).length),
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
  have hrd := read_putItems xs rest (by rw [haleaf] at hlen; have := h.hmx; omega)
  have hdr := drain_stream c.lim.maxItem rest xs (xs.length + 1) hx (by omega)
  unfold fullArm
  simp only [hrd, bind, Except.bind, pure, Except.pure, show ¬ (xs.length > aleaf) from by omega, ite_false]
  by_cases hbig : rankHi S I.hi - rankOf S I.lo > aleaf
  · simp only [hbig, ite_true, hdr, lr, Except.mapError, he, hrb, hsp]
  · have hvf : v = false := by
      cases v
      · rfl
      · exact absurd ⟨by omega, hv⟩ hno
    subst hvf
    simp only [hbig, ite_false, hv, Bool.not_false, ite_true, hdr, lr, Except.mapError, he, hrb, hsp, bind,
      Except.bind, pure, Except.pure]

/-- The initiator's FULL and COLD arm on an honest list of the part's range whose range the floors take: the peer's items
we lack go to `here`, ours it lacks to `there` (the arenas must have room). -/
theorem initFullArm_spec {lim S c} (I : Iv) (h : HCtx lim S c I) (kind : Nat)
    (xs : List Item) (hxl : xs.length < 2 ^ 63) (hx : ∀ t ∈ xs, t.length ≤ lim.maxItem ∧ t.length < 2 ^ 63)
    (hasc : Asc xs) (hin : ∀ t ∈ xs, within t I.lo I.hi = true) (rest : List Nat)
    (mf cf : Floor) (hmf : c.msgFloor.disjoint I.lo I.hi = .ok mf)
    (hcf : (if kind = tCOLD then c.coldFloor.ascending I.lo I.hi else .ok c.coldFloor) = .ok cf)
    (hroom : dataLen c.here + dataLen c.there + dataLen (xs.filter (fun x => !(I.items S).contains x))
      + dataLen ((I.items S).filter (fun x => !xs.contains x)) + varMax ≤ lim.maxReport) :
    initFullArm kind S c I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) (putItems xs ++ rest) =
      .ok ((if kind = tCOLD then
          { c with here := c.here ++ xs.filter (fun x => !(I.items S).contains x),
                   there := c.there ++ (I.items S).filter (fun x => !xs.contains x), msgFloor := mf, coldFloor := cf,
                   ans := { c.ans with cold := true, coldEnd := !I.hi.isSome } }
        else
          { c with here := c.here ++ xs.filter (fun x => !(I.items S).contains x),
                   there := c.there ++ (I.items S).filter (fun x => !xs.contains x), msgFloor := mf,
                   coldFloor := cf }), rest) := by
  have hr := h.ranks
  have hlim := h.hlim
  subst hlim
  have hrd := read_putItems xs rest hxl
  have hm := merge_spec c.lim S h.hlen (rankOf S I.lo) (rankHi S I.hi) hr.1 hr.2.1 (initFullF c.lim.maxReport I.lo I.hi) rest
    (c.here, c.there) xs hx hasc
  rw [hr.2.2] at hm
  have hme := mergeEv_spec _ (I.items S) xs 0 (Nat.le_refl _) (items_asc I h) hasc
  have hf := initFull_fold c.lim.maxReport I.lo I.hi (mergeEv (I.items S) xs 0) (c.here, c.there)
    (by rw [hme.2.2]; intro t ht; exact hin t (List.mem_filter.mp ht).1)
    (by rw [hme.2.2, hme.2.1]; simp only []; omega)
  unfold initFullArm
  simp only [hrd, bind, Except.bind, pure, Except.pure, hmf, hm, hf, hme.2.2, hme.2.1, Except.map]
  by_cases hk : kind = tCOLD
  · simp only [if_pos hk] at hcf ⊢; simp only [hcf]
  · simp only [if_neg hk] at hcf ⊢; cases hcf; rfl

end Pinc.Reconcile