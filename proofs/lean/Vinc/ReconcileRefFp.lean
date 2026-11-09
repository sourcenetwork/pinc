import Vinc.ReconcileRefArms

/-!
# Reconcile refinement, part 2c: the FP arm

The FP arm. `tailPart_fp` splits the arm on the fingerprint comparison; `tailPart_fp_equal` (fingerprints agree, nothing is
written), `fpDiffer_full` (a leaf of items fits: a FULL part), `fpDiffer_ids` (the initiator's ids leaf) and `fpDiffer_split`
(otherwise the range is split at some fan 2 to 16, writing exactly the parts of `splitIvs`, by `splitFit_spec` and
`splitParts_spec`) are the four outcomes, each on the bytes of an honest FP part.
-/

namespace Vinc.Reconcile

theorem readRange_spec (lim : Limits) (S : List Item) (hlen : ∀ x ∈ S, x.length ≤ lim.maxItem) :
    ∀ (k a : Nat), a + k ≤ S.length → readRange lim S a k = .ok ((S.drop a).take k)
  | 0, a, _ => by simp [readRange]
  | k + 1, a, h => by
    have ha : a < S.length := by omega
    rw [readRange, readItem_ok lim S hlen a ha, readRange_spec lim S hlen k (a + 1) (by omega)]
    simp only [Except.ok.injEq]
    rw [List.drop_eq_getElem_cons ha, List.take_succ_cons]

theorem itemsPart_spec (lim : Limits) (S : List Item) (hlen : ∀ x ∈ S, x.length ≤ lim.maxItem) (out : Out)
    (kind : Nat) (lo : Item) (hi : Option Item) (a b : Nat) (hab : a ≤ b) (hb : b ≤ S.length) :
    itemsPart lim S out kind lo hi a b = .ok
      (out.head kind lo hi |> fun h => { h with body := h.body ++ putItems ((S.drop a).take (b - a)) }) := by
  unfold itemsPart
  rw [readRange_spec lim S hlen (b - a) a (by omega)]
  have hl : ((S.drop a).take (b - a)).length = b - a := by simp only [List.length_take, List.length_drop]; omega
  simp [putItems, hl]

theorem idsPart_spec (o : Oracle) (lim : Limits) (S : List Item) (hlen : ∀ x ∈ S, x.length ≤ lim.maxItem) (out : Out)
    (lo : Item) (hi : Option Item) (a b : Nat) (hab : a ≤ b) (hb : b ≤ S.length) :
    idsPart o lim S out lo hi a b = .ok
      (out.head tIDS lo hi |> fun h => { h with body := h.body ++ venc ((((S.drop a).take (b - a)).map o.idf).length)
        ++ ((((S.drop a).take (b - a)).map o.idf).map (beBytes idLen)).flatten }) := by
  unfold idsPart
  rw [readRange_spec lim S hlen (b - a) a (by omega)]
  have hl : ((S.drop a).take (b - a)).length = b - a := by simp only [List.length_take, List.length_drop]; omega
  generalize (S.drop a).take (b - a) = xs at hl ⊢
  have e : xs.map (idBytes o) = (xs.map o.idf).map (beBytes idLen) := by
    simp [List.map_map, Function.comp_def, idBytes]
  simp [e, hl]


theorem fpBytes_len (f : Nat) : (fpBytes f).length = fpLen := length_beBytes _ _

theorem readBytes_fp (f : Nat) (rest : List Nat) : readBytes fpLen (fpBytes f ++ rest) = .ok (fpBytes f, rest) := by
  rw [readBytes_ok _ _ (by simp [fpBytes_len]), ← fpBytes_len f]
  simp

theorem fromBE_fpBytes (f : Nat) (h : f < 2 ^ 128) : fromBE (fpBytes f) = f :=
  fromBE_beBytes fpLen f (by simpa [fpLen] using (by omega : f < 2 ^ 128 ∧ 256 ^ 16 = 2 ^ 128).1)

theorem fpRange_slice (o : Oracle) {lim S c I} (h : HCtx lim S c I) :
    fpRange o S (rankOf S I.lo) (rankHi S I.hi) = xorH o (I.items S) := by
  unfold fpRange; rw [h.ranks.2.2]

theorem tailPart_fp_equal (o : Oracle) {lim S c} (I : Iv) (h : HCtx lim S c I) (f : Nat) (hf : f < 2 ^ 128)
    (rest : List Nat) (mark : Nat) (heq : xorH o (I.items S) = f) :
    tailPart o S c tFP I.lo I.hi (fpBytes f ++ rest) mark = .ok (c, rest) := by
  have hr := h.ranks
  have hs := fpRange_slice o h
  have hn := h.hn
  obtain ⟨lo, hi⟩ := I
  cases hi with
  | none =>
    simp only [rankHi] at hr hs
    have hab : ¬ S.length < rankOf S lo := by omega
    simp only [tailPart, hn, lr, readBytes_fp, fromBE_fpBytes f hf, hs, heq, hab, Except.mapError, bne_self_eq_false,
      Bool.false_eq_true, ite_false, ite_true, bind, Except.bind, pure, Except.pure]
  | some x =>
    simp only [rankHi] at hr hs
    have hab : ¬ rankOf S x < rankOf S lo := by omega
    simp only [tailPart, hn, lr, readBytes_fp, fromBE_fpBytes f hf, hs, heq, hab, Except.mapError, bne_self_eq_false,
      Bool.false_eq_true, ite_false, ite_true, bind, Except.bind, pure, Except.pure]

/-- The branch of the FP arm taken when the fingerprints differ, for the ranks `a..b`. -/
def fpDiffer (o : Oracle) (S : List Item) (c : Core) (lo : Item) (hi : Option Item) (a b : Nat) (r : List Nat)
    (mark : Nat) : Except Err (Core × List Nat) := do
  let lim := c.lim
  let items := !c.init || c.exact
  let leaf := if c.init then aleaf else bleaf
  let ok ← if b - a ≤ leaf then leafOk lim S lo hi a b items else pure false
  if ok then
    let c := if c.init then { c with leafed := true } else c
    let out ← if items then itemsPart lim S c.out tFULL lo hi a b else idsPart o lim S c.out lo hi a b
    pure (({ c with out := out }).bump 1, r)
  else
    let (out, cnt) ← splitFit o lim S c.out lo hi a b mark 3
    pure (({ c with out := out }).bump cnt, r)

theorem tailPart_fp (o : Oracle) {lim S c} (I : Iv) (h : HCtx lim S c I) (f : Nat) (hf : f < 2 ^ 128)
    (rest : List Nat) (mark : Nat) :
    tailPart o S c tFP I.lo I.hi (fpBytes f ++ rest) mark =
      if f = xorH o (I.items S) then .ok (c, rest)
      else fpDiffer o S c I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) rest mark := by
  have hr := h.ranks
  have hs := fpRange_slice o h
  have hn := h.hn
  obtain ⟨lo, hi⟩ := I
  cases hi with
  | none =>
    simp only [rankHi] at hr hs ⊢
    have hab : ¬ S.length < rankOf S lo := by omega
    by_cases he : f = xorH o (Iv.items S ⟨lo, none⟩)
    · simp only [tailPart, hn, lr, readBytes_fp, fromBE_fpBytes f hf, hs, ← he, hab, Except.mapError, bne_self_eq_false,
        Bool.false_eq_true, ite_false, ite_true, bind, Except.bind, pure, Except.pure, if_pos]
    · have hne : (f != xorH o (Iv.items S ⟨lo, none⟩)) = true := by simpa using he
      simp only [tailPart, hn, lr, readBytes_fp, fromBE_fpBytes f hf, hs, hne, hab, Except.mapError, ite_true,
        Bool.false_eq_true, ite_false, bind, Except.bind, pure, Except.pure, if_neg he, fpDiffer]
  | some x =>
    simp only [rankHi] at hr hs ⊢
    have hab : ¬ rankOf S x < rankOf S lo := by omega
    by_cases he : f = xorH o (Iv.items S ⟨lo, some x⟩)
    · simp only [tailPart, hn, lr, readBytes_fp, fromBE_fpBytes f hf, hs, ← he, hab, Except.mapError, bne_self_eq_false,
        Bool.false_eq_true, ite_false, ite_true, bind, Except.bind, pure, Except.pure, if_pos]
    · have hne : (f != xorH o (Iv.items S ⟨lo, some x⟩)) = true := by simpa using he
      simp only [tailPart, hn, lr, readBytes_fp, fromBE_fpBytes f hf, hs, hne, hab, Except.mapError, ite_true,
        Bool.false_eq_true, ite_false, bind, Except.bind, pure, Except.pure, if_neg he, fpDiffer]

theorem Out.rollback_idem (out : Out) (mark : Nat) : (out.rollback mark).rollback mark = out.rollback mark := by
  simp [Out.rollback, List.take_take]

/-- `split_fit` is `split` at one of the fans 16, 8, 4, 2, on the reply as it was or rolled back to the mark. -/
theorem splitFit_spec (o : Oracle) (lim : Limits) (S : List Item) (lo : Item) (hi : Option Item) (a b mark : Nat) :
    ∀ (k : Nat) (out : Out), ∃ fan o2, (o2 = out ∨ o2 = out.rollback mark) ∧ 2 ≤ fan ∧ fan ≤ 16 ∧
      splitFit o lim S out lo hi a b mark k = splitParts o lim S o2 lo hi a b fan
  | 0, out => ⟨2, out, Or.inl rfl, Nat.le_refl _, by decide, rfl⟩
  | k + 1, out => by
    have hfan : 2 ≤ spl / 2 ^ (2 - k) ∧ spl / 2 ^ (2 - k) ≤ 16 := by
      have : k = 0 ∨ k = 1 ∨ k ≥ 2 := by omega
      rcases this with rfl | rfl | hk
      · simp [spl]
      · simp [spl]
      · have : 2 - k = 0 := by omega
        simp [this, spl]
    cases hsp : splitParts o lim S out lo hi a b (spl / 2 ^ (2 - k)) with
    | error e => exact ⟨_, out, Or.inl rfl, hfan.1, hfan.2, by simp [splitFit, hsp]⟩
    | ok q =>
      obtain ⟨out', cnt⟩ := q
      by_cases hc : out'.body.length ≤ lim.cap ∨ mark > 0 ∨ spl / 2 ^ (2 - k) ≤ 2
      · exact ⟨_, out, Or.inl rfl, hfan.1, hfan.2, by simp [splitFit, hsp, hc]⟩
      · obtain ⟨fan, o2, ho, h1, h2, he⟩ := splitFit_spec o lim S lo hi a b mark k (out.rollback mark)
        refine ⟨fan, o2, ?_, h1, h2, ?_⟩
        · rcases ho with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inr (Out.rollback_idem _ _)
        · simp only [splitFit, hsp, hc, not_false_eq_true, ite_false]
          exact he

theorem HCtx.cnt_eq {lim S c I} (h : HCtx lim S c I) : cnt S I = rankHi S I.hi - rankOf S I.lo := by
  have hr := h.ranks
  unfold cnt; rw [← hr.2.2]; simp only [List.length_take, List.length_drop]; omega

/-- The core after the leaf flag of the initiator is set. -/
def leafUpd (c : Core) : Core := if c.init then { c with leafed := true } else c

theorem Out.head_addW_full (out : Out) (I : Iv) (xs : List Item) (kind : Nat) (hk : kind = tFULL) :
    (out.head kind I.lo I.hi |> fun h => { h with body := h.body ++ putItems xs }) = out.addW (.full I xs) := by
  subst hk; simp [Out.head, Out.addW, WP.enc, List.append_assoc]

theorem Out.head_addW_ids (out : Out) (I : Iv) (is : List Nat) :
    (out.head tIDS I.lo I.hi |> fun h => { h with body := h.body ++ venc is.length ++ (is.map (beBytes idLen)).flatten })
      = out.addW (.ids I is) := by
  simp [Out.head, Out.addW, WP.enc, List.append_assoc]

/-- A leaf of items (the responder, or the initiator in the exact pass) that fits is written as a FULL part. -/
theorem fpDiffer_full (o : Oracle) {lim S c} (I : Iv) (h : HCtx lim S c I) (rest : List Nat) (mark : Nat)
    (hitems : (!c.init || c.exact) = true) (hcnt : cnt S I ≤ (if c.init then aleaf else bleaf))
    (hfit : fitsM lim S true I) :
    fpDiffer o S c I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) rest mark =
      .ok ((({ leafUpd c with out := (leafUpd c).out.addW (.full I (I.items S)) }).bump 1), rest) := by
  have hr := h.ranks
  have hc := h.cnt_eq
  have hf : leafOk lim S I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) true = .ok true := hfit
  unfold fpDiffer
  have hitems' : (!c.init || c.exact) = true := hitems
  simp only [hitems', h.hlim, show rankHi S I.hi - rankOf S I.lo ≤ (if c.init then aleaf else bleaf) from by omega,
    ite_true, hf, bind, Except.bind, pure, Except.pure, itemsPart_spec lim S h.hlen _ tFULL I.lo I.hi _ _ hr.1 hr.2.1,
    hr.2.2, Out.head_addW_full _ _ _ tFULL rfl, leafUpd]

/-- The initiator's ids leaf (first pass). -/
theorem fpDiffer_ids (o : Oracle) {lim S c} (I : Iv) (h : HCtx lim S c I) (rest : List Nat) (mark : Nat)
    (hinit : c.init = true) (hex : c.exact = false) (hcnt : cnt S I ≤ aleaf) (hfit : fitsM lim S false I) :
    fpDiffer o S c I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) rest mark =
      .ok ((({ leafUpd c with out := (leafUpd c).out.addW (.ids I ((I.items S).map o.idf)) }).bump 1), rest) := by
  have hr := h.ranks
  have hc := h.cnt_eq
  have hf : leafOk lim S I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) false = .ok true := hfit
  unfold fpDiffer
  simp only [hinit, hex, h.hlim, show rankHi S I.hi - rankOf S I.lo ≤ aleaf from by omega, Bool.not_true,
    Bool.false_or, Bool.false_eq_true, ite_true, ite_false, hf, bind, Except.bind, pure, Except.pure,
    idsPart_spec o lim S h.hlen _ I.lo I.hi _ _ hr.1 hr.2.1, hr.2.2, Out.head_addW_ids, leafUpd]

/-- A range that is not a fitting leaf is split: at some fan 2 to 16, as the abstract system allows. -/
theorem fpDiffer_split (o : Oracle) {lim S c} (I : Iv) (h : HCtx lim S c I) (rest : List Nat) (mark : Nat)
    (hout : c.out.snap = c.out.last ∧ c.out.stage = [] ∧ c.out.body.length = mark)
    (hno : ¬ (cnt S I ≤ (if c.init then aleaf else bleaf) ∧ fitsM lim S (!c.init || c.exact) I)) :
    ∃ fan, 2 ≤ fan ∧ fan ≤ 16 ∧
      fpDiffer o S c I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) rest mark =
        .ok ((({ c with out :=
            { c.out with
              body := c.out.body ++ (encFps c.out.last ((splitIvs S I fan).zip
                ((blocksOf S I fan).map fun B => fpBytes (xorH o B)))).1,
              last := (encFps c.out.last ((splitIvs S I fan).zip
                ((blocksOf S I fan).map fun B => fpBytes (xorH o B)))).2 } }).bump (blocksOf S I fan).length), rest) := by
  have hr := h.ranks
  have hc := h.cnt_eq
  have hlim := h.hlim
  subst hlim
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
  obtain ⟨v, hv⟩ := leafOk_total c.lim S h.hlen I.lo I.hi (rankOf S I.lo) (rankHi S I.hi) (!c.init || c.exact) hr.2.1
  have hsp := splitParts_spec o c.lim S h.hS h.hlen I c.out fan (by omega) hr.1 hr.2.1
  unfold fpDiffer
  have hfit : ¬ (rankHi S I.hi - rankOf S I.lo ≤ (if c.init then aleaf else bleaf) ∧ v = true) := by
    rintro ⟨h3, h4⟩; subst h4; exact hno ⟨by omega, hv⟩
  by_cases hle : rankHi S I.hi - rankOf S I.lo ≤ (if c.init then aleaf else bleaf)
  · have hvf : v = false := by cases v <;> simp_all
    subst hvf
    simp only [hle, ite_true, hv, Bool.false_eq_true, ite_false, bind, Except.bind, pure, Except.pure, he, hrb, hsp]
  · simp only [hle, ite_false, Bool.false_eq_true, pure, Except.pure, bind, Except.bind, he, hrb, hsp]

end Vinc.Reconcile