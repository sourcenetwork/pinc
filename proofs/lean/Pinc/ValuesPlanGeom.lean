import Pinc.ValuesPlanOk

/-!
# The frames of a plan

`PlanM.frameStart` and `PlanM.frame` are `Plan::frame_start` and `Plan::frame` of `plan.rs` on `Nat`: the closed
form with `parents_before`. `frame_spec` proves, for every range of an accepted plan and every group of the
range, that

* the frame exists, with the stream offset of the reference (the range's start plus the bytes of the reference
  frames before it: `sumTo (fb ..)`), the group offset and length of the reference frame, the pair count of the
  reference frame times 64 as proof length, and `follows` exactly after the first frame;
* the frame ends where the next one starts (`frame_end_start`), so the frames of a range tile it and, with the
  ranges laid back to back (`RO`), the whole response `[0, total)` (`tiling`);
* the starts strictly increase (`start_strict`).

`frame_u32` shows the `u32::try_from` of the lengths never fails and `frame_none` that only a group of the range
has a frame. `frame_end_le_total` shows no frame passes the response, which is at most `2^62 - 1` bytes, so no
offset of the plan overflows.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesPlan
open Pinc.Layout Pinc.Encode

/-- One GROUP frame of a response (`plan::Frame`). -/
structure FrameM where
  range : Nat
  k : Nat
  start : Nat
  off : Nat
  dlen : Nat
  plen : Nat
  follows : Bool
  deriving DecidableEq, Repr

/-- The stream offset where the proof starts. -/
def FrameM.proofStart (f : FrameM) : Nat := f.start + HDR
/-- The stream offset where the group bytes start. -/
def FrameM.dataStart (f : FrameM) : Nat := f.start + HDR + f.plen
/-- The stream offset just past the frame. -/
def FrameM.fend (f : FrameM) : Nat := f.dataStart + f.dlen

/-- `Plan::frame_start`. -/
def PlanM.frameStart (pl : PlanM) (r : PR) (k : Nat) : Nat :=
  if k = 0 then r.start
  else r.start + k * HDR + (min ((r.first + k) * G) pl.len - r.first * G) +
    PARL * parentsBefore (groups pl.len lg) r.first (r.first + k - 1)

/-- `Plan::frame`. -/
def PlanM.frame (pl : PlanM) (i k : Nat) : Option FrameM :=
  match pl.rs[i]? with
  | none => none
  | some r =>
    if r.first + k < r.last then
      let n := groups pl.len lg
      let before := parentsBefore n r.first (r.first + k)
      let prev := if k = 0 then 0 else parentsBefore n r.first (r.first + k - 1)
      some ⟨i, k, pl.frameStart r k, (r.first + k) * G, groupSize pl.len lg (r.first + k), (before - prev) * PARL, decide (0 < k)⟩
    else none

/-- The bytes of frame `j` of the range `[a, ..)`: header, pairs, group. -/
def fb (len a j : Nat) : Nat := HDR + pendLen (groups len lg) a j * PARL + groupSize len lg (a + j)

theorem fb_pos (len a j : Nat) : HDR ≤ fb len a j := by unfold fb; omega

theorem fbytes_frameOf (len a j : Nat) : fbytes (frameOf len lg 0 (groups len lg) 0 a [] (a + j)) = fb len a j := by
  simp only [fbytes, frameOf, fb]
  rw [← frame_pend len lg _ a j]
  simp [frameOf]

theorem refSize_sumTo (len a b : Nat) (hab : a < b) (hb : b ≤ groups len lg) :
    refSize len a b = sumTo (fb len a) (b - a) := by
  unfold refSize refFrames
  rw [frames_of_range len lg a b hab hb, tab_sum]
  exact sumTo_congr _ _ _ (fun j _ => fbytes_frameOf len a j)

theorem refFrames_take (len a b k : Nat) (hab : a < b) (hb : b ≤ groups len lg) (hk : k ≤ b - a) :
    (((refFrames len a b).take k).map fbytes).sum = sumTo (fb len a) k := by
  unfold refFrames
  rw [frames_of_range len lg a b hab hb, tab_take, show min k (b - a) = k by omega, tab_sum]
  exact sumTo_congr _ _ _ (fun j _ => fbytes_frameOf len a j)

theorem refFrames_get (len a b k : Nat) (hab : a < b) (hb : b ≤ groups len lg) (hk : k < b - a) :
    (refFrames len a b)[k]? = some (frameOf len lg 0 (groups len lg) 0 a [] (a + k)) := by
  unfold refFrames
  rw [frames_of_range len lg a b hab hb]
  exact tab_getElem _ _ _ _ hk

theorem refFrames_length (len a b : Nat) (hab : a < b) (hb : b ≤ groups len lg) :
    (refFrames len a b).length = b - a := by
  unfold refFrames
  rw [frames_of_range len lg a b hab hb, tab_length]

theorem sumTo_fb_succ (len a k : Nat) : sumTo (fb len a) (k + 1) = sumTo (fb len a) k + fb len a k := rfl

theorem sumTo_fb_strict (len a k : Nat) : sumTo (fb len a) k < sumTo (fb len a) (k + 1) := by
  have := fb_pos len a k
  rw [sumTo_fb_succ]; unfold HDR at this; omega

theorem sumTo_fb_lt (len a : Nat) : ∀ j k, j < k → sumTo (fb len a) j < sumTo (fb len a) k := by
  intro j k h
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hj : j = k
    · subst hj; exact sumTo_fb_strict len a j
    · exact Nat.lt_trans (ih (by omega)) (sumTo_fb_strict len a k)

/-- The closed form of `frame_start` is the bytes of the frames before. -/
theorem frameStart_closed (len a b k : Nat) (hlen : len ≤ u64Max) (hab : a < b) (hb : b ≤ groups len lg)
    (hk : 0 < k) (hkb : k ≤ b - a) :
    k * HDR + (min len ((a + k) * G) - a * G) + PARL * parentsBefore (groups len lg) a (a + k - 1) =
      sumTo (fb len a) k := by
  have h1 : sumTo (fb len a) k = sumTo (fun _ => HDR) k + sumTo (fun j => pendLen (groups len lg) a j * PARL) k +
      sumTo (fun j => groupSize len lg (a + j)) k := by
    unfold fb; rw [← sumTo_add, ← sumTo_add]
  rw [h1, sumTo_const, sumTo_mul]
  have hlt : a * groupLen lg ≤ len := by
    have := (lt_groups_iff len lg a).1 (by omega)
    omega
  rw [sumTo_groupSize len lg a hlen _ hlt]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have := parentsBefore_sum len lg a b m hab hb (by omega)
  rw [show a + (m + 1) - 1 = a + m by omega, this]
  have e1 : (a + (m + 1)) * G = (a + (m + 1)) * groupLen lg := rfl
  have e2 : a * G = a * groupLen lg := rfl
  have e3 := Nat.mul_comm PARL (sumTo (pendLen (groups len lg) a) (m + 1))
  have e4 := Nat.mul_comm (m + 1) HDR
  omega

/-- The facts about an accepted plan the geometry uses. -/
structure Good (len : Nat) (pl : PlanM) : Prop where
  hlen : len ≤ u64Max
  plen : pl.len = len
  ro : RO len pl.rs 0 pl.total
  maxs : pl.total ≤ MAXS

theorem Good.of_new {len : Nat} {spans : List (Nat × Nat)} {pl : PlanM} (hlen : len ≤ u64Max)
    (h : planNew len spans = Except.ok pl) : Good len pl := by
  obtain ⟨a, b, c, d, e, f⟩ := planNew_ok len hlen spans pl h
  exact ⟨hlen, a, b, c⟩

/-- The range at index `i`, with its facts. -/
theorem Good.range {len : Nat} {pl : PlanM} (g : Good len pl) {i : Nat} {r : PR} (hr : pl.rs[i]? = some r) :
    r.first < r.last ∧ r.last ≤ groups len lg ∧
      r.start = ((pl.rs.take i).map (szr len)).sum := by
  obtain ⟨a, b, c⟩ := RO_index len pl.rs 0 pl.total g.ro
  have hi : i < pl.rs.length :=
    Classical.byContradiction fun hc => by rw [List.getElem?_eq_none (by omega)] at hr; cases hr
  have hr' : pl.rs[i] = r := by rw [List.getElem?_eq_getElem hi] at hr; exact Option.some.inj hr
  have hmem : r ∈ pl.rs := hr' ▸ List.getElem_mem hi
  obtain ⟨h1, h2⟩ := a r hmem
  refine ⟨h1, h2, ?_⟩
  have := c i hi
  rw [hr'] at this
  omega

theorem frameStart_eq {len : Nat} {pl : PlanM} (g : Good len pl) {i k : Nat} {r : PR} (hr : pl.rs[i]? = some r)
    (hk : k < r.last - r.first) : pl.frameStart r k = r.start + sumTo (fb len r.first) k := by
  obtain ⟨h1, h2, h3⟩ := g.range hr
  simp only [PlanM.frameStart, g.plen]
  by_cases h0 : k = 0
  · subst h0; simp [sumTo]
  · simp only [h0, ite_false]
    have := frameStart_closed len r.first r.last k g.hlen h1 h2 (by omega) (by omega)
    omega

theorem frame_spec {len : Nat} {pl : PlanM} (g : Good len pl) {i k : Nat} {r : PR} (hr : pl.rs[i]? = some r)
    (hk : k < r.last - r.first) :
    ∃ f, pl.frame i k = some f ∧ f.range = i ∧ f.k = k ∧ f.off = (r.first + k) * G ∧
      f.start = r.start + sumTo (fb len r.first) k ∧ f.fend = r.start + sumTo (fb len r.first) (k + 1) ∧
      f.plen = pendLen (groups len lg) r.first k * PARL ∧ f.dlen = groupSize len lg (r.first + k) ∧
      f.follows = decide (0 < k) := by
  obtain ⟨h1, h2, h3⟩ := g.range hr
  have hn : pl.len = len := g.plen
  have hx : r.first + k < r.last := by omega
  have hps := parentsBefore_sum len lg r.first r.last k h1 h2 hx
  have hplen : (parentsBefore (groups len lg) r.first (r.first + k) -
      (if k = 0 then 0 else parentsBefore (groups len lg) r.first (r.first + k - 1))) = pendLen (groups len lg) r.first k := by
    by_cases h0 : k = 0
    · subst h0
      rw [show r.first + 0 = r.first from rfl] at hps
      simp only [ite_true, Nat.sub_zero, Nat.add_zero]
      rw [hps]; simp [sumTo]
    · simp only [h0, ite_false]
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [show r.first + (m + 1) - 1 = r.first + m by omega, parentsBefore_sum len lg r.first r.last m h1 h2 (by omega), hps]
      simp [sumTo]
  have hstart := frameStart_eq g hr hk
  have hf : pl.frame i k = some ⟨i, k, pl.frameStart r k, (r.first + k) * G, groupSize len lg (r.first + k),
      pendLen (groups len lg) r.first k * PARL, decide (0 < k)⟩ := by
    simp only [PlanM.frame, hr, hx, ite_true, hn, hplen]
  refine ⟨_, hf, rfl, rfl, rfl, hstart, ?_, rfl, rfl, rfl⟩
  simp only [FrameM.fend, FrameM.dataStart, hstart, sumTo_fb_succ, fb]
  omega

end Pinc.ValuesPlan
