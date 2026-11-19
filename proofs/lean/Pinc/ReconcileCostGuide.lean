import Pinc.ReconcileCorrect

/-!
vertexclique

# What a reconciliation costs, and why: a guided proof

Say two nodes each keep a sorted set of items, and they'd like to know which items only one of them has. This file
answers one question about that: how much work is it? It goes slowly enough that you can check every step against
the Rust code. There's no new machinery in here. The model of the code lives in `ReconcileApsModel` and the counting
argument in `ReconcileApsCost` and `ReconcileApsBounds`. What I do here is restate their result the way you'd ask
for it while reading the code, say what each letter stands for, and then squeeze a few sharper facts out of it.

## The names, in plain words

The theorems are unreadable without these, so here they are once.

* The initiator's set is `A` and the responder's is `B`. Both are sorted lists that never repeat an item (`Core`
  reads them through the host's `ItemIndex`).
* `nA` and `nB` are how many items each of them holds. In the theorems you'll see them as `c.A.length` and
  `c.B.length`.
* `D` is how much the two sets disagree: count the items `A` has that `B` doesn't, add the items `B` has that `A`
  doesn't, and that's `D`. In the theorems it's `c.diff`. If the sets are equal, `D` is 0.
* A part is one entry of a message: a range of keys together with a fingerprint, or some ids, or whole items, or the
  reply to one of those last two. The code builds and answers parts in `Core::answer`. I count parts because a part
  is a unit of work: it costs the node one lookup in its index and one fingerprint, or one small merge.
* The fan `f` is how many pieces a range gets cut into when the two sides disagree about it. The code cuts 16 ways,
  and it only drops to 8, 4 or 2 when the answer for a narrow range wouldn't fit into a single message. `c.minFan`
  is the smallest fan a run is allowed to use.
* `lg f n` counts how often you have to divide `n` by `f`, rounding up every time, until you're down to one item.
  It's the smallest `k` with `n <= f^k`, so `lg 16 1048576 = 5` and `lg 2 1048576 = 20`.
* `s` is where a pass has got to. `s.log` is the list of parts already dealt with and `s.pend` the ones still
  waiting. Once `s.pend` is empty the pass is done, and the length of `s.log` is all the work both nodes did.
* `IReach c s` means you can get to `s` from the first message of a pass by handling pending parts, in whatever
  order you like. Every order, every way of cutting the parts into messages and every fan the code may pick is one
  such path. So when a theorem holds for every reachable `s`, it holds for every run.

## The bound

`stepsBound f D nA nB = 17 + 17 * (D * (2 * (lg f nA + lg f nB) + 2))`

The formula is easiest to read starting from the middle. `lg f nA + lg f nB` tells you how far the cutting can go
before a range has at most one item left on each side. A range the two sides disagree on gets passed back and forth,
which is why the depth shows up twice, and the extra 2 pays for the last exchange of ids or items. Put together,
that's how long a trail a single differing item can leave behind. Every step along the trail creates at most 16 new
parts and is a part itself, so you multiply by 17. With `D` differing items you get `D` trails. The 17 in front is
the opening message, which has at most 16 ranges in it plus the part carrying them.

So what you pay for is the difference times the depth. The size of the sets only gets in through the depth, as a
logarithm.

## What this file adds

1. `lg_base_anti`: a larger fan never needs more levels.
2. `stepsBound_base_anti`: so the bound with the fan the code really used is never worse than the bound with fan 2.
3. `equal_sets_cost`: two equal sets cost at most 17 parts whatever their size. This is below `D log n`: it is a
   constant.
4. `cost_of_sizes` and its two readings: for sets of up to a million items the cost is at most `17 + 374 * D` parts
   when no range had to be cut narrower than 16 ways, and at most `17 + 1394 * D` in every case.
5. `trail_depth`: no chain of answers is longer than `2 * (lg f nA + lg f nB) + 3`, whatever `D` is. The number of
   round trips follows the size of the sets only through that logarithm and does not grow with the difference.

## What it doesn't say

It counts parts. Bytes and messages have their own file, `ReconcileCostBytes`, which proves the same kind of bound
for both. Also, the theorems talk about the part rules of the code. The last link, from the functions that actually
read and write bytes down to those rules, is proved for the split and for the leaf rule but not from end to end
(`ReconcileCorrect` lists what's open). And I suspect the 16-way cut really satisfies something like
`D * log (n / D)`, which would be better still, but that isn't proved here either.
-/

namespace Pinc.Reconcile

/-!
## 1. A larger fan never needs more levels

`f` and `g` are two fans with `2 <= f <= g`, and `n` is a number of items. Cutting `g` ways shrinks a range at least
as fast as cutting `f` ways, so it reaches one item in no more levels.
-/
theorem lg_base_anti {f g : Nat} (hf : 2 ≤ f) (hfg : f ≤ g) : ∀ n : Nat, lg g n ≤ lg f n := by
  -- `n` is the number of items. We argue by induction on it: to prove the claim for `n` we may use it for every
  -- smaller number, which `ih` gives us.
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : 2 ≤ n
    · -- Two items or more: one more cut is needed with either fan.
      -- `hg` records that `g` is a fan too (at least 2), which the lemmas about `lg` ask for.
      have hg : 2 ≤ g := Nat.le_trans hf hfg
      -- Unfold one level on each side: `lg g n = lg g (ceil (n / g)) + 1` and the same for `f`.
      -- `(n + g - 1) / g` is how `ceil (n / g)` is written with whole numbers.
      rw [lg_step hn hg, lg_step hn hf]
      -- `h1`: a piece of a `g`-way cut is no larger than a piece of an `f`-way cut.
      have h1 : (n + g - 1) / g ≤ (n + f - 1) / f := ceil_anti (by omega) hfg
      -- `h2`: fewer items never need more levels (same fan `g` on both sides).
      have h2 : lg g ((n + g - 1) / g) ≤ lg g ((n + f - 1) / f) := lg_mono hg _ _ h1
      -- `h3`: the claim itself for the smaller number `ceil (n / f)`, which is below `n` by `ceil_lt`.
      have h3 : lg g ((n + f - 1) / f) ≤ lg f ((n + f - 1) / f) := ih _ (ceil_lt hn hf)
      -- Chain `h2` and `h3` and add the one level we unfolded.
      omega
    · -- Fewer than two items: no cut is needed with either fan, both sides are 0.
      have a : lg g n = 0 := lg_small (by omega)
      have b : lg f n = 0 := lg_small (by omega)
      omega

/-!
## 2. So the bound with the larger fan is the smaller bound

`D`, `nA`, `nB` are as in the header. `f <= g` are two fans. The bound is built from `lg` by adding and multiplying,
so it inherits the direction of `lg_base_anti`.
-/
theorem stepsBound_base_anti {f g : Nat} (hf : 2 ≤ f) (hfg : f ≤ g) (D nA nB : Nat) :
    stepsBound g D nA nB ≤ stepsBound f D nA nB := by
  -- Replace the name `stepsBound` by its formula on both sides.
  unfold stepsBound
  -- `a` and `b`: the levels for each set, fan `g` against fan `f`.
  have a := lg_base_anti hf hfg nA
  have b := lg_base_anti hf hfg nB
  -- `m`: multiply the per-item trail length by `D` on both sides; the order is kept.
  have m : D * (2 * (lg g nA + lg g nB) + 2) ≤ D * (2 * (lg f nA + lg f nB) + 2) :=
    Nat.mul_le_mul_left D (by omega)
  omega

/-!
## 3. Equal sets cost a constant

`c` is the pair of sets with the rules of the code, `s` a finished state of a pass (`hp`: nothing pending), and `hD`
says the sets do not differ. Then at most 17 parts were handled: the opening message and nothing after it, because
every fingerprint matched. The sizes `nA` and `nB` do not appear in the conclusion at all.
-/
theorem equal_sets_cost {c : Cfg} {s : St} (h : IReach c s) (hp : s.pend = []) (hD : c.diff = 0) :
    s.log.length ≤ 17 := by
  -- `b` is the general bound for this run, taken with fan 2, which every run satisfies (`c.hmin`: the smallest fan
  -- of a run is at least 2).
  have b := aps_steps_bound (f := 2) (Nat.le_refl 2) c.hmin h hp
  -- Write the bound out, put `D = 0` in, and `0 * anything` is `0`: what is left is `17 + 17 * 0`.
  unfold stepsBound at b
  rw [hD, Nat.zero_mul] at b
  omega

/-!
## 4. The cost for sets of a known size

`k` is a number of levels and `hA`, `hB` say both sets hold at most `f^k` items. `f` is any fan the run never went
below (`hfm : f <= c.minFan`). Then a finished pass handled at most `17 + 17 * (D * (4 * k + 2))` parts: the `lg` of
each set is at most `k`, and there are two sets and two directions, hence `4 * k`.
-/
theorem cost_of_sizes {c : Cfg} {f k : Nat} (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) {s : St} (h : IReach c s)
    (hp : s.pend = []) (hA : c.A.length ≤ f ^ k) (hB : c.B.length ≤ f ^ k) :
    s.log.length ≤ 17 + 17 * (c.diff * (4 * k + 2)) := by
  -- `b`: the general bound for this run and this fan.
  have b := aps_steps_bound hfl hfm h hp
  -- `a1`, `a2`: a set of at most `f^k` items needs at most `k` levels.
  have a1 := lg_le_of_pow hfl k _ hA
  have a2 := lg_le_of_pow hfl k _ hB
  unfold stepsBound at b
  -- `m`: the trail of one differing item is at most `4 * k + 2` long; multiply by `D`.
  have m : c.diff * (2 * (lg f c.A.length + lg f c.B.length) + 2) ≤ c.diff * (4 * k + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- Sets of up to 1,048,576 items each (`16^5`), in a run that never cut a range narrower than 16 ways (`h16`):
at most `17 + 374 * D` parts. Here `k = 5`, so `17 * (4 * 5 + 2) = 374`. -/
theorem cost_million_fan16 {c : Cfg} (h16 : c.minFan = 16) {s : St} (h : IReach c s) (hp : s.pend = [])
    (hA : c.A.length ≤ 1048576) (hB : c.B.length ≤ 1048576) : s.log.length ≤ 17 + 374 * c.diff := by
  -- `16^5 = 1048576`, so the size hypotheses are the ones `cost_of_sizes` wants with `f = 16` and `k = 5`.
  have e : (16 : Nat) ^ 5 = 1048576 := by decide
  have b := cost_of_sizes (f := 16) (k := 5) (by omega) (by omega) h hp (by omega) (by omega)
  omega

/-- The same sets with no assumption on the fan: at most `17 + 1394 * D` parts. A run may always be read with fan 2
(`c.hmin`), and `2^20 = 1048576`, so `k = 20` and `17 * (4 * 20 + 2) = 1394`. -/
theorem cost_million_any_fan {c : Cfg} {s : St} (h : IReach c s) (hp : s.pend = [])
    (hA : c.A.length ≤ 1048576) (hB : c.B.length ≤ 1048576) : s.log.length ≤ 17 + 1394 * c.diff := by
  have e : (2 : Nat) ^ 20 = 1048576 := by decide
  have b := cost_of_sizes (f := 2) (k := 20) (Nat.le_refl 2) c.hmin h hp (by omega) (by omega)
  omega

/-!
## 5. How long a chain of answers can get

Every part carries its depth `q.d`: the opening message is depth 1, the answer to a part of depth `d` has depth
`d + 1`. `q` ranges over every part of the run, handled (`s.log`) or waiting (`s.pend`). The theorem says no part
is deeper than `2 * (lg f nA + lg f nB) + 3`. `D` is not in the bound: a large difference makes the run wider (more
parts side by side in one message), never longer.
-/
theorem trail_depth {c : Cfg} {f : Nat} (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) {s : St} (h : IReach c s) :
    ∀ q ∈ s.log ++ s.pend, q.d ≤ 2 * (lg f c.A.length + lg f c.B.length) + 3 := by
  intro q hq
  -- `aps_depth_bound` states this with the name `depthBound`; unfolding the name gives the formula.
  have b := aps_depth_bound hfl hfm h q hq
  unfold depthBound at b
  exact b

/-!
## 6. The same facts for the code's own rules

`machineCfg lim o A B hA hB` is the model with the leaf rule of the code: `lim` are the size limits of a session
(`Limits` in the Rust crate), `o` the keyed hash, `hA` and `hB` the proofs that the two lists are sorted. Its smallest
fan is 2, because the code may narrow a cut that far, so the readings below use fan 2.
-/
theorem machine_equal_sets_cost {lim : Limits} {o : Oracle} {A B : List Item} (hA : Sorted A) (hB : Sorted B)
    {s : St} (h : IReach (machineCfg lim o A B hA hB) s) (hp : s.pend = [])
    (hD : (machineCfg lim o A B hA hB).diff = 0) : s.log.length ≤ 17 :=
  equal_sets_cost h hp hD

theorem machine_cost_million {lim : Limits} {o : Oracle} {A B : List Item} (hA : Sorted A) (hB : Sorted B)
    {s : St} (h : IReach (machineCfg lim o A B hA hB) s) (hp : s.pend = [])
    (hnA : A.length ≤ 1048576) (hnB : B.length ≤ 1048576) :
    s.log.length ≤ 17 + 1394 * (machineCfg lim o A B hA hB).diff :=
  cost_million_any_fan h hp hnA hnB

#audit_axioms Pinc.Reconcile.lg_base_anti
#audit_axioms Pinc.Reconcile.stepsBound_base_anti
#audit_axioms Pinc.Reconcile.equal_sets_cost
#audit_axioms Pinc.Reconcile.cost_of_sizes
#audit_axioms Pinc.Reconcile.cost_million_fan16
#audit_axioms Pinc.Reconcile.cost_million_any_fan
#audit_axioms Pinc.Reconcile.trail_depth
#audit_axioms Pinc.Reconcile.machine_equal_sets_cost
#audit_axioms Pinc.Reconcile.machine_cost_million

end Pinc.Reconcile
