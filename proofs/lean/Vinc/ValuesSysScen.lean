import Vinc.ValuesSysLive
import Vinc.ValuesSysLied

/-!
# The scenarios

PROPERTY 10: each scenario of `proofs/tla/ValuesSys_*.cfg` as an instance of the unbounded theorems, for every number of
groups, with the same providers and liars as its TLC configuration.

| scenario | TLC config | Lean |
|---|---|---|
| 1, 2, 3, 4 providers | `ValuesSys_n1`, `_n2`, `_n3`, `_n4` | `p1_safe` .. `p4_safe`, `p1_completes` .. `p4_completes` |
| a dropped provider (closed, redialled) | `ValuesSys_drop` | `drop_completes` |
| a slow provider (stall, steal) | `ValuesSys_slow` | `slow_completes` |
| a liar among honest providers | `ValuesSys_liar` | `liar_safe`, `liar_honest_survives` |
| every provider lies | `ValuesSys_alllie` | `all_lie` |
| restart in the middle | `ValuesSys_restart`, `_resume` | `restart_safe`, `restart_keeps_verified` |
| loss and reordering | `ValuesSys_loss` | `loss_safe` |
| deadline, refusing store, bad root, no provider | `ValuesSys_deadline`, `_store`, `_badroot`, `_noprov` | `edge_reasons` |

A dropped or a slow provider is a behaviour of the scheduling (`sched`: `redial`, `steal`) and the session, which the model lets the
adversary do anyway; their theorem is the completion theorem under `Fairness`, where `Fairness` is what the TLC liveness
check of those configurations establishes for the bounded model.
-/

namespace Vinc.ValuesSys

/-- A fetch of the first `g` groups from the providers `1..n`; the providers in `liars` may send bad frames. -/
def provs (g n : Nat) (liars : Nat → Bool) : Cfg where
  g := g
  want := fun x => decide (x < g)
  head0 := 0
  initVer := emp
  listed := fun p => decide (1 ≤ p ∧ p ≤ n)
  empty := false
  rootOk := true
  liars := liars
  storeFail := false
  deadline := none

def noLiars : Nat → Bool := fun _ => false
def liarOnly (k : Nat) : Nat → Bool := fun p => decide (p = k)
def everyLiar : Nat → Bool := fun _ => true

theorem provs_wf (g n : Nat) (l : Nat → Bool) : Wf (provs g n l) := by
  intro x hx; simpa [provs] using hx

/-- Completion for `n ≥ 1` providers that never lie, from the start. -/
theorem provs_completes {g n : Nat} (hn : 1 ≤ n) {σ : Nat → St} {rs : Nat} (hx : Exec (provs g n noLiars) σ)
    (hf : Fairness (provs g n noLiars) σ) (hr : Reach (provs g n noLiars) rs (σ 0)) (h0 : (σ 0).rs = 0)
    (hs : (σ 0).run ≠ .idle) (k : Nat) (hk : (σ k).run = .running) :
    ∃ m, (σ m).run = .done ∧ (σ m).fin = some .complete :=
  completes hx hf hr h0 hs rfl rfl (fun _ => rfl) ⟨1, by simp [provs, hn]⟩ (by simp [provs]) k hk

-- 1, 2, 3 and 4 providers
theorem p1_safe (g rs : Nat) (s : St) (h : Reach (provs g 1 noLiars) rs s) : Inv (provs g 1 noLiars) s := reach_inv h
theorem p2_safe (g rs : Nat) (s : St) (h : Reach (provs g 2 noLiars) rs s) : Inv (provs g 2 noLiars) s := reach_inv h
theorem p3_safe (g rs : Nat) (s : St) (h : Reach (provs g 3 (liarOnly 3)) rs s) : Inv (provs g 3 (liarOnly 3)) s :=
  reach_inv h
theorem p4_safe (g rs : Nat) (s : St) (h : Reach (provs g 4 (fun p => decide (2 ≤ p))) rs s) :
    Inv (provs g 4 (fun p => decide (2 ≤ p))) s := reach_inv h

theorem p1_completes (g : Nat) {σ : Nat → St} {rs : Nat} (hx : Exec (provs g 1 noLiars) σ)
    (hf : Fairness (provs g 1 noLiars) σ) (hr : Reach (provs g 1 noLiars) rs (σ 0)) (h0 : (σ 0).rs = 0)
    (hs : (σ 0).run ≠ .idle) (k : Nat) (hk : (σ k).run = .running) :
    ∃ m, (σ m).run = .done ∧ (σ m).fin = some .complete := provs_completes (by omega) hx hf hr h0 hs k hk
theorem p2_completes (g : Nat) {σ : Nat → St} {rs : Nat} (hx : Exec (provs g 2 noLiars) σ)
    (hf : Fairness (provs g 2 noLiars) σ) (hr : Reach (provs g 2 noLiars) rs (σ 0)) (h0 : (σ 0).rs = 0)
    (hs : (σ 0).run ≠ .idle) (k : Nat) (hk : (σ k).run = .running) :
    ∃ m, (σ m).run = .done ∧ (σ m).fin = some .complete := provs_completes (by omega) hx hf hr h0 hs k hk
theorem p3_completes (g : Nat) {σ : Nat → St} {rs : Nat} (hx : Exec (provs g 3 noLiars) σ)
    (hf : Fairness (provs g 3 noLiars) σ) (hr : Reach (provs g 3 noLiars) rs (σ 0)) (h0 : (σ 0).rs = 0)
    (hs : (σ 0).run ≠ .idle) (k : Nat) (hk : (σ k).run = .running) :
    ∃ m, (σ m).run = .done ∧ (σ m).fin = some .complete := provs_completes (by omega) hx hf hr h0 hs k hk
theorem p4_completes (g : Nat) {σ : Nat → St} {rs : Nat} (hx : Exec (provs g 4 noLiars) σ)
    (hf : Fairness (provs g 4 noLiars) σ) (hr : Reach (provs g 4 noLiars) rs (σ 0)) (h0 : (σ 0).rs = 0)
    (hs : (σ 0).run ≠ .idle) (k : Nat) (hk : (σ k).run = .running) :
    ∃ m, (σ m).run = .done ∧ (σ m).fin = some .complete := provs_completes (by omega) hx hf hr h0 hs k hk

-- a dropped provider and a slow provider: the same machine, the same theorem (the drop and the stall are
-- behaviours of the scheduling that the model lets the adversary do, and the fairness assumption covers their repair)
theorem drop_completes (g : Nat) {σ : Nat → St} {rs : Nat} (hx : Exec (provs g 3 noLiars) σ)
    (hf : Fairness (provs g 3 noLiars) σ) (hr : Reach (provs g 3 noLiars) rs (σ 0)) (h0 : (σ 0).rs = 0)
    (hs : (σ 0).run ≠ .idle) (k : Nat) (hk : (σ k).run = .running) :
    ∃ m, (σ m).run = .done ∧ (σ m).fin = some .complete := provs_completes (by omega) hx hf hr h0 hs k hk
theorem slow_completes (g : Nat) {σ : Nat → St} {rs : Nat} (hx : Exec (provs g 2 noLiars) σ)
    (hf : Fairness (provs g 2 noLiars) σ) (hr : Reach (provs g 2 noLiars) rs (σ 0)) (h0 : (σ 0).rs = 0)
    (hs : (σ 0).run ≠ .idle) (k : Nat) (hk : (σ k).run = .running) :
    ∃ m, (σ m).run = .done ∧ (σ m).fin = some .complete := provs_completes (by omega) hx hf hr h0 hs k hk

-- a liar among honest providers
theorem liar_safe (g rs : Nat) (s : St) (h : Reach (provs g 2 (liarOnly 2)) rs s) : Inv (provs g 2 (liarOnly 2)) s :=
  reach_inv h

/-- The honest provider is never evicted, and the fetch never fails with `EveryProviderLied` while it is there. -/
theorem liar_honest_survives (g rs : Nat) (s : St) (h : Reach (provs g 2 (liarOnly 2)) rs s) :
    s.lied 1 = false ∧ s.fin ≠ some .everyProviderLied := by
  have h1 : s.lied 1 = false := by
    have := liar_only h 1
    cases e : s.lied 1 with
    | false => rfl
    | true => have := this e; simp [provs, liarOnly] at this
  refine ⟨h1, fun hf => ?_⟩
  obtain ⟨_, hall⟩ := every_provider_lied h hf
  have := (hall 1 (by simp [provs])).2
  simp_all

-- every provider lies
theorem all_lie (g rs : Nat) (s : St) (h : Reach (provs g 2 everyLiar) rs s)
    (hall : s.inP 1 = false ∧ s.inP 2 = false) (hs : s.run ≠ .idle) :
    s.run = .done ∧ s.fin = some .everyProviderLied := by
  refine all_lie_fails h ⟨1, by simp [provs]⟩ ?_ hs
  intro p hp
  simp [provs] at hp
  rcases hp with ⟨h1, h2⟩
  have : p = 1 ∨ p = 2 := by omega
  rcases this with rfl | rfl <;> simp [hall]

-- a restart in the middle: the store survives, the verified set only grows, nothing verified at the start is asked
theorem restart_safe (g rs : Nat) (s : St) (h : Reach (provs g 2 noLiars) (rs + 1) s) :
    Inv (provs g 2 noLiars) s ∧ ∀ x, s.reqd x = true → s.ver0 x = false := ⟨reach_inv h, resume_not_asked h⟩

/-- A restart is a step of the model that keeps the verified set and the bytes written. -/
theorem restart_keeps_verified (c : Cfg) (s : St) (hr : s.run ≠ .idle) (hrs : 0 < s.rs) :
    ∃ s', Step c s s' ∧ s'.ver = s.ver ∧ s'.wr = s.wr ∧ s'.run = .idle :=
  ⟨_, Step.restart s hr hrs, rfl, rfl, rfl⟩

-- loss and reordering: out-of-order frames verified against range proofs are written through; the same steps
theorem loss_safe (g rs : Nat) (s : St) (h : Reach (provs g 1 everyLiar) rs s) : Inv (provs g 1 everyLiar) s :=
  reach_inv h

/-- The edge cases end with the right reason. -/
theorem edge_reasons {c : Cfg} {rs : Nat} {s : St} (h : Reach c rs s) :
    (s.fin = some .deadline → ∃ d, c.deadline = some d ∧ d < s.now) ∧
    (s.fin = some .noProvider → ∀ p, c.listed p = false) ∧
    (s.fin = some .store → c.storeFail = true) ∧
    (s.fin = some .badRoot → c.empty = true ∧ c.rootOk = false) := failure_reasons h

end Vinc.ValuesSys
