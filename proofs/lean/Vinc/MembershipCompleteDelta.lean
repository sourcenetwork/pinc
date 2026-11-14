import Vinc.MembershipViewPrimary
import Vinc.MembershipCompleteSent

/-!
# Completeness and accuracy over timed hypotheses, part 4: a Down delta removes the member from the view

What a node does with a `Down` delta of hub `H` for `m` (`apply_delta`, then `recompute_one` and `remove_from_view`):

* `applyDeltaCore_down_removes` (property 2, view side): the copy of `H` loses its entry for `m` (same or newer epoch), and
  when no other eligible copy lists `m`, the source does not hold removals and no quiet window is open, `m` is removed from the
  view at once.
* `applyDeltaCore_down_defers`: with a quiet window open (and room in the recheck table) the removal is deferred:
  the view is unchanged and `m` is queued for `recheck_due` (at the window's end unless it already waits).
* `applyDeltaCore_down_homes`: a hub that removes `m` from its view hands a `Down` delta to each homed member session.

`Srt` is the sortedness every table of the machine keeps (a `BTreeMap`): a hypothesis on the state, an invariant of every
reachable state.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership.Cmp
open Vinc.Membership
open Vinc.MemInc

/-- The keys of a table are strictly increasing. -/
def Srt {α : Type} (m : AMap α) : Prop := m.keys.Pairwise (· < ·)

theorem srt_tail {α : Type} {a : Nat} {b : α} {r : AMap α} (h : Srt ((a, b) :: r)) : Srt r ∧ ∀ x ∈ r, a < x.1 := by
  unfold Srt AMap.keys at h ⊢
  simp only [List.map_cons, List.pairwise_cons, List.mem_map] at h
  refine ⟨h.2, fun x hx => h.1 x.1 ⟨x, hx, rfl⟩⟩

theorem mem_insert_cases {α : Type} (m : AMap α) (hs : Srt m) (k : Nat) (v : α) (p : Nat × α) (hp : p ∈ m.insert k v) :
    p = (k, v) ∨ (p ∈ m ∧ p.1 ≠ k) := by
  induction m with
  | nil => simp [AMap.insert] at hp; left; exact hp
  | cons q r ih =>
    obtain ⟨a, b⟩ := q
    obtain ⟨hs', hlt⟩ := srt_tail hs
    simp only [AMap.insert] at hp
    by_cases h1 : k < a
    · rw [if_pos h1] at hp
      rcases List.mem_cons.mp hp with h | h
      · left; exact h
      · right
        refine ⟨h, ?_⟩
        rcases List.mem_cons.mp h with h | h
        · subst h; simp; omega
        · have := hlt p h; omega
    · rw [if_neg h1] at hp
      by_cases h2 : (k == a) = true
      · rw [if_pos h2] at hp
        have hka : k = a := by simpa using h2
        rcases List.mem_cons.mp hp with h | h
        · left; exact h
        · right
          refine ⟨List.mem_cons_of_mem _ h, ?_⟩
          have := hlt p h; omega
      · rw [if_neg h2] at hp
        have hka : k ≠ a := by simpa using h2
        rcases List.mem_cons.mp hp with h | h
        · right; subst h; exact ⟨List.mem_cons_self .., by simp; omega⟩
        · rcases ih hs' h with h3 | ⟨h3, h4⟩
          · left; exact h3
          · right; exact ⟨List.mem_cons_of_mem _ h3, h4⟩

/-- A key present in a sorted table is the key of exactly the entry `get?` returns. -/
theorem get?_of_mem {α : Type} (m : AMap α) (hs : Srt m) (p : Nat × α) (hp : p ∈ m) : m.get? p.1 = some p.2 := by
  induction m with
  | nil => simp at hp
  | cons q r ih =>
    obtain ⟨a, b⟩ := q
    obtain ⟨hs', hlt⟩ := srt_tail hs
    unfold AMap.get?
    simp only [List.find?_cons]
    rcases List.mem_cons.mp hp with h | h
    · subst h; simp
    · have hne : a ≠ p.1 := by have := hlt p h; omega
      have : (a == p.1) = false := by simpa using hne
      rw [this]
      simpa [AMap.get?] using ih hs' h


/-! ## The copy of the sending hub loses the entry -/

@[simp] theorem trace_members_c (n : N) (t : Tr) : (n.trace t).members = n.members := (trace_out n t).members
@[simp] theorem emit_members_c (n : N) (e : Ev) : (n.emit e).members = n.members := (emit_out n e).members
@[simp] theorem ite_members (c : Prop) [Decidable c] (a b : N) :
    (if c then a else b).members = if c then a.members else b.members := by split <;> rfl
@[simp] theorem homeDelta_members_c (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) :
    (N.homeDelta e n m rc a).members = n.members := (homeDelta_out e n m rc a).members

theorem keys_insert_of_has {α : Type} (m : AMap α) (hs : Srt m) (k : Nat) (v : α) (h : m.has k = true) :
    (m.insert k v).keys = m.keys := by
  induction m with
  | nil => simp [AMap.has] at h
  | cons q r ih =>
    obtain ⟨a, b⟩ := q
    obtain ⟨hs', hlt⟩ := srt_tail hs
    simp only [AMap.insert]
    have hk : k = a ∨ k ∈ AMap.keys r := by
      rw [AMap.has_keys] at h
      simp only [AMap.keys, List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · left; exact h
      · right; exact h
    have hnl : ¬ k < a := by
      rcases hk with h | h
      · omega
      · simp only [AMap.keys, List.mem_map] at h
        obtain ⟨y, hy, hyk⟩ := h
        have := hlt y hy; omega
    rw [if_neg hnl]
    by_cases h2 : (k == a) = true
    · rw [if_pos h2]
      have : k = a := by simpa using h2
      subst this; rfl
    · rw [if_neg h2]
      have hka : k ≠ a := by simpa using h2
      have hr : AMap.has r k = true := by
        rcases hk with h | h
        · exact absurd h hka
        · exact (AMap.has_keys _ _).mpr h
      simp only [AMap.keys, List.map_cons] at ih ⊢
      rw [ih hs' hr]

theorem adEntries_down (n : N) (H m : Nat) (rc : Rec) (c : HubCopy) (hH : n.hv.get? H = some c) (hs : Srt n.hv)
    (hent : ∀ x, c.entries.get? m = some x → x.rc.inc / 65536 ≤ rc.inc / 65536) :
    ∃ hv' : AMap HubCopy, n.adEntries H m rc .down = { n with hv := hv' } ∧ hv'.keys = n.hv.keys ∧
      (∀ p ∈ hv', p.1 = H → p.2.entries.get? m = none) ∧ (∀ p ∈ hv', p.1 ≠ H → p ∈ n.hv) := by
  have hhas : n.hv.has H = true := AMap.get?_has _ _ _ hH
  have hpc : ∀ p ∈ n.hv, p.1 = H → p.2 = c := by
    intro p hp hp1
    have := get?_of_mem n.hv hs p hp
    rw [hp1, hH] at this; injection this with h; exact h.symm
  unfold N.adEntries
  rw [hH]
  simp only []
  unfold N.adDown
  cases hx : c.entries.get? m with
  | none =>
    refine ⟨n.hv, rfl, rfl, fun p hp hp1 => ?_, fun p hp _ => hp⟩
    rw [hpc p hp hp1]; exact hx
  | some x =>
    have hle := hent x hx
    simp only [hle, if_true]
    refine ⟨n.hv.insert H { c with entries := c.entries.erase m }, ?_, keys_insert_of_has _ hs _ _ hhas, ?_, ?_⟩
    · simp
    · intro p hp hp1
      rcases mem_insert_cases n.hv hs H _ p hp with h | ⟨_, h⟩
      · subst h; exact AMap.get?_erase_self _ _
      · exact absurd hp1 h
    · intro p hp hp1
      rcases mem_insert_cases n.hv hs H _ p hp with h | ⟨h, _⟩
      · subst h; exact absurd rfl hp1
      · exact h

/-- `apply_delta` of a `Down` for `m` from `H`, as the code runs it when `H` has a copy: the copy loses `m`, then `m` is
recomputed. -/
theorem applyDeltaCore_down_eq (e : Env) (n : N) (now H m : Nat) (rc : Rec) (c : HubCopy) (hrev : n.revoked.has m = false)
    (hs : Srt n.hv) (hH : n.hv.get? H = some c)
    (hent : ∀ x, c.entries.get? m = some x → x.rc.inc / 65536 ≤ rc.inc / 65536) :
    ∃ hv' : AMap HubCopy, hv'.keys = n.hv.keys ∧ (∀ p ∈ hv', p.1 = H → p.2.entries.get? m = none) ∧
      (∀ p ∈ hv', p.1 ≠ H → p ∈ n.hv) ∧
      N.applyDeltaCore e n now H m rc .down =
        (let r := N.recomputeOne e ({ n with hv := hv' } : N) now m; if r.2 = true then r.1.bump else r.1) := by
  obtain ⟨hv', h1, h2, h3, h4⟩ := adEntries_down n H m rc c hH hs hent
  refine ⟨hv', h2, h3, h4, ?_⟩
  rw [applyDeltaCore_eq]
  unfold N.applyDeltaCoreS
  rw [if_neg (by simp [hrev])]
  have hE : n.adEnsure H = (n, true) := by
    unfold N.adEnsure
    have := AMap.get?_has _ _ _ hH
    simp [this]
  simp only [hE]
  rw [h1]
  simp

theorem source_hv (n : N) (hv' : AMap HubCopy) (now : Nat) (h : hv'.keys = n.hv.keys) :
    ({ n with hv := hv' } : N).source now = n.source now := by
  have hhas : ∀ p, hv'.has p = n.hv.has p := by
    intro p
    apply Bool.eq_iff_iff.mpr
    rw [AMap.has_keys, AMap.has_keys, h]
  unfold N.source
  simp only [hhas, h]
  rfl


/-! ## The view loses the member -/

theorem rfvDo_members (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (x : Bool) :
    (rfvDo e n now m c x).1.members = n.members.erase m := by
  unfold rfvDo
  repeat' split
  all_goals simp

theorem removeFromView_members_some (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (src : Source) (x : Bool)
    (hold : src.hold = false) (hq : ¬(now < n.quietUntil ∧ n.recheck.len < MAX_TABLE)) :
    (N.removeFromView e n now m (some c) src x).1.members = n.members.erase m := by
  rw [removeFromView_eq e n now m c src x hold hq]; exact rfvDo_members ..

/-- The node after `H`'s copy lost the entry: what the next steps read. -/
theorem rcdown_core (e : Env) (n : N) (now H m : Nat) (rc : Rec) (c : HubCopy) (hrev : n.revoked.has m = false)
    (hs : Srt n.hv) (hH : n.hv.get? H = some c)
    (hent : ∀ x, c.entries.get? m = some x → x.rc.inc / 65536 ≤ rc.inc / 65536)
    (hothers : ∀ p ∈ n.hv, p.1 ≠ H → n.eligible now (n.source now) p.1 = true → p.2.entries.get? m = none) :
    ∃ n2 : N, n2.members = n.members ∧ n2.quietUntil = n.quietUntil ∧ n2.recheck = n.recheck ∧ n2.regrace = n.regrace ∧
      n2.isHub = n.isHub ∧
      n2.homed = n.homed ∧ n2.revoked = n.revoked ∧ n2.me = n.me ∧ n2.left = n.left ∧ n2.source now = n.source now ∧
      (n2.candidates now (n2.source now) m).1 = none ∧
      N.applyDeltaCore e n now H m rc .down =
        (let r := N.recomputeOne e n2 now m; if r.2 = true then r.1.bump else r.1) := by
  obtain ⟨hv', hkeys, hH', hex, heq⟩ := applyDeltaCore_down_eq e n now H m rc c hrev hs hH hent
  have hsrc : ({ n with hv := hv' } : N).source now = n.source now := source_hv n hv' now hkeys
  refine ⟨{ n with hv := hv' }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hsrc, ?_, heq⟩
  rw [candidates_none_iff]
  intro p hp ce hl
  obtain ⟨he, hg, _⟩ := hl
  by_cases hpH : p.1 = H
  · have := hH' p hp hpH; rw [this] at hg; cases hg
  · have hpn := hex p hp hpH
    have := hothers p hpn hpH (by rw [hsrc] at he; exact he)
    rw [this] at hg; cases hg

/-- **The copy loses the entry.** A `Down` for `m` from `H` at the same or a newer epoch than the entry of `H`'s copy removes the
entry from the copy: when `apply_delta` returns, the copy of `H` does not list `m`. -/
theorem applyDeltaCore_down_copy (e : Env) (n : N) (now H m : Nat) (rc : Rec) (c : HubCopy) (hrev : n.revoked.has m = false)
    (hs : Srt n.hv) (hH : n.hv.get? H = some c)
    (hent : ∀ x, c.entries.get? m = some x → x.rc.inc / 65536 ≤ rc.inc / 65536) :
    ∀ p ∈ (N.applyDeltaCore e n now H m rc .down).hv, p.1 = H → p.2.entries.get? m = none := by
  obtain ⟨hv', hkeys, hH', hex, heq⟩ := applyDeltaCore_down_eq e n now H m rc c hrev hs hH hent
  rw [heq]
  dsimp only
  have hk := recomputeOne_keeps2 e ({ n with hv := hv' } : N) now m
  generalize N.recomputeOne e ({ n with hv := hv' } : N) now m = R at hk
  obtain ⟨n3, ch⟩ := R
  simp only [] at hk ⊢
  have hhv : n3.hv = hv' := hk.1.1
  split
  · rw [bump_hv, hhv]; exact hH'
  · rw [hhv]; exact hH'

/-- **A Down delta removes the member from the view (property 2, view side).** A node receives `H`'s `Down` for `m`, at the
same or a newer epoch than its copy's entry. No other eligible copy lists `m`, the source does not hold removals, and no
quiet window is open: `m` is no longer in the view when the call returns. -/
theorem applyDeltaCore_down_removes (e : Env) (n : N) (now H m : Nat) (rc : Rec) (c : HubCopy) (hrev : n.revoked.has m = false)
    (hs : Srt n.hv) (hH : n.hv.get? H = some c)
    (hent : ∀ x, c.entries.get? m = some x → x.rc.inc / 65536 ≤ rc.inc / 65536)
    (hothers : ∀ p ∈ n.hv, p.1 ≠ H → n.eligible now (n.source now) p.1 = true → p.2.entries.get? m = none)
    (hhold : (n.source now).hold = false) (hq : ¬(now < n.quietUntil ∧ n.recheck.len < MAX_TABLE)) :
    (N.applyDeltaCore e n now H m rc .down).members.get? m = none := by
  obtain ⟨n2, hm2, hq2, hr2, -, -, -, -, -, -, hsrc, hcand, heq⟩ := rcdown_core e n now H m rc c hrev hs hH hent hothers
  rw [heq]
  dsimp only
  rw [recomputeOne_none e n2 now m hcand]
  have hm : (N.removeFromView e n2 now m (n2.members.get? m) (n2.source now)
      (n2.candidates now (n2.source now) m).2).1.members.get? m = none := by
    cases hcur : n2.members.get? m with
    | none => unfold N.removeFromView; exact hcur
    | some c0 =>
      rw [removeFromView_members_some e n2 now m c0 _ _ (by rw [hsrc]; exact hhold) (by rw [hq2, hr2]; exact hq)]
      exact AMap.get?_erase_self _ _
  split
  · rw [bump_members]; exact hm
  · exact hm

/-- With a quiet window open (and room in the recheck table) the removal is deferred: the view is unchanged and the member is
queued for `recheck_due`, at the window's end with the window's grace state unless it already waits (#284). -/
theorem applyDeltaCore_down_defers (e : Env) (n : N) (now H m : Nat) (rc : Rec) (c : HubCopy) (hrev : n.revoked.has m = false)
    (hs : Srt n.hv) (hH : n.hv.get? H = some c)
    (hent : ∀ x, c.entries.get? m = some x → x.rc.inc / 65536 ≤ rc.inc / 65536)
    (hothers : ∀ p ∈ n.hv, p.1 ≠ H → n.eligible now (n.source now) p.1 = true → p.2.entries.get? m = none)
    (hhold : (n.source now).hold = false) (hq : now < n.quietUntil ∧ n.recheck.len < MAX_TABLE)
    (c0 : ViewEntry) (hcur : n.members.get? m = some c0) :
    (N.applyDeltaCore e n now H m rc .down).members = n.members ∧
    (N.applyDeltaCore e n now H m rc .down).recheck = n.recheck.orIns m (n.quietUntil, n.regrace) := by
  obtain ⟨n2, hm2, hq2, hr2, hg2, -, -, -, -, -, hsrc, hcand, heq⟩ := rcdown_core e n now H m rc c hrev hs hH hent hothers
  rw [heq]
  dsimp only
  rw [recomputeOne_none e n2 now m hcand]
  have h2 : n2.members.get? m = some c0 := by rw [hm2]; exact hcur
  rw [h2]
  obtain ⟨h4, h5, h6⟩ := removeFromView_defers e n2 now m c0 (n2.source now) (n2.candidates now (n2.source now) m).2
    (by rw [hsrc]; exact hhold) (by rw [hq2]; exact hq.1) (by rw [hr2]; exact hq.2)
  rw [if_neg (by simp [h6])]
  rw [h4, h5, hm2, hr2, hq2, hg2]
  exact ⟨rfl, rfl⟩


/-! ## A hub that removes the member from its view tells the homed members -/

theorem bump_outSent (n : N) : n.bump.outSent = n.outSent := by unfold N.bump; simp

theorem homeDelta_loop_mem (e : Env) (m : Nat) (rc : Rec) (a : Alive) (ks : List Nat) :
    ∀ (n : N) (p : Nat), p ∈ ks → p ≠ m → n.revoked.has p = false → p ≠ n.me →
      (p, Route.session, NFrame.delta m rc a, e.acc.has p) ∈
        (forKeys ks (fun p n => if p != m then N.deltaTo e n p m rc a else n) n).outSent := by
  induction ks with
  | nil => intro n p hp; simp at hp
  | cons k r ih =>
    intro n p hp hpm hr hme
    unfold forKeys
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with h | h
    · subst h
      have hmem : (p, Route.session, NFrame.delta m rc a, e.acc.has p) ∈
          (if p != m then N.deltaTo e n p m rc a else n).outSent := by
        rw [if_pos (by simp [hpm])]
        exact tx_mem e n p .session _ hr hme
      exact sent_mem_of_ps (forKeys_ps r _ (fun k n => by split; exact deltaTo_ps ..; exact PS_refl n) _) _ hmem
    · have hk : ∀ k n, (if k != m then N.deltaTo e n k m rc a else n).revoked = n.revoked ∧
          (if k != m then N.deltaTo e n k m rc a else n).me = n.me := by
        intro k n; split <;> simp
      obtain ⟨h2, h3⟩ := hk k n
      exact ih _ p h hpm (by rw [h2]; exact hr) (by rw [h3]; exact hme)

theorem homeDelta_mem (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) (p : Nat) (hp : p ∈ n.homed.keys) (hpm : p ≠ m)
    (hr : n.revoked.has p = false) (hme : p ≠ n.me) :
    (p, Route.session, NFrame.delta m rc a, e.acc.has p) ∈ (N.homeDelta e n m rc a).outSent := by
  unfold N.homeDelta
  exact homeDelta_loop_mem e m rc a n.homed.keys n p hp hpm hr hme

theorem tail_sent (nn : N) (t : Tr) (ev : Ev) (e : Env) (m : Nat) (rc : Rec) (a : Alive) (p : Nat)
    (hh : nn.isHub = true) (hp : p ∈ nn.homed.keys) (hpm : p ≠ m) (hr : nn.revoked.has p = false) (hme : p ≠ nn.me) :
    (p, Route.session, NFrame.delta m rc a, e.acc.has p) ∈
      (if ((nn.trace t).emit ev).isHub = true then N.homeDelta e ((nn.trace t).emit ev) m rc a else (nn.trace t).emit ev).outSent := by
  have h1 : ((nn.trace t).emit ev).isHub = true := by simpa using hh
  rw [if_pos h1]
  exact homeDelta_mem e _ m rc a p (by simpa using hp) hpm (by simpa using hr) (by simpa using hme)

theorem rfvDo_homes (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (x : Bool) (hh : n.isHub = true)
    (hl : n.left.has m = false) (p : Nat) (hp : p ∈ n.homed.keys) (hpm : p ≠ m) (hr : n.revoked.has p = false)
    (hme : p ≠ n.me) :
    (p, Route.session, NFrame.delta m c.rc .down, e.acc.has p) ∈ (rfvDo e n now m c x).1.outSent := by
  unfold rfvDo
  dsimp only
  cases x <;> by_cases hg : (n.goneVer.len < MAX_TABLE || n.goneVer.has m) = true <;>
    simp only [hg, hl, if_true, if_false, Bool.false_eq_true, ite_true, ite_false, Bool.or_true, Bool.true_or] <;>
    exact tail_sent _ _ _ e m c.rc _ p (by simpa using hh) (by simpa using hp) hpm (by simpa using hr) (by simpa using hme)

/-- **The hub tells the homed members (property 2, hub side).** A hub that removes `m` from its view because of a `Down` of
its own copy hands a `Down` delta for `m`, with the record the view held, to the session of every homed member. -/
theorem applyDeltaCore_down_homes (e : Env) (n : N) (now H m : Nat) (rc : Rec) (c : HubCopy) (hrev : n.revoked.has m = false)
    (hs : Srt n.hv) (hH : n.hv.get? H = some c)
    (hent : ∀ x, c.entries.get? m = some x → x.rc.inc / 65536 ≤ rc.inc / 65536)
    (hothers : ∀ p ∈ n.hv, p.1 ≠ H → n.eligible now (n.source now) p.1 = true → p.2.entries.get? m = none)
    (hhold : (n.source now).hold = false) (hq : ¬(now < n.quietUntil ∧ n.recheck.len < MAX_TABLE))
    (hhub : n.isHub = true) (c0 : ViewEntry) (hcur : n.members.get? m = some c0) (hleft : n.left.has m = false)
    (p : Nat) (hp : p ∈ n.homed.keys) (hpm : p ≠ m) (hr : n.revoked.has p = false) (hme : p ≠ n.me) :
    (p, Route.session, NFrame.delta m c0.rc .down, e.acc.has p) ∈ (N.applyDeltaCore e n now H m rc .down).outSent := by
  obtain ⟨n2, hm2, hq2, hr2, -, hh2, hho2, hrv2, hme2, hl2, hsrc, hcand, heq⟩ := rcdown_core e n now H m rc c hrev hs hH hent hothers
  rw [heq]
  dsimp only
  rw [recomputeOne_none e n2 now m hcand]
  have h2 : n2.members.get? m = some c0 := by rw [hm2]; exact hcur
  rw [h2]
  rw [removeFromView_eq e n2 now m c0 _ _ (by rw [hsrc]; exact hhold) (by rw [hq2, hr2]; exact hq)]
  have hmem := rfvDo_homes e n2 now m c0 (n2.candidates now (n2.source now) m).2 (by rw [hh2]; exact hhub)
    (by rw [hl2]; exact hleft) p (by rw [hho2]; exact hp) hpm (by rw [hrv2]; exact hr) (by rw [hme2]; exact hme)
  split
  · rw [bump_outSent]; exact hmem
  · exact hmem

end Vinc.Membership.Cmp
