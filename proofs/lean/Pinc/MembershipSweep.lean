import Pinc.MembershipViewPrimary
import Pinc.MembershipTick

/-!
# Membership view: marking and sweeping omitted members (property 3c, 4)

`mark_absent` (a complete snapshot of a hub listed round `round`) and `sweep_absent` (every second, drop copy entries
whose omission lasted a lease) only ever act on the hub copies, and `recompute_one` never writes them, so each one is a
function of the copy table alone. This file proves exactly what they do to it:

* `markAbsent_marks_only_unlisted`: after `mark_absent` every entry of the hub's copy is as it was, except an entry of
  an earlier round with no mark yet, which carries the mark `now`; no other copy, no key, no round and no open flag
  changes. `markAbsent_marks_all_unlisted`: every such entry is marked.
* `sweepAbsent_only_expired`: after `sweep_absent` every entry of every copy is as it was, or gone; an entry that
  is gone had an omission mark older than `LEASE` (`expiredAbs`). `sweepAbsent_removes_expired`: no entry with such a
  mark remains in a copy.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Pinc.Membership
open Pinc.MemInc

/-- The entry of hub `hub` for `m`. -/
def entryOf (hv : AMap HubCopy) (hub m : Nat) : Option CopyEntry := (hv.get? hub).bind (fun c => c.entries.get? m)

/-- The step of `mark_absent`'s loop on the copy table. -/
def maHv (now hub round : Nat) (hv : AMap HubCopy) (m : Nat) : AMap HubCopy :=
  match entryOf hv hub m with
  | some ce =>
    if ce.round != round && ce.absentSince.isNone then
      match hv.get? hub with
      | some c => hv.insert hub { c with entries := c.entries.modify m (fun x => { x with absentSince := some now }) }
      | none => hv
    else hv
  | none => hv

theorem markAbsent_hv_step (e : Env) (now hub round : Nat) (a : N × Bool) (m : Nat) :
    ((fun (a : N × Bool) m =>
      let (n, changed) := a
      match (n.hv.get? hub).bind (fun c => c.entries.get? m) with
      | some ce =>
        if ce.round != round && ce.absentSince.isNone then
          let n := match n.hv.get? hub with
            | some c => { n with hv := n.hv.insert hub { c with entries := c.entries.modify m (fun x => { x with absentSince := some now }) } }
            | none => n
          let n := (n.noteAbsent now).trace (.absent m)
          let (n, ch) := N.recomputeOne e n now m
          (n, changed || ch)
        else a
      | none => a) a m).1.hv = maHv now hub round a.1.hv m := by
  obtain ⟨n1, c1⟩ := a
  simp only [maHv, entryOf]
  cases hg : (n1.hv.get? hub).bind (fun c => c.entries.get? m) with
  | none => rfl
  | some ce =>
    simp only []
    by_cases h : (ce.round != round && ce.absentSince.isNone) = true
    · simp only [h, if_true]
      cases hh : n1.hv.get? hub with
      | none => simp [hh] at hg
      | some c =>
        simp only []
        have := (recomputeOne_keeps2 e (((({ n1 with hv := n1.hv.insert hub { c with entries := c.entries.modify m (fun x => { x with absentSince := some now }) } }) : N).noteAbsent now).trace (.absent m)) now m).1.1
        simp only [trace_hv] at this
        exact this
    · simp [h]

theorem foldl_proj {α β : Type} (g : α → β) (G : β → Nat → β) (f : α → Nat → α) (h : ∀ a m, g (f a m) = G (g a) m)
    (ks : List Nat) (a : α) : g (ks.foldl f a) = ks.foldl G (g a) := by
  induction ks generalizing a with
  | nil => rfl
  | cons k r ih => simp only [List.foldl_cons]; rw [ih, h]

/-- The copy table `mark_absent` leaves: the fold of `maHv` over the keys of the hub's copy at the start. -/
theorem markAbsent_hv (e : Env) (n : N) (now hub round : Nat) :
    (N.markAbsent e n now hub round).1.hv =
      (match n.hv.get? hub with | some c => c.entries.keys | none => []).foldl (maHv now hub round) n.hv := by
  unfold N.markAbsent
  exact foldl_proj (fun a : N × Bool => a.1.hv) (maHv now hub round) _ (fun a m => markAbsent_hv_step e now hub round a m) _ _

/-- What the loop has done to the copy table so far, relative to the table `hv0` at its start. -/
def MaInv (now hub round : Nat) (hv0 cur : AMap HubCopy) : Prop :=
  (∀ h, h ≠ hub → cur.get? h = hv0.get? h) ∧
  (hv0.get? hub = none → cur.get? hub = none) ∧
  (∀ c0, hv0.get? hub = some c0 → ∃ c, cur.get? hub = some c ∧ c.round = c0.round ∧ c.open_ = c0.open_ ∧
    c.entries.keys = c0.entries.keys ∧
    ∀ m, c.entries.get? m = c0.entries.get? m ∨
      ∃ ce, c0.entries.get? m = some ce ∧ ce.round ≠ round ∧ ce.absentSince = none ∧
        c.entries.get? m = some { ce with absentSince := some now })

theorem MaInv.refl (now hub round : Nat) (hv : AMap HubCopy) : MaInv now hub round hv hv :=
  ⟨fun _ _ => rfl, id, fun c0 h => ⟨c0, h, rfl, rfl, rfl, fun m => Or.inl rfl⟩⟩

theorem maHv_inv (now hub round : Nat) (hv0 cur : AMap HubCopy) (m : Nat) (h : MaInv now hub round hv0 cur) :
    MaInv now hub round hv0 (maHv now hub round cur m) := by
  obtain ⟨hA, hN, hB⟩ := h
  unfold maHv entryOf
  cases hg : cur.get? hub with
  | none => simp only [hg, Option.bind_none]; exact ⟨hA, hN, hB⟩
  | some c =>
    simp only [hg, Option.bind_some]
    cases he : c.entries.get? m with
    | none => simp only []; exact ⟨hA, hN, hB⟩
    | some ce =>
      simp only []
      by_cases hc : (ce.round != round && ce.absentSince.isNone) = true
      · simp only [hc, if_true, hg]
        have hc' := hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none] at hc'
        obtain ⟨hr, ha⟩ := hc'
        refine ⟨fun h' hh => ?_, fun h0 => ?_, fun c0 h0 => ?_⟩
        · rw [AMap.get?_insert_ne _ _ _ _ hh]; exact hA h' hh
        · rw [hN h0] at hg; cases hg
        · obtain ⟨c', hc', r1, o1, k1, hm⟩ := hB c0 h0
          rw [hg] at hc'; injection hc' with hc'; subst hc'
          refine ⟨_, AMap.get?_insert_self _ _ _, r1, o1, ?_, fun m' => ?_⟩
          · simp [AMap.modify_keys, k1]
          · by_cases hmm : m' = m
            · subst hmm
              simp only [AMap.get?_modify_self, he, Option.map_some]
              rcases hm m' with h1 | ⟨ce0, h1, h2, h3, h4⟩
              · right; rw [he] at h1; exact ⟨ce, h1.symm, hr, ha, rfl⟩
              · rw [he] at h4; injection h4 with h4; subst h4; simp at ha
            · simp only [AMap.get?_modify_ne _ _ _ _ hmm]; exact hm m'
      · simp only [hc, if_false]; exact ⟨hA, hN, hB⟩

theorem maHv_fold_inv (now hub round : Nat) (hv0 : AMap HubCopy) (ks : List Nat) :
    MaInv now hub round hv0 (ks.foldl (maHv now hub round) hv0) :=
  foldl_inv (MaInv now hub round hv0) _ ks hv0 (fun b a hb => maHv_inv now hub round hv0 b a hb) (MaInv.refl _ _ _ _)

/-- After `mark_absent`, the hub's copy holds the same entries, except that an entry of an earlier round that carried
no mark is marked with `now`: an entry listed in this round, or marked before, is as it was. No other copy, no key, no
round and no open flag changes. -/
theorem markAbsent_marks_only_unlisted (e : Env) (n : N) (now hub round : Nat) :
    (∀ h, h ≠ hub → (N.markAbsent e n now hub round).1.hv.get? h = n.hv.get? h) ∧
    (n.hv.get? hub = none → (N.markAbsent e n now hub round).1.hv.get? hub = none) ∧
    (∀ c0, n.hv.get? hub = some c0 → ∃ c, (N.markAbsent e n now hub round).1.hv.get? hub = some c ∧ c.round = c0.round ∧
      c.open_ = c0.open_ ∧ c.entries.keys = c0.entries.keys ∧
      ∀ m, c.entries.get? m = c0.entries.get? m ∨
        ∃ ce, c0.entries.get? m = some ce ∧ ce.round ≠ round ∧ ce.absentSince = none ∧
          c.entries.get? m = some { ce with absentSince := some now }) := by
  rw [markAbsent_hv]
  exact maHv_fold_inv now hub round n.hv _

/-- Once marked, an entry is not touched again by the loop. -/
theorem maHv_marked (now hub round : Nat) (hv : AMap HubCopy) (m k : Nat) (ce : CopyEntry) (t : Nat)
    (h : entryOf hv hub m = some ce) (ht : ce.absentSince = some t) : entryOf (maHv now hub round hv k) hub m = some ce := by
  unfold maHv
  cases hk : entryOf hv hub k with
  | none => simp only [hk]; exact h
  | some cek =>
    simp only [hk]
    by_cases hc : (cek.round != round && cek.absentSince.isNone) = true
    · simp only [hc, if_true]
      cases hg : hv.get? hub with
      | none => exact h
      | some c =>
        simp only []
        by_cases hkm : k = m
        · subst hkm
          rw [hk] at h; injection h with h; subst h; rw [ht] at hc; simp at hc
        · unfold entryOf at h ⊢
          rw [AMap.get?_insert_self]
          simp only [Option.bind_some, AMap.get?_modify_ne _ _ _ _ (Ne.symm hkm)]
          rw [hg] at h; exact h
    · simp only [hc, if_false]; exact h

theorem maHv_other (now hub round : Nat) (hv : AMap HubCopy) (m k : Nat) (hkm : k ≠ m) :
    entryOf (maHv now hub round hv k) hub m = entryOf hv hub m := by
  unfold maHv
  cases hk : entryOf hv hub k with
  | none => simp only [hk]
  | some cek =>
    simp only [hk]
    by_cases hc : (cek.round != round && cek.absentSince.isNone) = true
    · simp only [hc, if_true]
      cases hg : hv.get? hub with
      | none => rfl
      | some c =>
        simp only []
        unfold entryOf
        rw [AMap.get?_insert_self]
        simp only [Option.bind_some, AMap.get?_modify_ne _ _ _ _ (Ne.symm hkm), hg]
    · simp [hc]

theorem maHv_done (now hub round : Nat) (ks : List Nat) (hv : AMap HubCopy) :
    ∀ m, m ∈ ks → ∀ ce, entryOf hv hub m = some ce → ce.round ≠ round → ce.absentSince = none →
      entryOf (ks.foldl (maHv now hub round) hv) hub m = some { ce with absentSince := some now } := by
  induction ks generalizing hv with
  | nil => intro m hm; exact absurd hm (by simp)
  | cons k r ih =>
    intro m hm ce he hr ha
    simp only [List.foldl_cons]
    by_cases hkm : k = m
    · subst hkm
      have h1 : entryOf (maHv now hub round hv k) hub k = some { ce with absentSince := some now } := by
        have hc : (ce.round != round && ce.absentSince.isNone) = true := by simp [hr, ha]
        simp only [maHv, he]
        rw [if_pos hc]
        cases hg : hv.get? hub with
        | none => simp [entryOf, hg] at he
        | some c =>
          simp only []
          unfold entryOf
          rw [AMap.get?_insert_self]
          simp [entryOf, hg] at he
          simp [AMap.get?_modify_self, he]
      -- marked entries stay as they are
      have : ∀ (r : List Nat) (hv' : AMap HubCopy), entryOf hv' hub k = some { ce with absentSince := some now } →
          entryOf (r.foldl (maHv now hub round) hv') hub k = some { ce with absentSince := some now } := by
        intro r
        induction r with
        | nil => intro hv' h; exact h
        | cons k' r' ih' => intro hv' h; simp only [List.foldl_cons]; exact ih' _ (maHv_marked now hub round hv' k k' _ _ h rfl)
      exact this r _ h1
    · have hm' : m ∈ r := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h.symm hkm
        · exact h
      exact ih _ m hm' ce (by rw [maHv_other now hub round hv m k hkm]; exact he) hr ha

/-- Every entry of an earlier round with no mark is marked. -/
theorem markAbsent_marks_all_unlisted (e : Env) (n : N) (now hub round : Nat) (c0 : HubCopy) (h0 : n.hv.get? hub = some c0)
    (m : Nat) (ce : CopyEntry) (he : c0.entries.get? m = some ce) (hr : ce.round ≠ round) (ha : ce.absentSince = none) :
    ∃ c, (N.markAbsent e n now hub round).1.hv.get? hub = some c ∧ c.entries.get? m = some { ce with absentSince := some now } := by
  have hmem : m ∈ (match n.hv.get? hub with | some c => c.entries.keys | none => []) := by
    rw [h0]; exact (AMap.has_keys _ _).1 (AMap.get?_has _ _ _ he)
  have := maHv_done now hub round _ n.hv m hmem ce (by simp [entryOf, h0, he]) hr ha
  rw [← markAbsent_hv e n now hub round] at this
  unfold entryOf at this
  cases hg : (N.markAbsent e n now hub round).1.hv.get? hub with
  | none => rw [hg] at this; simp at this
  | some c => rw [hg] at this; exact ⟨c, rfl, by simpa using this⟩

/-! ## `sweep_absent` -/

/-- The step of `sweep_absent`'s inner loop on the copy table. -/
def swHv (now hub : Nat) (hv : AMap HubCopy) (m : Nat) : AMap HubCopy :=
  if (match entryOf hv hub m with | some ce => expiredAbs now ce | none => false) = true then
    match hv.get? hub with
    | some c => hv.insert hub { c with entries := c.entries.erase m }
    | none => hv
  else hv

/-- The inner loop over the entries of copy `hub`, as the table sees it when the loop starts. -/
def swInner (now hub : Nat) (hv : AMap HubCopy) : AMap HubCopy :=
  (match hv.get? hub with | some c => c.entries.keys | none => []).foldl (swHv now hub) hv

/-- The body of the inner loop of `sweep_absent`. -/
def swIn (e : Env) (now hub : Nat) (a : N × Bool) (m : Nat) : N × Bool :=
  let (n, changed) := a
  let expired := match (n.hv.get? hub).bind (fun c => c.entries.get? m) with
    | some ce => (match ce.absentSince with | some t => decide (LEASE ≤ now - t) | none => false)
    | none => false
  if expired then
    let (n, ch) := N.recomputeOne e n now m
    let n := match n.hv.get? hub with
      | some c => { n with hv := n.hv.insert hub { c with entries := c.entries.erase m } }
      | none => n
    (n, changed || ch)
  else (n.keepAbsent hub m, changed)

/-- The body of the outer loop of `sweep_absent`. -/
def swOut (e : Env) (now : Nat) (a : N × Bool) (hub : Nat) : N × Bool :=
  (match a.1.hv.get? hub with | some c => c.entries.keys | none => []).foldl (swIn e now hub) a

theorem sweepAbsent_eq (e : Env) (n : N) (now : Nat) :
    N.sweepAbsent e n now =
      (let n0 : N := { n with nextAbsent := none }
       let (n, changed) := n0.hv.keys.foldl (swOut e now) (n0, false); if changed then n.bump else n) := rfl

theorem swIn_hv (e : Env) (now hub : Nat) (a : N × Bool) (m : Nat) : (swIn e now hub a m).1.hv = swHv now hub a.1.hv m := by
  obtain ⟨n1, c1⟩ := a
  unfold swIn
  simp only [swHv, entryOf]
  have hk := (recomputeOne_keeps2 e n1 now m).1.1
  by_cases hx : (match (n1.hv.get? hub).bind (fun c => c.entries.get? m) with
          | some ce => (match ce.absentSince with | some t => decide (LEASE ≤ now - t) | none => false)
          | none => false) = true
  · have hx' : (match (n1.hv.get? hub).bind (fun c => c.entries.get? m) with | some ce => expiredAbs now ce | none => false) = true := by
      cases hh : (n1.hv.get? hub).bind (fun c => c.entries.get? m) with
      | none => rw [hh] at hx; simp at hx
      | some ce => rw [hh] at hx; exact hx
    simp only [hx, hx', if_true]
    cases hh : n1.hv.get? hub with
    | none => simp [hk, hh]
    | some c =>
      simp only [hk, hh]
  · have hx' : ¬ (match (n1.hv.get? hub).bind (fun c => c.entries.get? m) with | some ce => expiredAbs now ce | none => false) = true := by
      intro h'
      apply hx
      cases hh : (n1.hv.get? hub).bind (fun c => c.entries.get? m) with
      | none => rw [hh] at h'; simp at h'
      | some ce => rw [hh] at h'; exact h'
    simp [hx, hx']

theorem swOut_hv (e : Env) (now : Nat) (a : N × Bool) (hub : Nat) : (swOut e now a hub).1.hv = swInner now hub a.1.hv := by
  unfold swOut swInner
  exact foldl_proj (fun a : N × Bool => a.1.hv) (swHv now hub) _ (fun a m => swIn_hv e now hub a m) _ _

theorem sweepAbsent_hv (e : Env) (n : N) (now : Nat) :
    (N.sweepAbsent e n now).hv = n.hv.keys.foldl (fun hv hub => swInner now hub hv) n.hv := by
  rw [sweepAbsent_eq]
  have := foldl_proj (fun a : N × Bool => a.1.hv) (fun hv hub => swInner now hub hv) (swOut e now) (fun a hub => swOut_hv e now a hub) n.hv.keys ({ n with nextAbsent := none }, false)
  simp only [] at this
  dsimp only
  rw [← this]
  generalize n.hv.keys.foldl (swOut e now) ({ n with nextAbsent := none }, false) = F
  obtain ⟨f1, f2⟩ := F
  by_cases h : f2 = true <;> simp [h, bump_hv]

/-- What the sweep has done so far, relative to the table `hv0` at its start. -/
def SwInv (now : Nat) (hv0 cur : AMap HubCopy) : Prop :=
  (∀ hub m ce, entryOf cur hub m = some ce → entryOf hv0 hub m = some ce) ∧
  (∀ hub m ce, entryOf hv0 hub m = some ce → entryOf cur hub m = none → expiredAbs now ce = true) ∧
  (∀ hub c, cur.get? hub = some c → ∃ c0, hv0.get? hub = some c0 ∧ c.round = c0.round ∧ c.open_ = c0.open_) ∧
  (∀ hub c0, hv0.get? hub = some c0 → ∃ c, cur.get? hub = some c)

theorem SwInv.refl (now : Nat) (hv : AMap HubCopy) : SwInv now hv hv :=
  ⟨fun _ _ _ h => h, fun hub m ce h h' => (by rw [h] at h'; cases h'),
   fun hub c h => ⟨c, h, rfl, rfl⟩, fun hub c0 h => ⟨c0, h⟩⟩

theorem swHv_inv (now hub : Nat) (hv0 cur : AMap HubCopy) (m : Nat) (h : SwInv now hv0 cur) :
    SwInv now hv0 (swHv now hub cur m) := by
  obtain ⟨hA, hB, hC, hD⟩ := h
  unfold swHv
  by_cases hx : (match entryOf cur hub m with | some ce => expiredAbs now ce | none => false) = true
  · rw [if_pos hx]
    cases hg : cur.get? hub with
    | none => exact ⟨hA, hB, hC, hD⟩
    | some c =>
      simp only []
      have hex : ∃ ce, entryOf cur hub m = some ce ∧ expiredAbs now ce = true := by
        cases hh : entryOf cur hub m with
        | none => rw [hh] at hx; simp at hx
        | some ce => rw [hh] at hx; exact ⟨ce, rfl, hx⟩
      obtain ⟨ce, hce, hxe⟩ := hex
      have key : ∀ hub' m', entryOf (cur.insert hub { c with entries := c.entries.erase m }) hub' m' =
          if hub' = hub ∧ m' = m then none else entryOf cur hub' m' := by
        intro hub' m'
        by_cases h1 : hub' = hub
        · subst h1
          by_cases h2 : m' = m
          · subst h2; simp [entryOf, AMap.get?_insert_self, AMap.get?_erase_self]
          · simp [entryOf, AMap.get?_insert_self, AMap.get?_erase_ne _ _ _ h2, hg, h2]
        · simp [entryOf, AMap.get?_insert_ne _ _ _ _ h1, h1]
      refine ⟨fun hub' m' ce' h' => ?_, fun hub' m' ce' h' h'' => ?_, fun hub' c' h' => ?_, fun hub' c0 h' => ?_⟩
      · rw [key] at h'
        split at h'
        · cases h'
        · exact hA _ _ _ h'
      · rw [key] at h''
        by_cases hhm : hub' = hub ∧ m' = m
        · obtain ⟨rfl, rfl⟩ := hhm
          have := hA _ _ _ hce
          rw [h'] at this; injection this with this; subst this; exact hxe
        · rw [if_neg hhm] at h''; exact hB _ _ _ h' h''
      · by_cases h1 : hub' = hub
        · subst h1
          rw [AMap.get?_insert_self] at h'; injection h' with h'; subst h'
          obtain ⟨c0, h0, r, o⟩ := hC _ _ hg
          exact ⟨c0, h0, r, o⟩
        · rw [AMap.get?_insert_ne _ _ _ _ h1] at h'; exact hC _ _ h'
      · by_cases h1 : hub' = hub
        · subst h1; exact ⟨_, AMap.get?_insert_self _ _ _⟩
        · rw [AMap.get?_insert_ne _ _ _ _ h1]; exact hD _ _ h'
  · rw [if_neg hx]; exact ⟨hA, hB, hC, hD⟩

theorem swInner_inv (now hub : Nat) (hv0 hv : AMap HubCopy) (h : SwInv now hv0 hv) : SwInv now hv0 (swInner now hub hv) := by
  unfold swInner
  exact foldl_inv (SwInv now hv0) _ _ hv (fun b a hb => swHv_inv now hub hv0 b a hb) h

theorem sweepHv_inv (now : Nat) (hv0 : AMap HubCopy) : SwInv now hv0 (hv0.keys.foldl (fun hv hub => swInner now hub hv) hv0) :=
  foldl_inv (SwInv now hv0) _ hv0.keys hv0 (fun b a hb => swInner_inv now a hv0 b hb) (SwInv.refl _ _)

/-- After `sweep_absent`, every entry of every copy is as it was, or gone; an entry that is gone had an omission mark
older than `LEASE`. The copies, their rounds and their open flags are kept. -/
theorem sweepAbsent_only_expired (e : Env) (n : N) (now : Nat) :
    (∀ hub m ce, entryOf (N.sweepAbsent e n now).hv hub m = some ce → entryOf n.hv hub m = some ce) ∧
    (∀ hub m ce, entryOf n.hv hub m = some ce → entryOf (N.sweepAbsent e n now).hv hub m = none → expiredAbs now ce = true) ∧
    (∀ hub c, (N.sweepAbsent e n now).hv.get? hub = some c → ∃ c0, n.hv.get? hub = some c0 ∧ c.round = c0.round ∧ c.open_ = c0.open_) ∧
    (∀ hub c0, n.hv.get? hub = some c0 → ∃ c, (N.sweepAbsent e n now).hv.get? hub = some c) := by
  rw [sweepAbsent_hv]
  exact sweepHv_inv now n.hv

/-! ### Nothing expired survives -/

/-- Copy `hub` holds no entry whose omission lasted a lease. -/
def NoExp (now hub : Nat) (hv : AMap HubCopy) : Prop := ∀ m ce, entryOf hv hub m = some ce → expiredAbs now ce = false

theorem swHv_sub (now h'' : Nat) (hv : AMap HubCopy) (k h m : Nat) (ce : CopyEntry)
    (hh : entryOf (swHv now h'' hv k) h m = some ce) : entryOf hv h m = some ce := by
  have := (swHv_inv now h'' hv hv k (SwInv.refl now hv)).1 h m ce hh
  exact this

theorem swFold_sub (now h'' : Nat) (ks : List Nat) (hv : AMap HubCopy) (h m : Nat) (ce : CopyEntry)
    (hh : entryOf (ks.foldl (swHv now h'') hv) h m = some ce) : entryOf hv h m = some ce := by
  induction ks generalizing hv with
  | nil => exact hh
  | cons k r ih => exact swHv_sub now h'' hv k h m ce (ih _ hh)

theorem swFold_noexp (now hub : Nat) (ks : List Nat) (hv : AMap HubCopy) :
    ∀ m ce, m ∈ ks → entryOf (ks.foldl (swHv now hub) hv) hub m = some ce → expiredAbs now ce = false := by
  induction ks generalizing hv with
  | nil => intro m ce hm; exact absurd hm (by simp)
  | cons k r ih =>
    intro m ce hm hf
    simp only [List.foldl_cons] at hf
    by_cases hmr : m ∈ r
    · exact ih _ m ce hmr hf
    · have hmk : m = k := by
        rcases List.mem_cons.mp hm with h | h
        · exact h
        · exact absurd h hmr
      subst hmk
      have h1 : entryOf (swHv now hub hv m) hub m = some ce := swFold_sub now hub r _ hub m ce hf
      unfold swHv at h1
      by_cases hx : (match entryOf hv hub m with | some ce => expiredAbs now ce | none => false) = true
      · rw [if_pos hx] at h1
        cases hg : hv.get? hub with
        | none => simp [entryOf, hg] at h1
        | some c => simp [entryOf, AMap.get?_insert_self, AMap.get?_erase_self, hg] at h1
      · rw [if_neg hx] at h1
        rw [h1] at hx; simpa using hx

theorem swInner_noexp (now hub : Nat) (hv : AMap HubCopy) (hhub : hv.get? hub ≠ none) : NoExp now hub (swInner now hub hv) := by
  intro m ce hf
  unfold swInner at hf
  have hsub := swFold_sub now hub _ hv hub m ce hf
  have hmem : m ∈ (match hv.get? hub with | some c => c.entries.keys | none => []) := by
    cases hg : hv.get? hub with
    | none => exact absurd hg hhub
    | some c => simp only [entryOf, hg, Option.bind_some] at hsub; exact (AMap.has_keys _ _).1 (AMap.get?_has _ _ _ hsub)
  exact swFold_noexp now hub _ hv m ce hmem hf

theorem swInner_keeps_noexp (now hub h : Nat) (hv : AMap HubCopy) (hn : NoExp now h hv) : NoExp now h (swInner now hub hv) := by
  intro m ce hf
  unfold swInner at hf
  exact hn m ce (swFold_sub now hub _ hv h m ce hf)

theorem sweepOuter_noexp (now hub : Nat) (K : List Nat) (hv : AMap HubCopy) (hK : hub ∈ K) (hhub : hv.get? hub ≠ none) :
    NoExp now hub (K.foldl (fun hv h => swInner now h hv) hv) := by
  induction K generalizing hv with
  | nil => exact absurd hK (by simp)
  | cons k r ih =>
    simp only [List.foldl_cons]
    have hpres : (swInner now k hv).get? hub ≠ none := by
      obtain ⟨c0, hc0⟩ := Option.ne_none_iff_exists'.1 hhub
      obtain ⟨c, hc⟩ := (swInner_inv now k hv hv (SwInv.refl now hv)).2.2.2 hub c0 hc0
      rw [hc]; simp
    by_cases hr : hub ∈ r
    · exact ih _ hr hpres
    · have hk : hub = k := by
        rcases List.mem_cons.mp hK with h | h
        · exact h
        · exact absurd h hr
      subst hk
      have h1 := swInner_noexp now hub hv hhub
      have : ∀ (r : List Nat) (hv' : AMap HubCopy), NoExp now hub hv' → NoExp now hub (r.foldl (fun hv h => swInner now h hv) hv') := by
        intro r
        induction r with
        | nil => intro hv' h; exact h
        | cons k' r' ih' => intro hv' h; simp only [List.foldl_cons]; exact ih' _ (swInner_keeps_noexp now k' hub hv' h)
      exact this r _ h1

/-- After `sweep_absent`, no copy lists a member whose omission lasted a lease: every such entry is gone. -/
theorem sweepAbsent_removes_expired (e : Env) (n : N) (now : Nat) (hub : Nat) (c : HubCopy)
    (hc : (N.sweepAbsent e n now).hv.get? hub = some c) (m : Nat) (ce : CopyEntry) (hm : c.entries.get? m = some ce) :
    expiredAbs now ce = false := by
  rw [sweepAbsent_hv] at hc
  obtain ⟨c0, h0, -, -⟩ := (sweepHv_inv now n.hv).2.2.1 hub c hc
  have hK : hub ∈ n.hv.keys := (AMap.has_keys _ _).1 (AMap.get?_has _ _ _ h0)
  have := sweepOuter_noexp now hub n.hv.keys n.hv hK (by rw [h0]; simp)
  exact this m ce (by simp [entryOf, hc, hm] <;> (rw [sweepAbsent_hv]; simp [hc, hm]))

end Pinc.Membership
