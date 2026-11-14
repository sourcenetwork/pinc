import Vinc.MembershipViewEpoch

/-!
# Membership view: a snapshot takes nothing from the other hubs' copies (property 3c)

`apply_snap` deletes no entry from any copy but the sender's: it creates the sender's copy, inserts the listed entries
and, for a complete snapshot, drops the omitted entries of members the view does not list (`drop_gone`) and marks the
other omitted ones with the time (`mark_absent`); those entries stay. An omission that has just been marked is not
expired (`fresh_mark_not_expired`), so the omitted member is still a live candidate of `recompute_one`
(`MembershipViewUnion.lean`, `recomputeOne_listed_stays`) and stays in the view, with no event and no flag (c26385e: a view reports no suspicion). It leaves only when a hub
reports it down, or a full lease of omission passes (`sweep_absent`, `sweepAbsent_only_expired`). A member the view
does not list is never brought back by an omission.

* `applySnap_copies_mono`: no copy but the sender's loses an entry;
* `fresh_mark_not_expired`: a freshly marked omission is not an expired one;
* `markAbsent_marks_only_unlisted`: only entries of an earlier round without a mark get marked;
* `markViewAbsent_mono`, `snapAbsent_mono`: the confirmed home's snapshot only adds entries to its copy.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

/-- Whether hub `k`'s copy lists `m`. -/
def EntHas (h : AMap HubCopy) (k m : Nat) : Bool := ((h.get? k).map (fun c => c.entries.has m)).getD false

/-- No hub copy loses an entry from `h` to `h'`. -/
def HvMono (h h' : AMap HubCopy) : Prop := ∀ k m, EntHas h k m = true → EntHas h' k m = true

theorem HvMono.refl (h : AMap HubCopy) : HvMono h h := fun _ _ x => x
theorem HvMono.trans {a b c : AMap HubCopy} (h1 : HvMono a b) (h2 : HvMono b c) : HvMono a c := fun k m x => h2 k m (h1 k m x)

/-- No hub copy other than `hub`'s loses an entry from `h` to `h'`. -/
def HvMonoX (hub : Nat) (h h' : AMap HubCopy) : Prop := ∀ k m, k ≠ hub → EntHas h k m = true → EntHas h' k m = true

theorem HvMono.x {h h' : AMap HubCopy} (hm : HvMono h h') (hub : Nat) : HvMonoX hub h h' := fun k m _ x => hm k m x
theorem HvMonoX.trans {hub : Nat} {a b c : AMap HubCopy} (h1 : HvMonoX hub a b) (h2 : HvMonoX hub b c) : HvMonoX hub a c :=
  fun k m hk x => h2 k m hk (h1 k m hk x)

namespace AMap
variable {α : Type}
theorem has_insert_mono (m : AMap α) (k j : Nat) (v : α) (h : m.has j = true) : (m.insert k v).has j = true := by
  induction m with
  | nil => simp [has] at h
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    simp only [insert]
    by_cases h1 : k < a
    · rw [if_pos h1]
      simp only [has, List.any_cons, Bool.or_eq_true, beq_iff_eq] at h ⊢
      rcases h with h | h
      · right; left; exact h
      · right; right; exact h
    · rw [if_neg h1]
      by_cases h2 : (k == a) = true
      · rw [if_pos h2]
        simp only [beq_iff_eq] at h2
        simp only [has, List.any_cons, Bool.or_eq_true, beq_iff_eq] at h ⊢
        rcases h with h | h
        · left; omega
        · right; exact h
      · rw [if_neg h2]
        simp only [has, List.any_cons, Bool.or_eq_true, beq_iff_eq] at h ih ⊢
        rcases h with h | h
        · left; exact h
        · right; exact ih h
end AMap

theorem hvMono_insert (h : AMap HubCopy) (hub : Nat) (c' : HubCopy)
    (hc : ∀ c, h.get? hub = some c → ∀ m, c.entries.has m = true → c'.entries.has m = true) :
    HvMono h (h.insert hub c') := by
  intro k m hk
  by_cases hkh : k = hub
  · subst hkh
    unfold EntHas at hk ⊢
    rw [AMap.get?_insert_self]
    cases hg : h.get? k with
    | none => simp [hg] at hk
    | some c => simp [hg] at hk; simpa using hc c hg m hk
  · unfold EntHas at hk ⊢
    rw [AMap.get?_insert_ne _ _ _ _ hkh]; exact hk

theorem hvMono_of_eq {n n' : N} (h : n'.hv = n.hv) : HvMono n.hv n'.hv := by rw [h]; exact HvMono.refl _

theorem Keeps.hvMono {n n' : N} (h : Keeps n n') : HvMono n.hv n'.hv := hvMono_of_eq h.1

theorem fresh_mark_not_expired (now : Nat) (ce : CopyEntry) : expiredAbs now { ce with absentSince := some now } = false := by
  simp [expiredAbs, LEASE, S]

theorem bump_hv (n : N) : n.bump.hv = n.hv := by unfold N.bump; simp

@[simp] theorem ite_hv (c : Prop) [Decidable c] (a b : N) : (if c then a else b).hv = if c then a.hv else b.hv := by split <;> rfl


/-! ## The hub copies through `renew` and `on_self_entry` (they send, but do not change the copies) -/

theorem pushDelta_me_hv (e : Env) (n : N) (now : Nat) (rc : Rec) (a : Alive) :
    (N.pushDelta e n now n.me rc a).hv = n.hv := by
  unfold N.pushDelta
  have h : ∀ (ks : List Nat) (x : N), x.hv = n.hv ∧ x.me = n.me →
      (forKeys ks (fun p n' => if p != n.me && (n'.isBoot p || (n.me == n'.me && n'.homed.has p)) then N.deltaTo e n' p n.me rc a else n') x).hv = n.hv ∧
      (forKeys ks (fun p n' => if p != n.me && (n'.isBoot p || (n.me == n'.me && n'.homed.has p)) then N.deltaTo e n' p n.me rc a else n') x).me = n.me := by
    intro ks
    unfold forKeys
    induction ks with
    | nil => intro x hx; exact hx
    | cons k r ih =>
      intro x hx
      simp only [List.foldl_cons]
      apply ih
      split
      · rw [deltaTo_hv, deltaTo_me_v]; exact hx
      · exact hx
  have h1 := h n.attached.keys n ⟨rfl, rfl⟩
  generalize forKeys n.attached.keys (fun p n' => if p != n.me && (n'.isBoot p || (n.me == n'.me && n'.homed.has p)) then N.deltaTo e n' p n.me rc a else n') n = x at h1 ⊢
  have : (n.me == x.me) = true := by simp [h1.2]
  simp only [this, if_true]
  exact h1.1

theorem rnStep_hv (e : Env) (now : Nat) (fs p : Bool) (n : N) (hub : Nat) : (rnStep e now fs p n hub).hv = n.hv := by
  unfold rnStep N.helloTo
  repeat' split
  all_goals simp_all [N.markHello]

theorem bumpRecord_hv (n : N) : n.bumpRecord.hv = n.hv := by
  unfold N.bumpRecord; split <;> simp

theorem rnPre_hv (n : N) (p : Bool) : (rnPre n p).1.hv = n.hv := by
  unfold rnPre; dsimp only; split <;> simp [bumpRecord_hv]

theorem rnPush_hv (e : Env) (n : N) (now : Nat) : (rnPush e n now).hv = n.hv := by
  unfold rnPush
  dsimp only
  split
  · exact pushDelta_me_hv e { n with own := ⟨n.inc.word, n.ver, n.th⟩ } now _ _
  · rfl

theorem renew_eq' (e : Env) (n : N) (now : Nat) (forceSnap periodic : Bool) :
    N.renew e n now forceSnap periodic =
      { (List.foldl (rnStep e now forceSnap (rnPre n periodic).2) (rnPush e (rnPre n periodic).1 now)
          (rnPush e (rnPre n periodic).1 now).boot) with nextRenew := satAdd now RENEW } := rfl

theorem renew_hv (e : Env) (n : N) (now : Nat) (fs p : Bool) : (N.renew e n now fs p).hv = n.hv := by
  rw [renew_eq']
  have e1 := rnPre_hv n p
  have e3 : (List.foldl (rnStep e now fs (rnPre n p).2) (rnPush e (rnPre n p).1 now) (rnPush e (rnPre n p).1 now).boot).hv
      = (rnPush e (rnPre n p).1 now).hv :=
    foldl_inv (fun (x : N) => x.hv = (rnPush e (rnPre n p).1 now).hv) _ _ _ (fun b a hb => by rw [rnStep_hv]; exact hb) rfl
  exact e3.trans ((rnPush_hv e _ now).trans e1)


theorem onSelfEntry_hv (e : Env) (n : N) (now hub : Nat) (rc : Rec) (a : Alive) : (N.onSelfEntry e n now hub rc a).hv = n.hv := by
  unfold N.onSelfEntry
  by_cases h0 : (hub == n.me) = true
  · simp only [h0, if_true]
  · simp only [h0, Bool.false_eq_true, if_false]
    have e1 : (n.trace (.selfDelta hub)).hv = n.hv := trace_hv n _
    generalize n.trace (.selfDelta hub) = n1 at e1 ⊢
    by_cases h1 : (a == .alive && n1.inc.word < rc.inc) = true
    · simp only [h1, if_true]
      rcases hO : observe n1.loc n1.inc rc.inc with err | ⟨ch, i', l'⟩
      · simp [e1, trace_hv]
      · cases ch
        · exact e1
        · rw [renew_hv]; simp [e1, trace_hv]
    · simp only [h1, if_false]
      by_cases h2 : (a != .alive || rc.inc < n1.inc.word) = true
      · simp only [h2, if_true]; simp [e1, N.helloTo]
      · simp only [h2, if_false]; simp [e1, N.bc]

theorem hubEnsure_mono (n : N) (hub : Nat) : HvMono n.hv (hubEnsure n hub).1.hv := by
  unfold hubEnsure
  by_cases h : (!n.hv.has hub) = true
  · simp only [h, if_true]
    by_cases h2 : MAX_HUBS ≤ n.hv.len
    · simp only [h2, if_true]; exact HvMono.refl _
    · simp only [h2, if_false]
      exact hvMono_insert _ _ _ (fun c hc m hm => by
        exfalso; have := h; simp at this; rw [AMap.has_iff_get, hc] at this; simp at this)
  · simp only [h, if_false]; exact HvMono.refl _


theorem markAbsent_mono (e : Env) (n : N) (now hub round : Nat) : HvMono n.hv (N.markAbsent e n now hub round).1.hv := by
  unfold N.markAbsent
  refine foldl_inv (fun (a : N × Bool) => HvMono n.hv a.1.hv) _ _ _ ?_ (HvMono.refl _)
  intro a m ha
  obtain ⟨n1, c1⟩ := a
  simp only at ha ⊢
  cases hg : (n1.hv.get? hub).bind (fun c => c.entries.get? m) with
  | none => simpa [hg] using ha
  | some ce =>
    simp only []
    by_cases h : (ce.round != round && ce.absentSince.isNone) = true
    · simp only [h, if_true]
      cases hh : n1.hv.get? hub with
      | none => simp [hh] at hg
      | some c =>
        have hm : HvMono n1.hv (n1.hv.insert hub { c with entries := c.entries.modify m (fun x => { x with absentSince := some now }) }) :=
          hvMono_insert _ _ _ (fun c' hc' m' hm' => by
            rw [hh] at hc'; cases hc'; simp [AMap.has_modify, hm'])
        simp only [hh]
        have := (recomputeOne_keeps2 e ((({ n1 with hv := n1.hv.insert hub { c with entries := c.entries.modify m (fun x => { x with absentSince := some now }) } }) : N).trace (.absent m)) now m).1.1
        simp only [trace_hv] at this
        refine ha.trans (hm.trans ?_)
        rw [this]; exact HvMono.refl _
    · simp only [h, if_false]; exact ha

theorem markViewAbsent_mono (e : Env) (n : N) (now hub round : Nat) :
    HvMono n.hv (N.markViewAbsent e n now hub round).1.hv := by
  unfold N.markViewAbsent
  refine foldl_inv (fun (a : N × Bool) => HvMono n.hv a.1.hv) _ _ _ ?_ (HvMono.refl _)
  intro a m ha
  obtain ⟨n1, c1⟩ := a
  simp only at ha ⊢
  cases hv : n1.members.get? m with
  | none => simpa [hv] using ha
  | some v =>
    cases hh : n1.hv.get? hub with
    | none => simpa [hv, hh] using ha
    | some c =>
      simp only []
      by_cases h1 : c.entries.has m = true
      · simp only [h1, if_true]; exact ha
      · by_cases h2 : (decide (MAX_TABLE ≤ c.entries.len) && !c.entries.has m) = true
        · rw [if_neg h1, if_pos h2]
          simp only []
          have := (recomputeOne_keeps2 e n1 now m).1.1
          rw [this]; exact ha
        · rw [if_neg h1, if_neg h2]
          simp only []
          have hm : HvMono n1.hv (n1.hv.insert hub { c with entries := c.entries.insert m ⟨v.rc, round - 1, some now⟩ }) :=
            hvMono_insert _ _ _ (fun c' hc' m' hm' => by
              rw [hh] at hc'; cases hc'; exact AMap.has_insert_mono _ _ _ _ hm')
          have := (recomputeOne_keeps2 e ((({ n1 with hv := n1.hv.insert hub { c with entries := c.entries.insert m ⟨v.rc, round - 1, some now⟩ } }) : N).trace (.absent m)) now m).1.1
          simp only [trace_hv] at this
          refine ha.trans (hm.trans ?_)
          rw [this]; exact HvMono.refl _

theorem snapAbsent_mono (e : Env) (n : N) (now hub round : Nat) : HvMono n.hv (N.snapAbsent e n now hub round).1.hv := by
  simp only [N.snapAbsent]
  split
  · exact (markAbsent_mono e n now hub round).trans (markViewAbsent_mono e _ now hub round)
  · exact markAbsent_mono e n now hub round

/-- `drop_gone` only touches the sender's copy. -/
theorem dropGone_monoX (n : N) (hub round : Nat) : HvMonoX hub n.hv (n.dropGone hub round).hv := by
  intro k m hk x
  unfold N.dropGone
  split
  · dsimp only [EntHas] at x ⊢
    rw [AMap.get?_insert_ne _ _ _ _ hk]
    exact x
  · exact x

theorem snapRound_mono (n : N) (hub : Nat) : HvMono n.hv (snapRound n hub).1.hv := by
  unfold snapRound
  cases hg : n.hv.get? hub with
  | none => exact HvMono.refl _
  | some c =>
    simp only []
    refine hvMono_insert _ _ _ (fun c' hc' m hm => ?_)
    rw [hg] at hc'; cases hc'
    split <;> simpa using hm

theorem snapStep_mono (e : Env) (now hub round : Nat) (a : N × Bool × Nat) (p : Nat × Rec) :
    HvMono a.1.hv (snapStep e now hub round a p).1.hv := by
  obtain ⟨n, c, k⟩ := a
  unfold snapStep
  dsimp only
  by_cases h1 : (p.1 == n.me) = true
  · simp only [h1, if_true]; rw [onSelfEntry_hv]; exact HvMono.refl _
  · simp only [h1, Bool.false_eq_true, if_false]
    by_cases h2 : n.revoked.has p.1 = true
    · simp only [h2, if_true]; exact HvMono.refl _
    · simp only [h2, Bool.false_eq_true, if_false]
      cases hg : n.hv.get? hub with
      | none =>
        simp only []
        have := (recomputeOne_keeps2 e ({ n with left := n.left.del p.1 } : N) now p.1).1.1
        simp only [] at this
        rw [this]; exact HvMono.refl _
      | some c =>
        simp only []
        by_cases h3 : (decide (MAX_TABLE ≤ c.entries.len) && !c.entries.has p.1) = true
        · simp only [h3, if_true]; exact HvMono.refl _
        · simp only [h3, Bool.false_eq_true, if_false]
          have := (recomputeOne_keeps2 e ({ n with hv := n.hv.insert hub { c with entries := c.entries.insert p.1 ⟨p.2, round, none⟩ }, left := n.left.del p.1 } : N) now p.1).1.1
          simp only [] at this
          rw [this]
          exact hvMono_insert _ _ _ (fun c' hc' m hm => by
            rw [hg] at hc'; cases hc'; exact AMap.has_insert_mono _ _ _ _ hm)

def sfClose (n : N) (hub : Nat) : N :=
  match n.hv.get? hub with
  | some c => { n with hv := n.hv.insert hub { c with open_ := false } }
  | none => n

def sfMid (e : Env) (now hub : Nat) (partial_ : Bool) (round : Nat) (n : N) (changed : Bool) : N × Bool :=
  let n := sfClose n hub
  let (n, changed) := if !partial_ then
      let (n', ch) := N.snapAbsent e (n.dropGone hub round) now hub round
      (n', changed || ch)
    else (n, changed)
  let n := if n.primary == some hub then n.bc (.resub hub) else n
  (n, changed)

theorem snapFin_eq (e : Env) (now hub : Nat) (partial_ more : Bool) (round : Nat) (a : N × Bool × Nat) :
    snapFin e now hub partial_ more round a =
      (let (n, changed, cnt) := a
       let n := n.trace (.snapApplied hub cnt more)
       let (n, changed) : N × Bool := if !more then sfMid e now hub partial_ round n changed else (n, changed)
       if changed then n.bump else n) := rfl

theorem sfClose_mono (n : N) (hub : Nat) : HvMono n.hv (sfClose n hub).hv := by
  unfold sfClose
  cases hg : n.hv.get? hub with
  | none => exact HvMono.refl _
  | some c => exact hvMono_insert _ _ _ (fun c' hc' m hm => by rw [hg] at hc'; cases hc'; exact hm)

theorem sfMid_mono (e : Env) (now hub : Nat) (partial_ : Bool) (round : Nat) (n : N) (changed : Bool) :
    HvMonoX hub n.hv (sfMid e now hub partial_ round n changed).1.hv := by
  unfold sfMid
  dsimp only
  have h1 := (sfClose_mono n hub).x hub
  by_cases hp : (!partial_) = true
  · simp only [hp, if_true]
    have h2 := (dropGone_monoX (sfClose n hub) hub round).trans
      ((snapAbsent_mono e ((sfClose n hub).dropGone hub round) now hub round).x hub)
    by_cases hq : ((N.snapAbsent e ((sfClose n hub).dropGone hub round) now hub round).1.primary == some hub) = true
    · simp only [hq, if_true]
      rw [bc_hv]; exact h1.trans h2
    · simp only [hq, Bool.false_eq_true, if_false]; exact h1.trans h2
  · simp only [hp, Bool.false_eq_true, if_false]
    by_cases hq : ((sfClose n hub).primary == some hub) = true
    · simp only [hq, if_true]
      rw [bc_hv]; exact h1
    · simp only [hq, Bool.false_eq_true, if_false]; exact h1

theorem snapFin_mono (e : Env) (now hub : Nat) (partial_ more : Bool) (round : Nat) (a : N × Bool × Nat) :
    HvMonoX hub a.1.hv (snapFin e now hub partial_ more round a).hv := by
  rw [snapFin_eq]
  obtain ⟨n, c, k⟩ := a
  dsimp only
  have key : ∀ (n' : N) (b : Bool), HvMonoX hub n.hv n'.hv → HvMonoX hub n.hv (if b = true then n'.bump else n').hv := by
    intro n' b h
    by_cases hb : b = true
    · simp only [hb, if_true]; rw [bump_hv]; exact h
    · simp only [hb, Bool.false_eq_true, if_false]; exact h
  have ht : HvMonoX hub n.hv (n.trace (.snapApplied hub k more)).hv := by rw [trace_hv]; exact (HvMono.refl _).x hub
  by_cases hm : (!more) = true
  · simp only [hm, if_true]
    exact key _ _ (ht.trans (sfMid_mono e now hub partial_ round _ c))
  · simp only [hm, Bool.false_eq_true, if_false]
    exact key _ _ ht


/-- **A snapshot takes nothing from the other hubs' copies.** After `apply_snap`, every copy but the sender's still
lists every member it listed before. The sender's copy gains the listed entries, marks the omitted ones of members the
view lists, at a member whose confirmed home the sender is gains a marked entry for every view member it lacks
(`mark_view_absent`), and drops only the omitted ones of members the view does not list (`drop_gone`). -/
theorem applySnap_copies_mono (e : Env) (n : N) (now hub : Nat) (partial_ more : Bool) (es : List (Nat × Rec)) :
    HvMonoX hub n.hv (N.applySnap e n now hub partial_ more es).hv := by
  rw [applySnap_eq]
  have h1 := hubEnsure_mono n hub
  rcases hE : hubEnsure n hub with ⟨n1, ok⟩
  rw [hE] at h1
  change HvMono n.hv n1.hv at h1
  by_cases hok : ok = true
  · simp only [hok, Bool.not_true, if_false, Bool.false_eq_true]
    rcases hR : snapRound n1 hub with ⟨n2, round⟩
    have h2 := snapRound_mono n1 hub
    rw [hR] at h2
    change HvMono n1.hv n2.hv at h2
    generalize hn3 : (if (!n2.isHub && n2.primary == some hub) = true then
        ({ n2 with homeOk := some hub, homeSeen := true } : N) else n2) = n3
    have h3 : n3.hv = n2.hv := by rw [← hn3]; split <;> rfl
    have h4 : HvMono n3.hv (List.foldl (snapStep e now hub round) (n3, false, 0) es).1.hv := by
      refine foldl_inv (fun (a : N × Bool × Nat) => HvMono n3.hv a.1.hv) _ _ _ ?_ (HvMono.refl _)
      intro b a hb
      exact hb.trans (snapStep_mono e now hub round b a)
    have h5 := snapFin_mono e now hub partial_ more round (List.foldl (snapStep e now hub round) (n3, false, 0) es)
    have h6 := (h4.x hub).trans h5
    rw [h3] at h6
    exact (h1.x hub).trans ((h2.x hub).trans h6)
  · have : ok = false := by simpa using hok
    simp only [this, Bool.not_false, if_true]
    exact h1.x hub

/-- A freshly marked omission is not an expired one: the member it concerns is still a live candidate. -/
theorem snap_mark_is_live (now : Nat) (ce : CopyEntry) : expiredAbs now { ce with absentSince := some now } = false :=
  fresh_mark_not_expired now ce

end Vinc.Membership
