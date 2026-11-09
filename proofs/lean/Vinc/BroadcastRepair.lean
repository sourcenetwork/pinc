import Vinc.Axioms

/-!
# Gap repair of the broadcast crate

The unbounded counterpart of `proofs/tla/BroadcastRepair.tla`: the coverage arithmetic and the bounded-set facts
of `gap.rs`. A hub log is a list of `(mid, wall)` pairs; `sinceIds` is the newest `k` mids logged at or after
`since` (log.rs `since`); the subscriber keeps what it delivered, its last receipt, its last periodic check and
its newest receipt. A question (SUB, HAVE, GET, MSG) is `ask`: GET names the HAVE ids not yet delivered
(`need`, the set difference) and each message is delivered once (`deliver`). `sinceMs` is the point a
resubscription asks the log back from (with and without the `gapMark` fix), `gapSince` that of the periodic
check, `gapAe` the periodic check itself (skipped on a topic that is not live).

Facts for every log, every parameter and every instant: `ask_delivers`, `ask_nodup`, `periodic_overlap`,
`periodic_cover`, `resub_covers`, `resub_asks`, `haveMax_bound`, `quiet_topic_gap`, `gap_delivers`; the concrete
witness `fallback_hole`. Not proved: that `sinceIds` keeps the newest entries (only membership, size and
completeness under the bound), nor the link behaviour (a message before a check sent while the link was up).
-/

namespace Vinc.BroadcastRepair

/-- The gap-repair parameters (nanoseconds, ids). -/
structure Cfg where
  (gapEvery gapSpan gapLive resubBack haveMax : Nat)

/-- `GAP_EVERY`, `GAP_SPAN` in ns and `HAVE_MAX`. -/
def gapEveryNs : Nat := 20_000_000_000
def gapSpanNs : Nat := 25_000_000_000
def haveMaxReal : Nat := 512

/-- `(at, id)` order, newest first. -/
def newer (a b : Nat × Nat) : Bool := decide (b.2 < a.2) || (a.2 == b.2 && decide (b.1 ≤ a.1))

/-- log.rs `since`: the newest `k` mids logged at or after `since`. -/
def sinceIds (log : List (Nat × Nat)) (since k : Nat) : List Nat :=
  (((log.filter fun e => decide (since ≤ e.2)).mergeSort newer).take k).map (·.1)

theorem sinceIds_mem {log : List (Nat × Nat)} {since k m : Nat} (h : m ∈ sinceIds log since k) :
    ∃ w, (m, w) ∈ log ∧ since ≤ w := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
  have := List.mem_mergeSort.1 (List.mem_of_mem_take he)
  simp only [List.mem_filter, decide_eq_true_eq] at this
  exact ⟨e.2, this.1, this.2⟩

theorem sinceIds_length (log : List (Nat × Nat)) (since k : Nat) : (sinceIds log since k).length ≤ k := by
  simp [sinceIds]; exact Nat.min_le_left _ _

theorem sinceIds_complete {log : List (Nat × Nat)} {since k m t : Nat} (hk : (log.filter fun e => decide (since ≤ e.2)).length ≤ k)
    (hm : (m, t) ∈ log) (ht : since ≤ t) : m ∈ sinceIds log since k := by
  have hp := List.mergeSort_perm (log.filter fun e => decide (since ≤ e.2)) newer
  have hl : ((log.filter fun e => decide (since ≤ e.2)).mergeSort newer).length ≤ k := by rw [hp.length_eq]; exact hk
  unfold sinceIds
  rw [List.take_of_length_le hl]
  exact List.mem_map.2 ⟨(m, t), List.mem_mergeSort.2 (by simp [hm, ht]), rfl⟩

/-- A subscriber: delivered ids, last receipt, last periodic check sent, newest receipt, base time. -/
structure Sub where
  (delivered : List Nat) (lastRx lastGap newest : Option Nat) (born : Nat)

/-- on_get: deliver a message once. -/
def deliver (d : List Nat) (m : Nat) : List Nat := if m ∈ d then d else d ++ [m]

theorem nodup_deliver {d : List Nat} (h : d.Nodup) (m : Nat) : (deliver d m).Nodup := by
  unfold deliver; split
  · exact h
  · rename_i hm
    refine List.nodup_append.2 ⟨h, by simp, ?_⟩
    intro a ha b hb hab; simp at hb; subst hb; exact hm (hab ▸ ha)

theorem mem_deliver_of {d : List Nat} {a : Nat} (m : Nat) (h : a ∈ d) : a ∈ deliver d m := by
  unfold deliver; split <;> simp_all

theorem nodup_foldl : ∀ (ids d : List Nat), d.Nodup → (ids.foldl deliver d).Nodup
  | [], _, h => h
  | m :: t, _, h => nodup_foldl t _ (nodup_deliver h m)

theorem mem_foldl_of {a : Nat} : ∀ (ids d : List Nat), a ∈ d → a ∈ ids.foldl deliver d
  | [], _, h => h
  | m :: t, _, h => mem_foldl_of t _ (mem_deliver_of m h)

theorem mem_foldl : ∀ (ids d : List Nat) (a : Nat), a ∈ ids → a ∈ ids.foldl deliver d
  | [], _, _, h => by simp at h
  | m :: t, d, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact mem_foldl_of t _ (by unfold deliver; split <;> simp_all)
    · exact mem_foldl t _ a h

/-- GET: the ids of the HAVE answer the subscriber lacks. -/
def need (s : Sub) (log : List (Nat × Nat)) (since k : Nat) : List Nat :=
  (sinceIds log since k).filter fun m => decide (m ∉ s.delivered)

/-- SUB(since), HAVE, GET, MSG: deliver what is lacking; a new receipt moves `lastRx` and `newest`. -/
def ask (s : Sub) (log : List (Nat × Nat)) (since k now : Nat) : Sub :=
  let n := need s log since k
  { s with delivered := n.foldl deliver s.delivered,
           lastRx := if n.isEmpty then s.lastRx else some now,
           newest := if n.isEmpty then s.newest else some now }

/-- (1) After the question the subscriber has every id of the answer, and nothing it had is lost. -/
theorem ask_delivers (s : Sub) (log : List (Nat × Nat)) (since k now : Nat) :
    (∀ m ∈ sinceIds log since k, m ∈ (ask s log since k now).delivered) ∧
    ∀ m ∈ s.delivered, m ∈ (ask s log since k now).delivered := by
  refine ⟨fun m hm => ?_, fun m hm => mem_foldl_of _ _ hm⟩
  by_cases hd : m ∈ s.delivered
  · exact mem_foldl_of _ _ hd
  · exact mem_foldl _ _ _ (List.mem_filter.2 ⟨hm, by simpa using hd⟩)

/-- (1) Each id is delivered at most once: the delivered list stays duplicate-free. -/
theorem ask_nodup (s : Sub) (log : List (Nat × Nat)) (since k now : Nat) (h : s.delivered.Nodup) :
    (ask s log since k now).delivered.Nodup := nodup_foldl _ _ h

/-- (5) HAVE carries at most `k` ids (`haveMax`), and GET names only ids that are in the log at or after `since` and
that the subscriber lacks, at most `k` of them. -/
theorem haveMax_bound (s : Sub) (log : List (Nat × Nat)) (since k : Nat) :
    (sinceIds log since k).length ≤ k ∧ (need s log since k).length ≤ k ∧
    ∀ m ∈ need s log since k, (∃ w, (m, w) ∈ log ∧ since ≤ w) ∧ m ∉ s.delivered := by
  refine ⟨sinceIds_length .., Nat.le_trans (List.length_filter_le _ _) (sinceIds_length ..), fun m hm => ?_⟩
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hm
  exact ⟨sinceIds_mem h1, by simpa using h2⟩

/-! ### Periodic check -/

/-- The point the periodic check asks the log back from. -/
def gapSince (span born now : Nat) : Nat := max (now - span) born

/-- (2) With the span above the period, a message logged after the check at `gPrev` and before the next check at
`g ≤ gPrev + every` is inside the span of the check at `g`. -/
theorem periodic_overlap (every span born gPrev g t : Nat) (hs : every < span) (hg : g ≤ gPrev + every)
    (hb : born ≤ t) (h1 : gPrev < t) (h2 : t ≤ g) : gapSince span born g ≤ t ∧ t ≤ g := by
  unfold gapSince; omega

/-- (2) Every instant from `gPrev - span` to `g` is in the span of the check at `gPrev` or in that of the check
at `g`: consecutive checks leave no uncovered instant. -/
theorem periodic_cover (every span born gPrev g t : Nat) (hs : every < span) (hg : g ≤ gPrev + every)
    (hb : born ≤ t) (h1 : gPrev - span ≤ t) (h2 : t ≤ g) :
    (gapSince span born gPrev ≤ t ∧ t ≤ gPrev) ∨ (gapSince span born g ≤ t ∧ t ≤ g) := by
  by_cases h : t ≤ gPrev
  · left; unfold gapSince; omega
  · right; exact periodic_overlap every span born gPrev g t hs hg hb (by omega) h2

/-- (2) The real values: 25 s over 20 s. -/
theorem periodic_overlap_real (born gPrev g t : Nat) (hg : g ≤ gPrev + gapEveryNs) (hb : born ≤ t)
    (h1 : gPrev < t) (h2 : t ≤ g) : gapSince gapSpanNs born g ≤ t ∧ t ≤ g :=
  periodic_overlap gapEveryNs gapSpanNs born gPrev g t (by decide) hg hb h1 h2

/-! ### Resubscription -/

/-- gap.rs `since_ms`; with `gapMark` no later than the last periodic check sent, the base while none was. -/
def sinceMs (gapMark : Bool) (resubBack born : Nat) (lastRx lastGap : Option Nat) : Nat :=
  match lastRx with
  | none => born
  | some r =>
    if gapMark then (match lastGap with | none => born | some g => max born (min (r - resubBack) g))
    else max born (r - resubBack)

/-- (3) With `gapMark`, a message logged at or after the last check sent (not covered by it) is at or after the
point the resubscription asks from. -/
theorem resub_covers (resubBack born g0 t : Nat) (lastRx : Option Nat) (hg : g0 ≤ t) (hb : born ≤ t) :
    sinceMs true resubBack born lastRx (some g0) ≤ t := by
  cases lastRx <;> simp [sinceMs] <;> omega

/-- (3) With `gapMark` and no check sent yet, the resubscription asks from the base. -/
theorem resub_none (resubBack born : Nat) (lastRx : Option Nat) : sinceMs true resubBack born lastRx none = born := by
  cases lastRx <;> simp [sinceMs]

/-- The resubscription question. -/
def resub (c : Cfg) (gapMark : Bool) (s : Sub) (log : List (Nat × Nat)) (now : Nat) : Sub :=
  ask s log (sinceMs gapMark c.resubBack s.born s.lastRx s.lastGap) c.haveMax now

/-- (3) The resubscription delivers a logged message the subscriber lacks that is at or after the last check sent,
provided the answer is within `haveMax`. -/
theorem resub_asks (c : Cfg) (s : Sub) (log : List (Nat × Nat)) (now m t g0 : Nat) (hlg : s.lastGap = some g0)
    (hg : g0 ≤ t) (hb : s.born ≤ t) (hm : (m, t) ∈ log)
    (hk : (log.filter fun e => decide (sinceMs true c.resubBack s.born s.lastRx s.lastGap ≤ e.2)).length ≤ c.haveMax) :
    m ∈ (resub c true s log now).delivered := by
  have hc := resub_covers c.resubBack s.born g0 t s.lastRx hg hb
  rw [← hlg] at hc
  exact (ask_delivers s log _ c.haveMax now).1 m (sinceIds_complete hk hm hc)

/-- (4) The finding: without `gapMark` (the old rule) there are numbers where a lacked message, logged after the
last check sent, is before the resubscription point and before the span of the next check, so it is skipped; with
`gapMark` the resubscription asks for it. -/
theorem fallback_hole (resubBack span : Nat) : ∃ born g0 lastRx t next : Nat, g0 < t ∧ born ≤ t ∧
    t < sinceMs false resubBack born (some lastRx) (some g0) ∧ t < gapSince span born next ∧
    sinceMs true resubBack born (some lastRx) (some g0) ≤ t :=
  ⟨0, 0, resubBack + 2, 1, span + 2, by omega, by omega, by simp [sinceMs], by simp [gapSince],
    by simp [sinceMs]⟩

/-! ### Quiet topics -/

/-- The topic is live: something was received less than `gapLive` ago. -/
def live (gapLive now : Nat) : Option Nat → Bool
  | none => false
  | some n => decide (now - n < gapLive)

/-- gap.rs `gap_ae`: while the topic is live, ask for the last `gapSpan`; `none` is no question. -/
def gapAe (c : Cfg) (s : Sub) (log : List (Nat × Nat)) (now : Nat) : Option Sub :=
  if live c.gapLive now s.newest then
    some { ask s log (gapSince c.gapSpan s.born now) c.haveMax now with lastGap := some now }
  else none

/-- (6) A topic whose newest recorded id is not younger than `gapLive` is not live: the periodic check asks
nothing, so a missed message there waits for a membership resubscription. -/
theorem quiet_topic_gap (c : Cfg) (s : Sub) (log : List (Nat × Nat)) (now n : Nat) (hn : s.newest = some n)
    (hq : c.gapLive ≤ now - n) : gapAe c s log now = none := by
  simp [gapAe, live, hn]; omega

/-- (6) Nothing received yet is not live either. -/
theorem quiet_topic_none (c : Cfg) (s : Sub) (log : List (Nat × Nat)) (now : Nat) (hn : s.newest = none) :
    gapAe c s log now = none := by
  simp [gapAe, live, hn]

/-- A live check delivers every id of the answer and records the check. -/
theorem gap_delivers (c : Cfg) (s : Sub) (log : List (Nat × Nat)) (now n : Nat) (hn : s.newest = some n)
    (hl : now - n < c.gapLive) : ∃ s', gapAe c s log now = some s' ∧ s'.lastGap = some now ∧
    ∀ m ∈ sinceIds log (gapSince c.gapSpan s.born now) c.haveMax, m ∈ s'.delivered := by
  refine ⟨{ ask s log (gapSince c.gapSpan s.born now) c.haveMax now with lastGap := some now }, ?_, rfl, ?_⟩
  · simp [gapAe, live, hn, hl]
  · exact (ask_delivers s log _ c.haveMax now).1

#audit_axioms Vinc.BroadcastRepair.ask_delivers
#audit_axioms Vinc.BroadcastRepair.ask_nodup
#audit_axioms Vinc.BroadcastRepair.periodic_overlap
#audit_axioms Vinc.BroadcastRepair.periodic_cover
#audit_axioms Vinc.BroadcastRepair.periodic_overlap_real
#audit_axioms Vinc.BroadcastRepair.resub_covers
#audit_axioms Vinc.BroadcastRepair.resub_none
#audit_axioms Vinc.BroadcastRepair.resub_asks
#audit_axioms Vinc.BroadcastRepair.fallback_hole
#audit_axioms Vinc.BroadcastRepair.haveMax_bound
#audit_axioms Vinc.BroadcastRepair.quiet_topic_gap
#audit_axioms Vinc.BroadcastRepair.quiet_topic_none
#audit_axioms Vinc.BroadcastRepair.gap_delivers

end Vinc.BroadcastRepair
