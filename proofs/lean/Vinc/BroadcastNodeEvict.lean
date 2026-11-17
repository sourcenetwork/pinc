import Vinc.BroadcastNodeDepth

/-!
# Broadcast node: an id that leaves the hub log is in the dedupe set (`EvictedSeen`)

The unbounded counterpart of `EvictedSeen` of `proofs/tla/BroadcastNode.tla`: on every step of a reachable node
other than a restart, every id that was in the hub log before the step and is not after it has a record in the
dedupe set after it (`evictedSeen`), so a late copy of an evicted message is a duplicate.

The statement needs two hypotheses, and neither can be dropped:
* `p.evictGuard = true`: an evicted id the set already holds is not recorded again. Without the guard a second
  record of the same id at the same time lets a later drop of the first forget the id
  (`BroadcastNode_evict.cfg` is the witness).
* `2 * p.logCap ≤ p.seenCap`: the dedupe set holds at least twice as many ids as the log holds messages. With
  less, one store can evict the whole log, and the forced inserts of that step can push the record of the first
  evicted id out of the front of a full set (`BroadcastNode_evictCap.cfg` is the witness, with a set of 3 against
  a log of 2). The constants of the code are 8192 against 2048.

The invariant (`EInv`) is the accounting `KeepInv` of `BroadcastNodeDepth` between the log and the depths of the
records: a logged id the set holds has at most `logCap - 1 - q` re-records of older evicted ids and one record per
newer logged id behind it, `q` being its place in the log. An eviction step walks the evicted ids oldest first
(`sweep_loop`) and keeps, for each id already evicted, room for the inserts the rest of the log can still cause
(`DoneInv`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Vinc.BroadcastNode

/-! ## The shape of a push to and an expiry of the log -/

/-- A push evicts a prefix of the log, oldest first, and appends the new id when it stores it. -/
def PushShape (p : Params) (mid : Nat) (L : Log) (ev : List Nat) (r : PushRes) : Prop :=
  ∃ k, r.ev = ev ++ (LIds L).take k ∧
    ((r.ok = false ∧ LIds r.log = (LIds L).drop k) ∨
     (r.ok = true ∧ ((LIds L).drop k).length < p.logCap ∧ LIds r.log = (LIds L).drop k ++ [mid]))

theorem LIds_pop {L : Log} {e : LEntry} {rest : List LEntry} (hL : L.entries = e :: rest) :
    LIds L = e.mid :: LIds (LPop L) := by
  have hp : (LPop L).entries = rest := by rw [LPop_entries, hL]; rfl
  simp [LIds, hp, hL]

theorem LLoop_shape (p : Params) (mid at_ wall n : Nat) (f : Nat) :
    ∀ (L : Log) (ev : List Nat), PushShape p mid L ev (LLoop p mid at_ wall n f L ev) := by
  induction f with
  | zero => intro L ev; exact ⟨0, by simp [LLoop], Or.inl ⟨rfl, by simp [LLoop]⟩⟩
  | succ f ih =>
    intro L ev
    unfold LLoop
    split
    · rename_i hc
      refine ⟨0, by simp, Or.inr ⟨rfl, ?_, ?_⟩⟩
      · simp [LIds]; exact hc.1
      · simp [LIds, LWrite]
    · rcases hL : L.entries with _ | ⟨e, rest⟩
      · exact ⟨0, by simp, Or.inl ⟨rfl, by simp⟩⟩
      · obtain ⟨k, h1, h2⟩ := ih (LPop L) (ev ++ [e.mid])
        have hI := LIds_pop hL
        refine ⟨k + 1, ?_, ?_⟩
        · show (LLoop p mid at_ wall n f (LPop L) (ev ++ [e.mid])).ev = _
          rw [h1, hI]; simp
        · rcases h2 with ⟨a, b⟩ | ⟨a, b, c⟩
          · exact Or.inl ⟨a, by rw [hI]; simpa using b⟩
          · exact Or.inr ⟨a, by rw [hI]; simpa using b, by rw [hI]; simpa using c⟩

theorem LPush_shape (p : Params) (L : Log) (mid at_ wall n : Nat) :
    PushShape p mid L [] (LPush p L mid at_ wall n) := by
  unfold LPush
  split
  · exact ⟨0, by simp, Or.inl ⟨rfl, by simp⟩⟩
  · exact LLoop_shape p mid at_ wall n _ L []

/-- An expiry evicts a prefix of the log, oldest first. -/
theorem LExpireAux_shape (p : Params) (now f : Nat) :
    ∀ (L : Log) (ev : List Nat), ∃ k, (LExpireAux p now f L ev).ev = ev ++ (LIds L).take k ∧
      LIds (LExpireAux p now f L ev).log = (LIds L).drop k := by
  induction f with
  | zero => intro L ev; exact ⟨0, by simp [LExpireAux], by simp [LExpireAux]⟩
  | succ f ih =>
    intro L ev
    unfold LExpireAux
    rcases hL : L.entries with _ | ⟨e, rest⟩
    · exact ⟨0, by simp, by simp⟩
    · by_cases hc : p.logWin < now - e.at_
      · simp only [hc, ite_true]
        obtain ⟨k, h1, h2⟩ := ih (LPop L) (ev ++ [e.mid])
        have hI := LIds_pop hL
        exact ⟨k + 1, by rw [h1, hI]; simp, by rw [h2, hI]; simp⟩
      · simp only [hc, ite_false]
        exact ⟨0, by simp, by simp⟩

/-! ## The eviction loop -/

theorem SInsertAll_guard {p : Params} {now : Nat} (hg : p.evictGuard = true) :
    ∀ (ids : List Nat) (S : Seen), SInsertAll p S now ids = SweepIds p S now ids := by
  intro ids
  induction ids with
  | nil => intro S; rfl
  | cons i ids ih =>
    intro S
    simp only [SInsertAll, SweepIds, hg, Bool.true_and]
    exact ih _

/-- The evicted ids `ids`, oldest first, are recorded unless held. Afterwards the accounting holds for the rest of
the log `E`, every evicted id is held with room for what `E` can still cause, and no other id became held. -/
theorem sweep_loop {p : Params} {now : Nat} (hcap : 0 < p.seenCap) (h2 : 2 * p.logCap ≤ p.seenCap) :
    ∀ (ids : List Nat) (S : Seen) (E done : List Nat),
      SeenG p S now → (ids ++ E).Nodup → (ids ++ E).length ≤ p.logCap → (∀ y ∈ done, y ∉ ids ++ E) →
      KeepInv p.logCap (D p S now) (ids ++ E) → DoneInv p.seenCap (D p S now) done (ids ++ E) →
      SeenG p (SweepIds p S now ids) now ∧ KeepInv p.logCap (D p (SweepIds p S now ids) now) E ∧
      DoneInv p.seenCap (D p (SweepIds p S now ids) now) (done ++ ids) E ∧
      (∀ x, x ∉ ids → D p S now x = none → D p (SweepIds p S now ids) now x = none) := by
  intro ids
  induction ids with
  | nil =>
    intro S E done hG _ _ _ hK hJ
    simp only [SweepIds, List.append_nil]
    exact ⟨hG, hK, hJ, fun x _ h => h⟩
  | cons i ids ih =>
    intro S E done hG hnd hlen hdis hK hJ
    have hnd' : (i :: (ids ++ E)).Nodup := hnd
    obtain ⟨hi, hnd2⟩ := List.nodup_cons.1 hnd'
    have hK' : KeepInv p.logCap (D p S now) (i :: (ids ++ E)) := hK
    have hJ' : DoneInv p.seenCap (D p S now) done (i :: (ids ++ E)) := hJ
    have hlen' : (ids ++ E).length + 1 ≤ p.logCap := by simpa using hlen
    have hdis2 : ∀ y ∈ done ++ [i], y ∉ ids ++ E := by
      intro y hy
      rcases List.mem_append.1 hy with h1 | h1
      · intro hm
        have : y ∈ i :: (ids ++ E) := List.mem_cons_of_mem _ hm
        exact hdis y h1 this
      · rw [List.mem_singleton] at h1; subst h1; exact hi
    unfold SweepIds
    by_cases hc : SContains p S i now = true
    · rw [if_pos hc]
      obtain ⟨d, hd⟩ := D_of_contains hG.inv hc
      have hKi := hK' [] i (ids ++ E) rfl d hd
      have hJ2 : DoneInv p.seenCap (D p S now) (done ++ [i]) (ids ++ E) := by
        intro y hy
        rcases List.mem_append.1 hy with h1 | h1
        · exact hJ'.evict_skip y h1
        · rw [List.mem_singleton] at h1; subst h1
          refine ⟨d, hd, ?_⟩
          have hl2 : (y :: (ids ++ E)).length = (ids ++ E).length + 1 := rfl
          rw [hl2] at hKi
          simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hKi
          omega
      obtain ⟨a, b, c, e⟩ := ih S E (done ++ [i]) hG hnd2 (by omega) hdis2 hK'.evict_skip hJ2
      refine ⟨a, b, ?_, fun x hx h => e x (fun hm => hx (List.mem_cons_of_mem _ hm)) h⟩
      have : done ++ i :: ids = done ++ [i] ++ ids := by simp
      rw [this]; exact c
    · rw [if_neg hc]
      have hc' : SContains p S i now = false := by simpa using hc
      obtain ⟨hG1, hI⟩ := SInsert_rel (f := true) hcap hG hc' (Or.inl rfl)
      have hdi : ∀ y ∈ done, y ≠ i := by
        intro y hy e1
        have : y ∈ i :: (ids ++ E) := by rw [e1]; exact List.mem_cons_self
        exact hdis y hy this
      have hJ2 : DoneInv p.seenCap (D p (SInsert p S i now true) now) (done ++ [i]) (ids ++ E) := by
        intro y hy
        rcases List.mem_append.1 hy with h1 | h1
        · exact (hJ'.evict_push hI (D_none hc') hi hdi) y h1
        · rw [List.mem_singleton] at h1; subst h1
          refine ⟨0, hI.self, ?_⟩
          have := NB_le_length (D p (SInsert p S y now true) now) 0 (ids ++ E)
          omega
      obtain ⟨a, b, c, e⟩ := ih (SInsert p S i now true) E (done ++ [i]) hG1 hnd2 (by omega) hdis2
        (hK'.evict_push hI hi) hJ2
      refine ⟨a, b, ?_, fun x hx h => e x (fun hm => hx (List.mem_cons_of_mem _ hm)) ?_⟩
      · have : done ++ i :: ids = done ++ [i] ++ ids := by simp
        rw [this]; exact c
      · cases hd : D p (SInsert p S i now true) now x with
        | none => rfl
        | some d' =>
          have hxi : x ≠ i := fun e1 => hx (by rw [e1]; exact List.mem_cons_self)
          obtain ⟨d, h1, _⟩ := hI.back x d' hxi hd
          rw [h] at h1; cases h1

/-! ## The state of a hub and what its operators keep -/

/-- The invariant of a hub node at `now`: the dedupe set under guarded recording, the log without a repeated id and
within its capacity, and the accounting between the two. -/
structure EI (p : Params) (N : Node) (now : Nat) : Prop where
  g : SeenG p N.seen now
  nodup : (LIds N.lg).Nodup
  len : (LIds N.lg).length ≤ p.logCap
  keep : KeepInv p.logCap (D p N.seen now) (LIds N.lg)

/-- What a step leaves of the log: an id that left it has a record in the dedupe set. -/
def Evicted (N N' : Node) : Prop := ∀ x ∈ LIds N.lg, x ∉ LIds N'.lg → N'.seen.map x ≠ none

theorem EI.of_eq {p : Params} {N N' : Node} {now : Nat} (h : EI p N now) (hs : N'.seen = N.seen)
    (hl : N'.lg = N.lg) : EI p N' now ∧ Evicted N N' := by
  refine ⟨⟨by rw [hs]; exact h.g, by rw [hl]; exact h.nodup, by rw [hl]; exact h.len, by rw [hs, hl]; exact h.keep⟩, ?_⟩
  intro x hx hn
  rw [hl] at hn; exact absurd hx hn

theorem Offer_seen (p : Params) (N : Node) (now : Nat) (m : Ent) :
    (Offer p N now m).n.seen = N.seen ∨
      (N.seen.order.length < p.seenCap ∧ (Offer p N now m).n.seen = SInsert p N.seen m.mid now false) := by
  have F := Offer_form p N now m
  generalize Offer p N now m = r at F
  cases F with
  | topic _ => exact Or.inl rfl
  | seenFull _ _ => exact Or.inl rfl
  | floor _ _ _ _ => exact Or.inl (HoldFloor_frame p N m).2.1
  | full _ _ _ _ _ => exact Or.inl (HoldAndAsk_frame p N m).2.1
  | skip _ hl _ => exact Or.inr ⟨hl, rfl⟩
  | deliver _ hl _ _ _ _ _ _ _ => exact Or.inr ⟨hl, rfl⟩
  | deny _ hl _ => exact Or.inr ⟨hl, rfl⟩
  | ask _ hl _ _ => exact Or.inr ⟨hl, (HoldAndAsk_frame p (N1of p N now m) m).2.1⟩

/-- The dedupe set and the log after `hub_store`. -/
theorem HubStore_shape (p : Params) (N : Node) (now wall : Nat) (fanned : Bool) (m : Msg) :
    ((HubStore p N now wall fanned m).n.seen = N.seen ∧ (HubStore p N now wall fanned m).n.lg = N.lg) ∨
    ((HubStore p N now wall fanned m).n.lg = (LPush p N.lg m.mid now wall m.n).log ∧
      (((LPush p N.lg m.mid now wall m.n).ok = false ∧
          (HubStore p N now wall fanned m).n.seen = SInsertAll p N.seen now (LPush p N.lg m.mid now wall m.n).ev) ∨
       ((LPush p N.lg m.mid now wall m.n).ok = true ∧
          ((HubStore p N now wall fanned m).n.seen = SInsertAll p N.seen now (LPush p N.lg m.mid now wall m.n).ev ∨
           ∃ f, (f = true ∨ (SInsertAll p N.seen now (LPush p N.lg m.mid now wall m.n).ev).order.length < p.seenCap) ∧
             (HubStore p N now wall fanned m).n.seen =
               SInsert p (SInsertAll p N.seen now (LPush p N.lg m.mid now wall m.n).ev) m.mid now f)))) := by
  unfold HubStore
  by_cases htf : p.topicFull = true
  · rw [if_pos htf]; exact Or.inl ⟨rfl, rfl⟩
  · rw [if_neg htf]
    dsimp only
    generalize LPush p N.lg m.mid now wall m.n = rr
    by_cases hok : rr.ok = true
    · rw [if_neg (by simp [hok])]
      by_cases hsub : (N.sub && m.origin != p.me) = true
      · rw [if_pos hsub]
        have hlg := (Offer_spec p {N with seen := SInsertAll p N.seen now rr.ev, lg := rr.log} now m.ent).lg
        refine Or.inr ⟨hlg, Or.inr ⟨hok, ?_⟩⟩
        rcases Offer_seen p {N with seen := SInsertAll p N.seen now rr.ev, lg := rr.log} now m.ent with h | ⟨hl, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨false, Or.inr hl, h⟩
      · rw [if_neg hsub]
        exact Or.inr ⟨rfl, Or.inr ⟨hok, Or.inr ⟨true, Or.inl rfl, rfl⟩⟩⟩
    · rw [if_pos (by simpa using hok)]
      exact Or.inr ⟨rfl, Or.inl ⟨by simpa using hok, rfl⟩⟩

/-- `hub_store` of an id that is no duplicate keeps the invariant, and every id it evicts has a record. -/
theorem HubStore_keep {p : Params} {N : Node} {now wall : Nat} {fanned : Bool} {m : Msg} (hcap : 0 < p.seenCap)
    (h2 : 2 * p.logCap ≤ p.seenCap) (hg : p.evictGuard = true) (h : EI p N now)
    (hdup : IsDup p N m.mid now = false) :
    EI p (HubStore p N now wall fanned m).n now ∧ Evicted N (HubStore p N now wall fanned m).n := by
  have hnc : SContains p N.seen m.mid now = false := by
    simp [IsDup] at hdup; simpa using hdup.1
  have hnl : m.mid ∉ LIds N.lg := by
    intro hm
    have := (LContains_iff N.lg m.mid).2 hm
    simp [IsDup] at hdup; rw [hdup.2] at this; cases this
  rcases HubStore_shape p N now wall fanned m with ⟨hs, hl⟩ | ⟨hl, hrest⟩
  · exact h.of_eq hs hl
  · obtain ⟨k, hev, hlog⟩ := LPush_shape p N.lg m.mid now wall m.n
    generalize LPush p N.lg m.mid now wall m.n = rr at hl hrest hev hlog
    generalize HubStore p N now wall fanned m = r at hl hrest ⊢
    have hsplit : (LIds N.lg).take k ++ (LIds N.lg).drop k = LIds N.lg := List.take_append_drop k _
    have hev' : rr.ev = (LIds N.lg).take k := by simpa using hev
    have L := sweep_loop (now := now) hcap h2 ((LIds N.lg).take k) N.seen ((LIds N.lg).drop k) [] h.g
      (by rw [hsplit]; exact h.nodup) (by rw [hsplit]; exact h.len) (fun y hy => by cases hy)
      (by rw [hsplit]; exact h.keep) (fun y hy => by cases hy)
    rw [← hev', ← SInsertAll_guard hg] at L
    obtain ⟨hG1, hK1, hJ1, hN1⟩ := L
    have hJ1' : DoneInv p.seenCap (D p (SInsertAll p N.seen now rr.ev) now) ((LIds N.lg).take k)
        ((LIds N.lg).drop k) := by simpa [hev'] using hJ1
    have hmE : m.mid ∉ (LIds N.lg).drop k := fun hm => hnl (List.mem_of_mem_drop hm)
    have hmT : m.mid ∉ rr.ev := by rw [hev']; exact fun hm => hnl (List.mem_of_mem_take hm)
    have hDm : D p (SInsertAll p N.seen now rr.ev) now m.mid = none := hN1 m.mid hmT (D_none hnc)
    have hndE : ((LIds N.lg).drop k).Nodup := List.Nodup.sublist (List.drop_sublist k _) h.nodup
    have hlenE : ((LIds N.lg).drop k).length ≤ p.logCap := by
      have := h.len; simp; omega
    -- an id that left the log is one of the evicted prefix
    have hleft : ∀ x ∈ LIds N.lg, x ∉ (LIds N.lg).drop k → x ∈ (LIds N.lg).take k := by
      intro x hx hn
      rw [← hsplit] at hx
      rcases List.mem_append.1 hx with h1 | h1
      · exact h1
      · exact absurd h1 hn
    rcases hrest with ⟨hok, hs⟩ | ⟨hok, hs⟩
    · -- not stored: the log is the rest
      have hlogE : LIds rr.log = (LIds N.lg).drop k := by
        rcases hlog with ⟨_, b⟩ | ⟨a, _, _⟩
        · exact b
        · rw [hok] at a; cases a
      refine ⟨⟨by rw [hs]; exact hG1, by rw [hl, hlogE]; exact hndE, by rw [hl, hlogE]; exact hlenE,
        by rw [hs, hl, hlogE]; exact hK1⟩, ?_⟩
      intro x hx hn
      rw [hl, hlogE] at hn
      obtain ⟨d, hd, _⟩ := hJ1' x (hleft x hx hn)
      rw [hs]; exact D_map hd
    · -- stored at the back
      obtain ⟨hlenlt, hlogE⟩ : ((LIds N.lg).drop k).length < p.logCap ∧ LIds rr.log = (LIds N.lg).drop k ++ [m.mid] := by
        rcases hlog with ⟨a, _⟩ | ⟨_, b, c⟩
        · rw [hok] at a; cases a
        · exact ⟨b, c⟩
      have hnd' : ((LIds N.lg).drop k ++ [m.mid]).Nodup := nodup_snoc hndE hmE
      have hlen' : ((LIds N.lg).drop k ++ [m.mid]).length ≤ p.logCap := by
        have h1 : ([m.mid] : List Nat).length = 1 := rfl
        rw [List.length_append, h1]; omega
      have hleft' : ∀ x ∈ LIds N.lg, x ∉ (LIds N.lg).drop k ++ [m.mid] → x ∈ (LIds N.lg).take k :=
        fun x hx hn => hleft x hx (fun hm => hn (List.mem_append_left _ hm))
      rcases hs with hs | ⟨f, hf, hs⟩
      · refine ⟨⟨by rw [hs]; exact hG1, by rw [hl, hlogE]; exact hnd', by rw [hl, hlogE]; exact hlen',
          by rw [hs, hl, hlogE]; exact hK1.store_unrec hDm⟩, ?_⟩
        intro x hx hn
        rw [hl, hlogE] at hn
        obtain ⟨d, hd, _⟩ := hJ1' x (hleft' x hx hn)
        rw [hs]; exact D_map hd
      · have hncm : SContains p (SInsertAll p N.seen now rr.ev) m.mid now = false := by
          cases hc : SContains p (SInsertAll p N.seen now rr.ev) m.mid now with
          | false => rfl
          | true =>
            obtain ⟨d, hd⟩ := D_of_contains hG1.inv hc
            rw [hDm] at hd; cases hd
        obtain ⟨hG2, hI⟩ := SInsert_rel (f := f) hcap hG1 hncm hf
        refine ⟨⟨by rw [hs]; exact hG2, by rw [hl, hlogE]; exact hnd', by rw [hl, hlogE]; exact hlen',
          by rw [hs, hl, hlogE]; exact hK1.store_rec hI hmE hlenlt⟩, ?_⟩
        intro x hx hn
        rw [hl, hlogE] at hn
        have hxt := hleft' x hx hn
        have hdis : ∀ y ∈ (LIds N.lg).take k, y ≠ m.mid := fun y hy e1 => hnl (e1 ▸ List.mem_of_mem_take hy)
        have := hJ1'.after_ins hI hdis x hxt
        rw [hs]
        intro hmap
        apply this
        unfold D; rw [hmap]

/-- The sweep of the timer keeps the invariant, and every id it expires from the log has a record. -/
theorem Sweep_keep {p : Params} {N : Node} {now : Nat} (hcap : 0 < p.seenCap) (h2 : 2 * p.logCap ≤ p.seenCap)
    (h : EI p N now) : EI p (Sweep p N now) now ∧ Evicted N (Sweep p N now) := by
  obtain ⟨k, hev, hlog⟩ := LExpireAux_shape p now N.lg.entries.length N.lg []
  have hs : (Sweep p N now).seen = SweepIds p (SExpire p N.seen now) now (LExpire p N.lg now).ev := rfl
  have hl : (Sweep p N now).lg = (LExpire p N.lg now).log := rfl
  have hev' : (LExpire p N.lg now).ev = (LIds N.lg).take k := by
    show (LExpireAux p now N.lg.entries.length N.lg []).ev = _
    simpa using hev
  have hlog' : LIds (LExpire p N.lg now).log = (LIds N.lg).drop k := hlog
  obtain ⟨hG0, hD0⟩ := SExpireAux_G (p := p) (now := now) N.seen.order.length h.g
  have hDeq : D p (SExpire p N.seen now) now = D p N.seen now := funext hD0
  have hG0' : SeenG p (SExpire p N.seen now) now := hG0
  have hsplit : (LIds N.lg).take k ++ (LIds N.lg).drop k = LIds N.lg := List.take_append_drop k _
  have L := sweep_loop (now := now) hcap h2 ((LIds N.lg).take k) (SExpire p N.seen now) ((LIds N.lg).drop k) [] hG0'
    (by rw [hsplit]; exact h.nodup) (by rw [hsplit]; exact h.len) (fun y hy => by cases hy)
    (by rw [hsplit, hDeq]; exact h.keep) (fun y hy => by cases hy)
  rw [← hev', ← hs] at L
  obtain ⟨hG1, hK1, hJ1, _⟩ := L
  have hJ1' : DoneInv p.seenCap (D p (Sweep p N now).seen now) ((LIds N.lg).take k) ((LIds N.lg).drop k) := by
    simpa [hev'] using hJ1
  refine ⟨⟨hG1, ?_, ?_, ?_⟩, ?_⟩
  · rw [hl, hlog']; exact List.Nodup.sublist (List.drop_sublist k _) h.nodup
  · rw [hl, hlog']; have := h.len; simp; omega
  · rw [hl, hlog']; exact hK1
  · intro x hx hn
    rw [hl, hlog'] at hn
    rw [← hsplit] at hx
    rcases List.mem_append.1 hx with h1 | h1
    · obtain ⟨d, hd, _⟩ := hJ1' x h1
      exact D_map hd
    · exact absurd h1 hn

/-- On a hub, `on_msg` leaves the dedupe set and the log alone or is `hub_store` of an id that is no duplicate. -/
theorem OnMsg_hub (p : Params) (N : Node) (now wall : Nat) (t : Frame) (b : Bool) (m : Msg) (hhub : p.isHub = true) :
    ((OnMsg p N now wall t b m).n.seen = N.seen ∧ (OnMsg p N now wall t b m).n.lg = N.lg) ∨
    (IsDup p N m.mid now = false ∧ ∃ fanned,
      (OnMsg p N now wall t b m).n.seen = (HubStore p {N with req := N.req.filter (fun x => x != m.mid)} now wall fanned m).n.seen ∧
      (OnMsg p N now wall t b m).n.lg = (HubStore p {N with req := N.req.filter (fun x => x != m.mid)} now wall fanned m).n.lg) := by
  unfold OnMsg
  by_cases h1 : (!Allowed p t b) = true
  · rw [if_pos h1]; exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg h1]
  by_cases h2 : m.kind = .badhead
  · rw [if_pos h2]; exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg h2]
  by_cases h3 : m.kind = .big
  · rw [if_pos h3]; exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg h3]
  dsimp only
  by_cases h4 : IsDup p N m.mid now = true
  · rw [if_pos h4]; exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg h4]
  by_cases h5 : p.revoked.contains m.origin = true
  · rw [if_pos h5]; exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg h5]
  by_cases h6 : (m.kind = .badsig ∨ m.kind = .graft)
  · rw [if_pos h6]; exact Or.inl ⟨rfl, rfl⟩
  rw [if_neg h6]
  rw [if_pos hhub]
  exact Or.inr ⟨by simpa using h4, _, NoteStored_seen _ _, NoteStored_lg _ _⟩

theorem OnMsg_keep {p : Params} {N : Node} {now wall : Nat} {t : Frame} {b : Bool} {m : Msg} (hcap : 0 < p.seenCap)
    (h2 : 2 * p.logCap ≤ p.seenCap) (hg : p.evictGuard = true) (hhub : p.isHub = true) (h : EI p N now) :
    EI p (OnMsg p N now wall t b m).n now ∧ Evicted N (OnMsg p N now wall t b m).n := by
  rcases OnMsg_hub p N now wall t b m hhub with ⟨hs, hl⟩ | ⟨hdup, fanned, hs, hl⟩
  · exact h.of_eq hs hl
  · have h' : EI p {N with req := N.req.filter (fun x => x != m.mid)} now := ⟨h.g, h.nodup, h.len, h.keep⟩
    have H := HubStore_keep (N := {N with req := N.req.filter (fun x => x != m.mid)}) (now := now) (wall := wall) (fanned := fanned) (m := m) hcap h2 hg h' hdup
    refine ⟨(EI.of_eq H.1 hs hl).1, ?_⟩
    intro x hx hn
    rw [hl] at hn
    have := H.2 x hx hn
    rwa [hs]

theorem OnTimer_hub {p : Params} {N : Node} {now : Nat} (hhub : p.isHub = true) (hI : NodeInv p N) :
    (OnTimer p N now).n = Sweep p N now := by
  unfold OnTimer
  dsimp only
  have hph : (Sweep p N now).phase = .never := hI.hubPhase hhub
  rw [if_neg (by rw [hph]; intro ⟨h, _⟩; cases h)]
  rfl

/-- Time passing keeps the invariant: a record behind a live record is live. -/
theorem EI.tick {p : Params} {N : Node} {now : Nat} (h : EI p N now) : EI p N (now + 1) := by
  refine ⟨h.g.mono (Nat.le_succ _), h.nodup, h.len, ?_⟩
  intro pre e post hE d hd
  have hd0 := D_earlier (Nat.le_succ now) hd
  have hold := h.keep pre e post hE d hd0
  have hnb : NB (D p N.seen (now + 1)) d post ≤ NB (D p N.seen now) d post := by
    apply NB_mono
    intro f _ hbf
    unfold behind at hbf ⊢
    rcases hDf : D p N.seen now f with _ | df
    · simp [hDf] at hbf
    · simp only [hDf, decide_eq_true_eq] at hbf
      rw [D_later h.g.t hd hDf hbf]
      simpa using hbf
  omega

theorem EI.init (p : Params) (born now : Nat) : EI p (NodeInit p born) now :=
  ⟨SeenEmpty_G p now, List.nodup_nil, Nat.zero_le _, KeepInv_nil _ _⟩

/-! ## The system -/

/-- One step of a hub keeps the invariant and, unless it is a restart, records every id that leaves the log. -/
theorem step_ei {p : Params} {s s' : Sys} (hcap : 0 < p.seenCap) (h2 : 2 * p.logCap ≤ p.seenCap)
    (hg : p.evictGuard = true) (hhub : p.isHub = true) (hI : NodeInv p s.node) (h : EI p s.node s.now)
    (st : Step p s s') : EI p s'.node s'.now ∧ (s' = Restarted p s ∨ Evicted s.node s'.node) := by
  cases st with
  | msg t b m =>
    have := OnMsg_keep (now := s.now) (wall := s.now) (t := t) (b := b) (m := m) hcap h2 hg hhub h
    exact ⟨this.1, Or.inr this.2⟩
  | timer =>
    have hn : (OnTimer p s.node s.now).n = Sweep p s.node s.now := OnTimer_hub hhub hI
    have := Sweep_keep (now := s.now) hcap h2 h
    refine ⟨?_, Or.inr ?_⟩
    · show EI p (OnTimer p s.node s.now).n s.now
      rw [hn]; exact this.1
    · show Evicted s.node (OnTimer p s.node s.now).n
      rw [hn]; exact this.2
  | answer c hc allow =>
    have := h.of_eq (AcpAnswer_seen p s.node s.now c.id allow) (AcpAnswer_lg p s.node s.now c.id allow)
    exact ⟨this.1, Or.inr this.2⟩
  | floors rf of_ nh hph =>
    have := hI.hubPhase hhub
    rw [hph] at this; cases this
  | tick ht =>
    exact ⟨h.tick, Or.inr (fun x hx hn => absurd hx hn)⟩
  | restart =>
    exact ⟨EI.init p s.now s.now, Or.inl rfl⟩

theorem reach_ei {p : Params} {s : Sys} (hcap : 0 < p.seenCap) (h2 : 2 * p.logCap ≤ p.seenCap)
    (hg : p.evictGuard = true) (hhub : p.isHub = true) (r : Reach p s) : EI p s.node s.now := by
  induction r with
  | init => exact EI.init p 0 0
  | step r0 st ih => exact (step_ei hcap h2 hg hhub (reach_inv hcap r0).inv ih st).1

/-- `EvictedSeen`: on a step other than a restart, an id that leaves the log has a record in the dedupe set
afterwards. It needs the guard on re-recording an evicted id and a dedupe set of at least twice the log's
capacity; a member, whose log is always empty, satisfies it trivially. -/
theorem evictedSeen {p : Params} {s s' : Sys} (hcap : 0 < p.seenCap) (h2 : 2 * p.logCap ≤ p.seenCap)
    (hg : p.evictGuard = true) (r : Reach p s) (st : Step p s s') :
    s' = Restarted p s ∨ ∀ x ∈ LIds s.node.lg, x ∉ LIds s'.node.lg → s'.node.seen.map x ≠ none := by
  cases hhub : p.isHub with
  | true => exact (step_ei hcap h2 hg hhub (reach_inv hcap r).inv (reach_ei hcap h2 hg hhub r) st).2
  | false =>
    right
    intro x hx
    have : s.node.lg.entries = [] := (reach_inv hcap r).inv.memberLg hhub
    simp [LIds, this] at hx

/-- In every reachable state of a hub no id is logged twice, and no record of the dedupe set is repeated. -/
theorem logIdsNodup {p : Params} {s : Sys} (hcap : 0 < p.seenCap) (h2 : 2 * p.logCap ≤ p.seenCap)
    (hg : p.evictGuard = true) (hhub : p.isHub = true) (r : Reach p s) :
    (LIds s.node.lg).Nodup ∧ s.node.seen.order.Nodup :=
  ⟨(reach_ei hcap h2 hg hhub r).nodup, (reach_ei hcap h2 hg hhub r).g.nodup⟩

#audit_axioms Vinc.BroadcastNode.evictedSeen
#audit_axioms Vinc.BroadcastNode.logIdsNodup

end Vinc.BroadcastNode
