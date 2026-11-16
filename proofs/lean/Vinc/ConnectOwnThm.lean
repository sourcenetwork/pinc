import Vinc.ConnectOwn
import Vinc.ConnectRecordsThm

/-!
# Theorems of the node's own record and address discovery

For the model of `ConnectOwn.lean`, over unbounded naturals and any `MAX_ADDRS` (`cf.cap`; the code's is 8):

* The candidate list: `cands_length` (at most `cap`), `cands_prefix` (the reflexive addresses come first, in relay
  order), `cands_tail` (then the node's own addresses, in their order, each once, none already listed), `cands_room`
  (all of them when there is room), `cands_only` (nothing else), `cands_distinct` (every address once). The reflexive
  addresses are distinct and in relay order (`reflexive_distinct`: an address that several relays report is listed
  once, at the first of them, #308 fixed), all of them when there is room (`reflexive_room`), and a ninth distinct one
  is dropped (`reflexive_dropped`).
* The QADR answer: `observe_took` (taken only from the first relay with that configured address, for the nonce of its
  outstanding probe; it clears that probe, records the address, and changes no other relay), `observe_refused` (an
  answer not taken changes nothing), `observe_once` (a probe is answered once).
* The sequence number is the wall clock of the last tick, or one above the last record's number when the clock did not
  move past it (`job_seq`, `seq_wall_ahead`, `seq_wall_behind`, `seq_above_last`); a restore only raises the last
  number (`restore_raises`) and no step lowers it (`run_floor`). So every record's number is strictly above the one
  before it, whatever happened in between (`seq_rises`): two records with no tick that had a clock between them are one
  apart (`same_tick_next_seq`, #287 fixed), and a clock set back does not lower the number (`clock_set_back_next_seq`).
  The relay refuses a number that is not above the stored one (`not_above_refused`, from `ConnectRecords.lean`) and
  stores the node's next record over the one before (`next_record_stored`), so that refusal never meets a node's own
  consecutive records. A number is below `u64::MAX`, where the code's addition saturates (a hypothesis where it
  matters).
* When a record is signed: the candidates enter a job only when it starts (`start_job`), nothing else changes the job
  (`run_job_fixed`) and only the answer to the signature hands it on (`run_sent_fixed`, `signed_sent`), so a reflexive
  address learnt after the job started waits for the next one (`later_address_waits`). The record is asked for by a
  class or home change, an opened carrier (`changed_then_publish`), new hints (`want_rises`), or 1800 s after the last
  record handed to the carrier (`republish_not_before`, `republish_at`).
-/

namespace Vinc.ConnectOwn

/-! ## The candidate list -/

theorem addNew_len (cap : Nat) (acc : List Nat) (a : Nat) (h : acc.length ≤ cap) :
    (addNew cap acc a).length ≤ cap := by
  unfold addNew
  split
  · rename_i hh; simp; omega
  · exact h

theorem foldl_len (cap : Nat) (l acc : List Nat) (h : acc.length ≤ cap) :
    (l.foldl (addNew cap) acc).length ≤ cap := by
  induction l generalizing acc with
  | nil => exact h
  | cons a l ih => exact ih _ (addNew_len cap acc a h)

theorem foldl_add (cap : Nat) (l acc : List Nat) :
    ∃ t, l.foldl (addNew cap) acc = acc ++ t ∧ t.Nodup ∧ (∀ x ∈ t, x ∉ acc) ∧ t.Sublist l := by
  induction l generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons a l ih =>
    by_cases h : acc.length < cap ∧ a ∉ acc
    · obtain ⟨t, h1, h2, h3, h4⟩ := ih (acc ++ [a])
      refine ⟨a :: t, ?_, ?_, ?_, ?_⟩
      · simp only [List.foldl_cons, addNew, if_pos h, h1]; simp
      · refine List.nodup_cons.2 ⟨?_, h2⟩
        intro hm; exact h3 a hm (by simp)
      · intro x hx hxa
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h.2 hxa
        · exact h3 x hx (by simp [hxa])
      · exact h4.cons₂ a
    · obtain ⟨t, h1, h2, h3, h4⟩ := ih acc
      refine ⟨t, ?_, h2, h3, h4.cons a⟩
      simp only [List.foldl_cons, addNew, if_neg h, h1]

theorem foldl_room (cap : Nat) (l acc : List Nat) (hr : (l.foldl (addNew cap) acc).length < cap) :
    ∀ x ∈ l, x ∈ l.foldl (addNew cap) acc := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    intro x hx
    have hr' : (l.foldl (addNew cap) (addNew cap acc a)).length < cap := by simpa using hr
    obtain ⟨t, ht, _, _, _⟩ := foldl_add cap l (addNew cap acc a)
    have hlen : (addNew cap acc a).length < cap := by
      rw [ht] at hr'; simp at hr'; omega
    have ha : a ∈ addNew cap acc a := by
      by_cases hh : acc.length < cap ∧ a ∉ acc
      · simp [addNew, hh]
      · have e : addNew cap acc a = acc := by simp [addNew, hh]
        rw [e] at hlen ⊢
        exact Classical.byContradiction fun hc => hh ⟨hlen, hc⟩
    rcases List.mem_cons.1 hx with hx | hx
    · rw [hx]
      show a ∈ l.foldl (addNew cap) (addNew cap acc a)
      rw [ht]; exact List.mem_append_left _ ha
    · exact ih _ hr' x hx

theorem reflList_length (cf : Cf) (s : St) : (reflList cf s).length ≤ cf.cap :=
  foldl_len cf.cap (s.refl.filterMap id) [] (Nat.zero_le _)

/-- The record lists at most `cap` addresses. -/
theorem cands_length (cf : Cf) (s : St) : (cands cf s).length ≤ cf.cap := by
  unfold cands
  exact foldl_len _ _ _ (reflList_length cf s)

/-- The reflexive addresses come first, in relay order. -/
theorem cands_prefix (cf : Cf) (s : St) : ∃ t, cands cf s = reflList cf s ++ t := by
  obtain ⟨t, h, _⟩ := foldl_add cf.cap s.loc (reflList cf s)
  exact ⟨t, h⟩

/-- After them come the node's own addresses, in their order (a sublist of `loc`), each once, none already listed. -/
theorem cands_tail (cf : Cf) (s : St) :
    ∃ t, cands cf s = reflList cf s ++ t ∧ t.Nodup ∧ (∀ x ∈ t, x ∉ reflList cf s) ∧ t.Sublist s.loc :=
  foldl_add cf.cap s.loc (reflList cf s)

/-- All the node's own addresses are listed when there is room. -/
theorem cands_room (cf : Cf) (s : St) (h : (cands cf s).length < cf.cap) : ∀ x ∈ s.loc, x ∈ cands cf s :=
  foldl_room cf.cap s.loc (reflList cf s) h

/-- Nothing else is listed. -/
theorem cands_only (cf : Cf) (s : St) : ∀ x ∈ cands cf s, x ∈ reflList cf s ∨ x ∈ s.loc := by
  intro x hx
  obtain ⟨t, h, _, _, h4⟩ := cands_tail cf s
  rw [h] at hx
  rcases List.mem_append.1 hx with h | h
  · exact Or.inl h
  · exact Or.inr (h4.subset h)

/-- #308 fixed: the reflexive addresses are listed each once, in relay order (an address that several relays report
is listed once, at the first of them). -/
theorem reflexive_distinct (cf : Cf) (s : St) :
    (reflList cf s).Nodup ∧ (reflList cf s).Sublist (s.refl.filterMap id) := by
  obtain ⟨t, h, h2, _, h4⟩ := foldl_add cf.cap (s.refl.filterMap id) []
  unfold reflList
  rw [h, List.nil_append]
  exact ⟨h2, h4⟩

/-- Every address a relay reported is listed when there is room. -/
theorem reflexive_room (cf : Cf) (s : St) (h : (reflList cf s).length < cf.cap) :
    ∀ a ∈ s.refl.filterMap id, a ∈ reflList cf s :=
  foldl_room cf.cap (s.refl.filterMap id) [] h

/-- Every address is listed once. -/
theorem cands_distinct (cf : Cf) (s : St) : (cands cf s).Nodup := by
  obtain ⟨t, h, h2, h3, _⟩ := cands_tail cf s
  rw [h]
  exact List.nodup_append.2 ⟨(reflexive_distinct cf s).1, h2, fun a ha b hb hab => h3 b hb (hab ▸ ha)⟩

/-- A ninth distinct reflexive address is dropped (the cap is 8). -/
theorem reflexive_dropped :
    (reflList ⟨8, List.replicate 9 10⟩
      { probe := List.replicate 9 none, refl := (List.range 9).map fun k => some (k + 1) }).length = 8 := by decide

/-! ## Taking an answer -/

theorem firstIdx_spec (x : Nat) (l : List Nat) (k : Nat) (h : firstIdx x l = some k) :
    l[k]? = some x ∧ ∀ j < k, l[j]? ≠ some x := by
  induction l generalizing k with
  | nil => simp [firstIdx] at h
  | cons y l ih =>
    unfold firstIdx at h
    by_cases hy : y = x
    · simp [hy] at h; subst h; simp [hy]
    · simp only [hy, if_false] at h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨i1, i2⟩ := ih k' hk'
      refine ⟨by simpa using i1, ?_⟩
      intro j hj
      cases j with
      | zero => simpa using hy
      | succ j => simpa using i2 j (by omega)

/-- An answer is taken only from the first relay with that configured address, for the nonce of its outstanding
probe; the probe is cleared, the address recorded, and nothing else changes. -/
theorem observe_took (cf : Cf) (s : St) (f n a : Nat) (h : (observe cf s f n a).2 = true)
    (hw : s.refl.length = s.probe.length) :
    ∃ k, relayAt cf f = some k ∧ cf.udp[k]? = some f ∧ (∀ j < k, cf.udp[j]? ≠ some f) ∧ f ≠ 0 ∧
      s.probe[k]? = some (some n) ∧
      (observe cf s f n a).1.probe[k]? = some none ∧ (observe cf s f n a).1.refl[k]? = some (some a) ∧
      (∀ j, j ≠ k → (observe cf s f n a).1.probe[j]? = s.probe[j]? ∧ (observe cf s f n a).1.refl[j]? = s.refl[j]?) ∧
      (observe cf s f n a).1.loc = s.loc ∧ (observe cf s f n a).1.wall = s.wall := by
  unfold observe at h ⊢
  cases hr : relayAt cf f with
  | none => simp [hr] at h
  | some k =>
    simp only [hr] at h ⊢
    by_cases hp : s.probe[k]? = some (some n)
    · rw [if_pos hp]
      have h0 : f ≠ 0 := by
        intro h0; simp [relayAt, h0] at hr
      have hk' := firstIdx_spec f cf.udp k (by simpa [relayAt, h0] using hr)
      have hlt : k < s.probe.length := by
        exact Classical.byContradiction fun hc => by simp [List.getElem?_eq_none (by omega : s.probe.length ≤ k)] at hp
      refine ⟨k, rfl, hk'.1, hk'.2, h0, hp, ?_, ?_, ?_, rfl, rfl⟩
      · simp [List.getElem?_set_self hlt]
      · simp [List.getElem?_set_self (by omega : k < s.refl.length)]
      · intro j hj
        simp [List.getElem?_set_ne (Ne.symm hj)]
    · simp [hp] at h

theorem observe_refused (cf : Cf) (s : St) (f n a : Nat) (h : (observe cf s f n a).2 = false) :
    (observe cf s f n a).1 = s := by
  unfold observe at h ⊢
  cases hr : relayAt cf f with
  | none => simp [hr]
  | some k =>
    simp only [hr] at h ⊢
    by_cases hp : s.probe[k]? = some (some n)
    · simp [hp] at h
    · simp [hp]

theorem observe_unknown (cf : Cf) (s : St) (f n a : Nat) (h : ∀ k : Nat, cf.udp[k]? ≠ some f) :
    (observe cf s f n a).2 = false := by
  unfold observe
  cases hr : relayAt cf f with
  | none => simp
  | some k =>
    exfalso
    unfold relayAt at hr
    by_cases h0 : f = 0
    · simp [h0] at hr
    · simp only [h0, if_false] at hr
      exact h k (firstIdx_spec f cf.udp k hr).1

theorem observe_wrong_nonce (cf : Cf) (s : St) (f n a k : Nat) (hk : relayAt cf f = some k)
    (h : s.probe[k]? ≠ some (some n)) : (observe cf s f n a).2 = false := by
  simp [observe, hk, h]

/-- A probe is answered once: the same answer again is refused. -/
theorem observe_once (cf : Cf) (s : St) (f n a a' : Nat) (hw : s.refl.length = s.probe.length)
    (h : (observe cf s f n a).2 = true) : (observe cf (observe cf s f n a).1 f n a').2 = false := by
  obtain ⟨k, hr, _, _, _, _, hp, _⟩ := observe_took cf s f n a h hw
  apply observe_wrong_nonce cf _ f n a' k hr
  rw [hp]; simp

/-! ## The sequence number -/

def clockOp : Op → Bool
  | .tick (some _) => true
  | _ => false

theorem step_wall (cf : Cf) (s : St) (o : Op) (h : clockOp o = false) : (step cf s o).wall = s.wall := by
  cases o with
  | tick w => cases w <;> simp [clockOp, step, tick] at h ⊢
  | answer f n a =>
    simp only [step]; unfold observe; split
    · rfl
    · split <;> rfl
  | start now hm c =>
    simp only [step, start]
    split
    · rfl
    · split
      · rfl
      · split
        · split <;> rfl
        · rfl
  | signed now ok sent =>
    simp only [step, signed]
    split
    · rfl
    · split
      · split <;> rfl
      · rfl
  | publish now c =>
    simp only [step, publish]
    split
    · rfl
    · split <;> rfl
  | _ => rfl

theorem run_wall (cf : Cf) (s : St) (ops : List Op) (h : ∀ o ∈ ops, clockOp o = false) :
    (run cf s ops).wall = s.wall := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    show (run cf (step cf s o) ops).wall = s.wall
    rw [ih _ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')), step_wall cf s o (h o (by simp))]

/-- The operations that set the last number: a record job that starts, a restore. -/
def lastOp : Op → Bool
  | .start _ _ _ => true
  | .restore _ => true
  | _ => false

theorem step_last (cf : Cf) (s : St) (o : Op) (h : lastOp o = false) : (step cf s o).last = s.last := by
  cases o with
  | start _ _ _ => simp [lastOp] at h
  | restore _ => simp [lastOp] at h
  | answer f n a =>
    simp only [step]; unfold observe; split
    · rfl
    · split <;> rfl
  | signed now ok sent =>
    simp only [step, signed]
    split
    · rfl
    · split
      · split <;> rfl
      · rfl
  | publish now c =>
    simp only [step, publish]
    split
    · rfl
    · split <;> rfl
  | tick w => cases w <;> rfl
  | setLocal _ => rfl
  | probe _ => rfl
  | restart => rfl
  | hints _ => rfl
  | changed _ => rfl

theorem run_last (cf : Cf) (s : St) (ops : List Op) (h : ∀ o ∈ ops, lastOp o = false) :
    (run cf s ops).last = s.last := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    show (run cf (step cf s o) ops).last = s.last
    rw [ih _ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')), step_last cf s o (h o (by simp))]

/-- The record's sequence number is the wall clock of the last tick, or one above the last record's number when the
clock did not move past it (the code's `wall_ms.max(last_seq.saturating_add(1))`). -/
theorem job_seq (cf : Cf) (s : St) (home cls : Option Nat) (j : Rec) (h : recordJob cf s home cls = some j) :
    ∃ w, s.wall = some w ∧ j.seq = nextSeq w s.last := by
  unfold recordJob at h
  split at h
  · have := Option.some.inj h
    subst this
    exact ⟨_, ‹s.wall = some _›, rfl⟩
  · simp at h

/-- The number is the wall clock when the clock is past the last number. -/
theorem seq_wall_ahead (cf : Cf) (s : St) (home cls : Option Nat) (j : Rec) (w : Nat) (hw : s.wall = some w)
    (hl : s.last < w) (h : recordJob cf s home cls = some j) : j.seq = w := by
  obtain ⟨w', hw', e⟩ := job_seq cf s home cls j h
  have hww : w = w' := Option.some.inj (hw.symm.trans hw')
  simp only [nextSeq, sadd] at e
  omega

/-- When the clock did not move past the last number (a record signed again before the next clock, a clock set back),
the record takes the number one above it. -/
theorem seq_wall_behind (cf : Cf) (s : St) (home cls : Option Nat) (j : Rec) (w : Nat) (hw : s.wall = some w)
    (hl : w ≤ s.last) (hm : s.last < uMax) (h : recordJob cf s home cls = some j) : j.seq = s.last + 1 := by
  obtain ⟨w', hw', e⟩ := job_seq cf s home cls j h
  have hww : w = w' := Option.some.inj (hw.symm.trans hw')
  simp only [nextSeq, sadd] at e
  omega

/-- A record's number is above the last number. -/
theorem seq_above_last (cf : Cf) (s : St) (home cls : Option Nat) (j : Rec) (hm : s.last < uMax)
    (h : recordJob cf s home cls = some j) : s.last < j.seq := by
  obtain ⟨w, _, e⟩ := job_seq cf s home cls j h
  simp only [nextSeq, sadd] at e
  omega

/-- `restore_record_seq` raises the last number to the one given and never lowers it. -/
theorem restore_raises (cf : Cf) (s : St) (n : Nat) : (step cf s (.restore n)).last = max s.last n := rfl

/-- No step lowers the last number (up to `u64::MAX`, where the code's addition saturates). -/
theorem step_floor (cf : Cf) (s : St) (o : Op) : min s.last uMax ≤ min (step cf s o).last uMax := by
  cases ho : lastOp o with
  | false =>
    have := step_last cf s o ho
    omega
  | true =>
    cases o with
    | restore n =>
      show min s.last uMax ≤ min (max s.last n) uMax
      omega
    | start now hm c =>
      simp only [step, start]
      split
      · exact Nat.le_refl _
      · split
        · exact Nat.le_refl _
        · split
          · split
            · rename_i j hj
              obtain ⟨w, _, e⟩ := job_seq cf s hm c j hj
              simp only [nextSeq, sadd] at e
              show min s.last uMax ≤ min j.seq uMax
              omega
            · exact Nat.le_refl _
          · exact Nat.le_refl _
    | _ => simp [lastOp] at ho

theorem run_floor (cf : Cf) (s : St) (ops : List Op) : min s.last uMax ≤ min (run cf s ops).last uMax := by
  induction ops generalizing s with
  | nil => exact Nat.le_refl _
  | cons o ops ih =>
    show min s.last uMax ≤ min (run cf (step cf s o) ops).last uMax
    exact Nat.le_trans (step_floor cf s o) (ih _)

/-- The relay refuses a record whose number is not above the stored one (unless it is the stored record itself). -/
theorem not_above_refused (cf : Vinc.ConnectRecords.Cf) (st : Vinc.ConnectRecords.St) (now : Nat)
    (r : Vinc.ConnectRecords.Rec) (e : Vinc.ConnectRecords.Ent)
    (h : Vinc.ConnectRecords.find st.ents r.node = some e) (hle : r.seq ≤ e.r.seq) (hd : r ≠ e.r) :
    Vinc.ConnectRecords.accept cf st now r = (.stale, st) := by
  rcases Nat.lt_or_ge r.seq e.r.seq with hl | hg
  · exact Vinc.ConnectRecords.accept_lower cf st now r e h hl
  · exact Vinc.ConnectRecords.accept_equal_diff cf st now r e h (by omega) hd

/-! ## When a record is signed -/

/-- A job starts when a record is wanted, none is outstanding and the clock is known: its candidates are those of
that moment, its number follows the clock and the last number, and it becomes the last number. -/
theorem start_job (cf : Cf) (s : St) (now : Nat) (home cls : Option Nat) (w : Nat) (j : Rec)
    (h0 : s.job = none) (hw : s.wall = some w) (hwant : s.want = true)
    (hj : recordJob cf s home cls = some j) :
    step cf s (.start now home cls) = { s with want := false, job := some j, last := j.seq } ∧
      j.addrs = cands cf s ∧ j.seq = nextSeq w s.last := by
  obtain ⟨w', hw', e⟩ := job_seq cf s home cls j hj
  have hww : w = w' := Option.some.inj (hw.symm.trans hw')
  subst hww
  refine ⟨?_, ?_, e⟩
  · simp [step, start, h0, hw, hwant, hj]
  · unfold recordJob at hj
    split at hj
    · have := Option.some.inj hj
      subst this
      rfl
    · simp at hj

/-- Without a home or a class the wanted record is dropped and tried again a retry period later. -/
theorem start_blocked (cf : Cf) (s : St) (now : Nat) (home cls : Option Nat) (w : Nat)
    (h0 : s.job = none) (hw : s.wall = some w) (hwant : s.want = true) (hj : recordJob cf s home cls = none) :
    step cf s (.start now home cls) = { s with want := false, np := sadd now retry } := by
  simp [step, start, h0, hw, hwant, hj]

/-- Nothing starts without the wanted record, with a job outstanding, or before the first wall clock. -/
theorem start_idle (cf : Cf) (s : St) (now : Nat) (home cls : Option Nat)
    (h : s.want = false ∨ s.job.isSome = true ∨ s.wall = none) : step cf s (.start now home cls) = s := by
  simp only [step, start]
  rcases h with h | h | h
  · split
    · rfl
    · split
      · rfl
      · simp [h]
  · split
    · rfl
    · rename_i hj; simp [hj] at h
  · simp [h]

def jobOp : Op → Bool
  | .start _ _ _ => true
  | .signed _ _ _ => true
  | _ => false

def signedOp : Op → Bool
  | .signed _ _ _ => true
  | _ => false

theorem step_job (cf : Cf) (s : St) (o : Op) (h : jobOp o = false) : (step cf s o).job = s.job := by
  cases o with
  | answer f n a => simp only [step]; unfold observe; split; rfl; split <;> rfl
  | publish now c => simp only [step, publish]; split; rfl; split <;> rfl
  | start _ _ _ => simp [jobOp] at h
  | signed _ _ _ => simp [jobOp] at h
  | setLocal _ => rfl
  | probe _ => rfl
  | restart => rfl
  | tick w => cases w <;> rfl
  | hints _ => rfl
  | changed _ => rfl
  | restore _ => rfl

theorem step_sent (cf : Cf) (s : St) (o : Op) (h : signedOp o = false) : (step cf s o).sent = s.sent := by
  cases o with
  | answer f n a => simp only [step]; unfold observe; split; rfl; split <;> rfl
  | publish now c => simp only [step, publish]; split; rfl; split <;> rfl
  | start now hm c =>
    simp only [step, start]; split; rfl; split; rfl; split; split <;> rfl; rfl
  | signed _ _ _ => simp [signedOp] at h
  | setLocal _ => rfl
  | probe _ => rfl
  | restart => rfl
  | tick w => cases w <;> rfl
  | hints _ => rfl
  | changed _ => rfl
  | restore _ => rfl

theorem run_job_fixed (cf : Cf) (s : St) (ops : List Op) (h : ∀ o ∈ ops, jobOp o = false) :
    (run cf s ops).job = s.job := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    show (run cf (step cf s o) ops).job = s.job
    rw [ih _ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')), step_job cf s o (h o (by simp))]

theorem run_sent_fixed (cf : Cf) (s : St) (ops : List Op) (h : ∀ o ∈ ops, signedOp o = false) :
    (run cf s ops).sent = s.sent := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    show (run cf (step cf s o) ops).sent = s.sent
    rw [ih _ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')), step_sent cf s o (h o (by simp))]

/-- The answer to the signature hands the job on, as it was when it started, and only then. -/
theorem signed_sent (s : St) (now : Nat) (j : Rec) (h : s.job = some j) :
    (signed s now true true).sent = some j ∧ (signed s now true true).job = none := by
  simp [signed, h]

/-- A reflexive address learnt (or any change) after the job started is not in the record that job becomes. -/
theorem later_address_waits (cf : Cf) (s : St) (now now' : Nat) (home cls : Option Nat) (w : Nat) (j : Rec)
    (ops : List Op) (hops : ∀ o ∈ ops, jobOp o = false)
    (h0 : s.job = none) (hw : s.wall = some w) (hwant : s.want = true)
    (hj : recordJob cf s home cls = some j) :
    (run cf (step cf s (.start now home cls)) (ops ++ [.signed now' true true])).sent = some j ∧
      j.addrs = cands cf s := by
  obtain ⟨e, ha, _⟩ := start_job cf s now home cls w j h0 hw hwant hj
  refine ⟨?_, ha⟩
  have : run cf (step cf s (.start now home cls)) (ops ++ [.signed now' true true]) =
      step cf (run cf (step cf s (.start now home cls)) ops) (.signed now' true true) := by
    simp [run, List.foldl_append]
  rw [this]
  have hjob := run_job_fixed cf (step cf s (.start now home cls)) ops hops
  have hj2 : (run cf (step cf s (.start now home cls)) ops).job = some j := by rw [hjob, e]
  exact (signed_sent _ now' j hj2).1

/-- A record is asked for 1800 s after the last one handed to the carrier, not before. -/
theorem republish_not_before (s : St) (j : Rec) (now now' : Nat) (c : Bool) (h : s.job = some j)
    (hl : now + repub < uMax) (hn : now' < now + repub) :
    publish (signed s now true true) now' c = signed s now true true := by
  have e : (signed s now true true).np = now + repub := by
    simp [signed, h, sadd, Nat.min_eq_left (Nat.le_of_lt hl)]
  unfold publish
  rw [if_pos]
  rw [e]; right; right; left; exact hn

theorem republish_at (s : St) (j : Rec) (now now' : Nat) (h : s.job = some j) (hwant : s.want = false)
    (hl : now + repub < uMax) (hn : now + repub ≤ now') :
    (publish (signed s now true true) now' true).want = true := by
  have e : (signed s now true true).np = now + repub := by
    simp [signed, h, sadd, Nat.min_eq_left (Nat.le_of_lt hl)]
  have e2 : (signed s now true true).want = false := by simp [signed, h, hwant]
  have e3 : (signed s now true true).job = none := by simp [signed, h]
  unfold publish
  rw [if_neg]
  · rw [if_pos rfl]
  · rw [e, e2, e3]
    have : repub > 0 := by decide
    simp only [not_or]
    refine ⟨by omega, by omega, by omega, by simp, by simp⟩

/-- A class or home change, or an opened carrier, sets the next publish to now: it is asked for at once. -/
theorem changed_then_publish (s : St) (now now' : Nat) (h0 : now ≠ 0) (hm : now ≠ uMax) (hn : now ≤ now')
    (hw : s.want = false) (hj : s.job = none) :
    (publish (changed s now) now' true).want = true := by
  unfold publish changed
  rw [if_neg]
  · rw [if_pos rfl]
  · simp only [not_or]
    refine ⟨h0, hm, by omega, by simp [hw], by simp [hj]⟩

/-- The record is wanted anew only by new hints or by the publish timer, which needs a due time, an open home carrier
and no record already wanted. -/
theorem want_rises (cf : Cf) (s : St) (o : Op) (hw : s.want = false) (h : (step cf s o).want = true) :
    (∃ x, o = .hints x) ∨ (∃ now, o = .publish now true ∧ s.np ≠ 0 ∧ s.np ≠ uMax ∧ s.np ≤ now ∧ s.job = none) := by
  cases o with
  | hints x => exact Or.inl ⟨x, rfl⟩
  | publish now c =>
    right
    refine ⟨now, ?_⟩
    unfold step publish at h
    by_cases hc : s.np = 0 ∨ s.np = uMax ∨ now < s.np ∨ s.want = true ∨ s.job.isSome = true
    · simp only [hc, if_true] at h; simp [hw] at h
    · simp only [hc, if_false] at h
      cases c with
      | false => simp [hw] at h
      | true =>
        simp only [not_or] at hc
        refine ⟨rfl, hc.1, hc.2.1, by omega, ?_⟩
        cases hj : s.job with
        | none => rfl
        | some _ => simp [hj] at hc
  | setLocal a => simp [step, setLocal, hw] at h
  | probe ns => simp [step, probeAll, hw] at h
  | answer f n a =>
    simp only [step] at h; unfold observe at h
    split at h
    · simp [hw] at h
    · split at h <;> simp [hw] at h
  | restart => simp [step, restart, hw] at h
  | tick w => cases w <;> simp [step, tick, hw] at h
  | changed now => simp [step, changed, hw] at h
  | restore n => simp [step, restoreSeq, hw] at h
  | start now hm c =>
    simp only [step, start] at h
    split at h
    · simp [hw] at h
    · split at h
      · simp [hw] at h
      · split at h
        · split at h <;> simp at h
        · simp [hw] at h
  | signed now ok sent =>
    simp only [step, signed] at h
    split at h
    · simp [hw] at h
    · split at h
      · split at h <;> simp [hw] at h
      · simp [hw] at h

/-! ## Consecutive records -/

/-- Every record's number is strictly above the one before it, whatever happens in between: ticks with no clock, the
same clock or a clock set back, restores, other records (below `u64::MAX`, where the code's addition saturates). -/
theorem seq_rises (cf : Cf) (s : St) (now : Nat) (home cls home' cls' : Option Nat) (j1 j2 : Rec) (ops : List Op)
    (h0 : s.job = none) (hwant : s.want = true) (h1 : recordJob cf s home cls = some j1)
    (h2 : recordJob cf (run cf (step cf s (.start now home cls)) ops) home' cls' = some j2) (hm : j1.seq < uMax) :
    j1.seq < j2.seq := by
  obtain ⟨w1, hw1, _⟩ := job_seq cf s home cls j1 h1
  have e1 : (step cf s (.start now home cls)).last = j1.seq := by
    rw [(start_job cf s now home cls w1 j1 h0 hw1 hwant h1).1]
  have f := run_floor cf (step cf s (.start now home cls)) ops
  rw [e1] at f
  obtain ⟨w2, _, e2⟩ := job_seq cf _ home' cls' j2 h2
  simp only [nextSeq, sadd] at e2
  omega

/-- With no restore and no other record between two records, the second is one above the first when the clock at it is
not past the first's number. -/
theorem seq_next_behind (cf : Cf) (s : St) (now : Nat) (home cls home' cls' : Option Nat) (j1 j2 : Rec)
    (ops : List Op) (w2 : Nat) (hops : ∀ o ∈ ops, lastOp o = false) (h0 : s.job = none) (hwant : s.want = true)
    (hw2 : (run cf (step cf s (.start now home cls)) ops).wall = some w2) (hle : w2 ≤ j1.seq)
    (h1 : recordJob cf s home cls = some j1)
    (h2 : recordJob cf (run cf (step cf s (.start now home cls)) ops) home' cls' = some j2) (hm : j1.seq < uMax) :
    j2.seq = j1.seq + 1 := by
  obtain ⟨w1, hw1, _⟩ := job_seq cf s home cls j1 h1
  have hlast : (run cf (step cf s (.start now home cls)) ops).last = j1.seq := by
    rw [run_last cf _ ops hops, (start_job cf s now home cls w1 j1 h0 hw1 hwant h1).1]
  obtain ⟨w, hw, e2⟩ := job_seq cf _ home' cls' j2 h2
  have hww : w2 = w := Option.some.inj (hw2.symm.trans hw)
  simp only [nextSeq, sadd] at e2
  omega

/-- #287 fixed: two records with no tick that had a wall clock between them, and no restore and no other record, are
one apart (the code before gave them the same number, which the relay refuses). -/
theorem same_tick_next_seq (cf : Cf) (s : St) (now : Nat) (home cls home' cls' : Option Nat) (j1 j2 : Rec)
    (ops : List Op) (hops : ∀ o ∈ ops, clockOp o = false ∧ lastOp o = false) (h0 : s.job = none)
    (hwant : s.want = true) (h1 : recordJob cf s home cls = some j1)
    (h2 : recordJob cf (run cf (step cf s (.start now home cls)) ops) home' cls' = some j2) (hm : j1.seq < uMax) :
    j2.seq = j1.seq + 1 := by
  obtain ⟨w1, hw1, e1⟩ := job_seq cf s home cls j1 h1
  have hw : (run cf (step cf s (.start now home cls)) ops).wall = some w1 := by
    rw [run_wall cf _ ops (fun o ho => (hops o ho).1), step_wall cf s (.start now home cls) rfl]
    exact hw1
  simp only [nextSeq, sadd] at e1
  exact seq_next_behind cf s now home cls home' cls' j1 j2 ops w1 (fun o ho => (hops o ho).2) h0 hwant hw
    (by omega) h1 h2 hm

/-- A clock set back does not lower the number: with no restore and no other record in between, the record after it is
one above the record before (the code before gave it a lower number, which the relay refuses). -/
theorem clock_set_back_next_seq (cf : Cf) (s : St) (now : Nat) (home cls home' cls' : Option Nat) (j1 j2 : Rec)
    (ops : List Op) (w1 w2 : Nat) (hops : ∀ o ∈ ops, lastOp o = false) (h0 : s.job = none) (hwant : s.want = true)
    (hw1 : s.wall = some w1) (hw2 : (run cf (step cf s (.start now home cls)) ops).wall = some w2) (hlt : w2 < w1)
    (h1 : recordJob cf s home cls = some j1)
    (h2 : recordJob cf (run cf (step cf s (.start now home cls)) ops) home' cls' = some j2) (hm : j1.seq < uMax) :
    j2.seq = j1.seq + 1 := by
  obtain ⟨w, hw, e1⟩ := job_seq cf s home cls j1 h1
  have hww : w1 = w := Option.some.inj (hw1.symm.trans hw)
  simp only [nextSeq, sadd] at e1
  exact seq_next_behind cf s now home cls home' cls' j1 j2 ops w2 hops h0 hwant hw2 (by omega) h1 h2 hm

/-- The relay stores the node's next record over the one before it, whose number it holds: so the refusal of a number
that is not above the stored one (`not_above_refused`) never meets a node's own consecutive records. -/
theorem next_record_stored (rcf : Vinc.ConnectRecords.Cf) (st : Vinc.ConnectRecords.St) (t : Nat)
    (r : Vinc.ConnectRecords.Rec) (e : Vinc.ConnectRecords.Ent) (hf : Vinc.ConnectRecords.find st.ents r.node = some e)
    (cf : Cf) (s : St) (now : Nat) (home cls home' cls' : Option Nat) (j1 j2 : Rec) (ops : List Op)
    (h0 : s.job = none) (hwant : s.want = true) (h1 : recordJob cf s home cls = some j1)
    (h2 : recordJob cf (run cf (step cf s (.start now home cls)) ops) home' cls' = some j2) (hm : j1.seq < uMax)
    (he : e.r.seq = j1.seq) (hr : r.seq = j2.seq) :
    Vinc.ConnectRecords.accept rcf st t r = (.stored, { st with ents := Vinc.ConnectRecords.put st.ents ⟨r, t⟩ }) := by
  have := seq_rises cf s now home cls home' cls' j1 j2 ops h0 hwant h1 h2 hm
  exact Vinc.ConnectRecords.accept_higher rcf st t r e hf (by omega)

end Vinc.ConnectOwn
