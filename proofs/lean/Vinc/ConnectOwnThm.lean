import Vinc.ConnectOwn
import Vinc.ConnectRecordsThm

/-!
# Theorems of the node's own record and address discovery

For the model of `ConnectOwn.lean`, over unbounded naturals and any `MAX_ADDRS` (`cf.cap`; the code's is 8):

* The candidate list: `cands_length` (at most `cap`), `cands_prefix` (the reflexive addresses come first, in relay
  order), `cands_tail` (then the node's own addresses, in their order, each once, none already listed), `cands_room`
  (all of them when there is room), `cands_only` (nothing else). `reflexive_repeats` states the known behaviour #308: a
  reflexive address repeats once per relay that reported it; `reflexive_dropped`: a ninth reflexive address is dropped.
* The QADR answer: `observe_took` (taken only from the first relay with that configured address, for the nonce of its
  outstanding probe; it clears that probe, records the address, and changes no other relay), `observe_refused` (an
  answer not taken changes nothing), `observe_once` (a probe is answered once).
* The sequence number is the wall clock of the last tick (`job_seq`). Two records signed with no tick that had a clock
  between them have the same number (`same_tick_same_seq`, `seq_rises_only_across_ticks`: #287); if the wall clock rose
  between the two record jobs the number rises, if it was set back the number falls (`seq_rises_with_wall`,
  `seq_falls_when_clock_set_back`, `seq_lt_iff`). The relay refuses a number that is not above the stored one
  (`not_above_refused`, from `ConnectRecords.lean`).
* When a record is signed: the candidates enter a job only when it starts (`start_job`), nothing else changes the job
  (`run_job_fixed`) and only the answer to the signature hands it on (`run_sent_fixed`, `signed_sent`), so a reflexive
  address learnt after the job started waits for the next one (`later_address_waits`). The record is asked for by a
  class or home change, an opened carrier (`changed_then_publish`), new hints (`want_rises`), or 1800 s after the last
  record handed to the carrier (`republish_not_before`, `republish_at`).
-/

namespace Vinc.ConnectOwn

/-! ## The candidate list -/

theorem addLocal_len (cap : Nat) (acc : List Nat) (a : Nat) (h : acc.length ≤ cap) :
    (addLocal cap acc a).length ≤ cap := by
  unfold addLocal
  split
  · rename_i hh; simp; omega
  · exact h

theorem foldl_len (cap : Nat) (l acc : List Nat) (h : acc.length ≤ cap) :
    (l.foldl (addLocal cap) acc).length ≤ cap := by
  induction l generalizing acc with
  | nil => exact h
  | cons a l ih => exact ih _ (addLocal_len cap acc a h)

theorem foldl_add (cap : Nat) (l acc : List Nat) :
    ∃ t, l.foldl (addLocal cap) acc = acc ++ t ∧ t.Nodup ∧ (∀ x ∈ t, x ∉ acc) ∧ t.Sublist l := by
  induction l generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons a l ih =>
    by_cases h : acc.length < cap ∧ a ∉ acc
    · obtain ⟨t, h1, h2, h3, h4⟩ := ih (acc ++ [a])
      refine ⟨a :: t, ?_, ?_, ?_, ?_⟩
      · simp only [List.foldl_cons, addLocal, if_pos h, h1]; simp
      · refine List.nodup_cons.2 ⟨?_, h2⟩
        intro hm; exact h3 a hm (by simp)
      · intro x hx hxa
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h.2 hxa
        · exact h3 x hx (by simp [hxa])
      · exact h4.cons₂ a
    · obtain ⟨t, h1, h2, h3, h4⟩ := ih acc
      refine ⟨t, ?_, h2, h3, h4.cons a⟩
      simp only [List.foldl_cons, addLocal, if_neg h, h1]

theorem foldl_room (cap : Nat) (l acc : List Nat) (hr : (l.foldl (addLocal cap) acc).length < cap) :
    ∀ x ∈ l, x ∈ l.foldl (addLocal cap) acc := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    intro x hx
    have hr' : (l.foldl (addLocal cap) (addLocal cap acc a)).length < cap := by simpa using hr
    obtain ⟨t, ht, _, _, _⟩ := foldl_add cap l (addLocal cap acc a)
    have hlen : (addLocal cap acc a).length < cap := by
      rw [ht] at hr'; simp at hr'; omega
    have ha : a ∈ addLocal cap acc a := by
      by_cases hh : acc.length < cap ∧ a ∉ acc
      · simp [addLocal, hh]
      · have e : addLocal cap acc a = acc := by simp [addLocal, hh]
        rw [e] at hlen ⊢
        exact Classical.byContradiction fun hc => hh ⟨hlen, hc⟩
    rcases List.mem_cons.1 hx with hx | hx
    · rw [hx]
      show a ∈ l.foldl (addLocal cap) (addLocal cap acc a)
      rw [ht]; exact List.mem_append_left _ ha
    · exact ih _ hr' x hx

/-- The record lists at most `cap` addresses. -/
theorem cands_length (cf : Cf) (s : St) : (cands cf s).length ≤ cf.cap := by
  unfold cands reflList
  exact foldl_len _ _ _ (by simp; omega)

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

theorem reflList_length (cf : Cf) (s : St) : (reflList cf s).length ≤ cf.cap := by simp [reflList]; omega

/-- #308: two relays that report the same reflexive address list it twice. -/
theorem reflexive_repeats :
    reflList ⟨8, [10, 11]⟩ { probe := [none, none], refl := [some 5, some 5] } = [5, 5] := by decide

/-- A ninth reflexive address is dropped (the cap is 8). -/
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

/-- The record's sequence number is the wall clock of the last tick that had one. -/
theorem job_seq (cf : Cf) (s : St) (home cls : Option Nat) (j : Rec) (h : recordJob cf s home cls = some j) :
    s.wall = some j.seq := by
  unfold recordJob at h
  split at h
  · have := Option.some.inj h
    subst this
    exact ‹s.wall = some _›
  · simp at h

/-- #287, as the code behaves: two records signed with no tick that had a wall clock between them carry the same
sequence number, whatever else changed in between (addresses, hints, class, home). -/
theorem same_tick_same_seq (cf : Cf) (s : St) (ops : List Op) (h : ∀ o ∈ ops, clockOp o = false)
    (home cls home' cls' : Option Nat) (j1 j2 : Rec)
    (h1 : recordJob cf s home cls = some j1) (h2 : recordJob cf (run cf s ops) home' cls' = some j2) :
    j1.seq = j2.seq := by
  have a := job_seq cf s home cls j1 h1
  have b := job_seq cf _ home' cls' j2 h2
  rw [run_wall cf s ops h, a] at b
  exact Option.some.inj b

/-- A different sequence number between two records means a tick with a wall clock came between them. -/
theorem seq_rises_only_across_ticks (cf : Cf) (s : St) (ops : List Op) (home cls home' cls' : Option Nat)
    (j1 j2 : Rec) (h1 : recordJob cf s home cls = some j1)
    (h2 : recordJob cf (run cf s ops) home' cls' = some j2) (hne : j1.seq ≠ j2.seq) :
    ∃ w, Op.tick (some w) ∈ ops := by
  refine Classical.byContradiction fun hc => ?_
  apply hne
  refine same_tick_same_seq cf s ops ?_ home cls home' cls' j1 j2 h1 h2
  intro o ho
  cases o with
  | tick w =>
    cases w with
    | none => rfl
    | some w => exact absurd ⟨w, ho⟩ hc
  | _ => rfl

/-- The positive property: if the wall clock rose between the two record jobs, the number rises. -/
theorem seq_rises_with_wall (cf : Cf) (s s' : St) (home cls home' cls' : Option Nat) (j1 j2 : Rec) (w1 w2 : Nat)
    (hw1 : s.wall = some w1) (hw2 : s'.wall = some w2) (hlt : w1 < w2)
    (h1 : recordJob cf s home cls = some j1) (h2 : recordJob cf s' home' cls' = some j2) : j1.seq < j2.seq := by
  have a := job_seq cf s home cls j1 h1
  have b := job_seq cf s' home' cls' j2 h2
  rw [hw1] at a; rw [hw2] at b
  have := Option.some.inj a; have := Option.some.inj b
  omega

/-- A clock set back gives a lower number than the record before it. -/
theorem seq_falls_when_clock_set_back (cf : Cf) (s s' : St) (home cls home' cls' : Option Nat) (j1 j2 : Rec)
    (w1 w2 : Nat) (hw1 : s.wall = some w1) (hw2 : s'.wall = some w2) (hlt : w2 < w1)
    (h1 : recordJob cf s home cls = some j1) (h2 : recordJob cf s' home' cls' = some j2) : j2.seq < j1.seq := by
  have a := job_seq cf s home cls j1 h1
  have b := job_seq cf s' home' cls' j2 h2
  rw [hw1] at a; rw [hw2] at b
  have := Option.some.inj a; have := Option.some.inj b
  omega

theorem seq_lt_iff (cf : Cf) (s s' : St) (home cls home' cls' : Option Nat) (j1 j2 : Rec)
    (h1 : recordJob cf s home cls = some j1) (h2 : recordJob cf s' home' cls' = some j2) :
    j1.seq < j2.seq ↔ ∃ w1 w2, s.wall = some w1 ∧ s'.wall = some w2 ∧ w1 < w2 := by
  have a := job_seq cf s home cls j1 h1
  have b := job_seq cf s' home' cls' j2 h2
  constructor
  · intro h; exact ⟨_, _, a, b, h⟩
  · rintro ⟨w1, w2, e1, e2, hl⟩
    exact seq_rises_with_wall cf s s' home cls home' cls' j1 j2 w1 w2 e1 e2 hl h1 h2

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
that moment. -/
theorem start_job (cf : Cf) (s : St) (now : Nat) (home cls : Option Nat) (w : Nat) (j : Rec)
    (h0 : s.job = none) (hw : s.wall = some w) (hwant : s.want = true)
    (hj : recordJob cf s home cls = some j) :
    step cf s (.start now home cls) = { s with want := false, job := some j } ∧ j.addrs = cands cf s ∧
      j.seq = w := by
  have a := job_seq cf s home cls j hj
  rw [hw] at a
  refine ⟨?_, ?_, (Option.some.inj a).symm⟩
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

end Vinc.ConnectOwn
