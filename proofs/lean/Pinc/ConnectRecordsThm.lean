import Pinc.ConnectRecords

/-!
# Theorems of the record store

Properties of the model of `ConnectRecords.lean`, for every state and every call, over unbounded `Nat`.

* The table: `Inv` (at most `R` entries, at most one per node id, every one verified) holds of the empty store and is kept
  by every call (`inv_store`, `inv_timeout`, `inv_republish`; `highest_reach` for a whole run).
* The accept rule: `accept_lower` and `accept_equal_diff` (a lower sequence number, or an equal one with different
  bytes, is refused and changes nothing), `accept_equal_same` (an equal one with the same bytes only renews its receive
  time), `accept_higher` (a higher one replaces, no other entry changes), `accept_new`, `accept_full`.
* Verification: `store_bad` (a record that does not verify is refused and nothing changes), `store_wrong_owner`,
  `store_ok_verified` (an accepted record verified and is its owner's), `store_ok_stored` (an accepted record is stored
  under its node), `store_lower`, `store_equal_diff`, `store_equal_same`, `store_higher` (the accept rule at `store`).
* The highest number: `highest_reach` (after any sequence of calls from the empty store, the stored record of a node has
  the highest sequence number accepted since the node had none stored).
* Replication: `publish_sync` (a published record goes once to every used peer slot, in slot order, with its length),
  `replica_quiet` (a replica or restored record, and any refused one, sends no frame).
* Lookup: `lookup_spec`, `lookup_none`, `answer_spec` (only a stored, unexpired, verified record is answered, too
  large when over the datagram), `answer_pure` (a lookup changes nothing but its counter).
* Expiry: `sweep_mem` (the sweep keeps exactly the unexpired records), `timeout_sweeps` (a call at least one sweep
  period after the previous one sweeps, and leaves no expired record), `timeout_dropped` (only expired records are dropped),
  `ttl_periods` (the lifetime is three republish periods of 1800 s).
* The own record: `setOwn_armed`, `republish_spec`, `republish_early`, `republish_frames`.
-/

namespace Pinc.ConnectRecords
open Pinc.ConnectRelay (V Ef)

/-! ### The table -/

theorem find_some {l : List Ent} {n : Nat} {e : Ent} (h : find l n = some e) : e ∈ l ∧ e.r.node = n := by
  unfold find at h
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using this⟩

theorem find_none {l : List Ent} {n : Nat} (h : find l n = none) : ∀ e ∈ l, e.r.node ≠ n := by
  unfold find at h
  intro e he hn
  have := List.find?_eq_none.mp h e he
  simp [hn] at this

theorem find_put_same (l : List Ent) (e : Ent) : find (put l e) e.r.node = some e := by
  simp [find, put]

theorem find_put_ne (l : List Ent) (e : Ent) (n : Nat) (h : n ≠ e.r.node) : find (put l e) n = find l n := by
  unfold find put
  rw [List.find?_cons_of_neg (by simpa using Ne.symm h)]
  induction l with
  | nil => simp
  | cons x t ih =>
    by_cases hx : (x.r.node != e.r.node) = true
    · by_cases hn : (x.r.node == n) = true
      · simp [hx, hn]
      · simp [hx, hn, ih]
    · have hx' : x.r.node = e.r.node := by simpa using hx
      have : (x.r.node == n) = false := by
        simp [hx']; exact fun h' => h h'.symm
      simp [hx, this, ih]

theorem mem_put {l : List Ent} {e x : Ent} : x ∈ put l e ↔ x = e ∨ (x ∈ l ∧ x.r.node ≠ e.r.node) := by
  simp [put, List.mem_filter]

/-- The invariant of the table: at most `R` entries, one per node id, each verified. -/
def Inv (cf : Cf) (st : St) : Prop :=
  List.Pairwise (fun a b : Ent => a.r.node ≠ b.r.node) st.ents ∧ st.ents.length ≤ cf.R ∧ ∀ e ∈ st.ents, e.r.ok = true

theorem inv_empty (cf : Cf) : Inv cf (St.new cf) := by
  simp [Inv, St.new]

theorem pairwise_put {l : List Ent} (e : Ent) (h : List.Pairwise (fun a b : Ent => a.r.node ≠ b.r.node) l) :
    List.Pairwise (fun a b : Ent => a.r.node ≠ b.r.node) (put l e) := by
  unfold put
  rw [List.pairwise_cons]
  refine ⟨?_, h.filter _⟩
  intro a ha
  simp [List.mem_filter] at ha
  exact fun h' => ha.2 h'.symm

theorem length_put_le {l : List Ent} (e : Ent) (h : ∃ x ∈ l, x.r.node = e.r.node) : (put l e).length ≤ l.length := by
  obtain ⟨x, hx, hn⟩ := h
  unfold put
  simp only [List.length_cons]
  have : (l.filter (fun y => y.r.node != e.r.node)).length < l.length := by
    rw [List.length_filter_lt_length_iff_exists]
    exact ⟨x, hx, by simp [hn]⟩
  omega

theorem length_put_new {l : List Ent} (e : Ent) (h : ∀ x ∈ l, x.r.node ≠ e.r.node) : (put l e).length = l.length + 1 := by
  unfold put
  have : l.filter (fun y => y.r.node != e.r.node) = l := by
    apply List.filter_eq_self.mpr
    intro a ha; simpa using h a ha
  simp [this]

/-! ### The accept rule -/

theorem accept_lower (cf : Cf) (st : St) (now : Nat) (r : Rec) (s : Ent) (h : find st.ents r.node = some s)
    (hl : r.seq < s.r.seq) : accept cf st now r = (.stale, st) := by
  simp [accept, h, hl]

theorem accept_equal_diff (cf : Cf) (st : St) (now : Nat) (r : Rec) (s : Ent) (h : find st.ents r.node = some s)
    (he : r.seq = s.r.seq) (hd : r ≠ s.r) : accept cf st now r = (.stale, st) := by
  simp [accept, h, he, hd]

theorem accept_equal_same (cf : Cf) (st : St) (now : Nat) (r : Rec) (s : Ent) (h : find st.ents r.node = some s)
    (he : r = s.r) :
    accept cf st now r = (.refreshed, { st with ents := put st.ents ⟨r, now⟩ }) := by
  subst he
  simp [accept, h]

theorem accept_higher (cf : Cf) (st : St) (now : Nat) (r : Rec) (s : Ent) (h : find st.ents r.node = some s)
    (hh : s.r.seq < r.seq) :
    accept cf st now r = (.stored, { st with ents := put st.ents ⟨r, now⟩ }) := by
  have h1 : ¬ r.seq < s.r.seq := by omega
  have h2 : ¬ r.seq = s.r.seq := by omega
  simp [accept, h, h1, h2]

theorem accept_new (cf : Cf) (st : St) (now : Nat) (r : Rec) (h : find st.ents r.node = none)
    (hl : st.ents.length < cf.R) :
    accept cf st now r = (.stored, { st with ents := put st.ents ⟨r, now⟩ }) := by
  simp [accept, h]; omega

theorem accept_full (cf : Cf) (st : St) (now : Nat) (r : Rec) (h : find st.ents r.node = none)
    (hl : cf.R ≤ st.ents.length) : accept cf st now r = (.full, st) := by
  simp [accept, h, hl]

/-- Every outcome of `accept` is one of the five above. -/
theorem accept_cases (cf : Cf) (st : St) (now : Nat) (r : Rec) :
    ((accept cf st now r).1 = .stale ∧ (accept cf st now r).2 = st ∧
      ∃ s, find st.ents r.node = some s ∧ (r.seq < s.r.seq ∨ (r.seq = s.r.seq ∧ r ≠ s.r))) ∨
    ((accept cf st now r).1 = .refreshed ∧ (accept cf st now r).2 = { st with ents := put st.ents ⟨r, now⟩ } ∧
      ∃ s, find st.ents r.node = some s ∧ r = s.r) ∨
    ((accept cf st now r).1 = .full ∧ (accept cf st now r).2 = st ∧ find st.ents r.node = none ∧
      cf.R ≤ st.ents.length) ∨
    ((accept cf st now r).1 = .stored ∧ (accept cf st now r).2 = { st with ents := put st.ents ⟨r, now⟩ } ∧
      ((∃ s, find st.ents r.node = some s ∧ s.r.seq < r.seq) ∨
        (find st.ents r.node = none ∧ st.ents.length < cf.R))) := by
  unfold accept
  cases hf : find st.ents r.node with
  | none =>
    by_cases hl : cf.R ≤ st.ents.length
    · simp [hl]
    · simp [hl]; omega
  | some s =>
    by_cases h1 : r.seq < s.r.seq
    · simp [h1]
    · by_cases h2 : r.seq = s.r.seq
      · by_cases h3 : r = s.r
        · simp [h3]
        · simp [h2, h3]
      · simp [h1, h2]; omega

/-! ### Store: verification, owner, and what an accepted record does -/

theorem fail_st (st : St) (w : String) (n : Nat) :
    (fail st w n).st.ents = st.ents ∧ (fail st w n).st.pr = st.pr ∧ (fail st w n).st.np = st.np ∧
      (fail st w n).st.ls = st.ls := by
  simp [fail]

theorem store_bad (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String) (h : r.ok = false) :
    store cf st now r owner origin = fail st "badrecord" owner := by
  simp [store, h]

theorem store_wrong_owner (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String)
    (h : r.ok = true) (ho : owner ≠ 0) (hn : owner ≠ r.node) :
    store cf st now r owner origin = fail st "wrongowner" owner := by
  simp [store, h, ho, hn]

/-- What a call of `store` leaves: peers, timers unchanged; a refusal changes no entry; an acceptance is a verified record
of its owner, and the entries are the accept rule's. -/
theorem store_facts (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String) :
    (store cf st now r owner origin).st.pr = st.pr ∧ (store cf st now r owner origin).st.np = st.np ∧
    (store cf st now r owner origin).st.ls = st.ls ∧
    ((store cf st now r owner origin).res = "ok" →
      r.ok = true ∧ (owner = 0 ∨ owner = r.node) ∧
      (store cf st now r owner origin).st.ents = put st.ents ⟨r, now⟩ ∧
      (find st.ents r.node = none → st.ents.length < cf.R) ∧
      (∀ s, find st.ents r.node = some s → s.r.seq ≤ r.seq)) ∧
    ((store cf st now r owner origin).res ≠ "ok" → (store cf st now r owner origin).st.ents = st.ents) := by
  unfold store
  by_cases hk : r.ok = true
  · by_cases ho : (owner != 0 && owner != r.node) = true
    · simp [hk, ho, fail]
    · have ho' : owner = 0 ∨ owner = r.node := by
        simp at ho; omega
      rcases accept_cases cf st now r with ⟨h1, h2, s, hs, hl⟩ | ⟨h1, h2, s, hs, he⟩ | ⟨h1, h2, hn, hf⟩ | ⟨h1, h2, hx⟩
      · have : (accept cf st now r) = (.stale, st) := Prod.ext h1 h2
        simp [hk, ho, this, fail]
      · have : (accept cf st now r) = (.refreshed, { st with ents := put st.ents ⟨r, now⟩ }) := Prod.ext h1 h2
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [hk, ho, this]
        refine ⟨ho', ?_, ?_⟩
        · intro h; rw [hs] at h; simp at h
        · intro s' hs'; rw [hs] at hs'; simp at hs'; subst hs'
          have h3 := congrArg Rec.seq he; omega
      · have : (accept cf st now r) = (.full, st) := Prod.ext h1 h2
        simp [hk, ho, this, fail]
      · have : (accept cf st now r) = (.stored, { st with ents := put st.ents ⟨r, now⟩ }) := Prod.ext h1 h2
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [hk, ho, this]
        refine ⟨ho', ?_, ?_⟩
        · intro hn
          rcases hx with ⟨s, hs, _⟩ | ⟨_, hl⟩
          · rw [hn] at hs; simp at hs
          · exact hl
        · intro s' hs'
          rcases hx with ⟨s, hs, hl⟩ | ⟨hn, _⟩
          · rw [hs] at hs'; simp at hs'; subst hs'; omega
          · rw [hn] at hs'; simp at hs'
  · simp at hk
    simp [hk, fail]

theorem store_lower (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String) (hk : r.ok = true)
    (ho : owner = 0 ∨ owner = r.node) (s : Ent) (hs : find st.ents r.node = some s) (hl : r.seq < s.r.seq) :
    (store cf st now r owner origin).res = "stalerec" ∧ (store cf st now r owner origin).st.ents = st.ents := by
  have ho' : (owner != 0 && owner != r.node) = false := by
    rcases ho with h | h <;> simp [h]
  simp [store, hk, ho', accept_lower cf st now r s hs hl, fail]

theorem store_equal_diff (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String) (hk : r.ok = true)
    (ho : owner = 0 ∨ owner = r.node) (s : Ent) (hs : find st.ents r.node = some s) (he : r.seq = s.r.seq)
    (hd : r ≠ s.r) :
    (store cf st now r owner origin).res = "stalerec" ∧ (store cf st now r owner origin).st.ents = st.ents := by
  have ho' : (owner != 0 && owner != r.node) = false := by
    rcases ho with h | h <;> simp [h]
  simp [store, hk, ho', accept_equal_diff cf st now r s hs he hd, fail]

theorem store_equal_same (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String) (hk : r.ok = true)
    (ho : owner = 0 ∨ owner = r.node) (s : Ent) (hs : find st.ents r.node = some s) (he : r = s.r) :
    (store cf st now r owner origin).res = "ok" ∧ (store cf st now r owner origin).st.ents = put st.ents ⟨r, now⟩ ∧
      (store cf st now r owner origin).ef = [] := by
  have ho' : (owner != 0 && owner != r.node) = false := by
    rcases ho with h | h <;> simp [h]
  simp [store, hk, ho', accept_equal_same cf st now r s hs he]

theorem store_higher (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String) (hk : r.ok = true)
    (ho : owner = 0 ∨ owner = r.node) (s : Ent) (hs : find st.ents r.node = some s) (hh : s.r.seq < r.seq) :
    (store cf st now r owner origin).res = "ok" ∧
      find (store cf st now r owner origin).st.ents r.node = some ⟨r, now⟩ ∧
      (∀ n, n ≠ r.node → find (store cf st now r owner origin).st.ents n = find st.ents n) := by
  have ho' : (owner != 0 && owner != r.node) = false := by
    rcases ho with h | h <;> simp [h]
  have e : (store cf st now r owner origin).st.ents = put st.ents ⟨r, now⟩ := by
    simp [store, hk, ho', accept_higher cf st now r s hs hh]
  refine ⟨by simp [store, hk, ho', accept_higher cf st now r s hs hh], ?_, ?_⟩
  · rw [e]; exact find_put_same _ _
  · intro n hn; rw [e]; exact find_put_ne _ _ _ hn

/-- An accepted record is stored under its node. -/
theorem store_ok_stored (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String)
    (h : (store cf st now r owner origin).res = "ok") :
    find (store cf st now r owner origin).st.ents r.node = some ⟨r, now⟩ ∧
      (∀ n, n ≠ r.node → find (store cf st now r owner origin).st.ents n = find st.ents n) := by
  obtain ⟨_, _, _, hok, _⟩ := store_facts cf st now r owner origin
  obtain ⟨_, _, e, _, _⟩ := hok h
  rw [e]
  exact ⟨find_put_same _ _, fun n hn => find_put_ne _ _ _ hn⟩

/-- An accepted record verified and is its owner's. -/
theorem store_ok_verified (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String)
    (h : (store cf st now r owner origin).res = "ok") : r.ok = true ∧ (owner = 0 ∨ owner = r.node) := by
  obtain ⟨_, _, _, hok, _⟩ := store_facts cf st now r owner origin
  obtain ⟨a, b, _⟩ := hok h
  exact ⟨a, b⟩

theorem inv_store (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String) (hI : Inv cf st) :
    Inv cf (store cf st now r owner origin).st := by
  obtain ⟨_, _, _, hok, hno⟩ := store_facts cf st now r owner origin
  by_cases h : (store cf st now r owner origin).res = "ok"
  · obtain ⟨hr, _, e, hnew, _⟩ := hok h
    obtain ⟨hp, hl, hall⟩ := hI
    refine ⟨?_, ?_, ?_⟩ <;> rw [e]
    · exact pairwise_put _ hp
    · by_cases hf : find st.ents r.node = none
      · have := hnew hf
        rw [length_put_new _ (find_none hf)]
        simp; omega
      · cases hs : find st.ents r.node with
        | none => exact absurd hs hf
        | some s =>
          have := find_some hs
          exact Nat.le_trans (length_put_le _ ⟨s, this.1, this.2⟩) hl
    · intro x hx
      rcases mem_put.mp hx with rfl | ⟨hx, _⟩
      · exact hr
      · exact hall x hx
  · have e := hno h
    obtain ⟨hp, hl, hall⟩ := hI
    refine ⟨?_, ?_, ?_⟩ <;> rw [e]
    · exact hp
    · exact hl
    · exact hall

/-! ### Replication -/

theorem sync_targets (st : St) (len : Nat) :
    sync st len = (st.pr.filter (· != 0)).map fun p => [V.s "peer", V.n p, V.s "sync", V.n len] :=
  rfl

theorem store_ef_trace (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String) :
    ∀ x ∈ (store cf st now r owner origin).ef, x.head? = some (V.s "t") := by
  intro x hx
  unfold store at hx
  by_cases hk : r.ok = true
  · by_cases ho : (owner != 0 && owner != r.node) = true
    · simp [hk, ho, fail] at hx; simp [hx]
    · rcases accept_cases cf st now r with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
      · have : (accept cf st now r) = (.stale, st) := Prod.ext h1 h2
        simp [hk, ho, this, fail] at hx; simp [hx]
      · have : (accept cf st now r).1 = .refreshed := h1
        simp [hk, ho] at hx
        rcases hh : accept cf st now r with ⟨k, s⟩
        rw [hh] at this; simp at this; subst this
        simp [hh] at hx
      · have : (accept cf st now r) = (.full, st) := Prod.ext h1 h2
        simp [hk, ho, this, fail] at hx; simp [hx]
      · have : (accept cf st now r).1 = .stored := h1
        simp [hk, ho] at hx
        rcases hh : accept cf st now r with ⟨k, s⟩
        rw [hh] at this; simp at this; subst this
        simp [hh] at hx; simp [hx]
  · simp at hk; simp [hk, fail] at hx; simp [hx]

/-- A published (or own) record that was accepted goes once to every used peer slot, in slot order, carrying its length;
the frames come after the relay's own trace transitions. -/
theorem publish_sync (cf : Cf) (st : St) (now node : Nat) (r : Rec)
    (h : (publish cf st now node r).res = "ok") :
    (publish cf st now node r).ef = (store cf st now r node "publish").ef ++
      (st.pr.filter (· != 0)).map (fun p => [V.s "peer", V.n p, V.s "sync", V.n r.len]) := by
  obtain ⟨hp, _⟩ := store_facts cf st now r node "publish"
  have hs : (store cf st now r node "publish").res = "ok" := by
    unfold publish at h; by_cases c : ((store cf st now r node "publish").res != "ok") = true
    · simp [c] at h; exact h
    · simpa using c
  simp [publish, hs, sync_targets, hp]

theorem publish_refused (cf : Cf) (st : St) (now node : Nat) (r : Rec) (h : (publish cf st now node r).res ≠ "ok") :
    ∀ x ∈ (publish cf st now node r).ef, x.head? = some (V.s "t") := by
  intro x hx
  have hs : (store cf st now r node "publish").res ≠ "ok" := by
    intro c; apply h; simp [publish, c]
  simp [publish, hs] at hx
  exact store_ef_trace cf st now r node "publish" x hx

/-- A replica, a restored record and any refused call send no frame to a peer. -/
theorem replica_quiet (cf : Cf) (st : St) (now : Nat) (r : Rec) :
    ∀ x ∈ (replica cf st now r).ef, x.head? ≠ some (V.s "peer") := by
  intro x hx
  have := store_ef_trace cf st now r 0 "replica" x hx
  simp [this]

theorem restore_quiet (cf : Cf) (st : St) (received : Nat) (r : Rec) :
    ∀ x ∈ (restore cf st received r).ef, x.head? ≠ some (V.s "peer") := replica_quiet cf st received r

/-! ### Lookup -/

theorem find_of_mem {l : List Ent} (hp : List.Pairwise (fun a b : Ent => a.r.node ≠ b.r.node) l) {e : Ent}
    (he : e ∈ l) : find l e.r.node = some e := by
  unfold find
  induction l with
  | nil => simp at he
  | cons x t ih =>
    rw [List.pairwise_cons] at hp
    by_cases hx : x = e
    · subst hx; simp
    · have hm : e ∈ t := by
        rcases List.mem_cons.mp he with h | h
        · exact absurd h.symm hx
        · exact h
      have hne : x.r.node ≠ e.r.node := hp.1 e hm
      simp [hne, ih hp.2 hm]

/-- A lookup answers only with a stored, unexpired, verified record of the node asked about. -/
theorem lookup_spec (cf : Cf) (st : St) (hI : Inv cf st) (now peer : Nat) (r : Rec)
    (h : lookup st now peer = some r) :
    ∃ e ∈ st.ents, e.r = r ∧ r.node = peer ∧ now - e.rcv < recTtl ∧ r.ok = true := by
  unfold lookup at h
  cases hf : find st.ents peer with
  | none => simp [hf] at h
  | some e =>
    simp [hf] at h
    obtain ⟨hlt, hr⟩ := h
    have := find_some hf
    exact ⟨e, this.1, hr, by rw [← hr]; exact this.2, hlt, by rw [← hr]; exact hI.2.2 e this.1⟩

theorem lookup_none (st : St) (now peer : Nat) (e : Ent) (hI : List.Pairwise (fun a b : Ent => a.r.node ≠ b.r.node) st.ents)
    (he : e ∈ st.ents) (hn : e.r.node = peer) (hfresh : now - e.rcv < recTtl) : lookup st now peer = some e.r := by
  unfold lookup
  rw [← hn, find_of_mem hI he]
  simp [hfresh]

/-- No stored record is answered once it is expired, before or after the sweep. -/
theorem lookup_expired (st : St) (now peer : Nat) (e : Ent) (hf : find st.ents peer = some e)
    (hx : recTtl ≤ now - e.rcv) : lookup st now peer = none := by
  unfold lookup; simp [hf]; omega

theorem answer_pure (st : St) (now peer : Nat) : (answer st now peer).1 = { st with lookups := st.lookups + 1 } := by
  simp [answer]

theorem answer_spec (st : St) (now peer : Nat) :
    ((answer st now peer).2.2 = "absent" → lookup st now peer = none) ∧
    ((answer st now peer).2.2 = "record" → ∃ r, lookup st now peer = some r ∧ r.len ≤ maxDns) ∧
    ((answer st now peer).2.2 = "toolarge" → ∃ r, lookup st now peer = some r ∧ maxDns < r.len) := by
  unfold answer
  cases hl : lookup st now peer with
  | none => simp
  | some r =>
    by_cases hm : maxDns < r.len
    · simp [hm]
    · simp [hm]; omega

/-! ### Expiry -/

theorem ttl_periods : recTtl = 3 * repub ∧ repub = 1800 * sec ∧ sec = 1000000000 := ⟨rfl, rfl, rfl⟩

theorem sweep_mem (st : St) (now : Nat) (e : Ent) :
    e ∈ (sweepRecs st now).ents ↔ e ∈ st.ents ∧ now - e.rcv < recTtl := by
  simp [sweepRecs, List.mem_filter]

theorem republish_ls (cf : Cf) (st : St) (now : Nat) : (republishDue cf st now).1.ls = st.ls := by
  unfold republishDue
  by_cases h : (st.np == 0 || decide (now < st.np)) = true
  · simp [h]
  · simp only [h]
    cases find ({ st with np := now + repub }).ents cf.me <;> simp

theorem timeout_keep (cf : Cf) (st : St) (now : Nat) (h : now - st.ls < sweepNs) :
    timeout cf st now = ⟨(republishDue cf st now).1, "ok", (republishDue cf st now).2⟩ := by
  have hl := republish_ls cf st now
  have c : now - (republishDue cf st now).1.ls < sweepNs := by omega
  simp [timeout, c]

theorem timeout_sweep (cf : Cf) (st : St) (now : Nat) (h : sweepNs ≤ now - st.ls) :
    timeout cf st now = ⟨{ sweepRecs (republishDue cf st now).1 now with ls := now }, "ok", (republishDue cf st now).2⟩ := by
  have hl := republish_ls cf st now
  have c : ¬ now - (republishDue cf st now).1.ls < sweepNs := by omega
  simp [timeout, c]

/-- A call at least one sweep period after the previous one sweeps, and no expired record is left. -/
theorem timeout_sweeps (cf : Cf) (st : St) (now : Nat) (h : sweepNs ≤ now - st.ls) :
    (timeout cf st now).st.ls = now ∧ ∀ e ∈ (timeout cf st now).st.ents, now - e.rcv < recTtl := by
  rw [timeout_sweep cf st now h]
  refine ⟨rfl, ?_⟩
  intro e he
  exact ((sweep_mem _ now e).mp he).2

theorem timeout_no_sweep (cf : Cf) (st : St) (now : Nat) (h : now - st.ls < sweepNs) :
    (timeout cf st now).st.ls = st.ls ∧
      (timeout cf st now).st.ents = (republishDue cf st now).1.ents := by
  rw [timeout_keep cf st now h]
  exact ⟨republish_ls cf st now, rfl⟩

/-- A record the sweep drops was expired, and the sweep ran because a period had passed. -/
theorem timeout_dropped (cf : Cf) (st : St) (now : Nat) (e : Ent) (he : e ∈ (republishDue cf st now).1.ents)
    (hn : e ∉ (timeout cf st now).st.ents) : sweepNs ≤ now - st.ls ∧ recTtl ≤ now - e.rcv := by
  by_cases h : now - st.ls < sweepNs
  · exfalso; apply hn; rw [(timeout_no_sweep cf st now h).2]; exact he
  · have h2 : sweepNs ≤ now - st.ls := by omega
    refine ⟨h2, ?_⟩
    refine Nat.le_of_not_lt ?_
    intro hc
    apply hn
    rw [timeout_sweep cf st now h2]
    exact (sweep_mem _ now e).mpr ⟨he, hc⟩

/-! ### The own record and the republish timer -/

/-- `set_own_record` stores a record of this relay and arms the republish timer 1800 s ahead (`cf.me` is a node id,
never the "none" of the model's owner argument). -/
theorem setOwn_armed (cf : Cf) (st : St) (now : Nat) (r : Rec) (hme : cf.me ≠ 0)
    (h : (setOwn cf st now r).res = "ok") :
    (setOwn cf st now r).st.np = now + repub ∧ r.node = cf.me ∧ r.ok = true ∧
      find (setOwn cf st now r).st.ents cf.me = some ⟨r, now⟩ := by
  have hs : (store cf st now r cf.me "own").res = "ok" := by
    unfold setOwn at h; by_cases c : ((store cf st now r cf.me "own").res != "ok") = true
    · simp [c] at h; exact h
    · simpa using c
  have hv := store_ok_verified cf st now r cf.me "own" hs
  have hnode : r.node = cf.me := by
    rcases hv.2 with h0 | h0
    · exact absurd h0 hme
    · exact h0.symm
  have hf := (store_ok_stored cf st now r cf.me "own" hs).1
  rw [hnode] at hf
  refine ⟨by simp [setOwn, hs], hnode, hv.1, ?_⟩
  simpa [setOwn, hs] using hf

theorem republish_early (cf : Cf) (st : St) (now : Nat) (h : st.np = 0 ∨ now < st.np) :
    republishDue cf st now = (st, []) := by
  unfold republishDue
  have : (st.np == 0 || decide (now < st.np)) = true := by
    rcases h with h | h <;> simp [h]
  simp [this]

/-- Past the timer the next republish is 1800 s later, and the own record, if stored, is renewed and sent once to every
used peer slot in slot order, followed by the trace transition with the peer count. -/
theorem republish_spec (cf : Cf) (st : St) (now : Nat) (h0 : st.np ≠ 0) (h1 : st.np ≤ now) :
    (republishDue cf st now).1.np = now + repub ∧
    (∀ e, find st.ents cf.me = some e →
      find (republishDue cf st now).1.ents cf.me = some { e with rcv := now } ∧
      (republishDue cf st now).2 =
        (st.pr.filter (· != 0)).map (fun p => [V.s "peer", V.n p, V.s "sync", V.n e.r.len]) ++
          [[V.s "t", V.s "repub", V.n (peerCount st)]]) ∧
    (find st.ents cf.me = none → (republishDue cf st now).2 = []) := by
  have hc : ¬ (st.np == 0 || decide (now < st.np)) = true := by simp; omega
  unfold republishDue
  simp only [hc]
  cases hf : find st.ents cf.me with
  | none => simp [hf]
  | some e =>
    have hn := (find_some hf).2
    have hq : find (put st.ents { e with rcv := now }) cf.me = some { e with rcv := now } := by
      have := find_put_same st.ents { e with rcv := now }
      simpa [hn] using this
    simp [sync_targets, peerCount]
    exact hq

theorem republish_frames (cf : Cf) (st : St) (now : Nat) :
    (republishDue cf st now).1.pr = st.pr := by
  unfold republishDue
  split <;> simp
  split <;> simp

/-! ### The whole run: the invariant and the highest sequence number -/

theorem republish_ents (cf : Cf) (st : St) (now : Nat) :
    ∀ e ∈ (republishDue cf st now).1.ents, ∃ e0 ∈ st.ents, e0.r = e.r := by
  intro e he
  unfold republishDue at he
  by_cases h : (st.np == 0 || decide (now < st.np)) = true
  · simp only [h] at he; exact ⟨e, he, rfl⟩
  · simp only [h] at he
    cases hf : find ({ st with np := now + repub }).ents cf.me with
    | none => simp [hf] at he; exact ⟨e, he, rfl⟩
    | some e1 =>
      simp [hf] at he
      rcases mem_put.mp he with rfl | ⟨hm, _⟩
      · exact ⟨e1, (find_some hf).1, rfl⟩
      · exact ⟨e, hm, rfl⟩

theorem inv_republish (cf : Cf) (st : St) (now : Nat) (hI : Inv cf st) : Inv cf (republishDue cf st now).1 := by
  obtain ⟨hp, hl, hall⟩ := hI
  unfold republishDue
  by_cases h : (st.np == 0 || decide (now < st.np)) = true
  · simp only [h]; exact ⟨hp, hl, hall⟩
  · simp only [h]
    cases hf : find ({ st with np := now + repub }).ents cf.me with
    | none => simp; exact ⟨hp, hl, hall⟩
    | some e1 =>
      have hm := find_some hf
      simp only []
      refine ⟨pairwise_put _ hp, ?_, ?_⟩
      · exact Nat.le_trans (length_put_le _ ⟨e1, hm.1, hm.2.symm ▸ rfl⟩) hl
      · intro x hx
        rcases mem_put.mp hx with rfl | ⟨hx, _⟩
        · exact hall e1 hm.1
        · exact hall x hx

theorem inv_sweep (cf : Cf) (st : St) (now : Nat) (hI : Inv cf st) : Inv cf (sweepRecs st now) := by
  obtain ⟨hp, hl, hall⟩ := hI
  refine ⟨hp.filter _, ?_, ?_⟩
  · exact Nat.le_trans (List.length_filter_le _ _) hl
  · intro x hx
    exact hall x (List.mem_filter.mp hx).1

theorem inv_timeout (cf : Cf) (st : St) (now : Nat) (hI : Inv cf st) : Inv cf (timeout cf st now).st := by
  have h1 := inv_sweep cf _ now (inv_republish cf st now hI)
  by_cases h : now - st.ls < sweepNs
  · rw [timeout_keep cf st now h]; exact inv_republish cf st now hI
  · rw [timeout_sweep cf st now (by omega)]; exact h1

theorem timeout_ents (cf : Cf) (st : St) (now : Nat) :
    ∀ e ∈ (timeout cf st now).st.ents, ∃ e0 ∈ st.ents, e0.r = e.r := by
  intro e he
  by_cases h : now - st.ls < sweepNs
  · rw [timeout_keep cf st now h] at he; exact republish_ents cf st now e he
  · rw [timeout_sweep cf st now (by omega)] at he
    exact republish_ents cf st now e ((sweep_mem _ now e).mp he).1

theorem publish_core (cf : Cf) (st : St) (now node : Nat) (r : Rec) :
    (publish cf st now node r).res = (store cf st now r node "publish").res ∧
      (publish cf st now node r).st.ents = (store cf st now r node "publish").st.ents := by
  by_cases c : ((store cf st now r node "publish").res != "ok") = true <;> simp [publish, c]

theorem setOwn_core (cf : Cf) (st : St) (now : Nat) (r : Rec) :
    (setOwn cf st now r).res = (store cf st now r cf.me "own").res ∧
      (setOwn cf st now r).st.ents = (store cf st now r cf.me "own").st.ents := by
  by_cases c : ((store cf st now r cf.me "own").res != "ok") = true
  · simp [setOwn, c]
  · have h' : (store cf st now r cf.me "own").res = "ok" := by simpa using c
    simp [setOwn, h']

inductive Call
  | pub (now node : Nat) (r : Rec)
  | rep (now : Nat) (r : Rec)
  | rst (t : Nat) (r : Rec)
  | own (now : Nat) (r : Rec)
  | tm (now : Nat)

/-- The ghost: the highest sequence number accepted for a node since the node had no record stored. -/
def hiPut (hi : Nat → Nat) (n v : Nat) : Nat → Nat := fun m => if m == n then v else hi m

def HI (st : St) (hi : Nat → Nat) : Prop :=
  (∀ e ∈ st.ents, hi e.r.node = e.r.seq) ∧ (∀ n, find st.ents n = none → hi n = 0)

def storeStep (o : Out) (r : Rec) (hi : Nat → Nat) : St × (Nat → Nat) :=
  (o.st, if o.res == "ok" then hiPut hi r.node (max (hi r.node) r.seq) else hi)

def gstep (cf : Cf) (g : St × (Nat → Nat)) : Call → St × (Nat → Nat)
  | .pub now node r => storeStep (publish cf g.1 now node r) r g.2
  | .rep now r => storeStep (replica cf g.1 now r) r g.2
  | .rst t r => storeStep (restore cf g.1 t r) r g.2
  | .own now r => storeStep (setOwn cf g.1 now r) r g.2
  | .tm now => ((timeout cf g.1 now).st, fun n => if (find (timeout cf g.1 now).st.ents n).isSome then g.2 n else 0)

theorem hi_store (cf : Cf) (st : St) (now : Nat) (r : Rec) (owner : Nat) (origin : String) (hi : Nat → Nat)
    (hH : HI st hi) :
    HI (store cf st now r owner origin).st
      (if (store cf st now r owner origin).res == "ok" then hiPut hi r.node (max (hi r.node) r.seq) else hi) := by
  obtain ⟨_, _, _, hok, hno⟩ := store_facts cf st now r owner origin
  by_cases h : (store cf st now r owner origin).res = "ok"
  · obtain ⟨_, _, e, _, hmono⟩ := hok h
    have hb : ((store cf st now r owner origin).res == "ok") = true := by simpa using h
    simp only [hb, ite_true]
    unfold HI
    rw [e]
    have hle : hi r.node ≤ r.seq := by
      cases hf : find st.ents r.node with
      | none => rw [hH.2 _ hf]; exact Nat.zero_le _
      | some s =>
        have hs := find_some hf
        have := hH.1 s hs.1
        rw [hs.2] at this
        rw [this]; exact hmono s hf
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases mem_put.mp hx with rfl | ⟨hm, hne⟩
      · simp [hiPut]; omega
      · simp [hiPut, hne]; exact hH.1 x hm
    · intro n hn
      by_cases hnn : n = r.node
      · subst hnn; rw [find_put_same] at hn; simp at hn
      · rw [find_put_ne _ _ _ hnn] at hn
        simp [hiPut, hnn]; exact hH.2 n hn
  · have e := hno h
    have hb : ((store cf st now r owner origin).res == "ok") = false := by simpa using h
    simp only [hb]
    simp only [Bool.false_eq_true, ite_false]
    unfold HI
    refine ⟨?_, ?_⟩
    · intro x hx; rw [e] at hx; exact hH.1 x hx
    · intro n hn; rw [e] at hn; exact hH.2 n hn

theorem gstep_inv (cf : Cf) (g : St × (Nat → Nat)) (c : Call) (h : Inv cf g.1 ∧ HI g.1 g.2) :
    Inv cf (gstep cf g c).1 ∧ HI (gstep cf g c).1 (gstep cf g c).2 := by
  obtain ⟨hI, hH⟩ := h
  cases c with
  | pub now node r =>
    obtain ⟨c1, c2⟩ := publish_core cf g.1 now node r
    have a := inv_store cf g.1 now r node "publish" hI
    have b := hi_store cf g.1 now r node "publish" g.2 hH
    simp only [gstep, storeStep, c1]
    unfold Inv HI at *
    rw [c2]; exact ⟨a, b⟩
  | rep now r =>
    have a := inv_store cf g.1 now r 0 "replica" hI
    have b := hi_store cf g.1 now r 0 "replica" g.2 hH
    exact ⟨a, b⟩
  | rst t r =>
    have a := inv_store cf g.1 t r 0 "replica" hI
    have b := hi_store cf g.1 t r 0 "replica" g.2 hH
    exact ⟨a, b⟩
  | own now r =>
    obtain ⟨c1, c2⟩ := setOwn_core cf g.1 now r
    have a := inv_store cf g.1 now r cf.me "own" hI
    have b := hi_store cf g.1 now r cf.me "own" g.2 hH
    simp only [gstep, storeStep, c1]
    unfold Inv HI at *
    rw [c2]; exact ⟨a, b⟩
  | tm now =>
    have a := inv_timeout cf g.1 now hI
    refine ⟨a, ?_, ?_⟩
    · intro x hx
      obtain ⟨x0, hx0, hr⟩ := timeout_ents cf g.1 now x hx
      have hs : (find (timeout cf g.1 now).st.ents x.r.node).isSome = true := by
        rw [find_of_mem a.1 hx]; rfl
      show (if (find (timeout cf g.1 now).st.ents x.r.node).isSome then g.2 x.r.node else 0) = x.r.seq
      simp only [hs, ite_true]
      rw [← hr]
      have := hH.1 x0 hx0
      rw [hr] at this
      rw [hr] at *
      simpa using this
    · intro n hn
      have hn' : find (timeout cf g.1 now).st.ents n = none := hn
      show (if (find (timeout cf g.1 now).st.ents n).isSome then g.2 n else 0) = 0
      rw [hn']; rfl

theorem gfold_inv (cf : Cf) (cs : List Call) :
    ∀ g : St × (Nat → Nat), (Inv cf g.1 ∧ HI g.1 g.2) → (Inv cf (cs.foldl (gstep cf) g).1 ∧ HI (cs.foldl (gstep cf) g).1 (cs.foldl (gstep cf) g).2) := by
  induction cs with
  | nil => intro g h; exact h
  | cons c t ih => intro g h; exact ih _ (gstep_inv cf g c h)

/-- After any sequence of calls from the empty store: the store holds at most `R` records, at most one per node id, all
verified, and the stored record of a node has the highest sequence number accepted for it since it had none stored
(`hi` is that number, kept by the ghost update of `gstep`; a node with no record stored has none). -/
theorem highest_reach (cf : Cf) (cs : List Call) :
    let g := cs.foldl (gstep cf) (St.new cf, fun _ => 0)
    Inv cf g.1 ∧ (∀ e ∈ g.1.ents, g.2 e.r.node = e.r.seq) ∧ (∀ n, find g.1.ents n = none → g.2 n = 0) := by
  have := gfold_inv cf cs (St.new cf, fun _ => 0) ⟨inv_empty cf, by simp [HI, St.new, find]⟩
  exact ⟨this.1, this.2.1, this.2.2⟩

end Pinc.ConnectRecords
