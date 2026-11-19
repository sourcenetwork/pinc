import Pinc.DtnCustodyThm

/-!
# Custody: runs of the book and the ledger

The system is a book and its ledger. One event is a book operation (`accept`, `offer`, `ack`, `delivered`, `bexpire`)
or a host operation on the ledger (`hostAdmit` of any key the book holds no record of, `hostExpire`, `hostRelease` of
a key the book holds no record of: the mailbox layer and transit bundles). `Reach s` is the set of systems reached
from an empty one by any sequence of allowed events, with any times (the clock `now` of every call is an arbitrary
input, it may even go back).

* `reach_inv`: every reachable system has `Inv` (charge = sum of sizes, within budget), no bundle held twice, every
  held bundle's ledger item is custody (`Linked`) and every outstanding offer id is below the book's counter.
* `offer_ids_distinct`, `outstanding_ids_handed`: over any sequence of operations (`ReachLog` keeps the log of the ids
  handed out) the ids handed out by one book are exactly `0, 1, 2, ...` (so pairwise distinct, strictly increasing).
* `stale_ack_noop`, `handback_then_ack_noop`: a stale ack (right node, wrong id, or after a cancel) never relieves and
  changes nothing; a hand-back cancels the offer, so every later ack of the bundle is stale.
* `custody_exit`: a custody item that is not yet expired at the time of the event leaves the ledger, or stops being
  custody, only through the event that delivers it, releases it, or acknowledges it. In particular an admission of any
  space, an expiry of other items, a refused call and an offer never drop it.
* `custody_to_transit_only_by_relief`: an unexpired item stops being custody only through a valid acknowledgement from
  exactly the node custody was offered to, naming exactly the offer outstanding (`relief_iff` says when that happens).
-/

namespace Pinc.DtnStore

/-- The system: the book's records, the ledger and the book's offer counter `next_offer`. -/
structure Sys where
  B : Recs
  L : Ledger
  nx : Nat

inductive Ev where
  | accept (bundle bytes expires previous now : Nat)
  | offer (b to : Nat)
  | ack (b custodian offer : Nat) (valid : Bool)
  | delivered (b : Nat)
  | bexpire (now : Nat)
  | hostAdmit (k : Key) (bytes : Nat) (c : Class) (expires now : Nat)
  | hostExpire (now : Nat)
  | hostRelease (k : Key)

/-- The time an event passes to the ledger, if it does. -/
def Ev.now : Ev → Option Nat
  | .accept _ _ _ _ n => some n
  | .bexpire n => some n
  | .hostAdmit _ _ _ _ n => some n
  | .hostExpire n => some n
  | _ => none

/-- The ledger key whose item the event may remove or relieve on purpose. -/
def Ev.touches : Ev → Key → Prop
  | .delivered b, k => k = bkey b
  | .ack b _ _ _, k => k = bkey b
  | .hostRelease k', k => k = k'
  | _, _ => False

/-- The host never admits or releases a key the book holds. -/
def Allowed (s : Sys) : Ev → Prop
  | .hostAdmit k _ _ _ _ => ¬ ∃ r ∈ recs s.B, k = bkey r.bundle
  | .hostRelease k => ¬ ∃ r ∈ recs s.B, k = bkey r.bundle
  | _ => True

def step (s : Sys) : Ev → Sys
  | .accept b by_ ex pr now => ⟨(accept s.B s.L b by_ ex pr now).B, (accept s.B s.L b by_ ex pr now).L, s.nx⟩
  | .offer b to => ⟨(offer s.B s.nx b to).B, s.L, (offer s.B s.nx b to).nx⟩
  | .ack b c o v => ⟨(onAck s.B s.L b c o v).B, (onAck s.B s.L b c o v).L, s.nx⟩
  | .delivered b => ⟨(delivered s.B s.L b).B, (delivered s.B s.L b).L, s.nx⟩
  | .bexpire now => ⟨(bexpire s.B s.L now).B, (bexpire s.B s.L now).L, s.nx⟩
  | .hostAdmit k by_ c ex now => ⟨s.B, (admitItem s.L k by_ c ex now).L, s.nx⟩
  | .hostExpire now => ⟨s.B, (expire s.L now).1, s.nx⟩
  | .hostRelease k => ⟨s.B, (release s.L k).1, s.nx⟩

/-- The invariant: the ledger is well formed, no bundle is held twice, every held bundle's item is custody, and every
outstanding offer id was handed out (is below the counter). -/
structure SInv (s : Sys) : Prop where
  inv : Inv s.L
  nodup : NodupB s.B
  linked : Linked s.B s.L
  ids : ∀ r ∈ recs s.B, r.offered ≠ none → r.oid < s.nx

inductive Reach : Sys → Prop where
  | init (budget n m : Nat) (h : budget ≤ MAX) : Reach ⟨List.replicate m none, Ledger.empty budget n, 0⟩
  | step {s : Sys} (ev : Ev) : Reach s → Allowed s ev → Reach (step s ev)

theorem SInv.init (budget n m : Nat) (h : budget ≤ MAX) : SInv ⟨List.replicate m none, Ledger.empty budget n, 0⟩ :=
  ⟨Inv.empty budget n h, by simp [NodupB, recs], by intro r hr; simp [recs] at hr, by intro r hr; simp [recs] at hr⟩

theorem release_sub (L : Ledger) (k : Key) : ∀ e ∈ (release L k).1.entries, e ∈ L.entries := by
  intro e he
  rcases release_exits L k with ⟨_, h2, _⟩ | ⟨x, _, _, hp⟩
  · rw [h2] at he; exact he
  · exact hp.symm.mem_iff.1 (List.mem_cons_of_mem _ he)

/-- After an accept every record is an old one or has no outstanding offer. -/
theorem accept_recs_shape (B : Recs) (L : Ledger) (bundle bytes expires previous now : Nat) :
    ∀ r ∈ recs (accept B L bundle bytes expires previous now).B, r ∈ recs B ∨ r.offered = none := by
  intro r hr
  have hs1 := sync_sub B (expire L now).1
  unfold accept at hr
  simp only at hr
  by_cases hh : holds (sync B (expire L now).1) bundle = true
  · obtain ⟨B', hB'⟩ := cancel_some hh
    simp only [hh, ite_true, hB', Option.getD_some] at hr
    obtain ⟨-, hsub, -⟩ := modFirst_spec bundle cancelRec cancelRec_bundle _ B' hB'
    rcases hsub r hr with h | ⟨r0, _, _, rfl⟩
    · exact Or.inl (hs1 r h)
    · right; rfl
  have hh' : holds (sync B (expire L now).1) bundle = false := by simpa using hh
  simp only [hh', Bool.false_eq_true, ite_false] at hr
  cases hs : (sync B (expire L now).1).findIdx? Option.isNone with
  | none => simp only [hs] at hr; exact Or.inl (hs1 r hr)
  | some slot =>
    simp only [hs] at hr
    by_cases hc : (expire L now).1.contains (bkey bundle) = true
    · simp only [hc, ite_true] at hr
      rcases mem_recs_set hr with rfl | h
      · right; rfl
      · exact Or.inl (hs1 r (sync_sub _ _ r h))
    · simp only [hc, Bool.false_eq_true, ite_false] at hr
      cases hr0 : (admitItem (expire L now).1 (bkey bundle) bytes .custody expires now).err with
      | some e => simp only [hr0] at hr; exact Or.inl (hs1 r hr)
      | none =>
        simp only [hr0] at hr
        rcases mem_recs_set hr with rfl | h
        · right; rfl
        · exact Or.inl (hs1 r (sync_sub _ _ r h))

theorem sinv_step {s : Sys} (hs : SInv s) (ev : Ev) (ha : Allowed s ev) : SInv (step s ev) := by
  cases ev with
  | accept b by_ ex pr now =>
    obtain ⟨h1, h2, h3⟩ := accept_inv hs.inv hs.nodup hs.linked b by_ ex pr now
    exact ⟨h1, h2, h3, fun r hr ho => by
      rcases accept_recs_shape s.B s.L b by_ ex pr now r hr with h | h
      · exact hs.ids r h ho
      · exact absurd h ho⟩
  | offer b to =>
    obtain ⟨h1, h2⟩ := offer_inv hs.nodup hs.linked s.nx b to
    refine ⟨hs.inv, h1, h2, fun r hr ho => ?_⟩
    by_cases herr : (offer s.B s.nx b to).err = none
    · obtain ⟨hset, -, hold⟩ := offer_sets hs.nodup s.nx b to herr
      have hn := (offer_counter s.B s.nx b to).1 herr
      show r.oid < (offer s.B s.nx b to).nx
      rw [hn.2]
      by_cases hb : r.bundle = b
      · have := (hset r hr hb).2; omega
      · have := hs.ids r (hold r hr hb) ho; omega
    · obtain ⟨hn, hB⟩ := (offer_counter s.B s.nx b to).2 herr
      show r.oid < (offer s.B s.nx b to).nx
      rw [hn]
      have hr' : r ∈ recs s.B := by
        have : (offer s.B s.nx b to).B = s.B := hB
        simpa [step, this] using hr
      exact hs.ids r hr' ho
  | ack b c o v =>
    obtain ⟨h1, h2, h3⟩ := onAck_inv hs.inv hs.nodup hs.linked b c o v
    exact ⟨h1, h2, h3, fun r hr ho => hs.ids r ((onAck_records (L := s.L) hs.nodup b c o v).1 r hr) ho⟩
  | delivered b =>
    obtain ⟨h1, h2, h3⟩ := delivered_inv hs.inv hs.nodup hs.linked b
    exact ⟨h1, h2, h3, fun r hr ho => by
      rcases delivered_cases hs.nodup s.L b with ⟨_, hB, -, -⟩ | ⟨-, -, hrr, -, -⟩
      · exact hs.ids r (by simpa [step, hB] using hr) ho
      · exact hs.ids r (hrr r hr).1 ho⟩
  | bexpire now =>
    obtain ⟨h1, h2, h3⟩ := bexpire_inv hs.inv hs.nodup hs.linked now
    exact ⟨h1, h2, h3, fun r hr ho => hs.ids r (sync_sub _ _ r hr) ho⟩
  | hostAdmit k by_ c ex now =>
    refine ⟨admit_inv hs.inv k by_ c ex now, hs.nodup, ?_, hs.ids⟩
    intro r hr e he hk
    rcases admit_entries_sub hs.inv k by_ c ex now e he with h | rfl
    · exact hs.linked r hr e h hk
    · exact absurd ⟨r, hr, hk⟩ ha
  | hostExpire now =>
    exact ⟨expire_inv hs.inv now, hs.nodup, linked_mono hs.linked (fun _ h => h) (expire_sub s.L now), hs.ids⟩
  | hostRelease k =>
    exact ⟨release_inv hs.inv k, hs.nodup, linked_mono hs.linked (fun _ h => h) (release_sub s.L k), hs.ids⟩

theorem reach_inv {s : Sys} (h : Reach s) : SInv s := by
  induction h with
  | init budget n m hb => exact SInv.init budget n m hb
  | step ev _ ha ih => exact sinv_step ih ev ha

/-! ## Offer ids -/

/-- The offer ids an event hands out: a successful offer hands out the counter. -/
def Ev.handed (s : Sys) : Ev → List Nat
  | .offer b to => if (Pinc.DtnStore.offer s.B s.nx b to).err = none then [s.nx] else []
  | _ => []

/-- `Reach` with the log of every offer id handed out so far, in order. -/
inductive ReachLog : Sys → List Nat → Prop where
  | init (budget n m : Nat) (h : budget ≤ MAX) : ReachLog ⟨List.replicate m none, Ledger.empty budget n, 0⟩ []
  | step {s : Sys} {ids : List Nat} (ev : Ev) : ReachLog s ids → Allowed s ev → ReachLog (step s ev) (ids ++ ev.handed s)

theorem step_nx (s : Sys) (ev : Ev) : (step s ev).nx = s.nx + (ev.handed s).length := by
  cases ev with
  | offer b to =>
    by_cases h : (offer s.B s.nx b to).err = none
    · simp [step, Ev.handed, h, (offer_counter s.B s.nx b to).1 h]
    · simp [step, Ev.handed, h, ((offer_counter s.B s.nx b to).2 h).1]
  | _ => simp [step, Ev.handed]

/-- Offer ids handed out by one book over any sequence of operations are pairwise distinct: the counter is strictly
increasing, so the log is exactly `0, 1, 2, ...` and every id is below the counter. -/
theorem offer_ids_distinct {s : Sys} {ids : List Nat} (h : ReachLog s ids) :
    ids = List.range s.nx ∧ ids.Nodup := by
  have key : ids = List.range s.nx := by
    induction h with
    | init => rfl
    | @step s0 ids0 ev _ _ ih =>
      rw [step_nx, ih]
      cases ev with
      | offer b to =>
        by_cases h : (offer s0.B s0.nx b to).err = none
        · simp [Ev.handed, h, List.range_succ]
        · simp [Ev.handed, h]
      | _ => simp [Ev.handed]
  exact ⟨key, by rw [key]; exact List.nodup_range⟩

/-- Every outstanding offer id is one that was handed out. -/
theorem outstanding_ids_handed {s : Sys} {ids : List Nat} (h : ReachLog s ids) :
    ∀ r ∈ recs s.B, r.offered ≠ none → r.oid ∈ ids := by
  have hr : Reach s := by
    induction h with
    | init budget n m hb => exact Reach.init budget n m hb
    | step ev _ ha ih => exact Reach.step ev ih ha
  intro r hrm ho
  rw [(offer_ids_distinct h).1, List.mem_range]
  exact (reach_inv hr).ids r hrm ho

/-! ## Where an item can go -/

theorem accept_entries_shape {B : Recs} {L : Ledger} (hI : Inv L) (bundle bytes expires previous now : Nat) :
    ∀ e' ∈ (accept B L bundle bytes expires previous now).L.entries,
      e' ∈ L.entries ∨ (e'.key = bkey bundle ∧ e'.cls = .custody) := by
  intro e' he'
  have hsub := expire_sub L now
  have hI1 := expire_inv hI now
  unfold accept at he'
  simp only at he'
  by_cases hh : holds (sync B (expire L now).1) bundle = true
  · simp only [hh, ite_true] at he'; exact Or.inl (hsub e' he')
  have hh' : holds (sync B (expire L now).1) bundle = false := by simpa using hh
  simp only [hh', Bool.false_eq_true, ite_false] at he'
  cases hs : (sync B (expire L now).1).findIdx? Option.isNone with
  | none => simp only [hs] at he'; exact Or.inl (hsub e' he')
  | some slot =>
    simp only [hs] at he'
    by_cases hc : (expire L now).1.contains (bkey bundle) = true
    · simp only [hc, ite_true] at he'
      rw [reclass_entries _ _ _ hc] at he'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he'
      by_cases hyk : y.key = bkey bundle
      · right; simp [hyk]
      · left; simp only [hyk, ite_false]; exact hsub y hy
    · have hc' : (expire L now).1.contains (bkey bundle) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ite_false] at he'
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, L2, ev2, slots', _, _, h2, _⟩
      · rw [h2] at he'; simp only at he'
        rw [(expire_idem L now).1] at he'
        exact Or.inl (hsub e' he')
      · rw [h2] at he'; simp only at he'
        rw [(expire_idem L now).1] at he'
        exact Or.inl (hsub e' he')
      · rw [h2] at he'; simp only at he'
        have := admit_entries_sub hI1 (bkey bundle) bytes .custody expires now e'
        rw [h2] at this
        rcases this he' with h | h
        · exact Or.inl (hsub e' h)
        · right; subst h; exact ⟨rfl, rfl⟩

theorem accept_keeps_custody {B : Recs} {L : Ledger} (hI : Inv L) (bundle bytes expires previous now : Nat)
    (e : Entry) (he : e ∈ L.entries) (hc : e.cls = .custody) (hlive : expiredAt now e = false) :
    e ∈ (accept B L bundle bytes expires previous now).L.entries := by
  have h1 : e ∈ (expire L now).1.entries := by
    rw [entries_expire]; exact List.mem_filter.2 ⟨he, by simp [hlive]⟩
  have hI1 := expire_inv hI now
  unfold accept
  simp only
  by_cases hh : holds (sync B (expire L now).1) bundle = true
  · simp only [hh, ite_true]; exact h1
  have hh' : holds (sync B (expire L now).1) bundle = false := by simpa using hh
  simp only [hh', Bool.false_eq_true, ite_false]
  cases hs : (sync B (expire L now).1).findIdx? Option.isNone with
  | none => simp only; exact h1
  | some slot =>
    simp only
    by_cases hct : (expire L now).1.contains (bkey bundle) = true
    · simp only [hct, ite_true]
      rw [reclass_entries _ _ _ hct]
      refine List.mem_map.2 ⟨e, h1, ?_⟩
      by_cases hk : e.key = bkey bundle
      · simp only [hk, ite_true]; cases e; simp_all
      · simp [hk]
    · have hc' : (expire L now).1.contains (bkey bundle) = false := by simpa using hct
      simp only [hc', Bool.false_eq_true, ite_false]
      have hk := admit_keeps_live_custody hI1 (bkey bundle) bytes .custody expires now e h1 hc (by simpa using hlive)
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, L2, ev2, slots', _, _, h2, _⟩
      · rw [h2] at hk ⊢; simpa using hk
      · rw [h2] at hk ⊢; simpa using hk
      · rw [h2] at hk ⊢; simpa using hk

theorem onAck_L_cases {B : Recs} {L : Ledger} (hn : NodupB B) (b c o : Nat) (v : Bool) :
    (onAck B L b c o v).L = L ∨ ((onAck B L b c o v).err = none ∧
      (onAck B L b c o v).L.entries = L.entries.map (fun x => if x.key = bkey b then { x with cls := .transit } else x)) := by
  obtain ⟨-, hsame, hunk, hok⟩ := onAck_state (L := L) hn b c o v
  by_cases herr : (onAck B L b c o v).err = none
  · exact Or.inr ⟨herr, hok herr⟩
  · left
    cases h : (onAck B L b c o v).err with
    | none => exact absurd h herr
    | some e =>
      cases e with
      | storeUnknown => exact (hunk h).1
      | ack | unknown | notOffered => exact (hsame (by simp [h])).2
      | store _ | capacity =>
        exfalso
        unfold onAck at h
        cases v <;> simp at h
        cases hs : slotOf B b <;> simp [hs] at h
        split at h <;> (try split at h) <;> simp_all

theorem onAck_entries_shape {B : Recs} {L : Ledger} (hn : NodupB B) (b c o : Nat) (v : Bool) :
    ∀ e' ∈ (onAck B L b c o v).L.entries, e' ∈ L.entries ∨ ∃ x ∈ L.entries, x.key = bkey b ∧ e' = { x with cls := .transit } := by
  intro e' he'
  rcases onAck_L_cases (L := L) hn b c o v with h | ⟨_, h⟩
  · rw [h] at he'; exact Or.inl he'
  · rw [h] at he'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he'
    by_cases hk : x.key = bkey b
    · right; exact ⟨x, hx, hk, by simp [hk]⟩
    · left; simpa [hk] using hx

theorem custody_exit {s : Sys} (hs : SInv s) (ev : Ev) (ha : Allowed s ev) (e : Entry) (he : e ∈ s.L.entries)
    (hc : e.cls = .custody) (hlive : ∀ t, ev.now = some t → expiredAt t e = false) (hn : ¬ ev.touches e.key) :
    e ∈ (step s ev).L.entries := by
  cases ev with
  | accept b by_ ex pr now => exact accept_keeps_custody hs.inv b by_ ex pr now e he hc (hlive now rfl)
  | offer b to => exact he
  | ack b c o v =>
    simp only [step]
    rcases onAck_L_cases (L := s.L) hs.nodup b c o v with h | ⟨_, h⟩
    · rw [h]; exact he
    · rw [h]
      exact List.mem_map.2 ⟨e, he, by simp [show e.key ≠ bkey b from hn]⟩
  | delivered b =>
    rcases delivered_cases hs.nodup s.L b with ⟨_, _, hL, _⟩ | ⟨h, _⟩
    · simp only [step]; rw [hL]; exact he
    · exact (delivered_exits hs.inv hs.nodup b h).2.1 e he (fun hk => hn hk)
  | bexpire now =>
    simp only [step, bexpire]
    rw [entries_expire]; exact List.mem_filter.2 ⟨he, by simp [hlive now rfl]⟩
  | hostAdmit k by_ c ex now => exact admit_keeps_live_custody hs.inv k by_ c ex now e he hc (hlive now rfl)
  | hostExpire now =>
    simp only [step]; rw [entries_expire]; exact List.mem_filter.2 ⟨he, by simp [hlive now rfl]⟩
  | hostRelease k =>
    simp only [step]
    rcases release_exits s.L k with ⟨_, h2, _⟩ | ⟨x, _, hxk, hp⟩
    · rw [h2]; exact he
    · have := hp.mem_iff.1 he
      simp only [List.mem_cons] at this
      rcases this with rfl | h
      · exact absurd hxk hn
      · exact h


theorem key_unique {L : Ledger} (hI : Inv L) {x y : Entry} (hx : x ∈ L.entries) (hy : y ∈ L.entries)
    (h : x.key = y.key) : x = y :=
  nodup_map_inj (fun e : Entry => e.key) L.entries hI.keys x hx y hy h

/-- Custody is relieved exactly by a valid acknowledgement from the node it was offered to, for the offer id
currently outstanding to it. -/
theorem relief_iff {s : Sys} (hs : SInv s) (b c o : Nat) (v : Bool) :
    (onAck s.B s.L b c o v).err = none ↔
      v = true ∧ (∃ r ∈ recs s.B, r.bundle = b ∧ r.offered = some c ∧ r.oid = o) ∧ s.L.contains (bkey b) = true :=
  onAck_ok_iff hs.nodup b c o v

/-- An item that has not expired stops being custody only through a valid acknowledgement of its bundle from exactly
the node custody was offered to, naming exactly the offer outstanding. (A custody item that has expired may be swept and
its key admitted again as a new item, which is not a change of class.) -/
theorem custody_to_transit_only_by_relief {s : Sys} (hs : SInv s) (ev : Ev) (ha : Allowed s ev) (e e' : Entry)
    (he : e ∈ s.L.entries) (hc : e.cls = .custody) (hlive : ∀ t, ev.now = some t → expiredAt t e = false)
    (he' : e' ∈ (step s ev).L.entries) (hk : e'.key = e.key) (ht : e'.cls = .transit) :
    ∃ b c o, ev = .ack b c o true ∧ e.key = bkey b ∧
      ∃ r ∈ recs s.B, r.bundle = b ∧ r.offered = some c ∧ r.oid = o := by
  have stay : e' ∈ s.L.entries → False := fun h => by
    have := key_unique hs.inv h he hk; rw [this] at ht; rw [hc] at ht; cases ht
  cases ev with
  | accept b by_ ex pr now =>
    exfalso
    rcases accept_entries_shape (B := s.B) hs.inv b by_ ex pr now e' he' with h | ⟨_, h⟩
    · exact stay h
    · rw [h] at ht; cases ht
  | offer b to => exact (stay he').elim
  | ack b c o v =>
    simp only [step] at he'
    rcases onAck_L_cases (L := s.L) hs.nodup b c o v with h | ⟨herr, h⟩
    · rw [h] at he'; exact (stay he').elim
    · rw [h] at he'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he'
      by_cases hxk : x.key = bkey b
      · have hv := (onAck_ok_iff hs.nodup b c o v).1 herr
        refine ⟨b, c, o, ?_, by rw [← hk, ← hxk]; simp [hxk], hv.2.1⟩
        have := hv.1
        subst this; rfl
      · simp only [hxk, ite_false] at hk ht
        exact (stay (by simpa [hxk] using hx)).elim
  | delivered b =>
    exfalso; exact stay ((fun h => by
      rcases delivered_cases hs.nodup s.L b with ⟨_, _, hL, _⟩ | ⟨herr, _⟩
      · simp only [step] at h; rw [hL] at h; exact h
      · exact (delivered_exits hs.inv hs.nodup b herr).1 e' h) he')
  | bexpire now =>
    exfalso; exact stay (expire_sub s.L now e' he')
  | hostAdmit k by_ c ex now =>
    exfalso
    simp only [step] at he'
    rcases admit_entries_sub hs.inv k by_ c ex now e' he' with h | h
    · exact stay h
    · -- the new item: its key is kept after the sweep (the item is live), so the admission was refused as a duplicate
      subst h
      have hkk : k = e.key := hk
      have he1 : e ∈ (expire s.L now).1.entries := by
        rw [entries_expire]; exact List.mem_filter.2 ⟨he, by simp [hlive now rfl]⟩
      have hcont : (expire s.L now).1.contains k = true := contains_iff.2 ⟨e, he1, hkk.symm⟩
      rw [admit_dup_sweeps k by_ c ex now hcont] at he'
      exact stay (expire_sub s.L now _ he')
  | hostExpire now =>
    exfalso; exact stay (expire_sub s.L now e' he')
  | hostRelease k =>
    exfalso; exact stay (release_sub s.L k e' he')

/-- A stale acknowledgement (right node but another offer id, another node, or a cancelled offer) changes nothing in the
system and never relieves. -/
theorem stale_ack_noop {s : Sys} (hs : SInv s) (b c o : Nat) (hheld : holds s.B b = true)
    (hst : ∀ r ∈ recs s.B, r.bundle = b → ¬ (r.offered = some c ∧ r.oid = o)) :
    step s (.ack b c o true) = s := by
  simp only [step, onAck_stale hs.nodup b c o hheld hst]

/-- A hand-back cancels the offer: after a node accepts a bundle it already holds, no acknowledgement of that bundle
(whichever node and offer id it names) relieves it or changes anything. -/
theorem handback_then_ack_noop {s : Sys} (hs : SInv s) (b bytes ex pr now c o : Nat)
    (hh : holds (sync s.B (expire s.L now).1) b = true) :
    step (step s (.accept b bytes ex pr now)) (.ack b c o true) = step s (.accept b bytes ex pr now) := by
  simp only [step]
  rw [handback_blocks_ack hs.inv hs.nodup hs.linked b bytes ex pr now hh c o]

#audit_axioms Pinc.DtnStore.reach_inv
#audit_axioms Pinc.DtnStore.custody_exit
#audit_axioms Pinc.DtnStore.custody_to_transit_only_by_relief
#audit_axioms Pinc.DtnStore.relief_iff
#audit_axioms Pinc.DtnStore.offer_ids_distinct
#audit_axioms Pinc.DtnStore.outstanding_ids_handed
#audit_axioms Pinc.DtnStore.stale_ack_noop
#audit_axioms Pinc.DtnStore.handback_then_ack_noop
#audit_axioms Pinc.DtnStore.onAck_stale
#audit_axioms Pinc.DtnStore.handback_blocks_ack
#audit_axioms Pinc.DtnStore.accept_held_cancels
#audit_axioms Pinc.DtnStore.accept_expired_refused
#audit_axioms Pinc.DtnStore.offer_sets
#audit_axioms Pinc.DtnStore.offer_counter
#audit_axioms Pinc.DtnStore.accept_inv
#audit_axioms Pinc.DtnStore.accept_err_state
#audit_axioms Pinc.DtnStore.accept_ok
#audit_axioms Pinc.DtnStore.accept_capacity_iff
#audit_axioms Pinc.DtnStore.onAck_ok_iff
#audit_axioms Pinc.DtnStore.onAck_inv
#audit_axioms Pinc.DtnStore.delivered_inv
#audit_axioms Pinc.DtnStore.delivered_exits
#audit_axioms Pinc.DtnStore.bexpire_inv
#audit_axioms Pinc.DtnStore.bexpire_exits
#audit_axioms Pinc.DtnStore.offer_inv
#audit_axioms Pinc.DtnStore.offer_ok_iff

end Pinc.DtnStore
