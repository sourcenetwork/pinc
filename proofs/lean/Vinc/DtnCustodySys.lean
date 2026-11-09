import Vinc.DtnCustodyThm

/-!
# Custody: runs of the book and the ledger

The system is a book and its ledger. One event is a book operation (`accept`, `offer`, `ack`, `delivered`, `bexpire`)
or a host operation on the ledger (`hostAdmit` of any key the book holds no record of, `hostExpire`, `hostRelease` of
a key the book holds no record of: the mailbox layer and transit bundles). `Reach s` is the set of systems reached
from an empty one by any sequence of allowed events, with any times (the clock `now` of every call is an arbitrary
input, it may even go back).

* `reach_inv`: every reachable system has `Inv` (charge = sum of sizes, within budget), no bundle held twice and every
  held bundle's ledger item is custody (`Linked`).
* `custody_exit`: a custody item that is not yet expired at the time of the event leaves the ledger, or stops being
  custody, only through the event that delivers it, releases it, or acknowledges it. In particular an admission of any
  space, an expiry of other items, a refused call and an offer never drop it.
* `custody_to_transit_only_by_relief`: an item stops being custody only through a valid acknowledgement from exactly the
  node custody was offered to (`relief_iff` says when that happens).
-/

namespace Vinc.DtnStore

structure Sys where
  B : Recs
  L : Ledger

inductive Ev where
  | accept (bundle bytes expires previous now : Nat)
  | offer (b to : Nat)
  | ack (b custodian : Nat) (valid : Bool)
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
  | .ack b _ _, k => k = bkey b
  | .hostRelease k', k => k = k'
  | _, _ => False

/-- The host never admits or releases a key the book holds. -/
def Allowed (s : Sys) : Ev → Prop
  | .hostAdmit k _ _ _ _ => ¬ ∃ r ∈ recs s.B, k = bkey r.bundle
  | .hostRelease k => ¬ ∃ r ∈ recs s.B, k = bkey r.bundle
  | _ => True

def step (s : Sys) : Ev → Sys
  | .accept b by_ ex pr now => ⟨(accept s.B s.L b by_ ex pr now).B, (accept s.B s.L b by_ ex pr now).L⟩
  | .offer b to => ⟨(offer s.B b to).2, s.L⟩
  | .ack b c v => ⟨(onAck s.B s.L b c v).B, (onAck s.B s.L b c v).L⟩
  | .delivered b => ⟨(delivered s.B s.L b).B, (delivered s.B s.L b).L⟩
  | .bexpire now => ⟨(bexpire s.B s.L now).B, (bexpire s.B s.L now).L⟩
  | .hostAdmit k by_ c ex now => ⟨s.B, (admitItem s.L k by_ c ex now).L⟩
  | .hostExpire now => ⟨s.B, (expire s.L now).1⟩
  | .hostRelease k => ⟨s.B, (release s.L k).1⟩

structure SInv (s : Sys) : Prop where
  inv : Inv s.L
  nodup : NodupB s.B
  linked : Linked s.B s.L

inductive Reach : Sys → Prop where
  | init (budget n m : Nat) (h : budget ≤ MAX) : Reach ⟨List.replicate m none, Ledger.empty budget n⟩
  | step {s : Sys} (ev : Ev) : Reach s → Allowed s ev → Reach (step s ev)

theorem SInv.init (budget n m : Nat) (h : budget ≤ MAX) : SInv ⟨List.replicate m none, Ledger.empty budget n⟩ :=
  ⟨Inv.empty budget n h, by simp [NodupB, recs], by intro r hr; simp [recs] at hr⟩

theorem release_sub (L : Ledger) (k : Key) : ∀ e ∈ (release L k).1.entries, e ∈ L.entries := by
  intro e he
  rcases release_exits L k with ⟨_, h2, _⟩ | ⟨x, _, _, hp⟩
  · rw [h2] at he; exact he
  · exact hp.symm.mem_iff.1 (List.mem_cons_of_mem _ he)

theorem sinv_step {s : Sys} (hs : SInv s) (ev : Ev) (ha : Allowed s ev) : SInv (step s ev) := by
  cases ev with
  | accept b by_ ex pr now =>
    obtain ⟨h1, h2, h3⟩ := accept_inv hs.inv hs.nodup hs.linked b by_ ex pr now
    exact ⟨h1, h2, h3⟩
  | offer b to =>
    obtain ⟨h1, h2⟩ := offer_inv hs.nodup hs.linked b to
    exact ⟨hs.inv, h1, h2⟩
  | ack b c v =>
    obtain ⟨h1, h2, h3⟩ := onAck_inv hs.inv hs.nodup hs.linked b c v
    exact ⟨h1, h2, h3⟩
  | delivered b =>
    obtain ⟨h1, h2, h3⟩ := delivered_inv hs.inv hs.nodup hs.linked b
    exact ⟨h1, h2, h3⟩
  | bexpire now =>
    obtain ⟨h1, h2, h3⟩ := bexpire_inv hs.inv hs.nodup hs.linked now
    exact ⟨h1, h2, h3⟩
  | hostAdmit k by_ c ex now =>
    refine ⟨admit_inv hs.inv k by_ c ex now, hs.nodup, ?_⟩
    intro r hr e he hk
    rcases admit_entries_sub hs.inv k by_ c ex now e he with h | rfl
    · exact hs.linked r hr e h hk
    · exact absurd ⟨r, hr, hk⟩ ha
  | hostExpire now =>
    exact ⟨expire_inv hs.inv now, hs.nodup, linked_mono hs.linked (fun _ h => h) (expire_sub s.L now)⟩
  | hostRelease k =>
    exact ⟨release_inv hs.inv k, hs.nodup, linked_mono hs.linked (fun _ h => h) (release_sub s.L k)⟩

theorem reach_inv {s : Sys} (h : Reach s) : SInv s := by
  induction h with
  | init budget n m hb => exact SInv.init budget n m hb
  | step ev _ ha ih => exact sinv_step ih ev ha

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
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨h1, _⟩ | ⟨_, _, h2⟩ | ⟨_, _, L2, ev2, slots', _, _, h2, _⟩
      · simp_all
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
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨h1, _⟩ | ⟨_, _, h2⟩ | ⟨_, _, L2, ev2, slots', _, _, h2, _⟩
      · simp_all
      · rw [h2] at hk ⊢; simpa using hk
      · rw [h2] at hk ⊢; simpa using hk

theorem onAck_L_cases {B : Recs} {L : Ledger} (hn : NodupB B) (b c : Nat) (v : Bool) :
    (onAck B L b c v).L = L ∨ ((onAck B L b c v).err = none ∧
      (onAck B L b c v).L.entries = L.entries.map (fun x => if x.key = bkey b then { x with cls := .transit } else x)) := by
  obtain ⟨-, hsame, hunk, hok⟩ := onAck_state (L := L) hn b c v
  by_cases herr : (onAck B L b c v).err = none
  · exact Or.inr ⟨herr, hok herr⟩
  · left
    cases h : (onAck B L b c v).err with
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
        split at h <;> simp_all

theorem onAck_entries_shape {B : Recs} {L : Ledger} (hn : NodupB B) (b c : Nat) (v : Bool) :
    ∀ e' ∈ (onAck B L b c v).L.entries, e' ∈ L.entries ∨ ∃ x ∈ L.entries, x.key = bkey b ∧ e' = { x with cls := .transit } := by
  intro e' he'
  rcases onAck_L_cases (L := L) hn b c v with h | ⟨_, h⟩
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
  | ack b c v =>
    simp only [step]
    rcases onAck_L_cases (L := s.L) hs.nodup b c v with h | ⟨_, h⟩
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

/-- Custody is relieved exactly by a valid acknowledgement from the node it was offered to. -/
theorem relief_iff {s : Sys} (hs : SInv s) (b c : Nat) (v : Bool) :
    (onAck s.B s.L b c v).err = none ↔
      v = true ∧ (∃ r ∈ recs s.B, r.bundle = b ∧ r.offered = some c) ∧ s.L.contains (bkey b) = true :=
  onAck_ok_iff hs.nodup b c v

/-- An item stops being custody only through a valid acknowledgement of its bundle from exactly the node custody
was offered to. -/
theorem custody_to_transit_only_by_relief {s : Sys} (hs : SInv s) (ev : Ev) (ha : Allowed s ev) (e e' : Entry)
    (he : e ∈ s.L.entries) (hc : e.cls = .custody) (he' : e' ∈ (step s ev).L.entries) (hk : e'.key = e.key)
    (ht : e'.cls = .transit) :
    ∃ b c, ev = .ack b c true ∧ e.key = bkey b ∧ ∃ r ∈ recs s.B, r.bundle = b ∧ r.offered = some c := by
  have stay : e' ∈ s.L.entries → False := fun h => by
    have := key_unique hs.inv h he hk; rw [this] at ht; rw [hc] at ht; cases ht
  cases ev with
  | accept b by_ ex pr now =>
    exfalso
    rcases accept_entries_shape (B := s.B) hs.inv b by_ ex pr now e' he' with h | ⟨_, h⟩
    · exact stay h
    · rw [h] at ht; cases ht
  | offer b to => exact (stay he').elim
  | ack b c v =>
    simp only [step] at he'
    rcases onAck_L_cases (L := s.L) hs.nodup b c v with h | ⟨herr, h⟩
    · rw [h] at he'; exact (stay he').elim
    · rw [h] at he'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he'
      by_cases hxk : x.key = bkey b
      · have hv := (onAck_ok_iff hs.nodup b c v).1 herr
        refine ⟨b, c, ?_, by rw [← hk, ← hxk]; simp [hxk], hv.2.1⟩
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
    · -- the new item: its key would be a key the ledger already holds, so the admission was refused
      subst h
      have hkk : k = e.key := hk
      have hcont : s.L.contains k = true := contains_iff.2 ⟨e, he, hkk.symm⟩
      rcases admit_cases hs.inv k by_ c ex now with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h2] at he'; simp only at he'; exact stay he'
      · rw [hcont] at h1; cases h1
      · rw [hcont] at h1; cases h1
  | hostExpire now =>
    exfalso; exact stay (expire_sub s.L now e' he')
  | hostRelease k =>
    exfalso; exact stay (release_sub s.L k e' he')

#audit_axioms Vinc.DtnStore.reach_inv
#audit_axioms Vinc.DtnStore.custody_exit
#audit_axioms Vinc.DtnStore.custody_to_transit_only_by_relief
#audit_axioms Vinc.DtnStore.relief_iff
#audit_axioms Vinc.DtnStore.accept_inv
#audit_axioms Vinc.DtnStore.accept_err_state
#audit_axioms Vinc.DtnStore.accept_ok
#audit_axioms Vinc.DtnStore.accept_capacity_iff
#audit_axioms Vinc.DtnStore.onAck_ok_iff
#audit_axioms Vinc.DtnStore.onAck_inv
#audit_axioms Vinc.DtnStore.delivered_inv
#audit_axioms Vinc.DtnStore.delivered_exits
#audit_axioms Vinc.DtnStore.bexpire_inv
#audit_axioms Vinc.DtnStore.bexpire_exits
#audit_axioms Vinc.DtnStore.offer_inv
#audit_axioms Vinc.DtnStore.offer_ok_iff

end Vinc.DtnStore
