import Pinc.DtnScenario

/-!
# The custody part of every node, in every reachable system

The book and the ledger of every node of every reachable system are a reachable system of `Pinc.DtnStore` (the single
node model of `DtnCustodySys`): the host glue drives them only through `DtnStore.step` (`ledgerAfter`), and the
host never admits a key the book holds (the mailbox layer's keys are in space 2, the bundles' in space 1). So the
theorems of that file hold at every node of a scenario: the charge is the sum of the sizes and within the budget
(`node_inv`), a custody item stays until it expires or is delivered, released or acknowledged (`custody_stays`), and
the class changes only by an acknowledgement from exactly the node custody was offered to
(`relief_only_by_offered_ack`).
-/

namespace Pinc.DtnScenario

/-- The `DtnStore` events the glue applies are never a host event on a key of the book. -/
theorem ledgerEv_allowed (s : Sys) (ev : Ev) (m : Nat) (le : DtnStore.Ev) (h : ledgerEv s ev m = some le) :
    DtnStore.Allowed ⟨(s.nodes m).B, (s.nodes m).L, (s.nodes m).nx⟩ le := by
  cases ev with
  | tick => simp only [ledgerEv] at h; cases h; trivial
  | poll n =>
    simp only [ledgerEv] at h
    split at h
    · split at h
      · split at h
        · cases h; trivial
        · simp at h
      · cases h; trivial
      · simp at h
    · simp at h
  | bun mm =>
    cases mm with
    | bun a b c d e f =>
      simp only [ledgerEv] at h
      split at h
      · cases h; trivial
      · simp at h
    | ack a b c d => simp [ledgerEv] at h
  | ack mm =>
    cases mm with
    | ack a b c d =>
      simp only [ledgerEv] at h
      split at h
      · cases h; trivial
      · simp at h
    | bun a b c d e f => simp [ledgerEv] at h
  | press n k =>
    simp only [ledgerEv] at h
    split at h
    · cases h
      show ¬ ∃ r ∈ DtnStore.recs (s.nodes m).B, (⟨2, k⟩ : DtnStore.Key) = DtnStore.bkey r.bundle
      rintro ⟨r, _, hk⟩
      simp [DtnStore.bkey] at hk
    · simp at h
  | contact a b up => simp [ledgerEv] at h
  | lose mm => simp [ledgerEv] at h
  | bad => simp [ledgerEv] at h


/-- Replacing a node: the others stay. -/
theorem set_nodes_same (s : Sys) (n m : Nat) (x : Node) (h : m ≠ n) : (s.set n x).nodes m = s.nodes m := by
  simp [Sys.set, h]

theorem set_nodes_self (s : Sys) (n : Nat) (x : Node) : (s.set n x).nodes n = x := by
  simp [Sys.set]

theorem ledgerAfter_none (s : Sys) (ev : Ev) (m : Nat) (h : ledgerEv s ev m = none) :
    ledgerAfter s ev m = ⟨(s.nodes m).B, (s.nodes m).L, (s.nodes m).nx⟩ := by
  simp [ledgerAfter, h]

/-- The book and ledger of every node after an event are what `ledgerAfter` says. -/
theorem exec_BL (s : Sys) (ev : Ev) (m : Nat) (hm : m ∈ s.cfg.ids) :
    ((exec s ev).nodes m).B = (ledgerAfter s ev m).B ∧ ((exec s ev).nodes m).L = (ledgerAfter s ev m).L ∧
      ((exec s ev).nodes m).nx = (ledgerAfter s ev m).nx := by
  have key : ∀ (n : Nat) (x : Node) (s' : Sys), (s'.nodes = (s.set n x).nodes) →
      (m = n → x.B = (ledgerAfter s ev m).B ∧ x.L = (ledgerAfter s ev m).L ∧ x.nx = (ledgerAfter s ev m).nx) →
      (m ≠ n → ledgerEv s ev m = none) →
      (s'.nodes m).B = (ledgerAfter s ev m).B ∧ (s'.nodes m).L = (ledgerAfter s ev m).L ∧
        (s'.nodes m).nx = (ledgerAfter s ev m).nx := by
    intro n x s' hs' h1 h2
    rw [hs']
    by_cases hmn : m = n
    · subst hmn; rw [set_nodes_self]; exact h1 rfl
    · rw [set_nodes_same _ _ _ _ hmn, ledgerAfter_none _ _ _ (h2 hmn)]; exact ⟨rfl, rfl, rfl⟩
  cases ev with
  | contact a b up =>
    have hl : ledgerEv s (.contact a b up) m = none := by simp [ledgerEv]
    rw [ledgerAfter_none _ _ _ hl]
    simp only [exec, exec0, Sys.set]
    by_cases hb : m = b
    · subst hb; simp
    · by_cases ha : m = a
      · subst ha; simp [hb]
      · simp [hb, ha]
  | tick =>
    simp [exec, exec0, hm, ledgerAfter, ledgerEv, DtnStore.step]
  | poll n =>
    refine key n ⟨(DtnForward.poll (s.nodes n).f).1, (ledgerAfter s (.poll n) n).B, (ledgerAfter s (.poll n) n).L, (ledgerAfter s (.poll n) n).nx⟩
      (exec s (.poll n)) ?_ ?_ ?_
    · simp only [exec, exec0]; split <;> rfl
    · intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    · intro h; simp [ledgerEv, h]
  | bun mm =>
    cases mm with
    | ack a b c d =>
      have hl : ledgerEv s (.bun (.ack a b c d)) m = none := by simp [ledgerEv]
      rw [ledgerAfter_none _ _ _ hl]
      simp [exec, exec0]
    | bun a from_ r c fresh off =>
      by_cases hr : r = s.cfg.dest
      · have hl : ledgerEv s (.bun (.bun a from_ r c fresh off)) m = none := by simp [ledgerEv, hr]
        rw [ledgerAfter_none _ _ _ hl]
        simp [exec, exec0, hr]
      · have hl : ledgerEv s (.bun (.bun a from_ r c fresh off)) r =
            some (.accept bid 1 s.cfg.exp from_ s.t) := by simp [ledgerEv, hr]
        have hl' : ∀ m', m' ≠ r → ledgerEv s (.bun (.bun a from_ r c fresh off)) m' = none := by
          intro m' hm'; simp [ledgerEv, hm']
        simp only [exec, exec0, hr, ite_false]
        split
        · refine key r ⟨(s.nodes r).f, (ledgerAfter s (.bun (.bun a from_ r c fresh off)) r).B,
              (ledgerAfter s (.bun (.bun a from_ r c fresh off)) r).L, (ledgerAfter s (.bun (.bun a from_ r c fresh off)) r).nx⟩ _ rfl ?_ (fun h => hl' m h)
          intro h; subst h; exact ⟨rfl, rfl, rfl⟩
        · refine key r ⟨(DtnForward.step (s.nodes r).f s.t (.hold bid s.cfg.dest s.cfg.exp c)).1,
              (ledgerAfter s (.bun (.bun a from_ r c fresh off)) r).B,
              (ledgerAfter s (.bun (.bun a from_ r c fresh off)) r).L, (ledgerAfter s (.bun (.bun a from_ r c fresh off)) r).nx⟩ _ rfl ?_ (fun h => hl' m h)
          intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | ack mm =>
    cases mm with
    | bun a b c d e f =>
      have hl : ledgerEv s (.ack (.bun a b c d e f)) m = none := by simp [ledgerEv]
      rw [ledgerAfter_none _ _ _ hl]
      simp [exec, exec0]
    | ack a c p o =>
      have hl' : ∀ m', m' ≠ p → ledgerEv s (.ack (.ack a c p o)) m' = none := by
        intro m' hm'; simp [ledgerEv, hm']
      simp only [exec, exec0]
      refine key p ⟨(DtnForward.step (s.nodes p).f s.t (.acked c bid)).1,
          (ledgerAfter s (.ack (.ack a c p o)) p).B, (ledgerAfter s (.ack (.ack a c p o)) p).L, (ledgerAfter s (.ack (.ack a c p o)) p).nx⟩ _ rfl ?_ (fun h => hl' m h)
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | lose mm =>
    have hl : ledgerEv s (.lose mm) m = none := by simp [ledgerEv]
    rw [ledgerAfter_none _ _ _ hl]
    simp [exec, exec0]
  | press n k =>
    have hl' : ∀ m', m' ≠ n → ledgerEv s (.press n k) m' = none := by
      intro m' hm'; simp [ledgerEv, hm']
    by_cases herr : (DtnStore.admitItem (s.nodes n).L ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t).err = none
    · have hl : ledgerEv s (.press n k) n = some (.hostAdmit ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t) := by
        simp [ledgerEv, herr]
      simp only [exec, exec0]
      rw [herr]
      simp only
      refine key n ⟨if (DtnStore.admitItem (s.nodes n).L ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t).ev.any
            (fun e => e.key.space == 1) then (DtnForward.step (s.nodes n).f s.t (.forget bid)).1 else (s.nodes n).f,
          (s.nodes n).B,
          (DtnStore.admitItem (s.nodes n).L ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t).L, (s.nodes n).nx⟩ _ rfl ?_ (fun h => hl' m h)
      intro h; subst h
      simp [ledgerAfter, hl, DtnStore.step]
    · have hl : ledgerEv s (.press n k) m = none := by
        by_cases hmn : m = n
        · subst hmn; simp [ledgerEv, herr]
        · exact hl' m hmn
      rw [ledgerAfter_none _ _ _ hl]
      have : ∃ e, (DtnStore.admitItem (s.nodes n).L ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t).err = some e := by
        cases h : (DtnStore.admitItem (s.nodes n).L ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t).err with
        | none => exact absurd h herr
        | some e => exact ⟨e, rfl⟩
      obtain ⟨e, he⟩ := this
      simp [exec, exec0, he]
  | bad => simp [exec, exec0, ledgerAfter, ledgerEv]


theorem exec_cfg (s : Sys) (ev : Ev) : (exec s ev).cfg = s.cfg := by
  cases ev <;> (simp only [exec, exec0, Sys.set]; repeat' split) <;> rfl

theorem node_reach {s : Sys} (h : Reach s) :
    ∀ m ∈ s.cfg.ids, DtnStore.Reach ⟨(s.nodes m).B, (s.nodes m).L, (s.nodes m).nx⟩ := by
  induction h with
  | init c hn hsrc hmax hacc hhold =>
    intro m hm
    have h0 : DtnStore.Reach ⟨List.replicate c.bslots none, DtnStore.Ledger.empty (if m = c.tight then 0 else c.lbud) c.lslots, 0⟩ :=
      DtnStore.Reach.init _ _ _ (by split <;> omega)
    by_cases hms : m = c.src
    · subst hms
      simp only [Sys.init, ite_true]
      exact DtnStore.Reach.step (.accept bid 1 c.exp 0 0) h0 (by trivial)
    · simp only [Sys.init, hms, ite_false, Node.empty]
      exact h0
  | @step s0 ev hR hE ih =>
    intro m hm
    rw [exec_cfg] at hm
    have h1 := ih m hm
    obtain ⟨hb, hl, hn⟩ := exec_BL s0 ev m hm
    rw [hb, hl, hn]
    unfold ledgerAfter
    cases hle : ledgerEv s0 ev m with
    | none => simp only [hle]; exact h1
    | some le => simp only [hle]; exact DtnStore.Reach.step le h1 (ledgerEv_allowed s0 ev m le hle)

/-- At every node of every reachable system the charge is the sum of the sizes within the budget, no bundle is held
twice and the item of a held bundle is custody. -/
theorem node_inv {s : Sys} (h : Reach s) (m : Nat) (hm : m ∈ s.cfg.ids) :
    DtnStore.SInv ⟨(s.nodes m).B, (s.nodes m).L, (s.nodes m).nx⟩ :=
  DtnStore.reach_inv (node_reach h m hm)

/-- The only events that touch the ledger key of a bundle on purpose are the release of a delivered or expired bundle
by a poll at that node and an acknowledgement addressed to it. -/
theorem ledgerEv_touches (s : Sys) (ev : Ev) (m : Nat) (le : DtnStore.Ev) (k : DtnStore.Key)
    (h : ledgerEv s ev m = some le) (ht : le.touches k) :
    (ev = .poll m ∧ ∃ b, (DtnForward.poll (s.nodes m).f).2 = .release b) ∨ ∃ a c o, ev = .ack (.ack a c m o) := by
  cases ev with
  | tick => simp only [ledgerEv] at h; cases h; exact absurd ht (by simp [DtnStore.Ev.touches])
  | poll n =>
    simp only [ledgerEv] at h
    by_cases hmn : m = n
    · subst hmn
      simp only [if_true] at h
      cases hp : DtnForward.poll (s.nodes m).f with
      | mk f' a =>
        rw [hp] at h
        cases a with
        | none => simp at h
        | send p b c r =>
          simp only at h
          split at h
          · cases h; exact absurd ht (by simp [DtnStore.Ev.touches])
          · simp at h
        | release b => left; exact ⟨rfl, b, rfl⟩
    · simp [hmn] at h
  | bun mm =>
    cases mm with
    | bun a b c d e f =>
      simp only [ledgerEv] at h
      split at h
      · cases h; exact absurd ht (by simp [DtnStore.Ev.touches])
      · simp at h
    | ack a b c d => simp [ledgerEv] at h
  | ack mm =>
    cases mm with
    | ack a c p o =>
      simp only [ledgerEv] at h
      split at h
      · rename_i hp; right; exact ⟨a, c, o, by rw [hp]⟩
      · simp at h
    | bun a b c d e f => simp [ledgerEv] at h
  | press n k' =>
    simp only [ledgerEv] at h
    split at h
    · cases h; exact absurd ht (by simp [DtnStore.Ev.touches])
    · simp at h
  | contact a b up => simp [ledgerEv] at h
  | lose mm => simp [ledgerEv] at h
  | bad => simp [ledgerEv] at h

/-- **Custody is never dropped before expiry.** A custody item of a node stays in that node's ledger through every
event except the release of a delivered or expired bundle by a poll there and an acknowledgement addressed to it, as
long as it has not expired at the time the event passes to the ledger. In particular a send, a refused or accepted
custody of any bundle, an admission of any space, a lost message, a tick before the expiry and a contact never drop it. -/
theorem custody_stays {s : Sys} (h : Reach s) (ev : Ev) (m : Nat) (hm : m ∈ s.cfg.ids) (e : DtnStore.Entry)
    (he : e ∈ (s.nodes m).L.entries) (hc : e.cls = .custody)
    (hlive : ∀ le t, ledgerEv s ev m = some le → le.now = some t → DtnStore.expiredAt t e = false)
    (hn : ¬ ((ev = .poll m ∧ ∃ b, (DtnForward.poll (s.nodes m).f).2 = .release b) ∨ ∃ a c o, ev = .ack (.ack a c m o))) :
    e ∈ ((exec s ev).nodes m).L.entries := by
  obtain ⟨-, hl, -⟩ := exec_BL s ev m hm
  rw [hl]
  unfold ledgerAfter
  cases hle : ledgerEv s ev m with
  | none => simpa [hle] using he
  | some le =>
    simp only [hle]
    exact DtnStore.custody_exit (node_inv h m hm) le (ledgerEv_allowed s ev m le hle) e he hc
      (fun t ht => hlive le t hle ht) (fun ht => hn (ledgerEv_touches s ev m le e.key hle ht))

/-- **Relief only from a valid ack from exactly the node custody was offered to.** An item that stops being custody
does so through an acknowledgement addressed to its node by a custodian to whom that node had offered custody. -/
theorem relief_only_by_offered_ack {s : Sys} (h : Reach s) (ev : Ev) (m : Nat) (hm : m ∈ s.cfg.ids)
    (e e' : DtnStore.Entry) (he : e ∈ (s.nodes m).L.entries) (hc : e.cls = .custody)
    (hlive : ∀ le t, ledgerEv s ev m = some le → le.now = some t → DtnStore.expiredAt t e = false)
    (he' : e' ∈ ((exec s ev).nodes m).L.entries) (hk : e'.key = e.key) (ht : e'.cls = .transit) :
    ∃ a c o, ev = .ack (.ack a c m o) ∧ e.key = DtnStore.bkey bid ∧
      ∃ r ∈ DtnStore.recs (s.nodes m).B, r.bundle = bid ∧ r.offered = some c ∧ r.oid = o := by
  obtain ⟨-, hl, -⟩ := exec_BL s ev m hm
  rw [hl] at he'
  unfold ledgerAfter at he'
  cases hle : ledgerEv s ev m with
  | none => simp only [hle] at he'; exact absurd he' (fun h' => by
      have := DtnStore.key_unique (node_inv h m hm).inv h' he hk
      rw [this, hc] at ht; cases ht)
  | some le =>
    simp only [hle] at he'
    obtain ⟨b, c, o, hev, hkey, hr⟩ := DtnStore.custody_to_transit_only_by_relief (node_inv h m hm) le
      (ledgerEv_allowed s ev m le hle) e e' he hc (fun t ht => hlive le t hle ht) he' hk ht
    subst hev
    rcases ledgerEv_touches s ev m (.ack b c o true) e.key hle (by simp [DtnStore.Ev.touches, hkey]) with ⟨hp, b0, hrel⟩ | ⟨a, c', o', hev'⟩
    · subst hp
      have hp2 : DtnForward.poll (s.nodes m).f = ((DtnForward.poll (s.nodes m).f).1, .release b0) := Prod.ext rfl hrel
      simp only [ledgerEv, if_true] at hle
      rw [hp2] at hle
      simp at hle
    · subst hev'
      simp only [ledgerEv] at hle
      split at hle
      · cases hle
        obtain ⟨r0, hr0, hr1, hr2, hr3⟩ := hr
        exact ⟨a, _, _, rfl, hkey, r0, hr0, hr1, hr2, hr3⟩
      · simp at hle

end Pinc.DtnScenario
