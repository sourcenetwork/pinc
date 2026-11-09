import Vinc.DtnForwardRetr

/-!
# The forwarder: timers, expiry, ordering, spray and the destination

Theorems about `DtnForward.advance`, `poll`, `spray` and `retr`, for every table capacity and every state.

* Timers (`advance_timer_up`, `advance_timer_down`, `advance_now`, `advance_unreadable`): the elapsed time is charged
  to a running timer exactly when its link is up, a timer on a link that is down keeps its time, the clock is the
  maximum of the old clock and the offered time, and nothing else of the state changes.
* Expiry is wall-clock (`expiry_ignores_links`, `poll_release_done`, `poll_release_only_done`): a delivered or expired
  bundle is released first, whatever the links and timers say, and a release is only of such a bundle.
* Order (`poll_retr_after_release`, `poll_spray_after_retr`): release, then retransmission, then new handovers.
* Give-up (`poll_gives_up_only`): a transfer gives up only with its timer out, its link up and its sends used.
* Spray (`spray_send_spec`, `poll_send_spec`): a handover to the destination carries no copies, to anyone else it
  hands `copies / 2` and the holder keeps at least one; a transfer is created once per (bundle, peer).
* The destination (`poll_serves_ready`, `dest_served`, `poll_quiet_spec`): whenever a bundle is held, the link to a
  peer is up, no transfer to that peer exists and there is a free transfer slot, `poll` does something; for the
  destination that something is a delivery (or an earlier action) and when `poll` is quiet, every such pair is
  already served, has no free transfer slot, or is a non-destination peer with a single copy.
-/

namespace Vinc.DtnForward

/-! ### Timers -/

theorem advance_now (f : F) (n : Nat) : (advance f n).now = max f.now n := rfl

theorem advance_unreadable (f : F) (n : Nat) :
    (advance f n).bs = f.bs ∧ (advance f n).ls = f.ls ∧ (advance f n).retry = f.retry ∧
      (advance f n).maxSends = f.maxSends := ⟨rfl, rfl, rfl, rfl⟩

/-- A running timer on a link that is up is charged the elapsed time (saturating at 0). -/
theorem advance_timer_up (f : F) (n i r s : Nat) (t : Transfer) (h : slot f.ts i = some t)
    (hp : t.phase = .sent r s) (hu : upLink f.ls t.peer = true) :
    slot (advance f n).ts i = some { t with phase := .sent (r - (n - f.now)) s } := by
  simp only [advance]
  rw [slot_map _ _ rfl, h]
  simp [hp, hu]

/-- A running timer on a link that is down keeps its time, whatever the elapsed time. -/
theorem advance_timer_down (f : F) (n i : Nat) (t : Transfer) (h : slot f.ts i = some t)
    (hu : upLink f.ls t.peer = false) : slot (advance f n).ts i = some t := by
  simp only [advance]
  rw [slot_map _ _ rfl, h]
  cases hp : t.phase <;> simp [hp, hu]

/-- Other phases are untouched by the elapsed time. -/
theorem advance_timer_idle (f : F) (n i : Nat) (t : Transfer) (h : slot f.ts i = some t)
    (hp : t.phase = .acked ∨ t.phase = .gaveUp) : slot (advance f n).ts i = some t := by
  simp only [advance]
  rw [slot_map _ _ rfl, h]
  rcases hp with hp | hp <;> simp [hp]

/-- Time charged never exceeds what was left: a timer only goes down. -/
theorem advance_timer_le (f : F) (n i r s : Nat) (t : Transfer) (h : slot f.ts i = some t)
    (hp : t.phase = .sent r s) :
    ∃ r', (slot (advance f n).ts i).map (·.phase) = some (.sent r' s) ∧ r' ≤ r := by
  by_cases hu : upLink f.ls t.peer = true
  · rw [advance_timer_up f n i r s t h hp hu]; exact ⟨r - (n - f.now), rfl, Nat.sub_le _ _⟩
  · have : upLink f.ls t.peer = false := by simpa using hu
    rw [advance_timer_down f n i t h this]; exact ⟨r, by simp [hp], Nat.le_refl _⟩

/-! ### Expiry is wall-clock -/

/-- The bundle that `poll` finds done depends on the clock and the bundles only: the links and the transfers do
not enter, so no outage delays an expiry. -/
theorem expiry_ignores_links (f : F) (ls : List (Option Link)) (ts : List (Option Transfer)) :
    doneIdx { f with ls := ls, ts := ts } = doneIdx f := rfl

theorem expiry_clock (f : F) (n : Nat) :
    doneIdx (advance f n) = firstIdx (fun b => b.delivered || decide (b.exp ≤ max f.now n)) f.bs := rfl

theorem poll_release_done (f : F) (i : Nat) (h : doneIdx f = some i) :
    ∃ b, slot f.bs i = some b ∧ (b.delivered = true ∨ b.exp ≤ f.now) ∧ poll f = (dropB f b.id, .release b.id) := by
  obtain ⟨b, hb, hp, _⟩ := firstIdx_some h
  refine ⟨b, hb, by simpa using hp, ?_⟩
  simp [poll, h, hb]

theorem spray_not_release (f : F) (id : Nat) : (spray f).2 ≠ .release id := by
  unfold spray
  repeat' split
  all_goals simp

theorem poll_release_only_done (f f' : F) (id : Nat) (h : poll f = (f', .release id)) :
    ∃ i b, doneIdx f = some i ∧ slot f.bs i = some b ∧ b.id = id ∧ (b.delivered = true ∨ b.exp ≤ f.now) := by
  unfold poll at h
  cases hd : doneIdx f with
  | some i =>
    obtain ⟨b, hb, hp, _⟩ := firstIdx_some hd
    simp only [hd, hb] at h
    simp at h
    exact ⟨i, b, rfl, hb, h.2, by simpa using hp⟩
  | none =>
    simp only [hd] at h
    cases hr : retr (upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a =>
      cases a with
      | some x =>
        obtain ⟨p, bb, c, hx⟩ := retr_act (x := x) (by rw [hr])
        simp only [hr, hx] at h
        simp at h
      | none =>
        simp only [hr] at h
        exact absurd (congrArg Prod.snd h) (spray_not_release _ _)

/-! ### The spray -/

theorem cand_spec {f : F} {li bi : Nat} (h : cand f = some (li, bi)) :
    ∃ l b, slot f.ls li = some l ∧ l.up = true ∧ slot f.bs bi = some b ∧
      anyS (fun t => t.bundle == b.id && t.peer == l.peer) f.ts = false ∧
      (l.peer == b.dest || b.copies / 2 != 0) = true := by
  unfold cand at h
  obtain ⟨x, _, hx⟩ := List.exists_of_findSome?_eq_some h
  cases hl : slot f.ls x with
  | none => simp [hl] at hx
  | some l =>
    by_cases hu : l.up = true
    · simp only [hl, hu, if_true] at hx
      obtain ⟨y, _, hy⟩ := List.exists_of_findSome?_eq_some hx
      cases hb : slot f.bs y with
      | none => simp [hb] at hy
      | some b =>
        simp only [hb] at hy
        by_cases ha : anyS (fun t => t.bundle == b.id && t.peer == l.peer) f.ts = true
        · simp [ha] at hy
        · by_cases hc : (l.peer != b.dest && b.copies / 2 == 0) = true
          · simp [ha, hc] at hy
          · simp only [ha, hc, if_false, Option.some.injEq, Prod.mk.injEq] at hy
            obtain ⟨rfl, rfl⟩ := hy
            refine ⟨l, b, hl, hu, hb, by simpa using ha, ?_⟩
            by_cases hd : l.peer = b.dest
            · simp [hd]
            · simp [hd] at hc; simp [hd]; omega
    · simp [hl, hu] at hx

theorem cand_none_spec {f : F} (h : cand f = none) {li bi : Nat} {l : Link} {b : Bundle}
    (hl : slot f.ls li = some l) (hu : l.up = true) (hb : slot f.bs bi = some b) :
    anyS (fun t => t.bundle == b.id && t.peer == l.peer) f.ts = true ∨ (l.peer != b.dest && b.copies / 2 == 0) = true := by
  unfold cand at h
  rw [List.findSome?_eq_none_iff] at h
  have h1 := h li (List.mem_range.mpr (slot_lt hl))
  simp only [hl, hu, if_true] at h1
  rw [List.findSome?_eq_none_iff] at h1
  have h2 := h1 bi (List.mem_range.mpr (slot_lt hb))
  simp only [hb] at h2
  by_cases ha : anyS (fun t => t.bundle == b.id && t.peer == l.peer) f.ts = true
  · exact Or.inl ha
  · right
    by_cases hc : (l.peer != b.dest && b.copies / 2 == 0) = true
    · exact hc
    · simp [ha, hc] at h2

/-- What a spray that sends does, in full. -/
theorem spray_unfold {f f' : F} {p id c : Nat} {r : Bool} (h : spray f = (f', .send p id c r)) :
    r = false ∧ ∃ li bi s l b, cand f = some (li, bi) ∧ slot f.ls li = some l ∧ slot f.bs bi = some b ∧
      freeIdx f.ts = some s ∧ p = l.peer ∧ id = b.id ∧
      c = (if l.peer == b.dest then 0 else b.copies / 2) ∧
      f' = { f with
        ts := upd f.ts s fun _ => some ⟨b.id, l.peer, c, l.peer == b.dest, .sent f.retry 1⟩
        bs := upd f.bs bi (Option.map fun b => { b with copies := b.copies - c }) } := by
  unfold spray at h
  cases hc : cand f with
  | none => simp [hc] at h
  | some q =>
    obtain ⟨li, bi⟩ := q
    simp only [hc] at h
    cases hl : slot f.ls li with
    | none => simp [hl] at h
    | some l =>
      cases hb : slot f.bs bi with
      | none => simp [hl, hb] at h
      | some b =>
        cases hs : freeIdx f.ts with
        | none => simp [hl, hb, hs] at h
        | some s =>
          simp only [hl, hb, hs, Prod.mk.injEq, Act.send.injEq] at h
          obtain ⟨hf, hp, hi, hcc, hr⟩ := h
          refine ⟨hr.symm, li, bi, s, l, b, rfl, hl, hb, rfl, hp.symm, hi.symm, hcc.symm, ?_⟩
          rw [← hf]
          simp only [hcc.symm]

theorem spray_send_spec {f f' : F} {p id c : Nat} {r : Bool} (h : spray f = (f', .send p id c r)) :
    r = false ∧ upLink f.ls p = true ∧ anyS (fun t => t.bundle == id && t.peer == p) f.ts = false ∧
      anyS (fun t => t.bundle == id && t.peer == p) f'.ts = true ∧ f'.now = f.now ∧
      ∃ bi b, slot f.bs bi = some b ∧ b.id = id ∧
        slot f'.bs bi = some { b with copies := b.copies - c } ∧
        ((p = b.dest ∧ c = 0) ∨ (p ≠ b.dest ∧ c = b.copies / 2 ∧ 1 ≤ c ∧ 1 ≤ b.copies - c)) := by
  obtain ⟨hr, li, bi, s, l, b, hc, hl, hb, hs, hp, hi, hcc, hf⟩ := spray_unfold h
  obtain ⟨l', b', hl', hu, hb', hno, hok⟩ := cand_spec hc
  rw [hl] at hl'; rw [hb] at hb'
  cases hl'; cases hb'
  obtain ⟨hsn, hsl⟩ := freeIdx_some hs
  subst hp hi
  refine ⟨hr, ?_, hno, ?_, by rw [hf], bi, b, hb, rfl, ?_, ?_⟩
  · exact (anyS_iff _ _).mpr ⟨li, l, hl, by simp [hu]⟩
  · rw [anyS_iff]
    refine ⟨s, ⟨b.id, l.peer, c, l.peer == b.dest, .sent f.retry 1⟩, ?_, by simp⟩
    rw [hf]; exact slot_upd_same _ _ _ hsl
  · rw [hf]
    have := slot_upd_same f.bs bi (Option.map fun b => { b with copies := b.copies - c }) (slot_lt hb)
    simpa [hb] using this
  · by_cases hd : l.peer = b.dest
    · left; exact ⟨hd, by simp [hd] at hcc; exact hcc⟩
    · right
      have hdb : (l.peer == b.dest) = false := by simpa using hd
      simp only [hdb, Bool.false_eq_true, if_false] at hcc
      have h2 : b.copies / 2 ≠ 0 := by
        have := hok; simp [hdb] at this; omega
      refine ⟨hd, hcc, by omega, by omega⟩

/-! ### Poll -/

/-- A scan keeps which slots are occupied and by what bundle and peer. -/
theorem retr_anyS {up : Nat → Bool} {retry maxS : Nat} (ts : List (Option Transfer)) (x y : Nat) :
    anyS (fun t => t.bundle == x && t.peer == y) (retr up retry maxS ts).1 = anyS (fun t => t.bundle == x && t.peer == y) ts := by
  obtain ⟨_, hs⟩ := retr_rel up retry maxS ts
  have key : ∀ (a b : Bool), (a = true ↔ b = true) → a = b := by
    intro a b h; cases a <;> cases b <;> simp_all
  apply key
  rw [anyS_iff, anyS_iff]
  constructor
  · rintro ⟨i, t', ht', hp⟩
    have := hs i
    rw [ht'] at this
    cases ho : slot ts i with
    | none => simp [ho, TRel] at this
    | some t =>
      rw [ho] at this
      simp only [TRel] at this
      exact ⟨i, t, ho, by simpa [this.1, this.2.1] using hp⟩
  · rintro ⟨i, t, ht, hp⟩
    have := hs i
    rw [ht] at this
    cases ho : slot (retr up retry maxS ts).1 i with
    | none => simp [ho, TRel] at this
    | some t' =>
      rw [ho] at this
      simp only [TRel] at this
      exact ⟨i, t', ho, by simpa [this.1, this.2.1] using hp⟩

theorem retr_free {up : Nat → Bool} {retry maxS : Nat} (ts : List (Option Transfer)) (s : Nat)
    (h : slot ts s = none) : slot (retr up retry maxS ts).1 s = none := by
  have := (retr_rel up retry maxS ts).2 s
  rw [h] at this
  cases ho : slot (retr up retry maxS ts).1 s with
  | none => rfl
  | some _ => simp [ho, TRel] at this

/-- `poll` does something whenever a bundle, a link that is up and a free transfer slot are ready. -/
theorem poll_serves_ready (f : F) {li bi s : Nat} {l : Link} {b : Bundle} (hl : slot f.ls li = some l)
    (hu : l.up = true) (hb : slot f.bs bi = some b)
    (hno : anyS (fun t => t.bundle == b.id && t.peer == l.peer) f.ts = false)
    (hok : (l.peer == b.dest || b.copies / 2 != 0) = true) (hs : slot f.ts s = none) (hsl : s < f.ts.length) :
    (poll f).2 ≠ .none := by
  unfold poll
  cases hd : doneIdx f with
  | some i =>
    obtain ⟨b', hb', _⟩ := firstIdx_some hd
    simp [hd, hb']
  | none =>
    simp only [hd]
    cases hr : retr (upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a =>
      cases a with
      | some x =>
        obtain ⟨p, bb, c, hx⟩ := retr_act (x := x) (by rw [hr])
        simp [hx]
      | none =>
        have hts : ts' = (retr (upLink f.ls) f.retry f.maxSends f.ts).1 := by rw [hr]
        have hno' : anyS (fun t => t.bundle == b.id && t.peer == l.peer) ts' = false := by
          rw [hts, retr_anyS]; exact hno
        have hs' : slot ts' s = none := by rw [hts]; exact retr_free _ _ hs
        have hlen : ts'.length = f.ts.length := by rw [hts]; exact (retr_rel _ _ _ _).1
        have hcand : cand { f with ts := ts' } ≠ none := by
          intro hc
          rcases cand_none_spec hc (li := li) (bi := bi) hl hu hb with h1 | h1
          · simp [hno'] at h1
          · simp at hok h1; omega
        cases hc : cand { f with ts := ts' } with
        | none => exact absurd hc hcand
        | some q =>
          obtain ⟨li', bi'⟩ := q
          obtain ⟨l', b', hl', _, hb', _⟩ := cand_spec hc
          have hfree : freeIdx ts' = some (freeIdx ts').get! ∨ True := Or.inr trivial
          have hfs := freeIdx_isSome (l := ts') (i := s) (by omega) hs'
          cases hfi : freeIdx ts' with
          | none => simp [hfi] at hfs
          | some s' => simp [spray, hc, hl', hb', hfi]


/-- Release comes first: a retransmission or a handover means no bundle was done. -/
theorem poll_send_spec {f f' : F} {p id c : Nat} {r : Bool} (h : poll f = (f', .send p id c r)) :
    doneIdx f = none ∧
    (r = true → ∃ i t s, slot f.ts i = some t ∧ t.phase = .sent 0 s ∧ upLink f.ls p = true ∧ s < f.maxSends ∧
        t.peer = p ∧ t.bundle = id ∧ t.given = c ∧
        slot f'.ts i = some { t with phase := .sent f.retry (sat8 (s + 1)) } ∧ f'.bs = f.bs) ∧
    (r = false → upLink f.ls p = true ∧ anyS (fun t => t.bundle == id && t.peer == p) f.ts = false ∧
        ∃ bi b, slot f.bs bi = some b ∧ b.id = id ∧ slot f'.bs bi = some { b with copies := b.copies - c } ∧
          ((p = b.dest ∧ c = 0) ∨ (p ≠ b.dest ∧ c = b.copies / 2 ∧ 1 ≤ c ∧ 1 ≤ b.copies - c))) := by
  unfold poll at h
  cases hd : doneIdx f with
  | some i =>
    obtain ⟨b, hb, _⟩ := firstIdx_some hd
    simp [hd, hb] at h
  | none =>
    simp only [hd] at h
    refine ⟨rfl, ?_⟩
    cases hr : retr (upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a =>
      cases a with
      | some x =>
        have hx := retr_send_slot (up := upLink f.ls) (retry := f.retry) (maxS := f.maxSends) (ts := f.ts) (x := x)
          (by rw [hr])
        simp only [hr] at hx h
        obtain ⟨i, t, sd, h1, h2, h3, h4, h5, h6⟩ := hx
        obtain ⟨hf, hx2⟩ := Prod.mk.inj h
        subst hf
        rw [h6] at hx2
        simp only [Act.send.injEq] at hx2
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hx2
        exact ⟨fun _ => ⟨i, t, sd, h1, h2, h3, h4, rfl, rfl, rfl, h5, rfl⟩, fun hf => by simp at hf⟩
      | none =>
        simp only [hr] at h
        obtain ⟨hr0, hup, hno, _, _, bi, b, hb, hid, hb', hcase⟩ := spray_send_spec h
        have hts : ts' = (retr (upLink f.ls) f.retry f.maxSends f.ts).1 := by rw [hr]
        refine ⟨fun hf => by simp [hr0] at hf, fun _ => ⟨hup, ?_, bi, b, hb, hid, hb', hcase⟩⟩
        rw [← retr_anyS (up := upLink f.ls) (retry := f.retry) (maxS := f.maxSends), ← hts]
        exact hno

/-- A quiet poll: no bundle is done, and every held bundle with a link up is served, or the transfer table is full,
or the peer is not the destination and a single copy is left. -/
theorem poll_quiet_spec {f f' : F} (h : poll f = (f', .none)) :
    doneIdx f = none ∧ ∀ {li bi : Nat} {l : Link} {b : Bundle}, slot f.ls li = some l → l.up = true →
      slot f.bs bi = some b →
      anyS (fun t => t.bundle == b.id && t.peer == l.peer) f.ts = true ∨ freeIdx f.ts = none ∨
        (l.peer != b.dest && b.copies / 2 == 0) = true := by
  have hd : doneIdx f = none := by
    cases hd : doneIdx f with
    | none => rfl
    | some i =>
      obtain ⟨b, _, _, hp⟩ := poll_release_done f i hd
      rw [hp] at h; simp at h
  refine ⟨hd, fun {li bi l b} hl hu hb => ?_⟩
  by_cases ha : anyS (fun t => t.bundle == b.id && t.peer == l.peer) f.ts = true
  · exact Or.inl ha
  · right
    cases hf : freeIdx f.ts with
    | none => exact Or.inl rfl
    | some s =>
      right
      refine Classical.byContradiction fun hc => ?_
      obtain ⟨hs, hsl⟩ := freeIdx_some hf
      have hok : (l.peer == b.dest || b.copies / 2 != 0) = true := by
        by_cases hd2 : l.peer = b.dest
        · simp [hd2]
        · simp [hd2] at hc ⊢; omega
      exact poll_serves_ready f hl hu hb (by simpa using ha) hok hs hsl (by rw [h])

/-- The destination is always served: when `poll` is quiet, a held bundle whose destination's link is up has a
transfer to it, or the transfer table is full. -/
theorem dest_served {f f' : F} (h : poll f = (f', .none)) {li bi : Nat} {l : Link} {b : Bundle}
    (hl : slot f.ls li = some l) (hu : l.up = true) (hb : slot f.bs bi = some b) (hd : l.peer = b.dest) :
    anyS (fun t => t.bundle == b.id && t.peer == l.peer) f.ts = true ∨ freeIdx f.ts = none := by
  rcases (poll_quiet_spec h).2 hl hu hb with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · simp [hd] at h1

theorem spray_cases (f : F) :
    spray f = (f, .none) ∨ ∃ f' p id c, spray f = (f', .send p id c false) := by
  unfold spray
  repeat' split
  all_goals first
    | (left; rfl)
    | (right; exact ⟨_, _, _, _, rfl⟩)

theorem spray_ts_old (f : F) {i : Nat} {t : Transfer} (h : slot f.ts i = some t) :
    slot (spray f).1.ts i = some t := by
  rcases spray_cases f with hs | ⟨f', p, id, c, hs⟩
  · rw [hs]; exact h
  · obtain ⟨_, li, bi, s, l, b, _, _, _, hfs, _, _, _, hf⟩ := spray_unfold hs
    obtain ⟨hsn, _⟩ := freeIdx_some hfs
    rw [hs]
    show slot f'.ts i = some t
    rw [hf]
    have : i ≠ s := fun e => by subst e; simp [h] at hsn
    simpa using (slot_upd_ne f.ts s i _ this).trans h

/-- A transfer gives up only with its timer out, its link up and its sends used. -/
theorem poll_gives_up_only {f f' : F} {a : Act} (h : poll f = (f', a)) {i : Nat} {t t' : Transfer}
    (ht : slot f.ts i = some t) (ht' : slot f'.ts i = some t') (hg : t'.phase = .gaveUp) :
    t.phase = .gaveUp ∨ ∃ s, t.phase = .sent 0 s ∧ upLink f.ls t.peer = true ∧ f.maxSends ≤ s := by
  have key : ∀ ts' a1, (∀ j, TRel (upLink f.ls) f.retry f.maxSends a1
      (slot f.ts j) (slot ts' j)) → slot ts' i = some t' →
      t.phase = .gaveUp ∨ ∃ s, t.phase = .sent 0 s ∧ upLink f.ls t.peer = true ∧ f.maxSends ≤ s := by
    intro ts' a1 hrel hs'
    have := hrel i
    rw [ht, hs'] at this
    simp only [TRel] at this
    obtain ⟨_, _, _, _, h1 | ⟨s, h2, h3, h4, h5⟩ | ⟨s, h2, h3, h4, h5, _⟩⟩ := this
    · subst h1; exact Or.inl hg
    · exact Or.inr ⟨s, h2, h3, h4⟩
    · subst h5; simp at hg
  unfold poll at h
  cases hd : doneIdx f with
  | some j =>
    simp only [hd] at h
    obtain ⟨hf, _⟩ := Prod.mk.inj h
    subst hf
    simp only [dropB] at ht'
    rw [slot_map _ _ rfl, ht] at ht'
    split at ht'
    · simp at ht'
    · cases ht'; exact Or.inl hg
  | none =>
    simp only [hd] at h
    cases hr : retr (upLink f.ls) f.retry f.maxSends f.ts with
    | mk ts' a0 =>
      have hrel := (retr_rel (upLink f.ls) f.retry f.maxSends f.ts).2
      simp only [hr] at hrel
      cases a0 with
      | some x =>
        simp only [hr] at h
        obtain ⟨hf, _⟩ := Prod.mk.inj h
        subst hf
        exact key ts' _ hrel ht'
      | none =>
        simp only [hr] at h
        have h1 : ∃ t1, slot ts' i = some t1 := by
          have := hrel i
          rw [ht] at this
          cases hs : slot ts' i with
          | none => rw [hs] at this; simp [TRel] at this
          | some t1 => exact ⟨t1, rfl⟩
        obtain ⟨t1, h1⟩ := h1
        have h2 := spray_ts_old { f with ts := ts' } (i := i) (t := t1) h1
        rw [show (spray { f with ts := ts' }).1 = f' from congrArg Prod.fst h] at h2
        rw [ht'] at h2
        cases h2
        exact key ts' _ hrel h1

end Vinc.DtnForward
