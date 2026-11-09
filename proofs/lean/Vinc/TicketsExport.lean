import Vinc.TicketsClient

/-!
# Exporting and restoring the client tickets

`ClientTickets::export` and `ClientTickets::restore` of `vinc-security/src/tickets.rs`. `export` keeps the live
(unexpired) tickets, orders them by `(stamp, index)`, and writes the newest at most `max`, oldest first, in the format
of `Vinc.TicketsWire`. `restore` checks the whole input first (`decode`), stores nothing if it is malformed, and
otherwise inserts, in order, every entry with `expiry >= now` through `cInsert` (the model of `insert`), returning how
many entries it took (entries counted even when `N = 0` stores nothing or a later entry of the same peer replaces
them).

`restore_export` is the round trip: restoring an export of a reachable store into an empty store with room for it
yields exactly the exported tickets, in the order of the export.
-/

namespace Vinc.Tickets

/-! ## The operations -/

/-- `(stamp, index)` of the live (`expiry >= now`) tickets, in index order, from index `i`. -/
def livePairs (now : Nat) : Slots → Nat → List (Nat × Nat)
  | [], _ => []
  | none :: l, i => livePairs now l (i + 1)
  | some s :: l, i => if now ≤ s.expiry then (s.stamp, i) :: livePairs now l (i + 1) else livePairs now l (i + 1)

/-- The order of `sort_unstable` on `(u64, usize)` pairs. -/
def pairLe (a b : Nat × Nat) : Bool := decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))

/-- The live pairs sorted by `(stamp, index)`. -/
def sortedLive (l : Slots) (now : Nat) : List (Nat × Nat) := (livePairs now l 0).mergeSort pairLe

/-- The live pairs `export` writes: all but the oldest `live - min live max` skipped. -/
def exportPairs (l : Slots) (now max : Nat) : List (Nat × Nat) :=
  (sortedLive l now).drop ((sortedLive l now).length - min (sortedLive l now).length max)

/-- The ticket in slot `i`. -/
def tkAt (l : Slots) (i : Nat) : Option Tk := ((l[i]?).getD none).map (·.tk)

/-- The tickets `export` writes, oldest first. -/
def exportList (l : Slots) (now max : Nat) : List Tk := (exportPairs l now max).filterMap fun p => tkAt l p.2

/-- Why `export` fails: the buffer is too small, or the count does not fit a byte. -/
inductive ExportErr where
  | small
  | count

/-- `ClientTickets::export` into a buffer of `cap` bytes: the bytes written, or the error. -/
def exportBytes (l : Slots) (now max cap : Nat) : Except ExportErr (List Nat) :=
  let ts := exportList l now max
  if cap < 1 then .error .small
  else if 255 < ts.length then .error .count
  else if (encode ts).length ≤ cap then .ok (encode ts) else .error .small

/-- `ClientTickets::restore`: nothing is stored unless the whole input decodes; then every entry with
`expiry >= now` is inserted. Returns the store and the count (`none`: the input was malformed). -/
def restore (st : Store) (bytes : List Nat) (now : Nat) : Store × Option Nat :=
  match decode bytes with
  | none => (st, none)
  | some ts =>
    let live := ts.filter fun t => decide (now ≤ t.expiry)
    (live.foldl (fun s t => cInsert s t now) st, some live.length)

/-- The tickets in a slot array, in slot order. -/
def tks (l : Slots) : List Tk := l.filterMap fun x => x.map (·.tk)

/-- `Tickets.restore_malformed`: an input that does not decode stores nothing. -/
theorem restore_malformed (st : Store) {bytes : List Nat} (h : decode bytes = none) (now : Nat) :
    restore st bytes now = (st, none) := by
  simp [restore, h]

/-- `Tickets.restore_filters`: only the entries that have not expired are inserted, and the count is theirs. -/
theorem restore_live (st : Store) {bytes : List Nat} {ts : List Tk} (h : decode bytes = some ts) (now : Nat) :
    restore st bytes now =
      ((ts.filter fun t => decide (now ≤ t.expiry)).foldl (fun s t => cInsert s t now) st,
        some (ts.filter fun t => decide (now ≤ t.expiry)).length) := by
  simp [restore, h]

/-- `Tickets.restore_zero`: a store without slots stays without slots, whatever is restored. -/
theorem restore_zero (clock : Nat) (bytes : List Nat) (now : Nat) : (restore ⟨[], clock⟩ bytes now).1.slots = [] := by
  unfold restore
  cases decode bytes with
  | none => rfl
  | some ts =>
    simp only
    have : ∀ (L : List Tk) (c : Nat), (L.foldl (fun s t => cInsert s t now) ⟨[], c⟩).slots = [] := by
      intro L
      induction L with
      | nil => intro c; rfl
      | cons t L ih =>
        intro c
        simp only [List.foldl]
        have h1 := cInsert_nil t now c
        have h2 : cInsert ⟨[], c⟩ t now = ⟨[], c + 1⟩ := by
          have := cInsert_clock ⟨[], c⟩ t now
          cases hh : cInsert ⟨[], c⟩ t now with
          | mk s cl => rw [hh] at h1 this; simp at h1 this; rw [h1, this]
        rw [h2]; exact ih (c + 1)
    exact this _ _

/-! ## The order of the export -/

theorem pairLe_iff (a b : Nat × Nat) : pairLe a b = true ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) := by
  simp [pairLe]

theorem livePairs_mem : ∀ (l : Slots) (now i0 s i : Nat), (s, i) ∈ livePairs now l i0 ↔
    ∃ (k : Nat) (t : Slot), l[k]? = some (some t) ∧ i = i0 + k ∧ s = t.stamp ∧ now ≤ t.expiry := by
  intro l
  induction l with
  | nil => intro now i0 s i; simp [livePairs]
  | cons x l ih =>
    intro now i0 s i
    cases x with
    | none =>
      simp only [livePairs, ih]
      constructor
      · rintro ⟨k, t, hk, hi, hs, he⟩
        exact ⟨k + 1, t, by simpa using hk, by omega, hs, he⟩
      · rintro ⟨k, t, hk, hi, hs, he⟩
        cases k with
        | zero => simp at hk
        | succ k => exact ⟨k, t, by simpa using hk, by omega, hs, he⟩
    | some u =>
      by_cases hu : now ≤ u.expiry
      · simp only [livePairs, hu, ite_true, List.mem_cons, Prod.mk.injEq, ih]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨k, t, hk, hi, hs, he⟩)
          · exact ⟨0, u, by simp, by omega, h1, hu⟩
          · exact ⟨k + 1, t, by simpa using hk, by omega, hs, he⟩
        · rintro ⟨k, t, hk, hi, hs, he⟩
          cases k with
          | zero => simp at hk; subst hk; exact Or.inl ⟨hs, by omega⟩
          | succ k => exact Or.inr ⟨k, t, by simpa using hk, by omega, hs, he⟩
      · simp only [livePairs, hu, ite_false, ih]
        constructor
        · rintro ⟨k, t, hk, hi, hs, he⟩
          exact ⟨k + 1, t, by simpa using hk, by omega, hs, he⟩
        · rintro ⟨k, t, hk, hi, hs, he⟩
          cases k with
          | zero => simp at hk; subst hk; exact absurd he hu
          | succ k => exact ⟨k, t, by simpa using hk, by omega, hs, he⟩

theorem livePairs_idx : ∀ (l : Slots) (now i0 : Nat),
    (∀ p ∈ livePairs now l i0, i0 ≤ p.2) ∧ (livePairs now l i0).Pairwise (fun a b => a.2 < b.2) := by
  intro l
  induction l with
  | nil => intro now i0; simp [livePairs]
  | cons x l ih =>
    intro now i0
    obtain ⟨h1, h2⟩ := ih now (i0 + 1)
    cases x with
    | none =>
      simp only [livePairs]
      exact ⟨fun p hp => by have := h1 p hp; omega, h2⟩
    | some u =>
      by_cases hu : now ≤ u.expiry
      · simp only [livePairs, hu, ite_true]
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact Nat.le_refl _
          · have := h1 p hp; omega
        · exact List.Pairwise.cons (fun b hb => by have := h1 b hb; simp only; omega) h2
      · simp only [livePairs, hu, ite_false]
        exact ⟨fun p hp => by have := h1 p hp; omega, h2⟩

theorem pairLe_trans : ∀ a b c : Nat × Nat, pairLe a b = true → pairLe b c = true → pairLe a c = true := by
  intro a b c h1 h2
  rw [pairLe_iff] at *
  omega

theorem pairLe_total : ∀ a b : Nat × Nat, (pairLe a b || pairLe b a) = true := by
  intro a b
  simp only [Bool.or_eq_true, pairLe_iff]
  omega

theorem sortedLive_mem (l : Slots) (now s i : Nat) :
    (s, i) ∈ sortedLive l now ↔ ∃ (k : Nat) (t : Slot), l[k]? = some (some t) ∧ i = k ∧ s = t.stamp ∧ now ≤ t.expiry := by
  unfold sortedLive
  rw [List.mem_mergeSort, livePairs_mem]
  simp

theorem sortedLive_sorted (l : Slots) (now : Nat) : (sortedLive l now).Pairwise (fun a b => pairLe a b = true) :=
  List.pairwise_mergeSort pairLe_trans pairLe_total _

theorem sortedLive_idx (l : Slots) (now : Nat) : (sortedLive l now).Pairwise (fun a b => a.2 ≠ b.2) := by
  have h : (livePairs now l 0).Pairwise (fun a b => a.2 ≠ b.2) :=
    (livePairs_idx l now 0).2.imp (fun h => Nat.ne_of_lt h)
  exact (List.Perm.pairwise_iff (fun h => Ne.symm h) (List.mergeSort_perm _ _)).2 h

theorem sortedLive_length (l : Slots) (now : Nat) : (sortedLive l now).length = (livePairs now l 0).length := by
  simp [sortedLive, List.length_mergeSort]

/-- `Tickets.export_len`: the export holds `min live max` tickets. -/
theorem export_len (l : Slots) (now max : Nat) :
    (exportPairs l now max).length = min (livePairs now l 0).length max := by
  unfold exportPairs
  simp only [List.length_drop, sortedLive, List.length_mergeSort]
  omega

/-- `Tickets.export_unexpired`: everything exported is a live ticket of the store; an expired ticket is never
exported. -/
theorem export_mem {l : Slots} {now max : Nat} {s i : Nat} (h : (s, i) ∈ exportPairs l now max) :
    ∃ (t : Slot), l[i]? = some (some t) ∧ s = t.stamp ∧ now ≤ t.expiry := by
  unfold exportPairs at h
  have := (sortedLive_mem l now s i).1 (List.mem_of_mem_drop h)
  obtain ⟨k, t, hk, rfl, hs, he⟩ := this
  exact ⟨t, hk, hs, he⟩

/-- `Tickets.export_oldest_first`: the exported tickets are in increasing order of issue (stamp), given distinct stamps. -/
theorem export_oldest_first {st : Store} (hs : StampInv st) (now max : Nat) :
    (exportPairs st.slots now max).Pairwise (fun a b => a.1 < b.1) := by
  unfold exportPairs
  have h1 := List.Pairwise.sublist (List.drop_sublist ((sortedLive st.slots now).length - min (sortedLive st.slots now).length max) (sortedLive st.slots now)) (sortedLive_sorted st.slots now)
  have h2 := List.Pairwise.sublist (List.drop_sublist ((sortedLive st.slots now).length - min (sortedLive st.slots now).length max) (sortedLive st.slots now)) (sortedLive_idx st.slots now)
  have h3 := h1.and h2
  have hm : ∀ {a b : Nat × Nat}, a ∈ (sortedLive st.slots now).drop ((sortedLive st.slots now).length - min (sortedLive st.slots now).length max) →
      b ∈ (sortedLive st.slots now).drop ((sortedLive st.slots now).length - min (sortedLive st.slots now).length max) →
      (pairLe a b = true ∧ a.2 ≠ b.2) → a.1 < b.1 := by
    intro a b ha hb ⟨hle, hne⟩
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    obtain ⟨ta, hta, hsa, _⟩ := export_mem (l := st.slots) (now := now) (max := max) (by unfold exportPairs; exact ha)
    obtain ⟨tb, htb, hsb, _⟩ := export_mem (l := st.slots) (now := now) (max := max) (by unfold exportPairs; exact hb)
    rw [pairLe_iff] at hle
    simp only at hle hne ⊢
    rcases hle with h | ⟨h, _⟩
    · exact h
    · exact absurd (hs.2 a2 b2 ta tb hta htb (by omega)) hne
  exact h3.imp_of_mem (fun ha hb h => hm ha hb h)

/-- `Tickets.export_newest`: a live ticket that is not exported is older than every exported one: the export is the
newest `min live max` tickets. -/
theorem export_newest {st : Store} (hs : StampInv st) (now max : Nat) {k : Nat} {t : Slot}
    (hk : st.slots[k]? = some (some t)) (he : now ≤ t.expiry) (hn : (t.stamp, k) ∉ exportPairs st.slots now max) :
    ∀ b ∈ exportPairs st.slots now max, t.stamp < b.1 := by
  intro b hb
  obtain ⟨b1, b2⟩ := b
  have hmem : (t.stamp, k) ∈ sortedLive st.slots now := (sortedLive_mem _ _ _ _).2 ⟨k, t, hk, rfl, rfl, he⟩
  have hsplit : sortedLive st.slots now =
      (sortedLive st.slots now).take ((sortedLive st.slots now).length - min (sortedLive st.slots now).length max) ++
        exportPairs st.slots now max := by
    unfold exportPairs; exact (List.take_append_drop _ _).symm
  have hin : (t.stamp, k) ∈ (sortedLive st.slots now).take ((sortedLive st.slots now).length - min (sortedLive st.slots now).length max) := by
    rw [hsplit] at hmem
    rcases List.mem_append.mp hmem with h | h
    · exact h
    · exact absurd h hn
  have hpw := sortedLive_sorted st.slots now
  rw [hsplit] at hpw
  have hle := (List.pairwise_append.mp hpw).2.2 _ hin _ hb
  rw [pairLe_iff] at hle
  obtain ⟨tb, htb, hsb, _⟩ := export_mem hb
  simp only at hle ⊢
  rcases hle with h | ⟨h, _⟩
  · exact h
  · have : k = b2 := hs.2 k b2 t tb hk htb (by omega)
    subst this
    rw [h] at hn
    exact absurd hb hn

/-! ## The exported tickets -/

theorem tkAt_some {l : Slots} {i : Nat} {tk : Tk} :
    tkAt l i = some tk ↔ ∃ s : Slot, l[i]? = some (some s) ∧ s.tk = tk := by
  unfold tkAt
  cases h : l[i]? with
  | none => simp
  | some x =>
    cases x with
    | none => simp
    | some s => simp

/-- Everything `export` writes is a live ticket of the store. -/
theorem exportList_mem {l : Slots} {now max : Nat} {t : Tk} (h : t ∈ exportList l now max) :
    now ≤ t.expiry ∧ ∃ (k : Nat) (s : Slot), l[k]? = some (some s) ∧ s.tk = t := by
  unfold exportList at h
  obtain ⟨⟨s0, i⟩, hp, hf⟩ := List.mem_filterMap.mp h
  obtain ⟨s, hs, _, he⟩ := export_mem hp
  obtain ⟨s', hs', hst⟩ := tkAt_some.mp hf
  rw [hs] at hs'
  cases hs'
  exact ⟨by rw [← hst]; exact he, i, s, hs, hst⟩

/-- Every pair of the export names a ticket, so the export has one ticket per pair. -/
theorem exportList_length (l : Slots) (now max : Nat) : (exportList l now max).length = (exportPairs l now max).length := by
  unfold exportList
  have : ∀ L : List (Nat × Nat), (∀ p ∈ L, ∃ s : Slot, l[p.2]? = some (some s)) →
      (L.filterMap fun p => tkAt l p.2).length = L.length := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons p L ih =>
      intro h
      obtain ⟨s, hs⟩ := h p (by simp)
      have : tkAt l p.2 = some s.tk := tkAt_some.2 ⟨s, hs, rfl⟩
      simp only [List.filterMap_cons, this, List.length_cons]
      rw [ih (fun q hq => h q (by simp [hq]))]
  apply this
  intro p hp
  obtain ⟨p1, p2⟩ := p
  obtain ⟨s, hs, _⟩ := export_mem hp
  exact ⟨s, hs⟩

/-- `Tickets.export_one_per_peer`: the exported tickets are of pairwise different peers when the store has one ticket
per peer. -/
theorem exportList_peers {st : Store} (ho : OnePerPeer st) (now max : Nat) :
    (exportList st.slots now max).Pairwise (fun a b => a.peer ≠ b.peer) := by
  unfold exportList
  have hidx : (exportPairs st.slots now max).Pairwise (fun a b => a.2 ≠ b.2) :=
    List.Pairwise.sublist (List.drop_sublist _ _) (sortedLive_idx st.slots now)
  rw [List.pairwise_filterMap]
  refine hidx.imp_of_mem ?_
  intro a b _ _ hne x hx y hy hxy
  obtain ⟨sa, hsa, rfl⟩ := tkAt_some.mp hx
  obtain ⟨sb, hsb, rfl⟩ := tkAt_some.mp hy
  exact hne (ho a.2 b.2 sa sb hsa hsb hxy)

theorem firstIdx_pre {α : Type} (p : α → Bool) : ∀ (pre : List α) (y : α) (R : List α) (i : Nat),
    (∀ x ∈ pre, p x = false) → p y = true → firstIdx p (pre ++ y :: R) i = some (i + pre.length) := by
  intro pre
  induction pre with
  | nil => intro y R i _ hy; simp [firstIdx, hy]
  | cons x pre ih =>
    intro y R i hx hy
    have := hx x (by simp)
    simp only [List.cons_append, firstIdx, this, Bool.false_eq_true, ite_false, List.length_cons]
    rw [ih y R (i + 1) (fun z hz => hx z (by simp [hz])) hy]
    congr 1; omega

theorem set_at_append {α : Type} : ∀ (pre : List α) (y z : α) (R : List α), (pre ++ y :: R).set pre.length z = pre ++ z :: R := by
  intro pre
  induction pre with
  | nil => intro y z R; simp
  | cons x pre ih => intro y z R; simp [ih]

theorem victim_pre (now : Nat) (pre R : Slots) (h : ∀ x ∈ pre, x.isSome = true) :
    victim (pre ++ none :: R) now = some pre.length := by
  unfold victim
  rw [firstIdx_pre isEmpty pre none R 0 (fun x hx => by have := h x hx; cases x with | none => simp at this | some _ => rfl) rfl]
  simp

/-- Inserting tickets of distinct peers, none of which is stored, into a store whose first slots are full and whose
rest are empty fills the empty slots in order. -/
theorem fold_insert_shape (now : Nat) : ∀ (ts : List Tk) (pre : Slots) (c m : Nat),
    (∀ x ∈ pre, x.isSome = true) → (∀ x ∈ pre, ∀ t ∈ ts, ∀ s, x = some s → s.peer ≠ t.peer) →
    ts.Pairwise (fun a b => a.peer ≠ b.peer) → ts.length ≤ m →
    ∃ ss : List Slot, ss.map (·.tk) = ts ∧
      (ts.foldl (fun s t => cInsert s t now) ⟨pre ++ List.replicate m none, c⟩).slots =
        pre ++ ss.map some ++ List.replicate (m - ts.length) none := by
  intro ts
  induction ts with
  | nil => intro pre c m _ _ _ _; exact ⟨[], rfl, by simp⟩
  | cons t ts ih =>
    intro pre c m hpre hdis hpw hlen
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hlen; omega⟩
    have hv := victim_pre now pre (List.replicate m' none) hpre
    have hslots : pre ++ List.replicate (m' + 1) none = pre ++ none :: List.replicate m' none := by simp [List.replicate_succ]
    have hnew : cInsert ⟨pre ++ List.replicate (m' + 1) none, c⟩ t now =
        ⟨pre ++ some ⟨t, c + 1⟩ :: List.replicate m' none, c + 1⟩ := by
      rw [hslots]
      have := client_insert_new_peer (st := ⟨pre ++ none :: List.replicate m' none, c⟩) (tk := t) (now := now)
        (fun k s hk => by
          have hmem := List.mem_of_getElem? hk
          rcases List.mem_append.mp hmem with h | h
          · exact hdis _ h t (by simp) s rfl
          · rcases List.mem_cons.mp h with h | h
            · cases h
            · have := List.eq_of_mem_replicate h; cases this) hv
      rw [this]
      simp only
      rw [set_at_append]
    simp only [List.foldl_cons, hnew]
    have hnewslots : pre ++ some ⟨t, c + 1⟩ :: List.replicate m' none = (pre ++ [some ⟨t, c + 1⟩]) ++ List.replicate m' none := by simp
    rw [hnewslots]
    obtain ⟨ss, hss, hres⟩ := ih (pre ++ [some ⟨t, c + 1⟩]) (c + 1) m'
      (fun x hx => by
        rcases List.mem_append.mp hx with h | h
        · exact hpre x h
        · simp at h; subst h; rfl)
      (fun x hx u hu s hxs => by
        rcases List.mem_append.mp hx with h | h
        · exact hdis x h u (by simp [hu]) s hxs
        · simp at h; subst h; cases hxs
          exact (List.pairwise_cons.mp hpw).1 u hu)
      (List.pairwise_cons.mp hpw).2 (by simp at hlen; omega)
    refine ⟨⟨t, c + 1⟩ :: ss, by simp [hss], ?_⟩
    rw [hres]
    simp

theorem filterMap_some_tk : ∀ ss : List Slot, (ss.map some).filterMap (fun x => x.map (·.tk)) = ss.map (·.tk) := by
  intro ss
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [List.map_cons, List.filterMap_cons, Option.map_some]; rw [ih]

/-- `Tickets.restore_export`: restoring the export of a reachable store of valid tickets into an empty store with room
for it reads back exactly the exported tickets (`decode` of the bytes), counts them all and stores them, in the order
of the export. The count `min live max` must fit a byte and the new store. -/
theorem restore_export {N N' : Nat} {st : Store} (h : CReach N st)
    (hv : ∀ (i : Nat) (s : Slot), st.slots[i]? = some (some s) → s.tk.Valid) (now max : Nat)
    (hcap : min (livePairs now st.slots 0).length max ≤ N') (h255 : min (livePairs now st.slots 0).length max < 256) :
    decode (encode (exportList st.slots now max)) = some (exportList st.slots now max) ∧
    (restore (Store.empty N') (encode (exportList st.slots now max)) now).2 = some (exportList st.slots now max).length ∧
    tks (restore (Store.empty N') (encode (exportList st.slots now max)) now).1.slots = exportList st.slots now max := by
  have hlen : (exportList st.slots now max).length = min (livePairs now st.slots 0).length max := by
    rw [exportList_length, export_len]
  have hvalid : ∀ t ∈ exportList st.slots now max, t.Valid := by
    intro t ht
    obtain ⟨_, k, s, hk, rfl⟩ := exportList_mem ht
    exact hv k s hk
  have hdec : decode (encode (exportList st.slots now max)) = some (exportList st.slots now max) :=
    decode_encode (by omega) hvalid
  refine ⟨hdec, ?_⟩
  have hlive : (exportList st.slots now max).filter (fun t => decide (now ≤ t.expiry)) = exportList st.slots now max := by
    apply List.filter_eq_self.mpr
    intro t ht
    simpa using (exportList_mem ht).1
  rw [restore_live _ hdec, hlive]
  obtain ⟨ss, hss, hres⟩ := fold_insert_shape now (exportList st.slots now max) [] 0 N'
    (by simp) (by simp) (exportList_peers (client_one_per_peer h) now max) (by omega)
  refine ⟨rfl, ?_⟩
  have hres' : ((exportList st.slots now max).foldl (fun s t => cInsert s t now) (Store.empty N')).slots =
      ss.map some ++ List.replicate (N' - (exportList st.slots now max).length) none := by
    have := hres
    simpa [Store.empty] using this
  simp only
  rw [hres']
  unfold tks
  rw [List.filterMap_append]
  have h1 := filterMap_some_tk ss
  have h2 : (List.replicate (N' - (exportList st.slots now max).length) (none : Option Slot)).filterMap (fun x => x.map (·.tk)) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro a ha
    cases List.eq_of_mem_replicate ha
    rfl
  rw [h1, h2, hss]
  simp

end Vinc.Tickets

#audit_axioms Vinc.Tickets.restore_malformed
#audit_axioms Vinc.Tickets.restore_live
#audit_axioms Vinc.Tickets.restore_zero
#audit_axioms Vinc.Tickets.export_len
#audit_axioms Vinc.Tickets.export_mem
#audit_axioms Vinc.Tickets.export_oldest_first
#audit_axioms Vinc.Tickets.export_newest
#audit_axioms Vinc.Tickets.exportList_mem
#audit_axioms Vinc.Tickets.exportList_length
#audit_axioms Vinc.Tickets.exportList_peers
#audit_axioms Vinc.Tickets.restore_export
