import Pinc.Axioms

/-!
# The endpoint's chunk store

A model of `pinc-transport/src/stream/store.rs` (`ChunkStore::new`, `grow`, `shrink`, `release`, `wait`, `leave`,
`serve`, `take`, `give`, `new_mark`), of the pool over it in `stream/pool.rs` (`BufferPool::make_room`, `trim`,
`alloc_chunk`, `free_chunk`), and of the endpoint's admission and release of a slot (`Endpoint::alloc_slot`,
`free_slot` in `pinc-core/src/endpoint.rs`).

The story: an endpoint has one store of `B` chunks, made when the endpoint is built, with every slot's floor `F` set
aside at once; the rest is the burst room. A slot reserves above its floor from the burst room and takes chunks only
inside its reservation: a reservation grows as far as the burst room has room and shrinks back when a stream ends, and
a session that ends gives back every chunk and everything above the floor. A slot whose grant found the burst room
short waits in a queue, oldest first, and room given back goes to the oldest waiter once it covers its whole want.
Every chunk remembers the mark of the session that held it last; a session handed a chunk another session wrote gets it
zeroed. What must never happen: the reservations passing the store, a session holding more than it reserved, a slot
below its floor (so no peer is refused for want of one), a slot in the queue twice, a younger waiter served before an
older one, a chunk handed to a second session while one holds it, or a session reading bytes another session wrote.

The model has three parts. The ledger counts: the burst room, and each slot's reservation and the chunks it holds. The
queue is a list of slots. The chunks are a list: who holds each one, the mark of its last holder, and whose bytes it
carries (0 for zeros). The code's choice of which free chunk to hand out (last in, first out) is left open: every
theorem holds for any free chunk.
-/

namespace Pinc.ChunkStore

-- A function from sessions to numbers with one session's value replaced.
/-- `f` with `s` mapped to `v`. -/
def upd (f : Nat → Nat) (s v : Nat) : Nat → Nat := fun x => if x = s then v else f x

-- The sum of a session function over a list of sessions.
/-- `Σ s ∈ l, f s`. -/
def total (l : List Nat) (f : Nat → Nat) : Nat := (l.map f).sum

-- Replacing the value of a session that is not in the list does not change the sum.
/-- `upd` outside the list leaves the total alone. -/
theorem total_upd_out (l : List Nat) (f : Nat → Nat) (s v : Nat) (h : s ∉ l) :
    total l (upd f s v) = total l f := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.mem_cons, not_or] at h
    have ha : a ≠ s := fun e => h.1 e.symm
    simp only [total, List.map_cons, List.sum_cons, upd, ha, ite_false] at ih ⊢
    rw [ih h.2]

-- Replacing the value of a session that is in the list once moves the sum by the difference.
/-- `upd` inside a list without duplicates swaps one term of the total. -/
theorem total_upd (l : List Nat) (hl : l.Nodup) (f : Nat → Nat) (s v : Nat) (h : s ∈ l) :
    total l (upd f s v) + f s = total l f + v := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    have hn := List.nodup_cons.mp hl
    by_cases ha : a = s
    · subst ha
      have := total_upd_out t f a v hn.1
      simp only [total, List.map_cons, List.sum_cons, upd, ite_true] at this ⊢
      omega
    · have ht : s ∈ t := by
        rcases List.mem_cons.mp h with e | e
        · exact absurd e.symm ha
        · exact e
      have := ih hn.2 ht
      simp only [total, List.map_cons, List.sum_cons, upd, ha, ite_false] at this ⊢
      omega

/-! ## The ledger -/

-- The ledger: the store's size, the floor, the burst room no slot reserved, the slots, and per slot its reservation
-- (the floor included) and the chunks it holds.
/-- The counts of `ChunkStore` (`stats.chunks`, `floor`, `burst_left`, `reserved(slot)`) and each pool's `used`. -/
structure Ledger where
  B : Nat
  F : Nat
  unres : Nat
  sessions : List Nat
  res : Nat → Nat
  used : Nat → Nat

-- The invariant: every chunk is either in the burst room or in one slot's reservation, no slot holds more than it
-- reserved, and every slot keeps its floor whatever its session does.
/-- Conservation, the reservation bound, and the floors set aside. -/
def Inv (L : Ledger) : Prop :=
  L.sessions.Nodup ∧ L.unres + total L.sessions L.res = L.B ∧ (∀ s, L.used s ≤ L.res s) ∧
    ∀ s ∈ L.sessions, L.F ≤ L.res s

-- The total of a constant is the constant times the length.
/-- `Σ s ∈ l, c = c · |l|`. -/
theorem total_const (l : List Nat) (c : Nat) : total l (fun _ => c) = c * l.length := by
  induction l with
  | nil => simp [total]
  | cons a t ih => simp only [total, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; rw [ih, Nat.mul_succ]; omega

-- A new endpoint: every slot's floor set aside, the rest is burst room, nothing held.
/-- `ChunkStore::new`: the floors of all the slots reserved at once. -/
def empty (B F : Nat) (ss : List Nat) : Ledger := ⟨B, F, B - F * ss.length, ss, fun _ => F, fun _ => 0⟩

-- A new endpoint keeps the invariant when the store holds every floor (the builder's check `B ≥ K × F`).
/-- The store starts with every floor set aside. -/
theorem inv_empty (B F : Nat) (ss : List Nat) (h : ss.Nodup) (hB : F * ss.length ≤ B) : Inv (empty B F ss) := by
  refine ⟨h, ?_, fun _ => Nat.zero_le _, fun _ _ => Nat.le_refl F⟩
  simp only [empty, total_const]; omega

-- No session is ever refused for want of a floor: a slot holds its floor from the start, whatever the others did.
/-- `Endpoint::alloc_slot` never meets a store without the floor (`store_refused` stays 0). -/
theorem admit_never_refused (L : Ledger) (h : Inv L) (s : Nat) (hs : s ∈ L.sessions) : L.F ≤ L.res s :=
  h.2.2.2 s hs

-- Without the floors set aside (each taken at admission from the same room bursts draw from), one slot's burst can
-- take the whole store: slot 1 reserved both chunks, slot 2 reserved none, and the next peer of slot 2 is refused.
/-- RED witness: floors taken from the burst room let bursts lock new peers out. -/
theorem floor_pool_refuses :
    let L : Ledger := ⟨2, 1, 0, [1, 2], fun s => if s = 1 then 2 else 0, fun _ => 0⟩
    L.unres + total L.sessions L.res = L.B ∧ L.unres < L.F - L.res 2 := by
  decide

-- Reserving `n` more chunks for slot `s`, when the burst room has them.
/-- `ChunkStore::grow` and `serve` (`add_above`), when `n ≤ burst_left`. -/
def reserve (L : Ledger) (s n : Nat) : Ledger :=
  { L with unres := L.unres - n, res := upd L.res s (L.res s + n) }

-- Giving back `n` of `s`'s reserved chunks, as long as `s` keeps its floor and what it holds.
/-- `ChunkStore::shrink` and `release`. -/
def unreserve (L : Ledger) (s n : Nat) : Ledger :=
  { L with unres := L.unres + n, res := upd L.res s (L.res s - n) }

-- Reserving keeps the invariant: what leaves the burst room joins `s`'s reservation.
/-- A reservation the burst room has room for conserves the store. -/
theorem inv_reserve (L : Ledger) (s n : Nat) (h : Inv L) (hs : s ∈ L.sessions) (hn : n ≤ L.unres) :
    Inv (reserve L s n) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have := total_upd L.sessions h0 L.res s (L.res s + n) hs
  refine ⟨h0, ?_, fun t => ?_, fun t ht => ?_⟩
  · simp only [reserve]; omega
  · simp only [reserve, upd]
    split
    · rename_i e; subst e; have := h2 t; omega
    · exact h2 t
  · simp only [reserve, upd]
    split
    · rename_i e; subst e; have := h3 t ht; omega
    · exact h3 t ht

-- Giving back keeps the invariant: what leaves `s` joins the burst room, and `s` keeps its floor and what it holds.
/-- Shrinking a reservation to no less than the floor and what is held conserves the store. -/
theorem inv_unreserve (L : Ledger) (s n : Nat) (h : Inv L) (hs : s ∈ L.sessions)
    (hn : L.used s + n ≤ L.res s) (hf : L.F + n ≤ L.res s) : Inv (unreserve L s n) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have := total_upd L.sessions h0 L.res s (L.res s - n) hs
  refine ⟨h0, ?_, fun t => ?_, fun t ht => ?_⟩
  · simp only [unreserve]; omega
  · simp only [unreserve, upd]
    split
    · rename_i e; subst e; omega
    · exact h2 t
  · simp only [unreserve, upd]
    split
    · rename_i e; subst e; omega
    · exact h3 t ht

-- Growing toward `want` chunks (`make_room`): as many as the burst room has, never more.
/-- `ChunkStore::grow`. -/
def grow (L : Ledger) (s want : Nat) : Ledger := reserve L s (min (want - L.res s) L.unres)

-- Growing keeps the invariant whatever is asked.
/-- `make_room` never reserves what the burst room does not have. -/
theorem inv_grow (L : Ledger) (s want : Nat) (h : Inv L) (hs : s ∈ L.sessions) : Inv (grow L s want) :=
  inv_reserve L s _ h hs (Nat.min_le_right _ _)

-- Taking a chunk: only inside the reservation (`alloc_chunk` returns `PoolExhausted` otherwise).
/-- `alloc_chunk` over a store: `some` with one more chunk held, `none` when the reservation is full. -/
def take (L : Ledger) (s : Nat) : Option Ledger :=
  if L.used s < L.res s then some { L with used := upd L.used s (L.used s + 1) } else none

-- Taking keeps the invariant: the reservation bound is the guard.
/-- A take stays inside the reservation. -/
theorem inv_take (L L' : Ledger) (s : Nat) (h : Inv L) (ht : take L s = some L') : Inv L' := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [take] at ht
  split at ht
  · cases ht
    refine ⟨h0, h1, fun t => ?_, h3⟩
    simp only [upd]; have := h2 t; split <;> simp_all <;> omega
  · cases ht

-- Giving a chunk back.
/-- `free_chunk` over a store. -/
def give (L : Ledger) (s : Nat) : Ledger := { L with used := upd L.used s (L.used s - 1) }

-- Giving back keeps the invariant.
/-- A give lowers what is held. -/
theorem inv_give (L : Ledger) (s : Nat) (h : Inv L) : Inv (give L s) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨h0, h1, fun t => ?_, h3⟩
  simp only [give, upd]
  split
  · rename_i e; subst e; have := h2 t; omega
  · exact h2 t

-- The trim at a stream's end: down to the floor, or to what is held and still owed when that is more.
/-- `ChunkStore::shrink` from `BufferPool::trim(granted_unreceived)`. -/
def trim (L : Ledger) (s owed : Nat) : Ledger :=
  unreserve L s (L.res s - max L.F (L.used s + owed))

-- Trimming keeps the invariant and never cuts below the floor or what is held and owed.
/-- A trim keeps the floor and the windows granted. -/
theorem trim_keeps (L : Ledger) (s owed : Nat) (h : Inv L) (hs : s ∈ L.sessions) :
    Inv (trim L s owed) ∧ min (L.res s) (max L.F (L.used s + owed)) ≤ (trim L s owed).res s := by
  have hb := h.2.2.1 s
  have hf := h.2.2.2 s hs
  refine ⟨inv_unreserve L s _ h hs (by omega) (by omega), ?_⟩
  simp only [trim, unreserve, upd, ite_true]; omega

-- Releasing a session that ended: everything it held goes back, then its reservation above the floor.
/-- `ChunkStore::release` from `free_slot`. -/
def release (L : Ledger) (s : Nat) : Ledger :=
  unreserve { L with used := upd L.used s 0 } s (L.res s - L.F)

-- Releasing keeps the invariant and leaves the slot its floor and nothing held.
/-- A released slot holds nothing and keeps only its floor; the burst room gets the rest back. -/
theorem release_all (L : Ledger) (s : Nat) (h : Inv L) (hs : s ∈ L.sessions) :
    Inv (release L s) ∧ (release L s).res s = L.F ∧ (release L s).used s = 0 ∧
      (release L s).unres = L.unres + (L.res s - L.F) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hf := h3 s hs
  have hi : Inv { L with used := upd L.used s 0 } := by
    refine ⟨h0, h1, fun t => ?_, h3⟩
    simp only [upd]; have := h2 t; split <;> omega
  refine ⟨inv_unreserve _ s _ hi hs (by simp [upd]) (by simp; omega), ?_, ?_, ?_⟩ <;>
    simp [release, unreserve, upd] <;> omega

/-! ## The waiting queue -/

-- The queue of slots whose grant found the burst room short, oldest first (`ChunkStore::wait`, `leave`, `serve`).

-- A slot joins at the back, once: one already waiting keeps its place.
/-- `ChunkStore::wait` for a slot short of room. -/
def wait (q : List Nat) (s : Nat) : List Nat := if s ∈ q then q else q ++ [s]

-- A slot leaves wherever it is.
/-- `ChunkStore::leave`, from a grant that went through and from `release`. -/
def leave (q : List Nat) (s : Nat) : List Nat := q.filter (· ≠ s)

-- No slot is ever in the queue twice.
/-- Joining keeps the queue free of duplicates. -/
theorem wait_nodup (q : List Nat) (s : Nat) (h : q.Nodup) : (wait q s).Nodup := by
  unfold wait
  split
  · exact h
  · rename_i hs
    exact List.nodup_append.mpr ⟨h, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun a ha b hb e => hs (by simp at hb; subst hb; subst e; exact ha)⟩

/-- Leaving keeps the queue free of duplicates, and the slot is out. -/
theorem leave_nodup (q : List Nat) (s : Nat) (h : q.Nodup) : (leave q s).Nodup ∧ s ∉ leave q s := by
  refine ⟨h.filter _, by simp [leave]⟩

-- Room given back goes to the oldest waiter, and only when it covers the waiter's whole want: it is reserved for it
-- at once and the waiter leaves the queue. `want s` is the reservation slot `s` waits for.
/-- `ChunkStore::serve`, one waiter: `some` when the burst room covers the head's want. -/
def serveOne (L : Ledger) (want : Nat → Nat) : List Nat → Option (Ledger × List Nat)
  | [] => none
  | h :: t => if want h - L.res h ≤ L.unres then some (reserve L h (want h - L.res h), t) else none

-- Serving keeps the invariant, serves the oldest waiter first, and leaves it holding its whole want.
/-- The head is served first, its want reserved, and the store conserved. -/
theorem serve_fifo (L L' : Ledger) (want : Nat → Nat) (h q : List Nat) (hd : Nat) (hi : Inv L)
    (hq : hd ∈ L.sessions) (hs : serveOne L want (hd :: h) = some (L', q)) :
    Inv L' ∧ q = h ∧ want hd ≤ L'.res hd := by
  simp only [serveOne] at hs
  split at hs
  · cases hs
    refine ⟨inv_reserve L hd _ hi hq (by assumption), rfl, ?_⟩
    simp only [reserve, upd, ite_true]; omega
  · cases hs

-- A waiter is served only once the room covers it: a younger waiter with a smaller want does not pass it.
/-- `serve` stops at a head the room does not cover. -/
theorem serve_waits_in_order (L : Ledger) (want : Nat → Nat) (hd : Nat) (t : List Nat)
    (h : L.unres < want hd - L.res hd) : serveOne L want (hd :: t) = none := by
  simp only [serveOne]; split <;> simp_all <;> omega

/-! ## The chunks -/

-- One chunk: who holds it (by the holder's mark), the mark of its last holder (0: never handed out), and whose bytes
-- it carries (0: zeros, as the system hands untouched memory out; otherwise the mark of the session that wrote them).
/-- A chunk of the store and its `Kept::mark`. -/
structure Chunk where
  holder : Option Nat
  last : Nat
  bytes : Nat

-- A chunk is clean when its bytes are zeros or its last holder's, and a held chunk's last holder is its holder.
/-- What every chunk of the store satisfies. -/
def Clean (c : Chunk) : Prop := (c.bytes = 0 ∨ c.bytes = c.last) ∧ ∀ m, c.holder = some m → c.last = m

-- Handing a chunk to the session marked `m`: zeroed when its last holder was another session.
/-- `ChunkStore::take`: `fill(0)` unless the mark is the taker's or the chunk was never handed out. -/
def hand (m : Nat) (c : Chunk) : Chunk :=
  { holder := some m, last := m, bytes := if c.last = m ∨ c.last = 0 then c.bytes else 0 }

-- The session marked `m` writes into a chunk it holds.
/-- A write into the chunk's memory. -/
def write (m : Nat) (c : Chunk) : Chunk := if c.holder = some m then { c with bytes := m } else c

-- A chunk goes back to the store, its mark kept.
/-- `ChunkStore::give`. -/
def back (c : Chunk) : Chunk := { c with holder := none }

-- A session handed a clean chunk sees zeros or its own bytes, never another session's.
/-- The zero fill on a foreign hand-out: no session reads another's bytes. -/
theorem hand_sees (m : Nat) (c : Chunk) (h : Clean c) : (hand m c).bytes = 0 ∨ (hand m c).bytes = m := by
  obtain ⟨hb, -⟩ := h
  simp only [hand]
  by_cases hl : c.last = m ∨ c.last = 0
  · simp only [hl, ite_true]
    rcases hl with e | e <;> rcases hb with b | b <;> simp_all
  · simp [hl]

-- Without the fill a session can see another's bytes: a chunk the session marked 1 wrote, handed to the session
-- marked 2, still carries 1.
/-- RED witness: handing out without the zero fill leaks a foreign session's bytes. -/
theorem no_fill_leaks :
    let c : Chunk := ⟨none, 1, 1⟩
    let unfilled : Chunk := { c with holder := some 2, last := 2 }
    Clean c ∧ unfilled.bytes ≠ 0 ∧ unfilled.bytes ≠ 2 := by
  refine ⟨⟨Or.inr rfl, fun m h => by cases h⟩, by decide, by decide⟩

-- Handing out, writing and giving back keep a chunk clean.
/-- Every step keeps a chunk clean. -/
theorem clean_hand (m : Nat) (c : Chunk) (h : Clean c) : Clean (hand m c) := by
  refine ⟨?_, fun k hk => ?_⟩
  · rcases hand_sees m c h with e | e
    · exact Or.inl e
    · exact Or.inr (by simp only [hand]; exact e)
  · simp only [hand, Option.some.injEq] at hk ⊢; exact hk

/-- Writing keeps a chunk clean. -/
theorem clean_write (m : Nat) (c : Chunk) (h : Clean c) : Clean (write m c) := by
  unfold write
  split
  · rename_i hh
    exact ⟨Or.inr (h.2 m hh).symm, fun k hk => h.2 k (by simpa using hk)⟩
  · exact h

/-- Giving back keeps a chunk clean. -/
theorem clean_back (c : Chunk) (h : Clean c) : Clean (back c) := ⟨h.1, fun _ hk => by cases hk⟩

-- Handing out chunk `i` of the store, which no session holds, to the session marked `m`.
/-- The store's `take`, for whichever free chunk the free list gives. -/
def handAt (cs : List Chunk) (i m : Nat) : List Chunk := cs.set i (hand m (cs.getD i ⟨none, 0, 0⟩))

-- A chunk is handed out only while no session holds it (it comes off the free list), so no chunk is ever held by two
-- sessions: every chunk a session held before the hand-out, that session still holds after it.
/-- No chunk in two sessions: a hand-out of a free chunk takes nothing from any holder. -/
theorem handAt_exclusive (cs : List Chunk) (i m m' : Nat) (hfree : (cs.getD i ⟨none, 0, 0⟩).holder = none)
    (j : Nat) :
    (cs.getD j ⟨none, 0, 0⟩).holder = some m' → ((handAt cs i m).getD j ⟨none, 0, 0⟩).holder = some m' := by
  intro hj
  by_cases hij : i = j
  · subst hij; rw [hfree] at hj; cases hj
  · simp only [handAt, List.getD_eq_getElem?_getD, List.getElem?_set, hij, ite_false] at hj ⊢
    exact hj

-- Without the guard a held chunk is taken from its holder: chunk 0, held by the session marked 1, handed to the
-- session marked 2.
/-- RED witness: handing out a chunk that is not free takes it from its holder. -/
theorem held_handout_steals :
    let cs : List Chunk := [⟨some 1, 1, 1⟩]
    (cs.getD 0 ⟨none, 0, 0⟩).holder = some 1 ∧ ((handAt cs 0 2).getD 0 ⟨none, 0, 0⟩).holder ≠ some 1 := by
  decide

-- A store of clean chunks stays clean when a free chunk is handed out.
/-- Handing out keeps every chunk of the store clean. -/
theorem handAt_clean (cs : List Chunk) (i m : Nat) (h : ∀ c ∈ cs, Clean c) (hi : i < cs.length) :
    ∀ c ∈ handAt cs i m, Clean c := by
  intro c hc
  simp only [handAt] at hc
  rcases List.mem_or_eq_of_mem_set hc with e | e
  · exact h c e
  · subst e
    apply clean_hand
    apply h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi

-- An untouched store is clean: every chunk is zeros and held by none.
/-- `ChunkStore::new`: zeroed memory, marks 0. -/
theorem fresh_clean : Clean ⟨none, 0, 0⟩ := ⟨Or.inl rfl, fun _ h => by cases h⟩

-- A session that ended takes a new mark (`Share::release`, `new_mark`) greater than every mark a chunk carries, so
-- the next session of its slot is foreign to everything the last one wrote: handed one of those chunks, it sees zeros.
/-- After a release the next session of the slot sees none of the last one's bytes. -/
theorem new_mark_sees_zero (m : Nat) (c : Chunk) (h : Clean c) (hm : c.last < m) (hb : c.bytes ≠ 0) :
    (hand m c).bytes = 0 := by
  have hl : ¬ (c.last = m ∨ c.last = 0) := by
    rintro (e | e)
    · omega
    · rcases h.1 with b | b
      · exact hb b
      · exact hb (b.trans e)
  simp only [hand, hl, ite_false]

#audit_axioms inv_empty
#audit_axioms admit_never_refused
#audit_axioms floor_pool_refuses
#audit_axioms inv_reserve
#audit_axioms inv_unreserve
#audit_axioms inv_take
#audit_axioms trim_keeps
#audit_axioms release_all
#audit_axioms wait_nodup
#audit_axioms leave_nodup
#audit_axioms serve_fifo
#audit_axioms serve_waits_in_order
#audit_axioms hand_sees
#audit_axioms handAt_exclusive
#audit_axioms handAt_clean
#audit_axioms new_mark_sees_zero

end Pinc.ChunkStore
