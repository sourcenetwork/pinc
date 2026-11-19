import Pinc.Axioms

/-!
# The memory a grown buffer pool holds

A model of the grown pool of `pinc-transport/src/stream/pool.rs` (`BufferPool::new_grown`, `alloc_chunk`,
`free_chunk`, `trim`, `reset`, over `Grown::take`, `give`, `trim`, `reset`), and of its one trim caller,
`Streams::settle` in `stream/table.rs`, which trims when the session's last stream ends.

The story: a session takes 16 KiB chunks from its pool and gives them back. A grown pool makes a chunk's memory when
it hands the chunk out, and a chunk that comes back keeps its memory, so a busy session takes the same chunks again
without allocating. When the session goes quiet (its last stream ended) the pool is trimmed: every idle chunk loses
its memory. What must never happen: a grown pool handing out
other chunks than a flat pool would (the stream layer's handles must not depend on how the pool keeps its memory), a
trim touching a chunk in use, or a trimmed pool holding more than the chunks in use, which is what made a
quiet session hold its busiest moment.

The model counts. `Pool` is what a flat pool and a grown pool share: the free list as a stack of chunk indices (the
last one returned on top), the bump cursor and the chunks in use. `Mem` is what only the grown pool has: how many of
the free entries have their memory (`idle`, the top of the stack) and how many have none (`bare`, the bottom). The
Rust trim frees the memory of each idle entry; `trimMem` counts it.
-/

namespace Pinc.PoolGrown

-- What a flat and a grown pool share: the free stack (head = most recently returned), the bump cursor, the chunks in use.
/-- The free list, the bump cursor `fresh` and the count `used`. -/
structure Pool where
  free : List Nat
  fresh : Nat
  used : Nat

-- What only the grown pool has: free entries that hold memory (on top) and that do not (at the bottom).
/-- `idle` free entries hold memory; `bare` do not. -/
structure Mem where
  idle : Nat
  bare : Nat

-- Taking a chunk, the same in both pools: the top of the free stack, or the chunk at the bump cursor.
/-- `alloc_chunk`: the index handed out and the pool after it (the budget check is left out: it is the same for both). -/
def take (p : Pool) : Nat × Pool :=
  match p.free with
  | i :: rest => (i, { p with free := rest, used := p.used + 1 })
  | [] => (p.fresh, { p with fresh := p.fresh + 1, used := p.used + 1 })

-- Giving a chunk back, the same in both pools: it goes on top of the free stack.
/-- `free_chunk`. -/
def give (p : Pool) (i : Nat) : Pool := { p with free := i :: p.free, used := p.used - 1 }

-- The memory side of a take: an idle chunk comes off the top with its memory; otherwise a bare entry or the cursor's
-- chunk gets new memory (counted in neither: it is in use now).
/-- `Grown::take`, its memory counts. -/
def takeMem (p : Pool) (m : Mem) : Mem :=
  match p.free with
  | _ :: _ => if 0 < m.idle then { m with idle := m.idle - 1 } else { m with bare := m.bare - 1 }
  | [] => m

-- The memory side of a give: the chunk comes back idle, with its memory.
/-- `Grown::give`, its memory counts. -/
def giveMem (m : Mem) : Mem := { m with idle := m.idle + 1 }

-- The trim: every idle entry loses its memory and becomes bare.
/-- `Grown::trim`. -/
def trimMem (m : Mem) : Mem := { idle := 0, bare := m.bare + m.idle }

-- The chunks whose memory a grown pool holds: those in use and the idle ones.
/-- `held_chunks`. -/
def held (p : Pool) (m : Mem) : Nat := p.used + m.idle

-- The invariant: idle and bare entries are exactly the free stack.
/-- The pool's invariant. -/
def Inv (p : Pool) (m : Mem) : Prop := m.idle + m.bare = p.free.length

-- A new pool and a reset pool: nothing free, nothing in use, no memory.
/-- `new_grown` and `reset`. -/
def empty : Pool × Mem := (⟨[], 0, 0⟩, ⟨0, 0⟩)

-- The empty pool satisfies the invariant.
/-- A new or reset pool satisfies the invariant. -/
theorem inv_empty : Inv empty.1 empty.2 := by
  simp [Inv, empty]

-- A grown pool's step: the flat pool's take, with the memory counts beside it.
/-- `alloc_chunk` of a grown pool. -/
def grownTake (p : Pool) (m : Mem) : Nat × Pool × Mem := ((take p).1, (take p).2, takeMem p m)

-- The grown pool hands out the very chunk the flat pool does, whatever memory it holds.
/-- The chunk a grown pool hands out depends on the free list and the cursor only, as a flat pool's does. -/
theorem take_indep (p : Pool) (m m' : Mem) : (grownTake p m).1 = (grownTake p m').1 ∧ (grownTake p m).1 = (take p).1 :=
  ⟨rfl, rfl⟩

-- Taking keeps the invariant: one entry leaves the stack and one count goes down with it.
/-- A take keeps the invariant. -/
theorem inv_take (p : Pool) (m : Mem) (h : Inv p m) : Inv (take p).2 (takeMem p m) := by
  simp only [Inv, take, takeMem] at *
  cases hf : p.free with
  | nil => simp only [hf, List.length_nil] at h ⊢; omega
  | cons i rest =>
    simp only [hf, List.length_cons] at h ⊢
    by_cases h0 : 0 < m.idle <;> simp only [h0, ite_true, ite_false] <;> omega

-- Giving keeps the invariant: the entry pushed is idle.
/-- A give keeps the invariant. -/
theorem inv_give (p : Pool) (m : Mem) (i : Nat) (h : Inv p m) : Inv (give p i) (giveMem m) := by
  simp only [Inv, give, giveMem, List.length_cons] at *
  omega

-- Trimming keeps the invariant and leaves the pool (free list, cursor, chunks in use) as it was.
/-- A trim keeps the invariant and touches no chunk in use. -/
theorem inv_trim (p : Pool) (m : Mem) (h : Inv p m) : Inv p (trimMem m) := by
  simp only [Inv, trimMem] at *
  omega

-- A busy session reuses memory: a chunk given back and taken again comes with its memory, nothing is allocated.
/-- Give then take: the bare entries (those without memory) are unchanged, so no chunk was made. -/
theorem give_take_reuses (p : Pool) (m : Mem) (i : Nat) :
    (takeMem (give p i) (giveMem m)).bare = m.bare := by
  simp [takeMem, give, giveMem]

-- The bound the change is for: a trimmed grown pool holds the chunks in use and no other.
/-- After a trim, the memory a pool holds is exactly the chunks it uses. -/
theorem held_after_trim (p : Pool) (m : Mem) : held p (trimMem m) = p.used := by
  simp [held, trimMem]

-- A quiet pool, trimmed, holds nothing, however busy it was.
/-- A trimmed pool with nothing in use holds no chunk. -/
theorem held_quiet (p : Pool) (m : Mem) (hq : p.used = 0) : held p (trimMem m) = 0 := by
  rw [held_after_trim, hq]

-- RED witness: without the trim, a session that gave back 20 chunks and went quiet holds all 20.
/-- The planted bug: a quiet pool that is never trimmed holds its busiest moment (20 chunks, not none). -/
theorem no_trim_breaks_bound : (Nat.repeat giveMem 20 ⟨0, 0⟩).idle ≠ 0 := by
  decide

end Pinc.PoolGrown
