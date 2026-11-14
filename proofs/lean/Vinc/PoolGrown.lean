import Vinc.Axioms

/-!
# The memory a grown buffer pool holds

A model of the grown pool of `vinc-transport/src/stream/pool.rs` (`BufferPool::new_grown`, `alloc_chunk`,
`free_chunk`, `trim`, `reset`, over `Grown::take`, `give`, `trim`, `reset`), and of its one trim caller,
`Streams::settle` in `stream/table.rs`, which trims when the session's last stream ends.

The story: a session takes 16 KiB chunks from its pool and gives them back. A grown pool keeps its chunks in segments
of `k` chunks (chunk `i` lives in segment `i / k`). A segment's memory is made when one of its chunks is handed out,
and a chunk that comes back stays in its segment, so a busy session takes the same chunks again without allocating.
When the session goes quiet (its last stream ended) the pool is trimmed: every segment with no chunk in use loses its
memory, whole. A segment is as large as the system allocator maps on its own (`SEGMENT_CHUNKS`, 2048 chunks, 32 MiB,
on 64-bit Linux with glibc), so freeing it gives its pages back to the system; a freed 16 KiB chunk would stay in the allocator's
heap under the sessions that outlive it (vinc#435). Elsewhere a segment is one chunk, the pool before #435. What must
never happen: a grown pool handing out other chunks than a flat pool would (the stream layer's handles must not depend
on how the pool keeps its memory), a trim taking the memory of a chunk in use, or a trimmed pool keeping a segment no
chunk in use needs, which is what made a quiet session hold its busiest moment.

The model: `Pool` is what a flat pool and a grown pool share: the free list as a stack of chunk indices (the last one
returned on top), the bump cursor and the count of chunks in use. `Mem` is what only the grown pool has: the chunks
handed out and not returned (`out`, which the Rust code counts per segment in `busy`), which segments have their memory
(`live`, the Rust `segs`) and which chunks were handed out since their segment's memory was made (`made`, what the
segment may have committed: the Rust `held_chunks`).
-/

namespace Vinc.PoolGrown

-- What a flat and a grown pool share: the free stack (head = most recently returned), the bump cursor, the chunks in use.
/-- The free list, the bump cursor `fresh` and the count `used`. -/
structure Pool where
  free : List Nat
  fresh : Nat
  used : Nat

-- What only the grown pool has: the chunks out, the segments with memory, the chunks made since their segment was.
/-- `out`: chunks handed out and not returned; `live s`: segment `s` has its memory; `made i`: chunk `i` was handed out
since its segment's memory was made. -/
structure Mem where
  out : List Nat
  live : Nat → Bool
  made : Nat → Bool

-- Taking a chunk, the same in both pools: the top of the free stack, or the chunk at the bump cursor.
/-- `alloc_chunk`: the index handed out and the pool after it (the budget check is left out: it is the same for both). -/
def take (p : Pool) : Nat × Pool :=
  match p.free with
  | i :: rest => (i, { p with free := rest, used := p.used + 1 })
  | [] => (p.fresh, { p with fresh := p.fresh + 1, used := p.used + 1 })

-- Giving a chunk back, the same in both pools: it goes on top of the free stack.
/-- `free_chunk`. -/
def give (p : Pool) (i : Nat) : Pool := { p with free := i :: p.free, used := p.used - 1 }

-- The memory side of a take of chunk `i`: it is out, its segment has memory (made now if it had none), and it is made.
/-- `Grown::take`, its memory, with segments of `k` chunks. -/
def takeMem (k : Nat) (m : Mem) (i : Nat) : Mem :=
  { out := i :: m.out
    live := fun s => if s = i / k then true else m.live s
    made := fun j => if j = i then true else m.made j }

-- The memory side of a give: the chunk is no longer out; its segment keeps its memory.
/-- `Grown::give`, its memory. -/
def giveMem (m : Mem) (i : Nat) : Mem := { m with out := m.out.erase i }

-- Whether segment `s` holds a chunk in use: the Rust `busy[s] > 0`.
/-- Some chunk out lies in segment `s`. -/
def busy (k : Nat) (m : Mem) (s : Nat) : Bool := m.out.any (fun j => j / k == s)

-- The trim: every segment with no chunk out loses its memory, and with it every chunk made in it.
/-- `Grown::trim`. -/
def trimMem (k : Nat) (m : Mem) : Mem :=
  { m with
    live := fun s => m.live s && busy k m s
    made := fun j => m.made j && busy k m (j / k) }

-- The invariant: a chunk out has its memory and is made, a made chunk's segment has its memory, and the chunks out are
-- as many as the pool counts in use.
/-- The pool's invariant. -/
def Inv (k : Nat) (p : Pool) (m : Mem) : Prop :=
  (∀ j, j ∈ m.out → m.live (j / k) = true ∧ m.made j = true) ∧
  (∀ j, m.made j = true → m.live (j / k) = true) ∧
  m.out.length = p.used

-- A new pool and a reset pool: nothing free, nothing in use, no memory.
/-- `new_grown` and `reset`. -/
def empty : Pool × Mem := (⟨[], 0, 0⟩, ⟨[], fun _ => false, fun _ => false⟩)

-- The empty pool satisfies the invariant.
/-- A new or reset pool satisfies the invariant. -/
theorem inv_empty (k : Nat) : Inv k empty.1 empty.2 := by
  simp [Inv, empty]

-- A grown pool's step: the flat pool's take, with the memory beside it.
/-- `alloc_chunk` of a grown pool. -/
def grownTake (k : Nat) (p : Pool) (m : Mem) : Nat × Pool × Mem :=
  ((take p).1, (take p).2, takeMem k m (take p).1)

-- The grown pool hands out the very chunk the flat pool does, whatever memory it holds and whatever its segments.
/-- The chunk a grown pool hands out depends on the free list and the cursor only, as a flat pool's does. -/
theorem take_indep (k k' : Nat) (p : Pool) (m m' : Mem) :
    (grownTake k p m).1 = (grownTake k' p m').1 ∧ (grownTake k p m).1 = (take p).1 :=
  ⟨rfl, rfl⟩

-- Taking counts one more chunk in use, in the flat pool's count.
/-- A take adds one to the count in use. -/
theorem take_used (p : Pool) : (take p).2.used = p.used + 1 := by
  unfold take; cases p.free <;> rfl

-- Taking keeps the invariant: the chunk handed out has its segment's memory and is made.
/-- A take keeps the invariant. -/
theorem inv_take (k : Nat) (p : Pool) (m : Mem) (h : Inv k p m) :
    Inv k (take p).2 (takeMem k m (take p).1) := by
  obtain ⟨hout, hmade, hlen⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    simp only [takeMem, List.mem_cons] at hj ⊢
    rcases hj with rfl | hj
    · simp
    · obtain ⟨h1, h2⟩ := hout j hj
      constructor
      · by_cases e : j / k = (take p).1 / k <;> simp [e, h1]
      · by_cases e : j = (take p).1 <;> simp [e, h2]
  · intro j hj
    simp only [takeMem] at hj ⊢
    by_cases e : j = (take p).1
    · simp [e]
    · simp only [e, ite_false] at hj
      by_cases e2 : j / k = (take p).1 / k <;> simp [e2, hmade j hj]
  · simp [takeMem, take_used, hlen]

-- Giving a chunk that is out keeps the invariant: the made marks and the memory stay.
/-- A give of a chunk in use keeps the invariant. -/
theorem inv_give (k : Nat) (p : Pool) (m : Mem) (i : Nat) (h : Inv k p m) (hi : i ∈ m.out) :
    Inv k (give p i) (giveMem m i) := by
  obtain ⟨hout, hmade, hlen⟩ := h
  refine ⟨fun j hj => hout j (List.mem_of_mem_erase hj), hmade, ?_⟩
  simp [giveMem, give, List.length_erase_of_mem hi, hlen]

-- Trimming keeps the invariant: a segment with a chunk out keeps its memory and its made chunks.
/-- A trim keeps the invariant and leaves the pool (free list, cursor, chunks in use) as it was. -/
theorem inv_trim (k : Nat) (p : Pool) (m : Mem) (h : Inv k p m) : Inv k p (trimMem k m) := by
  obtain ⟨hout, hmade, hlen⟩ := h
  have hb : ∀ j, j ∈ m.out → busy k m (j / k) = true := fun j hj => by
    simp only [busy, List.any_eq_true, beq_iff_eq]; exact ⟨j, hj, rfl⟩
  refine ⟨?_, ?_, hlen⟩
  · intro j hj
    obtain ⟨h1, h2⟩ := hout j hj
    simp [trimMem, h1, h2, hb j hj]
  · intro j hj
    simp only [trimMem, Bool.and_eq_true] at hj ⊢
    exact ⟨hmade j hj.1, hj.2⟩

-- The trim touches no chunk in use: its segment keeps its memory and the chunk stays made.
/-- A chunk out keeps its memory through a trim. -/
theorem trim_keeps_in_use (k : Nat) (p : Pool) (m : Mem) (h : Inv k p m) (j : Nat) (hj : j ∈ m.out) :
    (trimMem k m).live (j / k) = true ∧ (trimMem k m).made j = true :=
  (inv_trim k p m h).1 j hj

-- A busy session reuses memory: a chunk given back and taken again finds its segment's memory, nothing is allocated.
/-- Give then take of a chunk in use: the segments with memory are the same as before. -/
theorem give_take_reuses (k : Nat) (p : Pool) (m : Mem) (h : Inv k p m) (i : Nat) (hi : i ∈ m.out) :
    (takeMem k (giveMem m i) i).live = m.live := by
  funext s
  have hl := (h.1 i hi).1
  simp only [takeMem, giveMem]
  by_cases e : s = i / k
  · simp [e, hl]
  · simp [e]

-- The bound the change is for: after a trim, every segment that keeps its memory has a chunk in use.
/-- After a trim, a segment holds memory only if a chunk in use lies in it. -/
theorem held_after_trim (k : Nat) (m : Mem) (s : Nat) (hs : (trimMem k m).live s = true) :
    ∃ j, j ∈ m.out ∧ j / k = s := by
  simp only [trimMem, Bool.and_eq_true, busy, List.any_eq_true, beq_iff_eq] at hs
  exact hs.2

-- A quiet pool, trimmed, holds nothing, however busy it was: no segment has memory and no chunk is made.
/-- A trimmed pool with nothing in use holds no segment and no chunk. -/
theorem held_quiet (k : Nat) (m : Mem) (hq : m.out = []) (s : Nat) :
    (trimMem k m).live s = false ∧ (trimMem k m).made s = false := by
  simp [trimMem, busy, hq]

-- With segments of one chunk (wasm, 32-bit, bare metal), a trimmed pool holds exactly the chunks in use: the pool
-- before #435.
/-- With one chunk per segment, after a trim chunk `s`'s memory is held exactly when it is in use (given the
invariant). -/
theorem held_after_trim_one (p : Pool) (m : Mem) (h : Inv 1 p m) (s : Nat) :
    (trimMem 1 m).live s = true ↔ s ∈ m.out := by
  constructor
  · intro hs
    obtain ⟨j, hj, e⟩ := held_after_trim 1 m s hs
    simp only [Nat.div_one] at e
    exact e ▸ hj
  · intro hs
    have := (trim_keeps_in_use 1 p m h s hs).1
    simpa only [Nat.div_one] using this

-- The quiet pool of a whole burst: twenty chunks taken and given back.
/-- Twenty takes of chunks 0 to 19, then their twenty gives, from a new pool, with segments of `k` chunks. -/
def burst (k : Nat) : Mem :=
  (List.range 20).foldl giveMem ((List.range 20).foldl (takeMem k) empty.2)

-- RED witness: without the trim, a session that gave back its 20 chunks and went quiet still holds its segment.
/-- The planted bug: a quiet pool that is never trimmed holds its busiest moment (its segment, not nothing). -/
theorem no_trim_breaks_bound : (burst 2048).out = [] ∧ (burst 2048).live 0 = true := by
  decide

-- And the trim releases it.
/-- The same quiet pool, trimmed, holds no segment. -/
theorem trim_releases_burst : (trimMem 2048 (burst 2048)).live 0 = false := by
  decide

/-!
## The spare segments of a thread

A segment a trim frees goes to the thread's spare segments (`Segments` in `pool.rs`, shared by the grown pools of the
endpoints of one thread) when its pool handed out at most `w` of its chunks (`SPARE_WRITTEN`, 16) and the cache holds
fewer than `cap` (`SPARE_SEGMENTS`, 4); every other freed segment goes back to the system. A pool that needs a segment
takes a spare one first. So a session that goes quiet after every request reuses one segment without asking the
system for it, and what the spares keep resident is bounded however large a burst was. The model keeps, per spare
segment, how many of its chunks were handed out: the most of its pages it can have written.
-/

-- Offering a freed segment that had `written` chunks handed out: kept if written little and there is room.
/-- `Segments::put`. -/
def put (cap w : Nat) (sp : List Nat) (written : Nat) : List Nat :=
  if written ≤ w ∧ sp.length < cap then written :: sp else sp

-- Taking a spare segment: the cache gives one up, if it has any.
/-- `Segments::take`. -/
def takeSpare (sp : List Nat) : List Nat := sp.tail

-- The cache's bound: at most `cap` segments, each written at most `w` chunks.
/-- The spare segments' invariant. -/
def SpareInv (cap w : Nat) (sp : List Nat) : Prop := sp.length ≤ cap ∧ ∀ x, x ∈ sp → x ≤ w

-- An offer keeps the bound, whatever was offered.
/-- A put keeps the spare segments' invariant. -/
theorem put_inv (cap w : Nat) (sp : List Nat) (written : Nat) (h : SpareInv cap w sp) :
    SpareInv cap w (put cap w sp written) := by
  obtain ⟨hl, hx⟩ := h
  unfold put
  by_cases c : written ≤ w ∧ sp.length < cap
  · simp only [c, and_self, ite_true, SpareInv, List.length_cons, List.mem_cons]
    refine ⟨by omega, ?_⟩
    intro x hx'
    rcases hx' with rfl | hx'
    · exact c.1
    · exact hx x hx'
  · simp only [c, ite_false]
    exact ⟨hl, hx⟩

-- A take keeps the bound.
/-- Taking a spare keeps the invariant. -/
theorem take_inv (cap w : Nat) (sp : List Nat) (h : SpareInv cap w sp) : SpareInv cap w (takeSpare sp) := by
  obtain ⟨hl, hx⟩ := h
  refine ⟨?_, fun x hx' => hx x (List.mem_of_mem_tail hx')⟩
  simp only [takeSpare, List.length_tail]
  omega

-- The sum of a list of counts each at most `w` is at most its length times `w`.
/-- A helper: a bounded list's sum. -/
theorem sum_le (w : Nat) : ∀ sp : List Nat, (∀ x, x ∈ sp → x ≤ w) → sp.sum ≤ sp.length * w
  | [], _ => by simp
  | x :: rest, h => by
    have hx := h x (List.mem_cons_self ..)
    have hr := sum_le w rest (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

-- What the spares keep resident: at most `cap * w` chunks, however large the burst whose segments were offered.
/-- The chunks the spare segments may have written are at most `cap * w`. -/
theorem spare_resident (cap w : Nat) (sp : List Nat) (h : SpareInv cap w sp) : sp.sum ≤ cap * w := by
  have := sum_le w sp h.2
  have := Nat.mul_le_mul_right w h.1
  omega

-- A burst: every one of 12 quiet sessions offers a segment it wrote 8 chunks of, into the real bounds (4 and 16).
/-- Twelve offers of segments written 8 chunks each. -/
def burstOffers (cap w : Nat) : List Nat := (List.replicate 12 8).foldl (put cap w) []

-- The bounds hold after the burst: 4 segments kept, 32 chunks.
/-- The real bounds keep 4 of the 12 segments. -/
theorem burst_kept : burstOffers 4 16 = [8, 8, 8, 8] := by
  decide

-- RED witness: without the written check, a segment a session wrote 2048 chunks of (32 MiB) is kept spare.
/-- The planted bug: a cache that keeps whatever is offered holds a burst's whole segment. -/
theorem no_written_check_breaks_bound : put 4 2048 [] 2048 = [2048] ∧ ¬ (2048 ≤ 16) := by
  decide

-- With the check, the same segment goes back to the system.
/-- The real cache refuses it. -/
theorem written_check_refuses : put 4 16 [] 2048 = [] := by
  decide

end Vinc.PoolGrown
