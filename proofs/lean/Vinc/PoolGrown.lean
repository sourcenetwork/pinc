import Vinc.Axioms

/-!
# The memory a grown buffer pool holds

A model of the grown pool of `vinc-transport/src/stream/pool.rs` (`BufferPool::new_grown`, `alloc_chunk`,
`free_chunk`, `trim`, `reset`, over `Grown::take`, `give`, `trim`, `reset`, `locate` in `stream/pool/grown.rs`), and of
its one trim caller, `Streams::settle` in `stream/table.rs`, which trims when the session's last stream ends.

The story: a session takes 16 KiB chunks from its pool and gives them back. A grown pool keeps its chunks in segments:
each of its first `own` chunks is a segment of its own (`OWN_CHUNKS`, 1: what a session holds at once to shake hands
and move a first request and reply), and the others lie in segments of `k` chunks (`layout`, the Rust `Grown::locate`).
A segment's memory is made when one of its chunks is handed out, and a chunk that comes back stays in its segment, so a
busy session takes the same chunks again without allocating. When the session goes quiet (its last stream ended) the
pool is trimmed: every segment with no chunk in use loses its memory, whole. A segment past the first chunks is as
large as the system allocator maps on its own (`SEGMENT_CHUNKS`, 2048 chunks, 32 MiB, on 64-bit Linux with glibc), so
freeing it gives its pages back to the system; a freed 16 KiB chunk would stay in the allocator's heap under the
sessions that outlive it (vinc#435). Elsewhere a segment is one chunk, the pool before #435. What must never happen: a
grown pool handing out other chunks than a flat pool would (the stream layer's handles must not depend on how the pool
keeps its memory), a trim taking the memory of a chunk in use, a trimmed pool keeping a segment no chunk in use needs,
which is what made a quiet session hold its busiest moment, or a session that only shakes hands mapping a segment.

The model: `Pool` is what a flat pool and a grown pool share: the free list as a stack of chunk indices (the last one
returned on top), the bump cursor and the count of chunks in use. `Mem` is what only the grown pool has: the chunks
handed out and not returned (`out`, which the Rust code counts per segment in `busy`), which segments have their memory
(`live`, the Rust `segs`) and which chunks were handed out since their segment's memory was made (`made`, what the
segment may have committed: the Rust `place`, nonzero, and `held_chunks`). The theorems about the memory hold for any
way `g` of placing chunks in segments; `layout` is the code's.
-/

namespace Vinc.PoolGrown

-- Where the code puts chunk `i`: one of the first `own` chunks in a segment of its own, numbered as the chunk; the
-- others in segments of `k` chunks after them.
/-- `Grown::locate`, the segment of chunk `i`. -/
def layout (own k i : Nat) : Nat := if i < own then i else own + (i - own) / k

-- Each of the first chunks is the only chunk of its segment: whatever lies in that segment is that chunk.
/-- A chunk below `own` has a segment no other chunk shares. -/
theorem own_alone (own k i j : Nat) (hi : i < own) (e : layout own k j = layout own k i) : j = i := by
  unfold layout at e
  simp only [hi, ite_true] at e
  split at e
  · exact e
  · generalize (j - own) / k = x at e
    omega

-- And its segment is numbered as the chunk, below every segment of `k` chunks.
/-- The segment of a chunk below `own` is the chunk's own number. -/
theorem own_segment (own k i : Nat) (hi : i < own) : layout own k i = i := by
  simp [layout, hi]

-- RED witness: with no chunk of its own (`own = 0`), the one chunk a hello holds lies in the segment that a session's
-- later chunks share, so a session that only shakes hands maps a whole segment.
/-- The planted bug: no chunks of their own. -/
theorem no_own_shares : layout 0 2048 0 = layout 0 2048 1 := by
  decide

-- With segments of one chunk, every chunk is its own segment: the pool before #435.
/-- `layout own 1` is the identity. -/
theorem layout_one (own j : Nat) : layout own 1 j = j := by
  unfold layout
  split
  · rfl
  · rw [Nat.div_one]; omega

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
/-- `Grown::take`, its memory, with chunk `i` in segment `g i`. -/
def takeMem (g : Nat → Nat) (m : Mem) (i : Nat) : Mem :=
  { out := i :: m.out
    live := fun s => if s = g i then true else m.live s
    made := fun j => if j = i then true else m.made j }

-- The memory side of a give: the chunk is no longer out; its segment keeps its memory.
/-- `Grown::give`, its memory. -/
def giveMem (m : Mem) (i : Nat) : Mem := { m with out := m.out.erase i }

-- Whether segment `s` holds a chunk in use: the Rust `busy[s] > 0`.
/-- Some chunk out lies in segment `s`. -/
def busy (g : Nat → Nat) (m : Mem) (s : Nat) : Bool := m.out.any (fun j => g j == s)

-- The trim: every segment with no chunk out loses its memory, and with it every chunk made in it.
/-- `Grown::trim`. -/
def trimMem (g : Nat → Nat) (m : Mem) : Mem :=
  { m with
    live := fun s => m.live s && busy g m s
    made := fun j => m.made j && busy g m (g j) }

-- The invariant: a chunk out has its memory and is made, a made chunk's segment has its memory, and the chunks out are
-- as many as the pool counts in use.
/-- The pool's invariant. -/
def Inv (g : Nat → Nat) (p : Pool) (m : Mem) : Prop :=
  (∀ j, j ∈ m.out → m.live (g j) = true ∧ m.made j = true) ∧
  (∀ j, m.made j = true → m.live (g j) = true) ∧
  m.out.length = p.used

-- A new pool and a reset pool: nothing free, nothing in use, no memory.
/-- `new_grown` and `reset`. -/
def empty : Pool × Mem := (⟨[], 0, 0⟩, ⟨[], fun _ => false, fun _ => false⟩)

-- The empty pool satisfies the invariant.
/-- A new or reset pool satisfies the invariant. -/
theorem inv_empty (g : Nat → Nat) : Inv g empty.1 empty.2 := by
  simp [Inv, empty]

-- A grown pool's step: the flat pool's take, with the memory beside it.
/-- `alloc_chunk` of a grown pool. -/
def grownTake (g : Nat → Nat) (p : Pool) (m : Mem) : Nat × Pool × Mem :=
  ((take p).1, (take p).2, takeMem g m (take p).1)

-- The grown pool hands out the very chunk the flat pool does, whatever memory it holds and whatever its segments.
/-- The chunk a grown pool hands out depends on the free list and the cursor only, as a flat pool's does. -/
theorem take_indep (g g' : Nat → Nat) (p : Pool) (m m' : Mem) :
    (grownTake g p m).1 = (grownTake g' p m').1 ∧ (grownTake g p m).1 = (take p).1 :=
  ⟨rfl, rfl⟩

-- Taking counts one more chunk in use, in the flat pool's count.
/-- A take adds one to the count in use. -/
theorem take_used (p : Pool) : (take p).2.used = p.used + 1 := by
  unfold take; cases p.free <;> rfl

-- Taking keeps the invariant: the chunk handed out has its segment's memory and is made.
/-- A take keeps the invariant. -/
theorem inv_take (g : Nat → Nat) (p : Pool) (m : Mem) (h : Inv g p m) :
    Inv g (take p).2 (takeMem g m (take p).1) := by
  obtain ⟨hout, hmade, hlen⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    simp only [takeMem, List.mem_cons] at hj ⊢
    rcases hj with rfl | hj
    · simp
    · obtain ⟨h1, h2⟩ := hout j hj
      constructor
      · by_cases e : g j = g (take p).1 <;> simp [e, h1]
      · by_cases e : j = (take p).1 <;> simp [e, h2]
  · intro j hj
    simp only [takeMem] at hj ⊢
    by_cases e : j = (take p).1
    · simp [e]
    · simp only [e, ite_false] at hj
      by_cases e2 : g j = g (take p).1 <;> simp [e2, hmade j hj]
  · simp [takeMem, take_used, hlen]

-- Giving a chunk that is out keeps the invariant: the made marks and the memory stay.
/-- A give of a chunk in use keeps the invariant. -/
theorem inv_give (g : Nat → Nat) (p : Pool) (m : Mem) (i : Nat) (h : Inv g p m) (hi : i ∈ m.out) :
    Inv g (give p i) (giveMem m i) := by
  obtain ⟨hout, hmade, hlen⟩ := h
  refine ⟨fun j hj => hout j (List.mem_of_mem_erase hj), hmade, ?_⟩
  simp [giveMem, give, List.length_erase_of_mem hi, hlen]

-- Trimming keeps the invariant: a segment with a chunk out keeps its memory and its made chunks.
/-- A trim keeps the invariant and leaves the pool (free list, cursor, chunks in use) as it was. -/
theorem inv_trim (g : Nat → Nat) (p : Pool) (m : Mem) (h : Inv g p m) : Inv g p (trimMem g m) := by
  obtain ⟨hout, hmade, hlen⟩ := h
  have hb : ∀ j, j ∈ m.out → busy g m (g j) = true := fun j hj => by
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
theorem trim_keeps_in_use (g : Nat → Nat) (p : Pool) (m : Mem) (h : Inv g p m) (j : Nat) (hj : j ∈ m.out) :
    (trimMem g m).live (g j) = true ∧ (trimMem g m).made j = true :=
  (inv_trim g p m h).1 j hj

-- A busy session reuses memory: a chunk given back and taken again finds its segment's memory, nothing is allocated.
/-- Give then take of a chunk in use: the segments with memory are the same as before. -/
theorem give_take_reuses (g : Nat → Nat) (p : Pool) (m : Mem) (h : Inv g p m) (i : Nat) (hi : i ∈ m.out) :
    (takeMem g (giveMem m i) i).live = m.live := by
  funext s
  have hl := (h.1 i hi).1
  simp only [takeMem, giveMem]
  by_cases e : s = g i
  · simp [e, hl]
  · simp [e]

-- The bound the change is for: after a trim, every segment that keeps its memory has a chunk in use.
/-- After a trim, a segment holds memory only if a chunk in use lies in it. -/
theorem held_after_trim (g : Nat → Nat) (m : Mem) (s : Nat) (hs : (trimMem g m).live s = true) :
    ∃ j, j ∈ m.out ∧ g j = s := by
  simp only [trimMem, Bool.and_eq_true, busy, List.any_eq_true, beq_iff_eq] at hs
  exact hs.2

-- A quiet pool, trimmed, holds nothing, however busy it was: no segment has memory and no chunk is made.
/-- A trimmed pool with nothing in use holds no segment and no chunk. -/
theorem held_quiet (g : Nat → Nat) (m : Mem) (hq : m.out = []) (s : Nat) :
    (trimMem g m).live s = false ∧ (trimMem g m).made s = false := by
  simp [trimMem, busy, hq]

-- With segments of one chunk (wasm, 32-bit, bare metal), a trimmed pool holds exactly the chunks in use: the pool
-- before #435.
/-- With one chunk per segment, after a trim chunk `s`'s memory is held exactly when it is in use (given the
invariant). -/
theorem held_after_trim_one (own : Nat) (p : Pool) (m : Mem) (h : Inv (layout own 1) p m) (s : Nat) :
    (trimMem (layout own 1) m).live s = true ↔ s ∈ m.out := by
  constructor
  · intro hs
    obtain ⟨j, hj, e⟩ := held_after_trim (layout own 1) m s hs
    rw [layout_one] at e
    exact e ▸ hj
  · intro hs
    have := (trim_keeps_in_use (layout own 1) p m h s hs).1
    rwa [layout_one] at this

-- The quiet pool of a whole burst: twenty chunks taken and given back.
/-- Twenty takes of chunks 0 to 19, then their twenty gives, from a new pool, with chunk `i` in segment `g i`. -/
def burst (g : Nat → Nat) : Mem :=
  (List.range 20).foldl giveMem ((List.range 20).foldl (takeMem g) empty.2)

-- RED witness: without the trim, a session that gave back its 20 chunks and went quiet still holds its segment (the
-- one of 2048 chunks after its first chunk, numbered 1).
/-- The planted bug: a quiet pool that is never trimmed holds its busiest moment (its segment, not nothing). -/
theorem no_trim_breaks_bound : (burst (layout 1 2048)).out = [] ∧ (burst (layout 1 2048)).live 1 = true := by
  decide

-- And the trim releases it.
/-- The same quiet pool, trimmed, holds no segment. -/
theorem trim_releases_burst : (trimMem (layout 1 2048) (burst (layout 1 2048))).live 1 = false := by
  decide

/-!
## The spare segments of an endpoint

A segment a trim frees goes to the spare segments of its endpoint (`Segments` in `pool/grown.rs`, shared by the grown pools
of one endpoint's slots), with what its session wrote in it (the last section): nothing goes back to the system on a trim, so nothing is
unmapped while a packet or a command is handled. A pool that needs a segment takes the spare one freed last before
asking the system for a new one, so a burst takes back what its quiet sessions freed. The endpoint's timer
(`Segments::expire`, from `handle_timeout`) gives back to the system as many of the oldest spares as the cache held at
its lowest since the last expiry (`low`): the spares no session needed for a whole period. Its timing (that the
deadline covers the expiry, that an idle endpoint wakes, that nothing freed in a period goes back in it) is
`SegmentTimer.tla`; here are the counts, for any sizes.

The story: an endpoint's sessions acquire segments and release them; the timer expires. What must never happen: a
segment lost or given back twice, the endpoint holding more segments than its sessions held at once, an acquire or a
release giving a segment back to the system, or an acquire mapping a segment while one is spare. What must happen: two
expiries with no input between them leave nothing spare.
-/

-- The cache: the spare segments, oldest first (the names are only labels), and the low mark.
/-- `Segments`: `held`, oldest first, and `low`, the fewest held since the last expiry. -/
structure Spares where
  held : List Nat
  low : Nat
  deriving DecidableEq

-- Taking a spare: the newest leaves, and the low mark follows the count down.
/-- `Segments::take`. -/
def Spares.take (c : Spares) : Spares :=
  { held := c.held.dropLast, low := min c.low c.held.dropLast.length }

-- Freeing a segment to the cache: it is the newest; the low mark does not move.
/-- `Segments::put`. -/
def Spares.put (c : Spares) (x : Nat) : Spares := { c with held := c.held ++ [x] }

-- The expiry: the `low` oldest go back to the system, and the next period's low mark is what is left.
/-- `Segments::expire`, at its deadline. -/
def Spares.expire (c : Spares) : Spares :=
  { held := c.held.drop c.low, low := (c.held.drop c.low).length }

-- How many segments an expiry gives back.
/-- The segments `expire` gives back to the system. -/
def Spares.gone (c : Spares) : Nat := min c.low c.held.length

-- The endpoint: its cache, the segments its sessions hold, the most they held at once, and the system's counts.
/-- The segments of one endpoint. -/
structure Ep where
  spare : Spares
  inUse : Nat
  peak : Nat
  mapped : Nat
  unmapped : Nat
  deriving DecidableEq

-- A session needs a segment: a spare one if there is one, else one the system maps.
/-- `Grown::take` of a segment's first chunk. -/
def acquire (e : Ep) : Ep :=
  if e.spare.held = [] then
    { e with inUse := e.inUse + 1, peak := max e.peak (e.inUse + 1), mapped := e.mapped + 1 }
  else
    { e with spare := e.spare.take, inUse := e.inUse + 1, peak := max e.peak (e.inUse + 1) }

-- A session goes quiet: its segment goes to the cache, not to the system.
/-- `Grown::release` through a trim or a reset. -/
def release (e : Ep) : Ep := { e with spare := e.spare.put 0, inUse := e.inUse - 1 }

-- The timer's expiry: what it gives back is counted as unmapped.
/-- `handle_timeout` at the spares' deadline. -/
def tick (e : Ep) : Ep := { e with spare := e.spare.expire, unmapped := e.unmapped + e.spare.gone }

-- The invariant: every segment mapped is in use, spare or given back; no more held than at the peak; the low mark
-- within the cache.
/-- The endpoint's invariant. -/
def EpInv (e : Ep) : Prop :=
  e.mapped = e.inUse + e.spare.held.length + e.unmapped ∧
  e.inUse + e.spare.held.length ≤ e.peak ∧
  e.spare.low ≤ e.spare.held.length

-- A new endpoint: nothing anywhere.
/-- A new endpoint. -/
def Ep.new : Ep := ⟨⟨[], 0⟩, 0, 0, 0, 0⟩

-- The new endpoint satisfies the invariant.
/-- A new endpoint satisfies the invariant. -/
theorem epInv_new : EpInv Ep.new := by
  simp [EpInv, Ep.new]

-- An acquire keeps the invariant: a spare taken moves from the cache to the sessions, a mapped one is new.
/-- An acquire keeps the invariant. -/
theorem epInv_acquire (e : Ep) (h : EpInv e) : EpInv (acquire e) := by
  obtain ⟨hm, hp, hl⟩ := h
  unfold acquire
  cases hs : e.spare.held with
  | nil =>
    simp only [hs, List.length_nil, ite_true] at hm hp hl ⊢
    refine ⟨by simp [hs]; omega, by simp [hs]; omega, by simp [hs]; omega⟩
  | cons x t =>
    have hlen : (x :: t).dropLast.length = t.length := by simp
    simp only [hs, reduceCtorEq, ite_false, List.length_cons] at hm hp hl ⊢
    simp only [EpInv, Spares.take, hs, hlen]
    refine ⟨by omega, by omega, Nat.min_le_right _ _⟩

-- A release of a segment in use keeps the invariant: it moves from the sessions to the cache.
/-- A release keeps the invariant. -/
theorem epInv_release (e : Ep) (h : EpInv e) (hu : 0 < e.inUse) : EpInv (release e) := by
  obtain ⟨hm, hp, hl⟩ := h
  simp only [EpInv, release, Spares.put, List.length_append, List.length_singleton]
  refine ⟨by omega, by omega, by omega⟩

-- An expiry keeps the invariant: what leaves the cache is counted as given back.
/-- A tick keeps the invariant. -/
theorem epInv_tick (e : Ep) (h : EpInv e) : EpInv (tick e) := by
  obtain ⟨hm, hp, hl⟩ := h
  simp only [EpInv, tick, Spares.expire, Spares.gone, List.length_drop]
  refine ⟨by omega, by omega, Nat.le_refl _⟩

-- Only the timer gives a segment back: an acquire and a release never do.
/-- Inputs unmap nothing. -/
theorem inputs_unmap_nothing (e : Ep) : (acquire e).unmapped = e.unmapped ∧ (release e).unmapped = e.unmapped := by
  unfold acquire release
  constructor
  · split <;> rfl
  · rfl

-- A burst takes back what its quiet sessions freed: with a segment spare, an acquire maps nothing.
/-- With a spare segment, an acquire asks the system for nothing. -/
theorem acquire_reuses (e : Ep) (hs : e.spare.held ≠ []) : (acquire e).mapped = e.mapped := by
  simp [acquire, hs]

-- An expiry gives back exactly the `low` oldest spares, so a period's lowest count is what stays spare unneeded.
/-- What an expiry leaves is the cache without its `low` oldest segments. -/
theorem expire_keeps_newest (c : Spares) :
    (c.expire).held.length = c.held.length - c.low := by
  simp [Spares.expire]

-- Once quiet, two expiries leave nothing spare: the first sets the low mark to what is left, the second gives that back.
/-- Two expiries with no input between them empty the cache. -/
theorem quiet_two_expiries (e : Ep) : (tick (tick e)).spare.held = [] := by
  simp [tick, Spares.expire]; omega

-- A segment freed in a period is not given back by that period's expiry: the low mark never counts a later put.
/-- A put does not raise the low mark, so a segment freed since the last expiry outlives the next one. -/
theorem put_survives_expire (c : Spares) (x : Nat) (h : c.low ≤ c.held.length) :
    x ∈ ((c.put x).expire).held := by
  simp only [Spares.expire, Spares.put]
  rw [List.drop_append_of_le_length h]
  simp

-- A burst: from a new endpoint, 3 sessions take a segment, all go quiet, and 3 others take one in the same period.
/-- Three acquires, three releases, three acquires. -/
def burstEp : Ep :=
  acquire (acquire (acquire (release (release (release (acquire (acquire (acquire Ep.new))))))))

-- The second wave maps nothing and nothing was unmapped: 3 segments, all in use again.
/-- The burst maps 3 segments in all, unmaps none. -/
theorem burst_reuses : burstEp.mapped = 3 ∧ burstEp.unmapped = 0 ∧ burstEp.inUse = 3 := by
  decide

-- RED witness: a release that gives its segment straight back to the system (the first attempt) unmaps on the input,
-- and the burst's second wave maps all 3 again.
/-- The planted bug: an eager release. -/
def releaseEager (e : Ep) : Ep := { e with inUse := e.inUse - 1, unmapped := e.unmapped + 1 }

/-- The same burst with eager releases maps 6 segments and unmaps 3 while it runs. -/
theorem eager_release_remaps :
    let e := acquire (acquire (acquire (releaseEager (releaseEager (releaseEager
      (acquire (acquire (acquire Ep.new))))))))
    e.mapped = 6 ∧ e.unmapped = 3 := by
  decide

-- RED witness: an expiry that gives back every spare, the ones freed in its own period too, loses a segment that a
-- session freed just before it; the real expiry keeps it.
/-- The planted bug: an expiry that ignores the low mark. -/
def expireAll (_c : Spares) : Spares := { held := [], low := 0 }

/-- A segment put after the last expiry: the bad expiry gives it back, the real one keeps it. -/
theorem expire_all_loses_fresh :
    (expireAll ((Spares.mk [] 0).put 7)).held = [] ∧ ((Spares.mk [] 0).put 7).expire.held = [7] := by
  decide

/-!
## What a session finds in a spare segment

A spare segment keeps the bytes of the session that freed it, labelled here by that session's number. A session that
takes a spare finds them only if it wrote them itself (`Segments::take`: the same session takes its own back as it
was, so nothing is cleared or committed again on that path); a segment another session wrote is emptied first (its
length cut to nothing, so each chunk is zeroed as the new session commits it). What must never happen: a session that
reads bytes another session wrote, which on a hub is one member's data reaching another member.
-/

-- What session `s` can read in the spare it takes: the writer's bytes if `s` is the writer, else nothing (0).
/-- `Segments::take`: the label of the bytes session `s` finds in the spare freed last, 0 for zeros. -/
def Spares.seen (c : Spares) (s : Nat) : Nat :=
  match c.held.getLast? with
  | some w => if w = s then s else 0
  | none => 0

-- A session finds its own bytes or zeros, never another's.
/-- What a session finds in a spare is nothing or its own. -/
theorem seen_clean (c : Spares) (s : Nat) : c.seen s = 0 ∨ c.seen s = s := by
  unfold Spares.seen
  split
  · split <;> simp
  · simp

-- A session that takes back the segment it freed finds it as it left it: that path clears nothing.
/-- The spare freed last, taken by the session that freed it, keeps its bytes. -/
theorem seen_own (c : Spares) (s : Nat) (h : c.held.getLast? = some s) : c.seen s = s := by
  simp [Spares.seen, h]

-- RED witness: a take that does not empty another session's segment hands its bytes to the next session.
/-- The planted bug: a take with no clear. -/
def seenNoClear (c : Spares) (_s : Nat) : Nat := c.held.getLast?.getD 0

/-- Session 7 freed the spare; session 3 takes it: the bad take shows 7's bytes, the real one shows nothing. -/
theorem no_clear_leaks : seenNoClear (Spares.mk [7] 0) 3 = 7 ∧ (Spares.mk [7] 0).seen 3 = 0 := by
  decide

end Vinc.PoolGrown
