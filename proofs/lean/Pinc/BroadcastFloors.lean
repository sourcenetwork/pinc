import Pinc.Axioms

/-!
# Replay floors of the broadcast crate

The unbounded counterpart of `proofs/tla/BroadcastFloors.tla`: the `SentFloors` a hub keeps (`note`, `write`) with
its table caps and overflow flags, and what a restarting member does with the FLOOR bodies of every hub
(`on_floor`, `floor_settle`, `is_old`). Member and origin ids are `Nat`; a map is an association list (`look`,
`put`), so every definition is executable. A hub state is the fold of its operation log (newest first) over the
initial state `init born`.

`note` is the TLA `Note` (per-origin update with its own overflow, then the overall one, then `top := max top ts`;
`top` starts at `0` where TLA starts at `-1`, both vanish under `max hlc top`); `body`, `settle`, `isOld` are `Body`,
`Settle`, `IsOld`. Facts for every cap, member count, origin and stamp: `floorsSound`, `floorExact`, `caps`,
`bareMarker`, `listWithin`, `conservativeOverflow`; concrete witnesses `topFix_needed`, `hubRestartResidual`.
-/

namespace Pinc.BroadcastFloors

universe u
variable {α : Type u}

/-- Lookup in an association list. -/
def look : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (a, v) :: m, k => if a = k then some v else look m k

/-- Insert or overwrite. -/
def put : List (Nat × α) → Nat → α → List (Nat × α)
  | [], k, v => [(k, v)]
  | (a, w) :: m, k, v => if a = k then (a, v) :: m else (a, w) :: put m k v

theorem look_put : ∀ (m : List (Nat × α)) (k : Nat) (v : α) (j : Nat),
    look (put m k v) j = if k = j then some v else look m j
  | [], k, v, j => by simp [put, look]
  | (a, w) :: m, k, v, j => by
    have ih := look_put m k v j
    by_cases h : a = k <;> by_cases h2 : k = j <;> simp_all [put, look]
theorem length_put : ∀ (m : List (Nat × α)) (k : Nat) (v : α),
    (put m k v).length = if (look m k).isSome then m.length else m.length + 1
  | [], k, v => by simp [put, look]
  | (a, w) :: m, k, v => by
    have ih := length_put m k v
    by_cases h : a = k <;> simp_all [put, look] <;> split <;> simp

/-- `max` of an optional previous value and a new one. -/
def bump : Option Nat → Nat → Nat
  | some w, ts => max w ts
  | none, ts => ts
theorem le_bump (o : Option Nat) (ts : Nat) : ts ≤ bump o ts := by cases o <;> simp [bump] <;> omega

/-- The value at `(q, o)` of a two-level map. -/
def lk2 (os : List (Nat × List (Nat × Nat))) (q o : Nat) : Option Nat := (look os q).bind (look · o)
theorem look_getD (os : List (Nat × List (Nat × Nat))) (q o : Nat) :
    look ((look os q).getD []) o = lk2 os q o := by
  cases h : look os q <;> simp [lk2, h, look]
theorem lk2_put (os : List (Nat × List (Nat × Nat))) (p o ts q o' : Nat) :
    lk2 (put os p (put ((look os p).getD []) o (bump (lk2 os p o) ts))) q o'
      = if p = q ∧ o = o' then some (bump (lk2 os p o) ts) else lk2 os q o' := by
  by_cases hq : p = q
  · subst hq
    by_cases ho : o = o' <;> simp [lk2, look_put, ho, look_getD]
  · simp [lk2, look_put, hq]

/-! ### The hub state -/

/-- Table caps and the clock drift allowance. -/
structure Cfg where
  (tableMax originMax drift : Nat)

/-- A message taken by a hub: wall clock of the hub, member `p`, origin `o`, stamp `ts`. -/
structure Op where
  (wall p o ts : Nat)

/-- `SentFloors`. -/
structure Floors where
  (born hlc : Nat) (maxsent : List (Nat × Nat)) (msOver : Bool)
  (osent : List (Nat × List (Nat × Nat))) (opeers : List Nat) (oOver : Bool) (top : Nat)

/-- A hub at start time `born`. -/
def Floors.init (born : Nat) : Floors :=
  { born, hlc := born, maxsent := [], msOver := false, osent := [], opeers := [], oOver := false, top := 0 }

/-- Add a peer to the origin-table peer set. -/
def addPeer (l : List Nat) (p : Nat) : List Nat := if l.contains p then l else l ++ [p]
/-- The peer table is full and `p` is not in it. -/
def oFull (tm : Nat) (S : Floors) (p : Nat) : Bool := !S.opeers.contains p && decide (tm ≤ S.opeers.length)
/-- The per-origin update stops: the flag is set or the peer table is full. -/
def oStop (tm : Nat) (S : Floors) (p : Nat) : Bool := S.oOver || oFull tm S p
/-- The entry for `(p, o)` exists or the member's origin list has room. -/
def oFits (om : Nat) (S : Floors) (p o : Nat) : Bool :=
  (look ((look S.osent p).getD []) o).isSome || decide (((look S.osent p).getD []).length < om)

/-- The per-origin update of `Note`: stopped by a set overflow flag or a full peer table (overflow), else the entry
for `(p, o)` takes the maximum, unless the member's origin list is full (overflow, the peer still counted). -/
def noteO (tm om : Nat) (S : Floors) (p o ts : Nat) : Floors :=
  let d := (look S.osent p).getD []
  { S with oOver := oStop tm S p || !oFits om S p o,
           opeers := if oStop tm S p then S.opeers else addPeer S.opeers p,
           osent := if oStop tm S p || !oFits om S p o then S.osent else put S.osent p (put d o (bump (look d o) ts)) }

/-- The member table has the member or room for it. -/
def mOk (tm : Nat) (S : Floors) (p : Nat) : Bool := (look S.maxsent p).isSome || decide (S.maxsent.length < tm)

/-- The overall update of `Note`: a new member beyond the table cap sets `msOver`. -/
def noteM (tm : Nat) (S : Floors) (p ts : Nat) : Floors :=
  { S with maxsent := if mOk tm S p then put S.maxsent p (bump (look S.maxsent p) ts) else S.maxsent,
           msOver := S.msOver || !mOk tm S p }

/-- `SentFloors::note`. -/
def note (tm om : Nat) (S : Floors) (p o ts : Nat) : Floors :=
  let S2 := noteM tm (noteO tm om S p o ts) p ts
  { S2 with top := max S2.top ts }

/-- The hub follows a stamp unless it is more than `drift` ahead of its wall clock. -/
def observe (drift wall : Nat) (S : Floors) (ts : Nat) : Floors :=
  { S with hlc := if ts ≤ wall + drift then max S.hlc ts else S.hlc }

/-- A message accepted by a session: observe, then note. -/
def take (c : Cfg) (S : Floors) (x : Op) : Floors :=
  note c.tableMax c.originMax (observe c.drift x.wall S x.ts) x.p x.o x.ts

/-- The hub state after the log (newest first). -/
def run (c : Cfg) (born : Nat) (log : List Op) : Floors := log.foldr (fun x S => take c S x) (.init born)

/-- A FLOOR body for one member. -/
structure Body where
  (floor : Nat) (hist : Bool) (list : Option (List (Nat × Nat)))

/-- `SentFloors::write`. -/
def body (topFix : Bool) (S : Floors) (p : Nat) : Body :=
  let present := if topFix then max S.hlc S.top else S.hlc
  { floor := if S.msOver then present else max ((look S.maxsent p).getD 0) S.born,
    hist := S.msOver || (look S.maxsent p).isSome,
    list := if S.oOver || S.msOver then none else some ((look S.osent p).getD []) }

/-- What a member settles from the bodies of the hubs. -/
structure Settled where
  (rfloor : Option Nat) (hasOf : Bool) (ofloor : List (Nat × Nat)) (nohist : Bool)

/-- Merge one list entry into the per-origin maxima. -/
def mergeEntry (acc : List (Nat × Nat)) (e : Nat × Nat) : List (Nat × Nat) :=
  put acc e.1 (bump (look acc e.1) e.2)

/-- Merge one body. -/
def mergeBody (acc : List (Nat × Nat)) (b : Body) : List (Nat × Nat) :=
  match b.list with | some l => l.foldl mergeEntry acc | none => acc

/-- `Settle`. -/
def settle (bs : List Body) : Settled :=
  { rfloor := if bs.any (·.hist) then some (bs.foldl (fun a b => max a b.floor) 0) else none,
    hasOf := bs.all (·.list.isSome),
    ofloor := bs.foldl mergeBody [],
    nohist := !bs.any (·.hist) }

/-- `IsOld`: the per-origin floor if every hub sent a list, else the overall floor, else false. -/
def isOld (F : Settled) (o ts : Nat) : Bool :=
  if F.hasOf then (match look F.ofloor o with | some f => decide (ts ≤ f) | none => false)
  else (match F.rfloor with | some f => decide (ts ≤ f) | none => false)

/-- A hub: its start time and the messages it took (newest first). -/
structure Hub where
  (born : Nat) (log : List Op)

/-- The bodies of every hub for member `p`. -/
def bodies (c : Cfg) (topFix : Bool) (hubs : List Hub) (p : Nat) : List Body :=
  hubs.map fun h => body topFix (run c h.born h.log) p

/-- The maximum stamp noted for member `q` in a log. -/
def maxM : List Op → Nat → Option Nat
  | [], _ => none
  | x :: l, q => if x.p = q then some (bump (maxM l q) x.ts) else maxM l q

/-- The maximum stamp noted for member `q` and origin `o` in a log. -/
def maxO : List Op → Nat → Nat → Option Nat
  | [], _, _ => none
  | x :: l, q, o => if x.p = q ∧ x.o = o then some (bump (maxO l q o) x.ts) else maxO l q o

theorem le_maxM : ∀ (l : List Op) (x : Op), x ∈ l → ∃ v, maxM l x.p = some v ∧ x.ts ≤ v
  | [], _, h => by simp at h
  | y :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨bump (maxM l x.p) x.ts, by simp [maxM], le_bump _ _⟩
    · obtain ⟨v, hv, hle⟩ := le_maxM l x h
      by_cases hp : y.p = x.p
      · exact ⟨max v y.ts, by simp [maxM, hp, hv, bump], by omega⟩
      · exact ⟨v, by simp [maxM, hp, hv], hle⟩
theorem le_maxO : ∀ (l : List Op) (x : Op), x ∈ l → ∃ v, maxO l x.p x.o = some v ∧ x.ts ≤ v
  | [], _, h => by simp at h
  | y :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨bump (maxO l x.p x.o) x.ts, by simp [maxO], le_bump _ _⟩
    · obtain ⟨v, hv, hle⟩ := le_maxO l x h
      by_cases hp : y.p = x.p ∧ y.o = x.o
      · exact ⟨max v y.ts, by simp [maxO, hp, hv, bump], by omega⟩
      · exact ⟨v, by simp [maxO, hp, hv], hle⟩

/-! ### The invariant of a hub state -/

/-- What every reachable hub state satisfies with respect to the messages `l` it took. -/
structure Inv (c : Cfg) (S : Floors) (l : List Op) : Prop where
  (e1 : S.msOver = false → ∀ q, look S.maxsent q = maxM l q)
  (e2 : S.oOver = false → ∀ q o, lk2 S.osent q o = maxO l q o)
  (k1 : S.maxsent.length ≤ c.tableMax) (k2 : ∀ q d, look S.osent q = some d → d.length ≤ c.originMax)
  (k3 : S.opeers.length ≤ c.tableMax) (t : ∀ x ∈ l, x.ts ≤ S.top)
theorem inv_init (c : Cfg) (b : Nat) : Inv c (.init b) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Floors.init, maxM, maxO, lk2, look]

theorem inv_take {c : Cfg} {S : Floors} {l : List Op} (h : Inv c S l) (x : Op) : Inv c (take c S x) (x :: l) := by
  obtain ⟨e1, e2, k1, k2, k3, t⟩ := h
  have hmax : (take c S x).maxsent = if mOk c.tableMax S x.p then
      put S.maxsent x.p (bump (look S.maxsent x.p) x.ts) else S.maxsent := rfl
  have hms : (take c S x).msOver = (S.msOver || !mOk c.tableMax S x.p) := rfl
  have hos : (take c S x).osent = if oStop c.tableMax S x.p || !oFits c.originMax S x.p x.o then S.osent else
      put S.osent x.p (put ((look S.osent x.p).getD []) x.o (bump (lk2 S.osent x.p x.o) x.ts)) := by
    simp only [take, note, noteM, noteO, observe, look_getD]; rfl
  have hoo : (take c S x).oOver = (oStop c.tableMax S x.p || !oFits c.originMax S x.p x.o) := rfl
  have hop : (take c S x).opeers = if oStop c.tableMax S x.p then S.opeers else addPeer S.opeers x.p := rfl
  have htop : (take c S x).top = max S.top x.ts := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hm q
    rw [hms] at hm
    have hm' : S.msOver = false ∧ mOk c.tableMax S x.p = true := by simpa using hm
    rw [hmax]; simp only [hm'.2, ↓reduceIte]; rw [look_put, maxM]
    by_cases hq : x.p = q <;> simp [hq, e1 hm'.1 q]
  · intro ho q o'
    rw [hoo] at ho
    have ho' : (oStop c.tableMax S x.p || !oFits c.originMax S x.p x.o) = false := by simpa using ho
    have hs : S.oOver = false := by simp [oStop] at ho'; exact ho'.1.1
    rw [hos]; simp only [ho', Bool.false_eq_true, ↓reduceIte]; rw [lk2_put, maxO]
    by_cases hq : x.p = q ∧ x.o = o'
    · obtain ⟨rfl, rfl⟩ := hq; simp [e2 hs]
    · simp only [hq, ↓reduceIte]; exact e2 hs q o'
  · rw [hmax]
    split
    · rw [length_put]
      split
      · exact k1
      · simp only [mOk, Bool.or_eq_true, decide_eq_true_eq] at *; simp_all; omega
    · exact k1
  · intro q d hd
    rw [hos] at hd
    split at hd
    · exact k2 q d hd
    · have hf : oFits c.originMax S x.p x.o = true := by simp_all
      have hdd : ((look S.osent x.p).getD []).length ≤ c.originMax := by
        cases h0 : look S.osent x.p with
        | none => simp
        | some d0 => simpa using k2 _ _ h0
      rw [look_put] at hd
      split at hd
      · cases hd; rw [length_put]; split
        · exact hdd
        · simp only [oFits, Bool.or_eq_true, decide_eq_true_eq] at hf; simp_all; omega
      · exact k2 q d hd
  · rw [hop]
    split
    · exact k3
    · have hf : oFull c.tableMax S x.p = false := by simp_all [oStop]
      simp only [addPeer, oFull, Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not] at *
      split
      · exact k3
      · simp_all; omega
  · intro y hy
    rw [htop]
    rcases List.mem_cons.1 hy with rfl | hy
    · omega
    · have := t y hy; omega
theorem inv_run (c : Cfg) (b : Nat) : ∀ log : List Op, Inv c (run c b log) log
  | [] => inv_init c b
  | x :: l => inv_take (inv_run c b l) x

/-- (3) The member table never exceeds `tableMax` entries, the peer table never exceeds `tableMax`, and a member's
origin list never exceeds `originMax`. -/
theorem caps (c : Cfg) (b : Nat) (log : List Op) :
    (run c b log).maxsent.length ≤ c.tableMax ∧ (run c b log).opeers.length ≤ c.tableMax ∧
    ∀ q d, look (run c b log).osent q = some d → d.length ≤ c.originMax :=
  let h := inv_run c b log
  ⟨h.k1, h.k3, h.k2⟩

/-- (2) While no table overflowed, `maxsent` is exactly the maximum stamp noted per member, and the per-origin
lists are exactly the per-origin maxima. -/
theorem floorExact (c : Cfg) (b : Nat) (log : List Op) :
    ((run c b log).msOver = false → ∀ q, look (run c b log).maxsent q = maxM log q) ∧
    ((run c b log).oOver = false → ∀ q o, lk2 (run c b log).osent q o = maxO log q o) :=
  let h := inv_run c b log
  ⟨h.e1, h.e2⟩

/-- (4) Past either cap the body carries no list. -/
theorem bareMarker (topFix : Bool) (S : Floors) (p : Nat) (h : S.oOver = true ∨ S.msOver = true) :
    (body topFix S p).list = none := by
  rcases h with h | h <;> simp [body, h]

/-- (5) A body list holds at most `originMax` entries. -/
theorem listWithin (c : Cfg) (b : Nat) (log : List Op) (topFix : Bool) (p : Nat) (l : List (Nat × Nat))
    (h : (body topFix (run c b log) p).list = some l) : l.length ≤ c.originMax := by
  have hk := (inv_run c b log).k2
  simp only [body] at h
  split at h
  · cases h
  · cases h
    cases h0 : look (run c b log).osent p with
    | none => simp
    | some d => simpa using hk _ _ h0

/-- (6) With the table overflown, the floor is at least every stamp noted. -/
theorem conservativeOverflow (c : Cfg) (b : Nat) (log : List Op) (p : Nat)
    (h : (run c b log).msOver = true) (x : Op) (hx : x ∈ log) : x.ts ≤ (body true (run c b log) p).floor := by
  have := (inv_run c b log).t x hx
  simp only [body, h, ite_true]
  omega

/-- `r` holds a value at least `v`. -/
def AtLeast (r : Option Nat) (v : Nat) : Prop := ∃ w, r = some w ∧ v ≤ w

theorem mergeEntry_mono {acc : List (Nat × Nat)} {o v : Nat} (e : Nat × Nat) (h : AtLeast (look acc o) v) :
    AtLeast (look (mergeEntry acc e) o) v := by
  obtain ⟨w, hw, hv⟩ := h
  by_cases he : e.1 = o
  · subst he
    exact ⟨bump (some w) e.2, by simp [mergeEntry, look_put, hw], by simp [bump]; omega⟩
  · exact ⟨w, by simp [mergeEntry, look_put, he, hw], hv⟩
theorem mergeEntry_hit (acc : List (Nat × Nat)) (e : Nat × Nat) :
    AtLeast (look (mergeEntry acc e) e.1) e.2 :=
  ⟨bump (look acc e.1) e.2, by simp [mergeEntry, look_put], le_bump _ _⟩
theorem foldl_entry_mono {o v : Nat} : ∀ (l acc : List (Nat × Nat)), AtLeast (look acc o) v →
    AtLeast (look (l.foldl mergeEntry acc) o) v
  | [], _, h => h
  | e :: t, _, h => foldl_entry_mono t _ (mergeEntry_mono e h)
theorem foldl_entry_hit {o v : Nat} : ∀ (l acc : List (Nat × Nat)), look l o = some v →
    AtLeast (look (l.foldl mergeEntry acc) o) v
  | [], _, h => by simp [look] at h
  | (a, w) :: t, acc, h => by
    by_cases ha : a = o
    · simp only [look, ha, ↓reduceIte, Option.some.injEq] at h
      subst ha
      obtain ⟨u, hu, hle⟩ := mergeEntry_hit acc (a, w)
      simp only at hu hle
      exact foldl_entry_mono t _ ⟨u, hu, by omega⟩
    · simp only [look, ha, ↓reduceIte] at h
      exact foldl_entry_hit t _ h
theorem foldl_body_mono {o v : Nat} : ∀ (bs : List Body) (acc : List (Nat × Nat)), AtLeast (look acc o) v →
    AtLeast (look (bs.foldl mergeBody acc) o) v
  | [], _, h => h
  | b :: t, _, h => by
    apply foldl_body_mono t
    unfold mergeBody
    cases b.list with
    | none => exact h
    | some l => exact foldl_entry_mono l _ h
theorem foldl_body_hit {o v : Nat} (l : List (Nat × Nat)) (hl : look l o = some v) :
    ∀ (bs : List Body) (b : Body) (acc : List (Nat × Nat)), b ∈ bs → b.list = some l →
    AtLeast (look (bs.foldl mergeBody acc) o) v
  | [], _, _, hb, _ => by simp at hb
  | b' :: t, b, acc, hb, hbl => by
    rcases List.mem_cons.1 hb with rfl | hb
    · refine foldl_body_mono t (mergeBody acc b) ?_
      unfold mergeBody
      rw [hbl]
      exact foldl_entry_hit l _ hl
    · exact foldl_body_hit l hl t b _ hb hbl
theorem le_foldl_floor : ∀ (bs : List Body) (acc : Nat) (b : Body), b ∈ bs →
    b.floor ≤ bs.foldl (fun a b => max a b.floor) acc
  | [], _, _, hb => by simp at hb
  | b' :: t, acc, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · have : ∀ (t : List Body) (a : Nat), a ≤ t.foldl (fun a b => max a b.floor) a := fun t => by
        induction t with
        | nil => simp
        | cons y t ih => exact fun a => Nat.le_trans (by omega) (ih (max a y.floor))
      exact Nat.le_trans (by omega) (this t (max acc b.floor))
    · exact le_foldl_floor t _ b hb

/-- (1) Every message a hub took for a member is judged old once the member settles the bodies of all hubs, for
every table cap, hub count, origin, stamp and clock; `top` makes the overflow floor independent of the hub clock. -/
theorem floorsSound (c : Cfg) (hubs : List Hub) (h : Hub) (hh : h ∈ hubs) (x : Op) (hx : x ∈ h.log) :
    isOld (settle (bodies c true hubs x.p)) x.o x.ts = true := by
  have hI := inv_run c h.born h.log
  have hb : body true (run c h.born h.log) x.p ∈ bodies c true hubs x.p := List.mem_map.2 ⟨h, hh, rfl⟩
  generalize hS : run c h.born h.log = S at hI hb
  unfold isOld
  split
  · rename_i hs
    have hl := (by simpa [settle] using hs : ∀ b ∈ bodies c true hubs x.p, b.list.isSome = true) _ hb
    simp only [body] at hl
    split at hl
    · simp at hl
    · rename_i hn
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
      obtain ⟨v, hv, hle⟩ := le_maxO h.log x hx
      have hlk : look ((look S.osent x.p).getD []) x.o = some v := by rw [look_getD, hI.e2 hn.1 x.p x.o]; exact hv
      obtain ⟨w, hw, hvw⟩ := foldl_body_hit _ hlk (bodies c true hubs x.p) _ [] hb (by simp [body, hn.1, hn.2])
      simp only [settle, hw]
      simpa using Nat.le_trans hle hvw
  · simp only [settle]
    have hboth : (body true S x.p).hist = true ∧ x.ts ≤ (body true S x.p).floor := by
      simp only [body]
      by_cases hm : S.msOver = true
      · have := hI.t x hx
        simp only [hm, ite_true]; simp; omega
      · rw [Bool.not_eq_true] at hm
        obtain ⟨v, hv, hle⟩ := le_maxM h.log x hx
        simp only [hm, hI.e1 hm, hv]; simp; omega
    simp only [List.any_eq_true.2 ⟨_, hb, hboth.1⟩, ite_true]
    exact decide_eq_true (Nat.le_trans hboth.2 (le_foldl_floor _ 0 _ hb))

/-- One slot in the member table, no drift allowance. -/
def tiny : Cfg := { tableMax := 1, originMax := 1, drift := 0 }

/-- Member 0 is noted first (stamp 1), then member 1 with a stamp 10 ahead of the hub clock 0 (table full). -/
def aheadHub : Hub := { born := 0, log := [⟨0, 1, 0, 10⟩, ⟨0, 0, 0, 1⟩] }

/-- Without `topFix`, a full table reports the hub clock as floor, which a stamp ahead of the clock exceeds: the
message is not judged old. With `topFix` it is. -/
theorem topFix_needed :
    isOld (settle (bodies tiny false [aheadHub] 1)) 0 10 = false ∧
    isOld (settle (bodies tiny true [aheadHub] 1)) 0 10 = true := by
  decide

/-- The documented residual of a restarted hub: it forgot what it took, so its body is an empty list, and a
message it took before, whatever its stamp (in particular above `born`), is not judged old. -/
theorem hubRestartResidual (borns : List Nat) (p o ts : Nat) :
    isOld (settle (borns.map fun b => body true (Floors.init b) p)) o ts = false := by
  have hf : ∀ (bs : List Nat) (acc : List (Nat × Nat)),
      (bs.map fun b => body true (Floors.init b) p).foldl mergeBody acc = acc := fun bs => by
    induction bs with
    | nil => intro acc; rfl
    | cons b t ih =>
      intro acc
      have hm : mergeBody acc (body true (Floors.init b) p) = acc := by simp [mergeBody, body, Floors.init, look]
      simp only [List.map_cons, List.foldl_cons, hm, ih]
  have ha : ((borns.map fun b => body true (Floors.init b) p).all (·.list.isSome)) = true := by
    simp [List.all_eq_true, body, Floors.init, look]
  simp [isOld, settle, ha, hf _ [], look]

end Pinc.BroadcastFloors

#audit_axioms Pinc.BroadcastFloors.floorsSound
#audit_axioms Pinc.BroadcastFloors.floorExact
#audit_axioms Pinc.BroadcastFloors.caps
#audit_axioms Pinc.BroadcastFloors.bareMarker
#audit_axioms Pinc.BroadcastFloors.listWithin
#audit_axioms Pinc.BroadcastFloors.conservativeOverflow
#audit_axioms Pinc.BroadcastFloors.topFix_needed
#audit_axioms Pinc.BroadcastFloors.hubRestartResidual
