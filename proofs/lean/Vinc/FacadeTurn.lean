import Vinc.Axioms
import Vinc.FacadeStandbyOrder

/-!
# The drive's turn: one driver, no stale ticket, nothing the driver reads lost, the role never stranded

A transcription of `proofs/tla/FacadeTurn.tla` over any number of futures, datagrams and steps, on the slab of
`Vinc.FacadeStandby`. The Rust code is `crates/vinc/src/drive.rs` (`Shared::run_as`, the guard `Turn` and its
`Drop`). The futures are numbered; a future's waker is its number. A future is off, run (woken: the executor will
poll it), wait (its poll returned `Pending`) or flush (it sends what the endpoint wants sent). One poll is one call of
the poll function of `run_as`: it ends in Io before it registers anything (`pollIo`), finishes (`pollDone`), or waits
(`pollWait`): the future's ticket, allocated at its first wait, is armed with its waker, the future takes the role if
it may and the flag is free, and a driver reads at most `drain` datagrams the host has ready, handing each to the core.
The guard's `Drop` (`endedS`) clears the flag of a driver, releases the ticket and, for a driver or (`pass`) any
future that ends while the flag is free, passes the baton. The environment notifies held tickets, wakes every armed
ticket, delivers datagrams and fires the driver's sleep.

Assumed of the host (#246 (c)): its executor polls every woken future; a dropped receive future loses no datagram;
`sleep(at)` does not finish before `at`; every future runs on the thread that built the endpoint, so a poll is one
step and no borrow of the core is held across an await.

Main theorems: `inv_reach` (with the code's settings every reachable state has at most one driver, exactly when the
flag is set and holding the core's driver ticket; only tickets that name live slots of their generation, one future
per slot, every live slot held; a slot's waker is its holder's and a waiting future's waker is kept; the slab's own
invariant `FacadeStandby.Inv` (the exact queue of `FacadeStandby.QInv` is TLC's in the turn, `QueueOnce`, and is
not carried here: it holds while no stale entry is revived, which in the turn needs a count of the entries queued
since the entry went stale); every datagram delivered either still at the host or handed to the core once, in order;
at most `drain` read in a poll; and, while the flag is free and a future that may drive waits, a future that may
drive and holds a ticket is running or flushing), `pollWait_takes` (that future, polled, takes the role when its
attempt waits) and
`noPass_bad` (if a future that ends while the flag is free did not pass the baton on, a waiting future is stranded).
-/

namespace Vinc.FacadeTurn
open Vinc.FacadeStandby

inductive FSt where
  | off
  | run
  | wait
  | flush
  deriving DecidableEq, Repr

/-- What does not change: the relay role (only `owner` drives), the burst bound, and whether a future that ends
while the flag is free passes the baton (the code does; the witness does not). -/
structure Cfg where
  role : Bool
  owner : Nat
  drain : Nat
  pass : Bool

structure State where
  sb : S
  st : Nat → FSt
  tk : Nat → Option Ticket
  drv : Nat → Bool
  flag : Bool
  driver : Option Ticket
  sock : List Nat
  fed : List Nat
  arrived : Nat
  done : Nat → Bool
  took : Nat

def init : State := ⟨{}, fun _ => .off, fun _ => none, fun _ => false, false, none, [], [], 0, fun _ => false, 0⟩

def canDrive (c : Cfg) (f : Nat) : Bool := !c.role || f == c.owner

def set {α : Type} (g : Nat → α) (i : Nat) (v : α) : Nat → α := fun j => if j = i then v else g j

theorem set_same {α : Type} (g : Nat → α) (i : Nat) (v : α) : set g i v i = v := by simp [set]

theorem set_other {α : Type} (g : Nat → α) (i j : Nat) (v : α) (h : j ≠ i) : set g i v j = g j := by
  simp [set, h]

/-- The wakers `ws` are woken: a waiting future runs again; one running or flushing stays as it is. -/
def wake (st : Nat → FSt) (ws : List Nat) : Nat → FSt := fun f => if st f = .wait ∧ f ∈ ws then .run else st f

/-- The driver's own host futures (its receive, its sleep) wake it. -/
def hostWoken (s : State) : Nat → FSt := fun f => if s.drv f = true ∧ s.st f = .wait then .run else s.st f

/-- The burst: up to `drain` turns of the loop, each taking one datagram the host has ready (`ready` of them). -/
def burst (n drain : Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => if n = drain then 0 else 1 + burst (n + 1) drain r

/-- The ticket a waiting poll registers, and the slab after it is taken: the future's own, or a new one. -/
def ticketFor (s : State) (f : Nat) : Ticket × S :=
  match s.tk f with
  | some t => (t, s.sb)
  | none => alloc s.sb

def pollWaitS (c : Cfg) (s : State) (f ready : Nat) (moved : Bool) : State :=
  let t := (ticketFor s f).1
  let sb2 := arm t f (ticketFor s f).2
  let take := !s.drv f && canDrive c f && !s.flag
  let driving := s.drv f || take
  let k := burst 0 c.drain ready
  { s with sb := sb2, tk := set s.tk f (some t), drv := set s.drv f driving, flag := s.flag || take,
           driver := if take then some t else s.driver,
           fed := if driving then s.fed ++ s.sock.take k else s.fed,
           sock := if driving then s.sock.drop k else s.sock,
           took := if driving then k else 0,
           st := set s.st f (if driving && (decide (0 < k) || moved) then .flush else .wait) }

/-- The guard's `Drop`. -/
def endedS (c : Cfg) (s : State) (f : Nat) : State :=
  match s.tk f with
  | none => { s with st := set s.st f .off, took := 0 }
  | some t =>
    let flag1 := if s.drv f then false else s.flag
    let sb1 := release t s.sb
    let b := if s.drv f || (c.pass && !flag1) then baton sb1 else ([], sb1)
    { s with sb := b.2, flag := flag1, driver := if s.drv f then none else s.driver,
             st := set (wake s.st b.1) f .off, tk := set s.tk f none, drv := set s.drv f false, took := 0 }

inductive Step (c : Cfg) : State → State → Prop where
  | start (s : State) (f : Nat) : s.st f = .off →
      Step c s { s with st := set s.st f .run, done := set s.done f false, took := 0 }
  | pollIo (s : State) (f : Nat) : s.st f = .run → Step c s { s with st := set s.st f .flush, took := 0 }
  | pollDone (s : State) (f : Nat) : s.st f = .run →
      Step c s { s with st := set s.st f .flush, done := set s.done f true, took := 0 }
  | pollWait (s : State) (f ready : Nat) (moved : Bool) : s.st f = .run → ready ≤ s.sock.length →
      Step c s (pollWaitS c s f ready moved)
  | flushMore (s : State) (f : Nat) : s.st f = .flush → s.done f = false →
      Step c s { s with st := set s.st f .run, took := 0 }
  | flushEnd (s : State) (f : Nat) : s.st f = .flush → s.done f = true → Step c s (endedS c s f)
  | drop (s : State) (f : Nat) : s.st f ≠ .off → Step c s (endedS c s f)
  | notify (s : State) (f : Nat) (t : Ticket) : s.tk f = some t →
      Step c s { s with sb := (FacadeStandby.notify t s.sb).2, st := wake s.st (FacadeStandby.notify t s.sb).1,
                        took := 0 }
  | notifyAll (s : State) :
      Step c s { s with sb := (FacadeStandby.notifyAll s.sb).2, st := wake s.st (FacadeStandby.notifyAll s.sb).1,
                        took := 0 }
  | arrive (s : State) :
      Step c s { s with arrived := s.arrived + 1, sock := s.sock ++ [s.arrived + 1], st := hostWoken s, took := 0 }
  | hostWake (s : State) : Step c s { s with st := hostWoken s, took := 0 }

inductive Reach (c : Cfg) : State → Prop where
  | init : Reach c init
  | step (s t : State) : Reach c s → Step c s t → Reach c t

/-- While the flag is free and a future that may drive waits, a future that may drive and holds a ticket is running
or flushing. -/
def Offered (c : Cfg) (s : State) : Prop :=
  s.flag = false → (∃ f, s.st f = .wait ∧ canDrive c f = true) →
    ∃ g t, s.tk g = some t ∧ (s.st g = .run ∨ s.st g = .flush) ∧ canDrive c g = true

structure Inv (c : Cfg) (s : State) : Prop where
  slab : FacadeStandby.Inv s.sb
  one : ∀ f g, s.drv f = true → s.drv g = true → f = g
  flag_iff : s.flag = true ↔ ∃ f, s.drv f = true
  drv_ok : ∀ f, s.drv f = true → canDrive c f = true ∧ s.tk f ≠ none ∧ s.driver = s.tk f ∧ s.st f ≠ .off
  no_flag : s.flag = false → s.driver = none
  off_none : ∀ f, s.st f = .off → s.tk f = none
  tk_valid : ∀ f t, s.tk f = some t → (slotOf s.sb t).isSome = true
  tk_inj : ∀ f g t u, s.tk f = some t → s.tk g = some u → t.idx = u.idx → f = g
  live_held : ∀ i sl, s.sb.slots[i]? = some sl → sl.live = true → ∃ f t, s.tk f = some t ∧ t.idx = i
  waker_owner : ∀ i sl w, s.sb.slots[i]? = some sl → sl.waker = some w → ∃ t, s.tk w = some t ∧ t.idx = i
  wait_armed : ∀ f, s.st f = .wait → ∃ t sl, s.tk f = some t ∧ s.sb.slots[t.idx]? = some sl ∧ sl.waker = some f
  fed : s.fed ++ s.sock = List.range' 1 s.arrived
  took : s.took ≤ c.drain
  owner_wait : c.role = true → s.st c.owner = .wait → s.drv c.owner = true
  offered : Offered c s

theorem inv_init (c : Cfg) : Inv c init := by
  refine ⟨init_inv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [init, Offered]

/-! ## The slab under the turn's calls -/

theorem shape_back {a b : List Slot} {ws : List Nat} (hs : Shape a b ws) {j : Nat} {sl' : Slot}
    (hb : b[j]? = some sl') : ∃ sl, a[j]? = some sl ∧ sl'.live = sl.live ∧ sl'.gen = sl.gen ∧
      (sl'.waker = sl.waker ∨ (sl'.waker = none ∧ ∀ w, sl.waker = some w → w ∈ ws)) := by
  have hlt : j < a.length := by rw [hs.1]; exact lt_of_get hb
  obtain ⟨sl, ha⟩ : ∃ sl, a[j]? = some sl := ⟨a[j], by simp [hlt]⟩
  obtain ⟨sl'', h1, h2⟩ := hs.2 j sl ha
  rw [hb] at h1; cases h1
  exact ⟨sl, ha, h2⟩

theorem valid_shape {s s' : S} {ws : List Nat} (hs : Shape s.slots s'.slots ws) {t : Ticket}
    (h : (slotOf s t).isSome = true) : (slotOf s' t).isSome = true := by
  cases h1 : slotOf s t with
  | none => rw [h1] at h; cases h
  | some sl =>
    obtain ⟨hsl, hl, hg⟩ := slotOf_some.mp h1
    obtain ⟨sl', h2, l2, g2, _⟩ := hs.2 _ sl hsl
    have : slotOf s' t = some sl' := slotOf_some.mpr ⟨h2, l2.trans hl, g2.trans hg⟩
    rw [this]; rfl

theorem release_at {s : S} {t : Ticket} {sl : Slot} (h : slotOf s t = some sl) :
    (release t s).slots[t.idx]? =
      some { sl with live := false, gen := (sl.gen + 1) % GENS, waker := none, queued := false } ∧
    ∀ j, j ≠ t.idx → (release t s).slots[j]? = s.slots[j]? := by
  obtain ⟨hsl, _, _⟩ := slotOf_some.mp h
  have hlt := lt_of_get hsl
  unfold release
  rw [h]
  refine ⟨by simp [hlt], ?_⟩
  intro j hj
  simp [Ne.symm hj]

theorem alloc_slots (s : S) (h : FacadeStandby.Inv s) :
    (∀ j, j ≠ (alloc s).1.idx → (alloc s).2.slots[j]? = s.slots[j]?) ∧
    (∃ sl, (alloc s).2.slots[(alloc s).1.idx]? = some sl ∧ sl.live = true ∧ sl.gen = (alloc s).1.gen ∧
      sl.waker = none) ∧
    (∀ sl, s.slots[(alloc s).1.idx]? = some sl → sl.live = false) := by
  unfold alloc
  cases hf : s.free with
  | nil =>
    simp only
    refine ⟨fun j hj => by rw [get_push]; simp [hj], ⟨newSlot, by simp, rfl, rfl, rfl⟩, ?_⟩
    intro sl hsl; simp at hsl
  | cons i rest =>
    obtain ⟨sl0, hsl0, hdead⟩ := (h.f_iff i).mp (by rw [hf]; exact List.mem_cons_self)
    have hlt := lt_of_get hsl0
    have hw0 : sl0.waker = none := by
      cases hw : sl0.waker with
      | none => rfl
      | some w => have := (h.w_q i sl0 hsl0 (by simp [hw])).1; rw [hdead] at this; cases this
    simp only [hsl0]
    refine ⟨fun j hj => by simp [Ne.symm hj], ⟨{ sl0 with live := true }, by simp [hlt], rfl, rfl, hw0⟩, ?_⟩
    intro sl hsl; cases hsl; exact hdead

theorem arm_slots {s : S} {t : Ticket} {sl : Slot} (h : slotOf s t = some sl) (w : Nat) :
    (∀ j, j ≠ t.idx → (arm t w s).slots[j]? = s.slots[j]?) ∧
    ∃ sl', (arm t w s).slots[t.idx]? = some sl' ∧ sl'.live = sl.live ∧ sl'.gen = sl.gen ∧ sl'.waker = some w := by
  obtain ⟨hsl, _, _⟩ := slotOf_some.mp h
  have hlt := lt_of_get hsl
  unfold arm
  rw [h]
  simp only
  split
  · exact ⟨fun j hj => by simp [Ne.symm hj], ⟨{ sl with waker := some w }, by simp [hlt], rfl, rfl, rfl⟩⟩
  · exact ⟨fun j hj => by simp [Ne.symm hj],
      ⟨{ sl with waker := some w, queued := true }, by simp [hlt], rfl, rfl, rfl⟩⟩

/-- What a waiting poll does to the slab: the future's ticket names a live slot armed with its waker, no other slot
changes, and no other future held that slot. -/
theorem pw_slab (c : Cfg) (s : State) (h : Inv c s) (f : Nat) :
    FacadeStandby.Inv (arm (ticketFor s f).1 f (ticketFor s f).2) ∧
    (∃ sl, (arm (ticketFor s f).1 f (ticketFor s f).2).slots[(ticketFor s f).1.idx]? = some sl ∧
      sl.live = true ∧ sl.gen = (ticketFor s f).1.gen ∧ sl.waker = some f) ∧
    (∀ j, j ≠ (ticketFor s f).1.idx → (arm (ticketFor s f).1 f (ticketFor s f).2).slots[j]? = s.sb.slots[j]?) ∧
    (∀ g u, s.tk g = some u → u.idx = (ticketFor s f).1.idx → g = f) ∧
    (s.tk f = none ∨ s.tk f = some (ticketFor s f).1) := by
  unfold ticketFor
  cases htf : s.tk f with
  | some t =>
    simp only
    have hv := h.tk_valid f t htf
    obtain ⟨sl, hsl⟩ : ∃ sl, slotOf s.sb t = some sl := by
      cases h1 : slotOf s.sb t with
      | none => rw [h1] at hv; cases hv
      | some sl => exact ⟨sl, rfl⟩
    obtain ⟨_, hl, hg⟩ := slotOf_some.mp hsl
    obtain ⟨ha, sl', h1, l1, g1, w1⟩ := arm_slots hsl f
    exact ⟨arm_inv t f s.sb h.slab, ⟨sl', h1, l1.trans hl, g1.trans hg, w1⟩, ha,
      fun g u hu hi => h.tk_inj g f u t hu htf hi, by simp⟩
  | none =>
    simp only
    have hai := alloc_inv s.sb h.slab
    obtain ⟨hoth, ⟨sl, h1, l1, g1, _⟩, hdead⟩ := alloc_slots s.sb h.slab
    have hs : slotOf (alloc s.sb).2 (alloc s.sb).1 = some sl := slotOf_some.mpr ⟨h1, l1, g1⟩
    obtain ⟨ha, sl', h2, l2, g2, w2⟩ := arm_slots hs f
    refine ⟨arm_inv _ f _ hai, ⟨sl', h2, l2.trans l1, g2.trans g1, w2⟩, ?_, ?_, by simp⟩
    · intro j hj; rw [ha j hj, hoth j hj]
    · intro g u hu hi
      exfalso
      have hv := h.tk_valid g u hu
      cases h3 : slotOf s.sb u with
      | none => rw [h3] at hv; cases hv
      | some sl3 =>
        obtain ⟨h4, h5, _⟩ := slotOf_some.mp h3
        rw [hi] at h4
        rw [hdead sl3 h4] at h5; cases h5

theorem burst_le : ∀ (n drain r : Nat), n ≤ drain → burst n drain r ≤ drain - n
  | _, _, 0, _ => by simp [burst]
  | n, drain, r + 1, h => by
    unfold burst
    by_cases hn : n = drain
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      have := burst_le (n + 1) drain r (by omega)
      omega

/-! ## The steps keep the invariant -/

/-- A step that changes only the futures' states, none of them to wait, and none that holds a ticket to off. -/
theorem st_step (c : Cfg) (s s' : State) (st' : Nat → FSt) (h : Inv c s) (hst : s'.st = st')
    (hsb : s'.sb = s.sb) (htk : s'.tk = s.tk) (hdrv : s'.drv = s.drv) (hflag : s'.flag = s.flag)
    (hdriver : s'.driver = s.driver) (hfed : s'.fed ++ s'.sock = List.range' 1 s'.arrived)
    (htook : s'.took ≤ c.drain)
    (hoff : ∀ g, st' g = .off → s.tk g = none)
    (hwait : ∀ g, st' g = .wait → s.st g = .wait)
    (hrf : ∀ g t, s.tk g = some t → (s.st g = .run ∨ s.st g = .flush) → (st' g = .run ∨ st' g = .flush)) :
    Inv c s' := by
  subst hst
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfed, htook, ?_, ?_⟩
  · rw [hsb]; exact h.slab
  · rw [hdrv]; exact h.one
  · rw [hflag, hdrv]; exact h.flag_iff
  · intro f hf
    rw [hdrv] at hf
    obtain ⟨h1, h2, h3, _⟩ := h.drv_ok f hf
    exact ⟨h1, by rw [htk]; exact h2, by rw [hdriver, htk]; exact h3, fun h4 => h2 (hoff f h4)⟩
  · rw [hflag, hdriver]; exact h.no_flag
  · intro f hf; rw [htk]; exact hoff f hf
  · rw [htk, hsb]; exact h.tk_valid
  · rw [htk]; exact h.tk_inj
  · rw [htk, hsb]; exact h.live_held
  · rw [htk, hsb]; exact h.waker_owner
  · intro f hf; rw [htk, hsb]; exact h.wait_armed f (hwait f hf)
  · intro hr ho; rw [hdrv]; exact h.owner_wait hr (hwait _ ho)
  · intro hfl ⟨f, hf, hc⟩
    rw [hflag] at hfl
    obtain ⟨g, t, h1, h2, h3⟩ := h.offered hfl ⟨f, hwait f hf, hc⟩
    exact ⟨g, t, by rw [htk]; exact h1, hrf g t h1 h2, h3⟩

theorem wake_wait {st : Nat → FSt} {ws : List Nat} {g : Nat} (h : wake st ws g = .wait) :
    st g = .wait ∧ g ∉ ws := by
  unfold wake at h
  by_cases hc : st g = .wait ∧ g ∈ ws
  · simp [hc] at h
  · simp only [hc, ↓reduceIte] at h; exact ⟨h, fun hm => hc ⟨h, hm⟩⟩

theorem wake_off {st : Nat → FSt} {ws : List Nat} {g : Nat} (h : wake st ws g = .off) : st g = .off := by
  unfold wake at h; split at h
  · cases h
  · exact h

theorem wake_rf {st : Nat → FSt} {ws : List Nat} {g : Nat} (h : st g = .run ∨ st g = .flush) :
    wake st ws g = .run ∨ wake st ws g = .flush := by
  unfold wake; split
  · left; rfl
  · exact h

/-- A step that wakes `ws` while the slab changes as `Shape` says. -/
theorem wake_step (c : Cfg) (s : State) (h : Inv c s) (sb' : S) (ws : List Nat)
    (hinv : FacadeStandby.Inv sb') (hsh : Shape s.sb.slots sb'.slots ws) :
    Inv c { s with sb := sb', st := wake s.st ws, took := 0 } := by
  refine ⟨hinv, h.one, h.flag_iff, ?_, h.no_flag, ?_, ?_, h.tk_inj, ?_, ?_, ?_, h.fed, Nat.zero_le _, ?_, ?_⟩
  · intro f hf
    obtain ⟨h1, h2, h3, h4⟩ := h.drv_ok f hf
    exact ⟨h1, h2, h3, fun h5 => h4 (wake_off h5)⟩
  · intro f hf; exact h.off_none f (wake_off hf)
  · intro f t ht; exact valid_shape hsh (h.tk_valid f t ht)
  · intro i sl hi hl
    obtain ⟨sl0, h0, l0, _, _⟩ := shape_back hsh hi
    exact h.live_held i sl0 h0 (l0 ▸ hl)
  · intro i sl w hi hw
    obtain ⟨sl0, h0, _, _, w0⟩ := shape_back hsh hi
    rcases w0 with w0 | ⟨w0, _⟩
    · exact h.waker_owner i sl0 w h0 (w0 ▸ hw)
    · rw [w0] at hw; cases hw
  · intro f hf
    obtain ⟨hf1, hf2⟩ := wake_wait hf
    obtain ⟨t, sl, h1, h2, h3⟩ := h.wait_armed f hf1
    obtain ⟨sl', h4, _, _, w4⟩ := hsh.2 _ sl h2
    refine ⟨t, sl', h1, h4, ?_⟩
    rcases w4 with w4 | ⟨_, w4⟩
    · rw [w4, h3]
    · exact absurd (w4 f h3) hf2
  · intro hr ho; exact h.owner_wait hr (wake_wait ho).1
  · intro hfl ⟨f, hf, hc⟩
    obtain ⟨g, t, h1, h2, h3⟩ := h.offered hfl ⟨f, (wake_wait hf).1, hc⟩
    exact ⟨g, t, h1, wake_rf h2, h3⟩

theorem valid_some {s : S} {t : Ticket} (h : (slotOf s t).isSome = true) : ∃ sl, slotOf s t = some sl := by
  cases h1 : slotOf s t with
  | none => rw [h1] at h; cases h
  | some sl => exact ⟨sl, rfl⟩

/-- A waiting poll keeps the invariant. -/
theorem pw_inv (c : Cfg) (s : State) (h : Inv c s) (f ready : Nat) (moved : Bool) :
    Inv c (pollWaitS c s f ready moved) := by
  obtain ⟨hslab, ⟨slf, hf1, hf2, hf3, hf4⟩, hoth, hown, htkf⟩ := pw_slab c s h f
  simp only [pollWaitS]
  generalize arm (ticketFor s f).1 f (ticketFor s f).2 = sb2 at *
  generalize (ticketFor s f).1 = t at *
  generalize hk : burst 0 c.drain ready = k
  have hkle : k ≤ c.drain := by rw [← hk]; have := burst_le 0 c.drain ready (Nat.zero_le _); omega
  -- the facts the cases use
  have nodrv : s.flag = false → ∀ g, s.drv g = false := by
    intro hfl g
    cases hg : s.drv g with
    | false => rfl
    | true => have := h.flag_iff.mpr ⟨g, hg⟩; rw [hfl] at this; cases this
  have tkf_t : s.drv f = true → s.tk f = some t := by
    intro hd
    rcases htkf with h1 | h1
    · exact absurd h1 (h.drv_ok f hd).2.1
    · exact h1
  have valid_t : slotOf sb2 t = some slf := slotOf_some.mpr ⟨hf1, hf2, hf3⟩
  generalize htake : (!s.drv f && canDrive c f && !s.flag) = take
  have take_def : take = true → s.flag = false ∧ s.drv f = false ∧ canDrive c f = true := by
    intro ht; rw [← htake] at ht
    cases h1 : s.drv f <;> cases h2 : canDrive c f <;> cases h3 : s.flag <;> simp_all
  have take_back : s.flag = false → s.drv f = false → canDrive c f = true → take = true := by
    intro h1 h2 h3; rw [← htake, h1, h2, h3]; rfl
  generalize hdrv : (s.drv f || take) = driving
  have st_f : (set s.st f (if driving && (decide (0 < k) || moved) then FSt.flush else FSt.wait)) f ≠ .off := by
    rw [set_same]; split <;> simp
  refine ⟨hslab, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- one
  · intro a b ha hb
    simp only at ha hb
    by_cases haf : a = f <;> by_cases hbf : b = f
    · rw [haf, hbf]
    · rw [haf, set_same] at ha; rw [set_other _ _ _ _ hbf] at hb
      rw [← hdrv] at ha
      cases hd : s.drv f
      · rw [hd] at ha; simp at ha
        have := (take_def ha).1; rw [nodrv this b] at hb; cases hb
      · exact absurd (h.one f b hd hb) (Ne.symm hbf)
    · rw [hbf, set_same] at hb; rw [set_other _ _ _ _ haf] at ha
      rw [← hdrv] at hb
      cases hd : s.drv f
      · rw [hd] at hb; simp at hb
        have := (take_def hb).1; rw [nodrv this a] at ha; cases ha
      · exact absurd (h.one f a hd ha) (Ne.symm haf)
    · exact h.one a b (by rwa [set_other _ _ _ _ haf] at ha) (by rwa [set_other _ _ _ _ hbf] at hb)
  -- flag_iff
  · simp only
    constructor
    · intro hfl
      cases ht : take
      · rw [ht, Bool.or_false] at hfl
        obtain ⟨g, hg⟩ := h.flag_iff.mp hfl
        by_cases hgf : g = f
        · subst hgf; refine ⟨g, ?_⟩; rw [set_same, ← hdrv, hg]; rfl
        · exact ⟨g, by rw [set_other _ _ _ _ hgf]; exact hg⟩
      · exact ⟨f, by rw [set_same, ← hdrv, ht]; simp⟩
    · intro ⟨g, hg⟩
      by_cases hgf : g = f
      · rw [hgf, set_same, ← hdrv] at hg
        cases hd : s.drv f
        · rw [hd] at hg; simp at hg; rw [hg]; simp
        · rw [h.flag_iff.mpr ⟨f, hd⟩]; rfl
      · rw [set_other _ _ _ _ hgf] at hg; rw [h.flag_iff.mpr ⟨g, hg⟩]; rfl
  -- drv_ok
  · intro g hg
    simp only at hg ⊢
    by_cases hgf : g = f
    · subst hgf
      rw [set_same, ← hdrv] at hg
      refine ⟨?_, by rw [set_same]; simp, ?_, st_f⟩
      · cases hd : s.drv g
        · rw [hd] at hg; simp at hg; exact (take_def hg).2.2
        · exact (h.drv_ok g hd).1
      · rw [set_same]
        cases ht : take
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [ht, Bool.or_false] at hg
          rw [(h.drv_ok g hg).2.2.1, tkf_t hg]
        · rfl
    · rw [set_other _ _ _ _ hgf] at hg
      obtain ⟨h1, h2, h3, h4⟩ := h.drv_ok g hg
      have htf : take = false := by
        cases ht : take
        · rfl
        · have := (take_def ht).1; rw [nodrv this g] at hg; cases hg
      refine ⟨h1, by rw [set_other _ _ _ _ hgf]; exact h2, ?_, by rw [set_other _ _ _ _ hgf]; exact h4⟩
      rw [htf, set_other _ _ _ _ hgf]; simpa using h3
  -- no_flag
  · intro hfl
    simp only at hfl ⊢
    cases ht : take
    · rw [ht, Bool.or_false] at hfl; simp only [Bool.false_eq_true, ↓reduceIte]; exact h.no_flag hfl
    · rw [ht] at hfl; simp at hfl
  -- off_none
  · intro g hg
    simp only at hg ⊢
    by_cases hgf : g = f
    · subst hgf; exact absurd hg st_f
    · rw [set_other _ _ _ _ hgf] at hg ⊢; exact h.off_none g hg
  -- tk_valid
  · intro g u hu
    simp only at hu
    by_cases hgf : g = f
    · subst hgf; rw [set_same] at hu; cases hu; rw [valid_t]; rfl
    · rw [set_other _ _ _ _ hgf] at hu
      obtain ⟨sl, hsl⟩ := valid_some (h.tk_valid g u hu)
      obtain ⟨h1, h2, h3⟩ := slotOf_some.mp hsl
      have hne : u.idx ≠ t.idx := fun e => hgf (hown g u hu e)
      have : slotOf sb2 u = some sl := slotOf_some.mpr ⟨by rw [hoth _ hne]; exact h1, h2, h3⟩
      rw [this]; rfl
  -- tk_inj
  · intro a b u v ha hb hi
    simp only at ha hb
    by_cases haf : a = f <;> by_cases hbf : b = f
    · rw [haf, hbf]
    · rw [haf, set_same] at ha; cases ha; rw [set_other _ _ _ _ hbf] at hb
      exact absurd (hown b v hb hi.symm) hbf
    · rw [hbf, set_same] at hb; cases hb; rw [set_other _ _ _ _ haf] at ha
      exact absurd (hown a u ha hi) haf
    · rw [set_other _ _ _ _ haf] at ha; rw [set_other _ _ _ _ hbf] at hb; exact h.tk_inj a b u v ha hb hi
  -- live_held
  · intro i sl hi hl
    simp only at hi ⊢
    by_cases hit : i = t.idx
    · exact ⟨f, t, by rw [set_same], hit.symm⟩
    · rw [hoth i hit] at hi
      obtain ⟨g, u, hu, hui⟩ := h.live_held i sl hi hl
      have hgf : g ≠ f := by
        intro e; subst e
        rcases htkf with h1 | h1
        · rw [h1] at hu; cases hu
        · rw [h1] at hu; cases hu; exact hit hui.symm
      exact ⟨g, u, by rw [set_other _ _ _ _ hgf]; exact hu, hui⟩
  -- waker_owner
  · intro i sl w hi hw
    simp only at hi ⊢
    by_cases hit : i = t.idx
    · rw [hit, hf1] at hi; cases hi; rw [hf4] at hw; cases hw
      exact ⟨t, by rw [set_same], hit.symm⟩
    · rw [hoth i hit] at hi
      obtain ⟨u, hu, hui⟩ := h.waker_owner i sl w hi hw
      have hwf : w ≠ f := by
        intro e; subst e
        rcases htkf with h1 | h1
        · rw [h1] at hu; cases hu
        · rw [h1] at hu; cases hu; exact hit hui.symm
      exact ⟨u, by rw [set_other _ _ _ _ hwf]; exact hu, hui⟩
  -- wait_armed
  · intro g hg
    simp only at hg ⊢
    by_cases hgf : g = f
    · subst hgf; exact ⟨t, slf, by rw [set_same], hf1, hf4⟩
    · rw [set_other _ _ _ _ hgf] at hg
      obtain ⟨u, sl, h1, h2, h3⟩ := h.wait_armed g hg
      have hne : u.idx ≠ t.idx := fun e => hgf (hown g u h1 e)
      exact ⟨u, sl, by rw [set_other _ _ _ _ hgf]; exact h1, by rw [hoth _ hne]; exact h2, h3⟩
  -- fed
  · simp only
    split
    · rw [List.append_assoc, List.take_append_drop]; exact h.fed
    · exact h.fed
  -- took
  · simp only
    split
    · exact hkle
    · exact Nat.zero_le _
  -- owner_wait
  · intro hr ho
    simp only at ho ⊢
    by_cases hof : c.owner = f
    · rw [hof, set_same] at ho ⊢
      rw [← hdrv]
      cases hd : s.drv f
      · cases ht : take
        · exfalso
          have hcd : canDrive c f = true := by simp [canDrive, hof]
          cases hfl : s.flag
          · have := take_back hfl hd hcd; rw [ht] at this; cases this
          · obtain ⟨g, hg⟩ := h.flag_iff.mp hfl
            have := (h.drv_ok g hg).1
            simp [canDrive, hr] at this
            rw [this, hof] at hg; rw [hd] at hg; cases hg
        · rfl
      · rfl
    · rw [set_other _ _ _ _ hof] at ho ⊢; exact h.owner_wait hr ho
  -- offered
  · intro hfl ⟨g, hg, hc⟩
    simp only at hfl hg ⊢
    have hfl0 : s.flag = false := by cases h1 : s.flag <;> simp_all
    have ht0 : take = false := by cases h1 : take <;> simp_all
    have hcf : canDrive c f = false := by
      cases h1 : canDrive c f
      · rfl
      · have := take_back hfl0 (nodrv hfl0 f) h1; rw [ht0] at this; cases this
    have hgf : g ≠ f := by intro e; rw [e, hcf] at hc; cases hc
    rw [set_other _ _ _ _ hgf] at hg
    obtain ⟨g', u, h1, h2, h3⟩ := h.offered hfl0 ⟨g, hg, hc⟩
    have hg'f : g' ≠ f := by intro e; rw [e, hcf] at h3; cases h3
    exact ⟨g', u, by rw [set_other _ _ _ _ hg'f]; exact h1, by rw [set_other _ _ _ _ hg'f]; exact h2, h3⟩

/-- The guard's `Drop` keeps the invariant, when a future that ends while the flag is free passes the baton on. -/
theorem ended_inv (c : Cfg) (hp : c.pass = true) (s : State) (h : Inv c s) (f : Nat) : Inv c (endedS c s f) := by
  unfold endedS
  cases htf : s.tk f with
  | none =>
    simp only
    refine st_step c s _ (set s.st f .off) h rfl rfl rfl rfl rfl rfl h.fed (Nat.zero_le _) ?_ ?_ ?_
    · intro g hg
      by_cases hgf : g = f
      · rw [hgf]; exact htf
      · rw [set_other _ _ _ _ hgf] at hg; exact h.off_none g hg
    · intro g hg
      by_cases hgf : g = f
      · rw [hgf, set_same] at hg; cases hg
      · rwa [set_other _ _ _ _ hgf] at hg
    · intro g u hu hrf
      have hgf : g ≠ f := by intro e; rw [e, htf] at hu; cases hu
      rwa [set_other _ _ _ _ hgf]
  | some t =>
    simp only
    obtain ⟨slt, hslt⟩ := valid_some (h.tk_valid f t htf)
    obtain ⟨hrat, hroth⟩ := release_at hslt
    have hinv1 := release_inv t s.sb h.slab
    generalize hflag1 : (if s.drv f = true then false else s.flag) = flag1
    generalize hb : (if (s.drv f || (c.pass && !flag1)) = true then baton (release t s.sb)
      else ([], release t s.sb)) = b
    have hbinv : FacadeStandby.Inv b.2 := by
      rw [← hb]; split
      · exact baton_inv _ hinv1
      · exact hinv1
    have hbsh : Shape (release t s.sb).slots b.2.slots b.1 := by
      rw [← hb]; split
      · exact (baton_shape _).1
      · exact shape_refl _ _
    -- the slots of others are untouched by the release
    have other_idx : ∀ g u, s.tk g = some u → g ≠ f → u.idx ≠ t.idx :=
      fun g u hu hgf e => hgf (h.tk_inj g f u t hu htf e)
    have dead_t : ∀ sl, (release t s.sb).slots[t.idx]? = some sl → sl.live = false ∧ sl.waker = none := by
      intro sl hsl; rw [hrat] at hsl; cases hsl; exact ⟨rfl, rfl⟩
    have flag1_false_drv : flag1 = false → ∀ g, g ≠ f → s.drv g = false := by
      intro h1 g hgf
      cases hg : s.drv g with
      | false => rfl
      | true =>
        exfalso
        cases hd : s.drv f
        · rw [hd] at hflag1; simp at hflag1; rw [← hflag1] at h1
          have := h.flag_iff.mpr ⟨g, hg⟩; rw [h1] at this; cases this
        · exact hgf (h.one g f hg hd)
    refine ⟨hbinv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.fed, Nat.zero_le _, ?_, ?_⟩
    -- one
    · intro a b' ha hb'
      simp only at ha hb'
      have haf : a ≠ f := by intro e; rw [e, set_same] at ha; cases ha
      have hbf : b' ≠ f := by intro e; rw [e, set_same] at hb'; cases hb'
      rw [set_other _ _ _ _ haf] at ha; rw [set_other _ _ _ _ hbf] at hb'
      exact h.one a b' ha hb'
    -- flag_iff
    · simp only
      constructor
      · intro h1
        cases hd : s.drv f
        · rw [hd] at hflag1; simp at hflag1; rw [← hflag1] at h1
          obtain ⟨g, hg⟩ := h.flag_iff.mp h1
          have hgf : g ≠ f := by intro e; rw [e, hd] at hg; cases hg
          exact ⟨g, by rw [set_other _ _ _ _ hgf]; exact hg⟩
        · rw [hd] at hflag1; simp only [↓reduceIte] at hflag1; rw [← hflag1] at h1; cases h1
      · intro ⟨g, hg⟩
        have hgf : g ≠ f := by intro e; rw [e, set_same] at hg; cases hg
        rw [set_other _ _ _ _ hgf] at hg
        cases h1 : flag1
        · exact absurd hg (by rw [flag1_false_drv h1 g hgf]; simp)
        · rfl
    -- drv_ok
    · intro g hg
      simp only at hg ⊢
      have hgf : g ≠ f := by intro e; rw [e, set_same] at hg; cases hg
      rw [set_other _ _ _ _ hgf] at hg
      obtain ⟨h1, h2, h3, h4⟩ := h.drv_ok g hg
      have hdf : s.drv f = false := by
        cases hd : s.drv f
        · rfl
        · exact absurd (h.one g f hg hd) hgf
      refine ⟨h1, by rw [set_other _ _ _ _ hgf]; exact h2, ?_, ?_⟩
      · rw [hdf, set_other _ _ _ _ hgf]; simpa using h3
      · rw [set_other _ _ _ _ hgf]; exact fun h5 => h4 (wake_off h5)
    -- no_flag
    · intro h1
      simp only at h1 ⊢
      cases hd : s.drv f
      · rw [hd] at hflag1; simp at hflag1; rw [← hflag1] at h1
        simp only [Bool.false_eq_true, ↓reduceIte]; exact h.no_flag h1
      · rfl
    -- off_none
    · intro g hg
      simp only at hg ⊢
      by_cases hgf : g = f
      · rw [hgf, set_same]
      · rw [set_other _ _ _ _ hgf] at hg ⊢; exact h.off_none g (wake_off hg)
    -- tk_valid
    · intro g u hu
      simp only at hu
      have hgf : g ≠ f := by intro e; rw [e, set_same] at hu; cases hu
      rw [set_other _ _ _ _ hgf] at hu
      obtain ⟨sl, hsl⟩ := valid_some (h.tk_valid g u hu)
      obtain ⟨h1, h2, h3⟩ := slotOf_some.mp hsl
      have h4 : slotOf (release t s.sb) u = some sl :=
        slotOf_some.mpr ⟨by rw [hroth _ (other_idx g u hu hgf)]; exact h1, h2, h3⟩
      exact valid_shape hbsh (by rw [h4]; rfl)
    -- tk_inj
    · intro a b' u v ha hb' hi
      simp only at ha hb'
      have haf : a ≠ f := by intro e; rw [e, set_same] at ha; cases ha
      have hbf : b' ≠ f := by intro e; rw [e, set_same] at hb'; cases hb'
      rw [set_other _ _ _ _ haf] at ha; rw [set_other _ _ _ _ hbf] at hb'
      exact h.tk_inj a b' u v ha hb' hi
    -- live_held
    · intro i sl hi hl
      simp only at hi ⊢
      obtain ⟨sl0, h0, l0, _, _⟩ := shape_back hbsh hi
      have hit : i ≠ t.idx := by
        intro e; rw [e] at h0; rw [(dead_t sl0 h0).1] at l0; rw [l0] at hl; cases hl
      rw [hroth i hit] at h0
      obtain ⟨g, u, hu, hui⟩ := h.live_held i sl0 h0 (l0 ▸ hl)
      have hgf : g ≠ f := by intro e; rw [e, htf] at hu; cases hu; exact hit hui.symm
      exact ⟨g, u, by rw [set_other _ _ _ _ hgf]; exact hu, hui⟩
    -- waker_owner
    · intro i sl w hi hw
      simp only at hi ⊢
      obtain ⟨sl0, h0, _, _, w0⟩ := shape_back hbsh hi
      have hw0 : sl0.waker = some w := by
        rcases w0 with w0 | ⟨w0, _⟩
        · rw [← w0]; exact hw
        · rw [w0] at hw; cases hw
      have hit : i ≠ t.idx := by
        intro e; rw [e] at h0; rw [(dead_t sl0 h0).2] at hw0; cases hw0
      rw [hroth i hit] at h0
      obtain ⟨u, hu, hui⟩ := h.waker_owner i sl0 w h0 hw0
      have hwf : w ≠ f := by intro e; rw [e, htf] at hu; cases hu; exact hit hui.symm
      exact ⟨u, by rw [set_other _ _ _ _ hwf]; exact hu, hui⟩
    -- wait_armed
    · intro g hg
      simp only at hg ⊢
      have hgf : g ≠ f := by intro e; rw [e, set_same] at hg; cases hg
      rw [set_other _ _ _ _ hgf] at hg
      obtain ⟨hg1, hg2⟩ := wake_wait hg
      obtain ⟨u, sl, h1, h2, h3⟩ := h.wait_armed g hg1
      have h2' : (release t s.sb).slots[u.idx]? = some sl := by rw [hroth _ (other_idx g u h1 hgf)]; exact h2
      obtain ⟨sl', h4, _, _, w4⟩ := hbsh.2 _ sl h2'
      refine ⟨u, sl', by rw [set_other _ _ _ _ hgf]; exact h1, h4, ?_⟩
      rcases w4 with w4 | ⟨_, w4⟩
      · rw [w4, h3]
      · exact absurd (w4 g h3) hg2
    -- owner_wait
    · intro hr ho
      simp only at ho ⊢
      have hof : c.owner ≠ f := by intro e; rw [e, set_same] at ho; cases ho
      rw [set_other _ _ _ _ hof] at ho ⊢
      exact h.owner_wait hr (wake_wait ho).1
    -- offered
    · intro hfl ⟨g, hg, hc⟩
      simp only at hfl hg ⊢
      have hgf : g ≠ f := by intro e; rw [e, set_same] at hg; cases hg
      rw [set_other _ _ _ _ hgf] at hg
      obtain ⟨hg1, _⟩ := wake_wait hg
      -- the baton was passed
      have hpass : (s.drv f || (c.pass && !flag1)) = true := by rw [hp, hfl]; simp
      rw [hpass] at hb
      simp only [↓reduceIte] at hb
      -- with the relay role the waiting future is the owner, who drives: the flag was not free
      cases hrole : c.role
      · obtain ⟨u, sl, h1, h2, h3⟩ := h.wait_armed g hg1
        have h2' : (release t s.sb).slots[u.idx]? = some sl := by rw [hroth _ (other_idx g u h1 hgf)]; exact h2
        obtain ⟨w, hw⟩ := baton_one _ hinv1 u.idx sl h2' (by rw [h3]; rfl)
        rcases baton_first (release t s.sb) with ⟨h5, _, _⟩ | ⟨_, k, _, sli, w', _, _, hk, h8, h9, _⟩
        · rw [h5] at hw; cases hw
        · rw [hw] at h9; cases h9
          have h6 := (slotAt_some.mp hk).1
          have hit : k.idx ≠ t.idx := by intro e; rw [e] at h6; rw [(dead_t sli h6).2] at h8; cases h8
          rw [hroth k.idx hit] at h6
          obtain ⟨v, hv, hvi⟩ := h.waker_owner k.idx sli w h6 h8
          have hwf : w ≠ f := by intro e; rw [e, htf] at hv; cases hv; exact hit hvi.symm
          have hwoff : s.st w ≠ .off := fun e => by rw [h.off_none w e] at hv; cases hv
          refine ⟨w, v, by rw [set_other _ _ _ _ hwf]; exact hv, ?_, by simp [canDrive, hrole]⟩
          rw [set_other _ _ _ _ hwf, ← hb, hw]
          unfold wake
          split
          · left; rfl
          · rename_i hn
            cases hsw : s.st w with
            | off => exact absurd hsw hwoff
            | run => left; rfl
            | wait => exact absurd ⟨hsw, List.mem_singleton_self w⟩ hn
            | flush => right; rfl
      · exfalso
        have hgo : g = c.owner := by simpa [canDrive, hrole] using hc
        have hdg := h.owner_wait hrole (hgo ▸ hg1)
        rw [← hgo] at hdg
        apply flag1_false_drv hfl g hgf |> fun e => by rw [e] at hdg; cases hdg

theorem inv_step (c : Cfg) (hp : c.pass = true) (s t : State) (h : Inv c s) (hs : Step c s t) : Inv c t := by
  cases hs with
  | start f hf =>
    refine st_step c s _ (set s.st f .run) h rfl rfl rfl rfl rfl rfl h.fed (Nat.zero_le _) ?_ ?_ ?_
    · intro g hg
      by_cases hgf : g = f
      · subst hgf; rw [set_same] at hg; cases hg
      · rw [set_other _ _ _ _ hgf] at hg; exact h.off_none g hg
    · intro g hg
      by_cases hgf : g = f
      · subst hgf; rw [set_same] at hg; cases hg
      · rwa [set_other _ _ _ _ hgf] at hg
    · intro g u _ hrf
      by_cases hgf : g = f
      · subst hgf; rw [hf] at hrf; simp at hrf
      · rwa [set_other _ _ _ _ hgf]
  | pollIo f hf | pollDone f hf =>
    refine st_step c s _ (set s.st f .flush) h rfl rfl rfl rfl rfl rfl h.fed (Nat.zero_le _) ?_ ?_ ?_
    · intro g hg
      by_cases hgf : g = f
      · subst hgf; rw [set_same] at hg; cases hg
      · rw [set_other _ _ _ _ hgf] at hg; exact h.off_none g hg
    · intro g hg
      by_cases hgf : g = f
      · subst hgf; rw [set_same] at hg; cases hg
      · rwa [set_other _ _ _ _ hgf] at hg
    · intro g u _ hrf
      by_cases hgf : g = f
      · subst hgf; rw [set_same]; right; rfl
      · rwa [set_other _ _ _ _ hgf]
  | pollWait f ready moved _ _ => exact pw_inv c s h f ready moved
  | flushMore f hf _ =>
    refine st_step c s _ (set s.st f .run) h rfl rfl rfl rfl rfl rfl h.fed (Nat.zero_le _) ?_ ?_ ?_
    · intro g hg
      by_cases hgf : g = f
      · subst hgf; rw [set_same] at hg; cases hg
      · rw [set_other _ _ _ _ hgf] at hg; exact h.off_none g hg
    · intro g hg
      by_cases hgf : g = f
      · subst hgf; rw [set_same] at hg; cases hg
      · rwa [set_other _ _ _ _ hgf] at hg
    · intro g u _ hrf
      by_cases hgf : g = f
      · subst hgf; rw [set_same]; left; rfl
      · rwa [set_other _ _ _ _ hgf]
  | flushEnd f _ _ => exact ended_inv c hp s h f
  | drop f _ => exact ended_inv c hp s h f
  | notify f t _ => exact wake_step c s h _ _ (notify_inv t s.sb h.slab) (notify_shape t s.sb).1
  | notifyAll => exact wake_step c s h _ _ (notifyAll_inv s.sb h.slab) (notifyAll_shape s.sb).1
  | arrive =>
    have hhw : ∀ g, hostWoken s g = .wait → s.st g = .wait := by
      intro g hg; unfold hostWoken at hg; split at hg
      · cases hg
      · exact hg
    refine st_step c s _ (hostWoken s) h rfl rfl rfl rfl rfl rfl ?_ (Nat.zero_le _) ?_ ?_ ?_
    · show s.fed ++ (s.sock ++ [s.arrived + 1]) = List.range' 1 (s.arrived + 1)
      rw [← List.append_assoc, h.fed, List.range'_concat]
      congr 2
      omega
    · intro g hg; unfold hostWoken at hg; split at hg
      · cases hg
      · exact h.off_none g hg
    · exact hhw
    · intro g u _ hrf; unfold hostWoken; split
      · left; rfl
      · exact hrf
  | hostWake =>
    refine st_step c s _ (hostWoken s) h rfl rfl rfl rfl rfl rfl h.fed (Nat.zero_le _) ?_ ?_ ?_
    · intro g hg; unfold hostWoken at hg; split at hg
      · cases hg
      · exact h.off_none g hg
    · intro g hg; unfold hostWoken at hg; split at hg
      · cases hg
      · exact hg
    · intro g u _ hrf; unfold hostWoken; split
      · left; rfl
      · exact hrf

/-- With the code's settings (a future that ends while the flag is free passes the baton on), every reachable state
keeps the invariant: one driver, no stale ticket, a slot's waker its holder's, the slab's own invariant, nothing the
driver reads lost or read twice, at most `drain` in a poll, and the role never left with nobody to take it. -/
theorem inv_reach (c : Cfg) (hp : c.pass = true) (s : State) (h : Reach c s) : Inv c s := by
  induction h with
  | init => exact inv_init c
  | step s t _ hs ih => exact inv_step c hp s t ih hs

/-- The progress of the role: a future that may drive, polled while the flag is free, takes the role when its
attempt waits. With `inv_reach`'s `offered` and the host's executor polling every woken future (and an attempt not
ending in Io forever), a free role with a future waiting is taken (TLC checks this as `RoleTaken` under fairness). -/
theorem pollWait_takes (c : Cfg) (s : State) (h : Inv c s) (f ready : Nat) (moved : Bool)
    (hfl : s.flag = false) (hc : canDrive c f = true) :
    (pollWaitS c s f ready moved).drv f = true ∧ (pollWaitS c s f ready moved).flag = true ∧
    (pollWaitS c s f ready moved).driver = (pollWaitS c s f ready moved).tk f := by
  have hd : s.drv f = false := by
    cases h1 : s.drv f with
    | false => rfl
    | true => have := h.flag_iff.mpr ⟨f, h1⟩; rw [hfl] at this; cases this
  simp [pollWaitS, hd, hfl, hc, set_same]

/-! ## The witness: a future that ends while the flag is free must pass the baton on -/

/-- The code without the `else if !self.sh.driving.get()` branch of `Turn::drop`. -/
def noPass : Cfg := ⟨false, 1, 1, false⟩

def startS (s : State) (f : Nat) : State := { s with st := set s.st f .run, done := set s.done f false, took := 0 }

/-- Future 1 waits and drives, then 2 and 3 wait; 1 ends and the baton wakes 2; 2 ends before its poll. -/
def strand : State :=
  endedS noPass (endedS noPass (pollWaitS noPass (startS (pollWaitS noPass (startS
    (pollWaitS noPass (startS init 1) 1 0 true) 2) 2 0 false) 3) 3 0 false) 1) 2

theorem strand_reach : Reach noPass strand := by
  have r1 : Reach noPass (startS init 1) := Reach.step _ _ Reach.init (Step.start init 1 rfl)
  have r2 := Reach.step _ _ r1 (Step.pollWait (startS init 1) 1 0 true (by decide) (by simp))
  have r3 := Reach.step _ _ r2 (Step.start _ 2 (by decide))
  have r4 := Reach.step _ _ r3 (Step.pollWait _ 2 0 false (by decide) (by simp))
  have r5 := Reach.step _ _ r4 (Step.start _ 3 (by decide))
  have r6 := Reach.step _ _ r5 (Step.pollWait _ 3 0 false (by decide) (by simp))
  have r7 := Reach.step _ _ r6 (Step.drop _ 1 (by decide))
  exact Reach.step _ _ r7 (Step.drop _ 2 (by decide))

/-- Without passing the baton on, the role is stranded: the flag is free, future 3 waits, and no future that holds
a ticket runs or flushes. -/
theorem noPass_bad : ∃ s, Reach noPass s ∧ ¬Offered noPass s := by
  refine ⟨strand, strand_reach, fun hoff => ?_⟩
  have hfl : strand.flag = false := by decide
  have h3 : strand.st 3 = .wait := by decide
  obtain ⟨g, t, hg, hrf, _⟩ := hoff hfl ⟨3, h3, by decide⟩
  by_cases g1 : g = 1
  · subst g1; have : strand.tk 1 = none := by decide
    rw [this] at hg; cases hg
  by_cases g2 : g = 2
  · subst g2; have : strand.tk 2 = none := by decide
    rw [this] at hg; cases hg
  by_cases g3 : g = 3
  · subst g3; rw [h3] at hrf; simp at hrf
  have : strand.tk g = none := by
    simp [strand, endedS, pollWaitS, startS, set, g1, g2, g3, init, ticketFor]
  rw [this] at hg; cases hg

#audit_axioms Vinc.FacadeTurn.inv_reach
#audit_axioms Vinc.FacadeTurn.pollWait_takes
#audit_axioms Vinc.FacadeTurn.noPass_bad

end Vinc.FacadeTurn
