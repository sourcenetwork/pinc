/-!
# The spray-and-wait forwarder: the model

A model of `vinc-dtn/src/forward.rs` (`Forwarder::step`, `advance`, `poll`, `poll_retransmit`, `poll_spray`), one
node, step for step. The three tables are lists of `Option` slots of the capacities `B`, `L` and `T` (the lists have
that length; nothing here fixes the capacity, so every theorem is for every capacity). Searches run in slot order and
a new entry goes to the first free slot, as in the code. Node ids and bundle ids are `Nat`s (equal id, equal bytes).

Machine integers: the times and timers are `u64` with `saturating_sub` (`Nat` subtraction truncates at 0, the same
function) and the clock is `max`; `sat8` is the `u8` `saturating_add` of the send counter; the copies are a `u16`
halved by integer division. The model keeps the values as `Nat`. Nothing in the forwarder adds to a time, a timer or
a copy count (timers only go down, `advance_timer_le`; copies only move from held to handed, `spray_total`), and the
one addition, the send counter, is capped (`sat8_le`), so no `u64`, `u16` or `u8` wraps.

The theorems about the model are in `DtnForwardThm.lean` (ordering, timers, expiry, spray rules, the destination),
`DtnForwardInv.lean` (the invariants) and `DtnForwardCons.lean` (copies are conserved); the trace replay is
`TraceDtnForward.lean`; the TLA+ counterpart of the operators is `proofs/tla/DtnForwardOps.tla`.
-/

namespace Vinc.DtnForward

/-- `u8::saturating_add(1)` for a counter that is a `u8`. -/
def sat8 (x : Nat) : Nat := min x 255

/-- The phase of a transfer: `sent remaining sends` (`remaining` link-up milliseconds to the next send, `sends` so
far), `acked`, `gaveUp`. -/
inductive Phase where
  | sent (rem sends : Nat)
  | acked
  | gaveUp
  deriving DecidableEq, Repr

/-- A bundle to forward (`Held` with the `delivered` flag of the slot). -/
structure Bundle where
  id : Nat
  dest : Nat
  exp : Nat
  copies : Nat
  delivered : Bool
  deriving DecidableEq, Repr

/-- A link slot. -/
structure Link where
  peer : Nat
  up : Bool
  deriving DecidableEq, Repr

/-- A transfer slot. -/
structure Transfer where
  bundle : Nat
  peer : Nat
  given : Nat
  deliver : Bool
  phase : Phase
  deriving DecidableEq, Repr

/-- A memory slot: an accepted bundle and the time at which the memory of it ends. -/
structure Seen where
  id : Nat
  exp : Nat
  deriving DecidableEq, Repr

/-- The forwarder. `retry` and `maxSends` are the `Policy`; the tables are slot lists (`ds` is the memory). -/
structure F where
  retry : Nat
  maxSends : Nat
  now : Nat
  bs : List (Option Bundle)
  ls : List (Option Link)
  ts : List (Option Transfer)
  ds : List (Option Seen)
  deriving DecidableEq, Repr

/-- `Forwarder::new` with capacities `b`, `l`, `t`, `d` at time `now`. -/
def F.new (retry maxSends now b l t d : Nat) : F :=
  ⟨retry, maxSends, now, List.replicate b none, List.replicate l none, List.replicate t none, List.replicate d none⟩

/-- The inputs. -/
inductive Input where
  | tick
  | hold (id dest exp copies : Nat)
  | linkUp (peer : Nat)
  | linkDown (peer : Nat)
  | acked (peer id : Nat)
  | forget (id : Nat)
  deriving DecidableEq, Repr

/-- `ForwardError` (`ok` is the `Ok(())`). -/
inductive Err where
  | ok | duplicate | full | noCopies | unknown | finished
  deriving DecidableEq, Repr

/-- `Action`; `none` is the quiet poll. -/
inductive Act where
  | none
  | send (peer bundle copies : Nat) (retr : Bool)
  | release (bundle : Nat)
  deriving DecidableEq, Repr

/-! ### Slot-list helpers -/

/-- Apply `g` to the element at index `i`. -/
def upd {α : Type} : List α → Nat → (α → α) → List α
  | [], _, _ => []
  | a :: r, 0, g => g a :: r
  | a :: r, n + 1, g => a :: upd r n g

/-- The first slot holding a value that satisfies `p`. -/
def firstIdx {α : Type} (p : α → Bool) (l : List (Option α)) : Option Nat :=
  l.findIdx? fun o => o.any p

/-- The first free slot. -/
def freeIdx {α : Type} (l : List (Option α)) : Option Nat :=
  l.findIdx? Option.isNone

/-- The value in slot `i`. -/
def slot {α : Type} (l : List (Option α)) (i : Nat) : Option α := (l[i]?).getD none

/-- Whether some slot satisfies `p`. -/
def anyS {α : Type} (p : α → Bool) (l : List (Option α)) : Bool := l.any fun o => o.any p

/-- The first memory slot that is free or whose entry has expired (`exp ≤ now`). -/
def freeD (now : Nat) (l : List (Option Seen)) : Option Nat :=
  l.findIdx? fun o => o.all fun d => decide (d.exp ≤ now)

/-- Whether a link to `p` is up. -/
def upLink (ls : List (Option Link)) (p : Nat) : Bool := anyS (fun l => l.up && l.peer == p) ls

/-- `Forwarder::advance`: charge the elapsed time to the timers whose link is up; time never runs backwards. -/
def advance (f : F) (now : Nat) : F :=
  { f with
    now := max f.now now
    ts := f.ts.map (Option.map fun t =>
      match t.phase with
      | .sent r s => if upLink f.ls t.peer then { t with phase := .sent (r - (now - f.now)) s } else t
      | _ => t) }

/-- `Forwarder::drop_bundle`: the first slot of the bundle and every transfer of it. -/
def dropB (f : F) (id : Nat) : F :=
  { f with
    bs := match firstIdx (·.id == id) f.bs with
      | some i => upd f.bs i fun _ => none
      | none => f.bs
    ts := f.ts.map fun o => if o.any (·.bundle == id) then none else o }

/-- `Forwarder::step`: advance, then apply the input; an error leaves the advanced state. -/
def step (f0 : F) (now : Nat) (inp : Input) : F × Err :=
  let f := advance f0 now
  match inp with
  | .tick => (f, .ok)
  | .hold id dest exp copies =>
    if copies == 0 then (f, .noCopies)
    else if anyS (·.id == id) f.bs then (f, .duplicate)
    else if anyS (fun d => d.id == id && decide (f.now < d.exp)) f.ds then (f, .finished)
    else match freeD f.now f.ds, freeIdx f.bs with
      | some k, some i =>
        ({ f with bs := upd f.bs i fun _ => some ⟨id, dest, exp, copies, false⟩
                  ds := upd f.ds k fun _ => some ⟨id, exp⟩ }, .ok)
      | _, _ => (f, .full)
  | .linkUp peer | .linkDown peer =>
    let up := match inp with | .linkUp _ => true | _ => false
    match firstIdx (·.peer == peer) f.ls with
    | some i => ({ f with ls := upd f.ls i (Option.map fun l => { l with up := up }) }, .ok)
    | none => match freeIdx f.ls with
      | none => (f, .full)
      | some i => ({ f with ls := upd f.ls i fun _ => some ⟨peer, up⟩ }, .ok)
  | .acked peer id =>
    match firstIdx (fun t => t.bundle == id && t.peer == peer) f.ts with
    | none => (f, .unknown)
    | some i =>
      let deliver := (slot f.ts i).any (·.deliver)
      let f2 := { f with ts := upd f.ts i (Option.map fun t => { t with phase := .acked }) }
      if deliver then
        match firstIdx (·.id == id) f.bs with
        | some j => ({ f2 with bs := upd f2.bs j (Option.map fun b => { b with delivered := true }) }, .ok)
        | none => (f2, .ok)
      else (f2, .ok)
  | .forget id => if anyS (·.id == id) f.bs then (dropB f id, .ok) else (f, .unknown)

/-- The first bundle that is delivered or expired at the clock of `f`. -/
def doneIdx (f : F) : Option Nat := firstIdx (fun b => b.delivered || decide (b.exp ≤ f.now)) f.bs

/-- `poll_retransmit`: the scan of the transfers in slot order. A due transfer on a link that is up gives up (and
the scan goes on) when its sends are used, else it sends again and the scan stops. -/
def retr (up : Nat → Bool) (retry maxS : Nat) : List (Option Transfer) → List (Option Transfer) × Option Act
  | [] => ([], none)
  | none :: r => let (r', a) := retr up retry maxS r; (none :: r', a)
  | some t :: r =>
    match t.phase with
    | .sent 0 s =>
      if up t.peer then
        if maxS ≤ s then
          let (r', a) := retr up retry maxS r
          (some { t with phase := .gaveUp } :: r', a)
        else (some { t with phase := .sent retry (sat8 (s + 1)) } :: r, some (.send t.peer t.bundle t.given true))
      else let (r', a) := retr up retry maxS r; (some t :: r', a)
    | _ => let (r', a) := retr up retry maxS r; (some t :: r', a)

/-- The first (link slot, bundle slot) the spray visits that gets a transfer: link up, bundle held, no transfer to
that peer yet, and either the destination or at least two copies. -/
def cand (f : F) : Option (Nat × Nat) :=
  (List.range f.ls.length).findSome? fun li =>
    match slot f.ls li with
    | some l =>
      if l.up then
        (List.range f.bs.length).findSome? fun bi =>
          match slot f.bs bi with
          | some b =>
            if anyS (fun t => t.bundle == b.id && t.peer == l.peer) f.ts then none
            else if l.peer != b.dest && b.copies / 2 == 0 then none
            else some (li, bi)
          | none => none
      else none
    | none => none

/-- `poll_spray` on a state whose due transfers were already handled. -/
def spray (f : F) : F × Act :=
  match cand f with
  | none => (f, .none)
  | some (li, bi) =>
    match slot f.ls li, slot f.bs bi, freeIdx f.ts with
    | some l, some b, some s =>
      let deliver := l.peer == b.dest
      let given := if deliver then 0 else b.copies / 2
      ({ f with
          ts := upd f.ts s fun _ => some ⟨b.id, l.peer, given, deliver, .sent f.retry 1⟩
          bs := upd f.bs bi (Option.map fun b => { b with copies := b.copies - given }) },
        .send l.peer b.id given false)
    | _, _, _ => (f, .none)

/-- `Forwarder::poll`: a finished or expired bundle is released first, then due retransmissions on links that are
up, then new handovers. -/
def poll (f : F) : F × Act :=
  match doneIdx f with
  | some i =>
    let id := ((slot f.bs i).map (·.id)).getD 0
    (dropB f id, .release id)
  | none =>
    let (ts', a) := retr (upLink f.ls) f.retry f.maxSends f.ts
    match a with
    | some a => ({ f with ts := ts' }, a)
    | none => spray { f with ts := ts' }

/-! ### The observables -/

/-- `copies_held`. -/
def copiesHeld (f : F) (id : Nat) : Option Nat :=
  (firstIdx (·.id == id) f.bs).bind fun i => (slot f.bs i).map (·.copies)

/-- `copies_handed`: the sum of `given` over the transfers of the bundle. -/
def handed (f : F) (id : Nat) : Nat :=
  (f.ts.map fun o => match o with | some t => if t.bundle == id then t.given else 0 | none => 0).sum

/-- `timer_remaining`. -/
def timer (f : F) (peer id : Nat) : Option Nat :=
  (firstIdx (fun t => t.bundle == id && t.peer == peer) f.ts).bind fun i =>
    match (slot f.ts i).map (·.phase) with
    | some (Phase.sent r _) => some r
    | _ => none

end Vinc.DtnForward
