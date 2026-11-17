import Vinc.Axioms

/-!
# The path table and the path of a handshake reply

A model of the path table of `vinc-transport` `conn/path.rs` (`Paths::find`, `new_path_slot` as `learn_path` calls it,
`add_path`, `remove_path`) and of what a connection's datagram input does to it (`conn/recv.rs` `handle_inner`,
`on_handshake`, `process_payload`; `conn/drive.rs` `follow_reply`), as `proofs/tla/PathOps.tla` has it, for any
number of slots `np`. A slot index here counts from 0, as in the code. `learn` is `new_path_slot` as the code has it
since the correction that followed #399: the slot of a path already held, else `learnNew`, the placement without that
look-up (the rule before the correction).

What it proves:

- the bound: a path the connection learns by receiving on it, in either role, is found if it is held, or takes an
  empty slot below `np`, or the place of an unvalidated path that is not the active one, which is then given up, and
  nothing else (`learn_bounded`, `learn_gives_up`, `learnNew_other`); with no such place no path is added
  (`learn_none_iff`); no learning makes a path held twice (`learn_unique`);
- a dialing side takes a reply on any path, held or not (vinc#399): a message that authenticates establishes the
  session on the path it came on, held, validated and active, unless that path is not held and the table has no
  room, and then the table and the active path stay as they were (`rx_auth`, `follow_taken`, `follow_full`); a
  Reply that passed its first checks waits for the key host with its path (`rx_pend`, `inv_rx`), and the key answer
  that establishes moves the session to it by the same rule (`key_taken`);
- before the session is established, a datagram whose message does not authenticate and a key answer that does not
  establish change no path state, on any path (`rx_quiet`, `key_quiet`), and one that fails authentication is
  counted (`rx_bad`);
- the invariant `Inv` (bounded, no path twice, the active path held and validated, a waiting Reply's path
  remembered) holds after every step of a dialing side, a datagram with a 1-RTT packet behind its handshake packet
  included (`inv_rx`, `inv_key`, `inv_add`, `inv_remove`, `inv_app`);
- the rule before #399 drops a dialing side's handshake packet on a path it does not hold, so a reply there never
  establishes the session (`rxOld_drops`, `rxOld_never`);
- the choice of the active path ranks the usable paths by `(unseen, cost, slot)`, an unseen path being a relay path
  that is not seen (a packet sent on it was acknowledged: a fact of its own, which the stamp on a path the session
  leaves does not make true) and is not the active one (or is, after `PTO_FALLBACK` probe timeouts in a row): the
  session moves onto an unseen relay path only when no usable path is seen (`choose_sighted`), an active unseen
  relay path gives way to a seen one (`choose_escapes`), and so does the fall-back of a failed direct path
  (`fall_sighted`); a relay path the session left at the probe-timeout bound with nothing acknowledged on it is not
  the next choice (`choose_no_return`, `stamp_keeps_seen`). A path that takes a slot is unseen and has no cost by
  construction (`learnNew`).

`Vinc.TransportPathJoined` has the reply with a 1-RTT packet behind it in the same datagram, the rule before the
correction (`noLookup_dup`) and the responder; `Vinc.TraceReplyPath` replays the recorded runs of the real code through
these functions.

Not modelled: what a datagram to a standby path carries, and fail-over between relay paths (vinc#625, not built): a
failing relay path is left only for a path that ranks before it. The stamp is the same positive cost on every path.
-/

namespace Vinc.TransportPath

/-- A held path: its id, whether it is validated, whether it runs through a relay (`r`), its cost (`rt`, 0 for none:
`Path::rtt`, the session's estimate stamped on it) and whether it is seen (`seen`: a packet sent on it was
acknowledged; a fact of its own, which a stamp does not make true). A relay path is valid from the moment the
connection tracks it and is never challenged. -/
structure P where
  id : Nat
  v : Bool
  r : Bool
  rt : Nat
  seen : Bool
  deriving DecidableEq, Repr

/-- The table: slot `i` holds a path or nothing; only the slots below `np` are used (`Bounded`). -/
abbrev T := Nat → Option P

/-- The first index below `n` where `f` holds. -/
def first (f : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    match first f n with
    | some i => some i
    | none => if f n then some n else none

theorem first_none {f : Nat → Bool} {n : Nat} (h : first f n = none) : ∀ j, j < n → f j = false := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    cases hk : first f n with
    | some k => simp [first, hk] at h
    | none =>
      have hfn : f n = false := by
        cases hb : f n with
        | false => rfl
        | true => simp [first, hk, hb] at h
      by_cases hjn : j < n
      · exact ih hk j hjn
      · have : j = n := by omega
        subst this
        exact hfn

theorem first_some {f : Nat → Bool} {n i : Nat} (h : first f n = some i) :
    i < n ∧ f i = true ∧ ∀ j, j < i → f j = false := by
  induction n with
  | zero => simp [first] at h
  | succ n ih =>
    cases hk : first f n with
    | some k =>
      have hki : k = i := by simpa [first, hk] using h
      subst hki
      have := ih hk
      exact ⟨by omega, this.2.1, this.2.2⟩
    | none =>
      cases hb : f n with
      | false => simp [first, hk, hb] at h
      | true =>
        have hni : n = i := by simpa [first, hk, hb] using h
        subst hni
        exact ⟨by omega, hb, first_none hk⟩

theorem first_isSome {f : Nat → Bool} {n j : Nat} (hj : j < n) (hf : f j = true) : ∃ i, first f n = some i := by
  cases h : first f n with
  | some i => exact ⟨i, rfl⟩
  | none =>
    have := first_none h j hj
    rw [hf] at this
    cases this

/-- Put `x` in slot `i`. -/
def set (t : T) (i : Nat) (x : Option P) : T := fun j => if j = i then x else t j

/-- Mark the path of slot `i` validated or not. -/
def setV (t : T) (i : Nat) (b : Bool) : T := fun j => if j = i then (t j).map (fun p => { p with v := b }) else t j

/-- Whether slot `i` holds a relay path. -/
def rl (t : T) (i : Nat) : Bool :=
  match t i with
  | some p => p.r
  | none => false

/-- The id slot `j` holds. -/
def idOf (t : T) (j : Nat) : Option Nat := (t j).map P.id

/-- Whether slot `j` holds the path `pid`. -/
def holds (pid : Nat) : Option P → Bool
  | some p => p.id == pid
  | none => false

/-- `Paths::find`. -/
def find (np : Nat) (t : T) (pid : Nat) : Option Nat := first (fun i => holds pid (t i)) np

/-- A slot `new_path_slot` may give up: a path that is not validated and not the active one. -/
def standby (t : T) (act i : Nat) : Bool :=
  (i != act) && match t i with
    | some p => !p.v
    | none => false

/-- `new_path_slot`: the first empty slot, else the first unvalidated path that is not the active one. -/
def slot (np : Nat) (t : T) (act : Nat) : Option Nat :=
  match first (fun i => (t i).isNone) np with
  | some i => some i
  | none => first (standby t act) np

/-- `learnNew_path`: the path joins the table at `slot`, unvalidated; `none` when the table has no room. -/
def learnNew (np : Nat) (t : T) (act pid : Nat) : T × Option Nat :=
  match slot np t act with
  | some i => (set t i (some ⟨pid, false, false, 0, false⟩), some i)
  | none => (t, none)

/-- `learn_path` (`new_path_slot`): the slot of a path already held, its state untouched, else `learnNew`. -/
def learn (np : Nat) (t : T) (act pid : Nat) : T × Option Nat :=
  match find np t pid with
  | some i => (t, some i)
  | none => learnNew np t act pid

theorem learn_found {np : Nat} {t : T} {act pid i : Nat} (h : find np t pid = some i) :
    learn np t act pid = (t, some i) := by
  unfold learn; rw [h]

theorem learn_fresh {np : Nat} {t : T} {act pid : Nat} (h : find np t pid = none) :
    learn np t act pid = learnNew np t act pid := by
  unfold learn; rw [h]

/-- Every slot from `np` on is empty. -/
def Bounded (np : Nat) (t : T) : Prop := ∀ j, np ≤ j → t j = none

/-- No path is held in two slots. -/
def Unique (t : T) : Prop := ∀ i j x, idOf t i = some x → idOf t j = some x → i = j

/-- The same, as a check over the first `np` slots. -/
def uniqueB (np : Nat) (t : T) : Bool :=
  (List.range np).all fun i => (List.range np).all fun j => i == j || idOf t i == none || idOf t i != idOf t j

/-! ## The table -/

theorem slot_spec {np : Nat} {t : T} {act i : Nat} (h : slot np t act = some i) :
    i < np ∧ (t i = none ∨ (i ≠ act ∧ (∃ p, t i = some p ∧ p.v = false) ∧ ∀ j, j < np → t j ≠ none)) := by
  unfold slot at h
  cases hf : first (fun i => (t i).isNone) np with
  | some k =>
    rw [hf] at h
    cases h
    have ⟨h1, h2, _⟩ := first_some hf
    refine ⟨h1, Or.inl ?_⟩
    simpa using h2
  | none =>
    rw [hf] at h
    have ⟨h1, h2, _⟩ := first_some h
    have hfree := first_none hf
    refine ⟨h1, Or.inr ⟨?_, ?_, ?_⟩⟩
    · intro he; subst he; simp [standby] at h2
    · unfold standby at h2
      cases hti : t i with
      | none => simp [hti] at h2
      | some p => exact ⟨p, rfl, by simp [hti] at h2; exact h2.2⟩
    · intro j hj hn
      have := hfree j hj
      simp [hn] at this

theorem slot_none_iff {np : Nat} {t : T} {act : Nat} :
    slot np t act = none ↔ ∀ j, j < np → ∃ p, t j = some p ∧ (j = act ∨ p.v = true) := by
  constructor
  · intro h j hj
    unfold slot at h
    cases hf : first (fun i => (t i).isNone) np with
    | some k => rw [hf] at h; cases h
    | none =>
      rw [hf] at h
      have hfree := first_none hf j hj
      have hst := first_none h j hj
      cases htj : t j with
      | none => simp [htj] at hfree
      | some p =>
        refine ⟨p, rfl, ?_⟩
        by_cases hja : j = act
        · exact Or.inl hja
        · right
          unfold standby at hst
          simp [htj, hja] at hst
          exact hst
  · intro h
    unfold slot
    have hfree : first (fun i => (t i).isNone) np = none := by
      cases hf : first (fun i => (t i).isNone) np with
      | none => rfl
      | some k =>
        have ⟨hk, hk2, _⟩ := first_some hf
        obtain ⟨p, hp, _⟩ := h k hk
        simp [hp] at hk2
    rw [hfree]
    cases hs : first (standby t act) np with
    | none => rfl
    | some k =>
      have ⟨hk, hk2, _⟩ := first_some hs
      obtain ⟨p, hp, hor⟩ := h k hk
      unfold standby at hk2
      rcases hor with hor | hor
      · simp [hor] at hk2
      · simp [hp, hor] at hk2

theorem learnNew_snd {np : Nat} {t : T} {act pid : Nat} : (learnNew np t act pid).2 = slot np t act := by
  unfold learnNew
  cases slot np t act <;> rfl

/-- The slot the path joins holds it, unvalidated. -/
theorem learnNew_at {np : Nat} {t : T} {act pid i : Nat} (h : (learnNew np t act pid).2 = some i) :
    (learnNew np t act pid).1 i = some ⟨pid, false, false, 0, false⟩ := by
  rw [learnNew_snd] at h
  unfold learnNew
  rw [h]
  simp [set]

/-- Every other slot is as it was. -/
theorem learnNew_other {np : Nat} {t : T} {act pid j : Nat} (h : (learnNew np t act pid).2 ≠ some j) :
    (learnNew np t act pid).1 j = t j := by
  rw [learnNew_snd] at h
  unfold learnNew
  cases hs : slot np t act with
  | none => rfl
  | some i =>
    rw [hs] at h
    have hji : j ≠ i := fun e => h (by rw [e])
    simp [set, hji]

/-- The bound: the path joins a slot below `np`. -/
theorem learnNew_bounded {np : Nat} {t : T} {act pid : Nat} (hb : Bounded np t) : Bounded np (learnNew np t act pid).1 := by
  intro j hj
  cases hs : (learnNew np t act pid).2 with
  | none => rw [learnNew_other (by rw [hs]; simp)]; exact hb j hj
  | some i =>
    rw [learnNew_snd] at hs
    have := (slot_spec hs).1
    rw [learnNew_other (by rw [learnNew_snd, hs]; intro e; cases e; omega)]
    exact hb j hj

/-- A path the learning gives up was an unvalidated path that is not the active one, and every slot was held. -/
theorem learnNew_gives_up {np : Nat} {t : T} {act pid i : Nat} {p : P} (hp : t i = some p)
    (hne : (learnNew np t act pid).1 i ≠ some p) : i ≠ act ∧ p.v = false ∧ ∀ j, j < np → t j ≠ none := by
  by_cases hs : (learnNew np t act pid).2 = some i
  · rw [learnNew_snd] at hs
    have := (slot_spec hs).2
    rcases this with h | ⟨ha, ⟨q, hq, hv⟩, hall⟩
    · rw [hp] at h; cases h
    · rw [hp] at hq; cases hq
      exact ⟨ha, hv, hall⟩
  · rw [learnNew_other hs] at hne
    exact absurd hp hne

/-- No path is added exactly when every slot holds the active path or a validated one. -/
theorem learnNew_none_iff {np : Nat} {t : T} {act pid : Nat} :
    (learnNew np t act pid).2 = none ↔ ∀ j, j < np → ∃ p, t j = some p ∧ (j = act ∨ p.v = true) := by
  rw [learnNew_snd]; exact slot_none_iff

theorem find_none {np : Nat} {t : T} {pid : Nat} (hb : Bounded np t) (h : find np t pid = none) :
    ∀ j p, t j = some p → p.id ≠ pid := by
  intro j p hp hid
  by_cases hj : j < np
  · have := first_none h j hj
    simp [holds, hp, hid] at this
  · rw [hb j (by omega)] at hp; cases hp

theorem find_some {np : Nat} {t : T} {pid i : Nat} (h : find np t pid = some i) :
    i < np ∧ ∃ p, t i = some p ∧ p.id = pid := by
  have ⟨h1, h2, _⟩ := first_some h
  refine ⟨h1, ?_⟩
  cases hti : t i with
  | none => simp [hti, holds] at h2
  | some p => exact ⟨p, rfl, by simpa [hti, holds] using h2⟩

/-- Learning a path the table does not hold adds no path twice. -/
theorem learnNew_unique {np : Nat} {t : T} {act pid : Nat} (hb : Bounded np t) (hu : Unique t)
    (hf : find np t pid = none) : Unique (learnNew np t act pid).1 := by
  have hno := find_none hb hf
  have key : ∀ j x, idOf (learnNew np t act pid).1 j = some x →
      ((learnNew np t act pid).2 = some j ∧ x = pid) ∨ ((learnNew np t act pid).2 ≠ some j ∧ idOf t j = some x) := by
    intro j x hx
    by_cases hj : (learnNew np t act pid).2 = some j
    · left
      refine ⟨hj, ?_⟩
      rw [idOf, learnNew_at hj] at hx
      simp at hx; exact hx.symm
    · right
      refine ⟨hj, ?_⟩
      rw [idOf, learnNew_other hj] at hx
      exact hx
  intro i j x hi hj
  rcases key i x hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;> rcases key j x hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
  · rw [hi1] at hj1; cases hj1; rfl
  · subst hi2
    unfold idOf at hj2
    cases htj : t j with
    | none => rw [htj] at hj2; cases hj2
    | some p => rw [htj] at hj2; simp at hj2; exact absurd hj2 (hno j p htj)
  · subst hj2
    unfold idOf at hi2
    cases hti : t i with
    | none => rw [hti] at hi2; cases hi2
    | some p => rw [hti] at hi2; simp at hi2; exact absurd hi2 (hno i p hti)
  · exact hu i j x hi2 hj2

theorem setV_idOf (t : T) (i : Nat) (b : Bool) (j : Nat) : idOf (setV t i b) j = idOf t j := by
  unfold idOf setV
  by_cases h : j = i
  · subst h; cases t j <;> simp
  · simp [h]

theorem setV_none (t : T) (i : Nat) (b : Bool) (j : Nat) : setV t i b j = none ↔ t j = none := by
  unfold setV
  by_cases h : j = i
  · subst h; cases t j <;> simp
  · simp [h]

theorem unique_setV {t : T} (hu : Unique t) (i : Nat) (b : Bool) : Unique (setV t i b) := by
  intro a c x ha hc
  rw [setV_idOf] at ha hc
  exact hu a c x ha hc

theorem bounded_setV {np : Nat} {t : T} (hb : Bounded np t) (i : Nat) (b : Bool) : Bounded np (setV t i b) := by
  intro j hj; rw [setV_none]; exact hb j hj

theorem setV_at (t : T) (i : Nat) (b : Bool) : setV t i b i = (t i).map (fun p => { p with v := b }) := by
  simp [setV]

theorem setV_other (t : T) (i : Nat) (b : Bool) {j : Nat} (h : j ≠ i) : setV t i b j = t j := by
  simp [setV, h]

/-! ## A connection -/

/-- The handshake: the first flight is out, a Reply waits for the key host, or established. -/
inductive Hs where
  | wait
  | key
  | done
  deriving DecidableEq, Repr

/-- What a dialing side's handshake packet completes, as its machine answers it (see `PathOps.tla`). -/
inductive Kind where
  | none
  | bad
  | other
  | rej
  | pend
  | auth
  deriving DecidableEq, Repr

/-- A key answer: the session is established, another request follows, or the Reply failed a check. -/
inductive KeyR where
  | ok
  | more
  | bad
  deriving DecidableEq, Repr

/-- A connection: the table and the active slot, the handshake, `reply_from` (`rf`), the path of the Reply that
waits for the key host (`pend`, a ghost the theorems read), whether the round trip has a sample, whether the active path
failed `PTO_FALLBACK` probe timeouts in a row (`f`), `handshake_dropped`. -/
structure C where
  t : T
  act : Nat := 0
  hs : Hs := .wait
  rf : Option Nat := none
  pend : Option Nat := none
  smp : Bool := false
  f : Bool := false
  hd : Nat := 0

/-- The table of a dialing side when it dials on path `pid` (through a relay when `relay`): the path validated and
active in slot 0. -/
def dial (pid : Nat) (relay : Bool := false) : C :=
  { t := fun j => if j = 0 then some ⟨pid, true, relay, 0, false⟩ else none }

/-- `Path::left` for the slot `a` the session leaves: a relay path is as it was (it stays valid for as long as the
connection tracks it), a direct path is no longer validated. -/
def leave (t : T) (a : Nat) : T := if rl t a then t else setV t a false

/-- `follow_reply`: the reply's path is found or learnt; the session moves to it, validated, and the path it leaves
is left (`leave`): a direct path is no longer validated, a relay path stays valid for as long as the connection
tracks it. With no room it stays on its path. The code takes the round trip sample after this move, so the path it
leaves is not stamped with one (`switch` stamps). -/
def follow (np : Nat) (c : C) : C :=
  match c.rf with
  | none => c
  | some pid =>
    let r := learn np c.t c.act pid
    match r.2 with
    | none => { c with rf := none }
    | some i =>
      if i = c.act then { c with rf := none, t := r.1 }
      else { c with rf := none, t := setV (leave r.1 c.act) i true, act := i }

theorem leave_other (t : T) (a : Nat) {j : Nat} (h : j ≠ a) : leave t a j = t j := by
  unfold leave
  split
  · rfl
  · exact setV_other t a false h

theorem bounded_leave {np : Nat} {t : T} (hb : Bounded np t) (a : Nat) : Bounded np (leave t a) := by
  unfold leave
  split
  · exact hb
  · exact bounded_setV hb _ _

theorem unique_leave {t : T} (hu : Unique t) (a : Nat) : Unique (leave t a) := by
  unfold leave
  split
  · exact hu
  · exact unique_setV hu _ _

/-- `pump` at the establishment: `follow_reply`, and the round trip sample `feed` took (`s`). -/
def establish (np : Nat) (c : C) (s : Bool) : C := follow np { c with hs := .done, pend := none, smp := c.smp || s }

/-- `on_handshake` of a dialing side, once its packet's message is complete. -/
def hsMsg (np : Nat) (c : C) (pid : Nat) (k : Kind) (s : Bool) : C :=
  match c.hs, k with
  | .done, _ => c
  | _, .bad => { c with hd := c.hd + 1 }
  | .wait, .rej => { c with rf := some pid }
  | .wait, .pend => { c with rf := some pid, pend := some pid, hs := .key }
  | _, .auth => establish np { c with rf := some pid } s
  | _, _ => c

/-- A datagram on path `pid` at a dialing side: its handshake packet (`k`) and a 1-RTT packet behind it (`coal`).
`old` is the rule before #399 (a handshake packet on a path it does not hold is dropped). -/
def rx (old : Bool) (np : Nat) (c : C) (pid : Nat) (k : Kind) (coal s : Bool) : C :=
  let known := find np c.t pid
  let c1 := if old && known.isNone then c else hsMsg np c pid k s
  if coal && decide (c1.hs = .done) && known.isNone then { c1 with t := (learn np c1.t c1.act pid).1 } else c1

/-- The rule before the correction that followed #399: as `rx` under the rule of #399, but the 1-RTT packet behind the
handshake packet adds its path without looking it up (`learnNew`), so it adds a path the reply has just added. -/
def rxNoLook (np : Nat) (c : C) (pid : Nat) (k : Kind) (coal s : Bool) : C :=
  let known := find np c.t pid
  let c1 := hsMsg np c pid k s
  if coal && decide (c1.hs = .done) && known.isNone then { c1 with t := (learnNew np c1.t c1.act pid).1 } else c1

/-- `on_key_response`. -/
def key (np : Nat) (c : C) (r : KeyR) (s : Bool) : C :=
  match c.hs, r with
  | .key, .ok => establish np c s
  | .key, .bad => { c with hs := .wait, pend := none, hd := c.hd + 1 }
  | _, _ => c

/-- `add_path`: the table and whether it took the path (`false` is `TooMany`). -/
def addPath (np : Nat) (c : C) (pid : Nat) : C × Bool :=
  match find np c.t pid with
  | some _ => (c, true)
  | none => let l := learn np c.t c.act pid; ({ c with t := l.1 }, l.2.isSome)

/-- `remove_path`: 0 removed, 1 unknown, 2 the active path (refused). -/
def removePath (np : Nat) (c : C) (pid : Nat) : C × Nat :=
  match find np c.t pid with
  | none => (c, 1)
  | some i => if i = c.act then (c, 2) else ({ c with t := set c.t i none }, 0)

/-- An established connection, either role, takes a 1-RTT packet on a path it does not hold (`process_payload`). -/
def app (np : Nat) (c : C) (pid : Nat) : C :=
  if c.hs = .done ∧ find np c.t pid = none then { c with t := (learn np c.t c.act pid).1 } else c

/-- A responder's handshake datagram on path `pid` (`handle_inner`): it learns a path it does not hold while in its
handshake or holding none; `est` establishes the session, which validates the active path. -/
def respRx (np : Nat) (c : C) (pid : Nat) (est : Bool) : C :=
  let empty := (List.range np).all fun j => (c.t j).isNone
  let c1 := if find np c.t pid = none ∧ (empty = true ∨ c.hs ≠ .done) then { c with t := (learn np c.t c.act pid).1 } else c
  if est = true ∧ c1.hs ≠ .done ∧ (find np c1.t pid).isSome ∧ (c1.t c1.act).isSome then
    { c1 with hs := .done, t := setV c1.t c1.act true }
  else c1

/-! ## What a dialing side's steps do -/

/-- The active slot holds a validated path. -/
def ActiveV (c : C) : Prop := ∃ p, c.t c.act = some p ∧ p.v = true

/-- The invariant of a dialing side. -/
structure Inv (np : Nat) (c : C) : Prop where
  bounded : Bounded np c.t
  unique : Unique c.t
  act_lt : c.act < np
  active : ActiveV c
  waits : c.hs = .key → c.pend.isSome ∧ c.rf = c.pend

/-- The session `c'` is on path `pid`: held, validated, in the active slot. -/
def On (c' : C) (pid : Nat) : Prop := ∃ p, c'.t c'.act = some p ∧ p.id = pid ∧ p.v = true

theorem inv_dial (np pid : Nat) (relay : Bool) (h : 0 < np) : Inv np (dial pid relay) := by
  refine ⟨?_, ?_, h, ⟨⟨pid, true, relay, 0, false⟩, by simp [dial], rfl⟩, by simp [dial]⟩
  · intro j hj; simp [dial]; omega
  · intro i j x hi hj
    simp [dial, idOf] at hi hj
    omega

/-! ### `follow`, case by case -/

theorem follow_none (np : Nat) (c : C) (h : c.rf = none) : follow np c = c := by
  unfold follow; rw [h]

theorem follow_found {np : Nat} {c : C} {pid i : Nat} (hrf : c.rf = some pid) (hf : find np c.t pid = some i) :
    follow np c = if i = c.act then { c with rf := none, t := c.t }
      else { c with rf := none, t := setV (leave c.t c.act) i true, act := i } := by
  unfold follow; rw [hrf]; dsimp only; rw [learn_found hf]

theorem follow_learnt {np : Nat} {c : C} {pid i : Nat} (hrf : c.rf = some pid) (hf : find np c.t pid = none)
    (hl : (learnNew np c.t c.act pid).2 = some i) :
    follow np c = if i = c.act then { c with rf := none, t := (learnNew np c.t c.act pid).1 }
      else { c with
        rf := none
        t := setV (leave (learnNew np c.t c.act pid).1 c.act) i true
        act := i } := by
  unfold follow; rw [hrf]; dsimp only; rw [learn_fresh hf, hl]

theorem follow_noroom {np : Nat} {c : C} {pid : Nat} (hrf : c.rf = some pid) (hf : find np c.t pid = none)
    (hl : (learnNew np c.t c.act pid).2 = none) : follow np c = { c with rf := none } := by
  unfold follow; rw [hrf]; dsimp only; rw [learn_fresh hf, hl]

/-- `follow` moves nothing but the table, the active slot and `reply_from`. -/
theorem follow_keeps (np : Nat) (c : C) :
    (follow np c).hs = c.hs ∧ (follow np c).smp = c.smp ∧ (follow np c).hd = c.hd ∧ (follow np c).pend = c.pend := by
  cases hrf : c.rf with
  | none => rw [follow_none np c hrf]; exact ⟨rfl, rfl, rfl, rfl⟩
  | some pid =>
    cases hf : find np c.t pid with
    | some i => rw [follow_found hrf hf]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    | none =>
      cases hl : (learnNew np c.t c.act pid).2 with
      | none => rw [follow_noroom hrf hf hl]; exact ⟨rfl, rfl, rfl, rfl⟩
      | some i => rw [follow_learnt hrf hf hl]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A slot `new_path_slot` picks is never the active one while that holds a path. -/
theorem slot_ne_act {np : Nat} {t : T} {act i : Nat} {pa : P} (hpa : t act = some pa) (hs : slot np t act = some i) :
    i ≠ act := by
  rcases (slot_spec hs).2 with h | ⟨h, _⟩
  · intro e; subst e; rw [hpa] at h; cases h
  · exact h

/-- The reply's path is held or there is room for it: the session is on it afterwards. -/
theorem follow_taken {np : Nat} {c : C} {pid : Nat} (hi : Inv np c) (hrf : c.rf = some pid)
    (room : (find np c.t pid).isSome ∨ (slot np c.t c.act).isSome) : On (follow np c) pid := by
  obtain ⟨pa, hpa, hva⟩ := hi.active
  cases hf : find np c.t pid with
  | some i =>
    obtain ⟨_, p, hp, hpid⟩ := find_some hf
    rw [follow_found hrf hf]
    by_cases hia : i = c.act
    · rw [ite_eq_left hia]
      subst hia
      have hpp : p = pa := by rw [hp] at hpa; exact Option.some.inj hpa
      subst hpp
      exact ⟨p, hp, hpid, hva⟩
    · rw [ite_eq_right hia]
      refine ⟨{ p with v := true }, ?_, hpid, rfl⟩
      show setV (leave c.t c.act) i true i = _
      rw [setV_at, leave_other _ _ hia, hp]
      rfl
  | none =>
    rw [hf] at room
    have hsome : (slot np c.t c.act).isSome := by simpa using room
    obtain ⟨i, hs⟩ := Option.isSome_iff_exists.mp hsome
    have hia : i ≠ c.act := slot_ne_act hpa hs
    have hl : (learnNew np c.t c.act pid).2 = some i := by rw [learnNew_snd, hs]
    rw [follow_learnt hrf hf hl, ite_eq_right hia]
    refine ⟨⟨pid, true, false, 0, false⟩, ?_, rfl, rfl⟩
    show setV (leave (learnNew np c.t c.act pid).1 c.act) i true i = _
    rw [setV_at, leave_other _ _ hia, learnNew_at hl]
    rfl

/-- The reply's path is not held and there is no room: nothing of the table moves. -/
theorem follow_full {np : Nat} {c : C} {pid : Nat} (hrf : c.rf = some pid) (hf : find np c.t pid = none)
    (hs : slot np c.t c.act = none) : (follow np c).t = c.t ∧ (follow np c).act = c.act := by
  have hl : (learnNew np c.t c.act pid).2 = none := by rw [learnNew_snd, hs]
  rw [follow_noroom hrf hf hl]
  exact ⟨rfl, rfl⟩

theorem inv_follow {np : Nat} {c : C} (hi : Inv np c) (hhs : c.hs ≠ .key) : Inv np (follow np c) := by
  obtain ⟨pa, hpa, hva⟩ := hi.active
  have hw : (follow np c).hs = .key → (follow np c).pend.isSome ∧ (follow np c).rf = (follow np c).pend := by
    intro h; rw [(follow_keeps np c).1] at h; exact absurd h hhs
  cases hrf : c.rf with
  | none => rw [follow_none np c hrf]; exact hi
  | some pid =>
    cases hf : find np c.t pid with
    | some i =>
      obtain ⟨hil, p, hp, _⟩ := find_some hf
      have he := follow_found hrf hf
      by_cases hia : i = c.act
      · rw [ite_eq_left hia] at he
        refine ⟨by rw [he]; exact hi.bounded, by rw [he]; exact hi.unique, by rw [he]; exact hi.act_lt,
          by rw [he]; exact ⟨pa, hpa, hva⟩, hw⟩
      · rw [ite_eq_right hia] at he
        refine ⟨by rw [he]; exact bounded_setV (bounded_leave hi.bounded _) _ _,
          by rw [he]; exact unique_setV (unique_leave hi.unique _) _ _, by rw [he]; exact hil,
          ⟨{ p with v := true }, ?_, rfl⟩, hw⟩
        rw [he]
        show setV (leave c.t c.act) i true i = _
        rw [setV_at, leave_other _ _ hia, hp]
        rfl
    | none =>
      cases hl : (learnNew np c.t c.act pid).2 with
      | none =>
        have he := follow_noroom hrf hf hl
        exact ⟨by rw [he]; exact hi.bounded, by rw [he]; exact hi.unique, by rw [he]; exact hi.act_lt,
          by rw [he]; exact ⟨pa, hpa, hva⟩, hw⟩
      | some i =>
        have hs : slot np c.t c.act = some i := by rw [← learnNew_snd, hl]
        have hil := (slot_spec hs).1
        have hia : i ≠ c.act := slot_ne_act hpa hs
        have he := follow_learnt hrf hf hl
        rw [ite_eq_right hia] at he
        refine ⟨by rw [he]; exact bounded_setV (bounded_leave (learnNew_bounded hi.bounded) _) _ _,
          by rw [he]; exact unique_setV (unique_leave (learnNew_unique hi.bounded hi.unique hf) _) _ _,
          by rw [he]; exact hil, ⟨⟨pid, true, false, 0, false⟩, ?_, rfl⟩, hw⟩
        rw [he]
        show setV (leave (learnNew np c.t c.act pid).1 c.act) i true i = _
        rw [setV_at, leave_other _ _ hia, learnNew_at hl]
        rfl

/-! ### A datagram and a key answer at a dialing side -/

theorem hsMsg_done {np : Nat} {c : C} {pid : Nat} {k : Kind} {s : Bool} (h : c.hs = .done) : hsMsg np c pid k s = c := by
  unfold hsMsg; rw [h]

theorem hsMsg_auth {np : Nat} {c : C} {pid : Nat} {s : Bool} (h : c.hs ≠ .done) :
    hsMsg np c pid .auth s = establish np { c with rf := some pid } s := by
  unfold hsMsg; cases hh : c.hs <;> simp_all

theorem rx_plain (np : Nat) (c : C) (pid : Nat) (k : Kind) (s : Bool) :
    rx false np c pid k false s = hsMsg np c pid k s := by
  simp [rx]

/-- A message that authenticates, on any path: the session is established, on the reply's path if it is held or the
table has room for it, else on its own path with the table as it was. -/
theorem rx_auth {np : Nat} {c : C} {pid : Nat} (hi : Inv np c) (hhs : c.hs ≠ .done) (s : Bool) :
    (rx false np c pid .auth false s).hs = .done ∧
      (((find np c.t pid).isSome ∨ (slot np c.t c.act).isSome) → On (rx false np c pid .auth false s) pid) ∧
      (find np c.t pid = none → slot np c.t c.act = none →
        (rx false np c pid .auth false s).t = c.t ∧ (rx false np c pid .auth false s).act = c.act) := by
  rw [rx_plain, hsMsg_auth hhs]
  have hi0 : Inv np { c with rf := some pid, hs := .done, pend := none, smp := c.smp || s } :=
    ⟨hi.bounded, hi.unique, hi.act_lt, hi.active, fun h => by cases h⟩
  refine ⟨(follow_keeps np _).1, fun room => follow_taken hi0 rfl room, fun hf hs => follow_full rfl hf hs⟩

/-- A Reply that passed its first checks, on any path, waits for the key host with its path. -/
theorem rx_pend {np : Nat} {c : C} {pid : Nat} (hw : c.hs = .wait) (coal s : Bool) :
    rx false np c pid .pend coal s = { c with rf := some pid, pend := some pid, hs := .key } := by
  simp [rx, hsMsg, hw]

theorem hsMsg_quiet {np : Nat} {c : C} {pid : Nat} {k : Kind} {s : Bool} (hhs : c.hs ≠ .done) (hk : k ≠ .auth) :
    (hsMsg np c pid k s).t = c.t ∧ (hsMsg np c pid k s).act = c.act ∧ (hsMsg np c pid k s).smp = c.smp ∧
      (hsMsg np c pid k s).hs ≠ .done := by
  cases hh : c.hs <;> cases k <;> simp_all [hsMsg]

/-- With no establishment in it, the 1-RTT packet behind changes nothing (it is held for the keys). -/
theorem rx_tail {np : Nat} {c c1 : C} {pid : Nat} {coal : Bool} (h : c1.hs ≠ .done) :
    (if coal && decide (c1.hs = .done) && (find np c.t pid).isNone then
      { c1 with t := (learn np c1.t c1.act pid).1 } else c1) = c1 := by
  simp [h]

/-- Before the session is established, a datagram whose message does not authenticate changes no path state,
on any path and under either rule. -/
theorem rx_quiet {np : Nat} {c : C} {pid : Nat} {k : Kind} (hhs : c.hs ≠ .done) (hk : k ≠ .auth)
    (old coal s : Bool) :
    (rx old np c pid k coal s).t = c.t ∧ (rx old np c pid k coal s).act = c.act ∧
      (rx old np c pid k coal s).smp = c.smp ∧ (rx old np c pid k coal s).hs ≠ .done := by
  unfold rx
  dsimp only
  by_cases ho : (old && (find np c.t pid).isNone) = true
  · rw [ite_eq_left ho, rx_tail hhs]
    exact ⟨rfl, rfl, rfl, hhs⟩
  · rw [ite_eq_right ho, rx_tail (hsMsg_quiet hhs hk).2.2.2]
    exact hsMsg_quiet hhs hk

/-- One that fails authentication is counted, on any path. -/
theorem rx_bad {np : Nat} {c : C} {pid : Nat} (hhs : c.hs ≠ .done) (coal s : Bool) :
    (rx false np c pid .bad coal s).hd = c.hd + 1 := by
  have hm : hsMsg np c pid .bad s = { c with hd := c.hd + 1 } := by
    unfold hsMsg; cases hh : c.hs <;> simp_all
  have hq := (hsMsg_quiet (np := np) (pid := pid) (s := s) hhs (k := .bad) (by simp)).2.2.2
  unfold rx
  dsimp only
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [rx_tail hq, hm]

/-- The rule before #399: a handshake packet on a path a dialing side does not hold is dropped, so a reply there never
establishes the session. -/
theorem rxOld_drops {np : Nat} {c : C} {pid : Nat} (hf : find np c.t pid = none) (k : Kind) (s : Bool) :
    rx true np c pid k false s = c := by
  simp [rx, hf]

theorem rxOld_never {np : Nat} {c : C} {pid : Nat} (hf : find np c.t pid = none) (hhs : c.hs ≠ .done) (s : Bool) :
    (rx true np c pid .auth false s).hs ≠ .done := by
  rw [rxOld_drops hf]; exact hhs

/-- The key answer that establishes moves the session to the path of the Reply that waited, by the same rule. -/
theorem key_taken {np : Nat} {c : C} (hi : Inv np c) (hk : c.hs = .key) (s : Bool) :
    ∃ pid, c.pend = some pid ∧ (key np c .ok s).hs = .done ∧
      (((find np c.t pid).isSome ∨ (slot np c.t c.act).isSome) → On (key np c .ok s) pid) ∧
      (find np c.t pid = none → slot np c.t c.act = none →
        (key np c .ok s).t = c.t ∧ (key np c .ok s).act = c.act) := by
  obtain ⟨hps, hrf⟩ := hi.waits hk
  obtain ⟨pid, hpid⟩ := Option.isSome_iff_exists.mp hps
  have hkey : key np c .ok s = follow np { c with hs := .done, pend := none, smp := c.smp || s } := by
    unfold key; rw [hk]; rfl
  have hi0 : Inv np { c with hs := .done, pend := none, smp := c.smp || s } :=
    ⟨hi.bounded, hi.unique, hi.act_lt, hi.active, fun h => by cases h⟩
  have hrf0 : ({ c with hs := .done, pend := none, smp := c.smp || s } : C).rf = some pid := by
    show c.rf = some pid; rw [hrf, hpid]
  rw [hkey]
  exact ⟨pid, hpid, (follow_keeps np _).1, fun room => follow_taken hi0 hrf0 room,
    fun hf hs => follow_full hrf0 hf hs⟩

/-- A key answer that does not establish changes no path state. -/
theorem key_quiet {np : Nat} {c : C} {r : KeyR} (hr : r ≠ .ok) (s : Bool) :
    (key np c r s).t = c.t ∧ (key np c r s).act = c.act ∧ (key np c r s).smp = c.smp ∧
      (c.hs ≠ .done → (key np c r s).hs ≠ .done) := by
  cases hh : c.hs <;> cases r <;> simp_all [key]

/-! ## The invariant through every step of a dialing side -/

/-- The establishment keeps the invariant: it needs only the table's part. -/
theorem inv_establish {np : Nat} (c : C) (s : Bool) (hb : Bounded np c.t) (hu : Unique c.t) (ha : c.act < np)
    (hv : ActiveV c) : Inv np (establish np c s) :=
  inv_follow (c := { c with hs := .done, pend := none, smp := c.smp || s }) ⟨hb, hu, ha, hv, fun h => by cases h⟩
    (by simp)

theorem inv_hsMsg {np : Nat} {c : C} {pid : Nat} {k : Kind} (hi : Inv np c) (s : Bool) :
    Inv np (hsMsg np c pid k s) := by
  have hw := hi.waits
  cases hh : c.hs <;> cases k <;> simp only [hsMsg, hh]
  all_goals first
    | exact inv_establish _ s hi.bounded hi.unique hi.act_lt hi.active
    | exact ⟨hi.bounded, hi.unique, hi.act_lt, hi.active, fun h => by simp_all⟩

theorem inv_key {np : Nat} {c : C} {r : KeyR} (hi : Inv np c) (s : Bool) : Inv np (key np c r s) := by
  have hw := hi.waits
  cases hh : c.hs <;> cases r <;> simp only [key, hh]
  all_goals first
    | exact inv_establish _ s hi.bounded hi.unique hi.act_lt hi.active
    | exact ⟨hi.bounded, hi.unique, hi.act_lt, hi.active, fun h => by simp_all⟩

theorem learnNew_keeps_active {np : Nat} {t : T} {act pid : Nat} {pa : P} (hpa : t act = some pa) :
    (learnNew np t act pid).1 act = some pa := by
  by_cases hl : (learnNew np t act pid).2 = some act
  · rw [learnNew_snd] at hl
    exact absurd rfl (slot_ne_act hpa hl)
  · rw [learnNew_other hl, hpa]

/-! ### Learning with the look-up (`learn_path` since the correction that followed #399) -/

theorem learn_bounded {np : Nat} {t : T} {act pid : Nat} (hb : Bounded np t) : Bounded np (learn np t act pid).1 := by
  cases h : find np t pid with
  | some _ => rw [learn_found h]; exact hb
  | none => rw [learn_fresh h]; exact learnNew_bounded hb

/-- No step that learns a path makes a path held twice: a path already held is found, not added. -/
theorem learn_unique {np : Nat} {t : T} {act pid : Nat} (hb : Bounded np t) (hu : Unique t) :
    Unique (learn np t act pid).1 := by
  cases h : find np t pid with
  | some _ => rw [learn_found h]; exact hu
  | none => rw [learn_fresh h]; exact learnNew_unique hb hu h

theorem learn_gives_up {np : Nat} {t : T} {act pid i : Nat} {p : P} (hp : t i = some p)
    (hne : (learn np t act pid).1 i ≠ some p) : i ≠ act ∧ p.v = false ∧ ∀ j, j < np → t j ≠ none := by
  cases h : find np t pid with
  | some _ => rw [learn_found h] at hne; exact absurd hp hne
  | none => rw [learn_fresh h] at hne; exact learnNew_gives_up hp hne

/-- No path is added exactly when the path is not held and every slot holds the active path or a validated one. -/
theorem learn_none_iff {np : Nat} {t : T} {act pid : Nat} :
    (learn np t act pid).2 = none ↔ find np t pid = none ∧ ∀ j, j < np → ∃ p, t j = some p ∧ (j = act ∨ p.v = true) := by
  cases h : find np t pid with
  | some _ => rw [learn_found h]; simp
  | none => rw [learn_fresh h, learnNew_none_iff]; simp

theorem learn_keeps_active {np : Nat} {t : T} {act pid : Nat} {pa : P} (hpa : t act = some pa) :
    (learn np t act pid).1 act = some pa := by
  cases h : find np t pid with
  | some _ => rw [learn_found h]; exact hpa
  | none => rw [learn_fresh h]; exact learnNew_keeps_active hpa

theorem inv_learn {np : Nat} {c : C} {pid : Nat} (hi : Inv np c) :
    Inv np { c with t := (learn np c.t c.act pid).1 } := by
  obtain ⟨pa, hpa, hva⟩ := hi.active
  exact ⟨learn_bounded hi.bounded, learn_unique hi.bounded hi.unique, hi.act_lt,
    ⟨pa, learn_keeps_active hpa, hva⟩, hi.waits⟩

/-- The 1-RTT packet behind the handshake packet keeps the invariant: learning looks the path up. -/
theorem inv_tail {np : Nat} {c c1 : C} {pid : Nat} {coal : Bool} (h1 : Inv np c1) :
    Inv np (if coal && decide (c1.hs = .done) && (find np c.t pid).isNone then
      { c1 with t := (learn np c1.t c1.act pid).1 } else c1) := by
  split
  · exact inv_learn h1
  · exact h1

theorem inv_rx {np : Nat} {c : C} {pid : Nat} {k : Kind} (hi : Inv np c) (old coal s : Bool) :
    Inv np (rx old np c pid k coal s) := by
  have h1 : Inv np (if old && (find np c.t pid).isNone then c else hsMsg np c pid k s) := by
    split
    · exact hi
    · exact inv_hsMsg hi s
  exact inv_tail h1

theorem inv_add {np : Nat} {c : C} {pid : Nat} (hi : Inv np c) : Inv np (addPath np c pid).1 := by
  unfold addPath
  cases hf : find np c.t pid with
  | some _ => exact hi
  | none => exact inv_learn hi

theorem inv_app {np : Nat} {c : C} {pid : Nat} (hi : Inv np c) : Inv np (app np c pid) := by
  unfold app
  split
  · exact inv_learn hi
  · exact hi

theorem inv_remove {np : Nat} {c : C} {pid : Nat} (hi : Inv np c) : Inv np (removePath np c pid).1 := by
  unfold removePath
  cases hf : find np c.t pid with
  | none => exact hi
  | some i =>
    show Inv np (if i = c.act then (c, 2) else ({ c with t := set c.t i none }, 0)).1
    by_cases hia : i = c.act
    · rw [ite_eq_left hia]; exact hi
    · rw [ite_eq_right hia]
      obtain ⟨pa, hpa, hva⟩ := hi.active
      have hid : ∀ a x, idOf (set c.t i none) a = some x → idOf c.t a = some x := by
        intro a x ha
        unfold idOf set at ha
        by_cases h : a = i
        · rw [ite_eq_left h] at ha; cases ha
        · rw [ite_eq_right h] at ha; exact ha
      refine ⟨?_, fun a b x ha hb => hi.unique a b x (hid a x ha) (hid b x hb), hi.act_lt, ⟨pa, ?_, hva⟩, hi.waits⟩
      · intro j hj
        show set c.t i none j = none
        unfold set
        split
        · rfl
        · exact hi.bounded j hj
      · show set c.t i none c.act = some pa
        unfold set
        rw [ite_eq_right (Ne.symm hia), hpa]

/-! ## The choice of the active path

`conn/path.rs` `rank`, `best_path`, `choose_path`, `set_path_info`, `switch_active` and the fall-back of
`conn/path_fall.rs`, as `proofs/tla/PathOps.tla` has them (`Choose`, `SetInfo`, `Fallback`, `Timer`). The usable paths
(held and validated) are ranked by `(unseen, cost, slot)`, least first. A relay path that is not seen is unseen when
it is not the active path, or is the active path after `PTO_FALLBACK` probe timeouts in a row. So a seen path, or a
direct path, always ranks ahead of an unseen one: the session moves onto an unseen relay path only when no usable
path is seen (`choose_sighted`), an active unseen relay path gives way to a seen one (`choose_escapes`) and so does
the fall-back of a failed direct path (`fall_sighted`). -/

/-- Whether slot `i` holds a validated path (a usable one). -/
def usable (t : T) (i : Nat) : Bool :=
  match t i with
  | some p => p.v
  | none => false

/-- Whether slot `i` holds a validated relay path (`relay_fallback` takes the least ranked of these first). -/
def vrel (t : T) (i : Nat) : Bool :=
  match t i with
  | some p => p.v && p.r
  | none => false

/-- The first key of the rank: slot `i` holds a relay path that is not seen and is not the active path, or is the
active path after `PTO_FALLBACK` probe timeouts in a row (`f`). The seen fact is read, not the cost: a stamp gives a
path a cost and does not make it seen. -/
def unseen (t : T) (act : Nat) (f : Bool) (i : Nat) : Bool :=
  match t i with
  | some p => p.r && !p.seen && (i != act || f)
  | none => false

/-- The cost of a path: its round trip, and the relay penalty `pen` for a relay path. -/
def cost (pen : Nat) (t : T) (i : Nat) : Nat :=
  match t i with
  | some p => p.rt + if p.r then pen else 0
  | none => 0

/-- The rank of slot `i`: `(unseen, cost, slot)`. -/
def rank (pen : Nat) (t : T) (act : Nat) (f : Bool) (i : Nat) : Nat × Nat × Nat :=
  (if unseen t act f i then 1 else 0, cost pen t i, i)

/-- The order of ranks: the least first, lexicographically. -/
def Lt3 (a b : Nat × Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

instance (a b : Nat × Nat × Nat) : Decidable (Lt3 a b) := by unfold Lt3; infer_instance

theorem Lt3_trans {a b c : Nat × Nat × Nat} (h1 : Lt3 a b) (h2 : Lt3 b c) : Lt3 a c := by
  unfold Lt3 at *; omega

/-- The slot below `n` where `ok` holds of least key `k`; a later slot replaces an earlier one only when its key is
strictly less. -/
def least (ok : Nat → Bool) (k : Nat → Nat × Nat × Nat) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    match least ok k n with
    | none => if ok n then some n else none
    | some j => if ok n && decide (Lt3 (k n) (k j)) then some n else some j

theorem least_none {ok : Nat → Bool} {k : Nat → Nat × Nat × Nat} {n : Nat} (h : least ok k n = none) :
    ∀ j, j < n → ok j = false := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    cases hl : least ok k n with
    | some b =>
      simp only [least, hl] at h
      split at h <;> cases h
    | none =>
      cases hon : ok n with
      | true => simp [least, hl, hon] at h
      | false =>
        by_cases hjn : j < n
        · exact ih hl j hjn
        · have : j = n := by omega
          subst this
          exact hon

theorem least_isSome {ok : Nat → Bool} {k : Nat → Nat × Nat × Nat} {n : Nat} (h : ∃ j, j < n ∧ ok j = true) :
    ∃ b, least ok k n = some b := by
  cases hl : least ok k n with
  | some b => exact ⟨b, rfl⟩
  | none =>
    obtain ⟨j, hj, hok⟩ := h
    have := least_none hl j hj
    rw [hok] at this
    cases this

/-- The slot found is below `n`, where `ok` holds, and no slot below `n` where `ok` holds has a lesser key. -/
theorem least_spec {ok : Nat → Bool} {k : Nat → Nat × Nat × Nat} {n b : Nat} (h : least ok k n = some b) :
    b < n ∧ ok b = true ∧ ∀ j, j < n → ok j = true → ¬ Lt3 (k j) (k b) := by
  induction n generalizing b with
  | zero => simp [least] at h
  | succ n ih =>
    cases hl : least ok k n with
    | none =>
      have hall := least_none hl
      cases hon : ok n with
      | false => simp [least, hl, hon] at h
      | true =>
        simp [least, hl, hon] at h
        subst h
        refine ⟨by omega, hon, ?_⟩
        intro j hj hjok
        by_cases hjn : j < n
        · rw [hall j hjn] at hjok
          cases hjok
        · have : j = n := by omega
          subst this
          intro hlt
          unfold Lt3 at hlt
          omega
    | some m =>
      obtain ⟨hmn, hmok, hmin⟩ := ih hl
      by_cases hc : ok n = true ∧ Lt3 (k n) (k m)
      · have hs : least ok k (n + 1) = some n := by simp [least, hl, hc.1, hc.2]
        rw [hs] at h
        have hb := Option.some.inj h
        subst hb
        refine ⟨by omega, hc.1, ?_⟩
        intro j hj hjok
        by_cases hjn : j < n
        · intro hlt
          exact hmin j hjn hjok (Lt3_trans hlt hc.2)
        · have : j = n := by omega
          subst this
          intro hlt
          unfold Lt3 at hlt
          omega
      · have hc' : ¬ ((ok n && decide (Lt3 (k n) (k m))) = true) := by simpa using hc
        have hs : least ok k (n + 1) = some m := by
          simp only [least, hl]
          rw [ite_eq_right hc']
        rw [hs] at h
        have hb := Option.some.inj h
        subst hb
        refine ⟨by omega, hmok, ?_⟩
        intro j hj hjok
        by_cases hjn : j < n
        · exact hmin j hjn hjok
        · have : j = n := by omega
          subst this
          intro hlt
          exact hc ⟨hjok, hlt⟩

/-- `best_path`: the usable slot of least rank. -/
def best (np pen : Nat) (t : T) (act : Nat) (f : Bool) : Option Nat :=
  least (usable t) (rank pen t act f) np

/-- The last slot below `n` where `ok` holds. -/
def lastOf (ok : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 => if ok n then some n else lastOf ok n

/-- `relay_fallback`: the validated relay path of least rank, else the last relay path. -/
def fallTo (np pen : Nat) (t : T) (act : Nat) (f : Bool) : Option Nat :=
  match least (vrel t) (rank pen t act f) np with
  | some i => some i
  | none => lastOf (rl t) np

/-- `switch_active`'s stamp: the path the session leaves takes the connection's sample as its own cost, and is not
seen for that. Any positive one will do: two stamped relay paths are not compared by the model. -/
def stamp (t : T) (a : Nat) : T := fun j => if j = a then (t j).map (fun p => { p with rt := 1 }) else t j

/-- `switch_active`: the session moves to slot `i` by its own choice, and the path it leaves is stamped when the
connection has a sample. -/
def switch (c : C) (i : Nat) : C :=
  if i == c.act || (c.t i).isNone then c else { c with t := if c.smp then stamp c.t c.act else c.t, act := i }

/-- `choose_path`: to the best path at once from a relay path (or from none); from a direct path only for a gain,
which the model leaves out. -/
def choose (np pen : Nat) (c : C) : C :=
  match best np pen c.t c.act c.f with
  | none => c
  | some b => if (c.t c.act).isNone || rl c.t c.act then switch c b else c

/-- `fail_over`: the active direct path failed `PTO_FALLBACK` probe timeouts in a row; it is no longer validated and
the session moves to the relay path `fallTo` names. With no relay path nothing moves (the code challenges the failed
path, which the model leaves out). -/
def fallback (np pen : Nat) (c : C) : C :=
  match c.t c.act, fallTo np pen c.t c.act c.f with
  | some p, some r => if c.f && !p.r && p.v then switch { c with t := setV c.t c.act false } r else c
  | _, _ => c

/-- A timer pass: the fall-back of a failed direct path, then the choice (`on_path_timers`). -/
def timer (np pen : Nat) (c : C) : C := choose np pen (fallback np pen c)

/-- `set_path_info` for the path `pid` the connection holds: the new kind (`rel`: a relay path) first, then the choice,
then a path named a relay's is validated as every relay path is. -/
def setInfo (np pen : Nat) (c : C) (pid : Nat) (rel : Bool) : C :=
  match find np c.t pid with
  | none => c
  | some i =>
    match c.t i with
    | none => c
    | some p =>
      if p.r = rel then c
      else
        let c1 := choose np pen { c with t := set c.t i (some { p with r := rel }) }
        if rel then { c1 with t := setV c1.t i true } else c1

/-- A usable path is not an unseen relay path only if the choice may take it: the first key puts every seen path ahead
of every unseen one. -/
theorem best_sighted {np pen : Nat} {t : T} {act : Nat} {f : Bool} {b : Nat} (h : best np pen t act f = some b)
    (hu : unseen t act f b = true) : ∀ j, j < np → usable t j = true → unseen t act f j = true := by
  obtain ⟨_, _, hmin⟩ := least_spec h
  intro j hj hok
  refine Classical.byContradiction fun hn => ?_
  have hn' : unseen t act f j = false := by cases hh : unseen t act f j <;> simp_all
  apply hmin j hj hok
  unfold Lt3 rank
  simp [hu, hn']

/-- The choice moves the session only to the path `best` names. -/
theorem choose_moves {np pen : Nat} {c : C} {b : Nat} (h : (choose np pen c).act = b) (hne : b ≠ c.act) :
    best np pen c.t c.act c.f = some b := by
  unfold choose at h
  cases hb : best np pen c.t c.act c.f with
  | none =>
    simp only [hb] at h
    exact absurd h.symm hne
  | some b' =>
    simp only [hb] at h
    by_cases hg : ((c.t c.act).isNone || rl c.t c.act) = true
    · rw [ite_eq_left hg] at h
      unfold switch at h
      by_cases h1 : (b' == c.act || (c.t b').isNone) = true
      · rw [ite_eq_left h1] at h
        exact absurd h.symm hne
      · rw [ite_eq_right h1] at h
        have hb' : b' = b := h
        rw [hb']
    · rw [ite_eq_right hg] at h
      exact absurd h.symm hne

/-- The session moves onto an unseen relay path only from an active path that is not usable or has failed its probe
timeouts, and only when no usable path is seen. -/
theorem choose_sighted {np pen : Nat} {c : C} {b : Nat} (hl : c.act < np) (h : (choose np pen c).act = b)
    (hne : b ≠ c.act) (hu : unseen c.t c.act c.f b = true) :
    (usable c.t c.act = false ∨ c.f = true) ∧
      ∀ j, j < np → usable c.t j = true → unseen c.t c.act c.f j = true := by
  have hall := best_sighted (choose_moves h hne) hu
  refine ⟨?_, hall⟩
  by_cases hf : c.f = true
  · exact Or.inr hf
  · left
    have hf' : c.f = false := by cases hh : c.f <;> simp_all
    refine Classical.byContradiction fun hus => ?_
    have hus' : usable c.t c.act = true := by cases hh : usable c.t c.act <;> simp_all
    have hx := hall c.act hl hus'
    unfold unseen at hx
    cases hca : c.t c.act with
    | none => simp [hca] at hx
    | some p => simp [hca, hf'] at hx

theorem unseen_rl {t : T} {act : Nat} {f : Bool} {i : Nat} (h : unseen t act f i = true) : rl t i = true := by
  unfold unseen at h
  unfold rl
  cases hti : t i with
  | none => simp [hti] at h
  | some p => cases hr : p.r <;> simp [hti, hr] at h ⊢

/-- An active unseen relay path (it failed its probe timeouts, and is not seen) gives way to a usable path that
is not unseen, when there is one. -/
theorem choose_escapes {np pen : Nat} {c : C} (hact : unseen c.t c.act c.f c.act = true)
    (hj : ∃ j, j < np ∧ usable c.t j = true ∧ unseen c.t c.act c.f j = false) :
    (choose np pen c).act ≠ c.act ∧
      ∃ b, (choose np pen c).act = b ∧ usable c.t b = true ∧ unseen c.t c.act c.f b = false := by
  obtain ⟨j, hj, hjo, hju⟩ := hj
  obtain ⟨b, hb⟩ := least_isSome (ok := usable c.t) (k := rank pen c.t c.act c.f) ⟨j, hj, hjo⟩
  have hb' : best np pen c.t c.act c.f = some b := hb
  obtain ⟨_, hbo, _⟩ := least_spec hb
  have hbu : unseen c.t c.act c.f b = false := by
    cases hh : unseen c.t c.act c.f b
    · rfl
    · have := best_sighted hb' hh j hj hjo
      rw [hju] at this
      cases this
  have hne : b ≠ c.act := by
    intro e
    rw [e, hact] at hbu
    cases hbu
  have hg : ((c.t c.act).isNone || rl c.t c.act) = true := by simp [unseen_rl hact]
  have hsome : (c.t b).isNone = false := by
    unfold usable at hbo
    cases hcb : c.t b with
    | none => simp [hcb] at hbo
    | some _ => rfl
  have hsw : ¬ ((b == c.act || (c.t b).isNone) = true) := by simp [hne, hsome]
  have hch : (choose np pen c).act = b := by
    simp only [choose, hb']
    rw [ite_eq_left hg]
    unfold switch
    rw [ite_eq_right hsw]
  exact ⟨by rw [hch]; exact hne, b, hch, hbo, hbu⟩

/-- The fall-back of a failed direct path takes a validated relay path that is not unseen, when there is one. -/
theorem fall_sighted {np pen : Nat} {t : T} {act : Nat} {f : Bool}
    (h : ∃ j, j < np ∧ vrel t j = true ∧ unseen t act f j = false) :
    ∃ b, fallTo np pen t act f = some b ∧ vrel t b = true ∧ unseen t act f b = false := by
  obtain ⟨j, hj, hv, hu⟩ := h
  obtain ⟨b, hb⟩ := least_isSome (ok := vrel t) (k := rank pen t act f) ⟨j, hj, hv⟩
  obtain ⟨_, hbv, hmin⟩ := least_spec hb
  refine ⟨b, by simp [fallTo, hb], hbv, ?_⟩
  refine Classical.byContradiction fun hn => ?_
  have hn' : unseen t act f b = true := by cases hh : unseen t act f b <;> simp_all
  apply hmin j hj hv
  unfold Lt3 rank
  simp [hu, hn']

/-! ### The way back

A relay path the session left at the probe-timeout bound with nothing acknowledged on it is not the choice of the
next timer pass: the stamp the switch writes gives the path a cost and does not make it seen (the second round read
"seen" off the cost, and the session went back). -/

/-- The stamp changes the cost of the path the session leaves, and nothing else. -/
theorem stamp_other (t : T) (a : Nat) {j : Nat} (h : j ≠ a) : stamp t a j = t j := by
  simp [stamp, h]

theorem stamp_at (t : T) (a : Nat) : stamp t a a = (t a).map (fun p => { p with rt := 1 }) := by
  simp [stamp]

/-- A stamp does not make a path seen: the path keeps its seen fact. -/
theorem stamp_keeps_seen {t : T} {a : Nat} {p : P} (h : t a = some p) :
    ∃ q, stamp t a a = some q ∧ q.seen = p.seen :=
  ⟨{ p with rt := 1 }, by simp [stamp, h], rfl⟩

theorem usable_stamp (t : T) (a j : Nat) : usable (stamp t a) j = usable t j := by
  unfold usable stamp
  by_cases h : j = a
  · subst h
    cases ht : t j <;> simp [ht]
  · simp [h]

theorem unseen_parts {t : T} {act : Nat} {f : Bool} {i : Nat} (h : unseen t act f i = true) :
    ∃ p, t i = some p ∧ p.r = true ∧ p.seen = false := by
  unfold unseen at h
  cases hti : t i with
  | none => simp [hti] at h
  | some p =>
    have h1 : p.r = true := by cases hr : p.r <;> simp_all
    have h2 : p.seen = false := by cases hs : p.seen <;> simp_all
    exact ⟨p, rfl, h1, h2⟩

/-- The choice does not take the session to `a` when it is not on `a` and `a` is not the best path. -/
theorem choose_act_ne {np pen : Nat} {c : C} {a : Nat} (h1 : c.act ≠ a)
    (h2 : best np pen c.t c.act c.f ≠ some a) : (choose np pen c).act ≠ a := by
  unfold choose
  cases hb : best np pen c.t c.act c.f with
  | none => simp only [hb]; exact h1
  | some b2 =>
    simp only [hb]
    have hb2 : b2 ≠ a := fun e => h2 (by rw [hb, e])
    by_cases hg : ((c.t c.act).isNone || rl c.t c.act) = true
    · rw [ite_eq_left hg]
      unfold switch
      by_cases h3 : (b2 == c.act || (c.t b2).isNone) = true
      · rw [ite_eq_left h3]; exact h1
      · rw [ite_eq_right h3]; exact hb2
    · rw [ite_eq_right hg]; exact h1

/-- After the session leaves a relay path at the probe-timeout bound (the path is not seen and the session holds a
sample, so it is stamped), the next choice does not take the session back to it. The stamp is at most as high as the
cost the path had (`hrt`: the model stamps 1), so the path ranks no better than it did when the session left it. -/
theorem choose_no_return {np pen : Nat} {c : C} (hf : c.f = true) (hsm : c.smp = true)
    (hact : unseen c.t c.act c.f c.act = true) (hrt : ∀ p, c.t c.act = some p → p.rt ≤ 1)
    (hne : (choose np pen c).act ≠ c.act) : (choose np pen (choose np pen c)).act ≠ c.act := by
  obtain ⟨b, hbdef⟩ : ∃ b, (choose np pen c).act = b := ⟨_, rfl⟩
  have hne' : b ≠ c.act := by rw [← hbdef]; exact hne
  have hbest : best np pen c.t c.act c.f = some b := choose_moves hbdef hne'
  have hg : ((c.t c.act).isNone || rl c.t c.act) = true := by simp [unseen_rl hact]
  obtain ⟨hbl, hbo, hmin⟩ := least_spec hbest
  have hsome : (c.t b).isNone = false := by
    unfold usable at hbo
    cases hcb : c.t b with
    | none => simp [hcb] at hbo
    | some _ => rfl
  have hsw : ¬ ((b == c.act || (c.t b).isNone) = true) := by simp [hne', hsome]
  have hc1 : choose np pen c = { c with t := stamp c.t c.act, act := b } := by
    simp only [choose, hbest]
    rw [ite_eq_left hg]
    unfold switch
    rw [ite_eq_right hsw]
    simp [hsm]
  rw [hc1]
  refine choose_act_ne ?_ ?_
  · exact hne'
  · intro hbest1
    have hbest1' : least (usable (stamp c.t c.act)) (rank pen (stamp c.t c.act) b c.f) np = some c.act := hbest1
    obtain ⟨hal, hao, hamin⟩ := least_spec hbest1'
    have hao' : usable c.t c.act = true := by rw [← usable_stamp c.t c.act c.act]; exact hao
    have hbo' : usable (stamp c.t c.act) b = true := by rw [usable_stamp]; exact hbo
    obtain ⟨pa, hpa, hpar, hpas⟩ := unseen_parts hact
    have hrk_a0 : rank pen c.t c.act c.f c.act = (1, pa.rt + pen, c.act) := by
      unfold rank cost
      simp [hact, hpa, hpar]
    have hrk_a : rank pen (stamp c.t c.act) b c.f c.act = (1, 1 + pen, c.act) := by
      unfold rank unseen cost
      rw [stamp_at, hpa]
      simp [hpar, hpas, Ne.symm hne']
    have hrk_b : rank pen (stamp c.t c.act) b c.f b = rank pen c.t c.act c.f b := by
      unfold rank unseen cost
      rw [stamp_other c.t c.act hne', hf]
      simp
    obtain ⟨u, cb, hrb⟩ : ∃ u cb, rank pen c.t c.act c.f b = (u, cb, b) := ⟨_, _, rfl⟩
    have hA := hmin c.act hal hao'
    have hB := hamin b hbl hbo'
    rw [hrk_a0, hrb] at hA
    rw [hrk_b, hrb, hrk_a] at hB
    have hr := hrt pa hpa
    simp only [Lt3] at hA hB
    omega

#audit_axioms learn_bounded
#audit_axioms learn_gives_up
#audit_axioms learn_none_iff
#audit_axioms learn_unique
#audit_axioms learnNew_unique
#audit_axioms learnNew_gives_up
#audit_axioms follow_taken
#audit_axioms follow_full
#audit_axioms rx_auth
#audit_axioms rx_pend
#audit_axioms rx_quiet
#audit_axioms rx_bad
#audit_axioms rxOld_drops
#audit_axioms rxOld_never
#audit_axioms key_taken
#audit_axioms key_quiet
#audit_axioms inv_dial
#audit_axioms inv_rx
#audit_axioms inv_key
#audit_axioms inv_add
#audit_axioms inv_app
#audit_axioms inv_remove
#audit_axioms best_sighted
#audit_axioms choose_sighted
#audit_axioms choose_escapes
#audit_axioms fall_sighted
#audit_axioms stamp_keeps_seen
#audit_axioms choose_no_return

end Vinc.TransportPath
