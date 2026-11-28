import Pinc.Axioms

/-!
# The path table and the path of a handshake reply

A model of the path table of `pinc-transport` `conn/path.rs` (`Paths::find`, `new_path_slot` as `learn_path` calls it,
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
- a dialing side takes a reply on any path, held or not (pinc#399): a message that authenticates establishes the
  session; on a path the dial held (the flight went there) the session is there, validated and active
  (`follow_taken`); on a path only the reply named (a copy of the reply can come from any source, so it proves
  nothing) the session stays on its path and the reply's path joins unvalidated (`follow_joins`; it is challenged),
  unless the table has no room, and then the table and the active path stay as they were (`rx_auth`,
  `follow_full`); a Reply that passed its first checks waits for the key host with its path (`rx_pend`, `inv_rx`),
  and the key answer that establishes follows it by the same rule (`key_taken`);
- while a Reply waits for its verdict every datagram is held and applies nothing (`rx_held`); a failed verdict,
  counted, is the same verdict with nothing held followed by the held messages in arrival order, as if they arrived
  after it (`key_tried`, `replay_step`), so a held Reply waits for its own verdict and a held message that
  authenticates establishes the session (`key_bad_pend`, `key_bad_auth`); any other answer drops them
  (`key_drops`), and messages are held only while a verdict is awaited (`heldW_rx`, `heldW_key`);
- before the session is established, a datagram whose message does not authenticate and a key answer that does not
  establish (a failed verdict with no held message that authenticates) change no path state, on any path
  (`rx_quiet`, `key_quiet`), and one that fails authentication is counted, at once or when it is tried
  (`rx_bad`, `key_tried`);
- the invariant `Inv` (bounded, no path twice, the active path held, and validated until the establishment, a
  waiting Reply's path remembered) holds after every step of a dialing side, a datagram with a 1-RTT packet behind its handshake packet
  included (`inv_rx`, `inv_key`, `inv_add`, `inv_remove`, `inv_app`);
- the rule before #399 drops a dialing side's handshake packet on a path it does not hold, so a reply there never
  establishes the session (`rxOld_drops`, `rxOld_never`).

`Pinc.TransportPathJoined` has the reply with a 1-RTT packet behind it in the same datagram, the rule before the
correction (`noLookup_dup`) and the responder; `Pinc.TraceReplyPath` replays the recorded runs of the real code through
these functions.
-/

namespace Pinc.TransportPath

/-- A held path: its id and whether it is validated. -/
structure P where
  id : Nat
  v : Bool
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
  | some i => (set t i (some ⟨pid, false⟩), some i)
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
    (learnNew np t act pid).1 i = some ⟨pid, false⟩ := by
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

/-- The handshake: the first flight is out, a Reply waits for its verdict (the key host's answer to its Decapsulate
request), the Finish waits for its signature, or established. -/
inductive Hs where
  | wait
  | key
  | sign
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
waits for the key host (`pend`, a ghost the theorems read), whether the round trip has a sample, `handshake_dropped`,
for a resumed responder the path its one Reply went to while the proof of receipt is owed (`rp`, `proof`), and the
messages held while a Reply waits for its verdict, each with its path and what it completes (`hq`, `hold_part`). -/
structure C where
  t : T
  act : Nat := 0
  hs : Hs := .wait
  rf : Option Nat := none
  pend : Option Nat := none
  smp : Bool := false
  hd : Nat := 0
  rp : Option Nat := none
  hq : List (Nat × Kind) := []

/-- The table of a dialing side when it dials on path `pid`: the path validated and active in slot 0. -/
def dial (pid : Nat) : C := { t := fun j => if j = 0 then some ⟨pid, true⟩ else none }

/-- `follow_reply`: the reply's path is found or learnt. A path the dial held is validated (the flight went there and
came back) and the session moves to it; the path it leaves is no longer validated. A path the reply alone named
proves nothing (anyone can send a copy of the reply from any source): it joins unvalidated (it is challenged and
owed a copy of the Finish, which this model does not track) and the session stays on its path. With no room the
table is as it was. -/
def follow (np : Nat) (c : C) : C :=
  match c.rf with
  | none => c
  | some pid =>
    let held := (find np c.t pid).isSome
    let r := learn np c.t c.act pid
    match r.2 with
    | none => { c with rf := none }
    | some i =>
      if i = c.act ∨ held = false then { c with rf := none, t := r.1 }
      else { c with rf := none, t := setV (setV r.1 c.act false) i true, act := i }

/-- `pump` at the establishment: `follow_reply`, and the round trip sample `feed` took (`s`). -/
def establish (np : Nat) (c : C) (s : Bool) : C := follow np { c with hs := .done, pend := none, smp := c.smp || s }

/-- `on_handshake` of a dialing side, once its packet's message is complete. While a Reply waits for its verdict the
datagram is held and applies nothing (`hold_part`). -/
def hsMsg (np : Nat) (c : C) (pid : Nat) (k : Kind) (s : Bool) : C :=
  match c.hs, k with
  | .done, _ => c
  | .key, _ => { c with hq := c.hq ++ [(pid, k)] }
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

/-- `after_verdict` after a failed verdict: the held messages are given in arrival order until one makes the dial wait
for a verdict again (the rest stay held) or none is left; once the session is established the rest is dropped. -/
def replay (np : Nat) (s : Bool) : C → List (Nat × Kind) → C
  | x, [] => { x with hq := [] }
  | x, (pid, k) :: q =>
    if x.hs = .done then { x with hq := [] }
    else if x.hs = .key then { x with hq := (pid, k) :: q }
    else replay np s (hsMsg np x pid k s) q

/-- `on_key_response` and `answer_soft`: the Reply's verdict established the session, or the Finish's signature
follows, both dropping what was held; or the Reply failed a check once the key host answered, counted, and what was
held is tried. -/
def key (np : Nat) (c : C) (r : KeyR) (s : Bool) : C :=
  if c.hs = .key ∨ c.hs = .sign then
    match r with
    | .ok => establish np { c with hq := [] } s
    | .more => { c with hs := .sign, hq := [] }
    | .bad => replay np s { c with hs := .wait, pend := none, hd := c.hd + 1, hq := [] } c.hq
  else c

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

/-- What a responder's handshake datagram completes: nothing, a Finish that authenticated, or a resumption Hello whose
binder verified. -/
inductive RMsg where
  | part
  | finish
  | resume
  deriving DecidableEq, Repr

/-- A responder's handshake datagram on path `pid` (`handle_inner`): it learns a path it does not hold while in its
handshake or holding none. A Finish establishes the session and validates the active path (the dialer answered the
Reply sent there); a resumption Hello establishes it and validates nothing, since anyone who saw the Hello can send a
copy of it from any source: the path its Reply goes to is recorded (`proof`). -/
def respRx (np : Nat) (c : C) (pid : Nat) (m : RMsg) : C :=
  let empty := (List.range np).all fun j => (c.t j).isNone
  let c1 := if find np c.t pid = none ∧ (empty = true ∨ c.hs ≠ .done) then { c with t := (learn np c.t c.act pid).1 } else c
  if m ≠ .part ∧ c1.hs ≠ .done ∧ (find np c1.t pid).isSome ∧ (c1.t c1.act).isSome then
    if m = .finish then { c1 with hs := .done, t := setV c1.t c1.act true }
    else { c1 with hs := .done, rp := idOf c1.t c1.act }
  else c1

/-- A resumed responder resends its Reply on the active path: on a path other than the one the proof names, the keys
no longer say which path the dialer heard, and the proof is given up (`reply_left_on`; that path is challenged). -/
def resend (c : C) : C := if c.rp.isSome ∧ c.rp ≠ idOf c.t c.act then { c with rp := none } else c

/-- What authenticated after the establishment: a 1-RTT packet, or a 0-RTT one. -/
inductive Pkt where
  | app
  | early
  deriving DecidableEq, Repr

/-- The confirmation point (`on_short`): the dialer's first 1-RTT packet needs the Reply's fresh key share, so it
proves the Reply was received and validates the path the proof names, on whichever path it came. A 0-RTT packet opens
under keys of the ticket and the Hello alone and proves nothing. -/
def confirm (np : Nat) (c : C) (k : Pkt) : C :=
  match k with
  | .early => c
  | .app =>
    match c.rp with
    | none => c
    | some x =>
      match find np c.t x with
      | some i => { c with t := setV c.t i true, rp := none }
      | none => { c with rp := none }

/-! ## What a dialing side's steps do -/

/-- The active slot holds a validated path. -/
def ActiveV (c : C) : Prop := ∃ p, c.t c.act = some p ∧ p.v = true

/-- The invariant of a dialing side. -/
structure Inv (np : Nat) (c : C) : Prop where
  bounded : Bounded np c.t
  unique : Unique c.t
  act_lt : c.act < np
  held : ∃ p, c.t c.act = some p
  active : c.hs ≠ .done → ActiveV c
  waits : c.hs = .key ∨ c.hs = .sign → c.pend.isSome ∧ c.rf = c.pend

/-- The session `c'` is on path `pid`: held, in the active slot, validated exactly when `v`. -/
def On (c' : C) (pid : Nat) (v : Bool) : Prop := ∃ p, c'.t c'.act = some p ∧ p.id = pid ∧ p.v = v

theorem inv_dial (np pid : Nat) (h : 0 < np) : Inv np (dial pid) := by
  refine ⟨?_, ?_, h, ⟨⟨pid, true⟩, by simp [dial]⟩, fun _ => ⟨⟨pid, true⟩, by simp [dial], rfl⟩, by simp [dial]⟩
  · intro j hj; simp [dial]; omega
  · intro i j x hi hj
    simp [dial, idOf] at hi hj
    omega

/-! ### `follow`, case by case -/

theorem follow_none (np : Nat) (c : C) (h : c.rf = none) : follow np c = c := by
  unfold follow; rw [h]

theorem follow_found {np : Nat} {c : C} {pid i : Nat} (hrf : c.rf = some pid) (hf : find np c.t pid = some i) :
    follow np c = if i = c.act then { c with rf := none, t := c.t }
      else { c with rf := none, t := setV (setV c.t c.act false) i true, act := i } := by
  unfold follow; rw [hrf]; dsimp only; rw [learn_found hf, hf]
  by_cases h : i = c.act <;> simp [h]

theorem follow_learnt {np : Nat} {c : C} {pid i : Nat} (hrf : c.rf = some pid) (hf : find np c.t pid = none)
    (hl : (learnNew np c.t c.act pid).2 = some i) :
    follow np c = { c with rf := none, t := (learnNew np c.t c.act pid).1 } := by
  unfold follow; rw [hrf]; dsimp only; rw [learn_fresh hf, hl, hf]
  simp

theorem follow_noroom {np : Nat} {c : C} {pid : Nat} (hrf : c.rf = some pid) (hf : find np c.t pid = none)
    (hl : (learnNew np c.t c.act pid).2 = none) : follow np c = { c with rf := none } := by
  unfold follow; rw [hrf]; dsimp only; rw [learn_fresh hf, hl] <;> rfl

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
      | some i => rw [follow_learnt hrf hf hl]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem follow_hq (np : Nat) (c : C) : (follow np c).hq = c.hq := by
  cases hrf : c.rf with
  | none => rw [follow_none np c hrf]
  | some pid =>
    cases hf : find np c.t pid with
    | some i => rw [follow_found hrf hf]; split <;> rfl
    | none =>
      cases hl : (learnNew np c.t c.act pid).2 with
      | none => rw [follow_noroom hrf hf hl]
      | some i => rw [follow_learnt hrf hf hl]

theorem establish_hq (np : Nat) (c : C) (s : Bool) : (establish np c s).hq = c.hq := follow_hq np _

/-- A slot `new_path_slot` picks is never the active one while that holds a path. -/
theorem slot_ne_act {np : Nat} {t : T} {act i : Nat} {pa : P} (hpa : t act = some pa) (hs : slot np t act = some i) :
    i ≠ act := by
  rcases (slot_spec hs).2 with h | ⟨h, _⟩
  · intro e; subst e; rw [hpa] at h; cases h
  · exact h

/-- Learning a new path never takes the active slot. -/
theorem learnNew_keeps_active {np : Nat} {t : T} {act pid : Nat} {pa : P} (hpa : t act = some pa) :
    (learnNew np t act pid).1 act = some pa := by
  by_cases hl : (learnNew np t act pid).2 = some act
  · rw [learnNew_snd] at hl
    exact absurd rfl (slot_ne_act hpa hl)
  · rw [learnNew_other hl, hpa]

/-- The reply's path is held: the session is on it afterwards, validated. -/
theorem follow_taken {np : Nat} {c : C} {pid i : Nat} (hv : ActiveV c) (hrf : c.rf = some pid)
    (hf : find np c.t pid = some i) : On (follow np c) pid true := by
  obtain ⟨pa, hpa, hva⟩ := hv
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
    show setV (setV c.t c.act false) i true i = _
    rw [setV_at, setV_other _ _ _ hia, hp]
    rfl

/-- The reply's path is not held and has room in slot `i`: the session stays on its path, the reply's path joins
there unvalidated, and every other slot is as it was. -/
theorem follow_joins {np : Nat} {c : C} {pid i : Nat} {pa : P} (hpa : c.t c.act = some pa) (hrf : c.rf = some pid)
    (hf : find np c.t pid = none) (hs : slot np c.t c.act = some i) :
    (follow np c).act = c.act ∧ (follow np c).t c.act = some pa ∧ (follow np c).t i = some ⟨pid, false⟩ ∧
      ∀ j, j ≠ i → (follow np c).t j = c.t j := by
  have hl : (learnNew np c.t c.act pid).2 = some i := by rw [learnNew_snd, hs]
  rw [follow_learnt hrf hf hl]
  exact ⟨rfl, learnNew_keeps_active hpa, learnNew_at hl,
    fun j hji => learnNew_other (by rw [hl]; intro e; exact hji (Option.some.inj e).symm)⟩

/-- The reply's path is not held and there is no room: nothing of the table moves. -/
theorem follow_full {np : Nat} {c : C} {pid : Nat} (hrf : c.rf = some pid) (hf : find np c.t pid = none)
    (hs : slot np c.t c.act = none) : (follow np c).t = c.t ∧ (follow np c).act = c.act := by
  have hl : (learnNew np c.t c.act pid).2 = none := by rw [learnNew_snd, hs]
  rw [follow_noroom hrf hf hl]
  exact ⟨rfl, rfl⟩

theorem inv_follow {np : Nat} {c : C} (hi : Inv np c) (hhs : c.hs = .done) : Inv np (follow np c) := by
  obtain ⟨pa, hpa⟩ := hi.held
  have hw : (follow np c).hs = .key ∨ (follow np c).hs = .sign →
      (follow np c).pend.isSome ∧ (follow np c).rf = (follow np c).pend := by
    intro h; rw [(follow_keeps np c).1, hhs] at h; simp at h
  have ha : (follow np c).hs ≠ .done → ActiveV (follow np c) := by
    intro h; rw [(follow_keeps np c).1] at h; exact absurd hhs h
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
          by rw [he]; exact ⟨pa, hpa⟩, ha, hw⟩
      · rw [ite_eq_right hia] at he
        refine ⟨by rw [he]; exact bounded_setV (bounded_setV hi.bounded _ _) _ _,
          by rw [he]; exact unique_setV (unique_setV hi.unique _ _) _ _, by rw [he]; exact hil,
          ⟨{ p with v := true }, ?_⟩, ha, hw⟩
        rw [he]
        show setV (setV c.t c.act false) i true i = _
        rw [setV_at, setV_other _ _ _ hia, hp]
        rfl
    | none =>
      cases hl : (learnNew np c.t c.act pid).2 with
      | none =>
        have he := follow_noroom hrf hf hl
        exact ⟨by rw [he]; exact hi.bounded, by rw [he]; exact hi.unique, by rw [he]; exact hi.act_lt,
          by rw [he]; exact ⟨pa, hpa⟩, ha, hw⟩
      | some i =>
        have he := follow_learnt hrf hf hl
        refine ⟨by rw [he]; exact learnNew_bounded hi.bounded,
          by rw [he]; exact learnNew_unique hi.bounded hi.unique hf,
          by rw [he]; exact hi.act_lt, ⟨pa, by rw [he]; exact learnNew_keeps_active hpa⟩, ha, hw⟩

/-! ### A datagram and a key answer at a dialing side -/

theorem hsMsg_done {np : Nat} {c : C} {pid : Nat} {k : Kind} {s : Bool} (h : c.hs = .done) : hsMsg np c pid k s = c := by
  unfold hsMsg; rw [h]

theorem hsMsg_auth {np : Nat} {c : C} {pid : Nat} {s : Bool} (h : c.hs ≠ .done) (hk : c.hs ≠ .key) :
    hsMsg np c pid .auth s = establish np { c with rf := some pid } s := by
  unfold hsMsg; cases hh : c.hs <;> simp_all

theorem rx_plain (np : Nat) (c : C) (pid : Nat) (k : Kind) (s : Bool) :
    rx false np c pid k false s = hsMsg np c pid k s := by
  simp [rx]

/-- A message that authenticates, on any path, with no verdict awaited: the session is established; on the reply's
path, validated, if the dial held it; else on its own path, the reply's path joining unvalidated if the table has room
for it and the table as it was if not. -/
theorem rx_auth {np : Nat} {c : C} {pid : Nat} (hi : Inv np c) (hhs : c.hs ≠ .done) (hk : c.hs ≠ .key) (s : Bool) :
    (rx false np c pid .auth false s).hs = .done ∧
      ((find np c.t pid).isSome → On (rx false np c pid .auth false s) pid true) ∧
      (find np c.t pid = none → ∀ i, slot np c.t c.act = some i →
        (rx false np c pid .auth false s).act = c.act ∧ (rx false np c pid .auth false s).t c.act = c.t c.act ∧
          (rx false np c pid .auth false s).t i = some ⟨pid, false⟩) ∧
      (find np c.t pid = none → slot np c.t c.act = none →
        (rx false np c pid .auth false s).t = c.t ∧ (rx false np c pid .auth false s).act = c.act) := by
  rw [rx_plain, hsMsg_auth hhs hk]
  have hv0 : ActiveV { c with rf := some pid, hs := .done, pend := none, smp := c.smp || s } := hi.active hhs
  obtain ⟨pa, hpa⟩ := hi.held
  refine ⟨(follow_keeps np _).1, fun hf => ?_, fun hf i hs => ?_, fun hf hs => follow_full rfl hf hs⟩
  · obtain ⟨i, hfi⟩ := Option.isSome_iff_exists.mp hf
    exact follow_taken hv0 rfl hfi
  · obtain ⟨h1, h2, h3, _⟩ :=
      follow_joins (c := { c with rf := some pid, hs := .done, pend := none, smp := c.smp || s }) hpa rfl hf hs
    exact ⟨h1, h2.trans hpa.symm, h3⟩

/-- A Reply that passed its first checks, on any path, waits for the key host with its path. -/
theorem rx_pend {np : Nat} {c : C} {pid : Nat} (hw : c.hs = .wait) (coal s : Bool) :
    rx false np c pid .pend coal s = { c with rf := some pid, pend := some pid, hs := .key } := by
  simp [rx, hsMsg, hw]

theorem hsMsg_quiet {np : Nat} {c : C} {pid : Nat} {k : Kind} {s : Bool} (hhs : c.hs ≠ .done) (hk : k ≠ .auth) :
    (hsMsg np c pid k s).t = c.t ∧ (hsMsg np c pid k s).act = c.act ∧ (hsMsg np c pid k s).smp = c.smp ∧
      (hsMsg np c pid k s).hs ≠ .done := by
  cases hh : c.hs <;> cases k <;> simp_all [hsMsg]

/-- While a Reply waits for its verdict, a datagram is held and applies nothing (`ReplyPath.tla` `Held`). -/
theorem rx_held {np : Nat} {c : C} {pid : Nat} {k : Kind} (hk : c.hs = .key) (coal s : Bool) :
    rx false np c pid k coal s = { c with hq := c.hq ++ [(pid, k)] } := by
  simp [rx, hsMsg, hk]

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

/-- One that fails authentication is counted, on any path, with no verdict awaited. -/
theorem rx_bad {np : Nat} {c : C} {pid : Nat} (hhs : c.hs ≠ .done) (hk : c.hs ≠ .key) (coal s : Bool) :
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

/-- Held messages that do not authenticate change no path state when they are tried. -/
theorem replay_quiet {np : Nat} {s : Bool} {x : C} {q : List (Nat × Kind)} (hq : ∀ e ∈ q, e.2 ≠ .auth)
    (hx : x.hs ≠ .done) :
    (replay np s x q).t = x.t ∧ (replay np s x q).act = x.act ∧ (replay np s x q).smp = x.smp ∧
      (replay np s x q).hs ≠ .done := by
  induction q generalizing x with
  | nil => exact ⟨rfl, rfl, rfl, hx⟩
  | cons e q ih =>
    obtain ⟨pid, k⟩ := e
    simp only [replay]
    rw [ite_eq_right hx]
    by_cases hk : x.hs = .key
    · rw [ite_eq_left hk]; exact ⟨rfl, rfl, rfl, hx⟩
    · rw [ite_eq_right hk]
      have hk' : k ≠ .auth := hq (pid, k) (by simp)
      obtain ⟨h1, h2, h3, h4⟩ := hsMsg_quiet (np := np) (pid := pid) (s := s) hx hk'
      obtain ⟨g1, g2, g3, g4⟩ := ih (x := hsMsg np x pid k s) (fun e he => hq e (by simp [he])) h4
      exact ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4⟩

/-- A held message is tried as a datagram that arrives once the verdict is given: with no verdict awaited and the
session not established, the replay of `(pid, k)` then `q` is the replay of `q` after that datagram. -/
theorem replay_step {np : Nat} {s : Bool} {x : C} {pid : Nat} {k : Kind} {q : List (Nat × Kind)}
    (hd : x.hs ≠ .done) (hk : x.hs ≠ .key) :
    replay np s x ((pid, k) :: q) = replay np s (rx false np x pid k false s) q := by
  simp only [replay, rx_plain]
  rw [ite_eq_right hd, ite_eq_right hk]

/-- A failed verdict, counted, is the same verdict with nothing held followed by the held messages in arrival order
(`ReplyPath.tla` `HeldTried`). -/
theorem key_tried {np : Nat} {c : C} (hk : c.hs = .key ∨ c.hs = .sign) (s : Bool) :
    key np c .bad s = replay np s { c with hs := .wait, pend := none, hd := c.hd + 1, hq := [] } c.hq := by
  rcases hk with h | h <;> simp [key, h]

/-- After a failed verdict a held Reply that passed its first checks waits for its own verdict with its path, the
failed one counted (`ReplyPath.tla` `NotLost`). -/
theorem key_bad_pend {np : Nat} {c : C} {pid : Nat} {q : List (Nat × Kind)} (hk : c.hs = .key ∨ c.hs = .sign)
    (hq : c.hq = (pid, .pend) :: q) (s : Bool) :
    (key np c .bad s).hs = .key ∧ (key np c .bad s).pend = some pid ∧ (key np c .bad s).rf = some pid ∧
      (key np c .bad s).hd = c.hd + 1 := by
  rw [key_tried hk, hq]
  rcases q with _ | ⟨⟨p2, k2⟩, q⟩ <;> simp [replay, hsMsg]

/-- After a failed verdict a held message that authenticates establishes the session (`ReplyPath.tla` `NotLost`). -/
theorem key_bad_auth {np : Nat} {c : C} {pid : Nat} {q : List (Nat × Kind)} (hk : c.hs = .key ∨ c.hs = .sign)
    (hq : c.hq = (pid, .auth) :: q) (s : Bool) :
    (key np c .bad s).hs = .done ∧ (key np c .bad s).hd = c.hd + 1 := by
  rw [key_tried hk, hq]
  rcases q with _ | ⟨⟨p2, k2⟩, q⟩ <;> simp [replay, hsMsg, establish, follow_keeps]

/-- Any answer but a failed verdict drops what was held (`ReplyPath.tla` `HeldDropped`). -/
theorem key_drops {np : Nat} {c : C} {r : KeyR} (hk : c.hs = .key ∨ c.hs = .sign) (hr : r ≠ .bad) (s : Bool) :
    (key np c r s).hq = [] := by
  rcases hk with h | h <;> cases r <;> simp_all [key, establish_hq]

/-- The key answer that establishes follows the path of the Reply that waited, by the same rule, whether it is the
Reply's verdict or the Finish's signature. -/
theorem key_taken {np : Nat} {c : C} (hi : Inv np c) (hk : c.hs = .key ∨ c.hs = .sign) (s : Bool) :
    ∃ pid, c.pend = some pid ∧ (key np c .ok s).hs = .done ∧
      ((find np c.t pid).isSome → On (key np c .ok s) pid true) ∧
      (find np c.t pid = none → ∀ i, slot np c.t c.act = some i →
        (key np c .ok s).act = c.act ∧ (key np c .ok s).t c.act = c.t c.act ∧ (key np c .ok s).t i = some ⟨pid, false⟩) ∧
      (find np c.t pid = none → slot np c.t c.act = none →
        (key np c .ok s).t = c.t ∧ (key np c .ok s).act = c.act) := by
  obtain ⟨hps, hrf⟩ := hi.waits hk
  obtain ⟨pid, hpid⟩ := Option.isSome_iff_exists.mp hps
  have hkey : key np c .ok s = follow np { c with hq := [], hs := .done, pend := none, smp := c.smp || s } := by
    rcases hk with h | h <;> simp [key, establish, h]
  have hv0 : ActiveV { c with hq := [], hs := .done, pend := none, smp := c.smp || s } :=
    hi.active (by rcases hk with h | h <;> rw [h] <;> decide)
  have hrf0 : ({ c with hq := [], hs := .done, pend := none, smp := c.smp || s } : C).rf = some pid := by
    show c.rf = some pid; rw [hrf, hpid]
  rw [hkey]
  obtain ⟨pa, hpa⟩ := hi.held
  refine ⟨pid, hpid, (follow_keeps np _).1, fun hf => ?_, fun hf i hs => ?_, fun hf hs => follow_full hrf0 hf hs⟩
  · obtain ⟨i, hfi⟩ := Option.isSome_iff_exists.mp hf
    exact follow_taken hv0 hrf0 hfi
  · obtain ⟨h1, h2, h3, _⟩ :=
      follow_joins (c := { c with hq := [], hs := .done, pend := none, smp := c.smp || s }) hpa hrf0 hf hs
    exact ⟨h1, h2.trans hpa.symm, h3⟩

/-- A key answer that does not establish changes no path state: not the verdict that establishes, and not a failed
verdict with a held message that authenticates. -/
theorem key_quiet {np : Nat} {c : C} {r : KeyR} (hr : r ≠ .ok) (hq : r = .bad → ∀ e ∈ c.hq, e.2 ≠ .auth)
    (s : Bool) :
    (key np c r s).t = c.t ∧ (key np c r s).act = c.act ∧ (key np c r s).smp = c.smp ∧
      (c.hs ≠ .done → (key np c r s).hs ≠ .done) := by
  by_cases hk : c.hs = .key ∨ c.hs = .sign
  · cases r with
    | ok => exact absurd rfl hr
    | more =>
      have he : key np c .more s = { c with hs := .sign, hq := [] } := by
        rcases hk with h | h <;> simp [key, h]
      rw [he]; exact ⟨rfl, rfl, rfl, fun _ h => by cases h⟩
    | bad =>
      rw [key_tried hk]
      obtain ⟨h1, h2, h3, h4⟩ := replay_quiet (np := np) (s := s)
        (x := { c with hs := .wait, pend := none, hd := c.hd + 1, hq := [] }) (hq rfl) (fun h => by cases h)
      exact ⟨h1, h2, h3, fun _ => h4⟩
  · have he : key np c r s = c := by unfold key; rw [ite_eq_right hk]
    rw [he]; exact ⟨rfl, rfl, rfl, id⟩

/-! ## The invariant through every step of a dialing side -/

/-- The establishment keeps the invariant: it needs only the table's part. -/
theorem inv_establish {np : Nat} (c : C) (s : Bool) (hb : Bounded np c.t) (hu : Unique c.t) (ha : c.act < np)
    (hp : ∃ p, c.t c.act = some p) : Inv np (establish np c s) :=
  inv_follow (c := { c with hs := .done, pend := none, smp := c.smp || s })
    ⟨hb, hu, ha, hp, fun h => absurd rfl h, fun h => by simp at h⟩ rfl

theorem inv_hsMsg {np : Nat} {c : C} {pid : Nat} {k : Kind} (hi : Inv np c) (s : Bool) :
    Inv np (hsMsg np c pid k s) := by
  have hw := hi.waits
  cases hh : c.hs <;> cases k <;> simp only [hsMsg, hh]
  all_goals first
    | exact inv_establish _ s hi.bounded hi.unique hi.act_lt hi.held
    | exact hi
    | exact ⟨hi.bounded, hi.unique, hi.act_lt, hi.held, hi.active, hi.waits⟩
    | exact ⟨hi.bounded, hi.unique, hi.act_lt, hi.held, fun _ => hi.active (by rw [hh]; decide), fun h => by simp_all⟩

theorem inv_replay {np : Nat} {s : Bool} {x : C} {q : List (Nat × Kind)} (hi : Inv np x) :
    Inv np (replay np s x q) := by
  induction q generalizing x with
  | nil => exact ⟨hi.bounded, hi.unique, hi.act_lt, hi.held, hi.active, hi.waits⟩
  | cons e q ih =>
    obtain ⟨pid, k⟩ := e
    simp only [replay]
    by_cases hd : x.hs = .done
    · rw [ite_eq_left hd]; exact ⟨hi.bounded, hi.unique, hi.act_lt, hi.held, hi.active, hi.waits⟩
    · rw [ite_eq_right hd]
      by_cases hk : x.hs = .key
      · rw [ite_eq_left hk]; exact ⟨hi.bounded, hi.unique, hi.act_lt, hi.held, hi.active, hi.waits⟩
      · rw [ite_eq_right hk]; exact ih (x := hsMsg np x pid k s) (inv_hsMsg hi s)

theorem inv_key {np : Nat} {c : C} {r : KeyR} (hi : Inv np c) (s : Bool) : Inv np (key np c r s) := by
  by_cases hk : c.hs = .key ∨ c.hs = .sign
  · have hv : c.hs ≠ .done := by rcases hk with h | h <;> rw [h] <;> decide
    cases r with
    | ok =>
      have he : key np c .ok s = establish np { c with hq := [] } s := by rcases hk with h | h <;> simp [key, h]
      rw [he]; exact inv_establish _ s hi.bounded hi.unique hi.act_lt hi.held
    | more =>
      have he : key np c .more s = { c with hs := .sign, hq := [] } := by rcases hk with h | h <;> simp [key, h]
      rw [he]; exact ⟨hi.bounded, hi.unique, hi.act_lt, hi.held, fun _ => hi.active hv, fun _ => hi.waits hk⟩
    | bad =>
      rw [key_tried hk]
      exact inv_replay ⟨hi.bounded, hi.unique, hi.act_lt, hi.held, fun _ => hi.active hv, fun h => by simp at h⟩
  · have he : key np c r s = c := by unfold key; rw [ite_eq_right hk]
    rw [he]; exact hi

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
  obtain ⟨pa, hpa⟩ := hi.held
  refine ⟨learn_bounded hi.bounded, learn_unique hi.bounded hi.unique, hi.act_lt,
    ⟨pa, learn_keeps_active hpa⟩, fun h => ?_, hi.waits⟩
  obtain ⟨pb, hpb, hvb⟩ := hi.active h
  exact ⟨pb, learn_keeps_active hpb, hvb⟩

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
      obtain ⟨pa, hpa⟩ := hi.held
      have hkeep : ∀ q, c.t c.act = some q → set c.t i none c.act = some q := by
        intro q hq; unfold set; rw [ite_eq_right (Ne.symm hia), hq]
      have hid : ∀ a x, idOf (set c.t i none) a = some x → idOf c.t a = some x := by
        intro a x ha
        unfold idOf set at ha
        by_cases h : a = i
        · rw [ite_eq_left h] at ha; cases ha
        · rw [ite_eq_right h] at ha; exact ha
      refine ⟨?_, fun a b x ha hb => hi.unique a b x (hid a x ha) (hid b x hb), hi.act_lt, ⟨pa, hkeep pa hpa⟩,
        fun h => ?_, hi.waits⟩
      · intro j hj
        show set c.t i none j = none
        unfold set
        split
        · rfl
        · exact hi.bounded j hj
      · obtain ⟨pb, hpb, hvb⟩ := hi.active h
        exact ⟨pb, hkeep pb hpb, hvb⟩

/-! ## Messages are held only while a verdict is awaited -/

/-- `ReplyPath.tla` `HeldOnlyWaiting`. -/
def HeldW (c : C) : Prop := c.hq ≠ [] → c.hs = .key

theorem heldW_dial (pid : Nat) : HeldW (dial pid) := fun h => absurd rfl h

theorem heldW_replay {np : Nat} {s : Bool} {x : C} {q : List (Nat × Kind)} : HeldW (replay np s x q) := by
  induction q generalizing x with
  | nil => exact fun h => absurd rfl h
  | cons e q ih =>
    obtain ⟨pid, k⟩ := e
    simp only [replay]
    by_cases hd : x.hs = .done
    · rw [ite_eq_left hd]; exact fun h => absurd rfl h
    · rw [ite_eq_right hd]
      by_cases hk : x.hs = .key
      · rw [ite_eq_left hk]; exact fun _ => hk
      · rw [ite_eq_right hk]; exact ih (x := hsMsg np x pid k s)

theorem heldW_hsMsg {np : Nat} {c : C} {pid : Nat} {k : Kind} {s : Bool} (h : HeldW c) :
    HeldW (hsMsg np c pid k s) := by
  cases hh : c.hs <;> cases k <;> simp only [hsMsg, hh]
  all_goals first
    | exact h
    | exact fun _ => hh
    | exact fun _ => rfl
    | (intro hne; exact absurd (h hne) (by rw [hh]; decide))
    | (intro hne; rw [establish_hq] at hne; exact absurd (h hne) (by rw [hh]; decide))

theorem heldW_tail {np : Nat} {c c1 : C} {pid : Nat} {coal : Bool} (h1 : HeldW c1) :
    HeldW (if coal && decide (c1.hs = .done) && (find np c.t pid).isNone then
      { c1 with t := (learn np c1.t c1.act pid).1 } else c1) := by
  split
  · exact h1
  · exact h1

theorem heldW_rx {np : Nat} {c : C} {pid : Nat} {k : Kind} (h : HeldW c) (old coal s : Bool) :
    HeldW (rx old np c pid k coal s) := by
  have h1 : HeldW (if old && (find np c.t pid).isNone then c else hsMsg np c pid k s) := by
    split
    · exact h
    · exact heldW_hsMsg h
  exact heldW_tail h1

theorem heldW_key {np : Nat} {c : C} {r : KeyR} (h : HeldW c) (s : Bool) : HeldW (key np c r s) := by
  by_cases hk : c.hs = .key ∨ c.hs = .sign
  · cases r with
    | ok =>
      have he : key np c .ok s = establish np { c with hq := [] } s := by rcases hk with h | h <;> simp [key, h]
      rw [he]; intro hne; rw [establish_hq] at hne; exact absurd rfl hne
    | more =>
      have he : key np c .more s = { c with hs := .sign, hq := [] } := by rcases hk with h | h <;> simp [key, h]
      rw [he]; exact fun hne => absurd rfl hne
    | bad => rw [key_tried hk]; exact heldW_replay
  · have he : key np c r s = c := by unfold key; rw [ite_eq_right hk]
    rw [he]; exact h

theorem heldW_add {np : Nat} {c : C} {pid : Nat} (h : HeldW c) : HeldW (addPath np c pid).1 := by
  unfold addPath
  cases find np c.t pid with
  | some _ => exact h
  | none => exact h

theorem heldW_app {np : Nat} {c : C} {pid : Nat} (h : HeldW c) : HeldW (app np c pid) := by
  unfold app
  split
  · exact h
  · exact h

theorem heldW_remove {np : Nat} {c : C} {pid : Nat} (h : HeldW c) : HeldW (removePath np c pid).1 := by
  unfold removePath
  cases hf : find np c.t pid with
  | none => exact h
  | some i =>
    show HeldW (if i = c.act then (c, 2) else ({ c with t := set c.t i none }, 0)).1
    by_cases hia : i = c.act
    · rw [ite_eq_left hia]; exact h
    · rw [ite_eq_right hia]; exact h

#audit_axioms learn_bounded
#audit_axioms learn_gives_up
#audit_axioms learn_none_iff
#audit_axioms learn_unique
#audit_axioms learnNew_unique
#audit_axioms learnNew_gives_up
#audit_axioms follow_taken
#audit_axioms follow_joins
#audit_axioms follow_full
#audit_axioms rx_auth
#audit_axioms rx_pend
#audit_axioms rx_quiet
#audit_axioms rx_bad
#audit_axioms rxOld_drops
#audit_axioms rxOld_never
#audit_axioms key_taken
#audit_axioms key_quiet
#audit_axioms rx_held
#audit_axioms replay_step
#audit_axioms key_tried
#audit_axioms key_bad_pend
#audit_axioms key_bad_auth
#audit_axioms key_drops
#audit_axioms inv_replay
#audit_axioms heldW_rx
#audit_axioms heldW_key
#audit_axioms heldW_add
#audit_axioms heldW_app
#audit_axioms heldW_remove
#audit_axioms inv_dial
#audit_axioms inv_rx
#audit_axioms inv_key
#audit_axioms inv_add
#audit_axioms inv_app
#audit_axioms inv_remove

end Pinc.TransportPath
