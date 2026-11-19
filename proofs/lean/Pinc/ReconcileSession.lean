import Pinc.ReconcileParts

/-!
# Reconcile session: `answer`, `turn`, the frames and the handlers of `session.rs`

`answerLoop` is the loop of `Core::answer` with the rollback of a part that passes the message limit; `turn` pushes the
unread tail as a frame and resumes held frames while the reply has room; `Initiator.handle`, `Responder.handle` and
`Responder.resume` are the handlers, `start` and `restartExact` build the root, `checkMsg` the final check and
`coldChunk` a chunk of a cold stream.
-/

namespace Pinc.Reconcile

/-- The loop of `answer` over `nparts` parts: the state, the unread bytes (those from the first part that did not fit,
when some did not) and the number of parts left. -/
def answerLoop (o : Oracle) (S : List Item) : Core → List Nat → Nat → Except Err (Core × List Nat × Nat)
  | c, r, 0 => .ok (c, r, 0)
  | c, r, k + 1 => do
    let cnt0 := c.ans.cnt
    let (mark, out1) := c.out.mark
    let c := { c with out := out1, bsnap := c.blast }
    let (c', r') ← procPart o S c r mark
    if c'.out.body.length > c'.lim.cap then
      if mark = 0 then throw .messageTooLarge
      else pure ({ c' with out := c'.out.rollback mark, blast := c.blast, ans := { c'.ans with cnt := cnt0 } }, r, k + 1)
    else answerLoop o S c' r' k

/-- `push_frame`. -/
def Core.pushFrame (c : Core) (rest : List Nat) (left : Nat) : Except Err Core :=
  if c.frames.length ≥ maxNest then .error .tooManyRounds
  else .ok { c with frames := ⟨rest, left, c.blast⟩ :: c.frames }

/-- `resume`: continue the newest frame; whether it advanced. -/
def Core.resume (o : Oracle) (S : List Item) (c : Core) : Except Err (Core × Bool) :=
  match c.frames with
  | [] => .error (.malformed .state)
  | f :: tl => do
    let (c2, rest, left) ← answerLoop o S { c with blast := f.last } f.buf f.left
    if left = 0 then
      if !rest.isEmpty then throw (.malformed .frame)
      else pure ({ c2 with frames := tl }, true)
    else pure ({ c2 with frames := ⟨rest, left, c2.blast⟩ :: tl }, decide (left < f.left))

/-- The frames resumed while the reply has room. -/
def resumeLoop (o : Oracle) (S : List Item) : Nat → Core → Except Err Core
  | 0, c => .ok c
  | f + 1, c =>
    if !c.frames.isEmpty ∧ c.out.body.length < c.lim.cap then do
      let (c', adv) ← c.resume o S
      if adv then resumeLoop o S f c' else pure c'
    else .ok c

/-- `turn`: process the `nparts` parts of a message and build the reply parts. -/
def Core.turn (o : Oracle) (S : List Item) (c : Core) (r : List Nat) (nparts : Nat) : Except Err (Core × Ans) := do
  let c := { c with out := c.out.reset, blast := [], ans := {} }
  let (c, rest, left) ← answerLoop o S c r nparts
  let c ← if left > 0 then c.pushFrame rest left
    else if !rest.isEmpty then throw (.malformed .frame) else pure c
  let fuel := c.frames.foldl (fun s f => s + f.left + 1) 1
  let c ← resumeLoop o S fuel c
  pure (c, c.ans)

def Core.holds (c : Core) : Bool := !c.frames.isEmpty

/-- `Core::round`. -/
def Core.round (c : Core) : Except Err Core :=
  if c.rounds + 1 > c.lim.maxRounds then .error .tooManyRounds else .ok { c with rounds := c.rounds + 1 }

def Core.frameCap (c : Core) : Nat := c.lim.cap + 2 * c.lim.maxItem + 4 * varMax

/-- `Core::body`: the body of a received message, within the frame cap. -/
def Core.body (c : Core) (msg : List Nat) : Except Err (List Nat) :=
  match frameBody msg with
  | .error e => .error (.malformed e)
  | .ok b => if b.length > c.frameCap then .error .messageTooLarge else .ok b

/-- `Core::finish`: frame the header, the part count and the body. -/
def Core.finish (c : Core) (withHdr : Bool) (cnt : Nat) (more : Bool) : Except Err (List Nat) :=
  let body := (if withHdr then c.hdr else []) ++ putParts cnt more ++ c.out.body
  match frameHeader body.length with
  | none => .error .messageTooLarge
  | some h => if body.length > c.frameCap then .error .messageTooLarge else .ok (h ++ body)

/-- `end_msg`: the empty message. -/
def Core.endMsg (c : Core) : Except Err (List Nat) := { c with out := c.out.reset }.finish false 0 false

/-- `root`: the root parts of the initiator. -/
def Core.root (o : Oracle) (S : List Item) (c : Core) : Except Err (Core × Nat) := do
  let c := { c with out := c.out.reset }
  let n := c.n
  let ok ← if n ≤ aleaf then leafOk c.lim S [] none 0 n c.exact else pure false
  if ok then
    let c := { c with leafed := true }
    let out ← if c.exact then itemsPart c.lim S c.out tFULL [] none 0 n else idsPart o c.lim S c.out [] none 0 n
    pure ({ c with out := out }, 1)
  else
    let (out, cnt) ← splitFit o c.lim S c.out [] none 0 n 0 3
    pure ({ c with out := out }, cnt)

/-- `Core::start`: the first message of the initiator, for the set named `ref`. -/
def Core.start (o : Oracle) (S : List Item) (c : Core) (ref : Item) : Except Err (Core × List Nat) := do
  if ref.length > c.lim.maxItem then throw .itemTooLarge
  let c := c.clear
  let c := { c with n := S.length, hdr := venc ref.length ++ ref ++ venc S.length }
  let (c, cnt) ← c.root o S
  pure (c, ← c.finish true cnt false)

/-- `restart_exact`: restart from the root with items in place of ids, after the final check disagreed. -/
def Core.restartExact (o : Oracle) (S : List Item) (c : Core) : Except Err (Core × List Nat) := do
  let c := { c with exact := true, leafed := false, frames := [], here := [], there := [] }
  let (c, cnt) ← c.root o S
  pure (c, ← c.finish false cnt false)

/-- `check_msg`: the fingerprint the responder's whole set must have if the reported difference is exact. -/
def Core.checkMsg (o : Oracle) (S : List Item) (c : Core) : Except Err (Core × List Nat) := do
  let fp := fpRange o S 0 c.n ^^^ xorH o c.here ^^^ xorH o c.there
  let c := { c with out := (c.out.reset.head tCHECK [] none) }
  let c := { c with out := { c.out with body := c.out.body ++ fpBytes fp } }
  pure (c, ← c.finish false 1 false)

/-- `is_cold`. -/
def isCold (na nb : Nat) : Bool := decide (nb ≤ aleaf) || decide (na * coldRatio < nb)

/-- `cold_chunk`: the next chunk of the whole list as a cold part; whether it was the last. -/
def Core.coldChunk (S : List Item) (c : Core) : Except Err (Core × List Nat × Bool) := do
  let lim := c.lim
  let n := c.n
  let i := c.coldAt
  let budget := min lim.cap (1 <<< 20)
  let fixed := 2 * varMax + boundLen c.coldLo.length
  let rec go (j : Nat) (longest : Nat) (stage : List Nat) (fuel : Nat) : Except Err (Nat × List Nat) :=
    match fuel with
    | 0 => .ok (j, stage)
    | f + 1 =>
      if j < n then do
        let x ← readItem lim S j
        let longest := max longest x.length
        if j > i ∧ stage.length + x.length + varMax + fixed + boundLen (longest + 1) > budget then pure (j, stage)
        else go (j + 1) longest (stage ++ venc x.length ++ x) f
      else pure (j, stage)
  let (j, stage) ← go i 0 [] (n - i + 1)
  let last := decide (j ≥ n)
  let out := c.out.reset
  let (out, lo') ← if last then pure (out.head tCOLD c.coldLo none, c.coldLo) else do
    let p ← readItem lim S (j - 1)
    let q ← readItem lim S j
    let k := cpl p q + 1
    if k > q.length then throw .badIndex
    let sep := q.take k
    pure (out.head tCOLD c.coldLo (some sep), sep)
  let out := { out with body := out.body ++ venc (j - i) ++ stage, stage := stage }
  let c := { c with out := out, coldLo := lo', coldAt := j }
  pure (c, ← c.finish false 1 false, last)

/-! ## The handlers -/

inductive Phase where
  | idle | open | checking | done
  deriving DecidableEq, Repr

inductive Side where
  | fresh | open | cold | done
  deriving DecidableEq, Repr

structure Initiator where
  core : Core
  phase : Phase := .idle

structure Responder where
  core : Core
  side : Side := .fresh

/-- `Initiator::start`. -/
def Initiator.start (o : Oracle) (S : List Item) (s : Initiator) (ref : Item) : Except Err (Initiator × List Nat) := do
  let (c, msg) ← s.core.start o S ref
  pure ({ core := c, phase := .open }, msg)

/-- `Initiator::close`: the exchange has nothing left to say: verify if leaves were exchanged, else end. -/
def Initiator.close (o : Oracle) (S : List Item) (s : Initiator) (peerDone : Bool) :
    Except Err (Step × List Nat × Initiator) := do
  if s.phase = .checking then pure (.done, [], { s with phase := .done })
  else if s.core.leafed then
    let (c, msg) ← s.core.checkMsg o S
    pure (.send, msg, { core := c, phase := .checking })
  else if peerDone then pure (.done, [], { s with phase := .done })
  else pure (.last, ← s.core.endMsg, { s with phase := .done })

/-- `Initiator::handle`. -/
def Initiator.handle (o : Oracle) (S : List Item) (s : Initiator) (msg : List Nat) :
    Except Err (Step × List Nat × Initiator) := do
  if !(s.phase = .open ∨ s.phase = .checking) then throw (.malformed .state)
  let c ← s.core.round
  let body ← c.body msg
  let ((np, more), r) ← lr (readParts body)
  let (c, ans) ← c.turn o S r np
  let s := { s with core := c }
  if ans.cold then
    if ans.coldEnd then pure (.done, [], { s with phase := .done }) else pure (.wait, [], s)
  else
    if s.phase = .checking ∧ np > 0 ∧ !ans.miss then throw (.malformed .state)
    if ans.miss then
      if c.exact then throw .mismatch
      else
        let (c, msg) ← c.restartExact o S
        pure (.send, msg, { core := c, phase := .open })
    else if ans.cnt > 0 ∨ c.holds then
      pure (.send, ← c.finish false ans.cnt c.holds, s)
    else if more then pure (.send, ← c.endMsg, s)
    else s.close o S (np == 0)

/-- `Responder::resume`: the next chunk of a cold stream. -/
def Responder.resume (o : Oracle) (S : List Item) (s : Responder) : Except Err (Step × List Nat × Responder) :=
  if s.side != .cold then .error (.malformed .state)
  else
    match s.core.coldChunk S with
    | .error e => .error e
    | .ok (c, msg, last) =>
      if last then .ok (.last, msg, { core := c, side := .done }) else .ok (.chunk, msg, { s with core := c })

/-- The rounds of a responder session after the first message: count the round and answer the parts. -/
def Responder.run (o : Oracle) (S : List Item) (s : Responder) (r : List Nat) :
    Except Err (Step × List Nat × Responder) := do
  let c ← s.core.round
  let ((np, more), r) ← lr (readParts r)
  let (c, ans) ← c.turn o S r np
  if ans.cnt > 0 ∨ c.holds then pure (.send, ← c.finish false ans.cnt c.holds, { core := c, side := .open })
  else if more then pure (.send, ← c.endMsg, { core := c, side := .open })
  else if np == 0 then pure (.done, [], { core := c, side := .done })
  else pure (.last, ← c.endMsg, { core := c, side := .done })

/-- `Responder::handle`. -/
def Responder.handle (o : Oracle) (S : List Item) (s : Responder) (msg : List Nat) :
    Except Err (Step × List Nat × Responder) := do
  let fresh := s.side == .fresh
  if !fresh ∧ s.side != .open then throw (.malformed .state)
  let body ← s.core.body msg
  if fresh then
    let c := s.core.clear
    let (l, r1) ← lr (count body)
    if l > c.lim.maxItem then throw .itemTooLarge
    let (_, r2) ← lr (readBytes l r1)
    let (na, r3) ← lr (readVarint r2)
    let c := { c with n := S.length }
    if isCold na c.n then
      Responder.resume o S { core := { c with coldAt := 0, coldLo := [] }, side := .cold }
    else Responder.run o S { core := c, side := .open } r3
  else Responder.run o S s body

/-! ## The state a refused message leaves

`Initiator::handle` and `Responder::handle` wrap the rules above: a refused message ends the session of the object that
refused it (`Idle` for an initiator that was open or checking, `Done` for a responder that was not fresh or that refused the
rest of a first message; a fresh responder that refused the header of its first message keeps no state), so a caller that ignores the error and goes on is refused with
`Reason::State` until it starts again. `Responder::resume` ends a cold stream the same way. -/

/-- The initiator after `handle` returned an error. -/
def Initiator.afterErr (s : Initiator) : Initiator :=
  if s.phase = .open ∨ s.phase = .checking then { s with phase := .idle } else s

/-- Whether the header of a first message is refused before the responder commits to the session: the frame, the set
reference and the size of the other set. A refusal there leaves a fresh responder fresh. -/
def Responder.headerRefused (s : Responder) (msg : List Nat) : Bool :=
  match s.core.body msg with
  | .error _ => true
  | .ok body =>
    match lr (count body) with
    | .error _ => true
    | .ok (l, r1) =>
      decide (l > s.core.lim.maxItem) ||
        match lr (readBytes l r1) with
        | .error _ => true
        | .ok (_, r2) => match lr (readVarint r2) with | .error _ => true | .ok _ => false

/-- The responder after `handle` returned an error on `msg`. -/
def Responder.afterErr (s : Responder) (msg : List Nat) : Responder :=
  if s.side = .fresh ∧ s.headerRefused msg then s else { s with side := .done }

/-- The responder after `resume` returned an error. -/
def Responder.afterResumeErr (s : Responder) : Responder := { s with side := .done }

end Pinc.Reconcile
