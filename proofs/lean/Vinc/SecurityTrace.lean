import Vinc.Json
import Vinc.ReplayWindow
import Vinc.Amp
import Vinc.Token

/-!
# Replay of the record-layer traces

The replay half of the trace validation of `ReplayWindow`, `AmpBudget` and the token checks: it reads the events the
Rust test records and checks each against the proved model functions.

* `rw`: one `check` or `insert` of a window of `bits` packet numbers. `seq = 0` starts a fresh window. The answer
  (accepted, `Duplicate`, `TooOld`) and the highest number after the call (`-1` if none) must equal those of
  `ReplayWindow.check` / `ReplayWindow.insert`.
* `amp`: one `on_receive`, `on_send`, `validate` or `can_send` of an `AmpBudget`; `seq = 0` starts a fresh budget. The
  getters after the call (and the answer of `can_send`) must equal the model's, `Amp.onReceive`, `Amp.onSend` (both
  saturating) and `Amp.canSend`.
* `tok`: the checks `validate` makes after the AEAD opened (kind, address, age) for a recorded issue time and `now`
  must give the recorded outcome of `Token.verdict`.
-/

namespace Vinc.SecurityTrace
open Vinc.Json

/-- The model state of the current window run and budget run. -/
structure SecState where
  wrun : Nat := 0
  wbits : Nat := 1
  win : ReplayWindow.State := ReplayWindow.State.new
  arun : Nat := 0
  amp : Amp.Budget := Amp.Budget.new

instance : Inhabited SecState := ⟨{}⟩

/-- Replay one window event. -/
def replayWindow (j : J) (st : SecState) : Except String SecState := do
  let run ← natF j "run"
  let seq ← natF j "seq"
  let st ← if seq == 0 then do
      let b ← natF j "bits"
      check (1 ≤ b && b ≤ 1024) s!"window size {b} outside 1..=1024"
      pure { st with wrun := run, wbits := b, win := ReplayWindow.State.new }
    else do
      check (run == st.wrun) s!"window event of run {run} outside its run {st.wrun}"
      pure st
  let op ← strF j "op"
  let pn ← natF j "pn"
  let ok ← boolF j "ok"
  let err ← strF j "err"
  let hi ← intF j "hi"
  let B := st.wbits
  let w := st.win
  let (res, next) : Except ReplayWindow.Err Unit × ReplayWindow.State ←
    match op with
    | "c" => pure (ReplayWindow.check B w pn, w)
    | "i" =>
      pure (match ReplayWindow.insert B w pn with
        | .ok w' => (.ok (), w')
        | .error e => (.error e, w))
    | _ => throw s!"unknown window op {op}"
  let (mok, merr) : Bool × String := match res with
    | .ok () => (true, "none")
    | .error .dup => (false, "dup")
    | .error .tooOld => (false, "old")
  check (mok == ok && merr == err)
    s!"window {op} {pn} (bits {B}, run {run}, seq {seq}): model {merr} (accepted {mok}), code {err} (accepted {ok})"
  let expected : Int := if next.started then (next.highest : Int) else -1
  check (hi == expected) s!"window {op} {pn} (bits {B}, run {run}, seq {seq}): highest model {expected}, code {hi}"
  pure { st with win := next }

/-- Replay one amplification-budget event. -/
def replayAmp (j : J) (st : SecState) : Except String SecState := do
  let run ← natF j "run"
  let seq ← natF j "seq"
  let st := if seq == 0 then { st with arun := run, amp := Amp.Budget.new } else st
  check (run == st.arun) s!"amp event of run {run} outside its run {st.arun}"
  let op ← strF j "op"
  let n ← natF j "n"
  let b := st.amp
  let next ← match op with
    | "rx" => pure (Amp.onReceive b n)
    | "tx" => pure (Amp.onSend b n)
    | "val" => pure (Amp.validate b)
    | "can" => do
      let can ← boolF j "can"
      check (Amp.canSend b n == can) s!"amp can_send {n} (run {run}, seq {seq}): model {Amp.canSend b n}, code {can}"
      pure b
    | _ => throw s!"unknown amp op {op}"
  check (next.rx == (← natF j "rx") && next.tx == (← natF j "tx") && next.validated == (← boolF j "valid"))
    s!"amp {op} {n} (run {run}, seq {seq}): model rx {next.rx} tx {next.tx} valid {next.validated}"
  pure { st with amp := next }

/-- The recorded outcome string of a verdict. -/
def verdictName : Token.Verdict → String
  | .ok => "ok"
  | .malformed => "malformed"
  | .auth => "auth"
  | .kind => "kind"
  | .addr => "addr"
  | .notYet => "notyet"
  | .expired => "expired"

/-- Replay one token event. -/
def replayToken (j : J) : Except String Unit := do
  let kind ← match (← natF j "kind") with
    | 1 => pure Token.Kind.retry
    | 2 => pure Token.Kind.newToken
    | k => throw s!"unknown token kind {k}"
  let issued ← natF j "issued"
  let now ← natF j "now"
  let res ← strF j "res"
  let v := Token.verdict (← boolF j "kindok") (← boolF j "addrok") issued now kind
  check (verdictName v == res) s!"token issued {issued} now {now}: model {verdictName v}, code {res}"

/-- Replay one security event (`rw`, `amp` or `tok`) against the model state. -/
def replayEvent (j : J) (st : SecState) : Except String SecState := do
  match (← strF j "t") with
  | "rw" => replayWindow j st
  | "amp" => replayAmp j st
  | "tok" => do replayToken j; pure st
  | t => throw s!"unknown security event {t}"

end Vinc.SecurityTrace
