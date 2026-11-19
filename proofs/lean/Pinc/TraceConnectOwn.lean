import Pinc.Json
import Pinc.ConnectOwn

/-!
# Replay of the own record and address discovery trace

The replay half of the trace validation of the node's own record and address discovery (the Rust test
`trace_connect_own`, the TLA+ half is `TraceConnectOwn.tla`). Every recorded call is replayed through the functions the
theorems of `ConnectOwnThm.lean` are about and any difference exits with an error naming the line: the candidate list
the node offered after the call, whether an answer was taken, the last sequence number after a restore, and for a call
that may start a record job (a tick, an answer to a signature) whether a job started and the fields of the record: the
sequence number, the home, the class, the addresses and the hints.
-/

namespace Pinc.TraceConnectOwn
open Pinc.Json Pinc.ConnectOwn

structure W where
  cf : Cf := ⟨8, [0]⟩
  st : St := St.new ⟨8, [0]⟩

instance : Inhabited W := ⟨{}⟩

def optN (n : Nat) : Option Nat := if n = 0 then none else some n

def offered (j : J) (cf : Cf) (st : St) : Except String Unit := do
  let c ← natList (← field j "c")
  check (c == cands cf st) s!"candidates: model {cands cf st}, code {c}"

/-- `start_jobs` after the call: the job slot was `before` (the record outstanding); returns the state after. -/
def started (j : J) (cf : Cf) (st : St) : Except String St := do
  let hm ← natF j "hm"
  let cl ← natF j "cl"
  let s' := step cf st (.start 0 (optN hm) (optN cl))
  let jb ← natF j "j"
  if jb == 1 then
    let r : Rec := ⟨← natF j "seq", ← natF j "home", ← natF j "reach", ← natList (← field j "a"), ← natList (← field j "h")⟩
    check (st.job.isNone && s'.job == some r) s!"job: model {repr s'.job}, code {repr r}"
  else
    check (s'.job == st.job) s!"job: the model starts {repr s'.job}, the code none"
  pure s'

def replayEvent (j : J) (w : W) : Except String W := do
  let cf := w.cf
  let st := w.st
  match (← strF j "t") with
  | "onew" =>
    let cf : Cf := ⟨← natF j "cap", ← natList (← field j "udp")⟩
    let st := St.new cf
    offered j cf st
    pure { cf := cf, st := st }
  | "olocal" =>
    let st := setLocal cf st (← natList (← field j "a"))
    offered j cf st
    pure { w with st := st }
  | "oprobe" =>
    let ns := (← natList (← field j "n")).map optN
    let st := probeAll cf st ns
    offered j cf st
    pure { w with st := st }
  | "oans" =>
    let (st, took) := observe cf st (← natF j "from") (← natF j "n") (← natF j "a")
    check (took == ((← natF j "took") == 1)) s!"answer: model took {took}, code {← natF j "took"}"
    offered j cf st
    pure { w with st := st }
  | "orestart" =>
    let st := restart st
    offered j cf st
    pure { w with st := st }
  | "onoop" =>
    offered j cf st
    pure w
  | "oseq" =>
    let st := step cf st (.restore (← natF j "n"))
    let last ← natF j "last"
    check (st.last == last) s!"last number: model {st.last}, code {last}"
    offered j cf st
    pure { w with st := st }
  | "ohint" =>
    let h ← natList (← field j "h")
    let st := if (← natF j "ok") == 1 then setHints st h else st
    offered j cf st
    pure { w with st := st }
  | "otick" =>
    let st := tick st (optN (← natF j "w"))
    offered j cf st
    pure { w with st := ← started j cf st }
  | "osign" =>
    check st.job.isSome "an answer to a signature the model does not wait for"
    let st := signed st 0 true false
    offered j cf st
    pure { w with st := ← started j cf st }
  | t => throw s!"unknown own record event {t}"

/-- The tags this module replays. -/
def isTag (t : String) : Bool :=
  ["onew", "olocal", "oprobe", "oans", "orestart", "onoop", "oseq", "ohint", "otick", "osign"].contains t

end Pinc.TraceConnectOwn
