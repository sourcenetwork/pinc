import Vinc.Json
import Vinc.Varint
import Vinc.Ranges
import Vinc.Layout
import Vinc.TraceVerifier
import Vinc.TraceBuilder
import Vinc.SecurityTrace
import Vinc.HandshakeTrace
import Vinc.TraceKeyRoll
import Vinc.TraceKeyLayer
import Vinc.TraceStreams
import Vinc.TraceRecovery
import Vinc.TraceRx
import Vinc.TraceCid
import Vinc.TraceCc
import Vinc.TracePn
import Vinc.TraceReasm
import Vinc.TraceHdr
import Vinc.TraceFrame
import Vinc.TraceOrphan
import Vinc.TraceHalfOpen
import Vinc.TraceMtu
import Vinc.TraceTimers
import Vinc.TraceStores
import Vinc.TraceValuesSys
import Vinc.TraceValuesPlan
import Vinc.TraceValuesSched
import Vinc.ValuesWireTrace
import Vinc.ValuesVerifyTrace
import Vinc.ValuesTimeTrace
import Vinc.TraceConnectMailbox
import Vinc.TraceConnectTable
import Vinc.TraceConnectCodec
import Vinc.TraceConnectLink
import Vinc.TraceConnectClient
import Vinc.TraceConnectCarrier
import Vinc.TraceConnect
import Vinc.TraceTranscript
import Vinc.TraceCrypto
import Vinc.TraceKeystore
import Vinc.TraceDtnStore
import Vinc.TraceDtnForward
import Vinc.TraceDtnRs
import Vinc.TraceDtnCodec
import Vinc.TraceDtnReception
import Vinc.TraceDtnSeal
import Vinc.TraceDtnScenario
import Vinc.TraceDtnLayout
import Vinc.TraceMembershipInc
import Vinc.TraceMembershipCodec
import Vinc.TraceMembership
import Vinc.BroadcastTrace
import Vinc.TraceReconcile
import Vinc.TraceReconcileWire

/-!
# Trace replay

`replay <file>...` replays the ndjson traces written by the Rust test `trace_ranges` against the Lean model
functions (`Vinc.Varint.decode`, `Vinc.Varint.encodeInto`, `Vinc.Ranges.insertFixed`, `insertVec`, `find`,
`containsRange`, `coveredLen`, `Vinc.Layout.groupRange`, `groups`) and the traces written by `trace_verifier`
(the verifier model `Vinc.Tree.feed`, see `Vinc.TraceVerifier`; the layout sizes). Any difference between what the code
recorded and what the proved model computes exits with an error naming the line.
-/

open Vinc Vinc.Json

/-- Replay one varint or layout event. -/
private def replayPure (j : J) (t : String) : Except String Unit := do
  match t with
  | "venc" =>
    let v ← natF j "v"
    let cap ← natF j "cap"
    let res := Varint.encodeInto cap v
    match j.get? "ok", j.get? "err" with
    | some b, _ =>
      let bytes ← natList b
      check (match res with | .ok r => r == bytes | .error _ => false) s!"encode {v}: model {repr (match res with | .ok r => r | .error _ => [])}, code {bytes}"
    | _, some _ =>
      let e ← strF j "err"
      let expected : Varint.Error ← match e with
        | "overflow" => pure .overflow
        | "small" => pure (.bufferTooSmall (← natF j "needed"))
        | _ => throw s!"unknown error {e}"
      check (match res with | .error r => r == expected | .ok _ => false) s!"encode {v}: expected error {e}"
    | _, _ => throw "venc needs ok or err"
  | "vdec" =>
    let bytes ← natList (← field j "bytes")
    let res := Varint.decode bytes
    match j.get? "ok", j.get? "err" with
    | some p, _ =>
      match ← natList p with
      | [v, n] => check (match res with | .ok (a, b) => a == v && b == n | .error _ => false) s!"decode {bytes}: expected ({v}, {n})"
      | _ => throw "bad ok pair"
    | _, some _ =>
      let e ← strF j "err"
      let expected : Varint.Error ← match e with
        | "toolong" => pure .tooLong
        | "truncated" => pure .truncated
        | "nonminimal" => pure .nonMinimal
        | _ => throw s!"unknown error {e}"
      check (match res with | .error r => r == expected | .ok _ => false) s!"decode {bytes}: expected error {e}"
    | _, _ => throw "vdec needs ok or err"
  | "grange" =>
    let len ← natF j "len"
    let log ← natF j "log"
    let s ← natF j "s"
    let e ← natF j "e"
    check (Layout.groups len log == (← natF j "groups")) s!"groups {len} {log}"
    let res := Layout.groupRange len log s e
    match j.get? "ok" with
    | some p =>
      match ← natList p with
      | [a, b] => check (res == some (a, b)) s!"group_range {len} {log} {s} {e}: expected ({a}, {b})"
      | _ => throw "bad ok pair"
    | none => check res.isNone s!"group_range {len} {log} {s} {e}: expected an error"
  | "sizes" => TraceVerifier.replaySizes j
  | "enc" => TraceVerifier.replayEncoder j
  | "encout" => TraceVerifier.replayEncout j
  | _ => throw s!"unknown event {t}"

/-- Replay one verified-range event against the model state of its run; returns the new model state. -/
private def replayRanges (j : J) (items : List Ranges.Interval) : Except String (List Ranges.Interval) := do
  let kind ← strF j "kind"
  let n ← natF j "n"
  let seq ← natF j "seq"
  let s ← natF j "s"
  let e ← natF j "e"
  let ok ← boolF j "ok"
  let items := if seq == 0 then [] else items
  let (modelOk, next) ← match kind with
    | "fixed" => pure ((Ranges.insertFixed n items (s, e)).isSome, Ranges.insertState n items (s, e))
    | "vec" => pure (true, Ranges.insertVec items (s, e))
    | _ => throw s!"unknown kind {kind}"
  check (modelOk == ok) s!"insert [{s}, {e}) on {items}: model ok = {modelOk}, code ok = {ok}"
  let recorded ← pairList (← field j "items")
  check (next == recorded) s!"insert [{s}, {e}) on {items}: model {next}, code {recorded}"
  check (Ranges.coveredLen next == (← natF j "cl")) s!"covered_len of {next}"
  check (Ranges.contains next (← natF j "x") == (← boolF j "cx")) s!"contains of {next}"
  check (Ranges.containsRange next (← natF j "cs", ← natF j "ce") == (← boolF j "cr")) s!"contains_range of {next}"
  pure next

/-- Replay one file: the number of events that matched the model, and the number of those that were handshake (`hs`) events. -/
private def replayFile (path : String) : IO (Nat × Nat) := do
  let text ← IO.FS.readFile path
  let mut items : List Ranges.Interval := []
  let mut vs : TraceVerifier.RState := {}
  let mut sec : SecurityTrace.SecState := {}
  let mut count := 0
  let mut bst : TraceBuilder.BState := {}
  let mut hsw : HandshakeTrace.W := {}
  let mut hsCount := 0
  let mut stw : TraceStores.W := {}
  let mut krs : TraceKeyRoll.KState := {}
  let mut kls : TraceKeyLayer.KL := {}
  let mut vyw : TraceValuesSys.W := {}
  let mut vps : TraceValuesPlan.Srv := {}
  let mut vsw : TraceValuesSched.RS := {}
  let mut gvw : ValuesVerifyTrace.W := {}
  let mut vtw : ValuesTimeTrace.W := default
  let mut cmb : TraceConnectMailbox.W := {}
  let mut ctb : TraceConnectTable.W := {}
  let mut crl : TraceConnect.W := {}
  let mut clk : TraceConnectLink.W := {}
  let mut ccl : TraceConnectClient.W := {}
  let mut cca : TraceConnectCarrier.W := {}
  let mut trs : TraceTranscript.TS := {}
  let mut trCount := 0
  let mut dsw : TraceDtnStore.W := {}
  let mut dfw : TraceDtnForward.W := {}
  let mut drs : TraceDtnRs.W := {}
  let mut dcx : TraceDtnCodec.W := {}
  let mut drx : TraceDtnReception.W := {}
  let mut dss : TraceDtnSeal.W := {}
  let mut dsc : TraceDtnScenario.W := {}
  let mut mis : TraceMembershipInc.W := {}
  let mut mems : TraceMembership.W := {}
  let mut sts : TraceStreams.St := {}
  let mut rcs : TraceRecovery.St' := {}
  let mut rxw : TraceRx.W := {}
  let mut cidw : TransportCid.C := {}
  let mut ccw : TraceCc.W := {}
  let mut rsw : TraceReasm.W := {}
  let mut orw : TraceOrphan.W := {}
  let mut how : TraceHalfOpen.W := {}
  let mut mtw : TransportMtu.M := {}
  let mut tmw : TraceTimers.W := {}
  let mut bcw : BroadcastTrace.W := {}
  let mut rcw : TraceReconcile.W := {}
  let mut ksw : TraceKeystore.W := {}
  let mut lineNo := 0
  for line in text.splitOn "\n" do
    lineNo := lineNo + 1
    if line.trimAscii.isEmpty then continue
    -- Security events (`lbl`, `cred`, `amp`, `pad`) go to the security replay, which carries its own model state.
    if let .ok j := parse line then
      match j.get? "t" |>.bind (·.str?) with
      | some "hs" =>
        -- Handshake events (`hs`, written by `trace_handshake`): every step goes through the Lean step functions.
        match HandshakeTrace.replayEvent j hsw with
        | .ok w' =>
          hsw := w'
          hsCount := hsCount + 1
          count := count + 1
          continue
        | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
      | some t =>
        if TraceDtnStore.isTag t then
          -- Delay-tolerant layer events (`trace_dtn_*`): the Lean models of `vinc-dtn`.
          match TraceDtnStore.replayEvent j dsw with
          | .ok w' =>
            dsw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceDtnForward.isTag t then
          -- Delay-tolerant layer events (`trace_dtn_*`): the Lean models of `vinc-dtn`.
          match TraceDtnForward.replayEvent j dfw with
          | .ok w' =>
            dfw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceDtnRs.isTag t then
          -- Delay-tolerant layer events (`trace_dtn_*`): the Lean models of `vinc-dtn`.
          match TraceDtnRs.replayEvent j drs with
          | .ok w' =>
            drs := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceDtnCodec.isTag t then
          -- Delay-tolerant layer events (`trace_dtn_*`): the Lean models of `vinc-dtn`.
          match TraceDtnCodec.replayEvent j dcx with
          | .ok w' =>
            dcx := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceDtnReception.isTag t then
          -- Delay-tolerant layer events (`trace_dtn_*`): the Lean models of `vinc-dtn`.
          match TraceDtnReception.replayEvent j drx with
          | .ok w' =>
            drx := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceDtnSeal.isTag t then
          -- Delay-tolerant layer events (`trace_dtn_*`): the Lean models of `vinc-dtn`.
          match TraceDtnSeal.replayEvent j dss with
          | .ok w' =>
            dss := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceDtnScenario.isTag t then
          -- Delay-tolerant layer events (`trace_dtn_*`): the Lean models of `vinc-dtn`.
          match TraceDtnScenario.replayEvent j dsc with
          | .ok w' =>
            dsc := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceDtnLayout.isTag t then
          match TraceDtnLayout.replayEvent j with
          | .ok () =>
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceStores.isStoreTag t then
          -- Ticket store and prekey cache events (`trace_stores`): the Lean functions the store theorems are about.
          match TraceStores.replayEvent j stw with
          | .ok w' =>
            stw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if ValuesVerifyTrace.isTag t then
          -- GroupVerifier events (`trace_values_verify`): `feedG` and `skipG` next to the RangeVerifier replay.
          match ValuesVerifyTrace.replayEvent j gvw with
          | .ok w' =>
            gvw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if ValuesWireTrace.isWireTag t then
          -- Value wire codec events (`trace_values_wire`): REQ, GROUP header, PROOF and PROOF_REQ parse and encode.
          match ValuesWireTrace.replayEvent j with
          | .ok () =>
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "rc" && (j.get? "e").isSome then
          -- Reconciliation events (`rc` with an `e` field, written by `trace_reconcile`; an `rc` without one is loss recovery): the byte-level session model.
          match TraceReconcile.replayEvent j rcw with
          | .ok r' =>
            rcw := r'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "rw" then
          -- Reconcile wire events (`rw`, written by `trace_reconcile_wire`): the codec of `vinc-reconcile`.
          match TraceReconcileWire.replayEvent j with
          | .ok () =>
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "vs" then
          -- Scheduler events (`vs`, written by `trace_values_sched`): top-up, steal, eviction and verification on the model.
          match TraceValuesSched.replayChecked j vsw with
          | .ok w' =>
            vsw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if ValuesTimeTrace.isTag t then
          -- Time-rule events (`vtrun`, `vt`, written by `trace_values_time`): HEAD_HOLD, STALL_REDIAL, the deadline.
          match ValuesTimeTrace.replayEvent j vtw with
          | .ok w' =>
            vtw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "vsys" then
          -- Value fetch system events (`vsys`, written by `trace_values_sys`): the model `Vinc.ValuesSys` of the whole fetch.
          match TraceValuesSys.replayEvent j vyw with
          | .ok w' =>
            vyw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceConnect.isTag t then
          -- Relay events (`trace_connect`): every call and every effect through the Lean relay model.
          match TraceConnect.replayEvent j crl with
          | .ok w' =>
            crl := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceConnectLink.isTag t then
          -- Client carrier events (`trace_connect_link`): the Lean link state machine.
          match TraceConnectLink.replayEvent j clk with
          | .ok w' =>
            clk := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceConnectCarrier.isTag t then
          -- Protected carrier events (`cca`, written by `trace_connect_carrier`): framing, records, seals.
          match TraceConnectCarrier.replayEvent j cca with
          | .ok w' =>
            cca := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceConnectClient.isTag t then
          -- Client rule events (`trace_connect_client`): punch, tunnel, dial, lookup, netcheck.
          match TraceConnectClient.replayEvent j ccl with
          | .ok w' =>
            ccl := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceConnectCodec.isTag t then
          -- Wire format events (`trace_connect_codec`): the Lean frame, datagram, record, beacon, notice and ticket codecs.
          match TraceConnectCodec.replayEvent j with
          | .ok () =>
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceConnectTable.isTag t then
          -- Table and cache events (`trace_connect_table`): the Lean table model with the buckets of the real hash.
          match TraceConnectTable.replayEvent j ctb with
          | .ok w' =>
            ctb := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceConnectMailbox.isTag t then
          -- Mailbox events (`trace_connect_mailbox`): push, pop, sweep and clear of the Lean mailbox model.
          match TraceConnectMailbox.replayEvent j cmb with
          | .ok w' =>
            cmb := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceMembership.isTag t then
          -- Hub and member state machine events (`mem`, written by `trace_membership`): the model of the node.
          match TraceMembership.replayEvent j mems with
          | .ok m' =>
            mems := m'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceMembershipCodec.isTag t then
          -- Hub stream codec events (`mc`, written by `trace_membership`): the model of `codec.rs`.
          match TraceMembershipCodec.replayEvent j with
          | .ok () =>
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceMembershipInc.isTag t then
          -- Incarnation and address tag events (`mi`, written by `trace_membership`): the model of `incarnation.rs`.
          match TraceMembershipInc.replayEvent j mis with
          | .ok m' =>
            mis := m'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "bc" then
          -- Broadcast events (`bc`, written by `trace_broadcast`): the node operators the node theorems are about.
          match BroadcastTrace.replayEvent j bcw with
          | .ok b' =>
            bcw := b'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceCrypto.isTag t then
          -- `vinc-crypto` events (`cr`, written by `trace_crypto`): the KDF, identities, DRBG, provider and secrets.
          match TraceCrypto.replayEvent j with
          | .ok () =>
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "ks" || t == "kt" then
          -- `vinc-keystore` events (`ks`, `kt`, written by `trace_keystore` and `trace_keystore_tpm`).
          match TraceKeystore.replayEvent j ksw with
          | .ok w' =>
            ksw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "kr" then
          -- Key roll events (`kr`, written by `trace_keyroll`): the Roll machine, the packet keys, `due` and the REKEY codec.
          match TraceKeyRoll.replayEvent j krs with
          | .ok k' =>
            krs := k'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "tr" && (j.get? "label").isSome then
          -- Transcript events (`tr` with a label, written by `trace_transcript`; a `tr` without one is the tail repair of `trace_recovery`): the order of the fields every transcript absorbs.
          match TraceTranscript.replayEvent j trs with
          | .ok k' =>
            trs := k'
            trCount := trCount + 1
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "kl" then
          -- Key layer events (`kl`, written by `trace_keylayer`): the flip and hold layer of two real connections.
          match TraceKeyLayer.replayEvent j kls with
          | .ok k' =>
            kls := k'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceValuesPlan.isTag t then
          -- Plan, read_at and server proof-frame events (`trace_values_plan`): the Lean model functions of `ValuesPlan*`.
          match TraceValuesPlan.replayEvent j vps with
          | .ok v' =>
            vps := v'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceMtu.isTag t then
          -- Path MTU events (`txmt`, written by `trace_mtu`): probing, the floor and the black-hole fallback.
          match TraceMtu.replayEvent j mtw with
          | .ok w' =>
            mtw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceTimers.isTag t then
          -- Timer and closing events (`tmr`, written by `trace_timers`): poll_timeout, handle_timeout and the ends.
          match TraceTimers.replayEvent j tmw with
          | .ok w' =>
            tmw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceReasm.isTag t then
          -- Handshake fragment events (`txrs`, written by `trace_reasm`): the runs of a message put together.
          match TraceReasm.replayEvent j rsw with
          | .ok w' =>
            rsw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceHdr.isTag t then
          -- Packet header events (`txhd`, written by `trace_hdr`): the long and short header codecs, the packets of
          -- a datagram and the associated data of seal and open.
          match TraceHdr.replayEvent j with
          | .ok _ =>
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceFrame.isTag t then
          -- Frame codec events (`txfr`, written by `trace_frame`): decode, write, the iterator and the ACK ranges.
          match TraceFrame.replayEvent j with
          | .ok _ =>
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceOrphan.isTag t then
          -- Held first-flight fragment events (`coor`, written by `trace_orphan`): the endpoint's table of them.
          match TraceOrphan.replayEvent j orw with
          | .ok w' =>
            orw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceHalfOpen.isTag t then
          -- Half-open cap events (`coho`, written by `trace_halfopen`): admissions, the count and the lifetime.
          match TraceHalfOpen.replayEvent j how with
          | .ok w' =>
            how := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TracePn.isTag t then
          -- Packet-number codec events (`txpn`, written by `trace_pn`): truncation and expansion.
          match TracePn.replayEvent j with
          | .ok _ =>
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceCc.isTag t then
          -- Congestion control events (`txcc`, written by `trace_cc`): the cubic controller and the pacer.
          match TraceCc.replayEvent j ccw with
          | .ok w' =>
            ccw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceCid.isTag t then
          -- Connection id events (`txcid`, written by `trace_cid`): issuance, lookahead and retirement of derived ids.
          match TraceCid.replayEvent j cidw with
          | .ok w' =>
            cidw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if TraceRx.isTag t then
          -- Received-packet tracker events (`txrx`, written by `trace_rx`): the range set and the acknowledgement rules.
          match TraceRx.replayEvent j rxw with
          | .ok w' =>
            rxw := w'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "rc" || t == "tr" then
          -- Loss recovery events (`rc` and `tr`, written by `trace_recovery`): the sent ring, the probe timer and the tail repair.
          match TraceRecovery.replayEvent j rcs with
          | .ok s' =>
            rcs := s'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "st" then
          -- Stream table events (`st`, written by `trace_streams`): the receive and credit path of the stream layer.
          match TraceStreams.replayEvent j sts with
          | .ok s' =>
            sts := s'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "bnew" || t == "bupd" || t == "bfin" then
          -- Outboard builder events (`trace_builder`): the byte-level model of `update` and `finish`.
          match TraceBuilder.replayEvent j bst with
          | .ok b' =>
            bst := b'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
        if t == "lbl" || t == "cred" || t == "amp" || t == "pad" then
          match SecurityTrace.replayEvent j sec with
          | .ok s' =>
            sec := s'
            count := count + 1
            continue
          | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
      | none => pure ()
    let r : Except String (List Ranges.Interval × TraceVerifier.RState) := do
      let j ← parse line
      match j.get? "t" with
      | some t =>
        match t.str? with
        | some "vrun" => pure (items, ← TraceVerifier.replayRun vs j)
        | some "vfeed" => pure (items, ← TraceVerifier.replayFeed vs j)
        | some s =>
          replayPure j s
          pure (items, vs)
        | none => throw "t is not a string"
      | none => pure (← replayRanges j items, vs)
    match r with
    | .ok (next, vnext) =>
      items := next
      vs := vnext
      count := count + 1
    | .error msg => throw (IO.userError s!"{path}:{lineNo}: {msg}")
  -- A file of transcript lines must show every kind of transcript in full.
  if trCount > 0 then
    match TraceTranscript.covered trs with
    | .ok () => pure ()
    | .error msg => throw (IO.userError s!"{path}: {msg}")
  pure (count, hsCount)

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: replay <trace.ndjson>..."
    return 2
  let mut total := 0
  let mut hsTotal := 0
  for path in args do
    let (n, sk) ← replayFile path
    IO.println s!"replay: {path}: {n} events match the model, {sk} of them handshake steps through the Lean step functions"
    total := total + n
    hsTotal := hsTotal + sk
  IO.println s!"replay: ok, {total} events, {hsTotal} handshake steps replayed through the Lean step functions"
  return 0
