#!/usr/bin/env bash
# The proofs step of the gate: the Lean proofs, TLC on every TLA+ model, and trace validation of the Rust code
# against the TLA+ spec and the Lean model. Usage: scripts/proofs.sh
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"

TLA_HOME="${TLA_HOME:-$HOME/.local/share/tla}"
# Parallel TLC runs unpack the standard modules into the temp directory; give this run its own.
mkdir -p proofs/tla/states/tmp
export JAVA_TOOL_OPTIONS="${JAVA_TOOL_OPTIONS:-} -Djava.io.tmpdir=$PWD/proofs/tla/states/tmp"
# The trace check reads ndjson with the CommunityModules Json module, which needs a TLC of the same era as the jar.
TRACE_TLC="$TLA_HOME/tla2tools-2026.11.06.jar"
COMMUNITY="$TLA_HOME/CommunityModules-deps-202611060952.jar"
# TLC unpacks its standard modules into the JVM's temporary directory; runs that share one race on those files, so
# every run gets its own. The JVM's default heap bound is a quarter of the memory it sees, so 3 parallel runs could
# take 75% of the machine; 15% each keeps the 3 under half (of the cgroup limit, when the run has one).
jtmp_root=$(mktemp -d)
trap 'rm -rf "$jtmp_root"' EXIT
jopts() { printf -- '-XX:MaxRAMPercentage=15 -Djava.io.tmpdir=%s' "$(mktemp -d -p "$jtmp_root")"; }


need() { # need <file> <download command>
    [ -f "$1" ] || { echo "proofs: missing $1; fetch it with: $2" >&2; exit 1; }
}
need "$COMMUNITY" "curl -fsSL -o $COMMUNITY https://github.com/tlaplus/CommunityModules/releases/download/202611060952/CommunityModules-deps.jar"
need "$TRACE_TLC" "curl -fsSL -o $TRACE_TLC https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
command -v tlc >/dev/null || { echo "proofs: tlc not found; install TLC (a wrapper around tla2tools.jar) on PATH" >&2; exit 1; }
command -v lake >/dev/null || { echo "proofs: lake not found; install Lean 4 with elan (https://github.com/leanprover/elan)" >&2; exit 1; }

echo "-- lean"
if grep -rnE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b' proofs/lean/Vinc proofs/lean/Replay.lean proofs/lean/Vinc.lean \
    | grep -v '^proofs/lean/Vinc/Axioms.lean'; then
    echo "proofs: sorry, admit, axiom or native_decide in the Lean sources" >&2
    exit 1
fi
(cd proofs/lean && lake build)

run_tlc() { # run_tlc <name> <spec> <cfg> : model check one config, show the summary lines
    local out
    out=$(JAVA_TOOL_OPTIONS="$(jopts)" tlc -workers auto -metadir "proofs/tla/states/$1" -config "proofs/tla/$3.cfg" "proofs/tla/$2.tla" 2>&1) \
        || { echo "$out" >&2; echo "proofs: TLC failed on $3" >&2; exit 1; }
    echo "tlc $3: $(echo "$out" | grep -E 'states generated, ' | tail -1)"
}
run_tlc_deep() { # run_tlc_deep <name> <spec> <cfg> : like run_tlc, with the deep thread stack the word arithmetic of the specs needs
    local out
    out=$(JAVA_TOOL_OPTIONS="$(jopts)" java -Xss256m -XX:+UseParallelGC -cp "$TLA_HOME/tla2tools.jar" tlc2.TLC -workers auto \
        -metadir "proofs/tla/states/$1" -config "proofs/tla/$3.cfg" "proofs/tla/$2.tla" 2>&1) \
        || { echo "$out" >&2; echo "proofs: TLC failed on $3" >&2; exit 1; }
    echo "tlc $3: $(echo "$out" | grep -E 'states generated, ' | tail -1)"
}
witness_tlc() { # witness_tlc <name> <spec> <cfg> <property> : TLC must find a violation of <property> (a reachability witness or a documented finding)
    local out
    if out=$(JAVA_TOOL_OPTIONS="$(jopts)" tlc -workers auto -metadir "proofs/tla/states/$1" -config "proofs/tla/$3.cfg" "proofs/tla/$2.tla" 2>&1); then
        echo "$out" >&2; echo "proofs: TLC found no violation of $4 in $3: the witness is gone" >&2; exit 1
    fi
    grep -q "$4 is violated" <<<"$out" \
        || { echo "$out" >&2; echo "proofs: TLC failed on $3 for another reason than $4" >&2; exit 1; }
    echo "tlc $3: finds the expected violation of $4"
}
witness_live_tlc() { # witness_live_tlc <name> <spec> <cfg> : TLC must find a counterexample to the liveness property (the stuck states the code had)
    local out
    if out=$(JAVA_TOOL_OPTIONS="$(jopts)" tlc -workers auto -metadir "proofs/tla/states/$1" -config "proofs/tla/$3.cfg" "proofs/tla/$2.tla" 2>&1); then
        echo "$out" >&2; echo "proofs: TLC found no liveness violation in $3: the witness is gone" >&2; exit 1
    fi
    grep -q "Temporal properties were violated" <<<"$out" \
        || { echo "$out" >&2; echo "proofs: TLC failed on $3 for another reason than a liveness violation" >&2; exit 1; }
    echo "tlc $3: finds the expected liveness violation"
}
echo "-- tlc"
# The independent model checks run at most 3 at a time; a failure of any stops the script.
par() {
    while [ "$(jobs -rp | wc -l)" -ge 3 ]; do wait -n || exit 1; done
    "$@" &
}
par run_tlc ranges VerifiedRanges VerifiedRanges
par run_tlc ranges_n1 VerifiedRanges VerifiedRanges_n1
par run_tlc verifier RangeVerifier RangeVerifier
par run_tlc handshake Handshake Handshake
par run_tlc handshake_resume Handshake Handshake_resume
par run_tlc handshake_late Handshake Handshake_late
par run_tlc handshake_stores Handshake Handshake_stores
par run_tlc record Record Record
par run_tlc record_chacha Record Record_chacha
par run_tlc headerprot HeaderProt HeaderProt
par run_tlc headerprot_pn HeaderProt HeaderProt_pn
par run_tlc keyroll KeyRoll KeyRoll
par run_tlc keyroll_collide KeyRoll KeyRoll_collide
par run_tlc keyroll_two KeyRoll KeyRoll_two
par run_tlc keyroll_forge KeyRoll KeyRoll_forge
par witness_tlc keyroll_good KeyRoll KeyRoll_good NotGood
par run_tlc keyroll_stale KeyRoll KeyRoll_stale
par run_tlc keyroll_gate KeyRoll KeyRoll_gate
par run_tlc keyroll_orphan KeyRoll KeyRoll_orphan
par run_tlc labels Labels Labels
par run_tlc credit_w2 Credit Credit_w2
par run_tlc credit Credit Credit
par run_tlc transcript Transcript Transcript
par run_tlc amp Amp Amp
par run_tlc padding Padding Padding
par run_tlc_deep varint Varint Varint
par run_tlc_deep rekeycodec RekeyCodec RekeyCodec
par run_tlc_deep partition PartitionPoint PartitionPoint
par run_tlc_deep layout Layout Layout
par run_tlc_deep encoder Encoder Encoder
par run_tlc_deep builderbytes BuilderBytes BuilderBytes
par run_tlc_deep verifierbytes VerifierBytes VerifierBytes
par run_tlc tickets_client Tickets Tickets
par run_tlc tickets_client3 Tickets Tickets_n3
par run_tlc tickets_server Tickets Tickets_server
par run_tlc tickets_zero Tickets Tickets_zero
par run_tlc prekeycache PrekeyCache PrekeyCache
par run_tlc prekeycache_n0 PrekeyCache PrekeyCache_n0
par run_tlc prekeycache_n3 PrekeyCache PrekeyCache_n3
par run_tlc values_plan ValuesPlan ValuesPlan
par run_tlc values_plan_tight ValuesPlan ValuesPlan_tight
par run_tlc values_plan_word ValuesPlan ValuesPlan_word
par run_tlc values_plan_source ValuesPlanSource ValuesPlanSource
par run_tlc values_plan_proofs ValuesPlanProofs ValuesPlanProofs
par run_tlc values_plan_server ValuesPlanServer ValuesPlanServer
par run_tlc vsched_list ValuesSchedList ValuesSchedList
par run_tlc vsched_n2 ValuesSched ValuesSched_n2
par run_tlc vsched_n3 ValuesSched ValuesSched_n3
par run_tlc vsched_liar ValuesSched ValuesSched_liar
par run_tlc vsched_alllie ValuesSched ValuesSched_alllie
par run_tlc vsched_silent ValuesSched ValuesSched_silent
par run_tlc vsched_wants ValuesSched ValuesSched_wants
par run_tlc vsched_tight ValuesSched ValuesSched_tight
par run_tlc vsched_track ValuesSched ValuesSched_track
par run_tlc vsched_ends ValuesSched ValuesSched_ends
par run_tlc vsched_live ValuesSched ValuesSched_live
par witness_tlc vsched_wide ValuesSched ValuesSched_wide Room
par witness_tlc vsched_dup ValuesSched ValuesSched_dup ResumeFresh
par witness_tlc vsched_nocorr ValuesSched ValuesSched_nocorr NoStealOfJustGiven
par witness_tlc vsched_small ValuesSched ValuesSched_small NoSmallIdleSteal
par run_tlc vsys_n1 ValuesSys ValuesSys_n1
par run_tlc vsys_n2 ValuesSys ValuesSys_n2
par run_tlc vsys_n3 ValuesSys ValuesSys_n3
par run_tlc vsys_n3_live ValuesSys ValuesSys_n3_live
par run_tlc vsys_n4 ValuesSys ValuesSys_n4
par run_tlc vsys_drop ValuesSys ValuesSys_drop
par run_tlc vsys_slow ValuesSys ValuesSys_slow
par run_tlc vsys_steal ValuesSys ValuesSys_steal
par run_tlc vsys_liar ValuesSys ValuesSys_liar
par run_tlc vsys_alllie ValuesSys ValuesSys_alllie
par run_tlc vsys_restart ValuesSys ValuesSys_restart
par run_tlc vsys_resume ValuesSys ValuesSys_resume
par run_tlc vsys_loss ValuesSys ValuesSys_loss
par run_tlc vsys_extra ValuesSys ValuesSys_extra
par run_tlc vsys_deadline ValuesSys ValuesSys_deadline
par run_tlc vsys_deadline_ok ValuesSys ValuesSys_deadline_ok
par run_tlc vsys_badroot ValuesSys ValuesSys_badroot
par run_tlc vsys_noprov ValuesSys ValuesSys_noprov
par run_tlc vsys_store ValuesSys ValuesSys_store
par run_tlc vsys_done ValuesSys ValuesSys_done
par run_tlc vsys_mid ValuesSys ValuesSys_mid
par run_tlc vsys_code ValuesSys ValuesSys_code
par run_tlc vsys_code_steal ValuesSys ValuesSys_code_steal
par witness_tlc vsys_w_code_steal ValuesSys ValuesSys_w_code_steal NeverStolen
par witness_tlc vsys_midold ValuesSys ValuesSys_midold AnnOnce
par witness_tlc vsys_w_dup ValuesSys ValuesSys_w_dup NeverDup
par witness_tlc vsys_w_lied ValuesSys ValuesSys_w_lied NeverLiedFail
par witness_tlc vsys_w_deadline ValuesSys ValuesSys_w_deadline NeverDeadlineFail
par witness_tlc vsys_w_store ValuesSys ValuesSys_w_store NeverStoreFail
par witness_tlc vsys_w_ahead ValuesSys ValuesSys_w_ahead NeverAheadCommit
par witness_tlc vsys_w_liar_complete ValuesSys ValuesSys_w_liar_complete NeverLiarThenComplete
par witness_tlc vsys_w_steal ValuesSys ValuesSys_w_steal NeverStolen
par witness_tlc vsys_w_redial ValuesSys ValuesSys_w_redial NeverRedialed
par witness_live_tlc vsys_n2_old ValuesSys ValuesSys_n2_old
par witness_live_tlc vsys_n2_oldconn ValuesSys ValuesSys_n2_oldconn
par run_tlc valuestime_hold ValuesTime ValuesTime_hold
par run_tlc valuestime_holdsmall ValuesTime ValuesTime_holdsmall
par run_tlc valuestime_stall ValuesTime ValuesTime_stall
par run_tlc valuestime_live ValuesTime ValuesTime_live
par run_tlc valuestime_max ValuesTime ValuesTime_max
par run_tlc valuestime_dl ValuesTime ValuesTime_dl
par witness_tlc valuestime_seq ValuesTime ValuesTime_seq SwNot16
par witness_tlc valuestime_low ValuesTime ValuesTime_low SwNeverLowered
par run_tlc valuestime_dup ValuesTime ValuesTime_dup
par witness_tlc valuestime_wfirst ValuesTime ValuesTime_wfirst NoRedial
par run_tlc valuestime_tail ValuesTime ValuesTime_tail
par witness_tlc valuestime_wbuf ValuesTime ValuesTime_wbuf NoBuffered
par witness_tlc valuestime_wbufreal ValuesTime ValuesTime_wbufreal NoBuffered
par witness_tlc valuestime_wtail ValuesTime ValuesTime_wtail NoTail
par witness_tlc valuestime_wgran ValuesTime ValuesTime_wgran NoGranules
par witness_tlc valuestime_wtime ValuesTime ValuesTime_wtime NoTimeout
par witness_tlc valuestime_wdone ValuesTime ValuesTime_wdone NoDone
par run_tlc_deep valuesverify ValuesVerify ValuesVerify
par run_tlc_deep valuesverify_small ValuesVerify ValuesVerify_small
par run_tlc_deep valuesverify_real64 ValuesVerify ValuesVerify_real64
par run_tlc_deep valuesverify_real32 ValuesVerify ValuesVerify_real32
par run_tlc_deep valuesverify_skip ValuesVerify ValuesVerify_skip
par run_tlc_deep valuesverify_skip2 ValuesVerify ValuesVerify_skip2
par run_tlc_deep valuesverify_rx ValuesVerifyRx ValuesVerifyRx
par run_tlc_deep valueswire ValuesWire ValuesWire
par run_tlc connect_mailbox ConnectMailbox ConnectMailbox
par run_tlc connect_table ConnectTable ConnectTable
par run_tlc connect_table_n4 ConnectTable ConnectTable_n4
par run_tlc connect_cache ConnectTable ConnectTable_cache
par run_tlc connect_relay ConnectRelay ConnectRelay
par run_tlc dtn_store DtnStore DtnStore
par witness_tlc dtn_store_cross DtnStore DtnStore_cross NoCrossEviction
par run_tlc dtn_custody DtnCustody DtnCustody
par run_tlc dtn_custody_deep DtnCustody DtnCustody_deep
par run_tlc dtnforward DtnForward DtnForward
par run_tlc dtnforward_l1 DtnForward DtnForward_l1
par run_tlc dtnforward_live DtnForward DtnForward_live
par witness_tlc dtnforward_full DtnForward DtnForward_full DestServed
par run_tlc dtnforward_rehold DtnForward DtnForward_rehold
par run_tlc dtnforwardnet DtnForwardNet DtnForwardNet
par run_tlc dtnforwardnet_loss DtnForwardNet DtnForwardNet_loss
par run_tlc dtnforwardnet_replay DtnForwardNet DtnForwardNet_replay
par run_tlc dtnforwardnet_over DtnForwardNet DtnForwardNet_over
par run_tlc_deep dtngf DtnGf DtnGf
par run_tlc_deep dtnrs_a DtnRs DtnRs_a
par run_tlc_deep dtnrs_b DtnRs DtnRs_b
par run_tlc_deep dtnrs_c DtnRs DtnRs_c
par run_tlc_deep dtnrs_mds DtnRs DtnRs_mds
par run_tlc_deep dtnrs_bounds DtnRs DtnRs_bounds
par run_tlc_deep dtnlayout DtnLayout DtnLayout
par run_tlc_deep dtncodec DtnCodec DtnCodec
par run_tlc dtnreception DtnReception DtnReception
par run_tlc dtnreception_w3 DtnReception DtnReception_w3
par run_tlc_deep dtnclock DtnClock DtnClock
par run_tlc dtnseal DtnSeal DtnSeal
par run_tlc dtnseal_decap DtnSeal DtnSeal_decap
par run_tlc dtnseal_xbroken DtnSeal DtnSeal_xbroken
par run_tlc dtnseal_kbroken DtnSeal DtnSeal_kbroken
par witness_tlc dtnseal_nofs DtnSeal DtnSeal_nofs NotRevealed
par witness_tlc dtnseal_bothbroken DtnSeal DtnSeal_bothbroken NotRevealed
par witness_tlc dtnseal_reuse DtnSeal DtnSeal_reuse NonceUnique
par run_tlc dtn_sc_contacts DtnScenario DtnScenario_contacts
par run_tlc dtn_sc_chain DtnScenario DtnScenario_chain
par run_tlc dtn_sc_spray DtnScenario DtnScenario_spray
par run_tlc dtn_sc_expiry DtnScenario DtnScenario_expiry
par run_tlc dtn_sc_pressure DtnScenario DtnScenario_pressure
par run_tlc dtn_sc_tight DtnScenario DtnScenario_tight
par run_tlc dtn_sc_live DtnScenario DtnScenario_live
par run_tlc dtn_sc_live_relay DtnScenario DtnScenario_live_relay
par witness_tlc dtn_sc_nolive DtnScenario DtnScenario_nolive DeliveredByExpiry
par run_tlc dtn_sc_cycle DtnScenario DtnScenario_cycle
par run_tlc dtn_sc_replay DtnScenario DtnScenario_replay
par witness_tlc dtn_sc_forget DtnScenario DtnScenario_forget NoForget
par run_tlc hubcodec_hello HubCodec HubCodec_hello
par run_tlc hubcodec_fixed HubCodec HubCodec_fixed
par run_tlc hubcodec_snap HubCodec HubCodec_snap
par run_tlc hubcodec_snapn HubCodec HubCodec_snapn
par run_tlc hubcodec_down HubCodec HubCodec_down
par run_tlc hubcodec_other HubCodec HubCodec_other
par witness_tlc hubcodec_snapcut HubCodec HubCodec_snapcut SnapCutRefused
par run_tlc sys_steady MembershipSys MembershipSys_steady
par run_tlc sys_complete MembershipSys MembershipSys_complete
par run_tlc sys_complete33 MembershipSys MembershipSys_complete33
par run_tlc sys_lease MembershipSys MembershipSys_lease
par run_tlc sys_lostprobe MembershipSys MembershipSys_lostprobe
par run_tlc sys_slow MembershipSys MembershipSys_slow
par run_tlc sys_partition MembershipSys MembershipSys_partition
par run_tlc sys_return MembershipSys MembershipSys_return
par run_tlc sys_leave MembershipSys MembershipSys_leave
par run_tlc sys_revoke MembershipSys MembershipSys_revoke
par run_tlc sys_restart MembershipSys MembershipSys_restart
par run_tlc sys_jump MembershipSys MembershipSys_jump
par run_tlc sys_move MembershipSys MembershipSys_move
par run_tlc sys_primary MembershipSys MembershipSys_primary
par run_tlc sys_pulse MembershipSys MembershipSys_pulse
par witness_tlc sys_w_clockback MembershipSys MembershipSys_w_clockback IncOK
par witness_tlc sys_w_confirm MembershipSys MembershipSys_w_confirm NeverConfirmed
par witness_tlc sys_w_down MembershipSys MembershipSys_w_down NeverDown
par witness_tlc sys_w_susp MembershipSys MembershipSys_w_susp NeverSusp
par witness_tlc sys_w_restore MembershipSys MembershipSys_w_restore NeverRestore
par witness_tlc sys_w_left MembershipSys MembershipSys_w_left NeverLeft
par witness_tlc sys_w_revoked MembershipSys MembershipSys_w_revoked NeverRevoked
par witness_tlc sys_w_restart MembershipSys MembershipSys_w_restart NeverRestarted
par witness_tlc sys_w_suppressed MembershipSys MembershipSys_w_suppressed NeverSuppressed
par witness_tlc sys_w_switch MembershipSys MembershipSys_w_switch NeverSwitched
par run_tlc sys_live_complete MembershipSys MembershipSys_live_complete
par run_tlc sys_live_lease MembershipSys MembershipSys_live_lease
par run_tlc sys_live_return MembershipSys MembershipSys_live_return
par run_tlc sys_live_leave MembershipSys MembershipSys_live_leave
par run_tlc sys_live_heal MembershipSys MembershipSys_live_heal
par witness_tlc sys_w_finished MembershipSys MembershipSys_w_finished NeverFinished
par run_tlc incarnation Incarnation Incarnation
par run_tlc incarnation_pers Incarnation Incarnation_pers
par run_tlc incarnation_hlc Incarnation Incarnation_hlc
par witness_tlc incarnation_clock Incarnation Incarnation_clock MonoAll
par run_tlc streams Streams Streams
par run_tlc streams_ext Streams Streams_ext
par run_tlc streams_caps Streams Streams_caps
par run_tlc streams_ledger Streams Streams_ledger
par witness_tlc streams_stall Streams Streams_stall NoStuckGrant
par run_tlc streams_live Streams Streams_live
par witness_live_tlc streams_live_stall Streams Streams_live_stall
par witness_live_tlc streams_live_stall Streams Streams_live_stall
par run_tlc recovery Recovery Recovery
par run_tlc recovery_count Recovery Recovery_count
par run_tlc recovery_flags Recovery Recovery_flags
par run_tlc recovery_tail Recovery Recovery_tail
while [ -n "$(jobs -rp)" ]; do wait -n || exit 1; done

echo "-- trace"
dir=$(mktemp -d)
trap 'rm -rf "$dir" "$jtmp_root"' EXIT
VINC_TRACE_DIR="$dir" cargo test -q -p vinc-tests --test trace_ranges --test trace_verifier --test trace_builder --test trace_tla --test trace_handshake --test trace_security --test trace_keyroll --test trace_keylayer --test trace_stores --test trace_values_sched --test trace_values_sys --test trace_values_verify --test trace_values_wire --test trace_values_time --test trace_values_plan --test trace_connect_mailbox --test trace_connect_table --test trace_connect --test trace_transcript --test trace_dtn_store --test trace_dtn_custody --test trace_dtn_forward --test trace_dtn_rs --test trace_dtn_layout --test trace_dtn_codec --test trace_dtn_reception --test trace_dtn_seal --test trace_dtn_scenario --test trace_membership --test trace_streams --test trace_recovery
trace_tlc() { # trace_tlc <spec> <what> : TLC of the newer era over the recorded ndjson in $dir
    local out
    # -Xss: TLC's evaluator recurses deeply on the larger builder tables, which overflows the default thread stack.
    out=$(JAVA_TOOL_OPTIONS="$(jopts)" VINC_TRACE_DIR="$dir" java -Xss256m -XX:+UseParallelGC -cp "$TRACE_TLC:$COMMUNITY" tlc2.TLC -workers auto \
        -metadir "proofs/tla/states/$1" -config "proofs/tla/$1.cfg" "proofs/tla/$1.tla" 2>&1) \
        || { echo "$out" >&2; echo "proofs: the recorded $2 trace is not a behaviour of its TLA+ model" >&2; exit 1; }
    echo "tlc $1: $(echo "$out" | grep -E 'states generated, ' | tail -1)"
}
trace_tlc TraceVerifiedRanges ranges
trace_tlc TraceVarint varint
trace_tlc TraceLayout layout
trace_tlc TraceEncoder encoder
trace_tlc TraceRangeVerifier verifier
trace_tlc TraceBuilder builder
trace_tlc TraceHandshake handshake
trace_tlc TraceSecurity security
trace_tlc TraceKeyRoll keyroll
trace_tlc TraceKeyLayer "key layer"
trace_tlc TraceStores stores
trace_tlc TraceValuesPlan values_plan
trace_tlc TraceValuesSched values_sched
trace_tlc TraceValuesSys values_sys
trace_tlc TraceValuesTime values_time
trace_tlc TraceValuesVerify valuesverify
trace_tlc TraceValuesWire valueswire
trace_tlc TraceConnectMailbox mailbox
trace_tlc TraceConnectTable table
trace_tlc TraceConnect relay
trace_tlc TraceTranscript transcript
trace_tlc TraceDtnStore dtn-store
trace_tlc TraceDtnCustody dtn-custody
trace_tlc TraceDtnForward dtn-forward
trace_tlc TraceDtnRs dtn-rs
trace_tlc TraceDtnLayout dtn-layout
trace_tlc TraceDtnCodec dtn-codec
trace_tlc TraceDtnReception dtn-reception
trace_tlc TraceDtnSeal dtn-seal
trace_tlc TraceDtnScenario dtn-scenario
trace_tlc TraceHubCodec hubcodec
trace_tlc TraceIncarnation incarnation
trace_tlc TraceMembership membership
trace_tlc TraceStreams "stream table"
trace_tlc TraceRecovery "loss recovery"
proofs/lean/.lake/build/bin/replay "$dir"/*.ndjson
echo "proofs: ok"
