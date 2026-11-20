# The trace step of the proofs step, sourced by scripts/proofs.sh (which defines par, trace_tlc and $dir): the tests
# that record the ndjson traces, then one trace check per trace spec under proofs/tla.
PINC_TRACE_DIR="$dir" cargo test -q -p pinc-tests --features hwenc --test trace_ranges --test trace_verifier --test trace_builder --test trace_tla --test trace_handshake --test trace_security --test trace_keyroll --test trace_keylayer --test trace_stores --test trace_values_sched --test trace_values_sys --test trace_values_verify --test trace_values_wire --test trace_values_time --test trace_values_plan --test trace_connect_mailbox --test trace_connect_pack --test trace_connect_table --test trace_connect --test trace_connect_records --test trace_connect_own --test trace_transcript --test trace_dtn_store --test trace_dtn_custody --test trace_dtn_forward --test trace_dtn_rs --test trace_dtn_layout --test trace_dtn_codec --test trace_dtn_reception --test trace_dtn_seal --test trace_dtn_scenario --test trace_membership --test trace_streams --test trace_recovery --test trace_broadcast --test trace_reconcile_wire --test trace_reconcile --test trace_crypto --test trace_keystore --test trace_keystore_tpm --test trace_connect_codec --test trace_connect_link --test trace_connect_client --test trace_rx --test trace_cid --test trace_cc --test trace_pn --test trace_reasm --test trace_early --test trace_hdr --test trace_frame --test trace_framepack --test trace_ext --test trace_orphan --test trace_keepalive --test trace_node_backoff --test trace_rtt --test trace_standby --test trace_halfopen --test trace_core_table --test trace_heap --test trace_core_state --test trace_queue --test trace_held --test trace_ext_in --test trace_reach --test trace_mtu --test trace_reply_path --test trace_timers --test trace_connect_carrier --test trace_connect_ws --test trace_integration_codecs
par trace_tlc TraceVerifiedRanges ranges
par trace_tlc TraceVarint varint
par trace_tlc TraceLayout layout
par trace_tlc TraceEncoder encoder
par trace_tlc TraceRangeVerifier verifier
par trace_tlc TraceBuilder builder
par trace_tlc TraceHandshake handshake
par trace_tlc TraceSecurity security
par trace_tlc TraceKeyRoll keyroll
par trace_tlc TraceKeyLayer "key layer"
par trace_tlc TraceStores stores
par trace_tlc TraceValuesPlan values_plan
par trace_tlc TraceValuesSched values_sched
par trace_tlc TraceValuesSys values_sys
par trace_tlc TraceValuesTime values_time
par trace_tlc TraceValuesVerify valuesverify
par trace_tlc TraceValuesWire valueswire
par trace_tlc TraceConnectMailbox mailbox
par trace_tlc TraceConnectPack connect-pack
par trace_tlc TraceConnectTable table
par trace_tlc TraceConnect relay
par trace_tlc TraceConnectRecords connect-records
par trace_tlc TraceConnectOwn connect-own
par trace_tlc TraceConnectCodec connect-codec
par trace_tlc TraceConnectLink connect-link
par trace_tlc TraceConnectClient connect-client
par trace_tlc TraceConnectCarrier connect-carrier
par trace_tlc TraceConnectWs connect-ws
par trace_tlc TraceTranscript transcript
par trace_tlc TraceDtnStore dtn-store
par trace_tlc TraceDtnCustody dtn-custody
par trace_tlc TraceDtnForward dtn-forward
par trace_tlc TraceDtnRs dtn-rs
par trace_tlc TraceDtnLayout dtn-layout
par trace_tlc TraceDtnCodec dtn-codec
par trace_tlc TraceDtnReception dtn-reception
par trace_tlc TraceDtnSeal dtn-seal
par trace_tlc TraceDtnScenario dtn-scenario
par trace_tlc TraceHubCodec hubcodec
par trace_tlc TraceIncarnation incarnation
par trace_tlc TraceMembership membership
par trace_tlc TraceStreams "stream table"
par trace_tlc TraceRecovery "loss recovery"
par trace_tlc TraceRx "received packets"
par trace_tlc TraceCid "connection ids"
par trace_tlc TraceCc "congestion control"
par trace_tlc TracePn "packet numbers"
par trace_tlc TraceReasm "handshake fragments"
par trace_tlc TraceEarly "early packets"
par trace_tlc TraceHdr "packet headers"
par trace_tlc TraceFrame "frame codecs"
par trace_tlc TraceFramePack "packet builder"
par trace_tlc TraceExt "extension frames"
par trace_tlc TraceOrphan "held fragments"
par trace_tlc TraceKeepalive "keepalive schedule"
par trace_tlc TraceNodeBackoff "failed dials"
par trace_tlc TraceRtt "node round trips"
par trace_tlc TraceFacadeStandby "standby slab"
par trace_tlc TraceHalfOpen "half-open cap"
par trace_tlc TraceCoreTable "connection-id table"
par trace_tlc TraceHeap "deadline heap"
par trace_tlc TraceCoreState "saved state"
par trace_tlc TraceQueue "event queue"
par trace_tlc TraceHeld "held ring"
par trace_tlc TraceExtIn "extension ring"
par trace_tlc TraceReach "reach ring"
par trace_tlc TraceMtu "path MTU"
par trace_tlc TraceReplyPath "reply path"
par trace_tlc TraceTimers "timers and closing"
par trace_tlc TraceIntegrationCodecs "integration codecs"
par trace_tlc TraceBroadcast broadcast
par trace_tlc TraceReconcileWire reconcile-wire
par trace_tlc TraceReconcile reconcile
par trace_tlc TraceCrypto crypto
par trace_tlc TraceKeystore keystore
