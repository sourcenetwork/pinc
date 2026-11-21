# The trace step of the proofs step, sourced by scripts/proofs.sh (which defines par, trace_tlc and $dir): the tests
# that record the ndjson traces, then one trace check per trace spec under proofs/tla.
PINC_TRACE_DIR="$dir" cargo test -q -p pinc-tests --features hwenc --test trace_ranges --test trace_verifier --test trace_builder --test trace_tla --test trace_handshake --test trace_security --test trace_keyroll --test trace_keylayer --test trace_stores --test trace_values_sched --test trace_values_sys --test trace_values_verify --test trace_values_wire --test trace_values_time --test trace_values_plan --test trace_connect_mailbox --test trace_connect_pack --test trace_connect_table --test trace_connect --test trace_connect_records --test trace_connect_own --test trace_transcript --test trace_dtn_store --test trace_dtn_custody --test trace_dtn_forward --test trace_dtn_rs --test trace_dtn_layout --test trace_dtn_codec --test trace_dtn_reception --test trace_dtn_seal --test trace_dtn_scenario --test trace_membership --test trace_streams --test trace_recovery --test trace_broadcast --test trace_reconcile_wire --test trace_reconcile --test trace_crypto --test trace_keystore --test trace_keystore_tpm --test trace_connect_codec --test trace_connect_link --test trace_connect_client --test trace_rx --test trace_cid --test trace_cc --test trace_pn --test trace_reasm --test trace_early --test trace_hdr --test trace_frame --test trace_framepack --test trace_ext --test trace_orphan --test trace_keepalive --test trace_node_backoff --test trace_rtt --test trace_standby --test trace_halfopen --test trace_core_table --test trace_heap --test trace_core_state --test trace_queue --test trace_held --test trace_ext_in --test trace_reach --test trace_mtu --test trace_reply_path --test trace_timers --test trace_connect_carrier --test trace_connect_ws --test trace_integration_codecs
# The tests above record what the Lean replay reads (proofs/lean/Replay.lean); every trace recorded below is read by a
# TLA+ trace spec only.
lean_traces=("$dir"/*.ndjson)
# the tests of the PR line's models
PINC_TRACE_DIR="$dir" cargo test -q -p pinc-tests --features hwenc \
    --test trace_broadcast_adj_record --test trace_broadcast_auth2 --test trace_broadcast_push \
    --test trace_broadcast_reach --test trace_broadcast_repair --test trace_broadcast_statement \
    --test trace_broadcast_subs --test trace_broadcast_wire2 --test trace_connect_carriers --test trace_connect_drive \
    --test trace_connect_duty --test trace_connect_flight --test trace_connect_mapped --test trace_connect_node \
    --test trace_connect_own_timer \
    --test trace_connect_queue --test trace_connect_sleep --test trace_core_backlog --test trace_core_route_index \
    --test trace_ctl --test trace_dag_block --test trace_dag_car --test trace_dag_cid --test trace_dag_sizes \
    --test trace_dgram_queue --test trace_dgram_size --test trace_dtn_request --test trace_dtn_want \
    --test trace_dial_report \
    --test trace_evqueue --test trace_facade_gate --test trace_facade_records --test trace_facade_relay_carriers \
    --test trace_facade_relay_keep --test trace_facade_role_clock --test trace_facade_stream \
    --test trace_facade_turn \
    --test trace_facade_waits --test trace_finish_resend --test trace_frame_refs --test trace_iface \
    --test trace_keystore_refresh --test trace_keystore_template --test trace_lazy --test trace_ledger \
    --test trace_loss_estimate \
    --test trace_machines --test trace_message --test trace_node_dtn_backoff --test trace_node_dtn_codec \
    --test trace_node_due \
    --test trace_node_event_queue --test trace_node_portmap --test trace_node_silence --test trace_node_timer_bound \
    --test trace_node_values --test trace_node_values_net --test trace_packet_kind --test trace_path_held \
    --test trace_path_move --test trace_platform_time --test trace_portmap_addr --test trace_portmap_codec \
    --test trace_portmap_lease --test trace_portmap_text --test trace_portmap_upnp --test trace_recovery_math \
    --test trace_responder_limit --test trace_sec_ids --test trace_settle --test trace_stream_send \
    --test trace_table_array --test trace_table_bytes --test trace_table_pool --test trace_table_ring \
    --test trace_table_slab --test trace_tx --test trace_wire_cbor --test trace_wire_cursor
# the unit trace tests of the facade crate: every `trace_` test in the build without std, then the ones with std
PINC_TRACE_DIR="$dir" cargo test -q -p pinc --no-default-features --lib trace_
PINC_TRACE_DIR="$dir" cargo test -q -p pinc --lib trace_reserved
PINC_TRACE_DIR="$dir" cargo test -q -p pinc --lib trace_addr
PINC_TRACE_DIR="$dir" cargo test -q -p pinc --lib trace_state
PINC_TRACE_DIR="$dir" cargo test -q -p pinc --lib trace_events
PINC_TRACE_DIR="$dir" cargo test -q -p pinc --lib trace_facade_bufs
PINC_TRACE_DIR="$dir" cargo test -q -p pinc --lib trace_facade_machines
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
par trace_tlc TraceBroadcastAdjRecord "adjacency records"
par trace_tlc TraceBroadcastAuth2 "broadcast signatures version 2"
par trace_tlc TraceBroadcastPush "hub push under backpressure"
par trace_tlc TraceBroadcastReach "connected component"
par trace_tlc TraceBroadcastRepair "gap repair"
par trace_tlc TraceBroadcastStatement "broadcast statement"
par trace_tlc TraceBroadcastSubs "subscriptions on return"
par trace_tlc TraceBroadcastWire2 "broadcast head version 2"
par trace_tlc TraceConnectCarriers connect-carriers
par trace_tlc TraceConnectDrive connect-drive
par trace_tlc TraceConnectDuty connect-duty
par trace_tlc TraceConnectFlight connect-flight
par trace_tlc TraceConnectHeldQueue connect-queue
par trace_tlc TraceConnectMapped connect-mapped
par trace_tlc TraceConnectNodeId connect-node
par trace_tlc TraceConnectSleep connect-sleep
par trace_tlc TraceDgramQueue "datagram queues"
par trace_tlc TraceEvQueue "event queue"
par trace_tlc TraceIface "interface and suspension"
par trace_tlc TraceSettle "keepalive plan applied"
par trace_tlc TraceTx "datagrams out"
par trace_tlc TraceDagBlock "pinc-dag block"
par trace_tlc TraceDagCar "pinc-dag CAR"
par trace_tlc TraceDagCborLen "pinc-dag encoded sizes"
par trace_tlc TraceDagCid "pinc-dag CID"
par trace_tlc TraceNodePortMap "port-mapping client"
par trace_tlc TraceNodeValues "values layer over sessions"
par trace_tlc TraceNodeValuesNet "node values tables"
par trace_tlc TracePortMapAddr portmap-addr
par trace_tlc TracePortMapCodec portmap-codec
par trace_tlc TracePortMapLease portmap-lease
par trace_tlc TracePortMapText portmap-text
par trace_tlc TracePortMapUpnp portmap-upnp
par trace_tlc TraceSecIds secids
par trace_tlc TraceTableArray "table array"
par trace_tlc TraceTableBytes "table block sizes"
par trace_tlc TraceTablePool "table pool"
par trace_tlc TraceTableRing "table ring"
par trace_tlc TraceTableSlab "table slab"
par trace_tlc TraceCtlTable "control frames"
par trace_tlc TraceFrameRefs "frame descriptors"
par trace_tlc TraceLazy "lazy table"
par trace_tlc TraceLedger "amplification ledger"
par trace_tlc TraceLossEstimate "loss estimate"
par trace_tlc TraceMachines "handshake machine pool"
par trace_tlc TraceMessageCodec message
par trace_tlc TracePacketKind "packet kinds"
par trace_tlc TracePathHeld "held path flag"
par trace_tlc TracePathMove "path validation and migration"
par trace_tlc TraceRecoveryMath "recovery math"
par trace_tlc TraceStreamSend "stream send half"
par trace_tlc TraceWireCbor "dag-cbor codec"
par trace_tlc TraceWireCursor "wire cursors"
par trace_tlc TraceNodeSilence "silence bound"
par trace_tlc TraceNodeTimerBound "timer bound"
par trace_tlc TraceNodeEventQueue "event queue"
par trace_tlc TraceNodeDtnBackoff "delay-tolerant dial backoff"
par trace_tlc TraceNodeDtnCodec "delay-tolerant records and frames"
par trace_tlc TraceKeystoreTemplate "keystore templates"
par trace_tlc TraceDgramSize "datagram sizes"
par trace_tlc TraceFinishResend "Finish resends"
par trace_tlc TraceResponderLimit "responder hold"
par trace_tlc TraceCoreRouteIndex "sessions by address"
par trace_tlc TraceCoreBacklog "accept room"
par trace_tlc TraceDtnWant "the DTN request rule"
par trace_tlc TraceDtnRequest "DTN transfers"
par trace_tlc TraceFacadeWaits "session waiters"
par trace_tlc TraceFacadeStream "stream and datagram handles"
par trace_tlc TraceFacadeStreamDoc "stream handles as documented"
par trace_tlc TraceFacadeRoleClock "relay role clock"
par trace_tlc TraceFacadeRelayKeep "relay keep"
par trace_tlc TraceFacadeRelayCarriers "relay carriers"
par trace_tlc TracePlatformTime "platform time"
par trace_tlc TraceFacadePrekeys "facade prekeys"
par trace_tlc TraceFacadeRecords "record discovery"
par trace_tlc TraceFacadeReserved "reserved signing prefixes"
par trace_tlc TraceFacadeAddr "node id text and ticket"
par trace_tlc TraceFacadeState "saved state framing"
par trace_tlc TraceFacadeBufs "facade buffer pools"
par trace_tlc TraceFacadeMachines "facade machine pool rule"
par trace_tlc TraceFacadeEvents "facade topic event queue"
par trace_tlc TraceFacadeRevoke "facade revoke"
par trace_tlc TraceFacadeRevokeFull "facade revoke with the revoked set full"
par trace_tlc TraceFacadeAcpForget "facade access answers per peer"
par trace_tlc TraceDialReport "dial report"
par trace_tlc TraceFacadeTurn "facade drive turn"
par trace_tlc TraceConnectOwnTimer "record publish timer"
par trace_tlc TraceNodeDue "node deadline cache"
par trace_tlc TraceKeystoreRefresh "keystore refresh"
par trace_tlc TraceLimitsFit "limit sets that fit"
