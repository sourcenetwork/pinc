# The model-based tests of the proofs step, sourced by scripts/proofs.sh (which defines mbt_cases and $dir): the
# paths of each model's state graph, then the tests that drive the code along them.
mbt_cases MbtOrphan MbtOrphan orphan.ndjson
mbt_cases MbtOrphan MbtOrphan_edge orphan_edge.ndjson
mbt_cases MbtHalfOpen MbtHalfOpen halfopen.ndjson
mbt_cases MbtHalfOpen MbtHalfOpen_back halfopen_back.ndjson
mbt_cases MbtEndpoint MbtEndpoint endpoint.ndjson
mbt_cases MbtEndpoint MbtEndpoint_life endpoint_life.ndjson
mbt_cases MbtEndpoint MbtEndpoint_stall endpoint_stall.ndjson
mbt_cases MbtRanges MbtRanges ranges.ndjson
mbt_cases MbtRanges MbtRanges_wide ranges_wide.ndjson
mbt_cases MbtReasm MbtReasm reasm.ndjson
mbt_cases MbtNodeSets MbtNodeSets node_sets.ndjson
mbt_cases MbtPortMapFallback MbtPortMapFallback portmap_fallback.ndjson
mbt_cases MbtOutbox MbtOutbox outbox.ndjson
mbt_cases MbtSoftPrekeys MbtSoftPrekeys softprekeys.ndjson
mbt_cases MbtSoftPrekeys MbtSoftPrekeys_zero softprekeys_zero.ndjson
mbt_cases MbtFacadeOpen MbtFacadeOpen facade_open.ndjson
mbt_cases MbtConnectFound MbtConnectFound connect_found.ndjson
PINC_MBT_DIR="$dir/mbt" cargo test -q -p pinc-tests --features hwenc --test mbt_orphan --test mbt_halfopen --test mbt_endpoint \
    --test mbt_ranges --test mbt_reasm --test mbt_node_sets --test mbt_portmap_fallback --test mbt_outbox --test mbt_soft_prekeys \
    --test mbt_facade_open -- --nocapture
