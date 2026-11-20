# The model-based tests of the proofs step, sourced by scripts/proofs.sh (which defines mbt_cases and $dir): the
# paths of each model's state graph, then the tests that drive the code along them.
mbt_cases MbtOrphan MbtOrphan orphan.ndjson
mbt_cases MbtOrphan MbtOrphan_edge orphan_edge.ndjson
mbt_cases MbtHalfOpen MbtHalfOpen halfopen.ndjson
mbt_cases MbtHalfOpen MbtHalfOpen_back halfopen_back.ndjson
mbt_cases MbtRanges MbtRanges ranges.ndjson
mbt_cases MbtRanges MbtRanges_wide ranges_wide.ndjson
PINC_MBT_DIR="$dir/mbt" cargo test -q -p pinc-tests --features hwenc --test mbt_orphan --test mbt_halfopen --test mbt_ranges -- --nocapture
mbt_cases MbtReasm MbtReasm reasm.ndjson
PINC_MBT_DIR="$dir/mbt" cargo test -q -p pinc-tests --features hwenc --test mbt_orphan --test mbt_halfopen --test mbt_reasm -- --nocapture
