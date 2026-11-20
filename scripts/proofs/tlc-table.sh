# The model checks of the fixed tables crate added with the trace tests of the PR line, sourced by scripts/proofs.sh after
# tlc.sh (which holds the models before them): one line per TLC config under proofs/tla.
par run_tlc table_array TableArray TableArray
par witness_tlc table_array_full TableArray TableArray_full NotFull
par run_tlc_deep table_bytes TableBytes TableBytes
par witness_tlc table_bytes_sat TableBytes TableBytes_sat NoSaturation
par run_tlc table_pool TablePool TablePool
par witness_tlc table_pool_exhausted TablePool TablePool_exhausted NotExhausted
par witness_tlc table_pool_wrap TablePool TablePool_wrap NoOldMatch
par run_tlc table_ring TableRing TableRing
par witness_tlc table_ring_wrap TableRing TableRing_wrap NotWrappedFull
par run_tlc table_slab TableSlab TableSlab
par witness_tlc table_slab_full TableSlab TableSlab_full NeverFull
par witness_tlc table_slab_move TableSlab TableSlab_move NoRetainMove
