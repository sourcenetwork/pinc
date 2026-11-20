# The model checks of the endpoint core added with the trace tests of the PR line, sourced by scripts/proofs.sh after
# tlc.sh (which holds the models before them): one line per TLC config under proofs/tla.
par run_tlc dgram_queue_send DgramQueue DgramQueue_send
par run_tlc dgram_queue_recv DgramQueue DgramQueue_recv
par witness_tlc dgram_queue_drop DgramQueue DgramQueue_drop NoDrop
par run_tlc dgram_queue_sendcount DgramQueue DgramQueue_sendcount
par run_tlc dgram_queue_recvcount DgramQueue DgramQueue_recvcount
par run_tlc evqueue EvQueue EvQueue
par run_tlc evqueue_fits EvQueue EvQueue_fits
par run_tlc evqueue_over EvQueue EvQueue_over
par run_tlc iface Iface Iface
par witness_tlc iface_w_doubt Iface Iface_w_doubt NeverDoubt
par witness_tlc iface_w_moved Iface Iface_w_moved NeverMoved
par witness_tlc mbt_endpoint_w MbtEndpoint MbtEndpoint_w NoTwoHolders
par witness_tlc mbt_endpoint_life_w MbtEndpoint MbtEndpoint_life_w NoMaxSession
par witness_tlc mbt_endpoint_stall_w MbtEndpoint MbtEndpoint_stall_w NoOverdueStalled
par run_tlc settle Settle Settle
par run_tlc settle_watch Settle Settle_watch
par run_tlc settle_held Settle Settle_held
par run_tlc tx Tx Tx
par witness_tlc tx_w_stash Tx Tx_w_stash NoStash
par witness_tlc tx_w_full Tx Tx_w_full NotFull
