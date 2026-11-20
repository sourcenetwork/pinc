# The model checks of the wire codecs added with the trace tests of the PR line, sourced by scripts/proofs.sh after
# tlc.sh (which holds the models before them): one line per TLC config under proofs/tla.
par run_tlc_deep wirecbor WireCbor WireCbor
par run_tlc_deep wirecbor_skip WireCbor WireCbor_skip
par witness_tlc wirecbor_w_depth WireCbor WireCbor_w_depth NoDepth
par run_tlc_deep wirecursor WireCursor WireCursor
par witness_tlc wirecursor_w_rshort WireCursor WireCursor_w_rshort NoShortWithBytesLeft
par witness_tlc wirecursor_w_wpartial WireCursor WireCursor_w_wpartial NoPartialRefusal
