# The model checks of the DAG crate added with the trace tests of the PR line, sourced by scripts/proofs.sh after
# tlc.sh (which holds the models before them): one line per TLC config under proofs/tla.
par run_tlc_deep dag_block DagBlock DagBlock
par witness_tlc dag_block_loose DagBlock DagBlock_loose LooseRoundTrip
par run_tlc_deep dag_car DagCar DagCar
par witness_tlc dag_car_cut DagCar DagCar_cut CutRefused
par run_tlc dag_cbor_len DagCborLen DagCborLen
par run_tlc_deep dag_cid DagCid DagCid
par witness_tlc dag_cid_order DagCid DagCid_order ByteOrderIsTextOrder
