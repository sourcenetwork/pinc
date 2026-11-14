# Regression tests for the defects the proofs work found

Each file reproduces a filed issue and fails on `master` at the time it was filed. Copy a file into `tests/` with a
`[[test]]` entry in `tests/Cargo.toml` (or apply the `.patch`/`.diff` with `git apply`) to land it with the fix. This
branch is a carrier for the files; it is not meant to be merged.

| Issue | File | Tests |
|---|---|---|
| #251 | `ledger_probe.diff` (against `tests/core_defense.rs`) | `zz_probe_*` |
| #254 | `integration_risks.rs` | `c2_one_dials_failure_ends_another_dial_to_the_same_peer`, `c2_control_the_relay_path_alone_connects` |
| #255 | `integration_risks.rs` | `c3_the_node_queue_drops_an_unrecoverable_event_the_core_kept` |
| #256 | `integration_risks.rs` | `c1_a_stopped_hub_stream_reaches_the_application`, `c1b_after_the_stop_a_members_publish_is_lost` |
| #257 | `integration_risks.rs` | `c8_a_sub_open_refused_for_a_full_table_is_ignored_when_repeated`, `c8_control_a_repeat_is_accepted_when_the_first_refusal_marked_nothing` |
| #258 | `integration_risks.rs` | `c4_a_dial_refused_for_a_full_table_spends_the_ticket` |
| #270 | `core_acp_gate.rs` | both tests |
| #305 | `layers_dtn_restore_skip.rs` | the reproduction, plus a corrupt PARTIAL that must evict nothing and a HELD record with a bad custody byte or a trailing byte |
| #310 | `addr_roundtrip.rs` | the four tests |
| #311 | `vinc_standby_order.rs` | the order test and its control |
| #312 | `core_send_queue.rs` (public API only); `trace_sendq.rs` with `trace_sendq_accessors.diff` (the original, with `trace` accessors) | |
| #333 | `streams_send_ring_wrap.rs` | `overflow_route_ring_of_2`, `overflow_route_ring_of_1025`, `repair_route_ring_of_2` |
| #335 | `core_demux_leak.patch` (the test and three `trace`-feature accessors; `trace_session` exposes key material) | `an_id_a_connection_holds_twice_outlives_its_session` |
| #340 | `broadcast_restart_probes.patch` (five tests for `tests/broadcast_floors.rs`) | the two delivery probes fail; the control and the two trade-off probes pass |
| #343 | `membership_stale_view.patch` | the failing run and two controls |
| #344 | in PR #350 | |

`integration_risks.rs` holds all the tests for #254 to #258 with their shared helpers; take the ones an issue names.
