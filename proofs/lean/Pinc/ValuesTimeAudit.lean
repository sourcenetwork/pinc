import Pinc.ValuesTimeTrace

/-! Axiom audit of the main theorems of the time rules of the value fetch (HEAD_HOLD, STALL_REDIAL, the deadline). -/

open Pinc.ValuesTime

-- HEAD_HOLD: the causes, the buffer, the first granule over every run
#audit_axioms Pinc.ValuesTime.holdWhy_isSome_iff
#audit_axioms Pinc.ValuesTime.holdWhy_buffered
#audit_axioms Pinc.ValuesTime.holdWhy_tail
#audit_axioms Pinc.ValuesTime.holdWhy_granules
#audit_axioms Pinc.ValuesTime.holdWhy_timeout
#audit_axioms Pinc.ValuesTime.holdCheck_release
#audit_axioms Pinc.ValuesTime.bufOf_ge_iff
#audit_axioms Pinc.ValuesTime.reach_inv
#audit_axioms Pinc.ValuesTime.never_announced_unstored
#audit_axioms Pinc.ValuesTime.held_not_announced
#audit_axioms Pinc.ValuesTime.announced_once
#audit_axioms Pinc.ValuesTime.complete_announced_once
#audit_axioms Pinc.ValuesTime.later_granule_immediate
#audit_axioms Pinc.ValuesTime.reach_j0
#audit_axioms Pinc.ValuesTime.noLate_checkDone
#audit_axioms Pinc.ValuesTime.hold_poll_le
#audit_axioms Pinc.ValuesTime.onTimeout_clears_head
#audit_axioms Pinc.ValuesTime.onTimeout_timeout_cause
-- STALL_REDIAL
#audit_axioms Pinc.ValuesTime.nextSw_sequence
#audit_axioms Pinc.ValuesTime.arrival_lt_iff
#audit_axioms Pinc.ValuesTime.byteLive_ge
#audit_axioms Pinc.ValuesTime.byteLive_le
#audit_axioms Pinc.ValuesTime.byteLive_run
#audit_axioms Pinc.ValuesTime.stallRtt_le
#audit_axioms Pinc.ValuesTime.stallLive_ne_zero
#audit_axioms Pinc.ValuesTime.redial_iff
#audit_axioms Pinc.ValuesTime.redial_only_after_silence
#audit_axioms Pinc.ValuesTime.sw_decrease_cases
#audit_axioms Pinc.ValuesTime.sw_ge
#audit_axioms Pinc.ValuesTime.sw_le
#audit_axioms Pinc.ValuesTime.sw_range_without_live
#audit_axioms Pinc.ValuesTime.ark_lowers_example
#audit_axioms Pinc.ValuesTime.redial_lowers_example
-- the deadline and the failure reasons
#audit_axioms Pinc.ValuesTime.onTimeout_late_stops
#audit_axioms Pinc.ValuesTime.onTimeout_late_no_work
#audit_axioms Pinc.ValuesTime.onTimeout_late_outcome
#audit_axioms Pinc.ValuesTime.onTimeout_late_one_terminal
#audit_axioms Pinc.ValuesTime.poll_deadline
#audit_axioms Pinc.ValuesTime.late_of_poll
#audit_axioms Pinc.ValuesTime.deadline_max_never
#audit_axioms Pinc.ValuesTime.done_after_deadline
#audit_axioms Pinc.ValuesTime.redial_only_timeout
#audit_axioms Pinc.ValuesTime.fail_reason
#audit_axioms Pinc.ValuesTime.startFetch_badRoot
#audit_axioms Pinc.ValuesTime.startFetch_complete
#audit_axioms Pinc.ValuesTime.startFetch_noProvider
#audit_axioms Pinc.ValuesTime.startFetch_runs

-- the corrections: tail threshold, one announcement per granule, stall armed at the first request
#audit_axioms Pinc.ValuesTime.tail_waits_for_wanted_end
#audit_axioms Pinc.ValuesTime.tail_means_wanted_end
#audit_axioms Pinc.ValuesTime.dupStep_announces_only_the_held
#audit_axioms Pinc.ValuesTime.no_granule_not_stalled
#audit_axioms Pinc.ValuesTime.silent_after_granule_redialled
#audit_axioms Pinc.ValuesTime.poll_offers_stall_from_first_granule
#audit_axioms Pinc.ValuesTime.no_granule_no_timer
