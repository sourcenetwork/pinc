import Vinc.ValuesTimeTrace

/-! Axiom audit of the main theorems of the time rules of the value fetch (HEAD_HOLD, STALL_REDIAL, the deadline). -/

open Vinc.ValuesTime

-- HEAD_HOLD: the causes, the buffer, the first granule over every run
#audit_axioms Vinc.ValuesTime.holdWhy_isSome_iff
#audit_axioms Vinc.ValuesTime.holdWhy_buffered
#audit_axioms Vinc.ValuesTime.holdWhy_tail
#audit_axioms Vinc.ValuesTime.holdWhy_granules
#audit_axioms Vinc.ValuesTime.holdWhy_timeout
#audit_axioms Vinc.ValuesTime.holdCheck_release
#audit_axioms Vinc.ValuesTime.bufOf_ge_iff
#audit_axioms Vinc.ValuesTime.reach_inv
#audit_axioms Vinc.ValuesTime.never_announced_unstored
#audit_axioms Vinc.ValuesTime.held_not_announced
#audit_axioms Vinc.ValuesTime.announced_once
#audit_axioms Vinc.ValuesTime.complete_announced_once
#audit_axioms Vinc.ValuesTime.later_granule_immediate
#audit_axioms Vinc.ValuesTime.reach_j0
#audit_axioms Vinc.ValuesTime.noLate_checkDone
#audit_axioms Vinc.ValuesTime.hold_poll_le
#audit_axioms Vinc.ValuesTime.onTimeout_clears_head
#audit_axioms Vinc.ValuesTime.onTimeout_timeout_cause
-- STALL_REDIAL
#audit_axioms Vinc.ValuesTime.nextSw_sequence
#audit_axioms Vinc.ValuesTime.arrival_lt_iff
#audit_axioms Vinc.ValuesTime.byteLive_ge
#audit_axioms Vinc.ValuesTime.byteLive_le
#audit_axioms Vinc.ValuesTime.byteLive_run
#audit_axioms Vinc.ValuesTime.stallRtt_le
#audit_axioms Vinc.ValuesTime.stallLive_ne_zero
#audit_axioms Vinc.ValuesTime.redial_iff
#audit_axioms Vinc.ValuesTime.redial_only_after_silence
#audit_axioms Vinc.ValuesTime.sw_decrease_cases
#audit_axioms Vinc.ValuesTime.sw_ge
#audit_axioms Vinc.ValuesTime.sw_le
#audit_axioms Vinc.ValuesTime.sw_range_without_live
#audit_axioms Vinc.ValuesTime.ark_lowers_example
#audit_axioms Vinc.ValuesTime.redial_lowers_example
-- the deadline and the failure reasons
#audit_axioms Vinc.ValuesTime.onTimeout_late_stops
#audit_axioms Vinc.ValuesTime.onTimeout_late_no_work
#audit_axioms Vinc.ValuesTime.onTimeout_late_outcome
#audit_axioms Vinc.ValuesTime.onTimeout_late_one_terminal
#audit_axioms Vinc.ValuesTime.poll_deadline
#audit_axioms Vinc.ValuesTime.late_of_poll
#audit_axioms Vinc.ValuesTime.deadline_max_never
#audit_axioms Vinc.ValuesTime.done_after_deadline
#audit_axioms Vinc.ValuesTime.redial_only_timeout
#audit_axioms Vinc.ValuesTime.fail_reason
#audit_axioms Vinc.ValuesTime.startFetch_badRoot
#audit_axioms Vinc.ValuesTime.startFetch_complete
#audit_axioms Vinc.ValuesTime.startFetch_noProvider
#audit_axioms Vinc.ValuesTime.startFetch_runs

-- the corrections: tail threshold, one announcement per granule, stall armed at the first request
#audit_axioms Vinc.ValuesTime.tail_waits_for_wanted_end
#audit_axioms Vinc.ValuesTime.tail_means_wanted_end
#audit_axioms Vinc.ValuesTime.dupStep_announces_only_the_held
#audit_axioms Vinc.ValuesTime.no_granule_not_stalled
#audit_axioms Vinc.ValuesTime.silent_after_granule_redialled
#audit_axioms Vinc.ValuesTime.poll_offers_stall_from_first_granule
#audit_axioms Vinc.ValuesTime.no_granule_no_timer
