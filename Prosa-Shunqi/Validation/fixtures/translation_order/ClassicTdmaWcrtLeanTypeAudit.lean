import Validation.fixtures.translation_order.ClassicTdmaWcrtInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.formula_rt
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.job_response_time_tdma_in_at_most_one_job_is_pending
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.at_most_one_job_is_pending
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.TDMA_policy_case_RT_le_Period
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.pendingArrival
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.pendingSt
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.pendingSt_Sched
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.to_next_slot_pos
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.lt_to_next_slot_1LR
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.lt_to_next_slot_LR
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.S_t_not_sched
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.duration_not_sched
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.pending_Nsched_sched
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.at_next_start_of_slot_schedulabe
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.formula_not_sched_St
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.formula_sched_St
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.formula_not_sched_interval
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.formula_not_sched_to_next_slot
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.job_not_sched_to_cunsume_1unit
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.end_time_predicate_not_sched_eq
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.end_time_predicate_not_sched_eq_rev
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.end_time_predicate_eq
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.service_is_zero_in_Nsched_duration
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.completes_at_end_time_pre
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.completes_at_end_time
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.WCRT_formula
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.WCRT
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.response_time_le_WCRT
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.exists_WCRT
#check @Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.job_completed_by_WCRT
#check @Prosa.Validation.ClassicTdmaWcrtInterface.production_sumSeq_nil
#check @Prosa.Validation.ClassicTdmaWcrtInterface.production_sumSeq_cons
#check @Prosa.Validation.ClassicTdmaWcrtInterface.production_sumFiltered_nil
#check @Prosa.Validation.ClassicTdmaWcrtInterface.production_sumFiltered_cons_true
#check @Prosa.Validation.ClassicTdmaWcrtInterface.production_sumFiltered_cons_false
#check @Prosa.Validation.ClassicTdmaWcrtInterface.end_time_option_c0
#check @Prosa.Validation.ClassicTdmaWcrtInterface.end_time_option_wf0
#check @Prosa.Validation.ClassicTdmaWcrtInterface.end_time_option_step
#check @Prosa.Validation.DivModInterface.production_div_floor_eq
#check @Prosa.Validation.DivModInterface.production_div_ceil_eq
#check @Prosa.Validation.DivModInterface.production_div_add_mod
#check @Prosa.Validation.DivModInterface.production_mod_lt
#check @Prosa.Validation.DivModInterface.production_div_zero
#check @Prosa.Validation.DivModInterface.production_mod_zero
#check @Prosa.Validation.DivModInterface.production_dvd_iff_mod_eq_zero

#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.formula_rt
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.job_response_time_tdma_in_at_most_one_job_is_pending
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.at_most_one_job_is_pending
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.TDMA_policy_case_RT_le_Period
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.pendingArrival
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.pendingSt
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.pendingSt_Sched
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.to_next_slot_pos
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.lt_to_next_slot_1LR
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.lt_to_next_slot_LR
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.S_t_not_sched
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.duration_not_sched
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.pending_Nsched_sched
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.at_next_start_of_slot_schedulabe
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.formula_not_sched_St
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.formula_sched_St
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.formula_not_sched_interval
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.formula_not_sched_to_next_slot
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.job_not_sched_to_cunsume_1unit
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.end_time_predicate_not_sched_eq
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.end_time_predicate_not_sched_eq_rev
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.end_time_predicate_eq
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.service_is_zero_in_Nsched_duration
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.completes_at_end_time_pre
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.completes_at_end_time
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.WCRT_formula
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.WCRT
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.response_time_le_WCRT
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.exists_WCRT
#print axioms Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.job_completed_by_WCRT
#print axioms Prosa.Validation.ClassicTdmaWcrtInterface.production_sumSeq_nil
#print axioms Prosa.Validation.ClassicTdmaWcrtInterface.production_sumSeq_cons
#print axioms Prosa.Validation.ClassicTdmaWcrtInterface.production_sumFiltered_nil
#print axioms Prosa.Validation.ClassicTdmaWcrtInterface.production_sumFiltered_cons_true
#print axioms Prosa.Validation.ClassicTdmaWcrtInterface.production_sumFiltered_cons_false
#print axioms Prosa.Validation.ClassicTdmaWcrtInterface.end_time_option_c0
#print axioms Prosa.Validation.ClassicTdmaWcrtInterface.end_time_option_wf0
#print axioms Prosa.Validation.ClassicTdmaWcrtInterface.end_time_option_step
#print axioms Prosa.Validation.DivModInterface.production_div_floor_eq
#print axioms Prosa.Validation.DivModInterface.production_div_ceil_eq
#print axioms Prosa.Validation.DivModInterface.production_div_add_mod
#print axioms Prosa.Validation.DivModInterface.production_mod_lt
#print axioms Prosa.Validation.DivModInterface.production_div_zero
#print axioms Prosa.Validation.DivModInterface.production_mod_zero
#print axioms Prosa.Validation.DivModInterface.production_dvd_iff_mod_eq_zero
