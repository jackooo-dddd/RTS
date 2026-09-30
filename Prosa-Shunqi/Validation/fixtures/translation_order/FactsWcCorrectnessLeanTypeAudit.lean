import Prosa.Analysis.Facts.Transform.WcCorrectness
set_option pp.fieldNotation false

#check @Prosa.Analysis.Facts.Transform.WcCorrectness.is_work_conserving_at
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.swap_candidate_is_in_future
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.fsc_respects_has_arrived
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.swap_jobs_must_arrive_to_execute
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.fsc_jobs_must_be_ready_to_execute
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_service_bound
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_ready_job_also_ready_in_original_schedule
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.max_dl_is_greatest_dl
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.order
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.search_result
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.make_wc_at_case_result_found
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.no_relevant_state_in_range
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.service_of_j_is_less_than_cost
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.t_is_less_than_deadline_of_j
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.equal_service_t_max_dl
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.j_misses_deadline
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.make_wc_at_case_result_none
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_finds_ready_jobs
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_establishes_wc
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_jobs_come_from_arrival_sequence
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_jobs_must_be_ready_to_execute
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_all_deadlines_of_arrivals_met
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.wc_transform_prefix_inclusion
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_service_bound
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_job_meets_deadline
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_jobs_come_from_arrival_sequence
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_jobs_must_be_ready_to_execute
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.wc_jobs_come_from_arrival_sequence
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.wc_jobs_must_be_ready_to_execute
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.wc_all_deadlines_of_arrivals_met
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.wc_is_work_conserving_at
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.wc_is_work_conserving
#check @Prosa.Analysis.Facts.Transform.WcCorrectness.wc_transform_correctness

#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.is_work_conserving_at
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.swap_candidate_is_in_future
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.fsc_respects_has_arrived
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.swap_jobs_must_arrive_to_execute
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.fsc_jobs_must_be_ready_to_execute
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_service_bound
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_ready_job_also_ready_in_original_schedule
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.max_dl_is_greatest_dl
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.order
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.search_result
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.make_wc_at_case_result_found
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.no_relevant_state_in_range
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.service_of_j_is_less_than_cost
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.t_is_less_than_deadline_of_j
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.equal_service_t_max_dl
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.j_misses_deadline
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.make_wc_at_case_result_none
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_finds_ready_jobs
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_establishes_wc
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_jobs_come_from_arrival_sequence
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_jobs_must_be_ready_to_execute
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_all_deadlines_of_arrivals_met
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.wc_transform_prefix_inclusion
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_service_bound
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_job_meets_deadline
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_jobs_come_from_arrival_sequence
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_jobs_must_be_ready_to_execute
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.wc_jobs_come_from_arrival_sequence
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.wc_jobs_must_be_ready_to_execute
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.wc_all_deadlines_of_arrivals_met
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.wc_is_work_conserving_at
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.wc_is_work_conserving
#print axioms Prosa.Analysis.Facts.Transform.WcCorrectness.wc_transform_correctness
