import Prosa.Analysis.Facts.Transform.EdfOpt
set_option pp.fieldNotation false

#check @Prosa.Analysis.Facts.Transform.EdfOpt.t1_relevant
#check @Prosa.Analysis.Facts.Transform.EdfOpt.fsc_search_successful
#check @Prosa.Analysis.Facts.Transform.EdfOpt.fsc_search_result
#check @Prosa.Analysis.Facts.Transform.EdfOpt.fsc_not_idle
#check @Prosa.Analysis.Facts.Transform.EdfOpt.fsc_found_job_arrival
#check @Prosa.Analysis.Facts.Transform.EdfOpt.fsc_range
#check @Prosa.Analysis.Facts.Transform.EdfOpt.fsc_range1
#check @Prosa.Analysis.Facts.Transform.EdfOpt.fsc_found_job_deadline
#check @Prosa.Analysis.Facts.Transform.EdfOpt.fsc_no_later_deadline
#check @Prosa.Analysis.Facts.Transform.EdfOpt.scheduled_job_in_sched_has_later_deadline
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_completed_jobs
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_no_deadline_misses
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_scheduled_job_has_later_deadline
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_dl_orig
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_fsc_is_j_edf
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_deadlines
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_case_t'_past_deadline
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_case_t'_before_deadline
#check @Prosa.Analysis.Facts.Transform.EdfOpt.make_edf_at_guarantee
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_jobs_must_arrive
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_job_scheduled
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_job_scheduled'
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_jobs_come_from_arrival_sequence
#check @Prosa.Analysis.Facts.Transform.EdfOpt.mea_EDF_widen
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_well_formedness
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_jobs_must_arrive
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_scheduled_job_has_later_deadline
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_job_scheduled
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_job_scheduled'
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_jobs_come_from_arrival_sequence
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_guarantee
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_inclusion
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_finite_prefix
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_ensures_edf
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_completed_jobs_dont_execute
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_jobs_must_arrive
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_deadlines_met
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_job_scheduled
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_job_scheduled'
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_jobs_come_from_arrival_sequence
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_schedule_is_valid
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_schedule_meets_all_deadlines
#check @Prosa.Analysis.Facts.Transform.EdfOpt.edf_schedule_meets_all_deadlines_wrt_arrivals

#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.t1_relevant
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.fsc_search_successful
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.fsc_search_result
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.fsc_not_idle
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.fsc_found_job_arrival
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.fsc_range
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.fsc_range1
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.fsc_found_job_deadline
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.fsc_no_later_deadline
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.scheduled_job_in_sched_has_later_deadline
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_completed_jobs
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_no_deadline_misses
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_scheduled_job_has_later_deadline
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_dl_orig
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_fsc_is_j_edf
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_deadlines
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_case_t'_past_deadline
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_case_t'_before_deadline
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.make_edf_at_guarantee
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_jobs_must_arrive
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_job_scheduled
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_job_scheduled'
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_jobs_come_from_arrival_sequence
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.mea_EDF_widen
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_well_formedness
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_jobs_must_arrive
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_scheduled_job_has_later_deadline
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_job_scheduled
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_job_scheduled'
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_jobs_come_from_arrival_sequence
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_guarantee
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_inclusion
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_finite_prefix
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_ensures_edf
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_completed_jobs_dont_execute
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_jobs_must_arrive
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_deadlines_met
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_job_scheduled
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_job_scheduled'
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_jobs_come_from_arrival_sequence
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_schedule_is_valid
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_schedule_meets_all_deadlines
#print axioms Prosa.Analysis.Facts.Transform.EdfOpt.edf_schedule_meets_all_deadlines_wrt_arrivals
