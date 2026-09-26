import Prosa.Analysis.Facts.Behavior.Arrivals
set_option pp.fieldNotation false

#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_before
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrived_before_has_arrived
#check @Prosa.Analysis.Facts.Behavior.Arrivals.consistent_times_valid_arrival
#check @Prosa.Analysis.Facts.Behavior.Arrivals.uniq_valid_arrival
#check @Prosa.Analysis.Facts.Behavior.Arrivals.any_ready_job_is_pending
#check @Prosa.Analysis.Facts.Behavior.Arrivals.ready_implies_arrived
#check @Prosa.Analysis.Facts.Behavior.Arrivals.jobs_must_arrive_to_be_ready
#check @Prosa.Analysis.Facts.Behavior.Arrivals.valid_schedule_implies_jobs_must_arrive_to_execute
#check @Prosa.Analysis.Facts.Behavior.Arrivals.backlogged_implies_arrived
#check @Prosa.Analysis.Facts.Behavior.Arrivals.backlogged_implies_incomplete
#check @Prosa.Analysis.Facts.Behavior.Arrivals.job_scheduled_implies_ready
#check @Prosa.Analysis.Facts.Behavior.Arrivals.valid_schedule_jobs_come_from_arrival_sequence
#check @Prosa.Analysis.Facts.Behavior.Arrivals.valid_schedule_jobs_must_be_ready_to_execute
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_cat
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_P_cat
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_mem_cat
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_sub
#check @Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_arrives_at
#check @Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_at
#check @Prosa.Analysis.Facts.Behavior.Arrivals.job_in_arrivals_at
#check @Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between
#check @Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between_ge
#check @Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between_lt
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_filter_nil
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_filter
#check @Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived
#check @Prosa.Analysis.Facts.Behavior.Arrivals.in_arrseq_implies_arrives
#check @Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_between
#check @Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_before
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
#check @Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between_P
#check @Prosa.Analysis.Facts.Behavior.Arrivals.job_in_arrivals_between
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_uniq
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_geq
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_nonempty
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrival_lt_implies_job_in_arrivals_between_P
#check @Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_in_bounds
#check @Prosa.Analysis.Facts.Behavior.Arrivals.by_arrival_times
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_at_sorted
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_sorted
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_partitioned_by_task
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrives_in_jobs_come_from_arrival_sequence
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_jobs_must_arrive_to_execute
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_before_scheduled_at
#check @Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_up_to_scheduled_at

#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_before
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrived_before_has_arrived
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.consistent_times_valid_arrival
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.uniq_valid_arrival
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.any_ready_job_is_pending
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.ready_implies_arrived
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.jobs_must_arrive_to_be_ready
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.valid_schedule_implies_jobs_must_arrive_to_execute
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.backlogged_implies_arrived
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.backlogged_implies_incomplete
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.job_scheduled_implies_ready
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.valid_schedule_jobs_come_from_arrival_sequence
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.valid_schedule_jobs_must_be_ready_to_execute
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_cat
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_P_cat
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_mem_cat
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_sub
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_arrives_at
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_at
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.job_in_arrivals_at
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between_ge
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between_lt
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_filter_nil
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_filter
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.in_arrseq_implies_arrives
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_between
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_before
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between_P
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.job_in_arrivals_between
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_uniq
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_geq
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_nonempty
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrival_lt_implies_job_in_arrivals_between_P
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_in_bounds
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.by_arrival_times
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_at_sorted
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_sorted
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_partitioned_by_task
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrives_in_jobs_come_from_arrival_sequence
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_jobs_must_arrive_to_execute
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_before_scheduled_at
#print axioms Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_up_to_scheduled_at
