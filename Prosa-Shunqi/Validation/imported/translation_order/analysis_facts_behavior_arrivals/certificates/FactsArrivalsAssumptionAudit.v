From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations FactsArrivalsCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN arrived_between_before_correspondence". exact Logic.I. Qed.
Print Assumptions arrived_between_before_correspondence.
Goal Logic.True. idtac "AUDIT_END arrived_between_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrived_before_has_arrived_correspondence". exact Logic.I. Qed.
Print Assumptions arrived_before_has_arrived_correspondence.
Goal Logic.True. idtac "AUDIT_END arrived_before_has_arrived_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN consistent_times_valid_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions consistent_times_valid_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END consistent_times_valid_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniq_valid_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions uniq_valid_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END uniq_valid_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN any_ready_job_is_pending_correspondence". exact Logic.I. Qed.
Print Assumptions any_ready_job_is_pending_correspondence.
Goal Logic.True. idtac "AUDIT_END any_ready_job_is_pending_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ready_implies_arrived_correspondence". exact Logic.I. Qed.
Print Assumptions ready_implies_arrived_correspondence.
Goal Logic.True. idtac "AUDIT_END ready_implies_arrived_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jobs_must_arrive_to_be_ready_correspondence". exact Logic.I. Qed.
Print Assumptions jobs_must_arrive_to_be_ready_correspondence.
Goal Logic.True. idtac "AUDIT_END jobs_must_arrive_to_be_ready_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_schedule_implies_jobs_must_arrive_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions valid_schedule_implies_jobs_must_arrive_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_schedule_implies_jobs_must_arrive_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN backlogged_implies_arrived_correspondence". exact Logic.I. Qed.
Print Assumptions backlogged_implies_arrived_correspondence.
Goal Logic.True. idtac "AUDIT_END backlogged_implies_arrived_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN backlogged_implies_incomplete_correspondence". exact Logic.I. Qed.
Print Assumptions backlogged_implies_incomplete_correspondence.
Goal Logic.True. idtac "AUDIT_END backlogged_implies_incomplete_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_scheduled_implies_ready_correspondence". exact Logic.I. Qed.
Print Assumptions job_scheduled_implies_ready_correspondence.
Goal Logic.True. idtac "AUDIT_END job_scheduled_implies_ready_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_schedule_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions valid_schedule_jobs_come_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_schedule_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_schedule_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions valid_schedule_jobs_must_be_ready_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_schedule_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_between_cat_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_between_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_between_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_P_cat_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_P_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_P_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_between_mem_cat_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_between_mem_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_between_mem_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_between_sub_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_between_sub_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_between_sub_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_arrives_at_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_arrives_at_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_arrives_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_at_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_at_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_in_arrivals_at_correspondence". exact Logic.I. Qed.
Print Assumptions job_in_arrivals_at_correspondence.
Goal Logic.True. idtac "AUDIT_END job_in_arrivals_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_between_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_between_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_between_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_between_ge_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_between_ge_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_between_ge_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_between_lt_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_between_lt_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_between_lt_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_between_filter_nil_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_between_filter_nil_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_between_filter_nil_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_between_filter_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_between_filter_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_between_filter_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN in_arrivals_implies_arrived_correspondence". exact Logic.I. Qed.
Print Assumptions in_arrivals_implies_arrived_correspondence.
Goal Logic.True. idtac "AUDIT_END in_arrivals_implies_arrived_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN in_arrseq_implies_arrives_correspondence". exact Logic.I. Qed.
Print Assumptions in_arrseq_implies_arrives_correspondence.
Goal Logic.True. idtac "AUDIT_END in_arrseq_implies_arrives_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN in_arrivals_implies_arrived_between_correspondence". exact Logic.I. Qed.
Print Assumptions in_arrivals_implies_arrived_between_correspondence.
Goal Logic.True. idtac "AUDIT_END in_arrivals_implies_arrived_between_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN in_arrivals_implies_arrived_before_correspondence". exact Logic.I. Qed.
Print Assumptions in_arrivals_implies_arrived_before_correspondence.
Goal Logic.True. idtac "AUDIT_END in_arrivals_implies_arrived_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrived_between_implies_in_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions arrived_between_implies_in_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END arrived_between_implies_in_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_between_P_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_between_P_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_between_P_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_in_arrivals_between_correspondence". exact Logic.I. Qed.
Print Assumptions job_in_arrivals_between_correspondence.
Goal Logic.True. idtac "AUDIT_END job_in_arrivals_between_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_uniq_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_uniq_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_uniq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_between_geq_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_between_geq_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_between_geq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_between_nonempty_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_between_nonempty_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_between_nonempty_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrival_lt_implies_job_in_arrivals_between_P_correspondence". exact Logic.I. Qed.
Print Assumptions arrival_lt_implies_job_in_arrivals_between_P_correspondence.
Goal Logic.True. idtac "AUDIT_END arrival_lt_implies_job_in_arrivals_between_P_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_in_bounds_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_in_bounds_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_in_bounds_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN by_arrival_times_correspondence". exact Logic.I. Qed.
Print Assumptions by_arrival_times_correspondence.
Goal Logic.True. idtac "AUDIT_END by_arrival_times_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_at_sorted_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_at_sorted_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_at_sorted_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_between_sorted_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_between_sorted_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_between_sorted_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_between_partitioned_by_task_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_between_partitioned_by_task_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_between_partitioned_by_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrives_in_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions arrives_in_jobs_come_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END arrives_in_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrived_between_jobs_must_arrive_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions arrived_between_jobs_must_arrive_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END arrived_between_jobs_must_arrive_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_before_scheduled_at_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_before_scheduled_at_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_before_scheduled_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_up_to_scheduled_at_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_up_to_scheduled_at_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_up_to_scheduled_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_forall_arrival_sequence". exact Logic.I. Qed.
Print Assumptions fa_forall_arrival_sequence.
Goal Logic.True. idtac "AUDIT_END fa_forall_arrival_sequence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_forall_pred". exact Logic.I. Qed.
Print Assumptions fa_forall_pred.
Goal Logic.True. idtac "AUDIT_END fa_forall_pred". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_forall_list". exact Logic.I. Qed.
Print Assumptions fa_forall_list.
Goal Logic.True. idtac "AUDIT_END fa_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_forall_schedule". exact Logic.I. Qed.
Print Assumptions fa_forall_schedule.
Goal Logic.True. idtac "AUDIT_END fa_forall_schedule". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_sched_to_target_rel". exact Logic.I. Qed.
Print Assumptions fa_sched_to_target_rel.
Goal Logic.True. idtac "AUDIT_END fa_sched_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_sched_to_source_rel". exact Logic.I. Qed.
Print Assumptions fa_sched_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fa_sched_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_sorted_ischain". exact Logic.I. Qed.
Print Assumptions fa_sorted_ischain.
Goal Logic.True. idtac "AUDIT_END fa_sorted_ischain". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_bigcat_related". exact Logic.I. Qed.
Print Assumptions fa_bigcat_related.
Goal Logic.True. idtac "AUDIT_END fa_bigcat_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_jobs_come_from_related". exact Logic.I. Qed.
Print Assumptions fa_jobs_come_from_related.
Goal Logic.True. idtac "AUDIT_END fa_jobs_come_from_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_jobs_must_arrive_related". exact Logic.I. Qed.
Print Assumptions fa_jobs_must_arrive_related.
Goal Logic.True. idtac "AUDIT_END fa_jobs_must_arrive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_pending_related". exact Logic.I. Qed.
Print Assumptions fa_pending_related.
Goal Logic.True. idtac "AUDIT_END fa_pending_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_backlogged_related". exact Logic.I. Qed.
Print Assumptions fa_backlogged_related.
Goal Logic.True. idtac "AUDIT_END fa_backlogged_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_valid_schedule_related". exact Logic.I. Qed.
Print Assumptions fa_valid_schedule_related.
Goal Logic.True. idtac "AUDIT_END fa_valid_schedule_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fa_all_jobs_from_taskset_related". exact Logic.I. Qed.
Print Assumptions fa_all_jobs_from_taskset_related.
Goal Logic.True. idtac "AUDIT_END fa_all_jobs_from_taskset_related". exact Logic.I. Qed.
