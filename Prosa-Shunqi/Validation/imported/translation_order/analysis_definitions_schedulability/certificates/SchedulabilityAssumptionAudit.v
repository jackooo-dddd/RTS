From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations SchedulabilityCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN task_response_time_bound_correspondence". exact Logic.I. Qed.
Print Assumptions task_response_time_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END task_response_time_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN schedulable_task_correspondence". exact Logic.I. Qed.
Print Assumptions schedulable_task_correspondence.
Goal Logic.True. idtac "AUDIT_END schedulable_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN schedulability_from_response_time_bound_correspondence". exact Logic.I. Qed.
Print Assumptions schedulability_from_response_time_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END schedulability_from_response_time_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN all_deadlines_met_correspondence". exact Logic.I. Qed.
Print Assumptions all_deadlines_met_correspondence.
Goal Logic.True. idtac "AUDIT_END all_deadlines_met_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN all_deadlines_of_arrivals_met_correspondence". exact Logic.I. Qed.
Print Assumptions all_deadlines_of_arrivals_met_correspondence.
Goal Logic.True. idtac "AUDIT_END all_deadlines_of_arrivals_met_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN all_deadlines_met_in_valid_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions all_deadlines_met_in_valid_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END all_deadlines_met_in_valid_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_lean_transport". exact Logic.I. Qed.
Print Assumptions sch_lean_transport.
Goal Logic.True. idtac "AUDIT_END sch_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_nat_input". exact Logic.I. Qed.
Print Assumptions sch_nat_input.
Goal Logic.True. idtac "AUDIT_END sch_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_logic_eq_to_lean_eq". exact Logic.I. Qed.
Print Assumptions sch_logic_eq_to_lean_eq.
Goal Logic.True. idtac "AUDIT_END sch_logic_eq_to_lean_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_decide_eq_related". exact Logic.I. Qed.
Print Assumptions sch_decide_eq_related.
Goal Logic.True. idtac "AUDIT_END sch_decide_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_arrival_sequence_to_source_rel". exact Logic.I. Qed.
Print Assumptions sch_arrival_sequence_to_source_rel.
Goal Logic.True. idtac "AUDIT_END sch_arrival_sequence_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_forall_arrival_sequence". exact Logic.I. Qed.
Print Assumptions sch_forall_arrival_sequence.
Goal Logic.True. idtac "AUDIT_END sch_forall_arrival_sequence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions sch_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END sch_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_service_at_related". exact Logic.I. Qed.
Print Assumptions sch_service_at_related.
Goal Logic.True. idtac "AUDIT_END sch_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_service_related". exact Logic.I. Qed.
Print Assumptions sch_service_related.
Goal Logic.True. idtac "AUDIT_END sch_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_completed_by_related". exact Logic.I. Qed.
Print Assumptions sch_completed_by_related.
Goal Logic.True. idtac "AUDIT_END sch_completed_by_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_job_meets_deadline_related". exact Logic.I. Qed.
Print Assumptions sch_job_meets_deadline_related.
Goal Logic.True. idtac "AUDIT_END sch_job_meets_deadline_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_jobs_come_from_arrival_sequence_related". exact Logic.I. Qed.
Print Assumptions sch_jobs_come_from_arrival_sequence_related.
Goal Logic.True. idtac "AUDIT_END sch_jobs_come_from_arrival_sequence_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions sch_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END sch_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions sch_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END sch_schedule_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_forall_schedule". exact Logic.I. Qed.
Print Assumptions sch_forall_schedule.
Goal Logic.True. idtac "AUDIT_END sch_forall_schedule". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_job_of_task_related". exact Logic.I. Qed.
Print Assumptions sch_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END sch_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sch_task_deadline_instance_related". exact Logic.I. Qed.
Print Assumptions sch_task_deadline_instance_related.
Goal Logic.True. idtac "AUDIT_END sch_task_deadline_instance_related". exact Logic.I. Qed.
