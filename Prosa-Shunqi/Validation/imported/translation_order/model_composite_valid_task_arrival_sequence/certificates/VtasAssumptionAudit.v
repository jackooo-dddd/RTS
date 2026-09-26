From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence CurvesCorrespondence VtasCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN valid_task_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions valid_task_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_task_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_task_arrival_sequence_valid_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions valid_task_arrival_sequence_valid_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_task_arrival_sequence_valid_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_task_arrival_sequence_valid_costs_correspondence". exact Logic.I. Qed.
Print Assumptions valid_task_arrival_sequence_valid_costs_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_task_arrival_sequence_valid_costs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_task_arrival_sequence_from_taskset_correspondence". exact Logic.I. Qed.
Print Assumptions valid_task_arrival_sequence_from_taskset_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_task_arrival_sequence_from_taskset_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_task_arrival_sequence_respects_max_correspondence". exact Logic.I. Qed.
Print Assumptions valid_task_arrival_sequence_respects_max_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_task_arrival_sequence_respects_max_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_task_arrival_sequence_valid_curve_correspondence". exact Logic.I. Qed.
Print Assumptions valid_task_arrival_sequence_valid_curve_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_task_arrival_sequence_valid_curve_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskCost_source_total". exact Logic.I. Qed.
Print Assumptions TaskCost_source_total.
Goal Logic.True. idtac "AUDIT_END TaskCost_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskCost_target_total". exact Logic.I. Qed.
Print Assumptions TaskCost_target_total.
Goal Logic.True. idtac "AUDIT_END TaskCost_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN vt_arrivals_have_valid_job_costs_related". exact Logic.I. Qed.
Print Assumptions vt_arrivals_have_valid_job_costs_related.
Goal Logic.True. idtac "AUDIT_END vt_arrivals_have_valid_job_costs_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN vt_all_jobs_from_taskset_related". exact Logic.I. Qed.
Print Assumptions vt_all_jobs_from_taskset_related.
Goal Logic.True. idtac "AUDIT_END vt_all_jobs_from_taskset_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN vt_forall_list". exact Logic.I. Qed.
Print Assumptions vt_forall_list.
Goal Logic.True. idtac "AUDIT_END vt_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN vt_forall_arrival_sequence". exact Logic.I. Qed.
Print Assumptions vt_forall_arrival_sequence.
Goal Logic.True. idtac "AUDIT_END vt_forall_arrival_sequence". exact Logic.I. Qed.
