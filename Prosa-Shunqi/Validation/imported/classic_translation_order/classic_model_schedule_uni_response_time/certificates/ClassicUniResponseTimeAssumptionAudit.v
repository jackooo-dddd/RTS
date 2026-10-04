From FoundationCertificates Require Import ClassicUniResponseTimeCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN ResponseTime_is_response_time_bound_of_job_correspondence". exact Logic.I. Qed.
Print Assumptions ResponseTime_is_response_time_bound_of_job_correspondence.
Goal Logic.True. idtac "AUDIT_END ResponseTime_is_response_time_bound_of_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ResponseTime_is_response_time_bound_of_task_correspondence". exact Logic.I. Qed.
Print Assumptions ResponseTime_is_response_time_bound_of_task_correspondence.
Goal Logic.True. idtac "AUDIT_END ResponseTime_is_response_time_bound_of_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ResponseTime_service_after_job_rt_zero_correspondence". exact Logic.I. Qed.
Print Assumptions ResponseTime_service_after_job_rt_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END ResponseTime_service_after_job_rt_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ResponseTime_cumulative_service_after_job_rt_zero_correspondence". exact Logic.I. Qed.
Print Assumptions ResponseTime_cumulative_service_after_job_rt_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END ResponseTime_cumulative_service_after_job_rt_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ResponseTime_service_after_task_rt_zero_correspondence". exact Logic.I. Qed.
Print Assumptions ResponseTime_service_after_task_rt_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END ResponseTime_service_after_task_rt_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ResponseTime_cumulative_service_after_task_rt_zero_correspondence". exact Logic.I. Qed.
Print Assumptions ResponseTime_cumulative_service_after_task_rt_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END ResponseTime_cumulative_service_after_task_rt_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN crt_forall_sched". exact Logic.I. Qed.
Print Assumptions crt_forall_sched.
Goal Logic.True. idtac "AUDIT_END crt_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN crt_forall_par". exact Logic.I. Qed.
Print Assumptions crt_forall_par.
Goal Logic.True. idtac "AUDIT_END crt_forall_par". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN crt_ico". exact Logic.I. Qed.
Print Assumptions crt_ico.
Goal Logic.True. idtac "AUDIT_END crt_ico". exact Logic.I. Qed.
