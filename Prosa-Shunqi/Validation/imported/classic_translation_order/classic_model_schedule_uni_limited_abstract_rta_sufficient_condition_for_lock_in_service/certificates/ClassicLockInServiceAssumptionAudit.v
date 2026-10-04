From FoundationCertificates Require Import ClassicLockInServiceCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN AbstractRTALockInService_job_completes_within_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions AbstractRTALockInService_job_completes_within_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END AbstractRTALockInService_job_completes_within_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN AbstractRTALockInService_interference_is_complement_to_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions AbstractRTALockInService_interference_is_complement_to_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END AbstractRTALockInService_interference_is_complement_to_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN AbstractRTALockInService_j_receives_at_least_lock_in_service_correspondence". exact Logic.I. Qed.
Print Assumptions AbstractRTALockInService_j_receives_at_least_lock_in_service_correspondence.
Goal Logic.True. idtac "AUDIT_END AbstractRTALockInService_j_receives_at_least_lock_in_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN AbstractRTALockInService_job_completes_after_reaching_lock_in_service_correspondence". exact Logic.I. Qed.
Print Assumptions AbstractRTALockInService_job_completes_after_reaching_lock_in_service_correspondence.
Goal Logic.True. idtac "AUDIT_END AbstractRTALockInService_job_completes_after_reaching_lock_in_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN clk_forall_int". exact Logic.I. Qed.
Print Assumptions clk_forall_int.
Goal Logic.True. idtac "AUDIT_END clk_forall_int". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN clk_forall_wl". exact Logic.I. Qed.
Print Assumptions clk_forall_wl.
Goal Logic.True. idtac "AUDIT_END clk_forall_wl". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN clk_forall_sched". exact Logic.I. Qed.
Print Assumptions clk_forall_sched.
Goal Logic.True. idtac "AUDIT_END clk_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN clk_forall_par". exact Logic.I. Qed.
Print Assumptions clk_forall_par.
Goal Logic.True. idtac "AUDIT_END clk_forall_par". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN clk_forall_arr". exact Logic.I. Qed.
Print Assumptions clk_forall_arr.
Goal Logic.True. idtac "AUDIT_END clk_forall_arr". exact Logic.I. Qed.
