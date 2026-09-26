From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations FactsScheduledCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_jobs_at_iff_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_jobs_at_iff_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_jobs_at_iff_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_jobs_at_nil_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_jobs_at_nil_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_jobs_at_nil_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_scheduled_when_idle_correspondence". exact Logic.I. Qed.
Print Assumptions not_scheduled_when_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END not_scheduled_when_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_at_implies_in_served_at_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_at_implies_in_served_at_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_at_implies_in_served_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_jobs_at_seq1_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_jobs_at_seq1_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_jobs_at_seq1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_jobs_at_uni_cases_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_jobs_at_uni_cases_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_jobs_at_uni_cases_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_jobs_at_uni_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_jobs_at_uni_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_jobs_at_uni_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_job_at_scheduled_at_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_job_at_scheduled_at_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_job_at_scheduled_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_jobs_at_scheduled_at_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_jobs_at_scheduled_at_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_jobs_at_scheduled_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_job_at_none_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_job_at_none_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_job_at_none_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN is_idle_iff_correspondence". exact Logic.I. Qed.
Print Assumptions is_idle_iff_correspondence.
Goal Logic.True. idtac "AUDIT_END is_idle_iff_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN is_nonidle_iff_correspondence". exact Logic.I. Qed.
Print Assumptions is_nonidle_iff_correspondence.
Goal Logic.True. idtac "AUDIT_END is_nonidle_iff_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_at_dec_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_at_dec_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_at_dec_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_at_cases_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_at_cases_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_at_cases_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_forall_arrival_sequence". exact Logic.I. Qed.
Print Assumptions fs_forall_arrival_sequence.
Goal Logic.True. idtac "AUDIT_END fs_forall_arrival_sequence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_forall_schedule". exact Logic.I. Qed.
Print Assumptions fs_forall_schedule.
Goal Logic.True. idtac "AUDIT_END fs_forall_schedule". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_forall_state". exact Logic.I. Qed.
Print Assumptions fs_forall_state.
Goal Logic.True. idtac "AUDIT_END fs_forall_state". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_ideal_progress_related". exact Logic.I. Qed.
Print Assumptions fs_ideal_progress_related.
Goal Logic.True. idtac "AUDIT_END fs_ideal_progress_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_uniprocessor_related". exact Logic.I. Qed.
Print Assumptions fs_uniprocessor_related.
Goal Logic.True. idtac "AUDIT_END fs_uniprocessor_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_scheduled_jobs_at_related". exact Logic.I. Qed.
Print Assumptions fs_scheduled_jobs_at_related.
Goal Logic.True. idtac "AUDIT_END fs_scheduled_jobs_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_scheduled_job_at_related". exact Logic.I. Qed.
Print Assumptions fs_scheduled_job_at_related.
Goal Logic.True. idtac "AUDIT_END fs_scheduled_job_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_is_idle_related". exact Logic.I. Qed.
Print Assumptions fs_is_idle_related.
Goal Logic.True. idtac "AUDIT_END fs_is_idle_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_served_jobs_at_related". exact Logic.I. Qed.
Print Assumptions fs_served_jobs_at_related.
Goal Logic.True. idtac "AUDIT_END fs_served_jobs_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_list_eq_decide". exact Logic.I. Qed.
Print Assumptions fs_list_eq_decide.
Goal Logic.True. idtac "AUDIT_END fs_list_eq_decide". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_option_eq_decide". exact Logic.I. Qed.
Print Assumptions fs_option_eq_decide.
Goal Logic.True. idtac "AUDIT_END fs_option_eq_decide". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_option_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fs_option_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fs_option_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_nilp_related". exact Logic.I. Qed.
Print Assumptions fs_nilp_related.
Goal Logic.True. idtac "AUDIT_END fs_nilp_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ts_sumbool". exact Logic.I. Qed.
Print Assumptions ts_sumbool.
Goal Logic.True. idtac "AUDIT_END ts_sumbool". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ts_forall_arrival_sequence". exact Logic.I. Qed.
Print Assumptions ts_forall_arrival_sequence.
Goal Logic.True. idtac "AUDIT_END ts_forall_arrival_sequence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ts_forall_schedule". exact Logic.I. Qed.
Print Assumptions ts_forall_schedule.
Goal Logic.True. idtac "AUDIT_END ts_forall_schedule". exact Logic.I. Qed.
