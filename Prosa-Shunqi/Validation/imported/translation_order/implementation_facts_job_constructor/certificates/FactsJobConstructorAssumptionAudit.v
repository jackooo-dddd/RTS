From FoundationCertificates Require Import
  EacFullCorrespondence AbCorrespondence ImplTaskCorrespondence JobConstructorCorrespondence JcJitterSvcBaseAdapter JcJitterSvcNatBoolOperations JcJitterSvcIntervalOperations JcMaximalArrivalSequenceCorrespondence JcListOps FactsJobConstructorCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN job_generation_valid_number_correspondence". exact Logic.I. Qed.
Print Assumptions job_generation_valid_number_correspondence.
Goal Logic.True. idtac "AUDIT_END job_generation_valid_number_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN generate_jobs_at_unique_correspondence". exact Logic.I. Qed.
Print Assumptions generate_jobs_at_unique_correspondence.
Goal Logic.True. idtac "AUDIT_END generate_jobs_at_unique_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_consistent_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_consistent_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_consistent_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_at_unique_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_at_unique_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_at_unique_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_between_unique_correspondence". exact Logic.I. Qed.
Print Assumptions arrivals_between_unique_correspondence.
Goal Logic.True. idtac "AUDIT_END arrivals_between_unique_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_generation_valid_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions job_generation_valid_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END job_generation_valid_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_forall_cover". exact Logic.I. Qed.
Print Assumptions jf_forall_cover.
Goal Logic.True. idtac "AUDIT_END jf_forall_cover". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_imp". exact Logic.I. Qed.
Print Assumptions jf_imp.
Goal Logic.True. idtac "AUDIT_END jf_imp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_and". exact Logic.I. Qed.
Print Assumptions jf_and.
Goal Logic.True. idtac "AUDIT_END jf_and". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_forall_nat". exact Logic.I. Qed.
Print Assumptions jf_forall_nat.
Goal Logic.True. idtac "AUDIT_END jf_forall_nat". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_forall_task". exact Logic.I. Qed.
Print Assumptions jf_forall_task.
Goal Logic.True. idtac "AUDIT_END jf_forall_task". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_forall_job". exact Logic.I. Qed.
Print Assumptions jf_forall_job.
Goal Logic.True. idtac "AUDIT_END jf_forall_job". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_task_cancel". exact Logic.I. Qed.
Print Assumptions jf_task_cancel.
Goal Logic.True. idtac "AUDIT_END jf_task_cancel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_job_cancel". exact Logic.I. Qed.
Print Assumptions jf_job_cancel.
Goal Logic.True. idtac "AUDIT_END jf_job_cancel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_task_export_inj". exact Logic.I. Qed.
Print Assumptions jf_task_export_inj.
Goal Logic.True. idtac "AUDIT_END jf_task_export_inj". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_job_export_inj". exact Logic.I. Qed.
Print Assumptions jf_job_export_inj.
Goal Logic.True. idtac "AUDIT_END jf_job_export_inj". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_tasks_export". exact Logic.I. Qed.
Print Assumptions jf_tasks_export.
Goal Logic.True. idtac "AUDIT_END jf_tasks_export". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_tasks_import". exact Logic.I. Qed.
Print Assumptions jf_tasks_import.
Goal Logic.True. idtac "AUDIT_END jf_tasks_import". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_tasks_target_roundtrip". exact Logic.I. Qed.
Print Assumptions jf_tasks_target_roundtrip.
Goal Logic.True. idtac "AUDIT_END jf_tasks_target_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_forall_tasks". exact Logic.I. Qed.
Print Assumptions jf_forall_tasks.
Goal Logic.True. idtac "AUDIT_END jf_forall_tasks". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_tasks_ar". exact Logic.I. Qed.
Print Assumptions jf_tasks_ar.
Goal Logic.True. idtac "AUDIT_END jf_tasks_ar". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_jobs_ar". exact Logic.I. Qed.
Print Assumptions jf_jobs_ar.
Goal Logic.True. idtac "AUDIT_END jf_jobs_ar". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_tasks_arlist". exact Logic.I. Qed.
Print Assumptions jf_tasks_arlist.
Goal Logic.True. idtac "AUDIT_END jf_tasks_arlist". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_jobs_arlist". exact Logic.I. Qed.
Print Assumptions jf_jobs_arlist.
Goal Logic.True. idtac "AUDIT_END jf_jobs_arlist". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_tasks_uniq". exact Logic.I. Qed.
Print Assumptions jf_tasks_uniq.
Goal Logic.True. idtac "AUDIT_END jf_tasks_uniq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_jobs_uniq". exact Logic.I. Qed.
Print Assumptions jf_jobs_uniq.
Goal Logic.True. idtac "AUDIT_END jf_jobs_uniq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_task_mem_decide". exact Logic.I. Qed.
Print Assumptions jf_task_mem_decide.
Goal Logic.True. idtac "AUDIT_END jf_task_mem_decide". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_job_mem_decide". exact Logic.I. Qed.
Print Assumptions jf_job_mem_decide.
Goal Logic.True. idtac "AUDIT_END jf_job_mem_decide". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_jobs_length". exact Logic.I. Qed.
Print Assumptions jf_jobs_length.
Goal Logic.True. idtac "AUDIT_END jf_jobs_length". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_jobs_length_rel". exact Logic.I. Qed.
Print Assumptions jf_jobs_length_rel.
Goal Logic.True. idtac "AUDIT_END jf_jobs_length_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_max_arrivals_rel". exact Logic.I. Qed.
Print Assumptions jf_max_arrivals_rel.
Goal Logic.True. idtac "AUDIT_END jf_max_arrivals_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_jobs_append". exact Logic.I. Qed.
Print Assumptions jf_jobs_append.
Goal Logic.True. idtac "AUDIT_END jf_jobs_append". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_bigcat_tasks". exact Logic.I. Qed.
Print Assumptions jf_bigcat_tasks.
Goal Logic.True. idtac "AUDIT_END jf_bigcat_tasks". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_arrivals_at_rel". exact Logic.I. Qed.
Print Assumptions jf_arrivals_at_rel.
Goal Logic.True. idtac "AUDIT_END jf_arrivals_at_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_bigcat_delta". exact Logic.I. Qed.
Print Assumptions jf_bigcat_delta.
Goal Logic.True. idtac "AUDIT_END jf_bigcat_delta". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_bigcat_canonical". exact Logic.I. Qed.
Print Assumptions jf_bigcat_canonical.
Goal Logic.True. idtac "AUDIT_END jf_bigcat_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jf_arrivals_between_rel". exact Logic.I. Qed.
Print Assumptions jf_arrivals_between_rel.
Goal Logic.True. idtac "AUDIT_END jf_arrivals_between_rel". exact Logic.I. Qed.
