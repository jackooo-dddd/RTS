From FoundationCertificates Require Import ConceptClasses ConceptCorrespondence.

Goal True. idtac "AUDIT_BEGIN TaskType". exact I. Qed.
Print Assumptions task_type_correspondence.
Goal True. idtac "AUDIT_END TaskType". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobTask_import". exact I. Qed.
Print Assumptions job_task_import_certificate.
Goal True. idtac "AUDIT_END JobTask_import". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobTask_export". exact I. Qed.
Print Assumptions job_task_export_certificate.
Goal True. idtac "AUDIT_END JobTask_export". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN TaskDeadline_import". exact I. Qed.
Print Assumptions task_deadline_import_certificate.
Goal True. idtac "AUDIT_END TaskDeadline_import". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN TaskDeadline_export". exact I. Qed.
Print Assumptions task_deadline_export_certificate.
Goal True. idtac "AUDIT_END TaskDeadline_export". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN TaskCost_import". exact I. Qed.
Print Assumptions task_cost_import_certificate.
Goal True. idtac "AUDIT_END TaskCost_import". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN TaskCost_export". exact I. Qed.
Print Assumptions task_cost_export_certificate.
Goal True. idtac "AUDIT_END TaskCost_export". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN TaskMinCost_import". exact I. Qed.
Print Assumptions task_min_cost_import_certificate.
Goal True. idtac "AUDIT_END TaskMinCost_import". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN TaskMinCost_export". exact I. Qed.
Print Assumptions task_min_cost_export_certificate.
Goal True. idtac "AUDIT_END TaskMinCost_export". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN task_cost_positive". exact I. Qed.
Print Assumptions task_cost_positive_correspondence.
Goal True. idtac "AUDIT_END task_cost_positive". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN task_cost_at_most_deadline". exact I. Qed.
Print Assumptions task_cost_at_most_deadline_correspondence.
Goal True. idtac "AUDIT_END task_cost_at_most_deadline". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN valid_job_cost". exact I. Qed.
Print Assumptions valid_job_cost_correspondence.
Goal True. idtac "AUDIT_END valid_job_cost". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN jobs_have_valid_job_costs". exact I. Qed.
Print Assumptions jobs_have_valid_job_costs_correspondence.
Goal True. idtac "AUDIT_END jobs_have_valid_job_costs". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN arrivals_have_valid_job_costs". exact I. Qed.
Print Assumptions arrivals_have_valid_job_costs_correspondence.
Goal True. idtac "AUDIT_END arrivals_have_valid_job_costs". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN valid_min_job_cost". exact I. Qed.
Print Assumptions valid_min_job_cost_correspondence.
Goal True. idtac "AUDIT_END valid_min_job_cost". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN jobs_have_valid_min_job_costs". exact I. Qed.
Print Assumptions jobs_have_valid_min_job_costs_correspondence.
Goal True. idtac "AUDIT_END jobs_have_valid_min_job_costs". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN arrivals_have_valid_min_job_costs". exact I. Qed.
Print Assumptions arrivals_have_valid_min_job_costs_correspondence.
Goal True. idtac "AUDIT_END arrivals_have_valid_min_job_costs". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN TaskSet_import". exact I. Qed.
Print Assumptions task_set_correspondence.
Goal True. idtac "AUDIT_END TaskSet_import". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN TaskSet_export". exact I. Qed.
Print Assumptions task_set_export_certificate.
Goal True. idtac "AUDIT_END TaskSet_export". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN all_jobs_from_taskset". exact I. Qed.
Print Assumptions all_jobs_from_taskset_correspondence.
Goal True. idtac "AUDIT_END all_jobs_from_taskset". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN same_task". exact I. Qed.
Print Assumptions same_task_correspondence.
Goal True. idtac "AUDIT_END same_task". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN same_task_sym". exact I. Qed.
Print Assumptions same_task_sym_correspondence.
Goal True. idtac "AUDIT_END same_task_sym". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN job_of_task". exact I. Qed.
Print Assumptions job_of_task_correspondence.
Goal True. idtac "AUDIT_END job_of_task". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN diff_task". exact I. Qed.
Print Assumptions diff_task_correspondence.
Goal True. idtac "AUDIT_END diff_task". exact I. Qed.
