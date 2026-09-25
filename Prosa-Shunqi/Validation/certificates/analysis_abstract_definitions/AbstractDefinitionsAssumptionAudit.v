From FoundationCertificates Require Import
  AbstractDefinitionsClasses AbstractDefinitionsOperations
  AbstractDefinitionsSums AbstractDefinitionsLogical
  AbstractDefinitionsBusyInterval AbstractDefinitionsJobBound
  AbstractDefinitionsTaskOperations AbstractDefinitionsArrivalOperations
  AbstractDefinitionsPendingOperations.

Goal True.
Proof.
  idtac "AUDIT_BEGIN Interference".
  Print Assumptions ad_interference_import_certificate.
  idtac "AUDIT_END Interference".
  idtac "AUDIT_BEGIN InterferingWorkload".
  Print Assumptions ad_workload_import_certificate.
  idtac "AUDIT_END InterferingWorkload".
  idtac "AUDIT_BEGIN cond_interference".
  Print Assumptions cond_interference_correspondence.
  idtac "AUDIT_END cond_interference".
  idtac "AUDIT_BEGIN cumul_cond_interference".
  Print Assumptions cumul_cond_interference_correspondence.
  idtac "AUDIT_END cumul_cond_interference".
  idtac "AUDIT_BEGIN cumulative_interference".
  Print Assumptions cumulative_interference_correspondence.
  idtac "AUDIT_END cumulative_interference".
  idtac "AUDIT_BEGIN cumulative_interfering_workload".
  Print Assumptions cumulative_interfering_workload_correspondence.
  idtac "AUDIT_END cumulative_interfering_workload".
  idtac "AUDIT_BEGIN no_speculative_execution".
  Print Assumptions no_speculative_execution_correspondence.
  idtac "AUDIT_END no_speculative_execution".
  idtac "AUDIT_BEGIN quiet_time".
  Print Assumptions ad_quiet_time_correspondence.
  idtac "AUDIT_END quiet_time".
  idtac "AUDIT_BEGIN busy_interval_prefix".
  Print Assumptions ad_busy_interval_prefix_correspondence.
  idtac "AUDIT_END busy_interval_prefix".
  idtac "AUDIT_BEGIN busy_interval".
  Print Assumptions ad_busy_interval_correspondence.
  idtac "AUDIT_END busy_interval".
  idtac "AUDIT_BEGIN busy_interval_is_unique".
  Print Assumptions ad_busy_interval_unique_statement_correspondence.
  idtac "AUDIT_END busy_interval_is_unique".
  idtac "AUDIT_BEGIN work_conserving".
  Print Assumptions ad_work_conserving_correspondence.
  idtac "AUDIT_END work_conserving".
  idtac "AUDIT_BEGIN busy_intervals_are_bounded_by".
  Print Assumptions ad_busy_intervals_bounded_correspondence.
  idtac "AUDIT_END busy_intervals_are_bounded_by".
  idtac "AUDIT_BEGIN cond_interference_is_bounded_by".
  Print Assumptions ad_cond_interference_bounded_correspondence.
  idtac "AUDIT_END cond_interference_is_bounded_by".
  idtac "AUDIT_BEGIN job_interference_is_bounded_by".
  Print Assumptions ad_job_interference_bounded_correspondence.
  idtac "AUDIT_END job_interference_is_bounded_by".
  idtac "AUDIT_BEGIN JobTaskAdapter".
  Print Assumptions ad_job_of_task_related.
  idtac "AUDIT_END JobTaskAdapter".
  idtac "AUDIT_BEGIN ArrivalAdapter".
  Print Assumptions ad_arrives_in_related.
  idtac "AUDIT_END ArrivalAdapter".
  idtac "AUDIT_BEGIN ServiceAdapter".
  Print Assumptions ad_completed_by_related.
  idtac "AUDIT_END ServiceAdapter".
Abort.
