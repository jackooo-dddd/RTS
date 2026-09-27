Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.ExistenceSemanticSource.
Import ExistenceSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.job_completes_within_busy_interval". Abort.
Print statement_job_completes_within_busy_interval.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.job_completes_within_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.not_quiet_implies_exists_pending_job". Abort.
Print statement_not_quiet_implies_exists_pending_job.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.not_quiet_implies_exists_pending_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.idle_time_implies_quiet_time_at_the_next_time_instant". Abort.
Print statement_idle_time_implies_quiet_time_at_the_next_time_instant.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.idle_time_implies_quiet_time_at_the_next_time_instant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.pending_hp_job_exists". Abort.
Print statement_pending_hp_job_exists.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.pending_hp_job_exists". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.not_quiet_implies_not_idle". Abort.
Print statement_not_quiet_implies_not_idle.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.not_quiet_implies_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.hep_jobs_receive_no_service_before_quiet_time". Abort.
Print statement_hep_jobs_receive_no_service_before_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.hep_jobs_receive_no_service_before_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.no_idle_time_within_non_quiet_time_interval". Abort.
Print statement_no_idle_time_within_non_quiet_time_interval.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.no_idle_time_within_non_quiet_time_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.exists_busy_interval_prefix". Abort.
Print statement_exists_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.exists_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.busy_interval_has_uninterrupted_service". Abort.
Print statement_busy_interval_has_uninterrupted_service.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.busy_interval_has_uninterrupted_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.busy_interval_too_much_workload". Abort.
Print statement_busy_interval_too_much_workload.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.busy_interval_too_much_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.busy_interval_workload_larger_than_interval". Abort.
Print statement_busy_interval_workload_larger_than_interval.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.busy_interval_workload_larger_than_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.busy_interval_is_bounded". Abort.
Print statement_busy_interval_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.busy_interval_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.exists_busy_interval". Abort.
Print statement_exists_busy_interval.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.exists_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.busy_interval_bounds_response_time". Abort.
Print statement_busy_interval_bounds_response_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.busy_interval_bounds_response_time". Abort.
