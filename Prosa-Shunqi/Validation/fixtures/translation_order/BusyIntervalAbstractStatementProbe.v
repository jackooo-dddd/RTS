Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BusyIntervalAbstractSemanticSource.
Import BusyIntervalAbstractSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.analysis.abstract.definitions.
(* display-only: the official elaborated-type evidence was printed with the classical
   busy-interval notions in scope, so the abstract ones are displayed qualified as
   [definitions.busy_interval_prefix] etc. *)
Module BusyIntervalAbstractProbeDisplay.
  Definition busy_interval_prefix := tt. Definition busy_interval := tt.
  Definition quiet_time := tt. Definition work_conserving := tt.
End BusyIntervalAbstractProbeDisplay.
Import BusyIntervalAbstractProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.abstract_busy_interval_arrivals_before". Abort.
Print statement_abstract_busy_interval_arrivals_before.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.abstract_busy_interval_arrivals_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.abstract_busy_interval_job_arrival". Abort.
Print statement_abstract_busy_interval_job_arrival.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.abstract_busy_interval_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.abstract_busy_interval_prefix_job_arrival". Abort.
Print statement_abstract_busy_interval_prefix_job_arrival.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.abstract_busy_interval_prefix_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.busy_interval_has_uninterrupted_service". Abort.
Print statement_busy_interval_has_uninterrupted_service.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.busy_interval_has_uninterrupted_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.busy_interval_is_bounded". Abort.
Print statement_busy_interval_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.busy_interval_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.busy_interval_prefix_case". Abort.
Print statement_busy_interval_prefix_case.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.busy_interval_prefix_case". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.busy_interval_too_much_workload". Abort.
Print statement_busy_interval_too_much_workload.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.busy_interval_too_much_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.exists_busy_interval_prefix". Abort.
Print statement_exists_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.exists_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.job_completes_within_busy_interval". Abort.
Print statement_job_completes_within_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.job_completes_within_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.no_service_before_busy_interval". Abort.
Print statement_no_service_before_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.no_service_before_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.service_and_interference_bound". Abort.
Print statement_service_and_interference_bound.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.service_and_interference_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.service_within_busy_interval_ge_job_cost". Abort.
Print statement_service_within_busy_interval_ge_job_cost.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.service_within_busy_interval_ge_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.t1δ_is_quiet". Abort.
Print statement_t1δ_is_quiet.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.t1δ_is_quiet". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.t1δ_is_quiet_contra". Abort.
Print statement_t1δ_is_quiet_contra.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.t1δ_is_quiet_contra". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.terminating_busy_prefix_is_busy_interval". Abort.
Print statement_terminating_busy_prefix_is_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.terminating_busy_prefix_is_busy_interval". Abort.
