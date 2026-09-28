Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsCarryInSemanticSource.
Import FactsCarryInSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.no_carry_in_at_zero". Abort.
Print statement_no_carry_in_at_zero.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.no_carry_in_at_zero". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.pending_job_not_idle". Abort.
Print statement_pending_job_not_idle.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.pending_job_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.idle_instant_no_carry_in". Abort.
Print statement_idle_instant_no_carry_in.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.idle_instant_no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.idle_instant_next_no_carry_in". Abort.
Print statement_idle_instant_next_no_carry_in.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.idle_instant_next_no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.total_service_is_bounded_by_Δ". Abort.
Print statement_total_service_is_bounded_by_Δ.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.total_service_is_bounded_by_Δ". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.low_total_service_implies_existence_of_time_with_no_carry_in". Abort.
Print statement_low_total_service_implies_existence_of_time_with_no_carry_in.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.low_total_service_implies_existence_of_time_with_no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.completion_of_all_jobs_implies_no_carry_in". Abort.
Print statement_completion_of_all_jobs_implies_no_carry_in.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.completion_of_all_jobs_implies_no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.processor_is_not_too_busy". Abort.
Print statement_processor_is_not_too_busy.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.processor_is_not_too_busy". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.busy_interval_from_total_workload_bound". Abort.
Print statement_busy_interval_from_total_workload_bound.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.busy_interval_from_total_workload_bound". Abort.
