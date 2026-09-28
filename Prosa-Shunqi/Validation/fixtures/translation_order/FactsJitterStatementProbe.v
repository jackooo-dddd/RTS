Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsJitterSemanticSource.
Import FactsJitterSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the extracted module imports (does not export) platform_properties *)
Require Import prosa.model.processor.platform_properties.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_arrives_in_iff". Abort.
Print statement_jitter_arrives_in_iff.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_arrives_in_iff". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.valid_release_sequence". Abort.
Print statement_valid_release_sequence.
Goal True. idtac "END|prosa.analysis.facts.jitter.valid_release_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.valid_release_curve". Abort.
Print statement_valid_release_curve.
Goal True. idtac "END|prosa.analysis.facts.jitter.valid_release_curve". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.release_curve_respected". Abort.
Print statement_release_curve_respected.
Goal True. idtac "END|prosa.analysis.facts.jitter.release_curve_respected". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_prop_same_jobs". Abort.
Print statement_jitter_prop_same_jobs.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_prop_same_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_prop_same_jobs'". Abort.
Print statement_jitter_prop_same_jobs'.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_prop_same_jobs'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_prop_valid_costs". Abort.
Print statement_jitter_prop_valid_costs.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_prop_valid_costs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_ready_to_execute". Abort.
Print statement_jitter_ready_to_execute.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_work_conservation". Abort.
Print statement_jitter_work_conservation.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_work_conservation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_valid_schedule". Abort.
Print statement_jitter_valid_schedule.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_valid_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_scheduled_jobs_at_equiv". Abort.
Print statement_jitter_scheduled_jobs_at_equiv.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_scheduled_jobs_at_equiv". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_scheduled_job_at_eq". Abort.
Print statement_jitter_scheduled_job_at_eq.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_scheduled_job_at_eq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_FP_compliance". Abort.
Print statement_jitter_FP_compliance.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_FP_compliance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_response_time_bound". Abort.
Print statement_jitter_response_time_bound.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_response_time_bound". Abort.
