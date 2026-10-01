Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsJobConstructorSemanticSource.
Import FactsJobConstructorSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
(* display-only: the class projections job_arrival/job_task/job_cost/task_cost are in scope, as in the evidence *)
Require Import prosa.behavior.all prosa.model.task.concept.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.job_generation_valid_number". Abort.
Print statement_job_generation_valid_number.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.job_generation_valid_number". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.generate_jobs_at_unique". Abort.
Print statement_generate_jobs_at_unique.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.generate_jobs_at_unique". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.job_arrival_consistent". Abort.
Print statement_job_arrival_consistent.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.job_arrival_consistent". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.arrivals_at_unique". Abort.
Print statement_arrivals_at_unique.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.arrivals_at_unique". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.arrivals_between_unique". Abort.
Print statement_arrivals_between_unique.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.arrivals_between_unique". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.job_generation_valid_jobs". Abort.
Print statement_job_generation_valid_jobs.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.job_generation_valid_jobs". Abort.
