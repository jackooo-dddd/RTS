Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsBackloggedSemanticSource.
Import FactsBackloggedSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.ReadinessSemanticSource.
Import ReadinessSemanticSource.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.backlogged.mem_backlogged_jobs". Abort.
Print statement_mem_backlogged_jobs.
Goal True. idtac "END|prosa.analysis.facts.readiness.backlogged.mem_backlogged_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.backlogged.backlogged_job_arrives_in". Abort.
Print statement_backlogged_job_arrives_in.
Goal True. idtac "END|prosa.analysis.facts.readiness.backlogged.backlogged_job_arrives_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance". Abort.
Print statement_backlogged_prefix_invariance.
Goal True. idtac "END|prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance'". Abort.
Print statement_backlogged_prefix_invariance'.
Goal True. idtac "END|prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.backlogged.backlogged_jobs_prefix_invariance". Abort.
Print statement_backlogged_jobs_prefix_invariance.
Goal True. idtac "END|prosa.analysis.facts.readiness.backlogged.backlogged_jobs_prefix_invariance". Abort.
