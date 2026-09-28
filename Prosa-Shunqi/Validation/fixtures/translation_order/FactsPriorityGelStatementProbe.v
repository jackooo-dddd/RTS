Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsPriorityGelSemanticSource.
Import FactsPriorityGelSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the extracted module imports (does not export) util/int and model/priority/gel *)
Require Import prosa.util.int prosa.model.priority.gel.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.hep_job_priority_point". Abort.
Print statement_hep_job_priority_point.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.hep_job_priority_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.hep_job_arrival_gel". Abort.
Print statement_hep_job_arrival_gel.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.hep_job_arrival_gel". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.hep_job_arrives_before". Abort.
Print statement_hep_job_arrives_before.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.hep_job_arrives_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.hep_job_arrives_after_zero". Abort.
Print statement_hep_job_arrives_after_zero.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.hep_job_arrives_after_zero". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.GEL_respects_sequential_tasks". Abort.
Print statement_GEL_respects_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.GEL_respects_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.GEL_implies_sequential_tasks". Abort.
Print statement_GEL_implies_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.GEL_implies_sequential_tasks". Abort.
