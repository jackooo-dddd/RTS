Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsPriorityEdfSemanticSource.
Import FactsPriorityEdfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
Require Import prosa.model.priority.edf prosa.model.task.absolute_deadline prosa.model.task.sequentiality.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.edf.hep_job_deadline". Abort.
Print statement_hep_job_deadline.
Goal True. idtac "END|prosa.analysis.facts.priority.edf.hep_job_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.edf.hep_job_task_deadline". Abort.
Print statement_hep_job_task_deadline.
Goal True. idtac "END|prosa.analysis.facts.priority.edf.hep_job_task_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.edf.hep_job_arrival_edf". Abort.
Print statement_hep_job_arrival_edf.
Goal True. idtac "END|prosa.analysis.facts.priority.edf.hep_job_arrival_edf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.edf.EDF_respects_sequential_tasks". Abort.
Print statement_EDF_respects_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.edf.EDF_respects_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.edf.EDF_implies_sequential_tasks". Abort.
Print statement_EDF_implies_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.edf.EDF_implies_sequential_tasks". Abort.
