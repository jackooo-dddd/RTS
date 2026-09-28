Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsElfAthepBoundSemanticSource.
Import FactsElfAthepBoundSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.aggregate.workload prosa.model.job.properties.
(* display-only: the imports of the source (ELF/GEL instances and Int notations) *)
Require Import prosa.util.int prosa.model.priority.gel prosa.model.priority.elf prosa.model.task.absolute_deadline.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.total_ep_tsk_workload_shorten_range". Abort.
Print statement_total_ep_tsk_workload_shorten_range.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.total_ep_tsk_workload_shorten_range". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload". Abort.
Print statement_sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload". Abort.
Print statement_sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.sum_of_hep_workloads_partitioned". Abort.
Print statement_sum_of_hep_workloads_partitioned.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.sum_of_hep_workloads_partitioned". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload". Abort.
Print statement_sum_of_workloads_is_at_most_bound_on_total_hep_workload.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.bound_on_athep_workload_is_valid". Abort.
Print statement_bound_on_athep_workload_is_valid.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.bound_on_athep_workload_is_valid". Abort.
