Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.ElfAthepBoundSemanticSource.
Import ElfAthepBoundSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
(* display-only: the imports of the source (ELF/GEL and Int notations) *)
Require Import prosa.util.int prosa.model.priority.gel prosa.model.priority.elf.
Goal True. idtac "BEGIN|prosa.analysis.definitions.workload.elf_athep_bound.ep_task_interfering_interval_length". Abort.
Check @ep_task_interfering_interval_length.
Goal True. idtac "END|prosa.analysis.definitions.workload.elf_athep_bound.ep_task_interfering_interval_length". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_ep_task_workload". Abort.
Check @bound_on_ep_task_workload.
Goal True. idtac "END|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_ep_task_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_hp_task_workload". Abort.
Check @bound_on_hp_task_workload.
Goal True. idtac "END|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_hp_task_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_athep_workload". Abort.
Check @bound_on_athep_workload.
Goal True. idtac "END|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_athep_workload". Abort.
