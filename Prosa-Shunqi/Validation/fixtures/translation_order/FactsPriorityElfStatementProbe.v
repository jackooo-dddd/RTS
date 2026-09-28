Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsPriorityElfSemanticSource.
Import FactsPriorityElfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the imports of the source (ELF/GEL instances and Int notations) *)
Require Import prosa.util.int prosa.model.priority.gel prosa.model.priority.elf prosa.analysis.definitions.priority.classes.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.hep_job_elf_gel". Abort.
Print statement_hep_job_elf_gel.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.hep_job_elf_gel". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.hep_job_arrival_elf". Abort.
Print statement_hep_job_arrival_elf.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.hep_job_arrival_elf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_is_reflexive". Abort.
Print statement_ELF_is_reflexive.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_is_transitive". Abort.
Print statement_ELF_is_transitive.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_is_total". Abort.
Print statement_ELF_is_total.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_is_total". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_is_JLFP_FP_compatible". Abort.
Print statement_ELF_is_JLFP_FP_compatible.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_is_JLFP_FP_compatible". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_respects_sequential_tasks". Abort.
Print statement_ELF_respects_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_respects_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_implies_sequential_tasks". Abort.
Print statement_ELF_implies_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_implies_sequential_tasks". Abort.
