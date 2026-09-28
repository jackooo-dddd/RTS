Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.GeneralityElfSemanticSource.
Import GeneralityElfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the imports of the source (ELF/GEL instances and Int notations) *)
Require Import prosa.util.int prosa.model.priority.gel prosa.model.priority.elf.
Goal True. idtac "BEGIN|prosa.results.generality.elf.elf_generalizes_gel". Abort.
Print statement_elf_generalizes_gel.
Goal True. idtac "END|prosa.results.generality.elf.elf_generalizes_gel". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.elf.elf_is_fixed_priority". Abort.
Print statement_elf_is_fixed_priority.
Goal True. idtac "END|prosa.results.generality.elf.elf_is_fixed_priority". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.elf.elf_generalizes_fixed_priority". Abort.
Print statement_elf_generalizes_fixed_priority.
Goal True. idtac "END|prosa.results.generality.elf.elf_generalizes_fixed_priority". Abort.
