Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsBlockingBoundElfSemanticSource.
Import FactsBlockingBoundElfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the imports of the source (ELF/GEL instances, Int notations and the qualified ELF blocking bound) *)
Require Import prosa.util.int prosa.model.priority.gel prosa.model.priority.elf prosa.model.task.arrival.curves.
Goal True. idtac "BEGIN|prosa.analysis.facts.blocking_bound.elf.nonpreemptive_segments_bounded_by_blocking". Abort.
Print statement_nonpreemptive_segments_bounded_by_blocking.
Goal True. idtac "END|prosa.analysis.facts.blocking_bound.elf.nonpreemptive_segments_bounded_by_blocking". Abort.
