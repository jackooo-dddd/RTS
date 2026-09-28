Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BlockingBoundElfSemanticSource.
Import BlockingBoundElfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
(* display-only: the imports of the source *)
Require Import prosa.model.priority.gel prosa.model.priority.elf prosa.model.task.arrival.curves.
Goal True. idtac "BEGIN|prosa.analysis.definitions.blocking_bound.elf.blocking_bound". Abort.
Check @blocking_bound.
Goal True. idtac "END|prosa.analysis.definitions.blocking_bound.elf.blocking_bound". Abort.
