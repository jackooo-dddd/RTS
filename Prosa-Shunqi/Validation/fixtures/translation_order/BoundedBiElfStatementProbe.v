Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BoundedBiElfSemanticSource.
Import BoundedBiElfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the imports of the source *)
Require Import prosa.analysis.abstract.definitions prosa.model.aggregate.workload prosa.model.job.properties prosa.analysis.definitions.sbf.pred.
(* display-only: the official environment shows the ELF blocking bound module-qualified *)
Module BoundedBiElfProbeDisplay. Definition blocking_bound := tt. End BoundedBiElfProbeDisplay.
Import BoundedBiElfProbeDisplay.
(* display-only: the official environment shows the abstract work conservation module-qualified *)
Module BoundedBiElfWcProbeDisplay. Definition work_conserving := tt. End BoundedBiElfWcProbeDisplay.
Import BoundedBiElfWcProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.elf.busy_intervals_are_bounded_rs_elf". Abort.
Print statement_busy_intervals_are_bounded_rs_elf.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.elf.busy_intervals_are_bounded_rs_elf". Abort.
