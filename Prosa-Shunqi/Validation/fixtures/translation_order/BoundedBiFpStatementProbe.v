Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BoundedBiFpSemanticSource.
Import BoundedBiFpSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the imports of the source *)
Require Import prosa.analysis.abstract.definitions prosa.model.aggregate.workload prosa.model.job.properties prosa.analysis.definitions.sbf.pred.
(* display-only: the official environment shows the abstract work conservation module-qualified *)
Module BoundedBiFpWcProbeDisplay. Definition work_conserving := tt. End BoundedBiFpWcProbeDisplay.
Import BoundedBiFpWcProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.fp.busy_intervals_are_bounded_rs_fp". Abort.
Print statement_busy_intervals_are_bounded_rs_fp.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.fp.busy_intervals_are_bounded_rs_fp". Abort.
