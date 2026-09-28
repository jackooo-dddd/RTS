Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BoundedBiJlfpSemanticSource.
Import BoundedBiJlfpSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the imports of the source *)
Require Import prosa.analysis.abstract.definitions prosa.model.aggregate.workload prosa.model.job.properties prosa.analysis.definitions.sbf.pred.
(* display-only: the official environment shows the abstract work conservation module-qualified *)
Module BoundedBiJlfpWcProbeDisplay. Definition work_conserving := tt. End BoundedBiJlfpWcProbeDisplay.
Import BoundedBiJlfpWcProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp.busy_intervals_are_bounded_rs_jlfp". Abort.
Print statement_busy_intervals_are_bounded_rs_jlfp.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp.busy_intervals_are_bounded_rs_jlfp". Abort.
