Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BoundedBiEdfSemanticSource.
Import BoundedBiEdfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the imports of the source *)
Require Import prosa.analysis.abstract.definitions prosa.model.aggregate.workload prosa.model.job.properties prosa.analysis.definitions.sbf.pred.
(* display-only: the official environment shows the classical busy-interval prefix unqualified *)
Import prosa.BusyIntervalClassicalSemanticSource.BusyIntervalClassicalSemanticSource.
(* display-only: the official environment shows the abstract work conservation module-qualified *)
Module BoundedBiEdfWcProbeDisplay. Definition work_conserving := tt. End BoundedBiEdfWcProbeDisplay.
Import BoundedBiEdfWcProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.edf.longest_bi_with_pi_bound_is_valid". Abort.
Print statement_longest_bi_with_pi_bound_is_valid.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.edf.longest_bi_with_pi_bound_is_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.edf.busy_intervals_are_bounded_rs_edf". Abort.
Print statement_busy_intervals_are_bounded_rs_edf.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.edf.busy_intervals_are_bounded_rs_edf". Abort.
