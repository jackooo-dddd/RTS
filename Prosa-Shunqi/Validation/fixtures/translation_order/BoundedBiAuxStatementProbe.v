Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BoundedBiAuxSemanticSource.
Import BoundedBiAuxSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the imports of the source *)
Require Import prosa.analysis.abstract.definitions prosa.model.aggregate.workload prosa.model.aggregate.service_of_jobs prosa.model.job.properties.
(* display-only: abstract definitions and model/schedule/work_conserving loaded before the classical busy interval, as in the official environment *)
Require Import prosa.analysis.abstract.definitions prosa.model.schedule.work_conserving.
Import BusyIntervalClassicalSemanticSource.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.busy_interval_prefix_exists". Abort.
Print statement_busy_interval_prefix_exists.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.busy_interval_prefix_exists". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.service_lt_workload_in_busy". Abort.
Print statement_service_lt_workload_in_busy.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.service_lt_workload_in_busy". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.workload_exceeds_interval". Abort.
Print statement_workload_exceeds_interval.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.workload_exceeds_interval". Abort.
