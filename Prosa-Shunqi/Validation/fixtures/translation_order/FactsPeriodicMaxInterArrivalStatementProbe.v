Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsPeriodicMaxInterArrivalSemanticSource.
Import FactsPeriodicMaxInterArrivalSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.task.concept prosa.model.task.arrivals.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.max_inter_arrival.max_inter_eq_period". Abort.
Check @max_inter_eq_period.
Goal True. idtac "END|prosa.analysis.facts.periodic.max_inter_arrival.max_inter_eq_period". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.max_inter_arrival.valid_period_is_valid_max_inter_arrival_time". Abort.
Print statement_valid_period_is_valid_max_inter_arrival_time.
Goal True. idtac "END|prosa.analysis.facts.periodic.max_inter_arrival.valid_period_is_valid_max_inter_arrival_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.max_inter_arrival.periodic_model_respects_max_inter_arrival_model". Abort.
Print statement_periodic_model_respects_max_inter_arrival_model.
Goal True. idtac "END|prosa.analysis.facts.periodic.max_inter_arrival.periodic_model_respects_max_inter_arrival_model". Abort.
