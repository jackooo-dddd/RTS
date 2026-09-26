Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsSporadicArrivalBoundSemanticSource.
Import FactsSporadicArrivalBoundSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
Require Import prosa.util.div_mod.
Require Import prosa.model.task.arrivals.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_bound.max_sporadic_arrivals". Abort.
Check @max_sporadic_arrivals.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_bound.max_sporadic_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_bound.arrival_of_nth_job". Abort.
Print statement_arrival_of_nth_job.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_bound.arrival_of_nth_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_bound.minimum_distance_for_n_sporadic_arrivals". Abort.
Print statement_minimum_distance_for_n_sporadic_arrivals.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_bound.minimum_distance_for_n_sporadic_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_bound.sporadic_task_arrivals_bound". Abort.
Print statement_sporadic_task_arrivals_bound.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_bound.sporadic_task_arrivals_bound". Abort.
