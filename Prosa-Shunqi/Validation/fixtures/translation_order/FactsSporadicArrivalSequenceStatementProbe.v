Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsSporadicArrivalSequenceSemanticSource.
Import FactsSporadicArrivalSequenceSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.model.task.arrivals prosa.model.task.arrival.sporadic.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.size_task_arrivals_at_leq_one". Abort.
Print statement_size_task_arrivals_at_leq_one.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.size_task_arrivals_at_leq_one". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.only_j_in_task_arrivals_at_j". Abort.
Print statement_only_j_in_task_arrivals_at_j.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.only_j_in_task_arrivals_at_j". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.only_j_at_job_arrival_j". Abort.
Print statement_only_j_at_job_arrival_j.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.only_j_at_job_arrival_j". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.index_j_in_task_arrivals_at". Abort.
Print statement_index_j_in_task_arrivals_at.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.index_j_in_task_arrivals_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.prev_job_arr_lt". Abort.
Print statement_prev_job_arr_lt.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.prev_job_arr_lt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.task_arrivals_at_as_task_arrivals_between". Abort.
Print statement_task_arrivals_at_as_task_arrivals_between.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.task_arrivals_at_as_task_arrivals_between". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.prev_job_cat". Abort.
Print statement_prev_job_cat.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.prev_job_cat". Abort.
