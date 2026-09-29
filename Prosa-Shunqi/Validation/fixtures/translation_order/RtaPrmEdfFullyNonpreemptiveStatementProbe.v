Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaPrmEdfFullyNonpreemptiveSemanticSource.
Import RtaPrmEdfFullyNonpreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.analysis.definitions.sbf.pred.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.edf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.edf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
Print statement_uniprocessor_response_time_bound_fully_nonpreemptive_edf.
Goal True. idtac "END|prosa.results.rta.prm.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
