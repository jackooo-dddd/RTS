Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaPrmFpFullyNonpreemptiveSemanticSource.
Import RtaPrmFpFullyNonpreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.analysis.definitions.sbf.pred.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp". Abort.
Print statement_uniprocessor_response_time_bound_fully_non_preemptive_fp.
Goal True. idtac "END|prosa.results.rta.prm.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp". Abort.
