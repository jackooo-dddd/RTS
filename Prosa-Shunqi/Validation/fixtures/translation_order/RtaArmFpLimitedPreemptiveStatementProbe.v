Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaArmFpLimitedPreemptiveSemanticSource.
Import RtaArmFpLimitedPreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.analysis.definitions.sbf.pred.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.limited_preemptive.busy_window_recurrence_solution". Abort.
Check @busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fp.limited_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.limited_preemptive.rta_recurrence_solution". Abort.
Check @rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fp.limited_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp". Abort.
Print statement_uniprocessor_response_time_bound_limited_fp.
Goal True. idtac "END|prosa.results.rta.arm.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp". Abort.
