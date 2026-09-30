Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaIdealFpFullyNonpreemptiveSemanticSource.
Import RtaIdealFpFullyNonpreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module RtaIdealFpFullyNonpreemptiveProbeDisplay. Definition processor_state := tt. End RtaIdealFpFullyNonpreemptiveProbeDisplay.
Import RtaIdealFpFullyNonpreemptiveProbeDisplay.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp". Abort.
Print statement_uniprocessor_response_time_bound_fully_nonpreemptive_fp.
Goal True. idtac "END|prosa.results.rta.ideal.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp". Abort.
