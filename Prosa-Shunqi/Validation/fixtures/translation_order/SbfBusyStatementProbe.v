Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.SbfBusySemanticSource.
Import SbfBusySemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.task.concept.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.busy.sbf_respected_in_busy_interval". Abort.
Check @sbf_respected_in_busy_interval.
Goal True. idtac "END|prosa.analysis.definitions.sbf.busy.sbf_respected_in_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.busy.valid_busy_sbf". Abort.
Check @valid_busy_sbf.
Goal True. idtac "END|prosa.analysis.definitions.sbf.busy.valid_busy_sbf". Abort.
