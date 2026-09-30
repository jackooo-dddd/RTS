Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.OptimalityEdfSemanticSource.
Import OptimalityEdfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal prosa.model.schedule.edf prosa.model.priority.edf prosa.model.schedule.work_conserving.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module OptimalityEdfProbeDisplay. Definition processor_state := tt. End OptimalityEdfProbeDisplay.
Import OptimalityEdfProbeDisplay.
Goal True. idtac "BEGIN|prosa.results.optimality.edf.EDF_optimality". Abort.
Print statement_EDF_optimality.
Goal True. idtac "END|prosa.results.optimality.edf.EDF_optimality". Abort.
Goal True. idtac "BEGIN|prosa.results.optimality.edf.EDF_WC_optimality". Abort.
Print statement_EDF_WC_optimality.
Goal True. idtac "END|prosa.results.optimality.edf.EDF_WC_optimality". Abort.
Goal True. idtac "BEGIN|prosa.results.optimality.edf.EDF_priority_compliant_WC_optimality". Abort.
Print statement_EDF_priority_compliant_WC_optimality.
Goal True. idtac "END|prosa.results.optimality.edf.EDF_priority_compliant_WC_optimality". Abort.
Goal True. idtac "BEGIN|prosa.results.optimality.edf.weak_EDF_optimality". Abort.
Print statement_weak_EDF_optimality.
Goal True. idtac "END|prosa.results.optimality.edf.weak_EDF_optimality". Abort.
