Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.IdealCumulativeBoundsSemanticSource.
Import IdealCumulativeBoundsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module IdealCumulativeBoundsProbeDisplay. Definition processor_state := tt. End IdealCumulativeBoundsProbeDisplay.
Import IdealCumulativeBoundsProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_priority_inversion_is_bounded". Abort.
Print statement_cumulative_priority_inversion_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_priority_inversion_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_interference_is_bounded_by_total_service". Abort.
Print statement_cumulative_interference_is_bounded_by_total_service.
Goal True. idtac "END|prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_interference_is_bounded_by_total_service". Abort.
