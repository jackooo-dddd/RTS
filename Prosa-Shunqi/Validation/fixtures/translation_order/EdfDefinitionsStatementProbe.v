Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.EdfDefinitionsSemanticSource.
Import EdfDefinitionsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.processor.ideal prosa.model.schedule.edf prosa.model.priority.edf.
(* display-only: the official elaborated-type evidence was printed with another
   [processor_state] in scope, so the ideal one is displayed as [ideal.processor_state] *)
Module EdfDefinitionsProbeDisplay. Definition processor_state := tt. End EdfDefinitionsProbeDisplay.
Import EdfDefinitionsProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.facts.edf_definitions.EDF_schedule_implies_respects_policy_at_preemption_point". Abort.
Print statement_EDF_schedule_implies_respects_policy_at_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.edf_definitions.EDF_schedule_implies_respects_policy_at_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.edf_definitions.respects_policy_at_preemption_point_implies_EDF_schedule". Abort.
Print statement_respects_policy_at_preemption_point_implies_EDF_schedule.
Goal True. idtac "END|prosa.analysis.facts.edf_definitions.respects_policy_at_preemption_point_implies_EDF_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.edf_definitions.EDF_schedule_equiv". Abort.
Print statement_EDF_schedule_equiv.
Goal True. idtac "END|prosa.analysis.facts.edf_definitions.EDF_schedule_equiv". Abort.
