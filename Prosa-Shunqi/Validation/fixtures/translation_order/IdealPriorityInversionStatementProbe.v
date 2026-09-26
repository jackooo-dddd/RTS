Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.IdealPriorityInversionSemanticSource.
Import IdealPriorityInversionSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.processor.ideal prosa.model.schedule.scheduled.
(* display-only: the official elaborated-type evidence was printed with another
   [processor_state] in scope, so the ideal one is displayed as [ideal.processor_state] *)
Module IdealPriorityInversionProbeDisplay. Definition processor_state := tt. End IdealPriorityInversionProbeDisplay.
Import IdealPriorityInversionProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.priority_inversion.idle_implies_no_priority_inversion". Abort.
Print statement_idle_implies_no_priority_inversion.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.priority_inversion.idle_implies_no_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.priority_inversion.priority_inversion_equiv_sched_lower_priority". Abort.
Print statement_priority_inversion_equiv_sched_lower_priority.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.priority_inversion.priority_inversion_equiv_sched_lower_priority". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.priority_inversion.sched_hep_implies_no_priority_inversion". Abort.
Print statement_sched_hep_implies_no_priority_inversion.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.priority_inversion.sched_hep_implies_no_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.priority_inversion.sched_lp_implies_priority_inversion". Abort.
Print statement_sched_lp_implies_priority_inversion.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.priority_inversion.sched_lp_implies_priority_inversion". Abort.
