Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsEdfWcSemanticSource.
Import FactsEdfWcSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal prosa.model.schedule.edf prosa.model.schedule.work_conserving.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] and the wc_trans
   [find_swap_candidate] / [relevant_pstate] in scope, so these are displayed qualified *)
Module FactsEdfWcProbeDisplay. Definition processor_state := tt. Definition find_swap_candidate := tt. Definition relevant_pstate := tt. End FactsEdfWcProbeDisplay.
Import FactsEdfWcProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t1". Abort.
Print statement_non_idle_swap_maintains_work_conservation_t1.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t2". Abort.
Print statement_non_idle_swap_maintains_work_conservation_t2.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_LEQ_t1". Abort.
Print statement_non_idle_swap_maintains_work_conservation_LEQ_t1.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_LEQ_t1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_GT_t2". Abort.
Print statement_non_idle_swap_maintains_work_conservation_GT_t2.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_GT_t2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_BET_t1_t2". Abort.
Print statement_non_idle_swap_maintains_work_conservation_BET_t1_t2.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_BET_t1_t2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.fsc_swap_maintains_work_conservation". Abort.
Print statement_fsc_swap_maintains_work_conservation.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.fsc_swap_maintains_work_conservation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.mea_maintains_work_conservation". Abort.
Print statement_mea_maintains_work_conservation.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.mea_maintains_work_conservation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.scheduled_behavior_premises". Abort.
Check @scheduled_behavior_premises.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.scheduled_behavior_premises". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.edf_transform_prefix_maintains_work_conservation". Abort.
Print statement_edf_transform_prefix_maintains_work_conservation.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.edf_transform_prefix_maintains_work_conservation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.sched_satisfies_behavior_premises". Abort.
Print statement_sched_satisfies_behavior_premises.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.sched_satisfies_behavior_premises". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.edf_transform_maintains_work_conservation". Abort.
Print statement_edf_transform_maintains_work_conservation.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.edf_transform_maintains_work_conservation". Abort.
