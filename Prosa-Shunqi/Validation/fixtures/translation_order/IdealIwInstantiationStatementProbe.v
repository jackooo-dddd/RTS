Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.IdealIwInstantiationSemanticSource.
Import IdealIwInstantiationSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module IdealIwProbeDisplay. Definition processor_state := tt. End IdealIwProbeDisplay.
Import IdealIwProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.no_interference_when_idle". Abort.
Print statement_no_interference_when_idle.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.no_interference_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.no_task_interference_when_idle". Abort.
Print statement_no_task_interference_when_idle.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.no_task_interference_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.task_interference_eq_false". Abort.
Print statement_task_interference_eq_false.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.task_interference_eq_false". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.sched_athep_implies_task_interference". Abort.
Print statement_sched_athep_implies_task_interference.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.sched_athep_implies_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interference_split". Abort.
Print statement_cumulative_interference_split.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interfering_workload_split". Abort.
Print statement_cumulative_interfering_workload_split.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interfering_workload_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_task_interference_split". Abort.
Print statement_cumulative_task_interference_split.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_task_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_iw_hep_eq_workload_of_ohep". Abort.
Print statement_cumulative_iw_hep_eq_workload_of_ohep.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_iw_hep_eq_workload_of_ohep". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_cl_implies_quiet_time_ab". Abort.
Print statement_quiet_time_cl_implies_quiet_time_ab.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_cl_implies_quiet_time_ab". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_ab_implies_quiet_time_cl". Abort.
Print statement_quiet_time_ab_implies_quiet_time_cl.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_ab_implies_quiet_time_cl". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_quiet_time_equivalent_quiet_time". Abort.
Print statement_instantiated_quiet_time_equivalent_quiet_time.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_quiet_time_equivalent_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix". Abort.
Print statement_instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_interval_equivalent_busy_interval". Abort.
Print statement_instantiated_busy_interval_equivalent_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_interval_equivalent_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.abstract_busy_interval_classic_quiet_time". Abort.
Print statement_abstract_busy_interval_classic_quiet_time.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.abstract_busy_interval_classic_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.abstract_busy_interval_classic_busy_interval_prefix". Abort.
Print statement_abstract_busy_interval_classic_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.abstract_busy_interval_classic_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.not_interference_implies_scheduled". Abort.
Print statement_not_interference_implies_scheduled.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.not_interference_implies_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.scheduled_implies_no_interference". Abort.
Print statement_scheduled_implies_no_interference.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.scheduled_implies_no_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_i_and_w_are_coherent_with_schedule". Abort.
Print statement_instantiated_i_and_w_are_coherent_with_schedule.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_i_and_w_are_coherent_with_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks". Abort.
Print statement_instantiated_interference_and_workload_consistent_with_sequential_tasks.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_intervals_are_bounded". Abort.
Print statement_instantiated_busy_intervals_are_bounded.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_intervals_are_bounded". Abort.
