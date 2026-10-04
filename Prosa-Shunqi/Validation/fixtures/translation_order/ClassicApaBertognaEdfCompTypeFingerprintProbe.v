(* Recomputes the authoritative `Check @name` fingerprints for classic/analysis/apa/bertogna_edf_comp.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.apa.bertogna_edf_comp.
Require Import prosa.classic.analysis.apa.bertogna_edf_theory.
Require Import prosa.classic.analysis.apa.interference_bound.
Require Import prosa.classic.analysis.apa.interference_bound_edf.
Require Import prosa.classic.analysis.apa.workload_bound.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.apa.affinity.
Require Import prosa.classic.model.schedule.apa.constrained_deadlines.
Require Import prosa.classic.model.schedule.apa.interference.
Require Import prosa.classic.model.schedule.apa.interference_edf.
Require Import prosa.classic.model.schedule.apa.platform.
Require Import prosa.classic.model.schedule.global.basic.schedule.
Require Import prosa.classic.model.schedule.global.response_time.
Require Import prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.workload.
Require Import prosa.classic.model.time.
Require Import prosa.classic.util.all.
Require Import prosa.classic.util.bigcat.
Require Import prosa.classic.util.bigord.
Require Import prosa.classic.util.counting.
Require Import prosa.classic.util.div_mod.
Require Import prosa.classic.util.fixedpoint.
Require Import prosa.classic.util.induction.
Require Import prosa.classic.util.list.
Require Import prosa.classic.util.minmax.
Require Import prosa.classic.util.nat.
Require Import prosa.classic.util.notation.
Require Import prosa.classic.util.ord_quantifier.
Require Import prosa.classic.util.pick.
Require Import prosa.classic.util.powerset.
Require Import prosa.classic.util.seqset.
Require Import prosa.classic.util.sorting.
Require Import prosa.classic.util.ssromega.
Require Import prosa.classic.util.step_function.
Require Import prosa.classic.util.sum.
Require Import prosa.classic.util.tactics.
Require Import prosa.util.bigcat.
Require Import prosa.util.div_mod.
Require Import prosa.util.epsilon.
Require Import prosa.util.list.
Require Import prosa.util.minmax.
Require Import prosa.util.nat.
Require Import prosa.util.notation.
Require Import prosa.util.rel.
Require Import prosa.util.seqset.
Require Import prosa.util.setoid.
Require Import prosa.util.subadditivity.
Require Import prosa.util.sum.
Require Import prosa.util.supremum.
Require Import prosa.util.tactics.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div path.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_response_time_bound". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_response_time_bound.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.R_le_deadline". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.R_le_deadline.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.R_le_deadline". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.update_bound". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.update_bound.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.update_bound". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_rta_iteration". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_rta_iteration.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_rta_iteration". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_schedulable". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_schedulable.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_schedulable". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_unzip1_update_bound". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_unzip1_update_bound.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_unzip1_update_bound". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_unzip1_iteration". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_unzip1_iteration.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_unzip1_iteration". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_size". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_size.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_size". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_ge_cost". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_ge_cost.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_ge_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_le_deadline". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_le_deadline.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_le_deadline". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_has_R_for_every_task". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_has_R_for_every_task.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_has_R_for_every_task". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.all_le_reflexive". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.all_le_reflexive.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.all_le_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.all_le_transitive". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.all_le_transitive.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.all_le_transitive". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_preserves_minimum". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_preserves_minimum.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_preserves_minimum". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_inductive". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_inductive.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_inductive". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_preserves_order". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_preserves_order.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_preserves_order". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_monotonic". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_monotonic.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_iteration_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_f_converges_with_no_tasks". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_f_converges_with_no_tasks.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_f_converges_with_no_tasks". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_f_converges_early". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_f_converges_early.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_f_converges_early". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_f_increases". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_f_increases.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_f_increases". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_rt_grows_too_much". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_rt_grows_too_much.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.bertogna_edf_comp_rt_grows_too_much". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_finds_fixed_point_of_list". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_finds_fixed_point_of_list.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_finds_fixed_point_of_list". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_finds_least_fixed_point". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_finds_least_fixed_point.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_finds_least_fixed_point". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_finds_fixed_point_for_each_bound". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_finds_fixed_point_for_each_bound.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds_finds_fixed_point_for_each_bound". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.no_deadline_missed_by_task". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.no_deadline_missed_by_task.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.no_deadline_missed_by_task". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.no_deadline_missed_by_job". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.no_deadline_missed_by_job.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.no_deadline_missed_by_job". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_analysis_yields_response_time_bounds". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_analysis_yields_response_time_bounds.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.edf_analysis_yields_response_time_bounds". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.taskset_schedulable_by_edf_rta". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.taskset_schedulable_by_edf_rta.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.taskset_schedulable_by_edf_rta". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.jobs_schedulable_by_edf_rta". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.jobs_schedulable_by_edf_rta.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_comp.ResponseTimeIterationEDF.jobs_schedulable_by_edf_rta". Abort.
