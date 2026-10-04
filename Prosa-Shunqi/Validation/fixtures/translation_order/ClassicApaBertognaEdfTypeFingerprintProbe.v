(* Recomputes the authoritative `Check @name` fingerprints for classic/analysis/apa/bertogna_edf_theory.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
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
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_tsk_other_in_ts". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_tsk_other_in_ts.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_tsk_other_in_ts". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_R_other_ge_cost". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_R_other_ge_cost.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_R_other_ge_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_workload_bounds_interference". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_workload_bounds_interference.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_workload_bounds_interference". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_specific_bound_holds". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_specific_bound_holds.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_specific_bound_holds". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_too_much_interference". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_too_much_interference.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_too_much_interference". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_interference_by_different_tasks". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_interference_by_different_tasks.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_interference_by_different_tasks". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_all_previous_jobs_complete_by_their_period". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_all_previous_jobs_complete_by_their_period.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_all_previous_jobs_complete_by_their_period". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_all_cpus_in_affinity_busy". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_all_cpus_in_affinity_busy.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_all_cpus_in_affinity_busy". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_all_cpus_in_subaffinity_busy". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_all_cpus_in_subaffinity_busy.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_all_cpus_in_subaffinity_busy". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_alpha'_is_full". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_alpha'_is_full.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_alpha'_is_full". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_interference_in_non_full_processors". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_interference_in_non_full_processors.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_interference_in_non_full_processors". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_minimum_exceeds_interference". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_minimum_exceeds_interference.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_minimum_exceeds_interference". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_interference_on_subaffinity". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_interference_on_subaffinity.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_interference_on_subaffinity". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_sum_exceeds_total_interference". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_sum_exceeds_total_interference.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_sum_exceeds_total_interference". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_exists_task_that_exceeds_bound". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_exists_task_that_exceeds_bound.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_edf_exists_task_that_exceeds_bound". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_cirinei_response_time_bound_edf". Abort.
Check @prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_cirinei_response_time_bound_edf.
Goal True. idtac "END|prosa.classic.analysis.apa.bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_cirinei_response_time_bound_edf". Abort.
