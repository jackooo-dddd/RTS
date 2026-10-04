(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/end_time.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.uni.end_time.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.schedule.
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
Require Import prosa.util.unit_growth.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div path.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.diagnosis_option". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.diagnosis_option.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.diagnosis_option". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.end_time_option". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.end_time_option.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.end_time_option". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicate". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicate.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicate". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.completes_at". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.completes_at.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.completes_at". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.end_time_function_predicat_equivalence". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.end_time_function_predicat_equivalence.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.end_time_function_predicat_equivalence". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicat_function_equivalence". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicat_function_equivalence.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicat_function_equivalence". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicate_not_sched". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicate_not_sched.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicate_not_sched". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicate_sched". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicate_sched.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.end_time_predicate_sched". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.arrival_le_end". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.arrival_le_end.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.arrival_le_end". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.arrival_add_cost_le_end". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.arrival_add_cost_le_end.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.arrival_add_cost_le_end". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.service_eq_cost_at_end_time". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.service_eq_cost_at_end_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.service_eq_cost_at_end_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.completed_by_end_time". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.completed_by_end_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.completed_by_end_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.end_time_positive". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.end_time_positive.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.end_time_positive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.job_uncompletes_at_end_time_sub_1". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.job_uncompletes_at_end_time_sub_1.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.job_uncompletes_at_end_time_sub_1". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.end_time.end_time.job_uncompleted_before_end_time". Abort.
Check @prosa.classic.model.schedule.uni.end_time.end_time.job_uncompleted_before_end_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.end_time.end_time.job_uncompleted_before_end_time". Abort.
