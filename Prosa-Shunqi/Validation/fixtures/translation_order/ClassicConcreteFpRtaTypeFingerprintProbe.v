(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/limited/fixed_priority/nonpr_reg/concrete_models/response_time_bound.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.uni.arrival_curves.workload_bound.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.arrival.curves.bounds.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.basic.platform.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_rta.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.definitions.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.sufficient_condition_for_lock_in_service.
Require Import prosa.classic.model.schedule.uni.limited.busy_interval.
Require Import prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.
Require Import prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.response_time_bound.
Require Import prosa.classic.model.schedule.uni.limited.fixed_priority.response_time_bound.
Require Import prosa.classic.model.schedule.uni.limited.jlfp_instantiation.
Require Import prosa.classic.model.schedule.uni.limited.platform.definitions.
Require Import prosa.classic.model.schedule.uni.limited.platform.limited.
Require Import prosa.classic.model.schedule.uni.limited.platform.nonpreemptive.
Require Import prosa.classic.model.schedule.uni.limited.platform.preemptive.
Require Import prosa.classic.model.schedule.uni.limited.platform.priority_inversion_is_bounded.
Require Import prosa.classic.model.schedule.uni.limited.rbf.
Require Import prosa.classic.model.schedule.uni.limited.schedule.
Require Import prosa.classic.model.schedule.uni.nonpreemptive.schedule.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.schedule_of_task.
Require Import prosa.classic.model.schedule.uni.service.
Require Import prosa.classic.model.schedule.uni.workload.
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
Require Import prosa.util.nondecreasing.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Check @prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fully_preemptive_fp.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fully_nonpreemptive_fp". Abort.
Check @prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fully_nonpreemptive_fp.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fully_nonpreemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fp_with_fixed_preemption_points". Abort.
Check @prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fp_with_fixed_preemption_points.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fp_with_fixed_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions". Abort.
Check @prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.RTAforConcreteModels.uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions". Abort.
