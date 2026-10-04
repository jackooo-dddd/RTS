(* Recomputes the authoritative `Check @name` fingerprints for classic/analysis/uni/susp/sustainability/singlecost/reduction_properties.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction.
Require Import prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.susp.last_execution.
Require Import prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.model.schedule.uni.susp.schedule.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
Require Import prosa.classic.model.suspension.
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
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_depends_only_on_prefix". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_depends_only_on_prefix.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_depends_only_on_prefix". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_uses_construction_function". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_uses_construction_function.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_uses_construction_function". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_jobs_come_from_arrival_sequence". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_jobs_must_arrive_to_execute". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_jobs_must_arrive_to_execute.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_jobs_must_arrive_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_completed_jobs_dont_execute". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_completed_jobs_dont_execute.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_work_conserving". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_work_conserving.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_respects_policy". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_respects_policy.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_respects_policy". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_respects_self_suspensions". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_respects_self_suspensions.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_respects_self_suspensions". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_completion". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_completion.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_completion". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_time_after_last_exec". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_time_after_last_exec.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_time_after_last_exec". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_suspension_duration". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_suspension_duration.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_suspension_duration". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_suspension". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_suspension.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_suspension". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_schedule". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_schedule.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_schedule". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.scheduled_in_susp_iff_scheduled_in_wcet". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.scheduled_in_susp_iff_scheduled_in_wcet.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.scheduled_in_susp_iff_scheduled_in_wcet". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_service_for_j". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_service_for_j.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_same_service_for_j". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_r_le_R". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_r_le_R.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_r_le_R". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.R_bounds_inflated_cost". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.R_bounds_inflated_cost.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.R_bounds_inflated_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_incurs_more_interference". Abort.
Check @prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_incurs_more_interference.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.SustainabilitySingleCostProperties.sched_susp_highercost_incurs_more_interference". Abort.
