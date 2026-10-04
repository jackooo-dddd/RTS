(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/susp/build_suspension_table.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.susp.build_suspension_table.
Require Import prosa.classic.model.schedule.uni.susp.last_execution.
Require Import prosa.classic.model.schedule.uni.susp.schedule.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.build_suspension_duration". Abort.
Check @prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.build_suspension_duration.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.build_suspension_duration". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.not_suspended_before_suspension_start". Abort.
Check @prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.not_suspended_before_suspension_start.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.not_suspended_before_suspension_start". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.suspension_duration_no_suspension_after_t_max". Abort.
Check @prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.suspension_duration_no_suspension_after_t_max.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.suspension_duration_no_suspension_after_t_max". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.suspension_duration_matches_predicate_up_to_t_max". Abort.
Check @prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.suspension_duration_matches_predicate_up_to_t_max.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.build_suspension_table.SuspensionTableConstruction.suspension_duration_matches_predicate_up_to_t_max". Abort.
