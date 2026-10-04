(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/sustainability.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.schedulability.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.sustainability.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.parameter_label". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.parameter_label.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.parameter_label". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.eqlabelP". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.eqlabelP.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.eqlabelP". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.type_of_label". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.type_of_label.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.type_of_label". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.default_val". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.default_val.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.default_val". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.job_parameter". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.job_parameter.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.job_parameter". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.find_param". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.find_param.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.find_param". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.get_param_function". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.get_param_function.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.get_param_function". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.return_param". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.return_param.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.return_param". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.return_param_works1". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.return_param_works1.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.return_param_works1". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.return_param_works2". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.return_param_works2.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.return_param_works2". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.differ_only_by". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.differ_only_by.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.differ_only_by". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.labels_of". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.labels_of.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.labels_of". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.has_unique_labels". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.has_unique_labels.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.has_unique_labels". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.corresponding_labels". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.corresponding_labels.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.corresponding_labels". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.found_param_label". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.found_param_label.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.found_param_label". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.sustainable_param_becomes_better". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.sustainable_param_becomes_better.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.sustainable_param_becomes_better". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.sustainable_and_varying_params_in". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.sustainable_and_varying_params_in.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.sustainable_and_varying_params_in". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.has_consistent_labels". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.has_consistent_labels.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.has_consistent_labels". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.jobs_are_schedulable_with". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.jobs_are_schedulable_with.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.jobs_are_schedulable_with". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.jobs_are_V_schedulable_with". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.jobs_are_V_schedulable_with.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.jobs_are_V_schedulable_with". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.weakly_sustainable". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.weakly_sustainable.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.weakly_sustainable". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.sustainable_param_becomes_worse". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.sustainable_param_becomes_worse.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.sustainable_param_becomes_worse". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.jobs_are_not_schedulable_with". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.jobs_are_not_schedulable_with.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.jobs_are_not_schedulable_with". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.weakly_sustainable_contrapositive". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.weakly_sustainable_contrapositive.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.weakly_sustainable_contrapositive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.weak_sustainability_equivalence". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.weak_sustainability_equivalence.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.weak_sustainability_equivalence". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.sustainability.Sustainability.strongly_sustainable". Abort.
Check @prosa.classic.model.schedule.uni.sustainability.Sustainability.strongly_sustainable.
Goal True. idtac "END|prosa.classic.model.schedule.uni.sustainability.Sustainability.strongly_sustainable". Abort.
