(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/apa/platform.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.apa.affinity.
Require Import prosa.classic.model.schedule.apa.interference.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.apa.platform.Platform.apa_work_conserving". Abort.
Check @prosa.classic.model.schedule.apa.platform.Platform.apa_work_conserving.
Goal True. idtac "END|prosa.classic.model.schedule.apa.platform.Platform.apa_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.apa.platform.Platform.respects_affinity". Abort.
Check @prosa.classic.model.schedule.apa.platform.Platform.respects_affinity.
Goal True. idtac "END|prosa.classic.model.schedule.apa.platform.Platform.respects_affinity". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.apa.platform.Platform.respects_FP_policy_under_weak_APA". Abort.
Check @prosa.classic.model.schedule.apa.platform.Platform.respects_FP_policy_under_weak_APA.
Goal True. idtac "END|prosa.classic.model.schedule.apa.platform.Platform.respects_FP_policy_under_weak_APA". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.apa.platform.Platform.respects_JLFP_policy_under_weak_APA". Abort.
Check @prosa.classic.model.schedule.apa.platform.Platform.respects_JLFP_policy_under_weak_APA.
Goal True. idtac "END|prosa.classic.model.schedule.apa.platform.Platform.respects_JLFP_policy_under_weak_APA". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.apa.platform.Platform.respects_JLDP_policy_under_weak_APA". Abort.
Check @prosa.classic.model.schedule.apa.platform.Platform.respects_JLDP_policy_under_weak_APA.
Goal True. idtac "END|prosa.classic.model.schedule.apa.platform.Platform.respects_JLDP_policy_under_weak_APA". Abort.
