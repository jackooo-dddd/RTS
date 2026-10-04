(* Recomputes the authoritative `Check @name` fingerprints for classic/implementation/uni/basic/schedule_tdma.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.uni.basic.tdma_rta_theory.
Require Import prosa.classic.analysis.uni.basic.tdma_wcrt_analysis.
Require Import prosa.classic.implementation.arrival_sequence.
Require Import prosa.classic.implementation.job.
Require Import prosa.classic.implementation.task.
Require Import prosa.classic.implementation.uni.basic.schedule.
Require Import prosa.classic.implementation.uni.basic.schedule_tdma.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.policy_tdma.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.basic.platform.
Require Import prosa.classic.model.schedule.uni.basic.platform_tdma.
Require Import prosa.classic.model.schedule.uni.end_time.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.schedulability.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.schedule_of_task.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
Require Import prosa.classic.model.time.
Require Import prosa.classic.util.all.
Require Import prosa.classic.util.bigcat.
Require Import prosa.classic.util.bigord.
Require Import prosa.classic.util.counting.
Require Import prosa.classic.util.div_mod.
Require Import prosa.classic.util.find_seq.
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
Goal True. idtac "BEGIN|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pending_jobs". Abort.
Check @prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pending_jobs.
Goal True. idtac "END|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pending_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.job_to_schedule". Abort.
Check @prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.job_to_schedule.
Goal True. idtac "END|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.job_to_schedule". Abort.
Goal True. idtac "BEGIN|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pending_jobs_uniq". Abort.
Check @prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pending_jobs_uniq.
Goal True. idtac "END|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pending_jobs_uniq". Abort.
Goal True. idtac "BEGIN|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.respects_FIFO". Abort.
Check @prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.respects_FIFO.
Goal True. idtac "END|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.respects_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pending_job_in_penging_list". Abort.
Check @prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pending_job_in_penging_list.
Goal True. idtac "END|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pending_job_in_penging_list". Abort.
Goal True. idtac "BEGIN|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pendinglist_jobs_in_arr_seq". Abort.
Check @prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pendinglist_jobs_in_arr_seq.
Goal True. idtac "END|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.pendinglist_jobs_in_arr_seq". Abort.
Goal True. idtac "BEGIN|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_tdma". Abort.
Check @prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_tdma.
Goal True. idtac "END|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_tdma". Abort.
Goal True. idtac "BEGIN|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_depends_only_on_prefix". Abort.
Check @prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_depends_only_on_prefix.
Goal True. idtac "END|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_depends_only_on_prefix". Abort.
Goal True. idtac "BEGIN|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_uses_construction_function". Abort.
Check @prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_uses_construction_function.
Goal True. idtac "END|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_uses_construction_function". Abort.
Goal True. idtac "BEGIN|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_jobs_must_arrive_to_execute". Abort.
Check @prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_jobs_must_arrive_to_execute.
Goal True. idtac "END|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_jobs_must_arrive_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_completed_jobs_dont_execute". Abort.
Check @prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_completed_jobs_dont_execute.
Goal True. idtac "END|prosa.classic.implementation.uni.basic.schedule_tdma.ConcreteSchedulerTDMA.scheduler_completed_jobs_dont_execute". Abort.
