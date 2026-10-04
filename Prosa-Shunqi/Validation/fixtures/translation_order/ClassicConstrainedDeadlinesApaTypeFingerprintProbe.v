(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/apa/constrained_deadlines.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.apa.affinity.
Require Import prosa.classic.model.schedule.apa.constrained_deadlines.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.platform_at_most_one_pending_job_of_each_task". Abort.
Check @prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.platform_at_most_one_pending_job_of_each_task.
Goal True. idtac "END|prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.platform_at_most_one_pending_job_of_each_task". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.scheduled_task_with_higher_eq_priority". Abort.
Check @prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.scheduled_task_with_higher_eq_priority.
Goal True. idtac "END|prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.scheduled_task_with_higher_eq_priority". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_interfering_tasks". Abort.
Check @prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_interfering_tasks.
Goal True. idtac "END|prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_interfering_tasks". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_tsk". Abort.
Check @prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_tsk.
Goal True. idtac "END|prosa.classic.model.schedule.apa.constrained_deadlines.ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_tsk". Abort.
