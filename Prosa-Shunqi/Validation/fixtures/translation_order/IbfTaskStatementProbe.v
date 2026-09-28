Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.IbfTaskSemanticSource.
Import IbfTaskSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.analysis.definitions.task_schedule prosa.model.task.sequentiality prosa.model.aggregate.service_of_jobs prosa.model.aggregate.workload prosa.model.task.arrival.curves prosa.analysis.abstract.definitions.
(* display-only: the official elaborated-type evidence was printed with the classical
   busy-interval notions in scope, so the abstract ones are displayed qualified as
   [definitions.busy_interval] and [definitions.work_conserving] *)
Module IbfTaskProbeDisplay.
  Definition busy_interval := tt. Definition work_conserving := tt.
End IbfTaskProbeDisplay.
Import IbfTaskProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.nonself". Abort.
Check @nonself.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.nonself". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.task_interference". Abort.
Check @task_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.cumul_task_interference". Abort.
Check @cumul_task_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.cumul_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.task_interference_is_bounded_by". Abort.
Check @task_interference_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.task_interference_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_and_workload_consistent_with_sequential_tasks". Abort.
Check @interference_and_workload_consistent_with_sequential_tasks.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_and_workload_consistent_with_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.completed_before_beginning_of_busy_interval". Abort.
Print statement_completed_before_beginning_of_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.completed_before_beginning_of_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.arrives_after_beginning_of_busy_interval". Abort.
Print statement_arrives_after_beginning_of_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.arrives_after_beginning_of_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_idle". Abort.
Print statement_interference_plus_sched_le_serv_of_task_plus_task_interference_idle.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_task". Abort.
Print statement_interference_plus_sched_le_serv_of_task_plus_task_interference_task.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_job". Abort.
Print statement_interference_plus_sched_le_serv_of_task_plus_task_interference_job.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_and_service_eq_1". Abort.
Print statement_interference_and_service_eq_1.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_and_service_eq_1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_j". Abort.
Print statement_interference_plus_sched_le_serv_of_task_plus_task_interference_j.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_j". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference". Abort.
Print statement_interference_plus_sched_le_serv_of_task_plus_task_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference". Abort.
Print statement_cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.serv_of_task_le_workload_of_task_plus". Abort.
Print statement_serv_of_task_le_workload_of_task_plus.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.serv_of_task_le_workload_of_task_plus". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.cumulative_job_interference_le_task_interference_bound". Abort.
Print statement_cumulative_job_interference_le_task_interference_bound.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.cumulative_job_interference_le_task_interference_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.cumulative_job_interference_bound". Abort.
Print statement_cumulative_job_interference_bound.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.cumulative_job_interference_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.task_IBF_implies_job_IBF". Abort.
Print statement_task_IBF_implies_job_IBF.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.task_IBF_implies_job_IBF". Abort.
