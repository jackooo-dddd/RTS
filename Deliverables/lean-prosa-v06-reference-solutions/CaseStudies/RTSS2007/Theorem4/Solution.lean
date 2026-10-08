import CaseStudies.RTSS2007.Theorem4.Statement
import CaseStudies.Support.Common
import Prosa.Classic.Analysis.Global.Basic.WorkloadBound

/-! Reference solution of benchmark task `2007-RTSS-Theorem4`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.RTSS2007.Theorem4.WorkloadBound

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Util.DivMod (div_floor)

theorem Theorem4_07 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (job_deadline : Job → time)
    (arr_seq : arrival_sequence Job)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (H_constrained_deadline : task_deadline tsk ≤ task_period tsk)
    (H_no_deadline_miss :
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk)
    (t1 delta : time) :
    workload job_task sched tsk t1 (t1 + delta) ≤
      W task_cost task_period task_deadline tsk delta := by
  -- the case study's `W` is the classic `WorkloadBound.W` with the response-time bound `d_tsk`
  have hW : W task_cost task_period task_deadline tsk delta =
      Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.W task_cost task_period tsk
        (task_deadline tsk) delta := rfl
  have hvalid := H_valid_task_parameters tsk task_in_ts
  rw [hW]
  refine Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bounded_by_W
    task_cost task_period task_deadline job_arrival job_cost job_task job_deadline arr_seq
    H_valid_job_parameters sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks tsk hvalid
    H_constrained_deadline t1 delta (task_deadline tsk) ?_ ?_ (Nat.le_refl _)
  · intro j hj htsk _
    have h := H_no_deadline_miss j hj htsk
    have hd : job_deadline j = task_deadline tsk := by
      rw [← htsk]; exact (H_valid_job_parameters j hj).2.2
    simpa [job_misses_no_deadline, hd] using h
  · simpa [task_cost_le_deadline] using hvalid.2.2.2.1

end CaseStudies.RTSS2007.Theorem4.WorkloadBound

theorem CaseStudies.RTSS2007.Theorem4.solution : CaseStudies.RTSS2007.Theorem4.WorkloadBound.Theorem4_07_statement.{u, v} :=
  @CaseStudies.RTSS2007.Theorem4.WorkloadBound.Theorem4_07
