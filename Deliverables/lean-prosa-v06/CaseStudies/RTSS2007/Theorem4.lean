-- Case study 2007-RTSS-Theorem4: Bertogna, Cirinei — Response-Time Analysis for Globally Scheduled Symmetric Multiprocessor Platforms (RTSS 2007).
-- Original Rocq statement: RTS_Papers/2007-RTSS-Theorem4/Theorem4.v.
-- Benchmark file: read-only.  Prove `CaseStudies.RTSS2007.Theorem4.WorkloadBound.Theorem4_07_statement` in `Solutions/RTSS2007/Theorem4.lean`.
import Prosa.Classic.Util.DivMod
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform

/-!
Theorem 4 of RTSS 2007: the workload of a task that misses no deadline in an interval of length
`delta` is bounded by `W` (Rocq module `WorkloadBound`, sections `WorkloadBoundDef` and
`Theorem4_07`). The case study defines its own `max_jobs` and `W`, with the task deadline in place
of a response-time bound.

Representation notes: `minn` is `min`; the section-local `Let`s are unfolded (`workload_of tsk t1
t2` is `workload job_task sched tsk t1 t2`, `workload_bound` is `W task_cost task_period
task_deadline tsk delta`). Binder lists follow the Rocq original (the unused section variable
`tsk_k` of `WorkloadBoundDef` is not abstracted by the definitions).
-/

set_option linter.unusedVariables false

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

universe u v

def max_jobs {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) (tsk : sporadic_task)
    (delta : time) : Nat :=
  div_floor (delta + task_deadline tsk - task_cost tsk) (task_period tsk)

def W {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) (tsk : sporadic_task)
    (delta : time) : Nat :=
  let e_k := task_cost tsk
  let p_k := task_period tsk
  let d_k := task_deadline tsk
  min e_k (delta + d_k - e_k - max_jobs task_cost task_period task_deadline tsk delta * p_k) +
    max_jobs task_cost task_period task_deadline tsk delta * e_k

/-- The statement of the case study's theorem `Theorem4_07`. -/
def Theorem4_07_statement : Prop :=
  ∀ {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    (t1 delta : time),
    workload job_task sched tsk t1 (t1 + delta) ≤
      W task_cost task_period task_deadline tsk delta

end CaseStudies.RTSS2007.Theorem4.WorkloadBound
