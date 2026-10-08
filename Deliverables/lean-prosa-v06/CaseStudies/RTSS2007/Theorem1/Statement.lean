-- Case study 2007-RTSS-Theorem1: Bertogna, Cirinei — Response-Time Analysis for Globally Scheduled Symmetric Multiprocessor Platforms (RTSS 2007).
-- Original Rocq statement: RTS_Papers/2007-RTSS-Theorem1/Theorem1.v.
-- Benchmark file: read-only.  Prove `CaseStudies.RTSS2007.Theorem1.ResponseTimeAnalysisFP.Theorem1_07_statement` in `Solution.lean` (this folder).
import Prosa.Util.Sum
import Prosa.Classic.Util.DivMod
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.Interference

/-!
Theorem 1 of RTSS 2007: under global fixed-priority scheduling, a solution `R ≤ d_tsk` of `R = e_tsk
+ ⌊(Σ_(hp_tsk, R_hp) ∈ hp_bounds (⌈R / p_hp⌉ e_hp + e_hp)) / m⌋` is a response-time bound of `tsk`
(Rocq module `ResponseTimeAnalysisFP`, section `ResponseTimeBound`). The interference of a
higher-priority task over an interval of length `delta` is bounded by `⌈delta / p⌉ e + e`
(`interference_bound_generic`), i.e. at most `⌈delta / p⌉` jobs released in the interval plus one
carry-in job.

Representation notes: `\sum_((tsk_other, R_other) <- R_prev) F (tsk_other, R_other)` is `sumSeq
R_prev (fun (tsk_other, R_other) => F (tsk_other, R_other))`; the section-local `Let`s are unfolded
(`response_time_bounded_by` is `is_response_time_bound_of_task … sched`, `is_hp_task` is
`higher_priority_task higher_eq_priority tsk`); Boolean tests in proposition position are `= true`.
-/

set_option linter.unusedVariables false

namespace CaseStudies.RTSS2007.Theorem1.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Classic.Util.DivMod (div_floor div_ceil)
open Prosa.Util.Sum (sumSeq)

universe u v

def interference_bound_generic {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  let tsk_other := tsk_R.1
  div_ceil delta (task_period tsk_other) * task_cost tsk_other + task_cost tsk_other

def total_interference_bound_fp {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (R_prev : List (sporadic_task × time))
    (delta : time) : Nat :=
  sumSeq R_prev (fun (tsk_other, R_other) =>
    interference_bound_generic task_cost task_period delta (tsk_other, R_other))

/-- The statement of the case study's theorem `Theorem1_07`. -/
def Theorem1_07_statement : Prop :=
  ∀ {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines : ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks : ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
      higher_priority_task higher_eq_priority tsk hp_tsk = true → ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_response_time_bounds_ge_cost : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → task_cost hp_tsk ≤ R)
    (H_interfering_tasks_miss_no_deadlines : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds : R = task_cost tsk +
      div_floor (total_interference_bound_fp task_cost task_period hp_bounds R) num_cpus)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk),
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R

end CaseStudies.RTSS2007.Theorem1.ResponseTimeAnalysisFP
