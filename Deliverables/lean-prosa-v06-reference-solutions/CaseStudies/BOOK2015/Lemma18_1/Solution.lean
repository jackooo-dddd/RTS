import CaseStudies.BOOK2015.Lemma18_1.Statement
import CaseStudies.Support.Common

/-! Reference solution of benchmark task `2015-BOOK-Lemma18.1`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.BOOK2015.Lemma18_1.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Classic.Util.DivMod (div_floor div_ceil)
open Prosa.Util.Sum (sumSeq sumFiltered)

/-- LEAN_HELPER: a per-task bound of the form `min _ (delta - e + 1)` is at most one at `delta = e`. -/
theorem ib_generic_at_cost_le_one {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (p : sporadic_task × time) :
    interference_bound_generic task_cost task_period tsk (task_cost tsk) p ≤ 1 := by
  unfold interference_bound_generic
  exact le_trans (min_le_right _ _) (by simp)

theorem ib_nc_at_cost_le_one {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (p : sporadic_task × time) :
    interference_bound_nc task_cost task_period tsk (task_cost tsk) p ≤ 1 := by
  unfold interference_bound_nc
  exact le_trans (min_le_right _ _) (by simp)

/-- LEAN_HELPER: with fewer than `m` pairs, the carry-in set is all of them and the no-carry-in set is empty. -/
theorem NC_taskset_nil_of_short {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time))
    (delta : time) (num_cpus : Nat) (h : R_prev.length < num_cpus) :
    NC_taskset task_cost task_period tsk R_prev delta num_cpus = [] := by
  unfold NC_taskset CI_taskset
  rw [List.take_of_length_le (by rw [List.length_mergeSort]; omega)]
  rw [List.filter_eq_nil_iff]
  intro p hp
  simp [List.mem_mergeSort, hp]

theorem CI_taskset_length_of_short {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time))
    (delta : time) (num_cpus : Nat) (h : R_prev.length < num_cpus) :
    (CI_taskset task_cost task_period tsk R_prev delta num_cpus).length = R_prev.length := by
  unfold CI_taskset
  rw [List.take_of_length_le (by rw [List.length_mergeSort]; omega), List.length_mergeSort]

theorem Lemma18_1_15 {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    (num_higher_priority_tsk : sumSeq hp_bounds (fun (_, _) => 1) < num_cpus)
    (R1 R2 : time)
    (H_response_time_recurrence_holds_gn : R1 = task_cost tsk + div_floor (total_interference_bound_gn task_cost task_period tsk hp_bounds R1 num_cpus) num_cpus)
    (H_response_time_recurrence_holds_bertogna : R2 = task_cost tsk + div_floor (total_interference_bound_fp task_cost task_period tsk hp_bounds R2) num_cpus)
    (R1_is_least_solution : ∀ x : time, x = task_cost tsk + div_floor (total_interference_bound_gn task_cost task_period tsk hp_bounds x num_cpus) num_cpus → R1 ≤ x)
    (R2_is_least_solution : ∀ x : time, x = task_cost tsk + div_floor (total_interference_bound_fp task_cost task_period tsk hp_bounds x) num_cpus → R2 ≤ x) :
    sumSeq hp_bounds (fun (_, _) => 1) < num_cpus → R1 = task_cost tsk ∧ R2 = task_cost tsk := by
  intro hn
  rw [CaseStudies.Support.Common.sumSeq_one] at hn
  -- the cost solves both recurrences
  have hgn : total_interference_bound_gn task_cost task_period tsk hp_bounds (task_cost tsk) num_cpus < num_cpus := by
    unfold total_interference_bound_gn
    rw [NC_taskset_nil_of_short task_cost task_period tsk hp_bounds _ num_cpus hn]
    have := CaseStudies.Support.Common.sumSeq_le_length_of_le_one
      (CI_taskset task_cost task_period tsk hp_bounds (task_cost tsk) num_cpus)
      (fun p => interference_bound_generic task_cost task_period tsk (task_cost tsk) p)
      (fun p _ => ib_generic_at_cost_le_one task_cost task_period tsk p)
    rw [CI_taskset_length_of_short task_cost task_period tsk hp_bounds _ num_cpus hn] at this
    simp only [Prosa.Util.Sum.sumSeq, List.map_nil, List.sum_nil, Nat.zero_add]
    exact lt_of_le_of_lt this hn
  have hfp : total_interference_bound_fp task_cost task_period tsk hp_bounds (task_cost tsk) < num_cpus := by
    unfold total_interference_bound_fp
    have := CaseStudies.Support.Common.sumSeq_le_length_of_le_one hp_bounds
      (fun (tsk_other, R_other) =>
        interference_bound_generic task_cost task_period tsk (task_cost tsk) (tsk_other, R_other))
      (fun p _ => ib_generic_at_cost_le_one task_cost task_period tsk p)
    exact lt_of_le_of_lt this hn
  have e1 : task_cost tsk = task_cost tsk + div_floor
      (total_interference_bound_gn task_cost task_period tsk hp_bounds (task_cost tsk) num_cpus) num_cpus := by
    simp [div_floor, Nat.div_eq_of_lt hgn]
  have e2 : task_cost tsk = task_cost tsk + div_floor
      (total_interference_bound_fp task_cost task_period tsk hp_bounds (task_cost tsk)) num_cpus := by
    simp [div_floor, Nat.div_eq_of_lt hfp]
  have l1 := R1_is_least_solution _ e1
  have l2 := R2_is_least_solution _ e2
  constructor
  · have : task_cost tsk ≤ R1 := by rw [H_response_time_recurrence_holds_gn]; exact Nat.le_add_right _ _
    exact Nat.le_antisymm l1 this
  · have : task_cost tsk ≤ R2 := by rw [H_response_time_recurrence_holds_bertogna]; exact Nat.le_add_right _ _
    exact Nat.le_antisymm l2 this

end CaseStudies.BOOK2015.Lemma18_1.ResponseTimeAnalysisFP

theorem CaseStudies.BOOK2015.Lemma18_1.solution : CaseStudies.BOOK2015.Lemma18_1.ResponseTimeAnalysisFP.Lemma18_1_15_statement.{u, v} :=
  @CaseStudies.BOOK2015.Lemma18_1.ResponseTimeAnalysisFP.Lemma18_1_15
