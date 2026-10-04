import CaseStudies.RTSS2009.Lemma3
import Solutions.Support.Common
import Solutions.Support.BusyWindow
import Solutions.Support.CommonFp

/-! Reference solution of benchmark task `2009-RTSS-Lemma3`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.RTSS2009.Lemma3.ResponseTimeAnalysisFP

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

/-- LEAN_HELPER: the higher-priority bounds are a permutation of the carry-in set followed by the no-carry-in set. -/
theorem perm_CI_NC {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time))
    (delta : time) (num_cpus : Nat) (hnd : R_prev.Nodup) :
    R_prev.Perm (CI_taskset task_cost task_period tsk R_prev delta num_cpus ++
      NC_taskset task_cost task_period tsk R_prev delta num_cpus) := by
  unfold NC_taskset CI_taskset
  convert Solutions.Support.Common.perm_take_append_filter (List.mergeSort_perm _ _) hnd (num_cpus - 1)

theorem Lemma3_09 {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
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
    (H_response_time_recurrence_holds : R = task_cost tsk + div_floor (total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus) num_cpus)
    (Huniq_hp_bounds : hp_bounds.Nodup)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job) (t0 : schedule Job num_cpus → Job → time)
    (t0_leq_arrival_time : t0 sched j ≤ job_arrival j)
    (H_j_of_tsk : job_task j = tsk)
    (cpu_busy_during_t0_rk : ∀ t : Nat, (decide (t0 sched j ≤ t) && decide (t < job_arrival j)) = true →
      hp_busy job_task ts num_cpus sched higher_eq_priority tsk t)
    (t0_left_boundary : t0 sched j = 0 ∨ ¬ hp_busy job_task ts num_cpus sched higher_eq_priority tsk (t0 sched j - 1))
    (j_has_worstcase_responsetime : ∀ (j0 : Job) (x : Nat), arrives_in arr_seq j0 → job_task j0 = tsk →
      completed job_cost sched j (job_arrival j + x) = true →
      completed job_cost sched j0 (job_arrival j0 + x) = true)
    (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j0 + R) = true)
    (H_Lemma2_1 : ∀ (tsk_other : sporadic_task) (R_other t1 delta : time),
      (tsk_other, R_other) ∈ NC_taskset task_cost task_period tsk hp_bounds delta num_cpus →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W_NC task_cost task_period tsk_other delta)
    (H_Lemma2_2 : ∀ (tsk_other : sporadic_task) (R_other t1 delta : time),
      (tsk_other, R_other) ∈ CI_taskset task_cost task_period tsk hp_bounds delta num_cpus →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W task_cost task_period tsk_other R_other delta)
    (f : time)
    (f_is_finish_time : ((!completed job_cost sched j (f - 1)) && completed job_cost sched j f) = true)
    (arrival_before_finish : job_arrival j < f) :
    ∀ t : Nat, t < f - t0 sched j → task_cost tsk ≤ t →
      t - task_cost tsk < div_floor (total_interference_bound_gn task_cost task_period tsk hp_bounds t num_cpus) num_cpus := by
  intro t ht he
  have hfin := f_is_finish_time
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin
  have hnc : completed job_cost sched j (t0 sched j + t) = false := by
    cases hc : completed job_cost sched j (t0 sched j + t)
    · rfl
    · have := completion_monotonic job_cost sched j _ (f - 1) (by tomega) hc
      rw [this] at hfin; exact absurd hfin.1 (by simp)
  have hcost : job_cost j ≤ task_cost tsk := by
    have := (H_valid_job_parameters j H_j_arrives).2.1
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
    rw [H_job_of_tsk] at this; exact this
  have hprev : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j) = true := by
    intro j0 a0 h0 lt
    have hne : j0 ≠ j := by rintro rfl; exact absurd lt (Nat.lt_irrefl _)
    have SPO := H_sporadic_tasks j0 j hne a0 H_j_arrives (h0.trans H_job_of_tsk.symm) (le_of_lt lt)
    rw [h0] at SPO
    have hdp := H_constrained_deadlines tsk task_in_ts
    exact completion_monotonic job_cost sched j0 _ _ (by tomega)
      (H_previous_jobs_of_tsk_completed j0 a0 h0 lt)
  have EX := Solutions.Support.BusyWindow.busy_window_sum_min_ge task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq ts sched higher_eq_priority H_sporadic_tasks
    H_valid_task_parameters H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
    H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
    H_respects_FP_policy H_sequential_tasks tsk j H_j_arrives H_job_of_tsk hcost (t0 sched j)
    t0_leq_arrival_time (fun s h1 h2 => cpu_busy_during_t0_rk s (by simp [h1, h2])) hprev t he hnc
  let G := fun p : sporadic_task × time =>
    min (workload job_task sched p.1 (t0 sched j) (t0 sched j + t)) (t - task_cost tsk + 1)
  have hcov := Solutions.Support.CommonFp.sum_hp_le_sum_pairs ts
    (fun k => higher_priority_task higher_eq_priority tsk k) hp_bounds
    (fun k => min (workload job_task sched k (t0 sched j) (t0 sched j + t)) (t - task_cost tsk + 1))
    H_hp_bounds_has_interfering_tasks
  rw [Solutions.Support.Common.sumSeq_perm _ (perm_CI_NC task_cost task_period tsk hp_bounds t num_cpus
    Huniq_hp_bounds), Solutions.Support.Common.sumSeq_append] at hcov
  have hCI := Solutions.Support.Common.sumSeq_le_sumSeq
    (CI_taskset task_cost task_period tsk hp_bounds t num_cpus) G
    (fun p => interference_bound_generic task_cost task_period tsk t p) (by
      intro p hp
      obtain ⟨k, Rk⟩ := p
      exact min_le_min_right _ (H_Lemma2_2 k Rk (t0 sched j) t hp))
  have hNC := Solutions.Support.Common.sumSeq_le_sumSeq
    (NC_taskset task_cost task_period tsk hp_bounds t num_cpus) G
    (fun p => interference_bound_nc task_cost task_period tsk t p) (by
      intro p hp
      obtain ⟨k, Rk⟩ := p
      exact min_le_min_right _ (H_Lemma2_1 k Rk (t0 sched j) t hp))
  have hgn : total_interference_bound_gn task_cost task_period tsk hp_bounds t num_cpus =
      sumSeq (NC_taskset task_cost task_period tsk hp_bounds t num_cpus)
          (fun p => interference_bound_nc task_cost task_period tsk t p) +
        sumSeq (CI_taskset task_cost task_period tsk hp_bounds t num_cpus)
          (fun p => interference_bound_generic task_cost task_period tsk t p) := rfl
  have htot : (t - task_cost tsk + 1) * num_cpus ≤
      total_interference_bound_gn task_cost task_period tsk hp_bounds t num_cpus := by
    rw [hgn, Nat.mul_comm]
    exact le_trans EX (le_trans hcov ((Nat.add_le_add hCI hNC).trans (le_of_eq (Nat.add_comm _ _))))
  have hdiv := (Nat.le_div_iff_mul_le H_at_least_one_cpu).mpr htot
  unfold div_floor
  tomega

end CaseStudies.RTSS2009.Lemma3.ResponseTimeAnalysisFP

theorem Solutions.RTSS2009.Lemma3.solution : CaseStudies.RTSS2009.Lemma3.ResponseTimeAnalysisFP.Lemma3_09_statement.{u, v} :=
  @CaseStudies.RTSS2009.Lemma3.ResponseTimeAnalysisFP.Lemma3_09
