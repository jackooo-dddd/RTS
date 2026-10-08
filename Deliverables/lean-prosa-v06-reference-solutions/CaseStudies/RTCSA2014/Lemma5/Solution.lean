import CaseStudies.RTCSA2014.Lemma5.Statement
import CaseStudies.Support.Common
import CaseStudies.Support.CommonFp

/-! Reference solution of benchmark task `2014-RTCSA-Lemma5`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.RTCSA2014.Lemma5.ResponseTimeAnalysisFP

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

theorem Lemma5_14 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : ∀ tsk : sporadic_task, tsk ∈ ts →
      0 < task_cost tsk ∧ 0 < task_period tsk ∧ 0 < task_deadline tsk ∧
        task_cost tsk ≤ task_deadline tsk ∧ task_cost tsk < task_period tsk)
    (H_constrained_deadlines : ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (previous_job_must_finished : ∀ (j1 j2 : Job) (t : time), scheduled sched j1 t = true →
      job_task j1 = job_task j2 → job_arrival j2 < job_arrival j1 → completed job_cost sched j2 t = true)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (task_in_hpbound_in_ts : ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
      hp_tsk ∈ ts ∧ higher_priority_task higher_eq_priority tsk hp_tsk = true)
    (H_response_time_of_interfering_tasks_is_known : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks : ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
      higher_priority_task higher_eq_priority tsk hp_tsk = true → ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_response_time_bounds_ge_cost : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → task_cost hp_tsk ≤ R)
    (H_interfering_tasks_miss_no_deadlines : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (H_hp_bounds_uniq : hp_bounds.Nodup)
    (critical_instant : time)
    (critical_instant_left_boundary : critical_instant = 0 ∨ ¬ hp_busy job_task ts num_cpus sched higher_eq_priority tsk (critical_instant - 1))
    (critical_instant_is_busy : ts.val.countP (fun tsk_other =>
      task_is_scheduled job_task sched tsk_other critical_instant &&
        higher_priority_task higher_eq_priority tsk tsk_other) = num_cpus)
    (CI_taskset NC_taskset : List (sporadic_task × time))
    (H_CI_taskset_sub_hp_bounds : ∀ p, p ∈ CI_taskset → p ∈ hp_bounds)
    (has_carry_in_job : ∀ (tsk_other : sporadic_task) (R_other : time), (tsk_other, R_other) ∈ CI_taskset →
      ∃ j0 : Job, arrives_in arr_seq j0 ∧ job_task j0 = tsk_other ∧ job_arrival j0 < critical_instant ∧
        (!completed job_cost sched j0 critical_instant) = true)
    (H_CI_taskset_size : CI_taskset.length ≤ num_cpus - 1)
    (H_NC_taskset_sub_hp_bounds : ∀ p, p ∈ NC_taskset → p ∈ hp_bounds)
    (non_carry_in_job : ∀ (tsk_other : sporadic_task) (R_other : time), (tsk_other, R_other) ∈ NC_taskset →
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk_other → job_arrival j0 < critical_instant →
        completed job_cost sched j0 critical_instant = true)
    (H_hp_covered_by_CI_or_NC : ∀ x : sporadic_task × time, x ∈ hp_bounds →
      (decide (x ∈ CI_taskset) || decide (x ∈ NC_taskset)) = true)
    (H_CI_NC_disjoint : ∀ x : sporadic_task × time, x ∈ CI_taskset → (!decide (x ∈ NC_taskset)) = true)
    (H_CI_taskset_uniq : CI_taskset.Nodup) (H_NC_taskset_uniq : NC_taskset.Nodup)
    (lemma2 : ∀ (tsk_other : sporadic_task) (R_other t1 : time) (delta : Nat),
      (tsk_other, R_other) ∈ NC_taskset → (tsk_other, R_other) ∈ hp_bounds →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W_NC task_cost task_period tsk_other delta)
    (lemma4 : ∀ (tsk_other : sporadic_task) (R_other t1 : time) (delta : Nat),
      (tsk_other, R_other) ∈ CI_taskset → (tsk_other, R_other) ∈ hp_bounds →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W_CI task_cost task_period tsk_other R_other delta) :
    ∀ R : Nat, R ≤ task_deadline tsk →
      response_time_recurrence task_cost task_period num_cpus tsk R CI_taskset NC_taskset →
      R_is_minimal_solution task_cost task_period num_cpus tsk R CI_taskset NC_taskset →
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  intro R hRd hrec hmin
  unfold response_time_recurrence at hrec
  have hRe : task_cost tsk ≤ R := by tomega
  have hvalid : valid_sporadic_taskset task_cost task_period task_deadline ts.val := by
    intro k hk
    obtain ⟨h1, h2, h3, h4, h5⟩ := H_valid_task_parameters k hk
    simp only [Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.is_valid_sporadic_task,
      Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_positive,
      Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_period_positive,
      Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_deadline_positive,
      Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_le_deadline,
      Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_le_period, decide_eq_true_eq]
    exact ⟨h1, h2, h3, h4, Nat.le_of_lt h5⟩
  suffices MAIN : ∀ (n : Nat) (j : Job), job_arrival j = n → arrives_in arr_seq j →
      job_task j = tsk → completed job_cost sched j (job_arrival j + R) = true by
    intro j harr htsk
    exact MAIN _ j rfl harr htsk
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro j hn harr htsk
    by_contra hnc
    have hnc' : (!completed job_cost sched j (job_arrival j + R)) = true := by simpa using hnc
    have hprev : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j0 + R) = true :=
      fun j0 a0 t0 lt => IH _ (hn ▸ lt) j0 rfl a0 t0
    let TI := fun k => task_interference job_arrival job_cost job_task sched j k
      (job_arrival j) (job_arrival j + R)
    have EX := CaseStudies.Support.CommonFp.hp_interference_exceeds task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts
      hvalid H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute higher_eq_priority H_work_conserving H_respects_FP_policy tsk
      task_in_ts hp_bounds H_response_time_of_interfering_tasks_is_known
      H_hp_bounds_has_interfering_tasks H_interfering_tasks_miss_no_deadlines R hRe hRd j harr htsk
      hnc' hprev
    have hcov := CaseStudies.Support.CommonFp.sum_hp_le_sum_pairs ts
      (fun k => higher_priority_task higher_eq_priority tsk k) (CI_taskset ++ NC_taskset)
      (fun k => min (TI k) (R - task_cost tsk + 1)) (by
        intro k hk hhp
        obtain ⟨R', hR'⟩ := H_hp_bounds_has_interfering_tasks k hk hhp
        have := H_hp_covered_by_CI_or_NC _ hR'
        simp only [Bool.or_eq_true, decide_eq_true_eq] at this
        exact ⟨R', List.mem_append.mpr this⟩)
    rw [CaseStudies.Support.Common.sumSeq_append] at hcov
    have hCI := CaseStudies.Support.Common.sumSeq_le_sumSeq CI_taskset
      (fun p => min (TI p.1) (R - task_cost tsk + 1))
      (fun p => interference_bound_arbitrary_ci task_cost task_period tsk R p) (by
        intro p hp
        obtain ⟨k, Rk⟩ := p
        exact min_le_min_right _ (le_trans
          (task_interference_le_workload job_arrival job_cost job_task sched j k _ _)
          (lemma4 k Rk (job_arrival j) R hp (H_CI_taskset_sub_hp_bounds _ hp))))
    have hNC := CaseStudies.Support.Common.sumSeq_le_sumSeq NC_taskset
      (fun p => min (TI p.1) (R - task_cost tsk + 1))
      (fun p => interference_bound_arbitrary_nc task_cost task_period tsk R p) (by
        intro p hp
        obtain ⟨k, Rk⟩ := p
        exact min_le_min_right _ (le_trans
          (task_interference_le_workload job_arrival job_cost job_task sched j k _ _)
          (lemma2 k Rk (job_arrival j) R hp (H_NC_taskset_sub_hp_bounds _ hp))))
    have hbound : total_interference_bound_rtcsa14 task_cost task_period tsk CI_taskset NC_taskset R =
        sumSeq CI_taskset (fun p => interference_bound_arbitrary_ci task_cost task_period tsk R p) +
          sumSeq NC_taskset (fun p => interference_bound_arbitrary_nc task_cost task_period tsk R p) :=
      rfl
    have htot : (R - task_cost tsk + 1) * num_cpus ≤
        total_interference_bound_rtcsa14 task_cost task_period tsk CI_taskset NC_taskset R := by
      rw [hbound]; exact le_trans EX (le_trans hcov (Nat.add_le_add hCI hNC))
    have hdiv := (Nat.le_div_iff_mul_le H_at_least_one_cpu).mpr htot
    unfold div_floor at hrec
    tomega

end CaseStudies.RTCSA2014.Lemma5.ResponseTimeAnalysisFP

theorem CaseStudies.RTCSA2014.Lemma5.solution : CaseStudies.RTCSA2014.Lemma5.ResponseTimeAnalysisFP.Lemma5_14_statement.{u, v} :=
  @CaseStudies.RTCSA2014.Lemma5.ResponseTimeAnalysisFP.Lemma5_14
