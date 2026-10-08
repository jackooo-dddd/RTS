import CaseStudies.RTSS2009.Lemma2_1.Statement
import CaseStudies.Support.Common
import CaseStudies.Support.WorkloadJobs

/-! Reference solution of benchmark task `2009-RTSS-Lemma2-1`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.RTSS2009.Lemma2_1.ResponseTimeAnalysisFP

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

theorem Lemma2_09 {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    (H_arrival_times_are_consistent : ∀ (j : Job) (t : time), arrives_at arr_seq j t = true → job_arrival j = t)
    (H_no_duplicate_arrivals : ∀ t : time, (jobs_arriving_at arr_seq t).Nodup)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
    (H_at_least_one_cpu : 0 < num_cpus)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_priority_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_antisymmetric : FP_is_antisymmetric_over_task_set higher_eq_priority ts.val)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (j_has_worstcase_responsetime : ∀ (j0 : Job) (x : Nat), arrives_in arr_seq j0 → job_task j0 = tsk →
      completed job_cost sched j (job_arrival j + x) = true →
      completed job_cost sched j0 (job_arrival j0 + x) = true)
    (t0 : schedule Job num_cpus → Job → time)
    (t0_leq_arrival_time : t0 sched j ≤ job_arrival j)
    (cpu_busy_during_t0_rk : ∀ t : Nat, (decide (t0 sched j ≤ t) && decide (t < job_arrival j)) = true →
      hp_busy job_task ts num_cpus sched higher_eq_priority tsk t)
    (t0_left_boundary : t0 sched j = 0 ∨ ¬ hp_busy job_task ts num_cpus sched higher_eq_priority tsk (t0 sched j - 1))
    (carry_in_job_unique : ∀ (tsk_other : sporadic_task) (j1 j2 : Job),
      job_task j1 = tsk_other → is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk j t0 j1 →
      job_task j2 = tsk_other → is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk j t0 j2 → j1 = j2)
    (H_response_time_bound : ∀ (j0 : Job) (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ hp_bounds → arrives_in arr_seq j0 → job_task j0 = tsk_other →
      completed job_cost sched j0 (job_arrival j0 + R_other) = true)
    (H_no_deadline_miss : ∀ (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ hp_bounds → R_other ≤ task_deadline tsk_other) :
    ∀ (tsk_other : sporadic_task) (R_other : time) (t : Nat),
      no_carry_in_workload_of_task job_arrival job_cost job_task arr_seq num_cpus sched j t0 tsk_other →
      (tsk_other, R_other) ∈ hp_bounds →
      workload job_task sched tsk_other (t0 sched j) (t0 sched j + t) ≤ W_NC task_cost task_period tsk_other t := by
  intro tsk_other R_other t hnci hmem
  obtain ⟨L, hnd, hL, hw⟩ := CaseStudies.Support.WorkloadJobs.workload_as_jobs job_task sched tsk_other
    (t0 sched j) (t0 sched j + t)
  rw [hw]
  -- every job contributing to the workload arrives within the window (no carry-in)
  have hinfo : ∀ x ∈ L, arrives_in arr_seq x ∧ job_task x = tsk_other ∧ t0 sched j ≤ job_arrival x := by
    intro x hx
    obtain ⟨htk, s, hs1, hs2, hsch⟩ := hL x hx
    have harr := H_jobs_come_from_arrival_sequence x s hsch
    refine ⟨harr, htk, ?_⟩
    by_contra hlt
    have hc := hnci x harr htk (by tomega)
    have := CaseStudies.Support.WorkloadJobs.not_completed_of_scheduled_later job_arrival job_cost sched
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute x _ s hs1 hsch
    rw [hc] at this; exact Bool.noConfusion this
  cases L with
  | nil => simp [sumSeq]
  | cons x0 L0 =>
    have hp : 0 < task_period tsk_other := by
      obtain ⟨harr, htk, _⟩ := hinfo x0 List.mem_cons_self
      have := (H_valid_task_parameters _ (htk ▸ H_all_jobs_from_taskset x0 harr)).2.1
      simpa [task_period_positive] using this
    generalize hLdef : x0 :: L0 = L at hnd hL hinfo ⊢
    have hle : sumSeq L (fun x => service_during sched x (t0 sched j) (t0 sched j + t)) ≤
        sumSeq (L.map (fun x => job_arrival x - t0 sched j))
          (fun y => min (task_cost tsk_other) (t - y)) := by
      have : sumSeq (L.map (fun x => job_arrival x - t0 sched j))
          (fun y => min (task_cost tsk_other) (t - y)) =
          sumSeq L (fun x => min (task_cost tsk_other) (t - (job_arrival x - t0 sched j))) := by
        unfold sumSeq; rw [List.map_map]; rfl
      rw [this]
      apply CaseStudies.Support.Common.sumSeq_le_sumSeq
      intro x hx
      obtain ⟨harr, htk, hge⟩ := hinfo x hx
      apply le_min
      · have h1 := CaseStudies.Support.WorkloadJobs.service_during_le_remaining job_cost sched
          H_completed_jobs_dont_execute x (t0 sched j) (t0 sched j + t) (Nat.le_add_right _ _)
        have h2 := (H_valid_job_parameters x harr).2.1
        simp only [job_cost_le_task_cost, decide_eq_true_eq, htk] at h2
        tomega
      · have := CaseStudies.Support.WorkloadJobs.service_during_le_after_arrival job_arrival sched
          H_sequential_jobs H_jobs_must_arrive_to_execute x (t0 sched j) (t0 sched j + t) hge
        tomega
    refine le_trans hle (le_of_le_of_eq (CaseStudies.Support.WorkloadArith.sum_sep_le _ _ hp _ ?_ t) rfl)
    rw [List.pairwise_map]
    apply hnd.imp_of_mem
    intro a b ha hb hab
    obtain ⟨harra, hta, hgea⟩ := hinfo a ha
    obtain ⟨harrb, htb, hgeb⟩ := hinfo b hb
    rcases Nat.le_total (job_arrival a) (job_arrival b) with h | h
    · have := H_sporadic_tasks a b hab harra harrb (hta.trans htb.symm) h
      rw [hta] at this; left; tomega
    · have := H_sporadic_tasks b a (Ne.symm hab) harrb harra (htb.trans hta.symm) h
      rw [htb] at this; right; tomega

end CaseStudies.RTSS2009.Lemma2_1.ResponseTimeAnalysisFP

theorem CaseStudies.RTSS2009.Lemma2_1.solution : CaseStudies.RTSS2009.Lemma2_1.ResponseTimeAnalysisFP.Lemma2_09_statement.{u, v} :=
  @CaseStudies.RTSS2009.Lemma2_1.ResponseTimeAnalysisFP.Lemma2_09
