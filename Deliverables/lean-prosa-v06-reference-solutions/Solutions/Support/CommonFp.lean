import Solutions.Support.Common
import Prosa.Classic.Analysis.Global.Basic.BertognaFpTheory

/-!
Facts about global fixed-priority scheduling used by several case-study proofs, assembled from the public
lemmas of the classic Lean Prosa Bertogna–Cirinei FP analysis (`BertognaFpTheory`).  The only difference
from the classic chain is that the response-time recurrence is not assumed: the step that used it
(`bertogna_fp_too_much_interference`) only needs `task_cost tsk ≤ R`.
-/

set_option linter.unusedVariables false

namespace Solutions.Support.CommonFp

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Classic.Analysis.Global.Basic.BertognaFpTheory.ResponseTimeAnalysisFP
open Prosa.Util.Sum (sumSeq)

universe u v

/-- A job that is not complete `R ≥ e_tsk` time units after its arrival suffers at least
`R - e_tsk + 1` units of total interference (classic `bertogna_fp_too_much_interference`, with
`task_cost tsk ≤ R` in place of the response-time recurrence). -/
theorem too_much_interference {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (tsk : sporadic_task) (R : time) (hRe : task_cost tsk ≤ R)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true) :
    R - task_cost tsk + 1 ≤
      total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) := by
  have NOTCOMP := H_j_not_completed
  simp only [completed, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at NOTCOMP
  have hcost : job_cost j ≤ task_cost tsk := by
    have := (H_valid_job_parameters j H_j_arrives).2.1
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
    rw [H_job_of_tsk] at this
    exact this
  have hsvc : service sched j (job_arrival j + R) =
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), service_at sched j t :=
    service_before_arrival_eq_service_during job_arrival sched j H_jobs_must_arrive_to_execute 0 R
      (Nat.zero_le _)
  have hcover : R ≤ ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      ((backlogged job_arrival job_cost sched j t).toNat + service_at sched j t) := by
    calc R = ∑ _t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), 1 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Ico] at ht
        cases hb : backlogged job_arrival job_cost sched j t
        · simp only [Bool.toNat_false, Nat.zero_add]
          have hpend : pending job_arrival job_cost sched j t = true := by
            simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq,
              Bool.not_eq_true']
            refine ⟨ht.1, ?_⟩
            cases hc : completed job_cost sched j t
            · rfl
            · have := completion_monotonic job_cost sched j t (job_arrival j + R)
                (Nat.le_of_lt ht.2) hc
              simp only [completed, decide_eq_true_eq] at this
              tomega
          simp only [backlogged, hpend, Bool.true_and, Bool.not_eq_false'] at hb
          have := not_scheduled_no_service sched j t
          rw [hb] at this
          have hne : service_at sched j t ≠ 0 := by
            intro h0; rw [h0] at this; simp at this
          tomega
        · simp
  unfold total_interference
  rw [Finset.sum_add_distrib] at hcover
  rw [hsvc] at NOTCOMP
  tomega

/-- Bertogna–Cirinei core under global FP: if a job `j` of `tsk` is not complete by `a_j + R`
(`e_tsk ≤ R ≤ d_tsk`, earlier jobs of `tsk` complete within `R`), the higher-priority tasks'
interferences, each truncated at `R - e_tsk + 1`, sum to at least `m (R - e_tsk + 1)`. -/
theorem hp_interference_exceeds {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts) (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds →
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks : ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
      higher_priority_task higher_eq_priority tsk hp_tsk = true → ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_interfering_tasks_miss_no_deadlines : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time) (hRe : task_cost tsk ≤ R) (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true)
    (H_previous_jobs_of_tsk_completed : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j0 + R) = true) :
    (R - task_cost tsk + 1) * num_cpus ≤
      sumSeq (ts.val.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other))
        (fun tsk_k => min (task_interference job_arrival job_cost job_task sched j tsk_k
          (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1)) := by
  apply bertogna_fp_minimum_exceeds_interference task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq H_sporadic_tasks ts H_valid_task_parameters
    H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched
    H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute higher_eq_priority H_work_conserving H_respects_FP_policy tsk
    task_in_ts hp_bounds H_response_time_of_interfering_tasks_is_known
    H_hp_bounds_has_interfering_tasks H_interfering_tasks_miss_no_deadlines R
    H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk
    H_previous_jobs_of_tsk_completed
  rw [bertogna_fp_interference_on_all_cpus task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq H_sporadic_tasks ts H_valid_task_parameters
    H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    higher_eq_priority H_work_conserving H_respects_FP_policy tsk task_in_ts hp_bounds
    H_hp_bounds_has_interfering_tasks R H_response_time_no_larger_than_deadline j H_j_arrives
    H_job_of_tsk H_previous_jobs_of_tsk_completed]
  exact Nat.mul_le_mul_right _ (too_much_interference task_cost task_deadline job_arrival job_cost
    job_deadline job_task arr_seq H_valid_job_parameters sched H_jobs_must_arrive_to_execute tsk R
    hRe j H_j_arrives H_job_of_tsk H_j_not_completed)

/-- Summing over the higher-priority tasks is bounded by summing over any list of pairs whose first
components cover them. -/
theorem sum_hp_le_sum_pairs {sporadic_task : Type u} [DecidableEq sporadic_task]
    (ts : taskset_of sporadic_task) (P : sporadic_task → Bool) (L : List (sporadic_task × time))
    (F : sporadic_task → Nat) (hcov : ∀ k, k ∈ ts.val → P k = true → ∃ R, (k, R) ∈ L) :
    sumSeq (ts.val.filter P) F ≤ sumSeq L (fun p => F p.1) := by
  have := Prosa.Classic.Util.Sum.leq_sum_sub_uniq _ (ts.val.filter P) (L.map Prod.fst) F
    (ts.nodup.filter _) (by
      intro k hk
      rw [List.mem_filter] at hk
      obtain ⟨R, hR⟩ := hcov k hk.1 hk.2
      exact List.mem_map.mpr ⟨(k, R), hR, rfl⟩)
  refine le_trans this (le_of_eq ?_)
  unfold sumSeq
  rw [List.map_map]
  rfl

end Solutions.Support.CommonFp
