-- Translated from: ../rt-proofs/analysis/abstract/run_to_completion.v
import Prosa.Analysis.Facts.Model.Service_of_jobs
import Prosa.Analysis.Facts.Preemption.Rtc_threshold.Job_preemptable
import Prosa.Analysis.Abstract.Definitions

namespace Prosa.Analysis.Abstract.Run_to_completion

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Ideal
open Prosa.Model.Processor.Platform_properties
open Prosa.Model.Preemption.Parameter
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Ideal_schedule
open Prosa.Analysis.Facts.Preemption.Rtc_threshold.Job_preemptable
open Prosa.Util.Sum

section AbstractRTARunToCompletionThreshold

variable {Task : TaskType}
variable [TaskCost Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable [JobPreemptable Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

attribute [local instance] pstate_instance

variable (sched : schedule (processor_state Job))

variable (H_jobs_respect_taskset_costs : arrivals_have_valid_job_costs (Task := Task) arr_seq)

variable (tsk : Task)

variable (interference : Job → instant → Bool)
variable (interfering_workload : Job → instant → duration)

variable (H_work_conserving : work_conserving arr_seq sched tsk interference interfering_workload)

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)
variable (H_job_cost_positive : job_cost_positive j)

variable (t1 t2 : instant)
variable (H_busy_interval : busy_interval sched interference interfering_workload j t1 t2)

include H_arrival_times_are_consistent H_jobs_respect_taskset_costs H_work_conserving H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval in
theorem job_completes_within_busy_interval :
    completed_by sched j t2 := by
  obtain ⟨⟨⟨_, h_arr_lt_t2⟩, _, _⟩, _, h_not_pend⟩ := H_busy_interval
  by_contra h_nc
  exact h_not_pend ⟨h_arr_lt_t2, h_nc⟩

section InterferenceIsComplement

variable (t : instant) (delta : duration)
variable (H_greater_than_or_equal : t1 ≤ t)
variable (H_less_or_equal : t + delta ≤ t2)

include H_arrival_times_are_consistent H_jobs_respect_taskset_costs H_work_conserving H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval H_greater_than_or_equal H_less_or_equal in
theorem interference_is_complement_to_schedule :
    service_during sched j t (t + delta) + cumul_interference interference j t (t + delta) = delta := by
  simp only [service_during, cumul_interference, ← Finset.sum_add_distrib]
  have h_each : ∀ x ∈ Finset.Ico t (t + delta),
      service_at sched j x + (interference j x).toNat = 1 := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    have h_range : t1 ≤ x ∧ x < t2 :=
      ⟨Nat.le_trans H_greater_than_or_equal hx.1, Nat.lt_of_lt_of_le hx.2 H_less_or_equal⟩
    have h_wc := H_work_conserving j t1 t2 x H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval h_range
    rw [service_at_is_scheduled_at]
    cases h_int : interference j x <;> simp_all
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.card_Ico]
  simp [Nat.add_sub_cancel_left]

end InterferenceIsComplement

section InterferenceBoundedImpliesEnoughService

variable (progress_of_job : duration)
variable (H_progress_le_job_cost : progress_of_job ≤ job_cost j)

variable (delta : duration)
variable (H_total_workload_is_bounded :
  progress_of_job + cumul_interference interference j t1 (t1 + delta) ≤ delta)

include H_arrival_times_are_consistent H_jobs_respect_taskset_costs H_work_conserving H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval H_progress_le_job_cost H_total_workload_is_bounded in
theorem j_receives_at_least_run_to_completion_threshold :
    service sched j (t1 + delta) ≥ progress_of_job := by
  by_cases h : t1 + delta ≤ t2
  · -- Case: t1 + delta ≤ t2
    have h_compl := interference_is_complement_to_schedule
      arr_seq H_arrival_times_are_consistent sched H_jobs_respect_taskset_costs
      tsk interference interfering_workload H_work_conserving
      j H_j_arrives H_job_of_tsk H_job_cost_positive
      t1 t2 H_busy_interval t1 delta (le_refl t1) h
    have h1 : progress_of_job ≤ service_during sched j t1 (t1 + delta) :=
      Nat.le_of_add_le_add_right
        (le_trans H_total_workload_is_bounded (le_of_eq h_compl.symm))
    exact Nat.le_trans h1 (by
      simp only [service]
      rw [← service_during_cat sched j 0 t1 (t1 + delta) ⟨Nat.zero_le _, Nat.le_add_right _ _⟩]
      exact Nat.le_add_left _ _)
  · -- Case: t2 < t1 + delta
    push_neg at h
    have h_cb := job_completes_within_busy_interval
      arr_seq H_arrival_times_are_consistent sched H_jobs_respect_taskset_costs
      tsk interference interfering_workload H_work_conserving
      j H_j_arrives H_job_of_tsk H_job_cost_positive
      t1 t2 H_busy_interval
    exact Nat.le_trans H_progress_le_job_cost (Nat.le_trans h_cb
      (service_monotonic sched j t2 (t1 + delta) (Nat.le_of_lt h)))

end InterferenceBoundedImpliesEnoughService

section CompletionOfJobAfterRunToCompletionThreshold

variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)
variable (H_valid_preemption_model : valid_preemption_model arr_seq sched)

include H_arrival_times_are_consistent H_jobs_respect_taskset_costs H_work_conserving H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval H_completed_jobs_dont_execute H_valid_preemption_model in
theorem job_completes_after_reaching_run_to_completion_threshold :
    ∀ t,
      job_run_to_completion_threshold j ≤ service sched j t →
      completed_by sched j (t + (job_cost j - job_run_to_completion_threshold j)) := by
  intro t h_es
  have h_rtc_le := job_run_to_completion_threshold_le_job_cost j
  have h_jl_add : (job_cost j - job_run_to_completion_threshold j) +
      job_run_to_completion_threshold j = job_cost j :=
    Nat.sub_add_cancel h_rtc_le
  -- Generalize away the Nat subtraction so omega doesn't see it
  generalize job_cost j - job_run_to_completion_threshold j = job_last at *
  clear h_rtc_le
  by_contra h_not_compl
  -- Every time step in [t, t + job_last] is scheduled
  have h_sched : ∀ t', t ≤ t' → t' ≤ t + job_last → scheduled_at sched j t' = true := by
    intro t' h_ge h_le
    apply job_nonpreemptive_after_run_to_completion_threshold arr_seq sched
      H_valid_preemption_model j H_j_arrives t t' h_ge h_es
    intro h_c
    exact h_not_compl (completion_monotonic sched j t' (t + job_last) h_le h_c)
  -- Count service: at least job_last + 1 in [t, t + job_last + 1)
  have h_serv : job_last + 1 ≤ service_during sched j t (t + job_last + 1) := by
    simp only [service_during]
    have h_card : (Finset.Ico t (t + job_last + 1)).card = job_last + 1 := by
      rw [Nat.card_Ico]; omega
    calc job_last + 1
        = ∑ _i ∈ Finset.Ico t (t + job_last + 1), 1 := by
          rw [Finset.sum_const, h_card]; simp
      _ ≤ ∑ i ∈ Finset.Ico t (t + job_last + 1), service_at sched j i := by
          apply Finset.sum_le_sum
          intro i hi
          obtain ⟨hi_ge, hi_lt⟩ := Finset.mem_Ico.mp hi
          have hi_sched := h_sched i hi_ge (Nat.le_of_lt_succ hi_lt)
          rw [service_at_is_scheduled_at]
          simp [hi_sched]
  -- Total service bounded by job_cost
  have h_bound : service_during sched j 0 (t + job_last + 1) ≤ job_cost j := by
    have := service_at_most_cost sched H_completed_jobs_dont_execute j
      ideal_proc_model_provides_unit_service (t + job_last + 1)
    simp only [service] at this; exact this
  -- Split service at t
  have h_split := service_during_cat sched j 0 t (t + job_last + 1)
    ⟨Nat.zero_le _, le_trans (Nat.le_add_right t job_last) (Nat.le_succ _)⟩
  -- h_es with service unfolded
  have h_es' : job_run_to_completion_threshold j ≤ service_during sched j 0 t := by
    simp only [service] at h_es; exact h_es
  -- Derive contradiction: rtc + (jl + 1) ≤ ... ≤ job_cost = jl + rtc
  exact absurd
    (calc job_run_to_completion_threshold j + (job_last + 1)
        ≤ service_during sched j 0 t + service_during sched j t (t + job_last + 1) :=
          Nat.add_le_add h_es' h_serv
      _ = service_during sched j 0 (t + job_last + 1) := h_split
      _ ≤ job_cost j := h_bound)
    (by rw [← h_jl_add]; omega)

end CompletionOfJobAfterRunToCompletionThreshold

end AbstractRTARunToCompletionThreshold

end Prosa.Analysis.Abstract.Run_to_completion
