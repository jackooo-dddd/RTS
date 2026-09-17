-- Translated from: ../rt-proofs/classic/model/schedule/uni/basic/platform.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

namespace Prosa.Classic.Model.Schedule.Uni.Basic.Platform

set_option linter.dupNamespace false

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority

namespace Platform

section Properties

  variable {sporadic_task : Type _} [DecidableEq sporadic_task]
  variable (task_cost : sporadic_task → Time)
  variable (task_period : sporadic_task → Time)
  variable (task_deadline : sporadic_task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_deadline : Job → Time)
  variable (job_task : Job → sporadic_task)

  variable (arr_seq : arrival_sequence Job)

  variable (sched : schedule Job)

  section Execution

    def work_conserving :=
      ∀ j t,
        arrives_in arr_seq j →
        backlogged job_arrival job_cost sched j t →
        ∃ j_other, scheduled_at sched j_other t = true

  end Execution

  section FP

    variable (higher_eq_priority : FP_policy sporadic_task)

    def respects_FP_policy :=
      ∀ j j_hp t,
        arrives_in arr_seq j →
        backlogged job_arrival job_cost sched j t →
        scheduled_at sched j_hp t = true →
        higher_eq_priority (job_task j_hp) (job_task j) = true

  end FP

  section JLFP

    variable (higher_eq_priority : JLFP_policy Job)

    def respects_JLFP_policy :=
      ∀ j j_hp t,
        arrives_in arr_seq j →
        backlogged job_arrival job_cost sched j t →
        scheduled_at sched j_hp t = true →
        higher_eq_priority j_hp j = true

  end JLFP

  section JLDP

    variable (higher_eq_priority : JLDP_policy Job)

    def respects_JLDP_policy :=
      ∀ j j_hp t,
        arrives_in arr_seq j →
        backlogged job_arrival job_cost sched j t →
        scheduled_at sched j_hp t = true →
        higher_eq_priority t j_hp j = true

  end JLDP

end Properties

section Lemmas

  variable {sporadic_task : Type _} [DecidableEq sporadic_task]
  variable (task_cost : sporadic_task → Time)
  variable (task_period : sporadic_task → Time)
  variable (task_deadline : sporadic_task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_deadline : Job → Time)
  variable (job_task : Job → sporadic_task)

  variable (arr_seq : arrival_sequence Job)

  variable (sched : schedule Job)

  private abbrev job_backlogged_at := backlogged job_arrival job_cost sched
  private abbrev job_pending_at := pending job_arrival job_cost sched
  private abbrev job_completed_by := completed_by job_cost sched

  section JobNeverBacklogged

    variable (H_jobs_must_arrive_to_execute :
      jobs_must_arrive_to_execute job_arrival sched)
    variable (H_completed_jobs_dont_execute :
      completed_jobs_dont_execute job_cost sched)

    variable (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)

    variable (j : Job)

    variable (H_j_is_never_backlogged :
      ∀ t,
        job_arrival j ≤ t ∧ t < job_arrival j + job_cost j →
        ¬ job_backlogged_at job_arrival job_cost sched j t)

    include H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
            H_work_conserving H_j_is_never_backlogged

    theorem job_never_backlogged_response_time_holds :
      ∀ R,
        R ≥ job_cost j →
        job_completed_by job_cost sched j (job_arrival j + R) := by
      intro R hR
      -- Goal: job_cost j ≤ service sched j (job_arrival j + R)
      simp only [job_completed_by, completed_by, service, service_during]
      -- Use ignore_service_before_arrival to remove service before arrival
      rw [ignore_service_before_arrival job_arrival sched H_jobs_must_arrive_to_execute j 0
            (job_arrival j + R) (Nat.zero_le _) (Nat.le_add_right _ _)]
      -- Now goal: job_cost j ≤ ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), service_at sched j t
      -- Since [arr, arr+cost) ⊆ [arr, arr+R), bound from below
      calc job_cost j
          = ∑ _t ∈ Finset.Ico (job_arrival j) (job_arrival j + job_cost j), 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]
            simp only [Time] at *; omega
        _ ≤ ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + job_cost j), service_at sched j t := by
            apply Finset.sum_le_sum
            intro t ht
            rw [Finset.mem_Ico] at ht
            -- Show service_at sched j t ≥ 1 by contradiction
            by_contra h
            push_neg at h
            -- h : service_at sched j t < 1, i.e., service_at = 0
            have hnsched : ¬ (scheduled_at sched j t = true) := by
              intro hsched
              have : service_at sched j t = 1 := by
                simp only [service_at]; rw [hsched]; simp [Bool.toNat]
              simp only [Time] at *; omega
            -- j is not backlogged at t, by hypothesis
            have hnback := H_j_is_never_backlogged t ⟨ht.1, ht.2⟩
            -- But j is pending at t (arrived and not completed)
            have hpending : pending job_arrival job_cost sched j t := by
              constructor
              · -- has_arrived: job_arrival j ≤ t
                exact ht.1
              · -- ¬ completed_by: service sched j t < job_cost j
                intro hcomp
                simp only [completed_by, service, service_during] at hcomp
                rw [ignore_service_before_arrival job_arrival sched H_jobs_must_arrive_to_execute j 0
                      t (Nat.zero_le _) (by exact ht.1)] at hcomp
                -- ∑ i ∈ Ico (job_arrival j) t, service_at sched j i ≤ t - job_arrival j < job_cost j
                have hle_delta : ∑ i ∈ Finset.Ico (job_arrival j) t, service_at sched j i ≤ t - job_arrival j := by
                  calc ∑ i ∈ Finset.Ico (job_arrival j) t, service_at sched j i
                      ≤ ∑ _i ∈ Finset.Ico (job_arrival j) t, 1 := by
                        apply Finset.sum_le_sum; intro i _; exact service_at_most_one sched j i
                    _ = t - job_arrival j := by
                        rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]
                simp only [Time] at *; omega
            -- j is pending and not scheduled → j is backlogged
            have hback : backlogged job_arrival job_cost sched j t := ⟨hpending, hnsched⟩
            exact hnback hback
        _ ≤ ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), service_at sched j t := by
            apply Finset.sum_le_sum_of_subset
            intro x hx
            rw [Finset.mem_Ico] at hx ⊢
            constructor
            · exact hx.1
            · simp only [Time] at *; omega

  end JobNeverBacklogged

end Lemmas

end Platform

end Prosa.Classic.Model.Schedule.Uni.Basic.Platform
