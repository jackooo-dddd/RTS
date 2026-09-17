-- Translated from: ../rt-proofs/analysis/facts/behavior/completion.v
import Prosa.Analysis.Facts.Behavior.Service
import Prosa.Analysis.Facts.Behavior.Arrivals

namespace Prosa.Analysis.Facts.Behavior.Completion

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Processor.Platform_properties
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Arrivals

section CompletionFacts

variable {Job : JobType}
variable [JobCost Job]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (sched : schedule PState)
variable (j : Job)

theorem completion_monotonic :
    ∀ t t',
      t ≤ t' →
      completed_by sched j t →
      completed_by sched j t' := by
  intro t t' hle hcomp
  unfold completed_by at *
  exact le_trans hcomp (service_monotonic sched j t t' hle)

theorem less_service_than_cost_is_incomplete :
    ∀ t,
      service sched j t < job_cost j ↔
      ¬ completed_by sched j t := by
  intro t
  unfold completed_by
  simp only [work]
  omega

theorem incomplete_is_positive_remaining_cost :
    ∀ t,
      ¬ completed_by sched j t ↔
      remaining_cost sched j t > 0 := by
  intro t
  unfold completed_by remaining_cost
  simp only [work]
  omega

variable (H_completed_jobs : completed_jobs_dont_execute (Job := Job) sched)

include H_completed_jobs in
theorem serviced_implies_positive_remaining_cost :
    ∀ t,
      service_at sched j t > 0 →
      remaining_cost sched j t > 0 := by
  intro t hserv
  rw [incomplete_is_positive_remaining_cost sched j t |>.symm]
  rw [less_service_than_cost_is_incomplete sched j t |>.symm]
  exact H_completed_jobs j t (service_at_implies_scheduled_at sched j t hserv)

variable (H_scheduled_implies_serviced : ideal_progress_proc_model (Job := Job) PState)

include H_completed_jobs H_scheduled_implies_serviced in
theorem scheduled_implies_positive_remaining_cost :
    ∀ t,
      scheduled_at sched j t = true →
      remaining_cost sched j t > 0 := by
  intro t hsched
  apply serviced_implies_positive_remaining_cost sched j H_completed_jobs t
  unfold service_at
  exact H_scheduled_implies_serviced j (sched t) hsched

include H_completed_jobs in
theorem completed_implies_not_scheduled :
    ∀ t,
      completed_by sched j t →
      scheduled_at sched j t = false := by
  intro t hcomp
  by_contra hsched
  push_neg at hsched
  simp only [Bool.not_eq_false] at hsched
  have hlt := H_completed_jobs j t hsched
  unfold completed_by at hcomp
  simp only [work] at hlt hcomp
  omega

include H_completed_jobs H_scheduled_implies_serviced in
theorem scheduled_implies_not_completed :
    ∀ t,
      scheduled_at sched j t = true →
      ¬ completed_by sched j t := by
  intro t hsched
  have hrem := scheduled_implies_positive_remaining_cost sched j H_completed_jobs H_scheduled_implies_serviced t hsched
  exact (incomplete_is_positive_remaining_cost sched j t).mpr hrem

end CompletionFacts

section ServiceAndCompletionFacts

variable {Job : JobType}
variable [JobCost Job]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (sched : schedule PState)
variable (H_completed_jobs : completed_jobs_dont_execute (Job := Job) sched)
variable (j : Job)
variable (H_unit_service : unit_service_proc_model (Job := Job) PState)

include H_completed_jobs H_unit_service in
theorem service_at_most_cost :
    ∀ t,
      service sched j t ≤ job_cost j := by
  intro t
  induction t with
  | zero => rw [service0]; exact Nat.zero_le _
  | succ t ih =>
    show service sched j (t + 1) ≤ job_cost j
    rw [← service_last_plus_before sched j t]
    by_cases hcomp : completed_by sched j t
    · -- job already completed, so not scheduled, no service at t
      have hns := completed_implies_not_scheduled sched j H_completed_jobs t hcomp
      rw [not_scheduled_implies_no_service sched j t hns, Nat.add_zero]
      exact ih
    · -- not completed, so service < cost, and service_at ≤ 1
      have hlt := (less_service_than_cost_is_incomplete sched j t).mpr hcomp
      have hunit : service_at sched j t ≤ 1 := H_unit_service j (sched t)
      calc service sched j t + service_at sched j t
          ≤ service sched j t + 1 := Nat.add_le_add_left hunit _
        _ ≤ job_cost j := hlt

include H_completed_jobs H_unit_service in
theorem service_cost_invariant :
    ∀ t,
      (service sched j t) + (remaining_cost sched j t) = job_cost j := by
  intro t
  unfold remaining_cost
  have h := service_at_most_cost sched H_completed_jobs j H_unit_service t
  simp only [work] at h ⊢
  omega

include H_completed_jobs H_unit_service in
theorem cumulative_service_le_job_cost :
    ∀ t t',
      service_during sched j t t' ≤ job_cost j := by
  intro t t'
  by_cases hle : t ≤ t'
  · have hcat := service_cat sched j t t' hle
    have hbound := service_at_most_cost sched H_completed_jobs j H_unit_service t'
    simp only [work] at hcat hbound ⊢
    omega
  · push_neg at hle
    rw [service_during_geq sched j t t' (Nat.le_of_lt hle)]
    exact Nat.zero_le _

include H_completed_jobs H_unit_service in
theorem job_doesnt_complete_before_remaining_cost :
    ∀ t,
      ¬ completed_by sched j t →
      ¬ completed_by sched j (t + remaining_cost sched j t - 1) := by
  intro t hnotcomp
  have hlt := (less_service_than_cost_is_incomplete sched j t).mpr hnotcomp
  have hle := service_at_most_cost sched H_completed_jobs j H_unit_service t
  have hrem_pos : remaining_cost sched j t > 0 :=
    (incomplete_is_positive_remaining_cost sched j t).mp hnotcomp
  -- t ≤ t + rc - 1
  have ht_le : t ≤ t + remaining_cost sched j t - 1 :=
    Nat.le_sub_one_of_lt (Nat.lt_add_of_pos_right hrem_pos)
  -- service(t + rc - 1) = service(t) + service_during(t, t+rc-1)
  have hcat := service_cat sched j t (t + remaining_cost sched j t - 1) ht_le
  -- service_during(t, t+rc-1) ≤ rc - 1
  have heq : t + remaining_cost sched j t - 1 = t + (remaining_cost sched j t - 1) :=
    Nat.add_sub_assoc hrem_pos t
  have hsd_le : service_during sched j t (t + remaining_cost sched j t - 1) ≤ remaining_cost sched j t - 1 := by
    rw [heq]
    exact cumulative_service_le_delta H_unit_service sched j t (remaining_cost sched j t - 1)
  -- Goal: ¬ completed_by sched j (t + rc - 1)
  -- i.e., service(t + rc - 1) < job_cost j
  rw [← less_service_than_cost_is_incomplete sched j]
  rw [← hcat]
  have hinv := service_cost_invariant sched H_completed_jobs j H_unit_service t
  -- hinv : service sched j t + remaining_cost sched j t = job_cost j
  have hrc_ne : remaining_cost sched j t ≠ 0 := Nat.pos_iff_ne_zero.mp hrem_pos
  calc service sched j t + service_during sched j t (t + remaining_cost sched j t - 1)
      ≤ service sched j t + (remaining_cost sched j t - 1) := Nat.add_le_add_left hsd_le _
    _ < service sched j t + remaining_cost sched j t := by
        exact Nat.add_lt_add_left (Nat.sub_one_lt hrc_ne) _
    _ = job_cost j := hinv

section GuaranteedService

variable (H_scheduled_implies_serviced : ideal_progress_proc_model (Job := Job) PState)
variable [JobArrival Job]
variable (H_jobs_must_arrive : jobs_must_arrive_to_execute (Job := Job) sched)

include H_completed_jobs H_scheduled_implies_serviced H_jobs_must_arrive in
theorem scheduled_implies_pending :
    ∀ t,
      scheduled_at sched j t = true →
      pending sched j t := by
  intro t hsched
  unfold pending
  constructor
  · exact H_jobs_must_arrive j t hsched
  · exact scheduled_implies_not_completed sched j H_completed_jobs H_scheduled_implies_serviced t hsched

end GuaranteedService

end ServiceAndCompletionFacts

section PositiveCost

variable {Job : JobType}
variable [JobCost Job]
variable [JobArrival Job]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (sched : schedule PState)
variable (j : Job)
variable (H_positive_cost : job_cost j > 0)
variable (H_jobs_must_arrive : jobs_must_arrive_to_execute (Job := Job) sched)

include H_positive_cost H_jobs_must_arrive in
theorem completed_implies_scheduled_before :
    ∀ t,
      completed_by sched j t →
      ∃ t',
        job_arrival j ≤ t' ∧ t' < t ∧
        scheduled_at sched j t' = true := by
  intro t hcomp
  unfold completed_by at hcomp
  have hpos_service : 0 < service sched j t := by
    simp only [work] at hcomp H_positive_cost ⊢; omega
  exact positive_service_implies_scheduled_since_arrival sched j H_jobs_must_arrive t hpos_service

include H_positive_cost H_jobs_must_arrive in
theorem job_pending_at_arrival :
    pending sched j (job_arrival j) := by
  unfold pending
  constructor
  · unfold has_arrived; exact le_refl _
  · unfold completed_by
    rw [no_service_before_arrival sched j H_jobs_must_arrive (job_arrival j) (le_refl _)]
    simp only [work] at H_positive_cost ⊢
    omega

end PositiveCost

section CompletedJobs

variable {Job : JobType} {PState : Type _}
variable [ProcessorState Job PState]
variable (sched : schedule PState)
variable [JobCost Job]
variable [JobArrival Job]
variable [JobReady Job PState]

theorem ready_implies_incomplete :
    ∀ (j : Job) t, job_ready sched j t = true → ¬ completed_by sched j t := by
  intro j t hready
  exact (any_ready_job_is_pending sched j t hready).2

theorem completed_jobs_are_not_ready :
    jobs_must_be_ready_to_execute (Job := Job) sched →
    completed_jobs_dont_execute (Job := Job) sched := by
  intro hready
  unfold completed_jobs_dont_execute
  intro j t hsched
  have hready_jt := hready j t hsched
  have hnotcomp := ready_implies_incomplete sched j t hready_jt
  exact (less_service_than_cost_is_incomplete sched j t).mpr hnotcomp

theorem ideal_progress_completed_jobs :
    ideal_progress_proc_model (Job := Job) PState →
    (∀ (j : Job) t, service sched j t ≤ job_cost j) →
    completed_jobs_dont_execute (Job := Job) sched := by
  intro hideal hbound
  unfold completed_jobs_dont_execute
  intro j t hsched
  have hub := hbound j (t + 1)
  have hpos : service_at sched j t > 0 := by
    unfold service_at
    exact hideal j (sched t) hsched
  have hcat := service_last_plus_before sched j t
  simp only [work] at hcat hub hpos ⊢
  omega

end CompletedJobs

end Prosa.Analysis.Facts.Behavior.Completion
