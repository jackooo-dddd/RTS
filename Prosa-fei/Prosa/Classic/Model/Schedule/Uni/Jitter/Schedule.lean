-- Translated from: ../rt-proofs/classic/model/schedule/uni/jitter/schedule.v
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule

section RedefiningProperties

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_jitter : Job → Time)

variable (arr_seq : arrival_sequence Job)
variable (sched : schedule Job)

section JobProperties

variable (j : Job)

def pending (t : Time) : Prop :=
  jitter_has_passed job_arrival job_jitter j t ∧ ¬ completed_by job_cost sched j t

def backlogged (t : Time) : Prop :=
  pending job_arrival job_cost job_jitter sched j t ∧ ¬ (scheduled_at sched j t = true)

end JobProperties

section ValidSchedules

def jobs_execute_after_jitter : Prop :=
  ∀ j t, scheduled_at sched j t = true → jitter_has_passed job_arrival job_jitter j t

end ValidSchedules

section Lemmas

section Arrival

variable (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
include H_jobs_execute_after_jitter

theorem jobs_with_jitter_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival sched := by
  intro j t hsched
  unfold has_arrived
  have h := H_jobs_execute_after_jitter j t hsched
  unfold jitter_has_passed actual_arrival at h
  simp only [Time] at *; omega

variable (j : Job)

omit H_jobs_execute_after_jitter in
theorem jitter_has_passed_implies_arrived :
    ∀ t, jitter_has_passed job_arrival job_jitter j t →
      has_arrived job_arrival j t := by
  intro t h
  unfold jitter_has_passed actual_arrival at h
  unfold has_arrived
  simp only [Time] at *; omega

theorem service_before_jitter_is_zero :
    ∀ t, t < actual_arrival job_arrival job_jitter j →
      service_at sched j t = 0 := by
  intro t hlt
  simp only [service_at, scheduled_at]
  cases hd : (sched t == some j)
  · simp [Bool.toNat]
  · exfalso
    have hsched : scheduled_at sched j t = true := by simp [scheduled_at, hd]
    have h := H_jobs_execute_after_jitter j t hsched
    unfold jitter_has_passed at h
    simp only [Time] at *; omega

theorem cumulative_service_before_jitter_is_zero :
    ∀ t1 t2, t2 ≤ actual_arrival job_arrival job_jitter j →
      ∑ i ∈ Finset.Ico t1 t2, service_at sched j i = 0 := by
  intro t1 t2 hle
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_Ico] at hi
  exact service_before_jitter_is_zero job_arrival job_jitter sched H_jobs_execute_after_jitter j i (by simp only [Time] at *; omega)

theorem ignore_service_before_jitter :
    ∀ t1 t2, t1 ≤ actual_arrival job_arrival job_jitter j →
      actual_arrival job_arrival job_jitter j ≤ t2 →
      ∑ t ∈ Finset.Ico t1 t2, service_at sched j t =
      ∑ t ∈ Finset.Ico (actual_arrival job_arrival job_jitter j) t2, service_at sched j t := by
  intro t1 t2 hle1 hge2
  rw [(Finset.Ico_union_Ico_eq_Ico hle1 hge2).symm,
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive t1 (actual_arrival job_arrival job_jitter j) t2),
      cumulative_service_before_jitter_is_zero job_arrival job_jitter sched H_jobs_execute_after_jitter j t1 (actual_arrival job_arrival job_jitter j) (le_refl _)]
  omega

end Arrival

section Pending

variable (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
variable (H_completed_jobs : completed_jobs_dont_execute job_cost sched)
variable (j : Job)
include H_jobs_execute_after_jitter H_completed_jobs

theorem scheduled_implies_pending :
    ∀ t, scheduled_at sched j t = true →
      pending job_arrival job_cost job_jitter sched j t := by
  intro t hsched
  unfold pending
  constructor
  · exact H_jobs_execute_after_jitter j t hsched
  · intro hcomp
    unfold completed_by at hcomp
    have hbound : service sched j (t + 1) ≤ job_cost j := H_completed_jobs j (t + 1)
    -- service_at sched j t = 1 since j is scheduled at t
    have hsa : service_at sched j t = 1 := by
      simp only [service_at]; rw [hsched]; simp [Bool.toNat]
    -- ∑ i ∈ Ico t (t+1), service_at sched j i = service_at sched j t
    have hsingleton : ∑ i ∈ Finset.Ico t (t + 1), service_at sched j i = service_at sched j t := by
      simp
    -- service sched j (t+1) = service sched j t + service_at sched j t
    have hstep : service sched j (t + 1) = service sched j t + service_at sched j t := by
      unfold service service_during
      have h1 : ∑ i ∈ Finset.Ico 0 (t + 1), service_at sched j i =
          ∑ i ∈ Finset.Ico 0 t, service_at sched j i + ∑ i ∈ Finset.Ico t (t + 1), service_at sched j i := by
        rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 t (t + 1)),
            Finset.Ico_union_Ico_eq_Ico (Nat.zero_le t) (Nat.le_succ t)]
      rw [h1, hsingleton]
    -- Now: job_cost j ≤ service(t), service(t+1) ≤ job_cost j, service(t+1) = service(t) + 1
    simp only [Time] at *; omega

end Pending

end Lemmas

end RedefiningProperties

end Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
