-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/abstract_RTA/sufficient_condition_for_lock_in_service.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 101)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions

/-!
A sufficient condition for reaching the lock-in service (Rocq module `AbstractRTALockInService`).

Representation notes: the section-local `Let`s (`work_conserving`, `cumul_interference`,
`cumul_interfering_workload`, `busy_interval`, `job_last`) are unfolded; Boolean tests in proposition position are
`= true`. Binder lists follow the Rocq contract (e.g. `job_completes_within_busy_interval` takes only
`H_busy_interval`; `job_completes_after_reaching_lock_in_service` takes neither `H_lock_in_service_positive` nor
`H_work_conserving`).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.SufficientConditionForLockInService.AbstractRTALockInService

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

private theorem service_step {Job : Type v} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : Nat) :
    service sched j (t + 1) = service sched j t + service_at sched j t := by
  unfold service service_during
  rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]

theorem job_completes_within_busy_interval {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (interference : Job → time → Bool) (interfering_workload : Job → time → time) (j : Job)
    (t1 t2 : time)
    (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2) :
    completed_by job_cost sched j t2 = true := by
  obtain ⟨⟨RANGE, _, _⟩, _, QT2⟩ := H_busy_interval
  simp only [Bool.and_eq_true] at RANGE
  have LT := of_decide_eq_true RANGE.2
  simp only [pending_earlier_and_at, arrived_before, Bool.not_and, Bool.not_not, Bool.or_eq_true] at QT2
  rcases QT2 with h | h
  · exfalso; rw [decide_eq_true LT] at h; exact Bool.noConfusion h
  · exact h

theorem interference_is_complement_to_schedule {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (tsk : Task) (interference : Job → time → Bool)
    (interfering_workload : Job → time → time)
    (H_work_conserving : work_conserving job_arrival job_cost job_task arr_seq sched tsk interference
      interfering_workload)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j = true) (t1 t2 : time)
    (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2)
    (t delta : time) (H_greater_than_or_equal : t1 ≤ t) (H_less_or_equal : t + delta ≤ t2) :
    service_during sched j t (t + delta) + cumul_interference interference j t (t + delta) = delta := by
  unfold service_during cumul_interference
  rw [← Finset.sum_add_distrib]
  calc _ = ∑ _x ∈ Finset.Ico t (t + delta), (1 : Nat) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_Ico] at hx
        have WC := H_work_conserving j t1 t2 x H_j_arrives H_job_of_tsk (of_decide_eq_true H_job_cost_positive)
          H_busy_interval (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
        cases hi : interference j x
        · have := WC.mp (by rw [hi]; simp)
          simp [service_at, this]
        · have : scheduled_at sched j x = false := by
            cases hs : scheduled_at sched j x
            · rfl
            · exact absurd hi (WC.mpr hs)
          simp [service_at, this]
    _ = delta := by simp

theorem j_receives_at_least_lock_in_service {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (tsk : Task) (interference : Job → time → Bool)
    (interfering_workload : Job → time → time)
    (H_work_conserving : work_conserving job_arrival job_cost job_task arr_seq sched tsk interference
      interfering_workload)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j = true) (t1 t2 : time)
    (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2)
    (progress_of_job : time) (H_progress_le_job_cost : progress_of_job ≤ job_cost j) (delta : time)
    (H_total_workload_is_bounded : progress_of_job + cumul_interference interference j t1 (t1 + delta) ≤ delta) :
    progress_of_job ≤ service sched j (t1 + delta) := by
  by_cases NEQ : t1 + delta ≤ t2
  · have COMP := interference_is_complement_to_schedule job_arrival job_cost job_task arr_seq sched tsk interference
      interfering_workload H_work_conserving j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
      t1 delta (Nat.le_refl _) NEQ
    have SPLIT : service sched j (t1 + delta) = service sched j t1 + service_during sched j t1 (t1 + delta) := by
      unfold service service_during
      rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) (Nat.le_add_right _ _)]
    omega'
  · have C := job_completes_within_busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2
      H_busy_interval
    simp only [completed_by, decide_eq_true_eq] at C
    have M : service sched j t2 ≤ service sched j (t1 + delta) := by
      unfold service service_during
      exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl 0) (by omega'))
    omega'

theorem job_completes_after_reaching_lock_in_service {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (j : Job) (H_j_arrives : arrives_in arr_seq j)
    (H_job_cost_positive : job_cost_positive job_cost j = true)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (job_lock_in_service : Job → time)
    (H_lock_in_service_le_job_cost : job_lock_in_service_le_job_cost job_cost arr_seq job_lock_in_service)
    (H_job_nonpreemptive_after_lock_in_service :
      job_nonpreemptive_after_lock_in_service job_cost arr_seq sched job_lock_in_service) :
    ∀ t : time, job_lock_in_service j ≤ service sched j t →
      completed_by job_cost sched j (t + (job_cost j - job_lock_in_service j)) = true := by
  intro t ES
  have LE := H_lock_in_service_le_job_cost j H_j_arrives H_job_cost_positive
  generalize hL : job_cost j - job_lock_in_service j = L
  cases hc : completed_by job_cost sched j (t + L)
  · exfalso
    have SCHED : ∀ k, k ≤ L → scheduled_at sched j (t + k) = true := by
      intro k hk
      apply H_job_nonpreemptive_after_lock_in_service j t (t + k) H_j_arrives (Nat.le_add_right _ _) ES
      cases hck : completed_by job_cost sched j (t + k)
      · rfl
      · have := completion_monotonic job_cost sched j (t + k) (t + L) (by omega') hck
        rw [hc] at this; exact Bool.noConfusion this
    have GROW : ∀ k, k ≤ L + 1 → service sched j t + k ≤ service sched j (t + k) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k IH =>
        intro hk
        show service sched j t + (k + 1) ≤ service sched j (t + (k + 1))
        rw [show t + (k + 1) = (t + k) + 1 by omega', service_step]
        have := IH (by omega')
        have hs := SCHED k (by omega')
        simp only [service_at, hs, Bool.toNat_true]
        omega'
    have G := GROW (L + 1) (Nat.le_refl _)
    have D := H_completed_jobs_dont_execute j (t + (L + 1))
    omega'
  · rfl

end Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.SufficientConditionForLockInService.AbstractRTALockInService
